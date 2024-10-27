/*
The model of execution of an abstract kernel on an abstract OpenCL platform intended for auto-tuning; 
** several devices, several units, several processing elements ** 
@author Natalia Garanina natta.garanina@gmail.com https://www.researchgate.net/profile/Natalia-Garanina
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@conference LOPSTR-2022
@license GNU GPL
*/

#define GLOBAL_ACCESS_TIME 4
#define LOCAL_ACCESS_TIME 1

// PE - processing element

// hardware parameters
byte nPEsPerUnit = 0;
byte nUnitsPerDevice = 0;
byte nDevices = 0;

// tuning parameters
int workgroupSize = 0;
int nWorkgroups = 0;
int tileSize = 0;
 
int inputDataSize = 0;

// service vars
byte nRunningPEs = 0;
byte nWorkingDevices = 0;
byte nWorkingUnitsPerDevice = 0;
byte nWorkingPEsPerUnit = 0;
byte allWorkingPEs = 0;
byte nWaitingPEs = 0;
int globalTime = 0;

int Tmin = 0;
bool FIN = false;

mtype : action = { done, stop, go };

#define LOG_VAR(context_id, id) \
  printf("[LOG][Context=%d][ID=%d] nPEsPerUnit=%d, nUnitsPerDevice=%d, nDevices=%d, GLOBAL_ACCESS_TIME=%d, workgroupSize=%d, nWorkgroups=%d, tileSize=%d, inputDataSize=%d, nRunningPEs=%d, nWorkingDevices=%d, nWorkingUnitsPerDevice=%d, nWorkingPEsPerUnit=%d, allWorkingPEs=%d, globalTime=%d, Tmin=%d, FIN=%d\n", \
    context_id, id, nPEsPerUnit, nUnitsPerDevice, nDevices, GLOBAL_ACCESS_TIME, workgroupSize, nWorkgroups, tileSize, inputDataSize, nRunningPEs, nWorkingDevices, nWorkingUnitsPerDevice, nWorkingPEsPerUnit, allWorkingPEs, globalTime, Tmin, FIN)

inline work_step() {
    atomic { 
        curTime = globalTime;
        nRunningPEs++;
        globalTime == curTime + 1;  //waiting
    }
}

inline long_work(t) {
    do  
    :: globalTime >= (startTime + t) -> break;
    :: else ->  work_step()
    od;
}

proctype pex(byte me; chan pex_b; chan b_pex; chan pex_u; chan u_pex) { 
    int startTime = 0;
    int curTime = 0;
    byte i = 0;

    do 
    :: u_pex ? go ->
        atomic { 
            startTime = globalTime;
            curTime = globalTime;
        }
        for (i : 0 .. tileSize-1) { 
            long_work(GLOBAL_ACCESS_TIME);
            startTime = curTime;
            if
            :: true -> long_work(GLOBAL_ACCESS_TIME); startTime = curTime;
            :: true -> skip;
            fi;
        }
        pex_b ! done;		 
        b_pex ? go;  
        startTime = globalTime;
        long_work(LOCAL_ACCESS_TIME);
        startTime = curTime;
        if
        :: me == 0 ->
            for (i : 0 .. workgroupSize) {
                long_work(LOCAL_ACCESS_TIME);
                startTime = curTime;
            }
            long_work(LOCAL_ACCESS_TIME);
            startTime = curTime;
        :: else
        fi;
            
        pex_u ! done;  
    :: u_pex ? stop -> break;
    od;
}



proctype barrier(chan pex_b; chan b_pex) { 
    byte i = 0;
    do 
    :: pex_b ? done ->
        atomic {
            i = 1;
            nWaitingPEs++;
        }
        do  
        :: i < nWorkingPEsPerUnit -> 
            atomic { 
                pex_b ? done;
                i++;
                nWaitingPEs++
            }
        :: else -> break;
        od;	
        atomic { 
            for (i : 0 .. nWorkingPEsPerUnit-1) { 
                b_pex ! go; 
            }
            nWaitingPEs = nWaitingPEs - nWorkingPEsPerUnit;
        } 
    :: pex_b ? stop -> break;
    od;
    }



proctype unit(chan dev_u; chan u_dev) {
    byte i = 0;
    chan pex_b = [0] of {mtype : action};
    chan b_pex = [0] of {mtype : action};
    chan pex_u = [0] of {mtype : action}; 
    chan u_pex = [0] of {mtype : action}; 
    
    run barrier (pex_b, b_pex);
    atomic {
        for (i : 0 .. nWorkingPEsPerUnit-1) { 
            run pex(i, pex_b, b_pex, pex_u, u_pex);
        }
    }
    do 
    :: dev_u ? go ->
        atomic {
            for (i : 0 .. nWorkingPEsPerUnit-1) {
                u_pex ! go;
            }
        }
        i = 0;
        if 
        :: workgroupSize <= nPEsPerUnit -> 
            atomic {
                for (i : 0 .. nWorkingPEsPerUnit-1) {
                    pex_u ? done;
                }
            }
        :: else -> 
            do 
            :: i < workgroupSize-nPEsPerUnit -> 
                atomic { 
                    pex_u ? done;
                    u_pex ! go;
                    i++; 
                }
            :: else -> break;
            od; 
            i = 0;
            do 
            :: i < nPEsPerUnit -> 
                atomic { 
                    pex_u ? done;
                    i++; 
                }
            :: else -> break;
            od;
        fi;	
        u_dev ! done;
    :: dev_u ? stop -> 
        pex_b ! stop; 
        atomic { 
            for (i : 0 .. nWorkingPEsPerUnit-1) {
                u_pex ! stop;
            }
        }
        break;
    od;
}



proctype device(chan d_hst; chan hst_d) {   
    byte i = 0;
    chan dev_u = [0] of {mtype : action};
    chan u_dev = [0] of {mtype : action};

    atomic { 
        for (i : 0 .. nWorkingUnitsPerDevice-1) { 
            run unit (dev_u, u_dev); 
        }
    } 
    do 
    :: hst_d ? go ->
        atomic { 
            for (i : 0 .. nWorkingUnitsPerDevice-1) { 
                dev_u ! go;
            }
        }
        if 
        :: nWorkgroups <= nUnitsPerDevice -> 
            atomic {
                for (i : 0 .. nWorkingUnitsPerDevice-1) { 
                    u_dev ? done; 
                    allWorkingPEs = allWorkingPEs - nWorkingPEsPerUnit; 
                }
            }					
        :: else ->
            i = 0;
            do 
            :: i < nWorkgroups - nUnitsPerDevice -> 
                atomic { 
                    u_dev ? done;
                    dev_u ! go;
                    i++; 
                }
            :: else -> break;
            od;
            i = 0;
            do 
            :: i < nUnitsPerDevice -> 
                atomic { 
                    u_dev ? done;
                    allWorkingPEs = allWorkingPEs - nWorkingPEsPerUnit;
                    i++;
                }
            :: else -> break;
            od;	
        fi;
        d_hst ! done;
    :: hst_d ? stop -> 
        atomic { 
            for (i : 0 .. nWorkingUnitsPerDevice-1) { 
            dev_u ! stop;
            }
        } 
        break;
    od;
}



proctype host() { 
    byte i = 0;
    chan d_hst = [0] of {mtype : action};
    chan hst_d = [0] of {mtype : action};
    
    FIN = false;
    atomic { 
        for (i : 0 .. nWorkingDevices-1) {
            run device (d_hst, hst_d);
        }
    } 
    atomic { 
        for (i : 0 .. nWorkingDevices-1) {
            hst_d ! go;
        }
    }
    if
    :: nWorkgroups <= nUnitsPerDevice*nDevices -> 
        atomic { 
            for (i : 0 .. nWorkingDevices-1) {
                d_hst ? done; 
                hst_d ! stop;
            }
        }
    :: else -> 
        i = 0;
        do 
        :: i < (nWorkgroups / nUnitsPerDevice * nDevices) - nDevices -> 
            atomic { 
                d_hst ? done;
                allWorkingPEs = allWorkingPEs + (nWorkingPEsPerUnit * nWorkingUnitsPerDevice);
                hst_d ! go;
                i++; 
            }
        :: else -> break;
        od;
        i = 0;
        do 
        :: i < nDevices -> 
            atomic { 
                    d_hst ? done;
                    hst_d ! stop;
                    i++;
            }
        :: else -> break;
        od;	
    fi;
    FIN = true;
}



proctype clock() { 
    do 
    :: FIN -> break;
    :: nRunningPEs == allWorkingPEs - nWaitingPEs && 
                      allWorkingPEs != 0 && 
                      nWaitingPEs != allWorkingPEs -> 
        atomic { 
            LOG_VAR(1, globalTime)
            nRunningPEs = 0; 
            globalTime++; 
        }
    od;
}



active proctype main() { 
    nPEsPerUnit = 1;
    nUnitsPerDevice = 1;
    nDevices = 1;
    
    // inputDataSize = 2^n
    byte n = 3;
    inputDataSize = 1 << n;
    
    byte d;
    select (d : 2 .. n-1);  
    workgroupSize = inputDataSize >> (n - d);
    select (d : 1 .. n-1); 
    tileSize = inputDataSize >> (n - d);
    
    nWorkgroups = inputDataSize / workgroupSize;
    nWorkingDevices = (nWorkgroups <= (nUnitsPerDevice * nDevices) -> (nWorkgroups / nUnitsPerDevice) : nDevices); 
    nWorkingDevices = (nWorkgroups / nUnitsPerDevice -> nWorkingDevices : 1); 
    nWorkingUnitsPerDevice = (nWorkgroups <= nUnitsPerDevice -> nWorkgroups : nUnitsPerDevice);
    nWorkingPEsPerUnit = (workgroupSize <= nPEsPerUnit -> workgroupSize : nPEsPerUnit);
    allWorkingPEs = nWorkingPEsPerUnit * nWorkingUnitsPerDevice * nWorkingDevices;
    
    Tmin = 52; 

    atomic {
        run host(); 
        run clock(); 
    }
}

ltl NonTerm  { [] !FIN } 
ltl OverTime { [] (FIN -> (globalTime > Tmin)) } 
ltl Fin { <> FIN }