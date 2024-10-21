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
int warpSize = 0;

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

proctype pex(byte me; chan pex_u; chan u_pex) { 
    int startTime = 0;
    int curTime = 0;
    byte i = 0;

    do 
    :: u_pex ? go ->
        atomic { 
            startTime = globalTime;
            curTime = globalTime;
        } 
        long_work(GLOBAL_ACCESS_TIME); 
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


proctype collector(int countFree; chan pex_sch; chan coll_sch; chan sch_coll) {
    int diffFree = 0;

    do 
        :: sch_coll ? go ->
            do 
            :: pex_sch ? done ->
                diffFree = diffFree + 1
            :: empty(pex_sch) -> break;
            od; 
            coll_sch ! diffFree;
            diffFree = 0
        :: pex_sch ? done ->
            diffFree = diffFree + 1
        :: sch_coll ? stop ->
            break;
    od;
}


proctype scheduler(chan dev_sch; chan sch_dev) {
    chan warps = [16] of {int, bool, bool, int};
    chan pex_sch = [0] of {mtype : action}
    chan sch_pex = [0] of {mtype : action}
    chan sch_coll = [0] of {mtype : action}
    chan coll_sch = [0] of {int}

    int nWarps;
    int countPEs = 0;
    int countFree = nWorkingPEsPerUnit;
    int diffFree;
    if 
        :: workgroupSize <= warpSize ->
            nWarps = 1
            countPEs = countPEs + workgroupSize;
            warps ! 0, false, false, workgroupSize
        :: else ->
            nWarps = (nWorkingPEsPerUnit / warpSize) * (workgroupSize / warpSize + 1)
            byte i = 0
            for (i : 0 .. nWarps - (nWorkingPEsPerUnit / warpSize) - 1) { 
                warps ! i, false, false, warpSize;
                countPEs = countPEs + workgroupSize;
            }
            for (i : 0 .. nWorkingPEsPerUnit / warpSize - 1) { 
                warps ! i, false, false, workgroupSize % warpSize;
            }
    fi;

    atomic {
        for (i : 0 .. nWorkingPEsPerUnit-1) { 
            run pex(i, pex_sch, sch_pex);
        }
        run collector(countFree, pex_sch, coll_sch, sch_coll)
    }
    
    int currWarpIndex;
    int currWarpSize;
    bool currWarpHasInstr;
    bool currWarpIsReady;
    do 
        :: dev_sch ? go ->
            do 
                :: nempty(warps) ->
                    warps ? currWarpIndex, currWarpHasInstr, currWarpIsReady, currWarpSize;
                    if 
                        :: !currWarpHasInstr ->
                            //добавить задержку добавления инструкций
                            warps ! currWarpHasInstr, true, false, currWarpSize;

                        :: currWarpHasInstr && !currWarpIsReady ->
                            sch_coll ! go
                            coll_sch ? diffFree
                            countFree = countFree + diffFree;
                            if
                                :: countFree >= currWarpSize ->
                                    warps ! currWarpHasInstr, true, true, currWarpSize;
                                :: else ->
                                    warps ! currWarpHasInstr, true, false, currWarpSize;
                            fi;
                            // загружено ли все в кэш
                            // есть ли свободные ядра

                        :: currWarpHasInstr && currWarpIsReady ->
                            // запускаем ворп
                            atomic {
                                for (i : 0 .. currWarpSize-1) {
                                    sch_pex ! go;
                                }
                                countFree = countFree - currWarpSize;
                                warps ! currWarpHasInstr, false, true, currWarpSize;
                            }
                        
                        :: !currWarpHasInstr && currWarpIsReady ->
                            skip
                    fi;

                :: empty(warps) -> break;
            od;

            sch_dev ! done;
        :: dev_sch ? stop -> 
            atomic {
                int k = (countPEs > nWorkingPEsPerUnit -> nWorkingPEsPerUnit : countPEs) 
                for (i : 0 .. k-1) { 
                    sch_pex ! stop;
                }
                sch_coll ! stop
            }
            break;
    od;

}


proctype device(chan d_hst; chan hst_d) {   
    byte i = 0;
    chan dev_sch = [0] of {mtype : action};
    chan sch_dev = [0] of {mtype : action};

    atomic { 
        for (i : 0 .. nWorkingUnitsPerDevice-1) { 
            run scheduler(dev_sch, sch_dev); 
        }
    } 
    do 
    :: hst_d ? go ->
        atomic { 
            for (i : 0 .. nWorkingUnitsPerDevice-1) { 
                dev_sch ! go;
            }
        }
        if 
        :: nWorkgroups <= nUnitsPerDevice -> 
            atomic {
                for (i : 0 .. nWorkingUnitsPerDevice-1) { 
                    sch_dev ? done;
                }
            }					
        :: else ->
            i = 0;
            do 
            :: i < nWorkgroups - nUnitsPerDevice -> 
                atomic { 
                    sch_dev ? done;
                    dev_sch ! go;
                    i++; 
                }
            :: else -> break;
            od;
            i = 0;
            do 
            :: i < nUnitsPerDevice -> 
                atomic { 
                    sch_dev ? done;
                    i++;
                }
            :: else -> break;
            od;	
        fi;
        d_hst ! done;
    :: hst_d ? stop -> 
        atomic { 
            for (i : 0 .. nWorkingUnitsPerDevice-1) { 
            dev_sch ! stop;
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
    nPEsPerUnit = 2;
    nUnitsPerDevice = 2;
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
    //nWorkingPEsPerUnit = (workgroupSize <= nPEsPerUnit -> workgroupSize : nPEsPerUnit);
    nWorkingPEsPerUnit = nPEsPerUnit;
    allWorkingPEs = nWorkingPEsPerUnit * nWorkingUnitsPerDevice * nWorkingDevices;

    warpSize = nPEsPerUnit; //если максимально 1 выполняющийся warp
    
    Tmin = 52; 

    atomic {
        run host(); 
        run clock(); 
    }
}

ltl NonTerm  { [] !FIN } 
ltl OverTime { [] (FIN -> (globalTime > Tmin)) } 
ltl Fin { <> FIN }
