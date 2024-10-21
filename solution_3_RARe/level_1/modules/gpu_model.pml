#ifndef __GPU_PML__
#define __GPU_PML__

#include "function.pml"


proctype pex (byte id; byte unit_id; chan pex_u; chan u_pex) {
    int start_time = 0; 	// the start time of the operation for this workgroup
    int cur_time = 0; 		// the current time while the operation is running to track delays

    byte global_offset; 	// shift to access global memory so that each processor processes its own part of the data
    byte tile_idx;			// index of the current element within the workgroup (iterator over tile elements)
    byte wg_iter;			// number of the current iteration within the working group. Used to calculate shift when there is insufficient number of processors
    byte wg_id; 			// workgroup ID (number of the workgroup to which the data is assigned)
    byte local_id;  		// local ID of the process in the workgroup, may depend on the size of the workgroup and the current iteration
    byte local_mem_idx = id + unit_id * PEX_PER_UNIT; // The position of a process in the local workgroup memory depends on its unique identifier and block number

    do // 89
    :: 	u_pex ? wg_id, GOWG ->
        do
        :: u_pex ? wg_iter, GO ->
            atomic{
                start_time = service.time;
                cur_time = service.time;
            }
            local_id = (tuning.wgSize > PEX_PER_UNIT -> id + wg_iter : id);
            global_offset = (
                tuning.wgSize > PEX_PER_UNIT ->
                tuning.tileSize * (wg_id * tuning.wgSize + id + wg_iter * PEX_PER_UNIT) :
                tuning.tileSize * (wg_id * tuning.wgSize + local_id)
            );

            for ( tile_idx : 0 .. tuning.tileSize-1) {
                if
                :: tile_idx + global_offset >= SIZE_INPUT_DATA -> break;
                :: else -> skip;
                fi
                sum_even(LOC[local_mem_idx], GLOB[tile_idx + global_offset])
                long_work(GMT)
            }
            if
            :: (wg_iter+1) >= tuning.wgSize / PEX_PER_UNIT -> pex_u ! EOI; break;
            :: else -> pex_u ! NEOI;
            fi;
        od;

        :: 	u_pex ? 0, STOP ->
            if
            :: id == 0 ->
                for (tile_idx : 1..(service.count_elements-1)) { // REDUCE local
                    sum(LOC[unit_id * service.count_elements],LOC[tile_idx + unit_id * service.count_elements]) // access to local memory
                    service.time++;
                }
                // copy the result of this working group to global memory
                atomic {
                    GLOB[0] = 0;
                    service.time = service.time + GMT;
                    sum(GLOB[0],LOC[unit_id * service.count_elements])
                    service.time = service.time + GMT;
                }
                service.final = true;
            :: else -> skip;
            fi
            break;
    od;
}

proctype unit (byte id; chan dev_u; chan u_dev) {
    byte proc_idx; 		 		// process index
    byte wg_iter;		 		// the current iteration within a workgroup when the number of processors is less than the size of the workgroup
    byte wg_id;			 		// work group number (assigned work group to complete the task)
    byte proc_count;	 		// process count in the workgroup (how many processes were used in the current iteration)
    mtype : Action done_flag;	// message from the process about completion (for example, EOI - end of iteration)

    chan pex_u = [0] of {mtype : Action};
    chan u_pex = [0] of {byte, mtype : Action};

    xr pex_u;
    xs u_pex;

    atomic { for (proc_idx : 0..service.count_elements-1) { run pex(proc_idx, id, pex_u, u_pex); } }

    do
    :: dev_u ? wg_id, GO ->
        atomic{ for (proc_idx : 0..service.count_elements-1) { u_pex ! wg_id, GOWG; u_pex ! 0, GO; } }
        if
        :: tuning.wgSize <= PEX_PER_UNIT ->
            atomic{ for (proc_idx : 0..service.count_elements-1) { pex_u ? EOI;} }
        :: else ->
            wg_iter = 1;
            proc_count = 0;
            for (proc_idx : 0..(tuning.wgSize - PEX_PER_UNIT - 1)) {
                atomic{
                    pex_u ? done_flag;
                    if
                    :: done_flag == EOI -> skip;
                    :: else -> u_pex ! wg_iter, GO;
                    fi
                    proc_count++;
                    if
                    :: proc_count >= PEX_PER_UNIT -> wg_iter++; proc_count = 0;
                    :: else -> skip;
                    fi
                }
            }
            for (proc_idx : 0..(service.count_elements-1)) { pex_u ? EOI; }
        fi;
        u_dev ! DONE;
        :: dev_u ? 0, STOP ->
        atomic { for (proc_idx : 0..service.count_elements-1) { u_pex ! 0, STOP; } }
        break;
    od;
}

proctype device (chan d_hst; chan hst_d) {
    byte unit_idx;								// Unit index
    byte wg_count;								// Counter of running workgroups on the device
    byte wg_id;									// number of the work group that is sent for execution
    chan dev_u = [0] of {byte, mtype : Action};	// a communication channel with units, which is used to transmit commands to the unit
    chan u_dev = [0] of {mtype : Action};		// a communication channel with units to receive messages about the completion of work

    xr u_dev;
    xs dev_u;

    atomic { for (unit_idx : 0..service.count_units-1) { run unit (unit_idx, dev_u, u_dev); } }
    do
    :: hst_d ? GO ->
        dev_u ! 0, GO;
        if
        :: tuning.wgCount <= UNIT_PER_DEVICE ->
            atomic { u_dev ? DONE; service.count_all_elements = service.count_all_elements - service.count_elements; }
        :: else ->
            wg_id = 1;
            wg_count = 0;
            for (unit_idx : 0..tuning.wgCount-2) {
                atomic {
                    u_dev ? DONE;
                    dev_u ! wg_id,GO;
                    wg_id++; wg_count = 0;
                }
            }
            atomic { u_dev ? DONE; service.count_all_elements = service.count_all_elements - service.count_elements; }
        fi;
        d_hst ! DONE;
    :: hst_d ? STOP -> dev_u ! 0, STOP;
    break;
    od;
}

proctype host () {
    chan d_hst = [0] of {mtype : Action};
    chan hst_d = [0] of {mtype : Action};

    xr d_hst; //  remove cuz we use it in atomic ?
    xs hst_d;

    service.final = false;
    run device (d_hst, hst_d);
    hst_d ! GO;
    atomic { d_hst ? DONE; hst_d ! STOP; }
}

#endif // __GPU_PML__
