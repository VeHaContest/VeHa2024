
#ifndef __GLOBAL_PML__
#define __GLOBAL_PML__

#include "config.pml"

#define T_MIN 10

// hardware parameters
#define PEX_PER_UNIT 4		// 2^m -- the number of processing elements per unit --- COREs --
#define UNIT_PER_DEVICE 1		// the number of units per device --- SMs
#define DEVICE_NUMBER 1		// the number of devices --- GPCs
#define GMT 4 		// the service.time of computations using the global memory
#define LOCAL_MEMORY 8		// the SIZE_INPUT_DATA of local memory

// input
#define DATA_SIZE 4			// SIZE_INPUT_DATA = 2^DATA_SIZE -- data SIZE_INPUT_DATA
#define SIZE_INPUT_DATA 16 	// the SIZE_INPUT_DATA of the input data

int GLOB[SIZE_INPUT_DATA];	// input data -- array of integers -- global memory. Also used for result SUM
int LOC[LOCAL_MEMORY * UNIT_PER_DEVICE]	// local memory

ServiceVars service;
TuningParameters tuning;

#endif // __GLOBAL_PML__
