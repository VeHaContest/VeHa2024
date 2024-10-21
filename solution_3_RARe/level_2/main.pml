#include "modules/gpu_model.pml"

active proctype main() { 
  byte i;
  //  DATA 
  for (i : 0 .. SIZE_INPUT_DATA-1)  { GLOB[i] = SIZE_INPUT_DATA - i }
  for (i : 0 .. LOCAL_MEMORY*UNIT_PER_DEVICE-1) { LOC[i] = 0 }

  for (i : 0 .. UNIT_PER_DEVICE*WARP_PER_UNIT-1) { WARP_READY[i] = true }

  // tuning.wgSize selection
  select ( i : 2 .. DATA_SIZE-1 );  
  tuning.wgSize = SIZE_INPUT_DATA >> (DATA_SIZE - i); // Thread block = several warps
  // Tile SIZE_INPUT_DATA selection
  select ( i : 1 .. DATA_SIZE-1 ); 
  tuning.tileSize = SIZE_INPUT_DATA >> (DATA_SIZE - i);
  tuning.tileSize = (tuning.wgSize*tuning.tileSize > SIZE_INPUT_DATA -> SIZE_INPUT_DATA / tuning.wgSize : tuning.tileSize); 

  tuning.wgCount = SIZE_INPUT_DATA / (tuning.wgSize * tuning.tileSize); 						// the number of working groups
  service.count_devices = ( tuning.wgCount <= UNIT_PER_DEVICE * DEVICE_NUMBER -> (tuning.wgCount / UNIT_PER_DEVICE) : DEVICE_NUMBER ); 	// the number of working devices 
  service.count_devices = (tuning.wgCount / UNIT_PER_DEVICE -> service.count_devices : 1); 				// if tuning.wgCount <= UNIT_PER_DEVICE 
  service.count_units = ( tuning.wgCount <= UNIT_PER_DEVICE -> tuning.wgCount : UNIT_PER_DEVICE ); // the number of working units
  // service.count_warp = ( tuning.wgCount <= WARP_PER_UNIT -> tuning.wgSize : WARP_PER_UNIT); 			// the number of working warp
  service.count_warp = WARP_PER_UNIT
  service.count_elements = ( tuning.wgSize <= PEX_PER_UNIT -> tuning.wgSize : PEX_PER_UNIT); 			// the number of working elements

  service.count_all_elements = service.count_elements * service.count_units * service.count_devices;  

  atomic{ run host(); run clock(); }
}

ltl Timeout {[]!timeout } 
ltl Fin {<> service.final }
ltl CorrectSum {[](service.final -> (<>(GLOB[0] == 72)) )}
ltl NonTerm {[]!service.final }
ltl OverTime {[]( service.final -> (service.time > T_MIN)) }
