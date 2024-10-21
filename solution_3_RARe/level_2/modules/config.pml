#ifndef __CONFIG_PML__
#define __CONFIG_PML__

typedef ServiceVars {
    byte count_pex = 0;	            // the number of working running processing elements
    byte count_devices = 0;		    // number of work devices
    byte count_units = 0;		    // number of work units
    byte count_elements = 0;		// number of work elements
    byte count_warp = 0;		    // number of work warp
    byte count_all_elements = 0;	// number of all work elements
    int time = 0;
    int final = false;
}

mtype : Action = { DONE, STOP, GO, GOWG, EOI, NEOI, EOW };

typedef TuningParameters {
    int wgSize = 0;			        // the SIZE_INPUT_DATA of the workgroup 
    int wgCount = 0;		        // the number of the workgroups 
    int tileSize = 0; 		        // the tile SIZE_INPUT_DATA 
}

#endif // __CONFIG_PML__
