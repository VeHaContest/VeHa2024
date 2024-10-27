
#ifndef __FUNCTION_PML__
#define __FUNCTION_PML__

#include "global.pml"

inline sum_even(a, b) {
	atomic {
		if
		:: b % 2 == 0 -> a = a + b;
		:: else -> skip;
		fi
	}
}

inline sum(a, b) {
	atomic {
		a = a + b;
	}
}

inline work_step() {
 atomic { cur_time = service.time;
	  service.count_pex++;
	  service.time == cur_time + 1; 
	}
}
inline long_work (fct) {
    do  
    :: service.time > start_time + fct * tuning.tileSize -> break;
    :: else ->  work_step()
    od;
}

proctype clock () { 
	do 
	:: service.final -> break;
	:: service.count_pex == service.count_all_elements && service.count_all_elements != 0 -> atomic { service.count_pex = 0; service.time++; }
	od;
}

#endif // __FUNCTION_PML__
