/**********************************************************************
 *  Please be reminded that the C plugins are only meant for 
 *
 *                      FORWARD ANALYSIS. 
 *
 *  The reason is that C does not come with an intrinsic backward 
 *  execution module. 
 *  All C plugins in a model with backward analysis, 
 *  including model-checking, 
 *  simulation-checking will be ignored. 
 */
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include <limits.h> 

#include "redlib.h"  
#include "redlib.e"  

int	cplugin_proc(
  int	module_index, 
  int	proc_index
) { 
  switch(module_index) { 
  case 1: 
    break; 
  case 2: 
    break; 
  case 3: 
    switch (proc_index) { 
    case 1: 
      break; 
    case 2: 
      break; 
    case 3: 
    
      break; 
    default: 
      fprintf(RED_OUT, "\nCPLUG-INs module %1d: Illegal proc index %1d.\n", 
        module_index, proc_index
      ); 
      fflush(RED_OUT); 
      exit(0);  
    } 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nCPLUG-INs: Illegal module index %1d.\n", module_index
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}
  /* cplugin_proc() */ 



