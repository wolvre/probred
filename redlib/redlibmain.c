/******************************************************************
In the implementation of the redlib, to dynamically support 
both model-checking and bisimulation-checking, 
we need two sets of sync xtion structures. 
The 1st is for model-checking while the second is for bisimulation-checking. 
Thus we need two flags to show whether these two sets are ready. 
A set is not constructed unless it is called for execution. 

No internal data structures and constants may be directly used. 
All constant mapping from users' side to the internal side are done with 
two procedures. 

  switch_reachable_utilities() and reset_reachable_utilities(). 

*/

#include <stdio.h>
#include <stdlib.h>
/*
#include <unistd.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
*/
#include <limits.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <float.h>
#include <stdarg.h> 

#include "redbasics.h"
#include "redbasics.e"

#include "redparse.h"
#include "redparse.e"

#include "vindex.e"

#include "redbop.h"
#include "redbop.e"
#include "hybrid.e"

#include "fxp.h"
#include "fxp.e"

#include "counter.e"

#include "zone.h"  
#include "zone.e" 

#include "zapprox.e"


#include "redgram.e" 

#include "exp.e" 

#include "redstring.e" 

#include "treeman.h"
#include "treeman.e"

#include "hashman.h" 
#include "hashman.e" 

#include "redsymmetry.e"

#include "action.e"

#include "inactive.e"

#include "coverage.e"

#include "bisim.h" 
#include "bisim.e" 

#include "redgame.h" 
#include "redgame.e" 

#include "access_analysis.e" 

#include "redlib.h" 

#include "tctctl.e" 



#define	MASK_REDLIB_INPUT_MODE			4 
#define	FLAG_REDLIB_INPUT_ONLINE		4
#define	FLAG_REDLIB_INPUT_FILE			0

/* The phase heirarchy is as follows. 
 *
 *   bottom 
 *   SESSION_IDLE -+--> MODEL_INPUT -+--> VAR_DECLARING
 *                 |                 |
 *                 |                 +--> MODE_DECLARING ----> XTION_DECLARING
 *                 |                 |
 *                 |                 +--> INITIAL_DECLARING
 *                 |                 |
 *                 |                 +--> SPEC_DECLARING 
 *                 |                 |
 *                 |                 +--> FILE_INPUT 
 *                 +--> PARSING 
 *                 +--> PARSING_RULES
 *                 |
 *                 +--> ANALYSIS 
 *                 | 
 *                 +--> VERIFICATION 
 *
 *  The coding of the phase flags is to show the levels of the phases. 
 
 */
#define	FLAG_REDLIB_PHASE_SESSION_IDLE		(0x0000)
#define	FLAG_REDLIB_PHASE_MODEL_INPUT		(0x0010)
#define	FLAG_REDLIB_PHASE_VAR_DECLARING		(0x0110)
#define	FLAG_REDLIB_PHASE_MODE_DECLARING	(0x0210)
#define	FLAG_REDLIB_PHASE_XTION_DECLARING	(0x1210)
#define	FLAG_REDLIB_PHASE_INITIAL_DECLARING	(0x0310)
#define	FLAG_REDLIB_PHASE_SPEC_DECLARING	(0x0410)
#define	FLAG_REDLIB_PHASE_FILE_INPUT		(0x0510)
#define	FLAG_REDLIB_PHASE_PARSING		(0x0030)
#define	FLAG_REDLIB_PHASE_PARSING_RULES		(0x0130)
#define	FLAG_REDLIB_PHASE_ANALYSIS		(0x0040) 
#define	FLAG_REDLIB_PHASE_VERIFICATION		(0x0050) 

#define LIMIT_PHASE_REDLIB	100 
int	phase_redlib[100] = {FLAG_REDLIB_PHASE_SESSION_IDLE}, 
	TOP_PHASE = 0; 
	
int 	SESS_PROC_COUNT; 

char	*SESS_NAME_FOR_FILE, 
	*SESS_NAME_ORIGINAL, 
	*model_file_name,  
	*REDLIB_ROLE_STRING; 

FILE	*model_template_file; 

int			*cube_child_index, top_cube_child; 
struct red_type		*target_cube_set; 





struct string_link_type	{ 
  int				len; 
  char				*string; 
  struct string_link_type	*next_string_link; 
} 
  dummy_string_list, *string_tail; 

int	count_strings = 0, string_total_length = 0; 

/*********************************************************************
 *  The following three routines are for the construction of 
 *  parametric strings with variable-length arguments. 
 */
void	red_begin_string(char *f, ...) { 
  char				*real_f; 
  va_list			args; 
  struct string_link_type	*sl, *sl_tmp; 
  int				len; 
  
  if (count_strings > 0) { 
    for (sl = dummy_string_list.next_string_link; 
         sl; 
         free(sl->string), sl_tmp = sl, 
         sl = sl->next_string_link, free(sl_tmp)	
         ) ; 
  } 
  string_total_length = 0; 
  count_strings = 0; 
  dummy_string_list.next_string_link = NULL; 
  
  string_var(real_f, NULL, NULL, f, args); 
  
  len = strlen(real_f); 
  count_strings = 1; 
  dummy_string_list.next_string_link 
  = string_tail 
  = (struct string_link_type *) malloc(sizeof(struct string_link_type)); 
  string_tail->string = (char *) malloc(len + 1); 
  string_tail->len = len; 
  string_total_length = len; 
  
  sprintf(string_tail->string, "%s", real_f); 
  string_tail->next_string_link = NULL; 
}
  /* red_begin_string() */ 
  
  
void	red_concat_string(char *f, ...) { 
  char				*real_f; 
  va_list			args; 
  struct string_link_type	*sl; 
  int				len; 
  
  if (count_strings <= 0) { 
    count_strings = 0; 
    dummy_string_list.next_string_link = NULL; 
    string_tail = &dummy_string_list; 
  } 
  
  string_var(real_f, NULL, NULL, f, args); 
  
  len = strlen(real_f); 
  count_strings++; 
  sl = (struct string_link_type *) malloc(sizeof(struct string_link_type)); 
  sl->string = (char *) malloc(len + 1); 
  sl->len = len; 
  string_total_length = string_total_length + len; 
  
  sprintf(sl->string, "%s", real_f); 
  string_tail->next_string_link = sl; 
  sl->next_string_link = NULL; 
  string_tail = sl; 
}
  /* red_concat_string() */ 
  
  
char	*red_finalize_string() { 
  struct string_link_type	*sl, *sl_tmp; 
  int				pos; 
  
  if (inbuf_size < string_total_length + 3) { 
    free(inbuf); 
    inbuf_size = 2*inbuf_size; 
    if (inbuf_size < string_total_length + 3) 
      inbuf_size = string_total_length + 3; 
    inbuf = (char *) malloc(inbuf_size); 	
  } 
  pos = 0; 
  for (sl = dummy_string_list.next_string_link; 
       sl; 
       sl_tmp = sl, sl = sl->next_string_link, free(sl_tmp) 
       ) { 
    sprintf(&(inbuf[pos]), "%s", sl->string); 
    free(sl->string); 
    pos = pos + sl->len;   	
  } 
  sprintf(&(inbuf[pos]), "\0\0"); 
  dummy_string_list.next_string_link = NULL; 
  count_strings = 0; 
  string_total_length = 0; 
  
  return(inbuf); 
} 
  /* red_finalize_string() */ 
  



#define INDEX_FLAG_TASK			1
#define INDEX_FLAG_PARAMETRIC_ANALYSIS	2 
#define INDEX_FLAG_GAME_ROLES		3 
#define INDEX_FLAG_FULL_REACHABILITY	4 
#define INDEX_FLAG_COUNTER_EXAMPLE	5 
#define INDEX_FLAG_TIME_PROGRESS	6 
#define INDEX_FLAG_NORMALITY		7 
#define INDEX_FLAG_ACTION_APPROX	8 
#define INDEX_FLAG_REDUCTION		9 
#define INDEX_FLAG_STATE_APPROX		10 
#define INDEX_FLAG_SYMMETRY		11 
#define INDEX_FLAG_ZENO			12 
#define INDEX_FLAG_PRINT		13 


int	red_flag_conversion(int index_flag, int redlib_flag) {
  int	wflag; 
  
  switch (index_flag) { 
  case INDEX_FLAG_TASK: 
    switch (redlib_flag) { 
    case RED_TASK_SAFETY: 
      return(TASK_SAFETY); 
      break; 
    case RED_TASK_RISK: 
      return(TASK_RISK); 
      break; 
    case RED_TASK_GOAL: 
      return(TASK_GOAL); 
      break; 
    case RED_TASK_ZENO: 
      return(TASK_ZENO); 
      break; 
    case RED_TASK_DEADLOCK: 
      return(TASK_DEADLOCK); 
      break; 
    case RED_TASK_MODEL_CHECK:  
      return(TASK_MODEL_CHECK); 
      break; 
    case RED_TASK_SIMULATE:  
      return(TASK_SIMULATE); 
      break; 
    case RED_TASK_BRANCH_SIM_CHECK: 
      return(TASK_BRANCHING_SIM_CHECKING); 
      break; 
    case RED_TASK_BRANCH_BISIM_CHECK: 
      return(TASK_BRANCHING_BISIM_CHECKING); 
      break;   
    }
    break; 
    
  case INDEX_FLAG_PARAMETRIC_ANALYSIS: 
    switch (redlib_flag) {
    case RED_PARAMETRIC_ANALYSIS: 
      return(FLAG_PARAMETRIC_ANALYSIS); 
      break; 
    case RED_NO_PARAMETRIC_ANALYSIS: 
      return(0); 
      break; 
    }
    break; 
  
  case INDEX_FLAG_GAME_ROLES: 
    wflag = 0; 
    if (redlib_flag & RED_GAME_MODL) 
      wflag = wflag | FLAG_GAME_MODL; 

    if (redlib_flag & RED_GAME_SPEC) 
      wflag = wflag | FLAG_GAME_SPEC; 

    if (redlib_flag & RED_GAME_ENVR) 
      wflag = wflag | FLAG_GAME_ENVR; 
    return(wflag); 
      
  case INDEX_FLAG_FULL_REACHABILITY: 
    switch (redlib_flag) {
    case RED_FULL_REACHABILITY: 
      return(FLAG_FULL_REACHABILITY); 
      break; 
    case RED_NO_FULL_REACHABILITY: 
      return(0); 
      break; 
    } 
    break; 
  
  case INDEX_FLAG_COUNTER_EXAMPLE: 
    switch (redlib_flag) { 
    case RED_COUNTER_EXAMPLE: 
      return(FLAG_COUNTER_EXAMPLE); 
      break; 
    case RED_NO_COUNTER_EXAMPLE: 
      return(0); 
      break; 
    } 
    break; 
    
  case INDEX_FLAG_TIME_PROGRESS: 
    switch (redlib_flag) { 
    case RED_TIME_PROGRESS: 
      return(FLAG_TIME_PROGRESS); 
      break; 
    case RED_NO_TIME_PROGRESS: 
      return(0); 
      break; 
    } 
    break; 
  case INDEX_FLAG_NORMALITY: 
    switch (redlib_flag) { 
    case RED_NORM_ZONE_NONE: 
      return(FLAG_NORM_ZONE_NONE); 
      break; 
    case RED_NORM_ZONE_MAGNITUDE_REDUCED: 
      return(FLAG_NORM_ZONE_MAGNITUDE_REDUCTION); 
      break; 
    case RED_NORM_ZONE_CLOSURE: 
      return(FLAG_NORM_ZONE_CLOSURE); 
      break; 
    case RED_NORM_ZONE_CLOSURE_EQ: 
      return(FLAG_NORM_ZONE_CLOSURE_EQ); 
      break; 
    case RED_NORM_ZONE_MAGNITUDE_ONE_RIPPLE: 
      return(FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE); 
      break; 
    }
    wflag = 0;   
    if (redlib_flag & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD) 
      wflag = wflag | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD; 
    if (redlib_flag & RED_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD) 
      wflag = wflag | FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD; 
    if (redlib_flag & RED_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD) 
      wflag = wflag | FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD; 
    if (redlib_flag & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD) 
      wflag = wflag | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD;
    if (redlib_flag & RED_NORM_HYBRID_PROOF_OBLIGATIONS) 
      wflag = wflag | FLAG_NORM_HYBRID_PROOF_OBLIGATIONS;  
    return(wflag); 
  
  case INDEX_FLAG_ACTION_APPROX: 
    switch (redlib_flag) { 
    case RED_NO_ACTION_APPROX: 
      return(FLAG_NO_ACTION_APPROX); 
      break; 
    case RED_ACTION_APPROX_NOXTIVE: 
      return(FLAG_ACTION_APPROX_NOXTIVE); 
      break;  
    case RED_ACTION_APPROX_UNTIMED: 
      return(FLAG_ACTION_APPROX_UNTIMED); 
      break; 
    } 
    break; 
  case INDEX_FLAG_REDUCTION: 
    switch (redlib_flag) { 
      return(FLAG_NO_REDUCTION_INACTIVE); 
      break; 
    case RED_REDUCTION_INACTIVE_NOXTIVE: 
      return(FLAG_REDUCTION_INACTIVE_NOXTIVE); 
      break; 
    case RED_REDUCTION_INACTIVE: 
      return(FLAG_REDUCTION_INACTIVE); 
      break; 
    } 
    break; 
  
  case INDEX_FLAG_STATE_APPROX: 
    switch (redlib_flag & RED_MASK_APPROX) { 
    case RED_NOAPPROX: 
      return(FLAG_ROOT_NOAPPROX); 
      break; 
    case RED_UAPPROX: 
      return(FLAG_ROOT_UAPPROX); 
      break; 
    case RED_OAPPROX: 
      wflag = FLAG_ROOT_OAPPROX; 
      switch (redlib_flag & RED_MASK_OAPPROX_STRATEGY) { 
      case RED_OAPPROX_STRATEGY_GAME: 
        wflag = wflag | FLAG_OAPPROX_STRATEGY_GAME; 
        switch (redlib_flag & MASK_OAPPROX_SPEC_GAME) { 
        case RED_NOAPPROX_SPEC_GAME: 
          wflag = wflag | FLAG_NOAPPROX_SPEC_GAME; 
          break;  
        case RED_OAPPROX_SPEC_GAME_DIAG_MAG:
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_DIAG_MAG;
          break;  
        case RED_OAPPROX_SPEC_GAME_DIAGONAL: 
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_DIAGONAL; 
          break;  
        case RED_OAPPROX_SPEC_GAME_MAGNITUDE:
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE;
          break;  
        case RED_OAPPROX_SPEC_GAME_UNTIMED: 
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_UNTIMED; 
          break;  
        case RED_OAPPROX_SPEC_GAME_MODE_ONLY: 
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_MODE_ONLY;
          break;  
        case RED_OAPPROX_SPEC_GAME_NONE: 
          wflag = wflag | FLAG_OAPPROX_SPEC_GAME_NONE;
          break;  
        }     
    
        switch (redlib_flag & MASK_OAPPROX_MODL_GAME) { 
        case RED_NOAPPROX_MODL_GAME: 
          wflag = wflag | FLAG_NOAPPROX_MODL_GAME; 
          break;  
        case RED_OAPPROX_MODL_GAME_DIAG_MAG:
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_DIAG_MAG; 
          break;  
        case RED_OAPPROX_MODL_GAME_DIAGONAL:
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_DIAGONAL; 
          break;  
        case RED_OAPPROX_MODL_GAME_MAGNITUDE:
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_MAGNITUDE; 
          break;  
        case RED_OAPPROX_MODL_GAME_UNTIMED:
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_UNTIMED;
          break;  
        case RED_OAPPROX_MODL_GAME_MODE_ONLY:
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_MODE_ONLY; 
          break;  
        case RED_OAPPROX_MODL_GAME_NONE: 
          wflag = wflag | FLAG_OAPPROX_MODL_GAME_NONE;
          break;  
        }

        switch (redlib_flag & MASK_OAPPROX_ENVR_GAME) {
        case RED_NOAPPROX_ENVR_GAME:
          wflag = wflag | FLAG_NOAPPROX_ENVR_GAME;
          break;  
        case RED_OAPPROX_ENVR_GAME_DIAG_MAG:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_DIAG_MAG; 
          break;  
        case RED_OAPPROX_ENVR_GAME_DIAGONAL:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_DIAGONAL; 
          break;  
        case RED_OAPPROX_ENVR_GAME_MAGNITUDE:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_MAGNITUDE;
          break;  
        case RED_OAPPROX_ENVR_GAME_UNTIMED:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_UNTIMED;
          break;  
        case RED_OAPPROX_ENVR_GAME_MODE_ONLY:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_MODE_ONLY; 
          break;  
        case RED_OAPPROX_ENVR_GAME_NONE:
          wflag = wflag | FLAG_OAPPROX_ENVR_GAME_NONE;
          break;  
        }

        switch (redlib_flag & MASK_OAPPROX_GLOBAL_GAME) {
        case RED_NOAPPROX_GLOBAL_GAME:
          wflag = wflag | FLAG_NOAPPROX_GLOBAL_GAME; 
          break;  
        case RED_OAPPROX_GLOBAL_GAME_DIAG_MAG:
          wflag = wflag | FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG; 
          break;  
        case RED_OAPPROX_GLOBAL_GAME_DIAGONAL:
          wflag = wflag | FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL;
          break;  
        case RED_OAPPROX_GLOBAL_GAME_MAGNITUDE:
          wflag = wflag | FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE; 
          break;  
        case RED_OAPPROX_GLOBAL_GAME_UNTIMED:
          wflag = wflag | FLAG_OAPPROX_GLOBAL_GAME_UNTIMED;
          break;  
        case RED_OAPPROX_GLOBAL_GAME_NONE: 
          wflag = wflag | FLAG_OAPPROX_GLOBAL_GAME_NONE;
          break;  
        }
        break; 
      } // switch (redlib_flag & RED_MASK_OAPPROX_STRATEGY) 
      break; 
    } //  switch (redlib_flag & RED_MASK_APPROX) { 
    return(wflag); 
    break; 
    
  case INDEX_FLAG_SYMMETRY: 
    switch (redlib_flag) { 
    case RED_NO_SYMMETRY: 
      return(0); 
      break; 
    
    case RED_SYMMETRY_ZONE: 
      return(FLAG_SYMMETRY_ZONE); 
      break; 
    case RED_SYMMETRY_DISCRETE: 
      return(FLAG_SYMMETRY_DISCRETE_GENERAL);  
      break; 
    case RED_SYMMETRY_POINTER: 
      return(FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE); 
      break; 
    case RED_SYMMETRY_STATE: 
      return(FLAG_SYMMETRY_STATE); 
      break; 
    } 
    break; 
    
  case INDEX_FLAG_ZENO: 
    switch (redlib_flag) { 
    case RED_PLAIN_NONZENO: 
      return(FLAG_USE_PLAIN_NONZENO); 
      DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
      break; 
    case RED_APPROX_NONZENO: 
      return(FLAG_USE_APPROX_NONZENO); 
      DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
      break; 
    case RED_ZENO_TRACES_OK:  
      return(FLAG_ZENO_CYCLE_OK); 
      DISTANCE_ZENO = 0; 
      break; 
    }
  
  case INDEX_FLAG_PRINT: 
    return(0); 
  } 	
}
  /* red_flag_conversion() */ 
  
  



void	red_switch_output(FILE *out) {
  RED_OUT = out; 	
}
  /* red_switch_output() */  
  
  
  
char	*red_file_to_string(f) 
	char	*f; 
{ 
  return(file_to_string(f)); 
} 
  /* red_file_to_string(f) */  


/* Return the name of each phase
 */ 
char	*phase_name(pi)  
	int	pi; 
{ 
  switch (pi) { 
  case FLAG_REDLIB_PHASE_SESSION_IDLE: 
    return("IDLE"); 
  case FLAG_REDLIB_PHASE_MODEL_INPUT: 
    return("MODEL_INPUT"); 
  case FLAG_REDLIB_PHASE_VAR_DECLARING: 
    return("VAR_DECLARING"); 
  case FLAG_REDLIB_PHASE_MODE_DECLARING: 
    return("MODE_DECLARING"); 
  case FLAG_REDLIB_PHASE_XTION_DECLARING: 
    return("XTION_DECLARING"); 
  case FLAG_REDLIB_PHASE_INITIAL_DECLARING:
    return("INITIAL_DECLARING"); 
  case FLAG_REDLIB_PHASE_SPEC_DECLARING: 
    return("SPEC_DECLARING"); 
  case FLAG_REDLIB_PHASE_FILE_INPUT: 
    return("FILE_INPUT"); 
  case FLAG_REDLIB_PHASE_PARSING: 
    return("PARSING"); 
  case FLAG_REDLIB_PHASE_ANALYSIS: 
    return("ANALYSIS"); 
  case FLAG_REDLIB_PHASE_VERIFICATION: 
    return("VERIFICATION"); 
  } 
}
  /* phase_name() */  
  



int	top_redlib_phase() { 
  return(phase_redlib[TOP_PHASE]); 
}
  /* top_redlib_phase() */ 
  

void	print_phase_stack() { 
  int	i; 
  
  for (i = TOP_PHASE; i > 0; i--) 
    fprintf(RED_OUT, "%1d:%1d:%s-->", 
            i, phase_redlib[i], phase_name(phase_redlib[i])
            );  
  fprintf(RED_OUT, "0:%1d:%s", phase_redlib[0], phase_name(phase_redlib[0])); 
  fprintf(RED_OUT, "\n"); 
}
  /* print_phase_stack() */ 
  
  
void	push_redlib_phase(p) 
	int	p; 
{ 
  phase_redlib[++TOP_PHASE] = p;   
/*
  fprintf(RED_OUT, "push a phase %1d:%s at frame %1d\n", 
          p, phase_name(p), TOP_PHASE
          ); 
  print_phase_stack(); 
*/
} 
  /* push_redlib_phase() */ 
  
  
  
void	change_redlib_phase(p) 
	int	p; 
{ 
/*
  fprintf(RED_OUT, "change to a phase %1d:%s at frame %1d\n", 
          p, phase_name(p), TOP_PHASE
          ); 
*/
  phase_redlib[TOP_PHASE] = p; 
/*
  print_phase_stack(); 
*/
}
  /* change_redlib_phase() */ 
  
  

void	pop_redlib_phase() 
{ 
  if (TOP_PHASE <= 0) { 
    fprintf(RED_OUT, "Error: a push operation to an empty phase stack.\n"); 
    exit(0); 
  }
  TOP_PHASE--; 
/*
  fprintf(RED_OUT, "pop a phase %1d:%s at frame %1d\n", 
          top_redlib_phase(), phase_name(top_redlib_phase()), TOP_PHASE
          ); 
  print_phase_stack(); 
*/
}
  /* pop_redlib_phase() */ 

  
int	check_phase(phase, caller_name) 
	int	phase; 
	char	*caller_name; 
{ 
/*
  printf("In redlib check phase for caller %s at phase %1d\n", caller_name, phase); 
  fflush(stdout); 
*/  
  if (top_redlib_phase() != phase) { 
    switch (phase) { 
    case FLAG_REDLIB_PHASE_SESSION_IDLE: 
      printf("\n\nError 0: Starting REDLIB session from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_MODEL_INPUT: 
      printf("\n\nError 1: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      bk(0); 
      exit(0); 
    case FLAG_REDLIB_PHASE_VAR_DECLARING: 
      printf("\n\nError 4: Attempt to declare variables from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_MODE_DECLARING: 
      printf("\n\nError 5: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      bk(0); 
      exit(0); 

    case FLAG_REDLIB_PHASE_XTION_DECLARING: 
      printf("\n\nError 6: Attempt to declare a transition from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_INITIAL_DECLARING:
      printf("\n\nError 7: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_SPEC_DECLARING: 
      printf("\n\nError 8: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_FILE_INPUT: 
      printf("\n\nError 9: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_PARSING: 
      printf("\n\nError 10: Attempt to parse syntax from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_ANALYSIS: 
      printf("\n\nError 11: Attempt to use model construction procedures from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_VERIFICATION: 
      printf("\n\nError 12: Attempt to use model construction procedures from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 
    }
  } 
} 
  /* check_phase() */  
  



int	check_phase_above(phase, caller_name) 
	int	phase; 
	char	*caller_name; 
{ 
/*
  printf("In redlib check phase for caller %s at phase %1d\n", caller_name, phase); 
  fflush(stdout); 
*/  
  if (top_redlib_phase() < phase) { 
    switch (phase) {                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    case FLAG_REDLIB_PHASE_SESSION_IDLE: 
      printf("\n\nError 0a: Starting REDLIB session from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase()) 
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_MODEL_INPUT: 
      printf("\n\nError 1a: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      print_phase_stack(); 
      bk(0); 
      exit(0); 

    case FLAG_REDLIB_PHASE_VAR_DECLARING: 
      printf("\n\nError 4a: Attempt to declare variables from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_MODE_DECLARING: 
      printf("\n\nError 5a: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_XTION_DECLARING: 
      printf("\n\nError 6a: Attempt to declare a transition from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_INITIAL_DECLARING:
      printf("\n\nError 7a: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_SPEC_DECLARING: 
      printf("\n\nError 8a: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_FILE_INPUT: 
      printf("\n\nError 9a: Attempt to declare a mode from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_PARSING: 
      printf("\n\nError 10a: Attempt to parse syntax from %s while in phase %s. \n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_ANALYSIS: 
      printf("\n\nError 11a: Attempt to use model construction procedures from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 

    case FLAG_REDLIB_PHASE_VERIFICATION: 
      printf("\n\nError 12a: Attempt to use model construction procedures from %s while in phase %s.\n", 
	     caller_name, phase_name(top_redlib_phase())
	     ); 
      exit(0); 
    }
  }
  return(TYPE_TRUE); 
} 
  /* check_phase_above() */  
  

check_mi(mi, pname) 
	int 	mi; 
	char	*pname; 
{ 
  if (mi < 0 || mi >= MODE_COUNT) { 
    printf("\nError: Illegal mode index %1d in %s().\n", mi, pname); 
    exit(0); 	
  } 
  return(TYPE_TRUE); 
}
  /* check_mi() */ 
  

check_pi(pi, pname) 
	int	pi; 
	char	*pname; 
{ 
  if (pi < 1 || pi > PROCESS_COUNT) { 
    printf("\nError: Illegal process index %1d in %s().\n", pi, pname); 
    exit(0); 
  } 
  return(TYPE_TRUE); 
}
  /* check_pi() */
  
  
check_vi(vi, pname) 
	int	vi; 
	char	*pname; 
{ 
  if (vi < 0 || vi >= VARIABLE_COUNT) {
    printf("\nError: illegal variable index %1d accessed in %s().\n", vi, pname); 	
    exit(0); 
  }
  return(TYPE_TRUE); 
}
  /* check_vi() */ 
  

check_xi(xi, pname) 
	int	xi; 
	char	*pname; 
{ 
  if (xi >= XTION_COUNT || xi < 0) { 
    printf("\nError: Illegal declared transition index %1d in %s().\n", 
           xi, pname
           ); 
    exit(0); 
  } 
  return(TYPE_TRUE); 
}
  /* check_xi() */ 
  
  
  
int	check_sxi(
  int	sxi, 
  int	flag_sync_xtion_table_choice, 
  char	*pname
) { 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi > SYNC_XTION_COUNT || sxi < 0) { 
      printf("\nError: Illegal synchronous transition index %1d in %s().\n", 
             sxi, pname
             ); 
      exit(0); 
  } } 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    if (sxi > SYNC_XTION_COUNT_GAME || sxi < 0) { 
      printf("\nError: Illegal game synchronous transition index %1d in %s().\n", 
             sxi, pname
             ); 
      exit(0); 
    } 
  }
  return(TYPE_TRUE); 
}
  /* check_sxi() */ 
  
  
  
  
  
  
char    *red_diagram_string(
	redgram	d
	) { 
  return(string_diagram(d)); 
} 
  /* red_diagram_string() */  
  
  
  
  
int red_diagram_size(
	redgram	d, 
	int	*node_count_ptr, 
	int	*arc_count_ptr 
	) {
  int	size; 
  
  size = red_size(d, SIZE_SILENT, node_count_ptr, arc_count_ptr); 
  
  return(size); 
}
  /* red_diagram_size() */  
  
  

int red_diagram_cube_count(d) 
	redgram	d; 
{
  return(red_path_count(d)); 
} 
  /* red_diagram_cube_count() */ 
  
  
int	red_diagram_discrete_model_count(d) 
	redgram	d; 
{ 
  return(red_discrete_model_count(d)); 	
}
  /* red_diagram_discrete_model_count() */ 
  
    
  
int red_diagram_space(d) 
	redgram	d; 
{ 
  return (size_space(1, &d)); 	
}
  /* red_diagram_space() */   
  
  
    
/* This procedure starts a session of red verification task. 
 * It checks the phase stack and set the initial phase stack contents 
 * to the bottom with value FLAG_REDLIB_PHASE_SESSION_IDLE. 
 * Then it copies the session name and 
 * removes those characters in the session name that 
 * can cause trouble in creating file names. 
 */
#if RED_DEBUG_LIB_MODE
int	count_sessions = 0; 
#endif 
  

void	red_begin_session(type_system, session_name, process_count) 
	int	type_system, process_count; 
	char	*session_name; 
{ 
  int	i; 

  if (TOP_PHASE != 0) { 
    printf("Error: trying to start a session while in another session.\n"); 
    exit(0); 
  } 
  gettimeofday(&SYSTEM_START_TIME, &TIME_ZONE_P);
  check_phase(FLAG_REDLIB_PHASE_SESSION_IDLE, "red_begin_session"); 
  /* First we remove those characters in the session name that 
   * can cause trouble in creating file names. 
   */ 
  status_initialize(); 

  RT = NULL; 
  RED_USER_STACK = NULL;  

  RED_OUT = stdout; 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d, entering begin session\n", 
    ++ count_sessions
  ); 
  #endif 
  
  SESS_PROC_COUNT = process_count; 
  SESS_NAME_ORIGINAL = session_name; 
  REDLIB_ROLE_STRING = NULL; 
  i = strlen(session_name); 
/*
  fprintf(RED_OUT, "i=%1d for the length of session_name=%s\n", i, session_name); 
*/
  SESS_NAME_FOR_FILE = malloc(i+1); 
  sprintf(SESS_NAME_FOR_FILE, "%s", session_name);   
  for (i = 0; SESS_NAME_FOR_FILE[i] != '\0'; i++) { 
    if (   (SESS_NAME_FOR_FILE[i] < 'a' || SESS_NAME_FOR_FILE[i] > 'z') 
        && (SESS_NAME_FOR_FILE[i] < 'A' || SESS_NAME_FOR_FILE[i] > 'Z')
        && (SESS_NAME_FOR_FILE[i] < '0' || SESS_NAME_FOR_FILE[i] > '9') 
        && SESS_NAME_FOR_FILE[i] != '.'
        && SESS_NAME_FOR_FILE[i] != '_'
        ) 
      SESS_NAME_FOR_FILE[i] = '_'; 
  } 
/*
  fprintf(RED_OUT, "SESS_NAME_ORIGINAL: %s; SESS_NAME_FOR_FILE: %s\n", 
          SESS_NAME_ORIGINAL, SESS_NAME_FOR_FILE
          ); 
*/
  push_redlib_phase(FLAG_REDLIB_PHASE_MODEL_INPUT);   

  cube_child_index = NULL; 
  top_cube_child = -1; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d, leaving begin session\n", 
    count_sessions
  ); 
  #endif   
} 
  /* red_begin_session() */ 
  


void	red_end_session() { 
  int	i, vi; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d, entering end session\n", 
    count_sessions
  ); 
  #endif 
  for (i = 0; i < GLOBAL_COUNT[TYPE_STREAM]; i++) { 
    vi = variable_index[TYPE_STREAM][0][i]; 
    if (VAR[vi].U.STRM.SIZE_DATA > 0) { 
      fclose(VAR[vi].U.STRM.FILE_STREAM); 
    } 
  } 
  check_phase_above(FLAG_REDLIB_PHASE_SESSION_IDLE, "red_end_session"); 
  for (; 
       top_redlib_phase() > FLAG_REDLIB_PHASE_SESSION_IDLE; 
       pop_redlib_phase()
       ); 
  change_redlib_phase(FLAG_REDLIB_PHASE_SESSION_IDLE);   
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
  print_time_progress_statistics("Time statistics after end the session"); 
  #endif 

  free(inbuf); 
  inbuf_size = 0; 
  inbuf = NULL; 

  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nbefore releasing all\n"); 
  fflush(RED_OUT); 
  #endif 
  
  release_all_space(); 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d, leaving red end session()\n", count_sessions); 
  fflush(RED_OUT); 
  #endif 

} 
  /* red_end_session() */  
  

/**********************************************************
 * The following routines are for the parsing of a model and 
 * the query of the parsed model information. 
 */
void	red_parse_model(mf) 
	char	*mf; 
{ 
  fprintf(RED_OUT, 
    "\nSorry, procedure red_parse_model(mf) has been removed.\n"
  ); 
  fprintf(RED_OUT, 
    "Now please use red_input_model(mf, RED_PARSING_ONLY);\n\n"
  ); 
  fflush(RED_OUT); 
  exit(0);  
}
  /* red_parse_model() */ 



int	red_query_window_width() { 
  return(WINDOW_WIDTH); 
}
  /* red_query_window_width() */  


int	red_query_window_height() { 
  return(WINDOW_HEIGHT); 
}
  /* red_query_window_height() */  


void	red_set_window_width(int window_width) { 
  WINDOW_WIDTH = window_width; 
}
  /* red_set_window_width() */  


void	red_set_window_height(int window_height) { 
  WINDOW_HEIGHT = window_height; 
}
  /* red_set_window_height() */  


struct parse_variable_type	*query_pv; 
int				status_query_pv; 

#define FLAG_IN_GLOBAL_SYNCHRONIZERS	0
#define FLAG_IN_GLOBAL_DENSES		1
#define FLAG_IN_GLOBAL_CLOCKS		2
#define FLAG_IN_GLOBAL_DISCRETES	3
#define FLAG_IN_GLOBAL_POINTERS		4
#define FLAG_IN_LOCAL_SYNCHRONIZERS	5
#define FLAG_IN_LOCAL_DENSES		6
#define FLAG_IN_LOCAL_CLOCKS		7
#define FLAG_IN_LOCAL_DISCRETES		8
#define FLAG_IN_LOCAL_POINTERS		9


int 	red_next_var_declaration() { 
  query_pv = query_pv->next_parse_variable; 
  
  for (; TYPE_TRUE; ) { 
    for (; 
            query_pv 
         && (   (query_pv->status & FLAG_VAR_SYS_GEN)
             || (   query_pv->type == TYPE_POINTER
                 && (query_pv->status & FLAG_LOCAL_VARIABLE)
                 && (query_pv->status & FLAG_QUANTIFIED_SYNC) 
             )   ); 
         query_pv = query_pv->next_parse_variable
         ) ;
    if (query_pv) 
      return (RED_FLAG_SUCCESS); 
    else switch (status_query_pv) {
    case FLAG_IN_GLOBAL_SYNCHRONIZERS: 
      status_query_pv = FLAG_IN_GLOBAL_DENSES; 
      query_pv = declare_global_dense_list; 
      break; 
    case FLAG_IN_GLOBAL_DENSES: 
      status_query_pv = FLAG_IN_GLOBAL_CLOCKS; 
      query_pv = declare_global_clock_list;
      break; 
    case FLAG_IN_GLOBAL_CLOCKS:
      status_query_pv = FLAG_IN_GLOBAL_DISCRETES; 
      query_pv = declare_global_discrete_list;
      break; 
    case FLAG_IN_GLOBAL_DISCRETES: 
      status_query_pv = FLAG_IN_GLOBAL_POINTERS; 
      query_pv = declare_global_pointer_list;
      break; 
    case FLAG_IN_GLOBAL_POINTERS: 
      status_query_pv = FLAG_IN_LOCAL_SYNCHRONIZERS; 
      query_pv = declare_local_synchronizer_list; 
      break; 
    case FLAG_IN_LOCAL_SYNCHRONIZERS: 
      status_query_pv = FLAG_IN_LOCAL_DENSES; 
      query_pv = declare_local_dense_list; 
      break; 
    case FLAG_IN_LOCAL_DENSES: 
      status_query_pv = FLAG_IN_LOCAL_CLOCKS; 
      query_pv = declare_local_clock_list;
      break; 
    case FLAG_IN_LOCAL_CLOCKS: 
      status_query_pv = FLAG_IN_LOCAL_DISCRETES; 
      query_pv = declare_local_discrete_list;
      break; 
    case FLAG_IN_LOCAL_DISCRETES: 
      status_query_pv = FLAG_IN_LOCAL_POINTERS; 
      query_pv = declare_local_pointer_list; 
      break; 
    default: 
      return (RED_FLAG_FAILURE); 
    }
  } 
}
  /* red_next_var_declaration() */ 



int 	red_first_var_declaration() { 
  if (declare_global_synchronizer_list) { 
    status_query_pv = FLAG_IN_GLOBAL_SYNCHRONIZERS; 
    query_pv = declare_global_synchronizer_list; 
  }
  else if (declare_global_dense_list) { 
    status_query_pv = FLAG_IN_GLOBAL_DENSES; 
    query_pv = declare_global_dense_list; 
  } 
  else if (declare_global_clock_list) { 
    status_query_pv = FLAG_IN_GLOBAL_CLOCKS; 
    query_pv = declare_global_clock_list;
  }
  else if (declare_global_discrete_list) { 
    status_query_pv = FLAG_IN_GLOBAL_DISCRETES; 
    query_pv = declare_global_discrete_list;
  } 
  else if (declare_global_pointer_list) { 
    status_query_pv = FLAG_IN_GLOBAL_POINTERS; 
    query_pv = declare_global_pointer_list;
  }
  else if (declare_local_synchronizer_list) {  
    status_query_pv = FLAG_IN_LOCAL_SYNCHRONIZERS; 
    query_pv = declare_local_synchronizer_list; 
  }
  else if (declare_local_dense_list) {  
    status_query_pv = FLAG_IN_LOCAL_DENSES; 
    query_pv = declare_local_dense_list; 
  }
  else if (declare_local_clock_list) {  
    status_query_pv = FLAG_IN_LOCAL_CLOCKS; 
    query_pv = declare_local_clock_list;
  }
  else if (declare_local_discrete_list) { 
    status_query_pv = FLAG_IN_LOCAL_DISCRETES; 
    query_pv = declare_local_discrete_list;
  }
  else if (declare_local_pointer_list) { 
    status_query_pv = FLAG_IN_LOCAL_POINTERS; 
    query_pv = declare_local_pointer_list; 
  }
  else {  
    return (RED_FLAG_FAILURE); 
  }
  if (   (query_pv->status & FLAG_VAR_SYS_GEN) 
      || (   query_pv->type == TYPE_POINTER
          && (query_pv->status & FLAG_LOCAL_VARIABLE)
          && (query_pv->status & FLAG_QUANTIFIED_SYNC) 
      )   )
    red_next_var_declaration(); 
  if (query_pv) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE); 
} 
  /* red_first_var_declaration() */ 






char	*string_var_scope(struct parse_variable_type *pv) { 
  if (pv->status & FLAG_LOCAL_VARIABLE) 
    return("local"); 
  else 
    return("global"); 	
}
  /* string_var_scope() */ 
  
  
  
char	*string_var_type(struct parse_variable_type *pv) { 
  switch (pv->type) {
  case TYPE_SYNCHRONIZER: 
    return("synchronizer"); 
  case TYPE_DENSE: 
    return("dense"); 
  case TYPE_CLOCK: 
    return("clock"); 
  case TYPE_DISCRETE: 
    return("discrete"); 
  case TYPE_POINTER: 
    return("pointer"); 
  }
}
  /* string_var_type() */ 
  
  
  
char	*red_query_string_current_var_declaration() { 
  char	*s, *t, *d; 
  
  s = string_var_scope(query_pv); 
  t = string_var_type(query_pv); 
  
  switch (query_pv->type) {
  case TYPE_SYNCHRONIZER: 
  case TYPE_DENSE: 
  case TYPE_CLOCK: 
  case TYPE_POINTER: 
    d = malloc(
        strlen(s) 
      + 1 
      + strlen(t) 
      + 1 
      + strlen(query_pv->name) 
      + 2 
    );  
    sprintf(d, "%s %s %s;", s, t, query_pv->name); 
    return(d); 
  case TYPE_DISCRETE: 
    d = malloc(
        strlen(s) 
      + 1 // space 
      + strlen(t) 
      + 1 // space 
      + strlen(query_pv->name)
      + 1 // colon 
      + intlen(query_pv->u.disc.lb)
      + 2 // ..
      + intlen(query_pv->u.disc.ub)
      + 2 // semicolon and terminator
    );  
    sprintf(d, "%s %s %s:%1d..%1d;", 
      s, t, query_pv->name, query_pv->u.disc.lb, query_pv->u.disc.ub
    ); 
    return(d); 
  }
}
  /* red_query_string_current_var_declaration() */  


struct ps_bunit_type	*query_inline_exp; 

int	red_first_macro_const() { 
  for (query_inline_exp = declare_inline_exp_list; 
          query_inline_exp 
       && (  query_inline_exp->subexp->u.inline_declare.status 
           & MASK_INLINE_TYPE
           ) != FLAG_INLINE_CONSTANT; 
       query_inline_exp = query_inline_exp->bnext
       ); 
  if (query_inline_exp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_first_macro_const() */ 


int	red_next_macro_const() { 
  if (query_inline_exp == NULL) 
    return(RED_FLAG_FAILURE); 
    
  for (query_inline_exp = query_inline_exp->bnext; 
          query_inline_exp 
       && (  query_inline_exp->subexp->u.inline_declare.status 
           & MASK_INLINE_TYPE
           ) != FLAG_INLINE_CONSTANT; 
       query_inline_exp = query_inline_exp->bnext
       ); 
  if (query_inline_exp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
} 
  /* red_next_macro_const() */ 




char	*red_query_string_current_macro_const() { 
  char	*s; 
  
  s = malloc(
      1 // \n
    + 7 // #define 
    + 1 // \t 
    + strlen(query_inline_exp->subexp->u.inline_declare.inline_exp_name) 
    + 1 // \t 
    + intlen(query_inline_exp->subexp->u.inline_declare.declare_exp->u.value)
    + 1 // \n
    + 1 // terminator
  ); 
  sprintf(s, "\n#define\t%s\t%1d\n", 
    query_inline_exp->subexp->u.inline_declare.inline_exp_name,  
    query_inline_exp->subexp->u.inline_declare.declare_exp->u.value
  ); 
  return(s); 
}
  /* red_query_string_current_macro_const() */ 
  
  
  
  

int	red_first_inline_exp_declaration() { 
  for (query_inline_exp = declare_inline_exp_list; 
          query_inline_exp 
       && (  query_inline_exp->subexp->u.inline_declare.status 
           & MASK_INLINE_TYPE
           ) == FLAG_INLINE_CONSTANT; 
       query_inline_exp = query_inline_exp->bnext
       ); 
  if (query_inline_exp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_first_inline_exp_declaration() */ 


int	red_next_inline_exp_declaration() { 
  if (query_inline_exp == NULL) 
    return(RED_FLAG_FAILURE); 
    
  for (query_inline_exp = query_inline_exp->bnext; 
          query_inline_exp 
       && (  query_inline_exp->subexp->u.inline_declare.status 
           & MASK_INLINE_TYPE
           ) == FLAG_INLINE_CONSTANT; 
       query_inline_exp = query_inline_exp->bnext
       ); 
  if (query_inline_exp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
} 
  /* red_next_inline_exp_declaration() */ 
  



char	*red_query_string_current_inline_exp_declaration() { 
  return(string_parse_subformula(
    query_inline_exp->subexp, INDEX_LOCAL_IDENTIFIER, 0 
  ) ); 
}
  /* red_query_string_current_inline_exp_declaration() */ 



int	len_string_declaration_header() { 
  int	len, cs, vs; 
  char	*s; 
  
  len = 0; 
  for (cs = red_first_macro_const(); 
       cs == RED_FLAG_SUCCESS; 
       cs = red_next_macro_const()
       ) { 
    s = red_query_string_current_macro_const(); 
    len = len + strlen(s) + 1;  
    free(s); 
  } 

  len = len // "\nwindow(%1d,%1d)\n"
  + 8 
  + intlen(red_query_window_width()) 
  + 1 
  + intlen(red_query_window_height()) 
  + 2; 

  len = len // "process count = %1d;\n"
  + 16 
  + intlen(red_query_process_count()) 
  + 2; 
  
  for (vs = red_first_var_declaration(); 
       vs == RED_FLAG_SUCCESS; 
       vs = red_next_var_declaration()
       ) { 
    s = red_query_string_current_var_declaration(); 
    len = len + strlen(s) + 1; 
    free(s); 
  } 

  for (cs = red_first_inline_exp_declaration(); 
       cs == RED_FLAG_SUCCESS; 
       cs = red_next_inline_exp_declaration()
       ) { 
    s = red_query_string_current_inline_exp_declaration(); 
    len = len + strlen(s) + 1; 
    free(s); 
  } 
  return(len); 
}
  /* len_string_declaration_header() */ 
  
  
  
  
char	*red_query_string_declaration_header() { 
  char	*r, *s; 
  int	len, cs, vs, pos, i, j; 
  
  r = malloc(len_string_declaration_header()+1); 
  pos = 0; 
  
  for (cs = red_first_macro_const(); 
       cs == RED_FLAG_SUCCESS; 
       cs = red_next_macro_const()
       ) { 
    s = red_query_string_current_macro_const(); 
    sprintf(&(r[pos]), "%s\n", s); 
    pos = pos + strlen(s) + 1;  
    free(s); 
  } 
  sprintf(&(r[pos]), "\nwindow(%1d,%1d)\n", 
    i = red_query_window_width(), j = red_query_window_height()
  ); 
  pos = pos + 8 + intlen(i) + 1 + intlen(j) + 2; 
  sprintf(&(r[pos]), "process count = %1d;\n", 
    i = red_query_process_count()
  ); 
  pos = pos + 16 + intlen(i) + 2; 
  
  for (vs = red_first_var_declaration(); 
       vs == RED_FLAG_SUCCESS; 
       vs = red_next_var_declaration()
       ) { 
    s = red_query_string_current_var_declaration(); 
    sprintf(&(r[pos]), "%s\n", s); 
    pos = pos + strlen(s) + 1; 
    free(s); 
  } 

  for (cs = red_first_inline_exp_declaration(); 
       cs == RED_FLAG_SUCCESS; 
       cs = red_next_inline_exp_declaration()
       ) { 
    s = red_query_string_current_inline_exp_declaration(); 
    sprintf(&(r[pos]), "%s\n", s);    	
    pos = pos + strlen(s) + 1; 
    free(s); 
  } 
  r[pos] = '\0'; 
  
  return(r); 
}
  /* red_query_string_declaration_header() */ 
  
 
  
  
struct parse_mode_type			*query_pm; 
struct parse_xtion_link_type		*query_px; 
struct parse_rate_spec_link_type	*query_prs; 
struct index_pair_link_type		*query_pxp; 

int	red_first_mode() { 
  query_pm = declare_mode_list; 
  query_px = NULL; 
  query_prs = NULL; 
  query_pxp = NULL; 
  if (query_pm) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_first_mode() */ 


int	red_next_mode() { 
  query_pm = query_pm->next_parse_mode; 
  query_px = NULL; 
  query_prs = NULL; 
  query_pxp = NULL; 
  if (query_pm) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
} 
  /* red_next_mode() */ 
  

char	*red_query_current_mode_name() { 
  return(query_pm->name); 
} 
  /* red_query_current_mode_name() */  
  

char	*red_query_string_current_mode_urgency() { 
  if (query_pm->status & FLAG_MODE_URGENT) 
    return("urgent"); 
  else 
    return(""); 
} 
  /* red_query_string_current_mode_urgency() */  
  
  
  
char	*red_query_string_current_mode_invariance() { 
  return(string_parse_subformula( 
    query_pm->orig_invariance_exp, INDEX_LOCAL_IDENTIFIER, 
    FLAG_NO_SUBFORMULA_DEPTH 
  ) ); 
} 
  /* red_query_string_current_mode_invariance() */ 
  
  
int	red_query_current_mode_position_x() { 
  if (query_pm->position_x == FLAG_MODE_POSITION_UNKNOWN) 
    return(RED_FLAG_UNKNOWN); 
  else 
    return(query_pm->position_x); 
} 
  /* red_query_current_mode_position_x() */ 
  

int	red_query_current_mode_position_y() { 
  if (query_pm->position_y == FLAG_MODE_POSITION_UNKNOWN) 
    return(RED_FLAG_UNKNOWN); 
  else 
    return(query_pm->position_y); 
} 
  /* red_query_current_mode_position_y() */ 
  
  
int	red_query_current_mode_shape() { 
  switch (query_pm->shape) {
  case FLAG_MODE_SHAPE_UNKNOWN: 
    return(RED_FLAG_UNKNOWN); 
  case FLAG_MODE_OVAL: 
    return(RED_MODE_OVAL); 
  case FLAG_MODE_RECTANGLE: 
    return(RED_MODE_RECTANGLE); 
  case FLAG_MODE_TRIANGLE: 
    return(RED_MODE_TRIANGLE); 
  } 
} 
  /* red_query_current_mode_shape() */ 
  
  
int	red_query_current_mode_rectangle_width() { 
  return(query_pm->rectangle_width); 
} 
  /* red_query_current_mode_rectangle_width() */ 
  
#define	red_query_current_mode_oval_xradius	red_query_current_mode_rectangle_width
#define	red_query_current_mode_triangle_radius	red_query_current_mode_rectangle_width

  
  
int	red_query_current_mode_rectangle_height() { 
  return(query_pm->rectangle_height); 
} 
  /* red_query_current_mode_rectangle_height() */ 
  
#define	red_query_current_mode_oval_yradius	red_query_current_mode_rectangle_height


int	red_query_current_mode_triangle_direction() { 
  switch (query_pm->triangle_direction) { 
  case FLAG_TRIANGLE_LEFTWARD: 
    return(RED_TRIANGLE_LEFTWARD); 
  case FLAG_TRIANGLE_RIGHTWARD: 
    return(RED_TRIANGLE_RIGHTWARD); 
  case FLAG_TRIANGLE_UPWARD: 
    return(RED_TRIANGLE_UPWARD); 
  case FLAG_TRIANGLE_DOWNWARD: 
    return(RED_TRIANGLE_DOWNWARD); 
  } 
}
  /* red_query_current_mode_triangle_direction() */ 

  
int	red_query_current_mode_color() { 
  return(query_pm->color); 
} 
  /* red_query_current_mode_color() */ 

int	red_query_current_mode_rate_spec_count() { 
  return(query_pm->rate_spec_count); 
}
  /* red_query_current_mode_rate_spec_count() */ 


  
int	red_query_current_mode_xtion_count() { 
  return(query_pm->xtion_count); 
}
  /* red_query_current_mode_xtion_count() */ 


int	red_first_xtion() { 
  query_px = query_pm->parse_xtion_list;
  query_pxp = NULL; 
  if (query_px) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_first_xtion_of_current_mode() */
  
  
int	red_next_xtion() { 
  query_px = query_px->next_parse_xtion_link;
  query_pxp = NULL; 
  if (query_px) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_next_xtion_of_current_mode() */
  


char	*red_query_string_current_xtion_syncs() { 
  return(string_sync_list(query_px->parse_xtion->sync_list)); 	
} 
  /* red_query_string_current_xtion_syncs() */   
  
  
  
  
char	*red_query_string_current_xtion_trigger() { 
  return(string_parse_subformula(
    query_px->parse_xtion->orig_trigger_exp, 
    INDEX_LOCAL_IDENTIFIER, 
    FLAG_NO_SUBFORMULA_DEPTH
  ) ); 	
} 
  /* red_query_string_current_xtion_trigger() */   



char	*red_query_string_current_xtion_statement() { 
  return(string_parse_statement_instantiate(
    query_px->parse_xtion->statement, 
    INDEX_LOCAL_IDENTIFIER
  ) ); 	
} 
  /* red_query_string_current_xtion_statement() */ 



char 	*rec_statement_dest_name(pst)
     struct parse_statement_type	*pst;
{ 
  struct parse_statement_link_type	*psl; 
  char					*dn1, *dn2; 

  if (!pst) 
    return (NULL); 

  switch (pst->op) { 
  case UNCHANGED: 
    return(NULL); 
    break; 
  case ST_IF: 
    dn1 = rec_statement_dest_name(pst->u.branch.if_statement); 
    if (pst->st_status & FLAG_STATEMENT_ELSE) {
      dn2 = rec_statement_dest_name(pst->u.branch.else_statement); 
      if (dn1 != dn2) { 
      	fprintf(RED_OUT, "\nStatement with multiple destinations.\n"); 
      	fflush(RED_OUT); 
      	exit(0); 
      } 
    } 
    return(dn1); 
    break; 
  case ST_WHILE: 
    dn1 = rec_statement_dest_name(pst->u.loop.statement); 
    return(dn1); 
    break; 
  case ST_SEQ: 
    dn1 = NULL; 
    for (psl = pst->u.seq.statement_list; 
         psl; 
         psl = psl->next_parse_statement_link
         ) { 
      dn2 = rec_statement_dest_name(psl->statement); 
      if (dn2 != NULL) 
        dn1 = dn2; 
    } 
    return(dn1); 
    break; 

  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    return(NULL); 

  default: 
    if (   pst->u.act.lhs->type == TYPE_DISCRETE
        && pst->u.act.lhs->u.atom.var == var_mode
        && pst->u.act.lhs->u.atom.exp_base_proc_index->type 
           == TYPE_LOCAL_IDENTIFIER
        ) { 
      if (pst->u.act.rhs_exp->type == TYPE_MODE_INDEX) 
        return(pst->u.act.rhs_exp->u.mode_index.mode_name); 
      else if (   pst->u.act.rhs_exp->type == TYPE_CONSTANT 
               && pst->u.act.rhs_exp->u.value >= 0
               && pst->u.act.rhs_exp->u.value < MODE_COUNT
               ) { 
        struct parse_mode_type	*pm; 
        
        if (MODE) 
          return(MODE[pst->u.act.rhs_exp->u.value].name); 
        for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
          if (pm->index == pst->u.act.rhs_exp->u.value) 
            return(pm->name); 
        } 
      }
    } 
     
    return(NULL); 
    break; 	
  } 
}
  /* rec_statement_dest_name() */ 



char	*red_query_current_xtion_dest_name() { 
  char	*dn; 
  
  dn = rec_statement_dest_name(query_px->parse_xtion->statement); 
  if (dn == NULL) 
    return(query_pm->name); 
  else 
    return(dn); 
} 
  /* red_query_current_xtion_dest_name() */ 
  
  
int	count_rqscx = 0; 

char	*red_query_string_current_xtion() { 
  char	*s, *t, *a, *x; 

  /* 
  fprintf(RED_OUT, "%1d, entering red_query_string_current_xtion().\n", 
    ++count_rqscx
  ); 
  fflush(RED_OUT); 
  */ 
  s = string_sync_list(query_px->parse_xtion->sync_list); 
  t = string_parse_subformula(
    query_px->parse_xtion->orig_trigger_exp, 
    INDEX_LOCAL_IDENTIFIER, 
    FLAG_NO_SUBFORMULA_DEPTH 
  ); 
  a = string_parse_statement_instantiate(
    query_px->parse_xtion->statement, 
    INDEX_LOCAL_IDENTIFIER
  ); 
  
  x = malloc(
    5 // when and a space 
  + strlen(s) 
  + 2 // space and (
  + strlen(t) 
  + 6 // ), space, may, and a space
  + strlen(a) 
  + 1 // a terminator 
  ); 
  sprintf(x, "when %s (%s) may %s", s, t, a); 
  
  if (strcmp(s, "\0")) 
    free(s); 
  if (t) 
    free(t); 
  if (a) 
    free(a); 
  
  return(x); 
} 
  /* red_query_string_current_xtion() */ 



int 	red_first_xtion_point() { 
  query_pxp = query_px->parse_xtion->intermediate_point_list; 
  if (query_pxp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);     
}
  /* red_first_xtion_point() */  
  

int 	red_next_xtion_point() { 
  query_pxp = query_pxp->next_index_pair_link; 
  if (query_pxp) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);     
}
  /* red_next_xtion_point() */  



int	red_current_xtion_point_x() { 
  return(query_pxp->coordinate_x); 
}
  /* red_current_xtion_point_coordinate_x() */ 
  
  
  
int	red_current_xtion_point_y() { 
  return(query_pxp->coordinate_y); 
}
  /* red_current_xtion_point_coordinate_y() */ 
  
  
  

int	red_first_rate_spec() { 
  query_prs = query_pm->parse_rate_spec_list;
  if (query_prs) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_first_rate_spec_of_current_mode() */
  
  
int	red_next_rate_spec() { 
  query_prs = query_prs->next_parse_rate_spec_link;
  if (query_prs) 
    return(RED_FLAG_SUCCESS); 
  else 
    return(RED_FLAG_FAILURE);   
}
  /* red_next_rate_spec_of_current_mode() */
  


char	*string_lb_brac(int lbb) { 
  switch (lbb) { 
  case FLAG_RATE_LB_OPEN: 
    return("("); 
  default: 
    return("["); 
  } 
} 
  /* string_lb_brac() */  



char	*string_ub_brac(int ubb) { 
  switch (ubb) { 
  case FLAG_RATE_UB_OPEN: 
    return(")"); 
  default: 
    return("]"); 
  } 
} 
  /* string_ub_brac() */  




char	*red_query_string_current_rate_spec() { 
  char	*lbe, *ube, *r; 
  
  lbe = string_parse_subformula(
    query_prs->rate_lb, 
    INDEX_LOCAL_IDENTIFIER, 
    FLAG_NO_SUBFORMULA_DEPTH
  ); 
  ube = string_parse_subformula(
    query_prs->rate_ub, 
    INDEX_LOCAL_IDENTIFIER, 
    FLAG_NO_SUBFORMULA_DEPTH
  ); 
  r = malloc(5 
  + strlen(query_prs->rate_var_name)
  + 1 // lb bracket 
  + strlen(lbe)
  + 1 // comma
  + strlen(ube) 
  + 3 // ub bracket, semicolon, and a terminator 
  );  
  sprintf(r, "rate %s%s%s,%s%s;", 
    query_prs->rate_var_name, 
    string_lb_brac(query_prs->status & FLAG_RATE_LB_OPEN), 
    lbe, 
    ube, 
    string_ub_brac(query_prs->status & FLAG_RATE_UB_OPEN) 
  ); 
  free(lbe); 
  free(ube); 
  
  return(r); 
}
  /* red_query_string_current_rate_spec() */ 
  
  
  

  
#if RED_DEBUG_LIB_MODE
int	count_input_model = 0; 
#endif 


void	print_model_caution_message(char *mf) { 
  fprintf(RED_OUT, "  The tables include: \n");   
  fprintf(RED_OUT, "    1) process table, \n");  
  fprintf(RED_OUT, "    2) mode table, \n");  
  fprintf(RED_OUT, "    3) variable table, \n");  
  fprintf(RED_OUT, "    4) declared transition table, \n");  
  fprintf(RED_OUT, "    5) synchronous transition table, \n");  
  fprintf(RED_OUT, 
    "    6) decision diagram for synchronous transitions \n"
  );  
  fprintf(RED_OUT, 
    "       to be executed as a whole, and \n"
  );  
  fprintf(RED_OUT, 
    "    7) decision diagram for the initial condition. \n"
  );  
  fprintf(RED_OUT, "\n****<Caution>***************\n"); 
  fprintf(RED_OUT, 
    "  It is highly recommended that the tables be checked\n"
  ); 
  fprintf(RED_OUT, 
    "  to make sure that there is no bugs in the model,\n"
  );  
  fprintf(RED_OUT, 
    "  all declared transitions have been generated,\n"
  );  
  fprintf(RED_OUT, 
    "  all synchronous transitions have been properly constructed,\n"
  );  
  fprintf(RED_OUT, 
    "  the decision diagram for transition synchronization has \n"
  );  
  fprintf(RED_OUT, 
    "  been properly constructed,  \n"
  );  
  fprintf(RED_OUT, 
    "  and the decision diagram for the initial condition has \n"
  );  
  fprintf(RED_OUT, 
    "  been properly constructed. \n"
  );  
  fprintf(RED_OUT, 
    "  It is usually difficult to get the model right in the first \n"
  );  
  fprintf(RED_OUT, 
    "  few construciton. \n\n"
  );  
  fprintf(RED_OUT, 
    "  Especially, without understanding our bulk precondition and \n"
  );  
  fprintf(RED_OUT, 
    "  postcondition calculation techniques reported in ICFEM 2005 \n"
  );  
  fprintf(RED_OUT, 
    "  and Real-Time System Journal 2011, \n"
  );  
  fprintf(RED_OUT, 
    "  users may be unaware that some complex synchronous transitions are  \n"
  );  
  fprintf(RED_OUT, 
    "  to be executed as a whole.  \n"
  );  
  fprintf(RED_OUT, 
    "  Synchronous transitions are to be executed as a whole if the number\n"
  );  
  fprintf(RED_OUT, 
    "  of parties is more than a threshold value.\n"
  );  
  fprintf(RED_OUT, 
    "  Default threshold value is 4.  \n"
  );  
  fprintf(RED_OUT, 
    "  The threshold value can be queried and set respectively with\n"
  );  
  fprintf(RED_OUT, 
    "  red_query_sync_bulk_depth() and red_set_sync_bulk_depth().\n"
  );  
  
  fprintf(RED_OUT, 
    "\n  If you think that your model is right, but the synchronous \n"
  );  
  fprintf(RED_OUT, 
    "  transition enumeration and bulk decision diagram is incorrect,  \n"
  );  
  fprintf(RED_OUT, 
    "  please send emails to farn@cc.ee.ntu.edu.tw.  \n"
  );  
  fprintf(RED_OUT, 
    "  We will be more than happy to discuss with you. \n"
  );  
}
  /* print_mode_caution_message() */ 



void	print_modeling_result(char *mf) { 
  char 	*cf; 
  FILE	*cfile, *tfile; 
  
  cf = malloc(strlen(mf)+1+9+intlen(PROCESS_COUNT)); 
  sprintf(cf, "%s.%1d.redtab\0", mf, PROCESS_COUNT); 
  cfile = fopen(cf, "w"); 
  tfile = RED_OUT; 
  RED_OUT = cfile; 
  
  fprintf(RED_OUT, 
    "  The following tables are constructed for model template file: \n"  
  ); 
  fprintf(RED_OUT, "    %s\n", mf); 
  fprintf(RED_OUT, 
    "  of %1d processes.\n", 
    PROCESS_COUNT
  );   
  print_model_caution_message(mf); 

  print_processes(); 
  print_modes(); 
  print_variables(); 
  print_xtions();
  print_sync_xtions("", SYNC_XTION, SYNC_XTION_COUNT); 

  fprintf(RED_OUT, "\n------------------------------------------\n"); 
  fprintf(RED_OUT, 
    "The threshold for synchornous transition bulk execution is %1d.\n", 
    DEPTH_ENUMERATIVE_SYNCHRONIZATION
  ); 
  fprintf(RED_OUT, 
    "The decision diagram for synchronous transition bulk execution is:\n"
  ); 
  red_print_graph(RT[XI_SYNC_BULK]); 

  fprintf(RED_OUT, "\n------------------------------------------\n"); 
  fprintf(RED_OUT, "The initial condition decision diagram:\n"); 
  red_print_graph(RT[INDEX_INITIAL]); 
  
  fclose(cfile); 
  free(cf); 
  
  RED_OUT = tfile; 
  
  fprintf(RED_OUT, "\n****<Caution>***************\n"); 
  
  fprintf(RED_OUT, "  The following tables for model template file:\n"); 
  fprintf(RED_OUT, "    %s\n", mf); 
  fprintf(RED_OUT, "  of %1d processes has been written to file:\n", 
    PROCESS_COUNT 
  ); 
  fprintf(RED_OUT, "    %s.%1d.redtab.\n", mf, PROCESS_COUNT); 
  print_model_caution_message(mf); 
  
  fflush(RED_OUT); 
}
  /* print_modeling_result() */ 



  
void	red_input_model(
  char	*mf, 
  int 	flag_model_processing
) { 
  int		w;
  redgram	d; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, entering input model\n", 
    count_sessions, ++ count_input_model
  ); 
  #endif 
  
  check_phase(FLAG_REDLIB_PHASE_MODEL_INPUT, "red_input_model"); 
  
  change_redlib_phase(FLAG_REDLIB_PHASE_PARSING); 

  GSTATUS[INDEX_REDLIB_CONTROL] = GSTATUS[INDEX_REDLIB_CONTROL] 
  | FLAG_REDLIB_DECLARE_FULL_MODEL 
  | FLAG_REDLIB_RENEW_VARS
  | FLAG_REDLIB_RENEW_RULES; 
  
  switch (flag_model_processing) { 
  case RED_PARSING_ONLY: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_PARSING_ONLY; 
    break; 
  case RED_NO_REFINED_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE; 
    break;  
  case RED_REFINE_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_REFINED_ABSTRACT_SPACE; 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal model processing option %1d\n", 
      flag_model_processing
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  
  parse_system_description(
    mf, output_file_name, 
    SESS_PROC_COUNT, 
    TASK_REDLIB_SESSION
  );

  change_redlib_phase(FLAG_REDLIB_PHASE_ANALYSIS);  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nbefore red_abstract_space_bck()\n"); 
  fprintf(RED_OUT, "\nBefore refining the global invariances:\n"); 
  red_print_graph(RT[DECLARED_GLOBAL_INVARIANCE]); 
  fflush(RED_OUT); 
  #endif 
  
  switch (GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) {
  case FLAG_MODEL_PARSING_ONLY: 
  
    break; 
  case FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE: 
    print_modeling_result(mf); 
    RT[REFINED_GLOBAL_INVARIANCE] = RT[DECLARED_GLOBAL_INVARIANCE]; 
    break; 
  case FLAG_MODEL_REFINED_ABSTRACT_SPACE: 
    print_modeling_result(mf); 
    RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_bck(
      INDEX_INITIAL, 
      DECLARED_GLOBAL_INVARIANCE, 
      INDEX_GOAL, 
      GSTATUS[INDEX_TASK] & MASK_TASK, 
      GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
      0 // no print options are used. 
    ); 
    break; 
  }  

  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "After recalculating abstract image = %1d\n", 
    REFINED_GLOBAL_INVARIANCE
  ); 
  red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
  #endif  

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) ==  FLAG_SYSTEM_HYBRID) {
    mode_timed_inactive_analyze();
    #if RED_DEBUG_LIB_MODE
    fprintf(RED_OUT, "After timed inactive abstract image = %1d\n", 
      REFINED_GLOBAL_INVARIANCE
    ); 
    red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
    #endif  
  } 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, leaving input model\n", 
    count_sessions, count_input_model
  ); 
  #endif 
} 
  /* red_input_model() */ 
  
  
 

#if RED_DEBUG_LIB_MODE
int	count_input_rules = 0; 
#endif 
  

void	red_input_rules(
  char	*mf, 
  int 	flag_model_processing
) { 
  int	w; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, entering input rules\n", 
    count_sessions, ++ count_input_rules
  ); 
  #endif 
  
  check_phase(FLAG_REDLIB_PHASE_ANALYSIS, "red_input_rules"); 
  
  change_redlib_phase(FLAG_REDLIB_PHASE_PARSING_RULES); 

  release_all_rule_related_space(1); 
  
  GSTATUS[INDEX_REDLIB_CONTROL] = 
  (  GSTATUS[INDEX_REDLIB_CONTROL] 
   & (~FLAG_REDLIB_DECLARE_FULL_MODEL) 
   & (~FLAG_REDLIB_RENEW_VARS)
   & (~FLAG_REDLIB_PARSING_ONLY)
   )
  | FLAG_REDLIB_RENEW_RULES; 
  switch (flag_model_processing) { 
  case RED_PARSING_ONLY: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_PARSING_ONLY; 
    break; 
  case RED_NO_REFINED_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE;
    break;  
  case RED_REFINE_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_REFINED_ABSTRACT_SPACE;
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal model processing option %1d\n", 
      flag_model_processing
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED) {
    RT[INDEX_MODE_CONVEXITY] = NULL; 
    RT[INDEX_MODE_CONCAVITY] = NULL; 
  }
  parse_system_description(
    mf, output_file_name, 
    SESS_PROC_COUNT, 
    TASK_REDLIB_SESSION
  );

  change_redlib_phase(FLAG_REDLIB_PHASE_ANALYSIS);  
  switch (GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) {
  case FLAG_MODEL_PARSING_ONLY: 
  
    break; 
  case FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE: 
    print_modeling_result(mf); 
    RT[REFINED_GLOBAL_INVARIANCE] = RT[DECLARED_GLOBAL_INVARIANCE]; 
    break; 
  case FLAG_MODEL_REFINED_ABSTRACT_SPACE: 
    print_modeling_result(mf); 
    RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_bck(
      INDEX_INITIAL, 
      DECLARED_GLOBAL_INVARIANCE, 
      INDEX_GOAL, 
      GSTATUS[INDEX_TASK] & MASK_TASK, 
      GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
      0 // no print options are used. 
    ); 
    break; 
  }  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "After recalculating abstract image = %1d\n", 
    REFINED_GLOBAL_INVARIANCE
  ); 
  red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
  #endif  

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) ==  FLAG_SYSTEM_HYBRID) {
    mode_timed_inactive_analyze();
    #if RED_DEBUG_LIB_MODE
    fprintf(RED_OUT, "After timed inactive abstract image = %1d\n", 
      REFINED_GLOBAL_INVARIANCE
    ); 
    red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
    #endif  
  } 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, leaving input rules\n", 
    count_sessions, count_input_rules
  ); 
  #endif 
} 
  /* red_input_rules() */ 
  
  
 

/* The following procedure starts the declaration session of 
 * It first open a write file with name constructed out of the session_name 
 * parameter.  
 * The file is then used to hold the input model file constructed out 
 * of the input command. 
 */ 
#if RED_DEBUG_LIB_MODE
int	count_change_declaration = 0; 
#endif 
  

void	red_change_declaration(flag_vars, flag_rules) { 
  int	i; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, entering change declaration\n", 
    count_sessions, ++ count_change_declaration
  ); 
  #endif 
  
  check_phase(FLAG_REDLIB_PHASE_MODEL_INPUT, "red_begin_declaration"); 

  i = strlen(SESS_NAME_FOR_FILE); 

  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\ni=%1d, SESS_NAME_FOR_FILE:%s\n", i, SESS_NAME_FOR_FILE); 
  #endif 
  
  model_file_name = malloc(i+9); 
  sprintf(model_file_name, "%s.model.d\0", SESS_NAME_FOR_FILE); 
  
  spec_file_name = NULL; 
  output_file_name = "STDOUT"; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\ni=%1d, model_file_name:%s\n", i, model_file_name); 
  #endif 
  
  model_template_file = fopen(model_file_name, "w"); 
  fprintf(model_template_file, 
	  "/***************************************************\n"
	  ); 
  fprintf(model_template_file, 
	  " * model file for %s with %1d processes\n", 
	  SESS_NAME_ORIGINAL, SESS_PROC_COUNT  
	  ); 
  fprintf(model_template_file, " * file name: %s\n", model_file_name); 
  fprintf(model_template_file, " */\n"); 
  fprintf(model_template_file, "process count = %1d;\n\n", SESS_PROC_COUNT); 
  push_redlib_phase(FLAG_REDLIB_PHASE_VAR_DECLARING); 
  
  GSTATUS[INDEX_REDLIB_CONTROL] 
  = GSTATUS[INDEX_REDLIB_CONTROL] 
  | FLAG_REDLIB_DECLARE_FULL_MODEL;  

  switch (flag_vars & RED_MASK_DECLARE_VARIABLES) { 
  case RED_RENEW_VARIABLES: 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] | FLAG_REDLIB_RENEW_VARS; 
    break; 
  case RED_ADD_VARIABLES: 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] & ~FLAG_REDLIB_RENEW_VARS; 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] 
    & ~FLAG_REDLIB_DECLARE_FULL_MODEL;  
    break; 
  }
  switch (flag_rules & RED_MASK_DECLARE_RULES) { 
  case RED_RENEW_RULES: 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] | FLAG_REDLIB_RENEW_RULES; 
    break; 
  case RED_ADD_RULES: 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] & ~FLAG_REDLIB_RENEW_RULES; 
    GSTATUS[INDEX_REDLIB_CONTROL] 
    = GSTATUS[INDEX_REDLIB_CONTROL] 
    & ~FLAG_REDLIB_DECLARE_FULL_MODEL;  
    break; 
  }
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, leaving change declaration\n", 
    count_sessions, count_change_declaration
  ); 
  #endif 
}
  /* red_change_declaration() */ 
  


 
#if RED_DEBUG_LIB_MODE
int	count_begin_declaration = 0; 
#endif 
  

inline void	red_begin_declaration() { 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, entering begin declaration\n", 
    count_sessions, ++ count_begin_declaration
  ); 
  #endif 
  
  red_change_declaration(RED_RENEW_VARIABLES, RED_RENEW_RULES); 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nLIB %1d:%1d, leaving begin declaration\n", 
    count_sessions, count_begin_declaration
  ); 
  #endif 
}
  /* red_begin_declaration() */ 
  





/* This procedure declares an initial constraint. 
 * But it actually has no real effect in the usage of redlib.  
 * The reason is that in all redlib procedure-calls for 
 * verification tasks, we allow the users to input 
 * diagrams as parameters for the initial condition and target 
 * constraint. 
 * The only use of this procedure is to output an initial condition line 
 * in the model file for the users' reference. 
 */
void 	red_declare_initial(constraint) 
	char	*constraint; 
{ 
  if (   top_redlib_phase() != FLAG_REDLIB_PHASE_VAR_DECLARING
      && top_redlib_phase() != FLAG_REDLIB_PHASE_MODE_DECLARING
      ) {
    printf("\n\nError: declaring initial condition in phase %s with red_initial().\n", 
           phase_name(top_redlib_phase()) 
           ); 
    exit(0); 
  } 
  change_redlib_phase(FLAG_REDLIB_PHASE_INITIAL_DECLARING); 
  fprintf(model_template_file, "\ninitially \n  %s;\n", constraint); 
}
  /* red_declare_initial() */ 



void	red_set_initial(d) 
	struct red_type	*d; 
{
  RT[INDEX_INITIAL] = d; 
}
  /* red_set_initial() */ 
  
  

struct red_type	*red_query_diagram_initial() { 
  check_phase(FLAG_REDLIB_PHASE_ANALYSIS, "red_query_initial()"); 
  return(RT[INDEX_INITIAL]); 
}
  /* red_query_diagram_initial()() */ 


char	*red_query_string_initial() { 
  check_phase(FLAG_REDLIB_PHASE_ANALYSIS, "red_query_string_initial"); 
  return(string_parse_subformula(
    ORIG_PARSE_INITIAL_EXP, 0, FLAG_NO_SUBFORMULA_DEPTH
  ) ); 
}
  /* red_query_string_initial() */ 


/* This procedure does the following steps. 
 * 1. We first close the model template file. 
 * 2. Then we call the parser to read in and analyze the model file. 
 * 3. This step is implemented specifically for the new structure 
 *    of the redlib.  
 *    We want to allow the users to do simulation checking and model-checking 
 *    in the same session. 
 *    Thus we will have the construction of the sync xtions in 
 *    a lazy way. 
 *    That is, we will let do it only when the first invocation of 
 *    model-checking or bisimulation-checking task is to be executed. 
 *    Once that construction has been done, we will set the corresponding 
 *    flags so that next time we don't have to do the same construction 
 *    for the same task. 
 */
void	red_end_declaration(
  int flag_model_processing
) {   
  switch (top_redlib_phase()) { 
  case FLAG_REDLIB_PHASE_VAR_DECLARING: 
    fprintf(model_template_file, "\n/* A dmmy mode */\n"); 
    fprintf(model_template_file, "mode dummy (true) { }\n"); 
    change_redlib_phase(FLAG_REDLIB_PHASE_MODE_DECLARING); 
  case FLAG_REDLIB_PHASE_MODE_DECLARING: 
    red_declare_initial("dummy@(1)"); 
  } 
  check_phase(FLAG_REDLIB_PHASE_INITIAL_DECLARING, "red_end_declaration");
  fclose(model_template_file); 
  pop_redlib_phase(); // back to model input phase.  
  change_redlib_phase(FLAG_REDLIB_PHASE_PARSING); 

  switch (flag_model_processing) { 
  case RED_PARSING_ONLY: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_PARSING_ONLY; 
    break; 
  case RED_NO_REFINED_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE; 
    break;  
  case RED_REFINE_GLOBAL_INVARIANCE: 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_MODEL_PROCESSING) 
    | FLAG_MODEL_REFINED_ABSTRACT_SPACE; 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal model processing option %1d\n", 
      flag_model_processing
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 

  parse_system_description(
    model_file_name, output_file_name, 
    SESS_PROC_COUNT, 
    TASK_REDLIB_SESSION
  ); 
  change_redlib_phase(FLAG_REDLIB_PHASE_ANALYSIS);  
  switch (GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) {
  case FLAG_MODEL_PARSING_ONLY: 
  
    break; 
  case FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE: 
    print_modeling_result("RUN-TIME DECL"); 
    RT[REFINED_GLOBAL_INVARIANCE] = RT[DECLARED_GLOBAL_INVARIANCE]; 
    break; 
  case FLAG_MODEL_REFINED_ABSTRACT_SPACE: 
    print_modeling_result("RUN-TIME DECL"); 
    RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_bck(
      INDEX_INITIAL, 
      DECLARED_GLOBAL_INVARIANCE, 
      INDEX_GOAL, 
      GSTATUS[INDEX_TASK] & MASK_TASK, 
      GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
      0 // no print options are used. 
    ); 
    break; 
  }
} 
  /* red_end_declaration() */ 
  
  
  
void 	red_comment(com) 
	char	*com; 
{ 
  fprintf(model_template_file, "\n/* %s \n */\n", com); 	
}
  /* red_comment() */ 
  
void 	red_define_const(m, i) 
	char	*m; 
	int	i; 
{ 
  fprintf(model_template_file, "#define %s\t%1d\n", m, i); 
}
  /* red_define_const() */ 
  
  
void 	red_declare_variable(int vtype, int lb, int ub, char *f, ...) { 
  char		*name, *real_f; 
  va_list	args; 

  
  string_var(real_f, "", "", f, args); 
  name = malloc(strlen(real_f)+1); 
  sprintf(name, "%s", real_f); 
  
  check_phase(FLAG_REDLIB_PHASE_VAR_DECLARING, "red_declare_variable");
  switch (vtype) { 
  case RED_TYPE_CLOCK: 
    fprintf(model_template_file, "global clock %s;\n", name); 
    break; 
  case RED_TYPE_DISCRETE: 
    fprintf(model_template_file, "global discrete %s: %1d..%1d;\n", name, lb, ub); 
    break; 
  case RED_TYPE_POINTER: 
    fprintf(model_template_file, "global pointer %s;\n", name); 
    break; 
  case RED_TYPE_SYNCHRONIZER: 
    fprintf(model_template_file, "global synchronizer %s;\n", name); 
    break; 
  case RED_TYPE_DENSE: 
    fprintf(model_template_file, "global dense %s;\n", name); 
    break; 
  default: 
    printf("Error: Illegal variable type flag %1d\n", vtype); 
    exit(0); 
  }
}
  /* red_decalre_variable() */




void 	red_declare_local_variable(int vtype, int lb, int ub, char *f, ...) { 
  char		*name, *real_f; 
  va_list	args; 
  
  string_var(real_f, "", ";", f, args); 
  
  name = malloc(strlen(real_f)+1); 
  sprintf(name, "%s", real_f); 
  
  check_phase(FLAG_REDLIB_PHASE_VAR_DECLARING, "red_declare_variable");
  switch (vtype) { 
  case RED_TYPE_CLOCK: 
    fprintf(model_template_file, "local clock %s;\n", name); 
    break; 
  case RED_TYPE_DISCRETE: 
    fprintf(model_template_file, "local discrete %s: %1d..%1d;\n", name, lb, ub); 
    break; 
  case RED_TYPE_POINTER: 
    fprintf(model_template_file, "local pointer %s;\n", name); 
    break; 
  case RED_TYPE_SYNCHRONIZER: 
    fprintf(model_template_file, "local synchronizer %s;\n", name); 
    break; 
  case RED_TYPE_DENSE: 
    fprintf(model_template_file, "dense %s;\n", name); 
    break; 
  default: 
    printf("Error: Illegal variable type flag %1d\n", vtype); 
    exit(0); 
  }
}
  /* red_decalre_local_variable() */  
  
  
  
int	mode_cons_count = 0; 
char	*mode_name; 

void	red_begin_mode(int flag_urgent, char *name, char *inv, ...) { 
  char		*real_f1, *real_f2; 
  va_list	args; 

  string_2var(real_f1, real_f2, name, inv, args); 
  name = malloc(strlen(real_f1)+1); 
  inv = malloc(strlen(real_f2)+1); 
  sprintf(name, "%s", real_f1); 
  sprintf(inv, "%s", real_f2); 
  
  if (top_redlib_phase() != FLAG_REDLIB_PHASE_MODE_DECLARING) { 
    check_phase(FLAG_REDLIB_PHASE_VAR_DECLARING, "red_begin_mode");
    change_redlib_phase(FLAG_REDLIB_PHASE_MODE_DECLARING); 
  }
  push_redlib_phase(FLAG_REDLIB_PHASE_XTION_DECLARING); 

  if (flag_urgent) {
    fprintf(model_template_file, "/* urgent mode %1d: %s */\n", mode_cons_count++, name); 
    fprintf(model_template_file, "urgent mode %s (%s) \{ \n", name, inv); 
  }
  else { 
    fprintf(model_template_file, "/* mode %1d: %s */\n", mode_cons_count++, name); 
    fprintf(model_template_file, "mode %s (%s) { \n", name, inv); 
  } 
  mode_name = name; 
} 
  /* red_begin_mode() */  
  
  
void	red_end_mode() 
{ 
  check_phase(FLAG_REDLIB_PHASE_XTION_DECLARING, "red_end_mode");
  fprintf(model_template_file, "} /* %s */ \n", mode_name); 
  pop_redlib_phase(); 
  check_phase(FLAG_REDLIB_PHASE_MODE_DECLARING, "red_end_mode");  
} 
  /* red_end_mode() */  
  
  
  
int	xtion_cons_count = 1; 

void 	red_transition(char *rule, ...) { 
  char		*real_f; 
  va_list	args; 

  string_var(real_f, "", ";", rule, args); 
  
  rule = malloc(strlen(real_f)+1); 
  sprintf(rule, "%s", real_f); 
  
  check_phase(FLAG_REDLIB_PHASE_XTION_DECLARING, "red_transition()");
  fprintf(model_template_file, "  /* xtion %1d */\n", xtion_cons_count++); 
  fprintf(model_template_file, "  %s\n", rule); 
}
  /* red_transition() */ 
  


void 	red_dense_rate(vname, interval) 
	char	*vname, *interval; 
{ 
  check_phase(FLAG_REDLIB_PHASE_XTION_DECLARING, "red_dense_rate()");
  fprintf(model_template_file, "  rate %s: %s;\n", vname, interval); 
}
  /* red_dense_rate() */ 
  


char	*task_name(t) 
	int	t; 
{ 
  switch (t) { 
  case RED_TASK_SAFETY: 
    return("safety checking"); 
  case RED_TASK_RISK: 
    return("risk checking"); 
  case RED_TASK_MODEL_CHECK: 
    return("tctl checking"); 
  case RED_TASK_SIMULATE: 
    return("simulation"); 
  case RED_TASK_BRANCH_SIM_CHECK: 
    return("simulation checking"); 
  case RED_TASK_BRANCH_BISIM_CHECK: 
    return("bisimulation checking"); 
  default: 
    printf("\nError: Illegal task type flag %1d.\n", t); 
    exit(0); 
  } 	
}
  /* task_name() */ 




char	*red_task_name(task_type) { 
  switch (task_type) { 
  case RED_TASK_SAFETY: 
    return("unsafe"); 
  case RED_TASK_RISK: 
    return("risk"); 
  case RED_TASK_GOAL: 
    return("goal");  
  case RED_TASK_ZENO:  
    return("zeno"); 
  case RED_TASK_DEADLOCK:  
    return("deadlock"); 
  case RED_TASK_MODEL_CHECK: 
    fprintf(RED_OUT, "Error in red_goal_name(%1d:RED_TASK_MODEL_CHECK)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "unexpected goal-oriented task type!\n"); 
    return("MODEL_CHECK"); 
  case RED_TASK_SIMULATE:  
    fprintf(RED_OUT, "Error in red_goal_name(%1d:RED_TASK_SIMULATE)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "unexpected goal-oriented task type!\n"); 
    return("SIMULATE"); 
  case RED_TASK_BRANCH_SIM_CHECK: 
    fprintf(RED_OUT, "Error in red_goal_name(%1d:RED_TASK_BRANCH_SIM_CHECK)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "unexpected goal-oriented task type!\n"); 
    return("BRANCH_SIM_CHECK"); 
  case RED_TASK_BRANCH_BISIM_CHECK: 
    fprintf(RED_OUT, "Error in red_goal_name(%1d:RED_TASK_BRANCH_BISIM_CHECK)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "unexpected goal-oriented task type!\n"); 
    return("BRANCH_BISIM_CHECK"); 
  case RED_TASK_REDLIB_SESSION: 
    fprintf(RED_OUT, "Error in red_goal_name(%1d:RED_TASK_REDLIB_SESSION)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "unexpected goal-oriented task type!\n"); 
    return("REDLIB_SESSION"); 
  default: 
    fprintf(RED_OUT, "Error in red_goal_name(%1d)\n", 
      task_type
    ); 
    fprintf(RED_OUT, "undefined task type!\n"); 
    exit(0); 
  }
}
  /* red_task_name() */ 
  


/* This procedure declares a specification and the related verification task. 
 * But it actually has no real effect in the usage of redlib.  
 * The reason is that in all redlib procedure-calls for 
 * verification tasks, we allow the users to input 
 * diagrams as parameters for the initial condition and target 
 * constraint. 
 * The only use of this procedure is to output a specification line 
 * in the model file for the users' reference. 
 */
int	COUNT_REDLIB_SPEC = 0; 

inline double	red_query_system_time() { 
  return (red_system_time()); 
} 
  /* red_query_system_time() */ 
  
  
inline double 	red_query_user_time() {
  return(red_user_time()); 
}
/* red_query_user_time() */



inline int	red_query_memory() { 
  return(red_memory()); 
}
  /* red_query_memory() */  


void 	red_print_time(char *f, ...)
{
  char			*real_f; 
  va_list		args; 
  
  string_var(real_f, NULL, NULL, f, args);  
  
  fprintf(RED_OUT, "RED TIME:system:%1fsec; user:%1fsec; %s\n", 
    red_system_time(), red_user_time(), real_f 
  );
  /*
  fprintf(RED_OUT, "[SHARED:%1d; DATA:%1d; STACK:%1d]%%%%\n", usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
  */
  fflush(RED_OUT); 
}
/* red_print_time() */





  
  
int	red_query_system_type() { 
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) { 
  case FLAG_SYSTEM_UNTIMED: 
    return(RED_SYSTEM_UNTIMED); 
    break; 
  case FLAG_SYSTEM_TIMED: 
    return(RED_SYSTEM_TIMED); 
    break; 
  case FLAG_SYSTEM_HYBRID:
    return(RED_SYSTEM_HYBRID); 
    break; 
  default: 
    return(RED_SYSTEM_UNKNOWN); 
  } 
}
  /* red_query_system_type() */ 
  



  
  
  
int	red_query_task_type() { 
  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_REDLIB_SESSION: 
    return(RED_TASK_REDLIB_SESSION); 
  case TASK_BRANCHING_BISIM_CHECKING: 
    return(RED_TASK_BRANCH_BISIM_CHECK); 
  case TASK_BRANCHING_SIM_CHECKING: 
    return(RED_TASK_BRANCH_SIM_CHECK);  
    break; 
  case TASK_DEADLOCK:
    return(RED_TASK_DEADLOCK); 
  case TASK_SAFETY:
    return(RED_TASK_SAFETY); 
  case TASK_RISK:
    return(RED_TASK_RISK); 
  case TASK_GOAL:
    return(RED_TASK_GOAL); 
  case TASK_ZENO: 
    return(RED_TASK_ZENO); 
    break;

  case TASK_MODEL_CHECK:
    return(RED_TASK_MODEL_CHECK); 
    break; 
  default: 
    fprintf(RED_OUT, "An unspecified and probably unsupported task type %1d.\n", 
      GSTATUS[INDEX_TASK] & MASK_TASK
    ); 
    exit(0); 
  }
}
  /* red_query_task_type() */ 




int	red_query_task_parametric_analysis() { 
  if (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) { 
    return(RED_PARAMETRIC_ANALYSIS); 
  } 
  else 
    return(RED_NO_PARAMETRIC_ANALYSIS); 
}
  /* red_query_task_parametric_analysis() */ 
  
  

void 	red_declare_spec(task, constraint) 
	int	task; 
	char	*constraint; 
{ 
  int	i; 
  FILE	*spec_template_file; 
  
  if (   top_redlib_phase() != FLAG_REDLIB_PHASE_VAR_DECLARING
      && top_redlib_phase() != FLAG_REDLIB_PHASE_MODE_DECLARING
      && top_redlib_phase() != FLAG_REDLIB_PHASE_INITIAL_DECLARING
      ) {
    printf("\n\nError: declaring specification in phase %s with red_spec().\n", 
           phase_name(top_redlib_phase())
           ); 
    exit(0); 
  } 
  change_redlib_phase(FLAG_REDLIB_PHASE_SPEC_DECLARING); 
  i = strlen(SESS_NAME_FOR_FILE); 
  fprintf(RED_OUT, "\ni=%1d, SESS_NAME_FOR_FILE:%s\n", i, SESS_NAME_FOR_FILE); 
  spec_file_name = malloc(i+9+intlen(COUNT_REDLIB_SPEC)); 
  strcpy(spec_file_name, SESS_NAME_FOR_FILE); 
  sprintf(&(spec_file_name[i]), "spec.%1d.d\0", COUNT_REDLIB_SPEC++); 

  fprintf(RED_OUT, "\ni=%1d, spec_file_name:%s\n", i, spec_file_name); 
  
  if ((spec_template_file = fopen(spec_file_name, "r")) == NULL) {
    printf("Can not open specification file %s.\n", spec_file_name);
    free(spec_file_name); 
    spec_file_name = NULL; 
    bk(0); 
    exit(1); 
  } 
  fprintf(spec_template_file, "\n%s\n  %s;\n", task_name(task), constraint); 
  fclose(spec_template_file); 
}
  /* red_declare_spec() */ 



redgram red_query_diagram_spec_risk() 
{ 
  if (   SPEC_EXP == NULL 
      || SPEC_EXP->type != RED 
      ) {
    fprintf(RED_OUT, "Sorry that the specification is not for risk analysis.\n"); 
    exit(0);    	
  }
  return(SPEC_EXP->u.rpred.red);  
}
  /* red_query_diagram_spec_risk() */ 



char 	*red_query_spec_tctl() 
{ 
  return(string_parse_subformula(PARSE_SPEC, 0, FLAG_NO_SUBFORMULA_DEPTH));  
}
  /* red_query_spec_tctl() */ 
  
  

  
  
/********************************************************
 *  In the following, we have some procedures that return the 
 *  structure information of the model. 
 */
int red_query_var_count() { 
  return(VARIABLE_COUNT); 
} 
  /* red_query_var_count() */ 
  


/****************************************************************
 * In case an inappropriate attribute or an illegal variable is accessed, 
 * redlib just terminates the execution. 
 * If an internal system attribute is accessed, we will politely return 
 * -1.  
 */
int 	red_query_var_attribute(vi, attr) 
	int 	vi, attr; 
{ 
  check_vi(vi, "red_var_attribute"); 
  switch (attr) { 
  case RED_VAR_TYPE: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      return(RED_TYPE_DISCRETE); 
    case TYPE_POINTER: 
      return(RED_TYPE_POINTER);  
    case TYPE_BDD: 
      return(RED_TYPE_BOOLEAN);  
    case TYPE_CLOCK: 
      return(RED_TYPE_CLOCK); 
    case TYPE_DENSE: 
      return(RED_TYPE_DENSE); 
    case TYPE_SYNCHRONIZER: 
      return(RED_TYPE_SYNCHRONIZER); 
    case TYPE_CRD: 
      return(RED_TYPE_CRD); 
    case TYPE_FALSE: 
    case TYPE_TRUE: 
    case TYPE_XTION_INSTANCE: 
    case TYPE_ACTION_INSTANCE: 
    case TYPE_CDD: 
    case TYPE_HDD: 
      printf("\nError: system variable type %1d\n", vi, VAR[vi].TYPE); 
      return(-1); 
    default: 
      printf("\nError: Unknown variable type %1d\n", VAR[vi].TYPE); 
      exit(0); 
    } 
    break; 
  case RED_VAR_SCOPE: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_BDD: 
    case TYPE_CLOCK: 
    case TYPE_DENSE: 
    case TYPE_SYNCHRONIZER: 
      if (VAR[vi].PROC_INDEX == 0) 
        return(RED_SCOPE_GLOBAL); 
      else if (VAR[vi].PROC_INDEX > 0 && VAR[vi].PROC_INDEX <= PROCESS_COUNT) { 
        return(RED_SCOPE_LOCAL); 
      } 
      else { 
        printf("\nError: Illegal variable scope %1d.\n", VAR[vi].PROC_INDEX); 
        exit(0); 
      } 
      break; 
    default: 
      printf("\nError: a system generated variable %1d without scope queried in red_var_attribute().\n", vi); 
      exit(0); 
    } 
    break; 
  case RED_VAR_SYSGEN: 
    if (VAR[vi].STATUS & FLAG_VAR_SYS_GEN) 
      return(1); 
    else 
      return(0); 
  case RED_VAR_PRIMED: 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      return(1); 
    else 
      return(0); 
  case RED_VAR_PROC: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_BDD: 
    case TYPE_CLOCK: 
    case TYPE_DENSE: 
    case TYPE_SYNCHRONIZER: 
      if (VAR[vi].PROC_INDEX == 0) 
        return(0); 
      else if (VAR[vi].PROC_INDEX > 0 && VAR[vi].PROC_INDEX <= PROCESS_COUNT) { 
        return(VAR[vi].PROC_INDEX); 
      } 
      else { 
        printf("\nError: Illegal variable scope %1d.\n", VAR[vi].PROC_INDEX); 
        exit(0); 
      } 
    default: 
      printf("\nError: a system generated variable %1d without scope queried in red_var_attribute().\n", vi); 
      exit(0); 
    } 
    break; 
  case RED_VAR_LB: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_BDD: 
      return(VAR[vi].U.DISC.LB); 
    case TYPE_FLOAT: 
    case TYPE_DOUBLE: 
      fprintf(RED_OUT, 
        "\nERROR, integer query for floating point bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    default: 
      return(-1); 
    }
  case RED_VAR_UB: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_BDD: 
      return(VAR[vi].U.DISC.UB); 
    case TYPE_FLOAT: 
    case TYPE_DOUBLE: 
      fprintf(RED_OUT, 
        "\nERROR, integer query for floating point bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    default: 
      return(-1); 
    }
  case RED_VAR_CLOCK1: 
    if (VAR[vi].TYPE == TYPE_CRD) 
      return(VAR[vi].U.CRD.CLOCK1); 
    else 
      return(-1); 
  case RED_VAR_CLOCK2: 
    if (VAR[vi].TYPE == TYPE_CRD) 
      return(VAR[vi].U.CRD.CLOCK2); 
    else 
      return(-1); 
  case RED_VAR_STREAM_ORDERED: 
    if (VAR[vi].STATUS & FLAG_STREAM_ORDERED) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  default: 
    printf("\nError: Illegal attribute index %1d in red_var_attribute().\n", attr); 
    exit(0); 
  } 
} 
  /* red_query_var_attribute() */ 
  
  
  
  
float 	red_query_var_float_attribute(vi, attr) 
	int 	vi, attr; 
{ 
  check_vi(vi, "red_var_attribute"); 
  switch (attr) { 
  case RED_VAR_LB: 
    switch (VAR[vi].TYPE) { 
    case TYPE_FLOAT:  
      return(VAR[vi].U.FLT.LB); 
    default: 
      fprintf(RED_OUT, 
        "\nERROR, floating point query for integer bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    }
  case RED_VAR_UB: 
    switch (VAR[vi].TYPE) { 
    case TYPE_FLOAT:  
      return(VAR[vi].U.FLT.UB); 
    default: 
      fprintf(RED_OUT, 
        "\nERROR, floating point query for integer bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    }
  default: 
    printf("\nError: Illegal floating attribute index %1d in red_var_attribute().\n", attr); 
    exit(0); 
  } 
} 
  /* red_query_var_float_attribute() */ 
  
  
  
  
float 	red_query_var_double_attribute(vi, attr) 
	int 	vi, attr; 
{ 
  check_vi(vi, "red_var_attribute"); 
  switch (attr) { 
  case RED_VAR_LB: 
    switch (VAR[vi].TYPE) { 
    case TYPE_DOUBLE:  
      return(VAR[vi].U.DBLE.LB); 
    default: 
      fprintf(RED_OUT, 
        "\nERROR, floating point query for integer bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    }
  case RED_VAR_UB: 
    switch (VAR[vi].TYPE) {
    case TYPE_DOUBLE:  
      return(VAR[vi].U.DBLE.UB); 
    default: 
      fprintf(RED_OUT, 
        "\nERROR, floating point query for integer bounds of %s.\n", 
        VAR[vi].NAME
      ); 
      return(-1); 
    }
  default: 
    printf("\nError: Illegal floating attribute index %1d in red_var_attribute().\n", attr); 
    exit(0); 
  } 
} 
  /* red_query_var_double_attribute() */ 
  
  
  
  
char    *red_query_var_name(vi) 
	int 	vi; 
{ 
  check_vi(vi, "red_var_name"); 
  return(VAR[vi].NAME); 
}
  /* red_query_var_name() */ 
  
  
  

int 	red_query_local_var_index(vname, pi) 
	char	*vname; 
	int	pi; 
{ 
  int	vi, ci, cj, vend; 
  char	*tname; 
  
  if (pi == 0) { 
    for (vi = 0; vi < variable_index[TYPE_XTION_INSTANCE][1][0]; vi++) 
      if (!strcmp(vname, VAR[vi].NAME)) 
        return(vi); 
    for (ci = 0; ci < CLOCK_COUNT; ci++) 
      for (cj = 0; cj < CLOCK_COUNT; cj++) 
        if (!strcmp(vname, VAR[ZONE[ci][cj]].NAME)) { 
          return(ZONE[ci][cj]); 	
        } 
    printf("\nError: variable index query for an undeclared global variable %s.\n", 
           vname
           ); 
    return(-1);  
  } 
  
  tname = malloc(strlen(vname) + 5 + intlen(pi)); 
  sprintf(tname, "%s@(%1d)\0", vname, pi); 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) { 
  case FLAG_SYSTEM_UNTIMED: 
  case FLAG_SYSTEM_HYBRID: 
    if (PROCESS_COUNT < pi) 
      vend = variable_index[TYPE_XTION_INSTANCE][pi+1][0]; 
    else 
      vend = MEMORY_START_VI-1; 
    for (vi == variable_index[TYPE_XTION_INSTANCE][pi][0]; vi < vend; vi++) 
      if (!strcmp(vname, VAR[vi].NAME)) {
        free(tname); 
        return(vi); 
      }
    break; 
  case FLAG_SYSTEM_TIMED: 
    if (PROCESS_COUNT < pi) 
      vend = variable_index[TYPE_XTION_INSTANCE][pi+1][0]; 
    else 
      vend = MEMORY_START_VI-1; 
    for (vi == variable_index[TYPE_XTION_INSTANCE][pi][0]; 
         vi < vend && VAR[vi].TYPE != TYPE_CRD; 
         vi++
         ) 
      if (!strcmp(vname, VAR[vi].NAME)) {
      	free(tname); 
        return(vi); 
      }
    break; 
  } 
  printf("\nError: variable index query for an undeclared local variable %s.\n", 
         tname
         ); 
  free(tname); 
  return(-1);  
}
  /* red_query_local_var_index() */ 
  
  


int	red_query_var_index(char *vn) { 
  int	oi, pi, vi; 
  
  for (oi = 0; oi < GLOBAL_COUNT[TYPE_DISCRETE]; oi++) {
    vi = variable_index[TYPE_DISCRETE][0][oi]; 
    if (!strcmp(vn, VAR[vi].NAME)) 
      break; 	
  } 
  if (oi >= GLOBAL_COUNT[TYPE_DISCRETE]) { 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      for (oi = 0; oi < LOCAL_COUNT[TYPE_DISCRETE]; oi++) {
        vi = variable_index[TYPE_DISCRETE][pi][oi]; 
        if (!strcmp(vn, VAR[vi].NAME)) 
          break; 
      }
      if (oi < LOCAL_COUNT[TYPE_DISCRETE]) 
        break; 
    } 
    if (pi > PROCESS_COUNT) { 
      fprintf(RED_OUT, 
        "\nERROR: could not find %s in the declared discretes\n", 
        vn
      ); 
      fprintf(RED_OUT, "       in red_query_var_index().\n"); 
      fflush(RED_OUT); 
      return (-1); 
    } 
  }
  return(vi); 
} 
  /* red_query_var_index() */ 





redgram	red_query_var_active(vi) 
	int	vi; 
{ 
  check_vi(vi, "red_var_active"); 
  switch (VAR[vi].TYPE) { 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
  case TYPE_CLOCK: 
  case TYPE_DENSE: 
    return(VAR[vi].RED_ACTIVE); 
  default: 
    printf("\nError: no activeness predicate for variable %1d:%s\n", 
           vi, VAR[vi].NAME
           ); 
    exit(0); 
  }
} 
  /* red_query_var_active() */ 
  
  
  
redgram red_query_var_inactive(vi)
	int	vi; 
{ 
  check_vi(vi, "red_var_inactive"); 
  
  switch (VAR[vi].TYPE) { 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
  case TYPE_CLOCK: 
  case TYPE_DENSE: 
    return(VAR[vi].RED_INACTIVE); 
  default: 
    printf("\nError: no inactiveness predicate for variable %1d:%s\n", 
           vi, VAR[vi].NAME
           ); 
    exit(0); 
  }
} 
  /* red_query_var_inactive() */ 



int 	red_query_clock_count() { 
  return(CLOCK_COUNT); 
} 
  /* red_query_clock_count() */




int 	red_query_clock_var(ci) 
	int	ci; 
{ 
  if (ci < 0 || ci >= CLOCK_COUNT) { 
    printf("\nError: Illegal clock index %1d in red_clock_var()\n", ci); 
    exit(0); 	
  } 
  return (CLOCK[ci]); 
} 
  /* red_query_clock_var() */ 
  
  
  
  
int 	red_query_zone_index(ci1, ci2) 
	int	ci1, ci2; 
{ 
  return(ZONE[ci1][ci2]); 	
} 
  /* red_query_zone_index() */ 
  
  

/* This procedure returns the delcared transition count in between the 
 * red_begin_declaration() and red_end_declaration(). 
 * Note that red will automatically add one null xtion that 
 * is triggerible in any state and executible by any process.  
 * Thus the returned value is the count of declared transition rules 
 * plus one. 
 */ 
int 	red_query_xtion_count() {
  return(XTION_COUNT); 	
}
  /* red_query_xtion_count() */ 
  
  
  

int 	red_query_xtion_attribute(xi, attr) 
	int	xi, attr; 
{ 
  check_xi(xi, "red_xtion_attribute"); 
  switch (attr) { 
  case RED_XTION_SYNC_COUNT: 
    return(XTION[xi].sync_count); 
  case RED_XTION_SRC_MODE: 
    return(XTION[xi].src_mode_index); 
  case RED_XTION_DST_MODE: 
    return(XTION[xi].dst_mode_index); 
  case RED_XTION_PROCESS_COUNT: 
    return(XTION[xi].process_count); 
  case RED_XTION_STREAM_OP_COUNT: 
    return(XTION[xi].stream_operation_count); 
  default: 
    printf("\nError: Illegal attribute index %1d in red_xtion_attribute().\n", attr); 
    exit(0); 
  } 
} 
  /* red_query_xtion_attribute() */ 
  
  
  
char	*red_query_xtion_src_lines(
  int	xi
) { 
  return(XTION[xi].src_lines); 	
} 
  /* red_query_xtion_src_lines() */ 



int	red_query_xtion_stream_operation(
  int	xi, 
  int	soi  
) {
  check_xi(xi, "red_query_xtion_stream_operation"); 
  if (soi < 0 || soi >= XTION[xi].stream_operation_count) { 
    fprintf(RED_OUT, 
      "\nError: An illegal stream operation index %1d for transition %1d\n", 
      soi, xi 
    ); 
    fprintf(RED_OUT, 
      "       in procedure red_query_xtion_stream_operation().\n"  
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else switch (XTION[xi].stream_operation[soi].operation) { 
  case OP_STREAM_OPEN_INPUT: 
    return(RED_XTION_STREAM_OPEN_INPUT); 
  case OP_STREAM_OPEN_OUTPUT: 
    return(RED_XTION_STREAM_OPEN_OUTPUT); 
  case OP_STREAM_CLOSE: 
    return(RED_XTION_STREAM_CLOSE); 
  case OP_STREAM_INPUT: 
    return(RED_XTION_STREAM_INPUT); 
  case OP_STREAM_OUTPUT: 
    return(RED_XTION_STREAM_OUTPUT); 
  case OP_MALLOC: 
    return(RED_XTION_MALLOC); 
  case OP_FREE: 
    return(RED_XTION_FREE); 
  default: 
    fprintf(RED_OUT, 
      "\nError: unexpected stream operation type %1d in red_query_xtion_stream_operation().\n", 
      XTION[xi].stream_operation[soi].operation
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* red_query_xtion_stream_operation() */ 




char	*red_query_xtion_stream_name(
  int	xi, 
  int	soi  
) {
  check_xi(xi, "red_query_xtion_stream_operation"); 
  if (soi < 0 || soi >= XTION[xi].stream_operation_count) { 
    fprintf(RED_OUT, 
      "\nError: An illegal stream operation index %1d for transition %1d\n", 
      soi, xi  
    ); 
    fprintf(RED_OUT, 
      "       in procedure red_query_xtion_stream_operation().\n" 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else 
    return(VAR[XTION[xi].stream_operation[soi].stream].NAME); 
}
  /* red_query_xtion_stream_name() */ 




redgram	red_query_diagram_xtion_trigger(xi, pi)  
	int	xi, pi; 
{ 
  check_xi(xi, "red_xtion_trigger"); 
  check_pi(pi, "red_xtion_trigger"); 
  return(XTION[xi].red_trigger[pi]); 
}
  /* red_query_diagram_xtion_trigger() */ 


int	red_query_xtion_sync_attribute(
  int	xi, 
  int	si, 
  int	attr
) {
  check_xi(xi, "red_query_xtion_sync_attribute"); 
  if (si < 0 || si >= XTION[xi].sync_count) { 
    fprintf(RED_OUT, 
      "\nError: An illegal synchronization index %1d for transition %1d\n", 
      si, xi  
    ); 
    fprintf(RED_OUT, 
      "       in procedure red_query_xtion_sync_attribute().\n" 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else switch (attr) { 
  case RED_XTION_SYNC_DIRECTION: 
    switch (XTION[xi].sync[si].type) { 
    case FLAG_ACCESS_WRITE: 
      return(RED_XTION_SYNC_XMIT); 
    case FLAG_ACCESS_READ: 
      return(RED_XTION_SYNC_RECV); 
    default: 
      fprintf(RED_OUT, 
        "\nERROR: Unexpected transition %1d's synchronization type \n", xi
      ); 
      fprintf(RED_OUT, 
        "       at procedure red_query_xtion_sync_attribute().\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    break; 
  case RED_XTION_SYNC_QUANTIFIED_ADDRESS: 
    switch (XTION[xi].sync[si].status) {  
    case FLAG_NO_QUANTIFIED_SYNC: 
    case FLAG_ADDRESS_NULL: 
    case FLAG_ADDRESS_MULTIPLE: 
    case FLAG_ADDRESS_DUPLICATE: 
      return(RED_XTION_SYNC_NO_CORRESPONDENCE_REQUIREMENT); 
    case FLAG_ADDRESS_HOLDER: 
      return(RED_XTION_SYNC_QUANTIFIED_CORRESPONDENCE_VAR); 
    case FLAG_ADDRESS_ENFORCER: 
      return(RED_XTION_SYNC_CORRESPONDENCE_EXPRESSION); 
    }
    break; 
  case RED_XTION_SYNC_VAR_INDEX: 
    return(XTION[xi].sync[si].sync_index); 
  case RED_XTION_SYNC_QFD_CORRESPONDENCE_VAR_INDEX: 
    if (XTION[xi].sync[si].status == FLAG_ADDRESS_HOLDER) { 
      return(XTION[xi].sync[si].qsync_vi); 
    }
    else { 
      return(RED_FLAG_UNKNOWN); 
    } 
  default: 
    fprintf(RED_OUT, 
      "\nError: unexpected attribute type %1d in red_query_xtion_sync_attribute().\n", 
      attr
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* red_query_xtion_sync_attribute() */ 




int	red_query_string_xtion_sync(
  int	xi, 
  int	si 
) {
  check_xi(xi, "red_query_xtion_sync_string"); 
  if (si < 0 || si >= XTION[xi].sync_count) { 
    fprintf(RED_OUT, 
      "\nError: An illegal synchronization index %1d for transition %1d\n", 
      si, xi  
    ); 
    fprintf(RED_OUT, 
      "       in procedure red_query_xtion_sync_attribute().\n" 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  return(string_xtion_sync(xi, si)); 
}
  /* red_query_string_xtion_sync() */ 




char	*red_query_string_xtion_sync_correspondence_exp(
  int	xi, 
  int	si
) { 
  check_xi(xi, "red_query_string_xtion_sync_correspondence_exp"); 
  if (si < 0 || si >= XTION[xi].sync_count) { 
    fprintf(RED_OUT, 
      "\nError: An illegal synchronization index %1d for transition %1d\n", 
      si, xi  
    ); 
    fprintf(RED_OUT, 
      "       in procedure red_query_string_xtion_sync_correspondence_exp().\n" 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else if (XTION[xi].sync[si].status == FLAG_ADDRESS_ENFORCER) { 
    return(string_parse_subformula(
      XTION[xi].sync[si].exp_quantification, -1, 0
    ) ); 
  } 
  else { 
    return(NULL); 
  } 
}
  /* red_query_string_xtion_sync_correspondence_exp() */  
  
  

char 	*red_query_string_xtion_action(int xi, int pi) { 
  check_xi(xi, "red_xtion_action_string");  
  check_pi(pi, "red_xtion_action_string"); 
  return(string_statement_instantiate(XTION[xi].statement, pi)); 
} 
  /* red_query_string_xtion_action() */ 
  
  
  
char 	*red_query_string_xtion(
  int	xi, 
  int	pi
) {
  check_xi(xi, "red_xtion_string");  
  check_pi(pi, "red_xtion_string"); 
  return(string_xtion(xi, pi)); 
}
  /* red_query_string_xtion() */ 
  
  
  
int 	red_query_xtion_process(xi, i)  
	int	xi, i; 
{ 
  check_xi(xi, "red_xtion_process");  
  if (i < 0 || i >= XTION[xi].process_count) { 
    printf("\nError: Illegal executable process index %1d for transition %1d\n", i, xi); 
    printf("       in red_xtion_process().\n"); 
    exit(0); 	
  } 
  return(XTION[xi].process[i]); 
} 
  /* red_query_xtion_process() */ 
  
  
int 	red_query_process_count() { 
  return(PROCESS_COUNT); 	
} 
  /* red_query_process_count() */ 
  
  


int	red_query_process_role(int pi) { 
  switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
  case FLAG_GAME_SPEC: 
    return(RED_GAME_SPEC); 
  case FLAG_GAME_MODL: 
    return(RED_GAME_MODL); 
  case FLAG_GAME_ENVR: 
    return(RED_GAME_ENVR); 
  default: 
    return(RED_FLAG_UNKNOWN); 
  } 	
}
  /* red_query_process_role() */ 
  
  
int 	red_query_process_mode_count(pi) 
	int	pi; 
{ 
  check_pi(pi, "red_query_process_mode_count"); 
  return(PROCESS[pi].reachable_mode_count); 
} 
  /* red_query_process_mode_count() */ 
  
  
  
int 	red_query_process_mode(pi, imi) 
	int	pi, imi; 
{ 
  check_pi(pi, "red_query_process_mode"); 
  if (imi < 0 || imi >= PROCESS[pi].reachable_mode_count) { 
    printf("\nError: Illegal reachable mode index %1d for process %1d in red_process_xtion().\n", imi, pi); 
    exit(0); 
  } 
  return(PROCESS[pi].reachable_mode[imi]); 
} 
  /* red_query_process_mode() */ 
  
  
  
int 	red_query_process_xtion_count(pi) 
	int	pi; 
{ 
  check_pi(pi, "red_xtion_trigger"); 
  return(PROCESS[pi].firable_xtion_count); 
} 
  /* red_query_process_xtion_count() */ 
  
  
  
int 	red_query_process_xtion(pi,ixi) 
	int	pi, ixi; 
{ 
  check_pi(pi, "red_process_xtion"); 
  if (ixi < 0 || ixi >= PROCESS[pi].firable_xtion_count) { 
    printf("\nError: Illegal firable transition index %1d for process %1d in red_process_xtion().\n", ixi, pi); 
    exit(0); 
  } 
  return(PROCESS[pi].firable_xtion[ixi]); 
} 
  /* red_query_process_xtion() */ 
  
  
  
int 	red_query_mode_count() { 
  return(MODE_COUNT); 
} 
  /* red_query_mode_count() */ 
  
  
  
int red_query_mode_attribute(mi, attr) 
	int 	mi, attr; 
{ 
  check_mi(mi, "red_mode_attribute"); 
  switch (attr) { 
  case RED_MODE_XTION_COUNT: 
    return(MODE[mi].xtion_count); 
  case RED_MODE_URGENT: 
    if (MODE[mi].status & FLAG_MODE_URGENT) 
      return(1); 
    else 
      return(0); 
  case RED_MODE_PROCESS_COUNT: 
    return(MODE[mi].process_count); 
  default: 
    printf("\nError: Illegal attribute %1d of red_mode_attribute().\n", attr); 
    exit(0); 
  }
} 
  /* red_query_mode_attribute() */ 
  
  
  
  
int red_query_mode_rate(mi, vi, attr) 
	int 	mi, attr; 
{ 
  int	pi, ri; 
  
  check_mi(mi, "red_mode_rate"); 
  check_vi(vi, "red_mode_rate");  
  switch (VAR[vi].TYPE) { 
  case TYPE_CLOCK: 
    /* The rate of a clock is always 1/1. */ 
    return(1); 
  case TYPE_DENSE: 
    break; 
  default: 
    printf("\nError: Illegal rate query for a non-dense variable %1d:%s in red_mode_rate()\n", 
           vi, VAR[vi].NAME
           );  
    exit(0); 
  } 
  pi = VAR[vi].PROC_INDEX; 

  switch (attr) { 
  case RED_MODE_RATE_LB_NUM: 
    for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) { 
      if (MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index == vi) 
        return(MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator); 
    } 
    return(-1*red_hybrid_oo()); 
  case RED_MODE_RATE_LB_DEN: 
    for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) { 
      if (MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index == vi) 
        return(MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator); 
    } 
    return(1); 
  case RED_MODE_RATE_UB_NUM: 
    for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) { 
      if (MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index == vi) 
        return(MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator); 
    } 
    return(red_hybrid_oo()); 
  case RED_MODE_RATE_UB_DEN: 
    for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) { 
      if (MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index == vi) 
        return(MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator); 
    } 
    return(1); 
  default: 
    printf("\nError: Illegal rate bound specification %1d in red_mode_rate().\n", 
           attr
           ); 
    exit(0); 
  }
} 
  /* red_query_mode_rate() */ 
  
  
  
  
char 	*red_query_mode_name(mi)  
	int	mi; 
{ 
  check_mi(mi, "red_mode_name"); 
  return(MODE[mi].name); 
} 
  /* red_query_mode_name() */ 



char	*red_query_mode_src_lines(
  int	mi
) { 
  return(MODE[mi].src_lines); 	
} 
  /* red_query_mode_src_lines() */ 



  
  
int 	red_query_mode_xtion(mi, ixi) 
	int	mi, ixi; 
{ 
  check_mi(mi, "red_mode_xtion"); 
  if (ixi < 0 || ixi >= MODE[mi].xtion_count) { 
    printf("\nError: Illegal executable transition index %1d for mode %1d:%s\n", 
           ixi, mi, MODE[mi].name
           ); 
    printf("      in red_mode_xtion().\n"); 
    exit(0); 	
  } 
  return(MODE[mi].xtion[ixi]); 
} 
  /* red_query_mode_xtion() */ 
  
  
int red_query_mode_process(mi, ipi)  
	int mi, ipi; 
{ 
  check_mi(mi, "red_mode_process"); 
  if (ipi < 0 || ipi >= MODE[mi].process_count) { 
    printf("\nError: Illegal executable process index %1d for mode %1d:%s\n", 
           ipi, mi, MODE[mi].name
           ); 
    printf("      in red_mode_xtion().\n"); 
    exit(0); 	
  } 
  return(MODE[mi].process[ipi]); 
} 
  /* red_query_mode_process() */ 
  
  

redgram red_query_diagram_mode_invariance(mi, pi)  
	int	mi, pi; 
{ 
  check_mi(mi, "red_mode_invariance"); 
  check_pi(pi, "red_mode_invariance"); 
  return (MODE[mi].invariance[pi].red); 
} 
  /* red_query_diagram_mode_invariance() */ 




redgram red_query_diagram_declared_invariance() {
  return (RT[DECLARED_GLOBAL_INVARIANCE]); 
} 
  /* red_query_diagram_declared_invariance() */ 




  
int 	red_query_sync_bulk_depth() {
  switch (DEPTH_ENUMERATIVE_SYNCHRONIZATION) { 
  case DEPTH_ENUMERATIVE_DEFAULT: 
    return(RED_DEPTH_ENUMERATIVE_DEFAULT);  
  case DEPTH_ENUMERATIVE_ALL: 
    return(RED_DEPTH_ENUMERATIVE_ALL); 
  default: 
    return(DEPTH_ENUMERATIVE_SYNCHRONIZATION); 
  }
}
  /* red_query_sync_bulk_depth() */  
  
  

void    red_set_sync_bulk_depth(d) 
	int	d; 
{ 
  if (d < RED_DEPTH_ENUMERATIVE_ALL) { 
    printf("\Error: Illegal non-positive sync bulk depth %1d.\n", d); 	
    exit(0); 
  } 
  switch (d) { 
  case RED_DEPTH_ENUMERATIVE_DEFAULT: 
//    DEPTH_ENUMERATIVE_SYNCHRONIZATION = DEPTH_ENUMERATIVE_DEFAULT;  
    break; 
  case RED_DEPTH_ENUMERATIVE_ALL: 
    DEPTH_ENUMERATIVE_SYNCHRONIZATION = DEPTH_ENUMERATIVE_ALL; 
    break; 
  default: 
    DEPTH_ENUMERATIVE_SYNCHRONIZATION = d; 
    break; 
  }
} 
  /* red_set_sync_bulk_depth() */
   
   
   
int red_query_sync_xtion_count(int flag_sync_xtion_table_choice) { 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    return(SYNC_XTION_COUNT + 1); 	
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    return(SYNC_XTION_COUNT_GAME + 1); 
  }
} 
  /* red_query_sync_xtion_count() */  
  
  
  
int 	red_query_sync_xtion_party_count(
  int 	flag_sync_xtion_table_choice, 
  int	sxi
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_query_sync_xtion_party_count"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 
    else 
      return(SYNC_XTION[sxi].party_count); 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 
    else 
      return(SYNC_XTION_GAME[sxi].party_count); 
  }
}
  /* red_query_sync_xtion_party_count() */ 
  
  
  

int 	red_query_sync_xtion_party_process(
  int 	flag_sync_xtion_table_choice, 
  int	sxi, 
  int	party_index
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_query_sync_xtion_party_process"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 
    else if (   party_index >= SYNC_XTION[sxi].party_count
             || party_index < 0
             ) { 
      return(RED_FLAG_UNKNOWN); 
    } 
    else 
      return(SYNC_XTION[sxi].party[party_index].proc); 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 
    else if (   party_index >= SYNC_XTION_GAME[sxi].party_count
             || party_index < 0
             ) { 
      return(RED_FLAG_UNKNOWN); 
    } 
    else 
      return(SYNC_XTION_GAME[sxi].party[party_index].proc); 
  }
}
  /* red_query_sync_xtion_party_process() */ 
  
  
  

int 	red_query_sync_xtion_party_xtion(
  int 	flag_sync_xtion_table_choice, 
  int	sxi, 
  int	party_index
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_query_sync_xtion_party_xtion"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 
    else if (   party_index >= SYNC_XTION[sxi].party_count
             || party_index < 0
             ) { 
      return(RED_FLAG_UNKNOWN); 
    } 
    else 
      return(SYNC_XTION[sxi].party[party_index].xtion); 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 
    else if (   party_index >= SYNC_XTION_GAME[sxi].party_count
             || party_index < 0
             ) { 
      return(RED_FLAG_UNKNOWN); 
    } 
    else 
      return(SYNC_XTION_GAME[sxi].party[party_index].xtion); 
  }
}
  /* red_query_sync_xtion_party_xtion() */ 
  
  
  

  
  
  

redgram red_query_diagram_sync_xtion_trigger(
  int 	flag_sync_xtion_table_choice, 
  int	sxi
) { 
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_sync_xtion_trigger"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    if (sxi == SYNC_XTION_COUNT) 
      return((struct red_type *) RED_FLAG_UNKNOWN); 
    else 
      return(SYNC_XTION[sxi].red_trigger); 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return((struct red_type *) RED_FLAG_UNKNOWN); 
    else 
      return(SYNC_XTION_GAME[sxi].red_trigger); 
  }
} 
  /* red_query_diagram_sync_xtion_trigger() */ 
  
  
  
  
char    *red_query_string_sync_xtion_action(  
  int 	flag_sync_xtion_table_choice, 
  int 	sxi
) { 
  char				**ps, *s; 
  int				ipi, len, sx_count; 
  struct sync_xtion_type	*sxt; 
  
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_sync_xtion_action_string"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    sxt = SYNC_XTION; 
    sx_count = SYNC_XTION_COUNT; 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    sxt = SYNC_XTION_GAME; 
    sx_count = SYNC_XTION_COUNT_GAME; 
  } 

  if (sxi == sx_count) {
    s = malloc(20+ intlen(sxi)); 
    sprintf(s, "sync bulk %1d, actions", sxi); 
    return(s); 
  }  

  ps = (char **) malloc(sxt[sxi].party_count * sizeof(char *)); 
  len = 0; 
  for (ipi = 0; ipi < sxt[sxi].party_count; ipi++) { 
    ps[ipi] = string_statement_instantiate(
      sxt[sxi].party[ipi].statement, 
      sxt[sxi].party[ipi].proc
    );
    len = len + strlen(ps[ipi]); 
  } 
  if (len == 0) { 
    s = malloc(2); 
    sprintf(s, ";"); 	
  } 
  else { 
    s = malloc(len+1); 
    len = 0; 
    for (ipi = 0; ipi < sxt[sxi].party_count; ipi++) { 
      strcpy(&(s[len]), ps[ipi]); 
      len = len + strlen(ps[ipi]); 
      free(ps[ipi]); 
    } 
    free(ps); 
  }
  return(s); 
}
  /* red_query_string_sync_xtion_action() */  
  
  
  
char    *red_query_string_sync_xtion(
  int 	flag_sync_xtion_table_choice, 
  int	sxi
) {
  char				*ss, *ts, *ans; 
  int				sl, tl, sx_count; 
  struct sync_xtion_type	*sxt; 
  
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_sync_xtion_string"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    sxt = SYNC_XTION; 
    sx_count = SYNC_XTION_COUNT; 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    sxt = SYNC_XTION_GAME; 
    sx_count = SYNC_XTION_COUNT_GAME; 
  } 

  if (sxi == sx_count) {
    ans = malloc(11+ intlen(sxi)); 
    sprintf(ans, "sync bulk %1d", sxi); 
    return(ans); 
  } 
  ss = red_query_string_sync_xtion_action(flag_sync_xtion_table_choice, sxi); 
  ts = red_diagram_string(sxt[sxi].red_trigger); 
  sl = strlen(ss); 
  tl = strlen(ts); 
  ans = malloc(sl+tl+13); 
  sprintf(ans, "when (%s) may %s", ts, ss); 
  free(ss); 
  free(ts); 
  
  return(ans); 
}
  /* red_query_string_sync_xtion() */ 
  
  
    
  
  
redgram red_query_diagram_xtion_sync_bulk(  
  int 	flag_sync_xtion_table_choice 
) {
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    return(RT[XI_SYNC_BULK]); 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    return(RT[XI_GAME_SYNC_BULK]); 
  }
}
  /* red_query_diagram_xtion_sync_bulk() */ 
  
  
  
redgram red_query_diagram_triggers_from_sync_bulk_with_roles(
  int 	flag_sync_xtion_table_choice, 
  int	flag_game_roles 
) { 
  int			result, pi, fxi, ixi, xi; 
  struct red_type	*b, *conj; 
  
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    b = RT[XI_SYNC_BULK_WITH_TRIGGERS]; 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    b = RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS]; 
  } 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if (!(   (   (PROCESS[pi].status & FLAG_GAME_MODL) 
              && (flag_game_roles & RED_GAME_MODL) 
              )  
          || (   (PROCESS[pi].status & FLAG_GAME_SPEC)
              && (flag_game_roles & RED_GAME_SPEC) 
              )
          || (   (PROCESS[pi].status & FLAG_GAME_ENVR)
              && (flag_game_roles & RED_GAME_ENVR) 
        ) )   ) 
      continue; 

    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      xi = PROCESS[pi].firable_xtion[ixi]; 
      if (   !xi 
          || XTION[xi].statement == NULL 
          || XTION[xi].statement->op == UNCHANGED
          ) {
        continue; 
      } 
      conj = ddd_one_constraint(b, fxi, xi, xi); 
      conj = red_type_eliminate(conj, TYPE_XTION_INSTANCE); 
      RT[result] = red_bop(OR, RT[result], conj); 
    } 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_query_diagram_xtion_sync_bulk_with_trigger() */ 
  
  
  
  
  
  
redgram red_query_diagram_xtion_sync_bulk_with_trigger(
  int 	flag_sync_xtion_table_choice 
) { 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    return(RT[XI_SYNC_BULK_WITH_TRIGGERS]); 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    return(RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS]); 
  }
} 
  /* red_query_diagram_xtion_sync_bulk_with_trigger() */ 
  
  
  
redgram red_query_diagram_xtion_sync_bulk_whole(
  int 	flag_sync_xtion_table_choice 
) {
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) 
    return(RT[XI_SYNC_ALL]); 
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    return(RT[XI_GAME_SYNC_ALL]); 
  }
}
  /* red_query_diagram_xtion_sync_bulk_whole() */ 
  
  
  
  
  
  
  
int 	red_clock_oo() { 
  return(CLOCK_POS_INFINITY); 	
} 
  /* red_clock_oo() */ 
  
  
  
int  	red_hybrid_oo() {
  return(HYBRID_POS_INFINITY); 	
}
  /* red_hybrid_oo() */ 
  
  
  
  
redgram red_true() {
  return(NORM_NO_RESTRICTION); 	
}
  /* red_true() */ 
  
  
  
redgram red_false() {
  return(NORM_FALSE); 	
}
  /* red_false() */
  

int	red_var_prob() { 
  return(PROB_VALUE); 	
}
  /* red_var_prob() */ 



int	red_var_prob_work() { 
  return(PROB_WORK_VALUE); 	
}
  /* red_var_prob_work() */ 



  
int	count_diagram = 0; 

char	*ddd_new_filename(mid) 
	char	*mid; 
{ 
  int	i; 
  char	*stfile_name; 

/*  i = strlen(SESS_NAME_ORIGINAL); 
  stfile_name = malloc(i + strlen(mid) + intlen(++count_diagram)+1); 
  sprintf(stfile_name, "%s%s%1d", SESS_NAME_ORIGINAL, mid, count_diagram); 

  fprintf(RED_OUT, "in ddd_new_filename with length %1d for %s\n", 
    i + strlen(mid) + intlen(count_diagram)+1, 
    stfile_name
  ); 
  return(stfile_name); 
*/
  fprintf(RED_OUT, "count_diagram=%1d\n", ++count_diagram); 
  return("redlib.diagram.tmp"); 
}
  /* ddd_new_filename() */ 
  
  


redgram red_diagram_old(char *f, ...) { 
  int			i, len, real_len, j, v; 
  char			*real_f, *stfile_name, *s; 
  FILE			*stfile; 
  struct ps_exp_type	*e; 
  redgram		d; 
  va_list		args; 

  string_var(real_f, "global formula ", ";", f, args);  
 
  stfile_name = ddd_new_filename(".gf."); 
  
  stfile = fopen(stfile_name, "w"); 
  fprintf(stfile, "global formula %s;\n", real_f); 
  fclose(stfile); 
  free(real_f); 
  
  fprintf(RED_OUT, "Read in a new formula.\n"); 
  fflush(RED_OUT); 
  
  redlibrestart(redlibin); 
  if ((redlibin = fopen(stfile_name, "r")) == NULL) {
    printf("Can not open specification file %s.\n", spec_file_name);
    exit(1); 
  }
  else {
    flag_redlib_input_source = FLAG_INPUT_FILE; 
    redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
//  free(stfile_name); 
  }
  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
  pcform(PARSER_INPUT_FORMULA); 
  free(real_f); 
  
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_GLOBAL) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a formula is expected in red_diagram().\n"); 
    exit(0); 
  } 
/*
  fprintf(RED_OUT, "\nThe parsed goal after indirect referencing.\n");
//  pcform(PARSER_INPUT_FORMULA);
  print_parse_subformula_structure(PARSER_INPUT_FORMULA, 0); 
*/
  e = analyze_tctl(PARSER_INPUT_FORMULA, FLAG_ANALYZE_INITIAL, 0); 
  d = e->u.rpred.red; 
/*
  fprintf(RED_OUT, "\nred_diagram():\n"); 
  red_print_line(d); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
*/  
  return(d); 
} 
  /* red_diagram_old() */ 



  
redgram red_diagram(char *f, ...) { 
  char			*real_f; 
  struct ps_exp_type	*e; 
  redgram		d; 
  va_list		args; 

  string_var(real_f, "global formula ", ";", f, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 
/*
  fprintf(RED_OUT, "count_diagram %1d, redlib_input_string='%s', length=%1d\n", 
    ++count_diagram, redlib_input_string, redlib_input_string_len
  ); 
  fflush(RED_OUT); 
*/
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
//  free(stfile_name); 
//  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
//  pcform(PARSER_INPUT_FORMULA); 
  
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_GLOBAL) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a formula is expected in red_diagram().\n"); 
    exit(0); 
  } 
/*
  fprintf(RED_OUT, "\nBefore analyzing TCTL for the spec:\n"); 
  pcform(PARSER_INPUT_FORMULA); 
*/  
  e = analyze_tctl(PARSER_INPUT_FORMULA, FLAG_ANALYZE_INITIAL, 0); 
  d = e->u.rpred.red; 
 /*
  fprintf(RED_OUT, "\nred_diagram():\n"); 
  red_print_line(d); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
 */  
  return(d); 
} 
  /* red_diagram() */ 
  
  

redgram red_diagram_events(char *f, ...) { 
  char			*real_f; 
  redgram		d; 
  va_list		args; 

  string_var(real_f, "global events ", ";", f, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 
/*
  fprintf(RED_OUT, "count_diagram %1d, redlib_input_string='%s', length=%1d\n", 
    ++count_diagram, redlib_input_string, redlib_input_string_len
  ); 
  fflush(RED_OUT); 
*/
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
//  free(stfile_name); 
//  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
//  pcform(PARSER_INPUT_FORMULA); 
  
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_GLOBAL_EVENTS) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a formula is expected in red_diagram().\n"); 
    exit(0); 
  } 
/*
  fprintf(RED_OUT, "\nBefore analyzing TCTL for the spec:\n"); 
  pcform(PARSER_INPUT_FORMULA); 
*/  
  var_index_fillin(PARSER_INPUT_FORMULA);
/*
  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
  pcform(PARSE_SPEC); 
*/  
//  fillin_indirect_reference(PROC_GLOBAL, PARSER_INPUT_FORMULA);

  d = red_global(PARSER_INPUT_FORMULA, 0, 0); 
 /*
  fprintf(RED_OUT, "\nred_diagram():\n"); 
  red_print_line(d); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
 */  
  return(d); 
} 
  /* red_diagram_events() */ 
  
  

struct ps_exp_type	*ps_exp_from_string(char *f, ...) { 
  char			*real_f; 
  redgram		d; 
  va_list		args; 

  string_var(real_f, "global events ", ";", f, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 
/*
  fprintf(RED_OUT, "count_diagram %1d, redlib_input_string='%s', length=%1d\n", 
    ++count_diagram, redlib_input_string, redlib_input_string_len
  ); 
  fflush(RED_OUT); 
*/
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
//  free(stfile_name); 
//  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
//  pcform(PARSER_INPUT_FORMULA); 
  
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_GLOBAL_EVENTS) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a formula is expected in red_diagram().\n"); 
    exit(0); 
  } 
/*
  fprintf(RED_OUT, "\nBefore analyzing TCTL for the spec:\n"); 
  pcform(PARSER_INPUT_FORMULA); 
*/  
  var_index_fillin(PARSER_INPUT_FORMULA);
/*
  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
  pcform(PARSE_SPEC); 
*/  
//  fillin_indirect_reference(PROC_GLOBAL, PARSER_INPUT_FORMULA);

  return(PARSER_INPUT_FORMULA); 
 /*
  fprintf(RED_OUT, "\nred_diagram():\n"); 
  red_print_line(d); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
 */  
} 
  /* ps_exp_from_string() */ 
  
  

redgram red_diagram_local(int pi, char *f, ...) 
{ 
  char			*real_f; 
  struct ps_exp_type	*e; 
  redgram		d; 
  va_list		args; 
  
  string_var(real_f, "local formula ", ";", f, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 

/*  
  fprintf(RED_OUT, "Read in a new formula.\n"); 
  fflush(RED_OUT); 
*/  
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 

  if (   TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_GLOBAL
      && TYPE_PARSE_CHOICE != TYPE_PARSE_FORMULA_LOCAL
      ) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a formula is expected in red_local_diagram().\n"); 
    exit(0); 
  }
  var_index_fillin(PARSER_INPUT_FORMULA);
/*
  fprintf(RED_OUT, "\nafter parsing spec for PC=%1d\n", PROCESS_COUNT); 
  pcform(PARSE_SPEC); 
*/  
//  fillin_indirect_reference(pi, PARSER_INPUT_FORMULA);

  d = red_local(PARSER_INPUT_FORMULA, pi, 0); 

  return(d); 
} 
  /* red_diagram_local() */ 



redgram red_diagram_discrete(redgram d, int vi, int lb, int ub) {
  switch (VAR[vi].TYPE) {
  case TYPE_BDD: 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_HDD: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal variable type %1d in red_diagram_discrete().\n", 
      vi 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  if (d == NORM_FALSE)  
    return(NORM_FALSE); 
  else if (d == NORM_NO_RESTRICTION || d->var_index > vi) 
    return(ddd_lone_subtree(d, vi, lb, ub)); 
  else 
    return(ddd_one_constraint(d, vi, lb, ub)); 
}
  /* red_diagram_discrete() */ 


 
redgram red_diagram_float(redgram d, int vi, float lb, float ub) { 
  switch (VAR[vi].TYPE) {
  case TYPE_FLOAT: 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal variable type %1d in red_diagram_float().\n", 
      vi 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  if (d == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (d == NORM_NO_RESTRICTION || d->var_index > vi) 
    return(fdd_lone_subtree(d, vi, lb, ub)); 
  else 
    return(fdd_one_constraint(d, vi, lb, ub)); 
} 
  /* red_diagram_float() */ 



redgram red_diagram_double(redgram d, int vi, double lb, double ub) { 
  switch (VAR[vi].TYPE) {
  case TYPE_DOUBLE: 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal variable type %1d in red_diagram_double().\n", 
      vi
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  if (d == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (d == NORM_NO_RESTRICTION || d->var_index > vi) 
    return(dfdd_lone_subtree(d, vi, lb, ub)); 
  else 
    return(dfdd_one_constraint(d, vi, lb, ub)); 
}
  /* red_diagram_double() */ 


redgram	red_quantify(redgram d, char *f, ...) {
  char				*real_f; 
  struct ps_exp_type		*e; 
  va_list			args; 
  struct ps_quantify_link_type	*q, *nq; 
  int				t, i; 
  
  string_var(real_f, "quantify ", ";", f, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 

  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "Read in a new quantify formula: %s.\n", real_f); 
  fflush(RED_OUT); 
  #endif 

  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_QUANTIFY) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a quantification expression is expected in red_quantify().\n"); 
    exit(0); 
  } 
  for (i = 0, q = PARSER_QUANTIFICATION_LIST; 
       q; 
       i++, q = q->next_ps_quantify_link 
       ) { 
    #if RED_DEBUG_LIB_MODE
    fprintf(RED_OUT, "\n===============================\nQ %1d:\n", i); 
    #endif 
    
    switch (q->op_restriction) { 
    case AND: 
      d = red_bop(AND, d, q->red_restriction); 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "AND with :"); 
      red_print_line(q->red_restriction); 
      fprintf(RED_OUT, "\nresult :\n"); 
      red_print_graph(d); 
      fprintf(RED_OUT, "\n"); 
      #endif 
      break; 
      
    case OR: 
      d = red_bop(OR, d, q->red_restriction); 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "OR with :"); 
      red_print_line(q->red_restriction); 
      fprintf(RED_OUT, "\nresult :\n"); 
      red_print_graph(d); 
      fprintf(RED_OUT, "\n"); 
      #endif 
      break; 
      
    case IMPLY: 
      d = red_bop(OR, d, red_complement(q->red_restriction)); 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "IMPLICATION with :"); 
      red_print_line(q->red_restriction); 
      fprintf(RED_OUT, "\nresult :\n"); 
      red_print_graph(d); 
      fprintf(RED_OUT, "\n"); 
      #endif 
      break; 
      
    case NOT: 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "NOT :\n"); 
      #endif 
      d = red_complement(d); 
      break; 
    } 
    #if RED_DEBUG_LIB_MODE
    fprintf(RED_OUT, "Q %1d: after the restriciton:\n", i); 
    red_print_graph(d); 
    #endif 
    
    switch (q->op) { 
    case FORALL: 
      d = red_complement(d); 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "Q %1d: after the inner complement:\n", i); 
      red_print_graph(d); 
      #endif 
      
      switch (VAR[q->var_index].TYPE) { 
      case TYPE_CLOCK: 
        RT[t = RT_TOP++] = d;
        d = red_bypass_DOWNWARD(t, VAR[q->var_index].U.CLOCK.CLOCK_INDEX); 
        RT_TOP--; // t 
        d = red_variable_eliminate(d, q->var_index); 
        break; 

      case TYPE_DENSE: 
        RT[t = RT_TOP++] = d;
        d = hybrid_bypass_DOWNWARD(t, q->var_index); 
        RT_TOP--; // t 
        d = red_variable_eliminate(d, q->var_index); 
        break; 
      case TYPE_POINTER: 
      case TYPE_BDD:   
      case TYPE_DISCRETE: 
        d = red_variable_eliminate(d, q->var_index); 
        break; 
      } 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "Q %1d: after the existential quantification:\n", i); 
      red_print_graph(d); 
      #endif 
      
      d = red_complement(d); 
      #if RED_DEBUG_LIB_MODE
      fprintf(RED_OUT, "Q %1d: after the outer complementation:\n", i); 
      red_print_graph(d); 
      #endif 
      
      break; 
    case EXISTS: 
      switch (VAR[q->var_index].TYPE) { 
      case TYPE_CLOCK: 
        RT[t = RT_TOP++] = d; 
        d = red_bypass_DOWNWARD(t, VAR[q->var_index].U.CLOCK.CLOCK_INDEX); 
        RT_TOP--; // t 
        d = red_variable_eliminate(d, q->var_index); 
        break; 

      case TYPE_DENSE: 
        RT[t = RT_TOP++] = d;
        d = hybrid_bypass_DOWNWARD(t, q->var_index); 
        RT_TOP--; // t 
        d = red_variable_eliminate(d, q->var_index); 
        break; 
      case TYPE_POINTER: 
      case TYPE_BDD:   
      case TYPE_DISCRETE: 
        d = red_variable_eliminate(d, q->var_index); 
        break; 
      } 
      break; 
    } 
    #if RED_DEBUG_LIB_MODE
    fprintf(RED_OUT, "\nQ %1d: Result a quantification iteration:\n", i); 
    red_print_graph(d); 
    #endif 
  }
  return(d); 
}
  /* red_quantify() */  
  
  
  


redgram red_and(d1, d2) 
	redgram  d1, d2; 
{ 
  return(red_bop(AND, d1, d2)); 
} 
  /* red_and() */  
 
  
  
redgram red_or(d1, d2) 
	redgram  d1, d2; 
{ 
  return(red_subsume(red_bop(OR, d1, d2))); 
} 
  /* red_or() */  



redgram red_extract(d1, d2) 
	redgram	d1, d2; 
{
  return(red_bop(EXTRACT, d1, d2)); 
}
  /* red_extract() */  
  
  


redgram red_subtract(d1, d2) 
	redgram	d1, d2; 
{
  return(red_space_subtract(d1, d2)); 
}
  /* red_subtract() */  
  
  


  
  


redgram red_not(d)
	redgram	d; 
{ 
  return(red_complement(d)); 
}
  /* red_not() */ 
  
  
  
#define red_discrete_constraint	ddd_one_constraint

#define red_zone_constraint	crd_one_constraint

#define red_hybrid_constraint	hrd_one_constraint

redgram red_FM_elm(d, vi) 
	redgram d; 
	int	vi; 
{ 
  int	w; 
  
  check_vi(vi, "red_FM_elm"); 
  switch (VAR[vi].TYPE) { 
  case TYPE_CLOCK: 
    RT[w = RT_TOP++] = d; 
    RT[w] = red_time_clock_eliminate(
      red_bypass_DOWNWARD(w, VAR[vi].U.CLOCK.CLOCK_INDEX), 
      VAR[vi].U.CLOCK.CLOCK_INDEX
    ); 
    RT_TOP--; // w
    return(RT[w]); 
  case TYPE_DENSE: 
    RT[w = RT_TOP++] = d; 
    RT[w] = red_variable_eliminate(hybrid_bypass_DOWNWARD(w, vi), vi); 
    RT_TOP--; // w 
    
    return(RT[w]); 
  default: 
    return(red_variable_eliminate(d, vi)); 
  } 
} 
  /* red_FM_elm() */ 
  
  
  
redgram red_time_bck(dst, path)
	redgram 	dst, path; 
{ 
  int		d, p; 
  redgram	r; 
  
  RT[d = RT_TOP++] = dst; 
  RT[p = RT_TOP++] = path; 
  if (   path == RT[TYPE_TRUE] 
      || path == RT[DECLARED_GLOBAL_INVARIANCE]
      || path == RT[REFINED_GLOBAL_INVARIANCE]
      ) 
    r = red_game_time_progress_bck(
      NULL, 
      d, 
      DECLARED_GLOBAL_INVARIANCE, 
      MASK_GAME_ROLES, 
      TYPE_FALSE 
    ); 
  else { 
    r = red_game_time_progress_bck(NULL, d, p, MASK_GAME_ROLES, TYPE_FALSE); 
  }
  RT_TOP = RT_TOP-2; 
  return(r); 
} 
  /* red_time_bck() */ 
  
  
  
redgram red_time_fwd(src, path)
	redgram 	src, path; 
{ 
  int		d, p; 
  redgram	r; 
  
  RT[d = RT_TOP++] = src; 
  RT[p = RT_TOP++] = path; 
  r = red_time_progress_fwd(d, p); 
  RT_TOP = RT_TOP-2; 
  return(r); 
} 
  /* red_time_fwd() */ 
  
  

  
/* These are the normalizatoin operation code for red_norm.   
#define	RED_NORM_ZONE_NONE			(0x01000)
#define RED_NORM_ZONE_MAGNITUDE_REDUCED		(0x02000)
#define	RED_NORM_ZONE_CLOSURE			(0x03000)
#define RED_NORM_ZONE_MAGNITUDE_ONE_RIPPLE	(0x04000) 

#define RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD	(0x00010000)
#define RED_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD	(0x00020000)
#define RED_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD	(0x00040000)
#define RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD	(0x00080000)
#define RED_NORM_HYBRID_PROOF_OBLIGATIONS			(0x00100000)
*/ 
int	red_norm_code(int op) { 
  switch (op) { 
  case RED_NORM_ZONE_NONE: 
    return(FLAG_NORM_ZONE_NONE); 
  case RED_NORM_ZONE_MAGNITUDE_REDUCED: 
    return(FLAG_NORM_ZONE_MAGNITUDE_REDUCTION); 
  case RED_NORM_ZONE_CLOSURE: 
    return(FLAG_NORM_ZONE_CLOSURE); 
  case RED_NORM_ZONE_CLOSURE_EQ: 
    return(FLAG_NORM_ZONE_CLOSURE_EQ); 
  case RED_NORM_ZONE_MAGNITUDE_ONE_RIPPLE:  
    return(FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE); 
  case RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD: 
    return(FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD); 
  case RED_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD: 
    return(FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD); 
  case RED_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD: 
    return(FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD); 
  case RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD: 
    return(FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD); 
  case RED_NORM_HYBRID_PROOF_OBLIGATIONS: 
    return(FLAG_NORM_HYBRID_PROOF_OBLIGATIONS); 
  default: 
    fprintf(RED_OUT, "Sorry, an unsupported normalization option %1d.\n", 
      op
    ); 
    fflush(RED_OUT); 
    return(FLAG_NORM_ZONE_NONE); 
  }
} 
  /* red_norm_code() */ 


  
  
  
redgram red_norm(
  redgram	d, 
  int		op
) { 
  int	tmp_flag_normal_form, w; 
  
  tmp_flag_normal_form = GSTATUS[INDEX_NORM_ZONE]; 
  GSTATUS[INDEX_NORM_ZONE] = red_norm_code(op); 
  RT[w = RT_TOP++] = d; 
  d = red_hull_normalize(w); 
  RT_TOP--; // w 
  
  GSTATUS[INDEX_NORM_ZONE] = tmp_flag_normal_form; 
  return(d); 
}
  /* red_norm() */ 
  



redgram red_time_measurement_initial_fwd(src, path, time_lb, time_ub)
  redgram 	src, path; 
  int		time_lb, time_ub; 
{ 
  int		d, p; 
  redgram	r; 
  
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
      == FLAG_SYSTEM_UNTIMED
      ) { 
    return (src);         	
  } 

  RT[d = RT_TOP++] = src; 
  RT[d] = red_time_clock_eliminate(RT[d], TIME); 
  RT[d] = red_time_clock_eliminate(RT[d], MODAL_CLOCK); 
  RT[d] = crd_one_constraint(RT[d], ZONE[0][TIME], -1 * time_lb); 
  RT[d] = crd_one_constraint(RT[d], ZONE[TIME][0], time_ub); 
  RT[d] = crd_one_constraint(RT[d], ZONE[0][MODAL_CLOCK], 0); 
  RT[d] = crd_one_constraint(RT[d], ZONE[MODAL_CLOCK][0], 0); 
  
  RT[p = RT_TOP++] = path; 
  r = red_time_progress_fwd(d, p); 
  RT_TOP = RT_TOP-2; // p, d
  
  r = red_norm(r, RED_NORM_ZONE_CLOSURE); 
  
  return(r); 
} 
  /* red_time_measurement_initial_fwd() */ 
  

redgram red_measured_time_fwd(src, path)
	redgram 	src, path; 
{ 
  int		d, p; 
  redgram	r; 
  
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
      == FLAG_SYSTEM_UNTIMED
      ) { 
    return (src);         	
  }
  
  RT[d = RT_TOP++] = src; 
  RT[d] = red_time_clock_eliminate(RT[d], MODAL_CLOCK); 
  RT[d] = crd_one_constraint(RT[d], ZONE[0][MODAL_CLOCK], 0); 
  RT[d] = crd_one_constraint(RT[d], ZONE[MODAL_CLOCK][0], 0); 
  
  RT[p = RT_TOP++] = path; 
  r = red_time_progress_fwd(d, p); 
  RT_TOP = RT_TOP-2; // p, d
  
  r = red_norm(r, RED_NORM_ZONE_CLOSURE); 
  
  return(r); 
} 
  /* red_measured_time_fwd() */ 
  

void	red_measure_last_time(redgram d, int *lb_ptr, int *ub_ptr) { 
  red_measure_time_clock(d, MODAL_CLOCK, lb_ptr, ub_ptr); 
}
  /* red_measure_last_time() */ 
  
  
void	red_measure_acc_time(redgram d, int *lb_ptr, int *ub_ptr) { 
  red_measure_time_clock(d, TIME, lb_ptr, ub_ptr); 
}
  /* red_measure_acc_time() */ 
  
  

int	count_st = 0; 


redgram red_xtion_bck(d, pi, xi, flag_approx) 
	redgram	d; 
	int	pi, xi; 
{ 
  int	w, tmp_flag; 
  
  check_pi(pi, "red_xtion_bck"); 
  check_xi(xi, "red_xtion_bck"); 
  if (XTION[xi].sync_count > 0) { 
    printf("\nWarning: trying to execute transition rule %1d \n", xi); 
    printf("         with process %1d synchronizers in red_xtion_bck()\n.", 
           pi
           ); 
    exit(0); 
  } 
  tmp_flag = GSTATUS[INDEX_APPROX] & MASK_APPROX; 
  GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_APPROX) 
			| (MASK_APPROX & flag_approx); 
  RT[w = RT_TOP++] = d; 
  d = red_statement_bck(w, pi, XTION[xi].statement, 
    (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY), 
    FLAG_ACTION_DELAYED_EVAL 
  ); 
  RT_TOP--; /* w */ 
  GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_APPROX) 
			| (MASK_APPROX & tmp_flag); 
  d = red_delayed_eval(XTION[xi].red_trigger[pi], pi, d); 
  return (d); 
}
  /* red_xtion_bck() */ 
  
  
  
  
redgram red_xtion_fwd(d, pi, xi, flag_approx)
	redgram	d; 
	int	pi, xi, flag_approx; 
{ 
  int	w, tmp_flag; 
  
  check_pi(pi, "red_xtion_fwd"); 
  check_xi(xi, "red_xtion_fwd"); 
  if (XTION[xi].sync_count > 0) { 
    printf("\nWarning: trying to execute transition rule %1d \n", xi); 
    printf("         with process %1d synchronizers in red_xtion_bck()\n.", 
           pi
           ); 
    exit(0); 
  } 
  tmp_flag = GSTATUS[INDEX_APPROX] & MASK_APPROX; 
  GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_APPROX) 
			| (MASK_APPROX & flag_approx); 
  d = red_delayed_eval(XTION[xi].red_trigger[pi], pi, d); 
  RT[w = RT_TOP++] = d; 
  d = red_statement_fwd(w, pi, XTION[xi].statement, 
    (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY), 
    FLAG_ACTION_DELAYED_EVAL 
  ); 
  RT_TOP--; /* w */ 
  GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_APPROX) 
			| (MASK_APPROX & tmp_flag); 
  return (d); 
}
  /* red_xtion_fwd() */ 
  
  


int	TOP_STATUS = -1, stack_status[10][GSTATUS_SIZE]; 

void	push_time_experiment_flags(int flag_experiment) { 
  switch (flag_experiment & RED_MASK_TIME_PROGRESS_ANALYSIS) { 
  case RED_TIME_PROGRESS_ANALYSIS_NONE: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_NONE; 
    break; 
  case RED_TIME_PROGRESS_ANALYSIS_TCTCTL: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL; 
    break; 
  case RED_TIME_PROGRESS_ANALYSIS_ADVANCED:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED; 
    break; 
  } 
  
  if (flag_experiment & RED_TIME_TCONVEXITY_SHARED_PARTITIONS) 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_TCONVEXITY_SHARED_PARTITIONS) 
    | FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS; 
  else 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_TCONVEXITY_SHARED_PARTITIONS) 
    | FLAG_TIME_TCONVEXITY_NO_SHARED_PARTITIONS; 

  switch (flag_experiment & RED_MASK_TIME_PROGRESS_OPTIONS) { 
  case RED_TIME_PROGRESS_NONE: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_NONE; 
    break; 
  case RED_TIME_PROGRESS_ASSUMED_CONVEXITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
    break; 

  case RED_TIME_PROGRESS_SPLIT_CONVEXITIES: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES; 
    break; 

  case RED_TIME_PROGRESS_FULL_FORMULATION: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_FULL_FORMULATION; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_SHARED_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_CONCAVITY; 
    break; 

  case RED_TIME_PROGRESS_EASY_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_EASY_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_SHARED_EASY_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY; 
    break; 
  } 

}
  /* push_time_experiment_flags() */ 
  
  
  
void	push_sync_xtion_experiment_flags(int flag_experiment) { 
  push_time_experiment_flags(flag_experiment); 
}
  /*   push_sync_xtion_experiment_flags() */ 


inline void   push_sync_xtion_status(
  int	flag_optional_task, 
  int	flag_game_roles, 
  int 	flag_time_progress, 
  int	flag_normality, 
  int	flag_action_approx, 
  int	flag_reduction, 
  int	flag_state_approx, 
  int	flag_symmetry, 
  int	flag_experiment 
) { 
  int	gi; 
  
  TOP_STATUS++; 
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    stack_status[TOP_STATUS][gi] = GSTATUS[gi]; 
  } 
  switch (flag_optional_task) { 
  case RED_TASK_SAFETY: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SAFETY; 
    break; 
  case RED_TASK_RISK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_RISK; 
    break; 
  case RED_TASK_GOAL: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
    break; 
  case RED_TASK_ZENO: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_ZENO; 
    break; 
  case RED_TASK_DEADLOCK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_DEADLOCK; 
    break; 
  case RED_TASK_MODEL_CHECK:  
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_MODEL_CHECK; 
    break; 
  case RED_TASK_SIMULATE:  
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_SIMULATE; 
    break; 
  case RED_TASK_BRANCH_SIM_CHECK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_BRANCHING_SIM_CHECKING; 
    break; 
  case RED_TASK_BRANCH_BISIM_CHECK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_BRANCHING_BISIM_CHECKING; 
    break;   
  }
  if (flag_game_roles & RED_GAME_MODL) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_MODL; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_MODL; 

  if (flag_game_roles & RED_GAME_SPEC) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_SPEC; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_SPEC; 

  if (flag_game_roles & RED_GAME_ENVR) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_ENVR; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_ENVR; 
  
  switch (flag_time_progress) { 
  case RED_TIME_PROGRESS: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS]
    | FLAG_TIME_PROGRESS; 
    break; 
  case RED_NO_TIME_PROGRESS: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS]
    & ~FLAG_TIME_PROGRESS; 
    break; 
  } 

  switch (flag_normality) { 
  case RED_NORM_ZONE_NONE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_NONE; 
    break; 
  case RED_NORM_ZONE_MAGNITUDE_REDUCED: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_MAGNITUDE_REDUCTION; 
    break; 
  case RED_NORM_ZONE_CLOSURE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_CLOSURE; 
    break; 
  case RED_NORM_ZONE_MAGNITUDE_ONE_RIPPLE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE; 
    break; 
  }
  
  if (flag_normality & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD;
  if (flag_normality & RED_NORM_HYBRID_PROOF_OBLIGATIONS) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_PROOF_OBLIGATIONS;  

  switch (flag_action_approx) { 
  case RED_NO_ACTION_APPROX: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_NO_ACTION_APPROX; 
    break; 
  case RED_ACTION_APPROX_NOXTIVE: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_ACTION_APPROX_NOXTIVE; 
    break;  
  case RED_ACTION_APPROX_UNTIMED: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_ACTION_APPROX_UNTIMED; 
    break; 
  } 
  
  switch (flag_reduction) { 
  case RED_NO_REDUCTION_INACTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_NO_REDUCTION_INACTIVE; 
    break; 
  case RED_REDUCTION_INACTIVE_NOXTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
    break; 
  case RED_REDUCTION_INACTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_REDUCTION_INACTIVE; 
    break; 
  } 
  
  switch (flag_state_approx & RED_MASK_APPROX) { 
  case RED_NOAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_NOAPPROX; 
    break; 
  case RED_UAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_UAPPROX; 
    break; 
  case RED_OAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_OAPPROX; 
    switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) { 
    case RED_OAPPROX_STRATEGY_GAME: 
      GSTATUS[INDEX_APPROX] 
      = GSTATUS[INDEX_APPROX] 
      | FLAG_OAPPROX_STRATEGY_GAME; 
      switch (flag_state_approx & MASK_OAPPROX_SPEC_GAME) { 
      case RED_NOAPPROX_SPEC_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_SPEC_GAME; 
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAG_MAG;
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAGONAL: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_SPEC_GAME_UNTIMED: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_UNTIMED; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MODE_ONLY: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MODE_ONLY;
        break;  
      case RED_OAPPROX_SPEC_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_NONE;
        break;  
      }     
    
      switch (flag_state_approx & MASK_OAPPROX_MODL_GAME) { 
      case RED_NOAPPROX_MODL_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_MODL_GAME; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_MODL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_MODL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_MODL_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_MODL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_ENVR_GAME) {
      case RED_NOAPPROX_ENVR_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_ENVR_GAME;
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_ENVR_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_ENVR_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_ENVR_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_ENVR_GAME_NONE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_GLOBAL_GAME) {
      case RED_NOAPPROX_GLOBAL_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_GLOBAL_GAME; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_NONE;
        break;  
      }
      break; 
    } // switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) 
    break; 
  } //  switch (flag_state_approx & RED_MASK_APPROX) { 
  
  switch (flag_symmetry) { 
  case RED_NO_SYMMETRY: 
    GSTATUS[INDEX_SYMMETRY] = GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY; 
    break; 
    
  case RED_SYMMETRY_ZONE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_ZONE; 
    break; 
  case RED_SYMMETRY_DISCRETE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_DISCRETE_GENERAL;  
    break; 
  case RED_SYMMETRY_POINTER: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE; 
    break; 
  case RED_SYMMETRY_STATE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_STATE; 
    break; 
  } 

  push_sync_xtion_experiment_flags(flag_experiment); 
} 
  /* push_sync_xtion_status() */  



inline void	pop_sync_xtion_status() {  
  int	gi; 
  
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    GSTATUS[gi] = stack_status[TOP_STATUS][gi]; 
  } 
  TOP_STATUS--; 
}
  /* pop_sync_xtion_status() */  
  


#define FLAG_MARSHALL_FWD	1
#define FLAG_MARSHALL_BCK	-1 

void	sync_xtion_marshall(
  int		flag_dir, 
  char		*pname, 
  redgram	dfrom, 
  redgram	dpath, 
  int		flag_sync_xtion_table_choice, 
  int		sxi
) {
  if (dfrom == NULL) { 
    switch (flag_dir) { 
    case FLAG_MARSHALL_BCK: 
      fprintf(RED_OUT, 
        "\nERROR: NULL destination diagram to %s().\n", pname 
      ); 
      break; 
    case FLAG_MARSHALL_FWD: 
      fprintf(RED_OUT, 
        "\nERROR: NULL source diagram to %s().\n", pname 
      ); 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nERROR: NULL from diagram to %s().\n", pname 
      ); 
      break; 
    } 
    bk(); 
  } 
  else if (dpath == NULL) { 
    fprintf(RED_OUT, 
      "\nERROR: NULL path diagram to %s().\n", pname
    ); 	
    bk(); 
  } 
  else if (   flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION 
           && (sxi < 0  || sxi > SYNC_XTION_COUNT) 
           ) {
    fprintf(RED_OUT, 
      "\nERROR: Illegal synchronous transition index %1d \n", 
      sxi 
    ); 
    fprintf(RED_OUT, "       in %s().\n", pname);        	
    bk(); 
  } 
  else if (   flag_sync_xtion_table_choice == RED_USE_GAME_SYNC_XTION 
           && (sxi < 0 || sxi > SYNC_XTION_COUNT_GAME)  
           ) {
    fprintf(RED_OUT, 
      "\nERROR: Illegal game synchronous transition index %1d \n", sxi 
    ); 
    fprintf(RED_OUT, "       in %s().\n", pname);        	
    bk(); 
  }  
}
  /* sync_xtion_marshall() */


void	exit_without_support(
  char	*outdated, 
  char	*replacement
) { 
  fprintf(RED_OUT, 
    "\nERROR: Sorry that %s is no longer supported.\n", outdated 
  ); 
  fprintf(RED_OUT, "  Please use %s \n", replacement); 
  fprintf(RED_OUT, "  instead. \n\n"); 
  fflush(RED_OUT); 
  exit(0); 
} 
  /* exit_without_support() */ 


redgram red_sync_xtion_string_bck( 
  redgram	ddst, 
  redgram	dpath, 
  int		flag_optional_task, 
  int		flag_game_roles,  
  int		flag_time_progress, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int		flag_symmetry,  
  int		flag_experiment,  
  char		*sxt, ...
) { 
  struct sync_xtion_type		*psxt; 
  int					w, dst, path, 
  					tmp_flag_approx,  
  					tmp_flag_roles, 
  					tmp_flag_time;  
  char					*real_f; 
  struct ps_exp_type			*e; 
  va_list				args; 
  struct parse_redlib_party_link_type	*p; 
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_string_bck", 
    ddst, dpath, RED_USE_DECLARED_SYNC_XTION, 0
  ); 

  exit_without_support("red_sync_xtion_string_bck()", 
    "red_sync_xtion_event_bck() or red_sync_xtion_event_string_bck()" 
  ); 
  
  string_var(real_f, "xtions ", "", sxt, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 

/*  
  fprintf(RED_OUT, "Read in a new formula.\n"); 
  fflush(RED_OUT); 
*/  
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 

  if (TYPE_PARSE_CHOICE != TYPE_PARSE_SYNC_XTION) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", real_f); 
    fprintf(RED_OUT, "       when a formula is expected in red_sync_xtion_string_bck().\n"); 
    exit(0); 
  }
  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect.  
   There should not be time progress. 
*/
  for (p = PARSER_INPUT_SYNC_XTION->party_list; 
       p; 
       p = p->next_parse_redlib_party_link
       ) { 
    RT[dst] = red_general_statement_bck(
      dst, p->proc, p->xtion->statement, flag_state_approx, 
      FLAG_ACTION_DELAYED_EVAL 
    ); 
    switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
    case FLAG_NO_REDUCTION_INACTIVE: 
      break; 
    case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
      RT[dst] = process_inactive_variable_eliminate_noxtive(
        dst, ITERATE_PI
      );
      break; 
    case FLAG_REDUCTION_INACTIVE: 
      RT[dst] = process_inactive_variable_eliminate(
        dst, ITERATE_PI
      );
      break; 
    }
  } 
  for (p = PARSER_INPUT_SYNC_XTION->party_list; 
       p; 
       p = p->next_parse_redlib_party_link
       ) { 
    RT[dst] = red_delayed_eval(p->xtion->red_trigger[p->proc], 
      p->proc, RT[dst]
    ); 
  } 
  if (RT[dst] != NORM_FALSE) {
    RT[dst] = red_precondition_postprocessing(
      dst, NULL, 
      path,  
      NORM_FALSE, 
      NORM_FALSE, 
      NULL, 
      -1, // not an index to RT[sync_bulk]
      TYPE_TRUE // for postprocessing 
    );
  } 
  garbage_collect(FLAG_GC_SILENT);

  RT[dst] = red_subsume(RT[dst]);
/*
*/
  for (p = PARSER_INPUT_SYNC_XTION->party_list; 
       p; 
       p = p->next_parse_redlib_party_link
       ) { 
    free_ps_st(p->xtion->statement); 
    free(p->xtion->red_trigger); 
  } 
  free(PARSER_INPUT_SYNC_XTION->party_list); 
  free(PARSER_INPUT_SYNC_XTION); 

  RT_TOP = RT_TOP - 2; /* dst, path */ 
  pop_sync_xtion_status(); 
  return (RT[dst]); 
}
  /* red_sync_xtion_string_bck() */  
  
  
  
redgram red_sync_xtion_string_fwd( 
  redgram	dsrc, 
  redgram	dpath, 
  int		flag_optional_task, 
  int		flag_game_roles,  
  int		flag_time_progress, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int		flag_symmetry,  
  int		flag_experiment, 
  char		*sxt, ...
) { 
  struct sync_xtion_type		sx; 
  int					w, src, path, ipi, 
					tmp_flag_approx, 
  					tmp_flag_time, 
  					tmp_flag_roles; 
  char					*real_f; 
  struct ps_exp_type			*e; 
  va_list				args; 
  struct parse_redlib_party_link_type	*p; 
  
  sync_xtion_marshall(FLAG_MARSHALL_FWD, "red_sync_xtion_string_fwd", 
    dsrc, dpath, RED_USE_DECLARED_SYNC_XTION, 0
  ); 

  string_var(real_f, "xtions ", "", sxt, args);  

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = real_f; 
  redlib_input_string_len = strlen(real_f) + 2; /* 2 for two NULLs */ 

/*  
  fprintf(RED_OUT, "Read in a new formula.\n"); 
  fflush(RED_OUT); 
*/  
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
  sx.status = PARSER_INPUT_SYNC_XTION->status; 
  sx.party_count = PARSER_INPUT_SYNC_XTION->party_count; 
  sx.party = (struct sync_party_type *) malloc(
    sx.party_count * sizeof(struct sync_party_type)
  ); 
  for (ipi = 0, p = PARSER_INPUT_SYNC_XTION->party_list; 
       p; 
       ipi++, p = p->next_parse_redlib_party_link
       ) { 
    sx.party[ipi].xtion = p->xtion->index; 
    sx.party[ipi].proc = p->proc; 
    sx.party[ipi].red_trigger = p->xtion->red_trigger[p->proc]; 
    sx.party[ipi].statement = p->xtion->statement; 
  } 
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_SYNC_XTION) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", real_f); 
    fprintf(RED_OUT, "       when a formula is expected in red_sync_xtion_string_bck().\n"); 
    exit(0); 
  }
  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[src = RT_TOP++] = dsrc; 
  RT[path = RT_TOP++] = dpath; 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nREDLIB: before, sync_xtion_fwd(sxi=%1d)\nsrc:%x\n", 
    sxi, RT[src]
  ); 
//  red_print_graph(RT[src]); 
  fprintf(RED_OUT, "path:%x\n",RT[path]); 
//  red_print_graph(RT[path]); 
  #endif 
  
  RT[src] = red_postcondition_sync_SPECIFIC(
    src, 
    path, 
    NORM_FALSE, 
    NORM_FALSE, 
    &sx, 
    TYPE_TRUE // for postprocessing 
  ); 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nREDLIB: after sync_xtion_fwd(sxi=%1d)\nsrc:%x\n", 
    sxi, RT[src]
  ); 
//  red_print_graph(RT[src]); 
  #endif 

  free(sx.party); 
  for (p = PARSER_INPUT_SYNC_XTION->party_list; 
       p; 
       p = p->next_parse_redlib_party_link
       ) { 
    free_ps_st(p->xtion->statement); 
    free(p->xtion->red_trigger); 
  } 
  free(PARSER_INPUT_SYNC_XTION->party_list); 
  free(PARSER_INPUT_SYNC_XTION); 

  RT_TOP = RT_TOP-2; /* src, path */ 
  pop_sync_xtion_status(); 
  return (RT[src]); 
}
  /* red_sync_xtion_string_fwd() */  
  


  
  
redgram red_sync_xtion_bulk_bck(
  redgram	ddst, 
  redgram	dpath, 
  int		flag_sync_xtion_table_choice, 
  int		flag_optional_task, 
  int		flag_game_roles,  
  int		flag_time_progress, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int		flag_symmetry,  
  int		flag_experiment 
) { 
  int	dst, path, shared_discontinuity, flag_result;  
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_bulk_bck", 
    ddst, dpath, flag_sync_xtion_table_choice, 0 
  ); 

  exit_without_support("red_sync_xtion_bulk_bck()", 
    "red_sync_xtion_event_bck() or red_sync_xtion_event_string_bck()" 
  ); 
  
  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect.  There should not be time progress. 
*/
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[dst] = red_precondition_sync_bulk( 
      NULL, // the reachable_return record, 
          // NULL since the initial condition is FALSE.   
      dst, 
      NULL, path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE,  // the initial states for reachability 

      NORM_FALSE, 
      NORM_FALSE, 
      XI_SYNC_BULK, // RT[XI_SYNC_BULK] is the bulk representation of the 
                  // sync transitions.  
      XI_SYNC_BULK_WITH_TRIGGERS, 
      &flag_result, 

      TYPE_TRUE // for postprocessing 
    ); 
  }
  else  {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bulk bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bulk bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[dst] = red_precondition_sync_bulk( 
      NULL, // the reachable_return record, 
          // NULL since the initial condition is FALSE.   
      dst, 
      NULL, path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE,  // the initial states for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      
      XI_GAME_SYNC_BULK, // RT[XI_SYNC_BULK] is the bulk representation of the 
                  // sync transitions.  
      XI_GAME_SYNC_BULK_WITH_TRIGGERS, 
      &flag_result,  
      TYPE_TRUE // for postprocessing 
    ); 
  }
/*
*/
  RT_TOP = RT_TOP-2; /* dst, path */ 
  
  pop_sync_xtion_status(); 
  return(RT[dst]); 
} 
  /* red_sync_xtion_bulk_bck() */  

  
  
redgram red_sync_xtion_bulk_fwd(
	redgram dsrc, 
	redgram dpath, 
	int	flag_sync_xtion_table_choice, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 
	int	flag_experiment 
) { 
  int	src, path, flag;  
  
  sync_xtion_marshall(FLAG_MARSHALL_FWD, "red_sync_xtion_bulk_fwd", 
    dsrc, dpath, flag_sync_xtion_table_choice, 0 
  ); 
  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[src = RT_TOP++] = dsrc; 
  RT[path = RT_TOP++] = dpath; 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[src] = red_postcondition_sync_bulk( 
      NULL, // no goal check and reachability recording 
      src, 
      path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE, // the goal for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      XI_SYNC_BULK,  // RT[XI_SYNC_BULK] is the bulk representation of the 
                   // sync transitions.  
      TYPE_TRUE, // for postprocessing 
      &flag 
    );  
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bulk fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bulk fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[src] = red_postcondition_sync_bulk( 
      NULL, // no goal check and reachability recording 
      src, 
      path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE, // the goal for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      XI_GAME_SYNC_BULK, // RT[XI_GAME_SYNC_BULK] is the bulk representation of the 
                        // sync transitions.  
      TYPE_TRUE, // for postprocessing 
      &flag 
    );  
  }
  
  RT_TOP = RT_TOP-2; /* src, path */ 
  pop_sync_xtion_status(); 
  return(RT[src]); 
} 
  /* red_sync_xtion_bulk_fwd() */ 
  
  
  

  


  
redgram red_sync_xtion_bck( 
  redgram 	ddst, 
  redgram 	dpath, 
  int		flag_sync_xtion_table_choice, 
  int		sxi, 
  int		flag_optional_task, 
  int		flag_game_roles,  
  int		flag_time_progress, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int		flag_symmetry, 
  int		flag_experiment 
) { 
  int	dst, path, flag_result;  
  
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_sync_xtion_bck"
  ); 
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_bck", 
    ddst, dpath, flag_sync_xtion_table_choice, sxi
  ); 

  if (   (   flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION 
          && sxi == SYNC_XTION_COUNT 
          )
      || (   flag_sync_xtion_table_choice == RED_USE_GAME_SYNC_XTION 
          && sxi == SYNC_XTION_COUNT_GAME  
      )   )   
    return(red_sync_xtion_bulk_bck(
      ddst, dpath, 
      flag_sync_xtion_table_choice,
      flag_optional_task, 
      flag_game_roles,  
      flag_time_progress, 
      flag_normality, 
      flag_action_approx, 
      flag_reduction, 
      flag_state_approx, 
      flag_symmetry, 
      flag_experiment  
    ) ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 
    
  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect.  
   There should not be time progress. 
*/
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[dst] = red_precondition_sync_SPECIFIC( 
      dst, 
      NULL, path,  
      NORM_FALSE, 
      NORM_FALSE, 
      &(SYNC_XTION[sxi]), 
      &flag_result,  
      TYPE_TRUE // for postprocessing 
    ); 
  }
  else {
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[dst] = red_precondition_sync_SPECIFIC( 
      dst, 
      NULL, path,  
      NORM_FALSE, 
      NORM_FALSE, 
      &(SYNC_XTION_GAME[sxi]), 
      &flag_result,  
      TYPE_TRUE // for postprocessing 
    ); 
  }
/*
*/
  RT_TOP = RT_TOP - 2; /* dst, path */ 
  pop_sync_xtion_status(); 
  return (RT[dst]); 
} 
  /* red_sync_xtion_bck() */ 
  
  
  
redgram red_sync_xtion_fwd( 
	redgram dsrc, 
	redgram dpath, 
	int	flag_sync_xtion_table_choice, 
	int	sxi, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 
	int	flag_experiment 
) { 
  int	src, path;  
  
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_sync_xtion_fwd"
  ); 
  sync_xtion_marshall(FLAG_MARSHALL_FWD, "red_sync_xtion_fwd", 
    dsrc, dpath, flag_sync_xtion_table_choice, sxi
  ); 

  if (   (   flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION 
          && sxi == SYNC_XTION_COUNT 
          )
      || (   flag_sync_xtion_table_choice == RED_USE_GAME_SYNC_XTION 
          && sxi == SYNC_XTION_COUNT_GAME  
      )   )   
    return(red_sync_xtion_bulk_fwd(
      dsrc, dpath, 
      flag_sync_xtion_table_choice, 
      flag_optional_task, 
      flag_game_roles,  
      flag_time_progress, 
      flag_normality, 
      flag_action_approx, 
      flag_reduction, 
      flag_state_approx, 
      flag_symmetry, 
      flag_experiment  
    ) ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 
  
  RT[src = RT_TOP++] = dsrc; 
  RT[path = RT_TOP++] = dpath; 
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nREDLIB: before, sync_xtion_fwd(sxi=%1d)\nsrc:%x\n", 
    sxi, RT[src]
  ); 
//  red_print_graph(RT[src]); 
  fprintf(RED_OUT, "path:%x\n",RT[path]); 
//  red_print_graph(RT[path]); 
  #endif 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[src] = red_postcondition_sync_SPECIFIC(
      src, 
      path, 
      NORM_FALSE, 
      NORM_FALSE, 
      &(SYNC_XTION[sxi]), 
      TYPE_TRUE // for postprocessing 
    ); 
  }
  else { 
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[src] = red_postcondition_sync_SPECIFIC(
      src, 
      path, 
      NORM_FALSE, 
      NORM_FALSE, 
      &(SYNC_XTION_GAME[sxi]), 
      TYPE_TRUE // for postprocessing 
    ); 
  }
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nREDLIB: after sync_xtion_fwd(sxi=%1d)\nsrc:%x\n", 
    sxi, RT[src]
  ); 
//  red_print_graph(RT[src]); 
  #endif 
  RT_TOP = RT_TOP-2; /* src, path */ 
  pop_sync_xtion_status(); 
  return (RT[src]); 
} 
  /* red_sync_xtion_fwd() */ 
  
  


redgram red_sync_xtion_given_bulk_bck( 
	redgram ddst, 
	redgram dpath, 
	redgram dsxt_bulk, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 
	int	flag_experiment 
) { 
  int	dst, path, shared_discontinuity, flag_result, 
	sxi_bulk, sxi_bulk_with_trigger;  
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_given_bulk_bck", 
    ddst, dpath, RED_USE_DECLARED_SYNC_XTION, SYNC_XTION_COUNT 
  ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
  RT[sxi_bulk = RT_TOP++] = dsxt_bulk; 
  RT[sxi_bulk_with_trigger = RT_TOP++] = red_add_trigger_sync_bulk(dsxt_bulk); 
/* This is incorrect, there should not be time progress. 
*/
  RT[dst] = red_precondition_sync_bulk( 
    NULL, // the reachable_return record, 
          // NULL since the initial condition is FALSE.   
    dst, 
    NULL, path, // RT[path] is an invariance condition for reachable states
    INDEX_FALSE, // the initial states for reachability 
    NORM_FALSE, 
    NORM_FALSE, 
    sxi_bulk, // RT[sxi_bulk] is the bulk representation of the 
                          // sync transitions.  
    sxi_bulk_with_trigger, 
    &flag_result,   
    TYPE_TRUE // for postprocessing 
  );  

  RT_TOP = RT_TOP-4; /* dst, path, 
                      * sxi_bulk, sxi_bulk_with_trigger   
                      */ 
  pop_sync_xtion_status(); 
  return(RT[dst]); 
} 
  /* red_sync_xtion_given_bulk_bck() */  
  
  
  
redgram red_sync_xtion_given_bulk_fwd( 
	redgram dsrc, 
	redgram dpath, 
	redgram dsxt_bulk, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 
	int	flag_experiment 
) { 
  int	src, path, shared_discontinuity, sxi_bulk, sxi_bulk_with_trigger, 
	flag;  
  
  sync_xtion_marshall(FLAG_MARSHALL_FWD, "red_sync_xtion_given_bulk_bck", 
    dsrc, dpath, RED_USE_DECLARED_SYNC_XTION, SYNC_XTION_COUNT 
  ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[src = RT_TOP++] = dsrc; 
  RT[path = RT_TOP++] = dpath; 
  RT[sxi_bulk = RT_TOP++] = dsxt_bulk; 
  RT[src] = red_postcondition_sync_bulk( 
    NULL, // no goal check and reachability recording 
    src, 
    path, 
    INDEX_FALSE, // the goal state for reachability 
    NORM_FALSE, 
    NORM_FALSE, 
    sxi_bulk, // RT[sxi_bulk] is the bulk representation of the 
                          // sync transitions.  
    TYPE_TRUE, // for postprocessing 
    &flag 
  );  
  RT_TOP = RT_TOP-3; /* dst, path, sxi_bulk, sxi_bulk_with_trigger   */ 
  pop_sync_xtion_status(); 
  return(RT[src]); 
}
  /* red_sync_xtion_given_bulk_fwd() */  
  
  


  
redgram red_sync_xtion_all_bck(
	redgram	ddst, 
	redgram	dpath, 
	int	flag_sync_xtion_table_choice, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry,  
	int	flag_experiment 
) { 
  int	dst, path, shared_discontinuity, flag_result, result;  
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_all_bck", 
    ddst, dpath, flag_sync_xtion_table_choice, 0
  ); 

  exit_without_support("red_sync_xtion_all_bck()", 
    "red_sync_xtion_event_bck() or red_sync_xtion_event_string_bck()" 
  ); 
    
  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect, there should not be time progress. 
*/
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[result] = red_precondition_sync_ITERATIVE(
      NULL, // the reachable_return record, 
            // NULL since the initial condition is FALSE.  
      dst, 
      NULL, path,  
      INDEX_FALSE, // the initial states for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      &flag_result,    
      TYPE_TRUE // for postprocessing 
    ); 
    RT[result] = red_bop(OR, RT[result], 
      red_precondition_sync_bulk(
        NULL, // the reachable_return record, 
              // NULL since the initial condition is FALSE.  
        dst, 
        NULL, path, // RT[path] is an invariance condition for reachable states
        INDEX_FALSE, // the initial states for reachability 
        RT[result], 
        NORM_FALSE, 
        XI_SYNC_BULK, // RT[XI_SYNC_BULK] is the bulk representation of the 
                          // sync transitions.  
        XI_SYNC_BULK_WITH_TRIGGERS, 
        &flag_result,  
        TYPE_TRUE // for postprocessing 
    ) );  
  }
  else { 
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion all bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion all bck: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[result] = red_precondition_sync_ITERATIVE(
      NULL, // the reachable_return record, 
            // NULL since the initial condition is FALSE.  
      dst, 
      NULL, path,  
      INDEX_FALSE, // the initial states for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION_GAME, 
      SYNC_XTION_COUNT_GAME, 
      &flag_result,  
      TYPE_TRUE // for postprocessing 
    ); 
    RT[result] = red_bop(OR, RT[result], 
      red_precondition_sync_bulk(
        NULL, // the reachable_return record, 
              // NULL since the initial condition is FALSE.  
	dst, 
        NULL, path, // RT[path] is an invariance condition for reachable states
        INDEX_FALSE, // the initial states for reachability 
        RT[result], 
        NORM_FALSE, 
        XI_GAME_SYNC_BULK, // RT[XI_SYNC_BULK] is the bulk representation of the 
                          // sync transitions.  
        XI_GAME_SYNC_BULK_WITH_TRIGGERS, 
        &flag_result, 
        TYPE_TRUE // for postprocessing 
    ) );  
  }
  RT_TOP = RT_TOP - 3; /* result, dst, path  */
  pop_sync_xtion_status(); 
  return(RT[result]); 
}
  /* red_sync_xtion_all_bck() */ 
  
  
  
redgram red_sync_xtion_all_fwd(
	redgram	dsrc, 
	redgram	dpath, 
	int	flag_sync_xtion_table_choice, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry,  
	int	flag_experiment 
) {
  int	src, path, flag, result;  
  
  sync_xtion_marshall(FLAG_MARSHALL_FWD, "red_sync_xtion_all_fwd", 
    dsrc, dpath, flag_sync_xtion_table_choice, 0
  ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[src = RT_TOP++] = dsrc; 
  RT[path = RT_TOP++] = dpath; 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[result] = red_postcondition_sync_ITERATIVE(
      NULL, // no goal check and reachability recording 
      src, // RT[src] describes the source state. 
      path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE, // RT[goal] is the goal for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION, 
      SYNC_XTION_COUNT,   
      TYPE_TRUE, // for postprocessing 
      &flag 
    ); 
    RT[result] = red_bop(OR, RT[result], 
      red_postcondition_sync_bulk(
        NULL, // no goal check and reachability recording 
        src, 
        path, // RT[path] is an invariance condition for reachable states
        INDEX_FALSE, // RT[goal] is the goal for reachability 
        RT[result], 
        NORM_FALSE, 
        XI_SYNC_BULK_WITH_TRIGGERS, // RT[sxi_bulk] is the bulk representation of the 
                          // sync transitions.  
        TYPE_TRUE,  // for postprocessing 
        &flag 
    ) );  
  }
  else { 
    if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nBefore game structuring in sync xtion all fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    
      construct_bisim_structures_for_a_role_spec(); 
      #if RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "\nAfter game structuring in sync xtion all fwd: RT[15]->status=%x\n", 
        RT[15]->status
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
    
    RT[result] = red_postcondition_sync_ITERATIVE(
      NULL, // no goal check and reachability recording 
      src, // RT[src] describes the source state. 
      path, // RT[path] is an invariance condition for reachable states
      INDEX_FALSE, // RT[goal] is the goal for reachability 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION_GAME, 
      SYNC_XTION_COUNT_GAME,    
      TYPE_TRUE, // for postprocessing 
      &flag 
    ); 
    RT[result] = red_bop(OR, RT[result], 
      red_postcondition_sync_bulk(
        NULL, // no goal check and reachability recording 
        src, 
        path, // RT[path] is an invariance condition for reachable states
        INDEX_FALSE, // RT[goal] is the goal for reachability 
        RT[result], 
        NORM_FALSE, 
        XI_GAME_SYNC_BULK_WITH_TRIGGERS, // RT[sxi_bulk] is the bulk representation of the 
                          // sync transitions.  
        TYPE_TRUE, // for postprocessing 
        &flag 
    ) );  
  }
  RT_TOP = RT_TOP - 3; /* result, src, path  */
  pop_sync_xtion_status(); 
  return(RT[result]); 
}
  /* red_sync_xtion_all_fwd() */ 





redgram red_sync_xtion_event_bck(
	redgram	devents, 
	redgram	ddst, 
	redgram	dpath, 
	int	flag_sync_xtion_table_choice, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry,  
	int	flag_experiment 
) { 
  int			events, dst, path, shared_discontinuity, 
			flag_result;  
  struct ps_exp_type	*event_exp; 
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_event_bck", 
    ddst, dpath, flag_sync_xtion_table_choice, 0
  ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 

  if (devents == NULL) {
    RT[events = RT_TOP++] = NORM_NO_RESTRICTION; 
    event_exp = PS_EXP_TRUE; 
  }
  else {
    RT[events = RT_TOP++] = devents; 
    if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
      RT[events] = red_sync_bulk_from_event_diagram( 
        RT[events], XI_SYNC_BULK
      ); 
    }
    else { 
      RT[events] = red_sync_bulk_from_event_diagram( 
        RT[events], XI_GAME_SYNC_BULK
      ); 
    } 
    event_exp = ps_exp_from_string(red_diagram_string(devents)); 
  }
  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect, there should not be time progress. 
*/
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[dst] = red_role_event_precondition(
      event_exp, 
      RT[events], 
      NORM_NO_RESTRICTION, 
      dst, 
      PS_EXP_TRUE, 
      
      path, 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      
      XI_SYNC_BULK, 
      NULL, 
      GSTATUS[INDEX_GAME_ROLES] & MASK_GAME_ROLES, 
      FLAG_OPPONENT_KEEP, 
      GSTATUS[INDEX_APPROX], 
      
      FLAG_POST_PROCESSING 
    );  
  }
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Event preconditions are not supported for games now.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  RT_TOP = RT_TOP - 3; /* events, dst, path */
  pop_sync_xtion_status(); 
  return(RT[dst]); 
}
  /* red_sync_xtion_event_bck() */ 
  
  
  


redgram red_sync_xtion_event_string_bck(
	char	*str_events, 
	redgram	ddst, 
	redgram	dpath, 
	int	flag_sync_xtion_table_choice, 
	int	flag_optional_task, 
	int	flag_game_roles,  
	int	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry,  
	int	flag_experiment 
) { 
  int			events, dst, path, shared_discontinuity, flag_result;  
  struct ps_exp_type	*event_exp; 
  
  sync_xtion_marshall(FLAG_MARSHALL_BCK, "red_sync_xtion_event_string_bck", 
    ddst, dpath, flag_sync_xtion_table_choice, 0
  ); 

  push_sync_xtion_status(
    flag_optional_task, 
    flag_game_roles, flag_time_progress, flag_normality, 
    flag_action_approx, 
    flag_reduction, flag_state_approx, flag_symmetry, 
    flag_experiment 
  ); 
  RT[REACHABLE = RT_TOP++] = NORM_FALSE; 
  if (str_events == NULL || !strcmp(str_events, "true")) { 
    RT[events = RT_TOP++] = NORM_NO_RESTRICTION; 	
    event_exp = PS_EXP_TRUE; 
  } 
  else {
    RT[events = RT_TOP++] = red_diagram_events(str_events); 
    if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
      RT[events] = red_sync_bulk_from_event_diagram(RT[events], 
        XI_SYNC_BULK
      ); 
    } 
    else { 
      RT[events] = red_sync_bulk_from_event_diagram(RT[events], 
        XI_GAME_SYNC_BULK
      ); 
    } 
    event_exp = ps_exp_from_string(str_events); 
  }
  RT[dst = RT_TOP++] = ddst; 
  RT[path = RT_TOP++] = dpath; 
/* This is incorrect, there should not be time progress. 
*/
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    RT[dst] = red_role_event_precondition(
      event_exp, 
      RT[events], 
      NORM_NO_RESTRICTION, 
      dst, 
      PS_EXP_TRUE, 

      path, 
      NORM_FALSE, 
      NORM_FALSE, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 

      XI_SYNC_BULK, 
      NULL, 
      GSTATUS[INDEX_GAME_ROLES] & MASK_GAME_ROLES, 
      FLAG_OPPONENT_KEEP, 
      GSTATUS[INDEX_APPROX], 

      FLAG_POST_PROCESSING 
    );  
  }
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Event preconditions are not supported for games now.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  RT_TOP = RT_TOP - 3; /* events, dst, path */
  pop_sync_xtion_status(); 
  return(RT[dst]); 
}
  /* red_sync_xtion_event_string_bck() */ 
  
  
  


void	push_experiment_flags(int flag_experiment) { 
  push_time_experiment_flags(flag_experiment); 
  
  if (flag_experiment & RED_GFP_EASY_STRONG_FAIRNESS) { 
    GSTATUS[INDEX_GFP] 
    = GSTATUS[INDEX_GFP] | FLAG_IN_GFP_EASY_STRONG_FAIRNESS; 
  } 
  else {
    GSTATUS[INDEX_GFP] 
    = GSTATUS[INDEX_GFP] & ~FLAG_IN_GFP_EASY_STRONG_FAIRNESS; 
  }
  switch (flag_experiment & RED_MASK_LUB_EXTRAPOLATION) {
  case RED_GLUB_EXTRAPOLATION: 
    GSTATUS[INDEX_LUB_EXTRAPOLATION]
    = (GSTATUS[INDEX_LUB_EXTRAPOLATION] & ~MASK_LUB_EXTRAPOLATION) 
    | FLAG_GLUB_EXTRAPOLATION; 
    break; 
  case RED_LUB_EXTRAPOLATION: 
    GSTATUS[INDEX_LUB_EXTRAPOLATION]
    = (GSTATUS[INDEX_LUB_EXTRAPOLATION] & ~MASK_LUB_EXTRAPOLATION) 
    | FLAG_LUB_EXTRAPOLATION; 
    break; 
  } 
/*
  case RED_FAIRNESS_ASSUMPTIONS_EVAL_CONJ: 
    GSTATUS[INDEX_GFP] 
    = (GSTATUS[INDEX_GFP] & ~MASK_FAIRNESS_ASSUMPTIONS_EVAL) 
    | FLAG_FAIRNESS_ASSUMPTIONS_EVAL_CONJ; 
    break; 
  case RED_FAIRNESS_ASSUMPTIONS_EVAL_CONCAT: 
    GSTATUS[INDEX_GFP] 
    = (GSTATUS[INDEX_GFP] & ~MASK_FAIRNESS_ASSUMPTIONS_EVAL) 
    | FLAG_FAIRNESS_ASSUMPTIONS_EVAL_CONCAT; 
    break; 

  case RED_FAIRNESS_ASSUMPTIONS_EVAL_OCC_VAR: 
    GSTATUS[INDEX_GFP] 
    = (GSTATUS[INDEX_GFP] & ~MASK_FAIRNESS_ASSUMPTIONS_EVAL) 
    | FLAG_FAIRNESS_ASSUMPTIONS_EVAL_OCC_VAR; 
    break; 
  } 
*/  
  switch (flag_experiment & RED_MASK_GFP_PATH) { 
  case RED_GFP_PATH_INVARIANCE: 
    GSTATUS[INDEX_GFP] 
    = (GSTATUS[INDEX_GFP] & ~MASK_GFP_PATH) | FLAG_GFP_PATH_INVARIANCE; 
    break; 
  case RED_GFP_PATH_FXP: 
    GSTATUS[INDEX_GFP] 
    = (GSTATUS[INDEX_GFP] & ~MASK_GFP_PATH) | FLAG_GFP_PATH_FXP; 
    break; 
  } 
  
  if (flag_experiment & RED_GFP_ON_THE_FLY) 
    GSTATUS[INDEX_GFP] = GSTATUS[INDEX_GFP] | FLAG_GFP_ON_THE_FLY; 
  else 
    GSTATUS[INDEX_GFP] = GSTATUS[INDEX_GFP] & ~FLAG_GFP_ON_THE_FLY; 
    
  switch (flag_experiment & RED_MASK_SIMULATION_REASONING) {
  case RED_SIMULATION_UNIVERSAL:  
    GSTATUS[INDEX_SIMULATION_REASONING] 
    = (GSTATUS[INDEX_SIMULATION_REASONING] & ~MASK_SIMULATION_REASONING) 
    | FLAG_SIMULATION_UNIVERSAL; 
    break; 
  case RED_SIMULATION_NEG_EXISTENTIAL: 
    GSTATUS[INDEX_SIMULATION_REASONING] 
    = (GSTATUS[INDEX_SIMULATION_REASONING] & ~MASK_SIMULATION_REASONING) 
    | FLAG_SIMULATION_NEG_EXISTENTIAL; 
    break; 
  } 
}
  /* push_experiment_flags() */ 
  
  

void 	push_reachable_utilities(
  int 	flag_task, 
  int	flag_parametric_analysis, 
  int	flag_game_roles, 
  int	flag_full_reachability, 
  int	flag_reachability_depth_bound, 
  
  int	flag_counter_example, 
  int 	flag_time_progress, 
  int	flag_normality, 
  int	flag_action_approx, 
  int	flag_reduction, 
  
  int	flag_state_approx, 
  int	flag_symmetry, 
  int	flag_zeno, 
  int	flag_experiment, 
  int	flag_print 
) { 
  int	gi; 
  
  TOP_STATUS++; 
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    stack_status[TOP_STATUS][gi] = GSTATUS[gi]; 
  } 
  switch (flag_task) { 
  case RED_TASK_SAFETY: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SAFETY; 
    break; 
  case RED_TASK_RISK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_RISK; 
    break; 
  case RED_TASK_GOAL: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
    break; 
  case RED_TASK_ZENO: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_ZENO; 
    break; 
  case RED_TASK_DEADLOCK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_DEADLOCK; 
    break; 
  case RED_TASK_MODEL_CHECK:  
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_MODEL_CHECK; 
    break; 
  case RED_TASK_SIMULATE:  
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_SIMULATE; 
    break; 
  case RED_TASK_BRANCH_SIM_CHECK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_BRANCHING_SIM_CHECKING; 
    break; 
  case RED_TASK_BRANCH_BISIM_CHECK: 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
		        | TASK_BRANCHING_BISIM_CHECKING; 
    break;   
  }

  switch (flag_parametric_analysis) {
  case RED_PARAMETRIC_ANALYSIS: 
    GSTATUS[INDEX_PARAMETRIC_ANALYSIS] = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
  				       | FLAG_PARAMETRIC_ANALYSIS; 
    break; 
  case RED_NO_PARAMETRIC_ANALYSIS: 
    GSTATUS[INDEX_PARAMETRIC_ANALYSIS] = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
  				       & ~FLAG_PARAMETRIC_ANALYSIS; 
    break; 
  }
  
  if (flag_game_roles & RED_GAME_MODL) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_MODL; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_MODL; 

  if (flag_game_roles & RED_GAME_SPEC) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_SPEC; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_SPEC; 

  if (flag_game_roles & RED_GAME_ENVR) 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_ENVR; 
  else 
    GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_ENVR; 

  switch (flag_full_reachability) {
  case RED_FULL_REACHABILITY: 
    GSTATUS[INDEX_FULL_REACHABILITY] 
    = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY; 
    break; 
  case RED_NO_FULL_REACHABILITY: 
    GSTATUS[INDEX_FULL_REACHABILITY] 
    = GSTATUS[INDEX_FULL_REACHABILITY] & ~FLAG_FULL_REACHABILITY; 
    break; 
  } 
  if (   flag_reachability_depth_bound < 0
      || flag_reachability_depth_bound > (0xFFF)
      )  
    GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
    = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND]
    & ~FLAG_REACHABILITY_DEPTH_BOUND; 
  else {
    GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
    = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND]
    | FLAG_REACHABILITY_DEPTH_BOUND; 
    GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
    = (  GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
       & ~MASK_REACHABILITY_DEPTH_BOUND
       ) 
    | flag_reachability_depth_bound; 
  } 

  switch (flag_counter_example) { 
  case RED_COUNTER_EXAMPLE: 
    GSTATUS[INDEX_COUNTER_EXAMPLE] 
    = GSTATUS[INDEX_COUNTER_EXAMPLE]
    | FLAG_COUNTER_EXAMPLE; 
    break; 
  case RED_NO_COUNTER_EXAMPLE: 
    GSTATUS[INDEX_COUNTER_EXAMPLE] 
    = GSTATUS[INDEX_COUNTER_EXAMPLE]
    & ~FLAG_COUNTER_EXAMPLE; 
    break; 
  } 
  
  switch (flag_time_progress) { 
  case RED_TIME_PROGRESS: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS]
    | FLAG_TIME_PROGRESS; 
    break; 
  case RED_NO_TIME_PROGRESS: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS]
    & ~FLAG_TIME_PROGRESS; 
    break; 
  } 

  switch (flag_normality) { 
  case RED_NORM_ZONE_NONE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_NONE; 
    break; 
  case RED_NORM_ZONE_MAGNITUDE_REDUCED: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_MAGNITUDE_REDUCTION; 
    break; 
  case RED_NORM_ZONE_CLOSURE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_CLOSURE; 
    break; 
  case RED_NORM_ZONE_MAGNITUDE_ONE_RIPPLE: 
    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE; 
    break; 
  }
  
  if (flag_normality & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD; 
  if (flag_normality & RED_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD;
  if (flag_normality & RED_NORM_HYBRID_PROOF_OBLIGATIONS) 
    GSTATUS[INDEX_NORM_HYBRID] 
    = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
    | FLAG_NORM_HYBRID_PROOF_OBLIGATIONS;  

  switch (flag_action_approx) { 
  case RED_NO_ACTION_APPROX: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_NO_ACTION_APPROX; 
    break; 
  case RED_ACTION_APPROX_NOXTIVE: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_ACTION_APPROX_NOXTIVE; 
    break;  
  case RED_ACTION_APPROX_UNTIMED: 
    GSTATUS[INDEX_ACTION_APPROX] 
    = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
    | FLAG_ACTION_APPROX_UNTIMED; 
    break; 
  } 
  
  switch (flag_reduction) { 
  case RED_NO_REDUCTION_INACTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_NO_REDUCTION_INACTIVE; 
    break; 
  case RED_REDUCTION_INACTIVE_NOXTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
    break; 
  case RED_REDUCTION_INACTIVE: 
    GSTATUS[INDEX_REDUCTION_INACTIVE] 
    = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
    | FLAG_REDUCTION_INACTIVE; 
    break; 
  } 
  
  switch (flag_state_approx & RED_MASK_APPROX) { 
  case RED_NOAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_NOAPPROX; 
    break; 
  case RED_UAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_UAPPROX; 
    break; 
  case RED_OAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_OAPPROX; 
    switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) { 
    case RED_OAPPROX_STRATEGY_GAME: 
      GSTATUS[INDEX_APPROX] 
      = GSTATUS[INDEX_APPROX] 
      | FLAG_OAPPROX_STRATEGY_GAME; 
      switch (flag_state_approx & MASK_OAPPROX_SPEC_GAME) { 
      case RED_NOAPPROX_SPEC_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_SPEC_GAME; 
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAG_MAG;
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAGONAL: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_SPEC_GAME_UNTIMED: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_UNTIMED; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MODE_ONLY: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MODE_ONLY;
        break;  
      case RED_OAPPROX_SPEC_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_NONE;
        break;  
      }     
    
      switch (flag_state_approx & MASK_OAPPROX_MODL_GAME) { 
      case RED_NOAPPROX_MODL_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_MODL_GAME; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_MODL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_MODL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_MODL_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_MODL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_ENVR_GAME) {
      case RED_NOAPPROX_ENVR_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_ENVR_GAME;
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_ENVR_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_ENVR_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_ENVR_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_ENVR_GAME_NONE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_GLOBAL_GAME) {
      case RED_NOAPPROX_GLOBAL_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_GLOBAL_GAME; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_NONE;
        break;  
      }
      break; 
    } // switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) 
    break; 
  } //  switch (flag_state_approx & RED_MASK_APPROX) { 
  
  switch (flag_symmetry) { 
  case RED_NO_SYMMETRY: 
    GSTATUS[INDEX_SYMMETRY] = GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY; 
    break; 
    
  case RED_SYMMETRY_ZONE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_ZONE; 
    break; 
  case RED_SYMMETRY_DISCRETE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_DISCRETE_GENERAL;  
    break; 
  case RED_SYMMETRY_POINTER: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE; 
    break; 
  case RED_SYMMETRY_STATE: 
    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
      | FLAG_SYMMETRY_STATE; 
    break; 
  } 

  switch (flag_zeno & RED_MASK_ZENO) { 
  case RED_PLAIN_NONZENO: 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_USE_PLAIN_NONZENO; 
    DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
    break; 
  case RED_APPROX_NONZENO: 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_USE_APPROX_NONZENO; 
    DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
    break; 
  case RED_ZENO_TRACES_OK:  
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    DISTANCE_ZENO = 0; 
    break; 
  }
  
  push_experiment_flags(flag_experiment); 
  
  // We ahve not figured out how to support coverage analysis. 
  GSTATUS[INDEX_PRINT] = (GSTATUS[INDEX_PRINT] & ~MASK_PRINT) 
		       | (MASK_PRINT & flag_print); 
}
  /* push_reachable_utilities() */ 
  
  
  
void	pop_reachable_utilities() { 
  int	gi; 
  
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    GSTATUS[gi] = stack_status[TOP_STATUS][gi]; 
  } 
  switch (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) { 
  case FLAG_USE_PLAIN_NONZENO: 
  case FLAG_USE_APPROX_NONZENO: 
    DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
    break; 
  case FLAG_ZENO_CYCLE_OK:  
    DISTANCE_ZENO = 0; 
    break; 
  }
  TOP_STATUS--; 
}
  /* pop_reachable_utilities() */ 
  
  
  
// QQQ? 2007/10/08:2304
struct reachable_return_type 
  *red_reach_bck( 
	redgram	dinit, // redgram for the initial condition. 
	redgram	dpath, // redgram for the path condition. 
	redgram	dgoal, // redgram for the goal condition 
	int 	flag_task, 
	int	flag_parametric_analysis, 

	int	flag_game_roles, 
	int	flag_full_reachability, 
	int	flag_reachability_depth_bound, 
	int	flag_counter_example, 
	int 	flag_time_progress, 

	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 

	int	flag_experiment, 
	int	flag_print 
  ) { 
  int				init, local_path, pi, goal, i, j, 
  				local_flag_time_progress; 
  struct reachable_return_type	*result; 

  push_reachable_utilities(
    flag_task, 
    flag_parametric_analysis, 
    flag_game_roles, 
    flag_full_reachability, 
    flag_reachability_depth_bound, 
    
    flag_counter_example, 
    flag_time_progress, 
    flag_normality, 
    flag_action_approx, 
    flag_reduction, 
    
    flag_state_approx, 
    flag_symmetry, 
    RED_ZENO_TRACES_OK, 
    flag_experiment, 
    flag_print 
  ) ; 

  local_flag_time_progress = GSTATUS[INDEX_TIME_PROGRESS]; 
  if (   (GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
      && (   dpath == NORM_TRUE
          || dpath == RT[DECLARED_GLOBAL_INVARIANCE]
          || dpath == RT[REFINED_GLOBAL_INVARIANCE] 
      )   ) 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS)
    | FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 

  RT[init = RT_TOP++] = dinit; 
  RT[local_path = RT_TOP++] = dpath; 

  RT[goal = RT_TOP++] = red_delayed_eval(dgoal, PROC_GLOBAL, dpath); 
/*
  fprintf(RED_OUT, "\nred_reach_bck(RT[goal=%1d]):\n", goal); 
  red_print_graph(RT[goal]); 
*/  
  mark_working_in_red(RT[goal], FLAG_SPEC_REFERENCED, &i, &j); 

  result = red_reachable_bck(
    init, 
    local_path, 
    goal, 
    SYNC_XTION, SYNC_XTION_COUNT, 
    XI_SYNC_BULK, 
    XI_SYNC_BULK_WITH_TRIGGERS
  ); 
  RT_TOP--; // goal 
  RT_TOP = RT_TOP-2; // init, local_path
  GSTATUS[INDEX_TIME_PROGRESS] = local_flag_time_progress; 

  pop_reachable_utilities(); 
  
//  print_acc_time(FLAG_ACC_HASH_TIME);
  return (result); 
}
  /* red_reach_bck() */ 
  
  
  
struct reachable_return_type 
  *red_reach_fwd(	
	redgram  dinit, // redgram for the initial condition. 
	redgram  dpath, // redgram for the path condition. 
	redgram  dgoal, // redgram for the goal condition 
	int 	flag_task, 
	int	flag_parametric_analysis, 
	int	flag_game_roles, 
	int	flag_full_reachability, 
	int	flag_reachability_depth_bound, 
	int	flag_counter_example, 
	int 	flag_time_progress, 
	int	flag_normality, 
	int	flag_action_approx, 
	int	flag_reduction, 
	int	flag_state_approx, 
	int	flag_symmetry, 
	int	flag_experiment, 
	int	flag_print 
	) {
  int				init, path, shared_discontinuity, goal, i, j; 
  struct reachable_return_type	*result; 

  push_reachable_utilities(
    flag_task, 
    flag_parametric_analysis, 
    flag_game_roles, 
    flag_full_reachability, 
    flag_reachability_depth_bound, 
    
    flag_counter_example, 
    flag_time_progress, 
    flag_normality, 
    flag_action_approx, 
    flag_reduction, 
    
    flag_state_approx, 
    flag_symmetry, 
    RED_ZENO_TRACES_OK, 
    flag_experiment, 
    flag_print 
  ) ; 


  RT[init = RT_TOP++] = red_delayed_eval(dinit, PROC_GLOBAL, dpath); 
  RT[path = RT_TOP++] = dpath; 
//  RT[shared_discontinuity = RT_TOP++] = red_shared_concavity(path); 
  RT[goal = RT_TOP++] = dgoal; 
  mark_working_in_red(RT[goal], FLAG_SPEC_REFERENCED, &i, &j); 
  result = red_reachable_fwd( 
	init, // the initial state of the reachability 
	path, // the invariance condition of the reachability 
//	shared_discontinuity, 
	goal, // the goal state of the reachability, 
	SYNC_XTION, 
	SYNC_XTION_COUNT, 
	XI_SYNC_BULK_WITH_TRIGGERS
  ); 
  RT_TOP = RT_TOP-3; // init, path, /*shared_discontinuity,*/ goal 
  pop_reachable_utilities(); 

//  print_acc_time(FLAG_ACC_HASH_TIME);
  return (result); 
}
  /* red_reach_fwd() */ 
  


  
  
  
void	red_print_reachable_return(struct reachable_return_type	*rr) {
  print_reachable_return(rr); 
} 
  /* red_print_reachable_return() */ 





struct ps_exp_type	*redlib_parse_spec(char	*f) { 
  int			i; 
  FILE			*tctlf; 
  struct ps_exp_type	*result; 

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = f; 
  redlib_input_string_len = strlen(f) + 2; /* 2 for two NULLs */ 

/*  
  fprintf(RED_OUT, "Read in a new formula.\n"); 
  fflush(RED_OUT); 
*/  
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_TCTL) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", f); 
    fprintf(RED_OUT, "       when a TCTL formula is expected in red_model_check().\n"); 
    exit(0); 
  }
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\nredlib_parse_spec: after parsing spec for PC=%1d\n", PROCESS_COUNT); 
  print_parse_subformula_structure(PARSER_INPUT_FORMULA, 0); 
  fflush(RED_OUT); 
  #endif 

  if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
      == FLAG_MODEL_PARSING_ONLY
      ) {
    return(PARSER_INPUT_FORMULA); 	
  } 

  SPEC_EXP = analyze_tctl(PARSER_INPUT_FORMULA, 0, TYPE_TRUE);
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\n*********************************\nredlib_parse_spec: The negated parse spec after spec_global().\n");
  pcform(SPEC_EXP);
  print_tctctl_flag(SPEC_EXP); 
  fprintf(RED_OUT, "\nIn structured form:\n"); 
  print_parse_subformula_structure(SPEC_EXP, 0);
  fflush(RED_OUT); 
  #endif 
  
// disabled temporarily  change_event_counts_to_xi_sync_all(SPEC_EXP); 
/*
  fprintf(RED_OUT, "after changing event counts of the tctl spec.\n"); 
  pcform(SPEC_EXP); 
*/
  ps_exp_mark(SPEC_EXP, FLAG_GC_STABLE);
  
  return(SPEC_EXP); 
} 
  /* redlib_parse_spec() */  






  
struct model_check_return_type	*red_model_check(
  redgram	dinit, 
  redgram 	dpath, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int 		flag_zeno, // some experiment options are stored here. 
  int		flag_experiment, 
  int		flag_print, 
  char		*f, ... 
) { 
  struct ps_exp_type			*nspec; 
  char					*real_f; 
  struct model_check_return_type	*mr; 
  int					orig_task, 
  					w, flag_root_polarity, init, path, 
  					local_path, 
  					local_convex_start, 
  					local_convex_stop, 
					orig_zeno_status, 
					tmp_flag_utilities, 
					tmp_flag_approx, 
					tmp_flag_print, tmp_flag_roles, 
					tmp_flag_time, tmp_type_task, 
					tmp_flag_parametric_analysis, 
					tmp_flag_time_progress_options, 
					tmp_flag_time_progress_analysis, 
					tmp_flag_time_tconvexity_shared_partitions;  
  va_list				args; 

  orig_task = GSTATUS[INDEX_TASK]; 
  GSTATUS[INDEX_TASK] 
  = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
  | TASK_MODEL_CHECK; 
  GSTATUS[INDEX_FAIRNESS] 
  = GSTATUS[INDEX_FAIRNESS] & ~FLAG_FAIRNESS_ASSUMPTIONS; 
  
  string_var(real_f, "tctl ", ";", f, args); 

  /* In the following procedure, we complement the specification formula. 
   */ 
  nspec = redlib_parse_spec(real_f); 
  clear_while_gfp(); 

  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "\n**************************\nParsed TCTL formula in red_model_check():\n"); 
  print_tctctl_flag(nspec); 
  pcform(nspec); 
  #endif 
  
  // first save the original flags.  
  push_reachable_utilities(
    TASK_MODEL_CHECK, 
    RED_NO_PARAMETRIC_ANALYSIS, 
    RED_GAME_ROLES, 
    RED_FULL_REACHABILITY, 
    -1, 
    
    RED_NO_COUNTER_EXAMPLE, 
    RED_TIME_PROGRESS, 
    flag_normality, 
    flag_action_approx, 
    flag_reduction, 
    
    flag_state_approx, 
    RED_NO_SYMMETRY, 
    flag_zeno, 
    flag_experiment, 
    flag_print 
  ) ; 

  mark_working(nspec, FLAG_SPEC_REFERENCED, 
    &local_convex_start, &local_convex_stop
  ); 

  RT[init = RT_TOP++] = dinit; 
  RT[path = RT_TOP++] = red_bop(AND, dpath, RT[DECLARED_GLOBAL_INVARIANCE]); 
  if (flag_state_approx == 0) {
    flag_root_polarity = FLAG_ROOT_NOAPPROX; 
  } 
  else { 
    switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) {
    case RED_OAPPROX_STRATEGY_GAME: 
      GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_APPROX)
      			    | FLAG_ROOT_OAPPROX 
      			    | (MASK_OAPPROX & flag_state_approx);  
      break; 
    } 
    flag_root_polarity =  (GSTATUS[INDEX_APPROX] & ~MASK_APPROX) 
		       | FLAG_ROOT_NOAPPROX 
		       | (flag_state_approx & MASK_OAPPROX); 
  } 
  switch (flag_zeno & RED_MASK_ZENO) { 
  case RED_PLAIN_NONZENO: 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_USE_PLAIN_NONZENO; 
    break; 
  case RED_APPROX_NONZENO: 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_USE_APPROX_NONZENO; 
    break; 
  case RED_ZENO_TRACES_OK:  
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    break; 
  }

  tmp_flag_time_progress_analysis
  = GSTATUS[INDEX_TIME_PROGRESS]; 
  switch (flag_experiment & RED_MASK_TIME_PROGRESS_ANALYSIS) { 
  case RED_TIME_PROGRESS_ANALYSIS_NONE: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_NONE; 
    break; 
  case RED_TIME_PROGRESS_ANALYSIS_TCTCTL: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL; 
    break; 
  case RED_TIME_PROGRESS_ANALYSIS_ADVANCED:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_ANALYSIS) 
    | FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED; 
    break; 
  } 

  tmp_flag_time_tconvexity_shared_partitions
  = GSTATUS[INDEX_TIME_PROGRESS]; 
  if (flag_experiment & RED_TIME_TCONVEXITY_SHARED_PARTITIONS)
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS] | FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS; 
  else 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS] & ~FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS; 
  
  tmp_flag_time_progress_options = GSTATUS[INDEX_TIME_PROGRESS]; 
  switch (flag_experiment & RED_MASK_TIME_PROGRESS_OPTIONS) { 
  case RED_TIME_PROGRESS_ASSUMED_CONVEXITY:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
    break; 

  case RED_TIME_PROGRESS_SPLIT_CONVEXITIES:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 	
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 	
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES; 
    break; 
  case RED_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 	
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES; 
    break; 

  case RED_TIME_PROGRESS_FULL_FORMULATION:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_FULL_FORMULATION; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_SHARED_CONCAVITY: 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_CONCAVITY; 
    break; 

  case RED_TIME_PROGRESS_EASY_CONCAVITY:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_EASY_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_SHARED_EASY_CONCAVITY:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY; 
    break; 
  case RED_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY:  
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
    | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY; 
    break; 
  } 
  
  mr = red_model_chk(init, path, nspec); 
  
  pop_reachable_utilities(); 
  
  GSTATUS[INDEX_TIME_PROGRESS] = tmp_flag_time_progress_options; 
  GSTATUS[INDEX_TIME_PROGRESS] = tmp_flag_time_tconvexity_shared_partitions;  
  GSTATUS[INDEX_TIME_PROGRESS] = tmp_flag_time_progress_analysis; 
  
  #if RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "After the labeling algorithm, result = %x\n", 
    mr->failed_state_diagram
  ); 
  red_print_graph(mr->failed_state_diagram); 
  #endif  

  RT_TOP = RT_TOP-2; // init, path  
  

  GSTATUS[INDEX_TASK] = orig_task; 

  #if RED_DEBUG_LIB_MODE
  if (mr->status & FLAG_MODEL_CHECK_SATISFIED) { 
    fprintf(RED_OUT, 
      "\nThe following specification in TCTL is satisfied:\n%s\n", 
      real_f
    ); 
  } 
  else { 
    fprintf(RED_OUT, 
      "\nThe following specification in TCTL is violated:\n%s\n", 
      real_f
    ); 	
  }
  #endif 

//  print_acc_time(FLAG_ACC_HASH_TIME);
  return (mr); 
} 
  /* red_model_check() */ 
  
  


void	parse_roles(role_spec) 
	char	*role_spec; 
{ 
  int	i, tmp_flag; 

  flag_redlib_input_source = FLAG_INPUT_STRING; 
  redlibin = NULL; 
  redlib_input_string = role_spec; 
  redlib_input_string_len = strlen(role_spec) + 2; /* 2 for two NULLs */ 
  redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_GAME_ROLES) { 
    fprintf(RED_OUT, "Error: Unmatched parsing result for `%s' \n", role_spec); 
    fprintf(RED_OUT, "       when a role spec. is expected in red_diagram().\n"); 
    exit(0); 
  } 
  
  REDLIB_ROLE_STRING = role_spec; 
  parse_mode_xtion_system_spec(); 
  GSTATUS[INDEX_GAME_ROLES] 
  = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_ROLES_CHANGED; 
} 
  /* parse_roles() */ 
  
  
  

void	red_input_roles(char *role_spec, ...) {
  char		*real_f; 
  va_list	args; 

  string_var(real_f, "role ", "", role_spec, args); 

  parse_roles(real_f); 
}
  /* red_input_roles() */  
  




char	*red_query_role_string() { 
  return(REDLIB_ROLE_STRING); 
}
  /* red_query_role_string() */ 
  

int	red_query_process_game_role(int pi) { 
  switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
  case FLAG_GAME_SPEC: 
    return(RED_GAME_SPEC); 
    break; 
  case FLAG_GAME_MODL: 
    return(RED_GAME_MODL); 
    break; 
  case FLAG_GAME_ENVR: 
    return(RED_GAME_ENVR); 
    break; 
  } 
}
  /* red_query_process_game_role() */  
  
  
  
void	red_print_sim_check_return(
  struct sim_check_return_type	*sr
) {
  print_sim_check_return(sr); 	
}
  /* red_print_sim_check_return() */ 
  
  

  
struct sim_check_return_type	*red_sim_check(
	redgram  dinit, 
	redgram  dinvariance, 
	int	 flag_complete_greatest_fixpoint, 
	int	 flag_fixpoint_iteration_bound, 
	int	 flag_counter_example, 
	int 	 flag_time_progress, 
	int	 flag_normality, 
	int	 flag_action_approx, 
	int	 flag_reduction, 
	int	 flag_state_approx, 
	int	 flag_symmetry, 
	int	 flag_zeno, 
	int	 flag_experiment, 
	int	 flag_print,  
	char	 *role_spec, ...
	) {
  char				*real_f; 
  int				init, inv; 
  struct sim_check_return_type	*sr; 
  va_list			args; 

  string_var(real_f, "role ", "", role_spec, args); 

  GSTATUS[INDEX_TASK] 
  = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
  | TASK_BRANCHING_SIM_CHECKING; 
  GSTATUS[INDEX_FAIRNESS] 
  = GSTATUS[INDEX_FAIRNESS] & ~FLAG_FAIRNESS_ASSUMPTIONS; 
  parse_roles(real_f); 
  if (GSTATUS[INDEX_FAIRNESS] & FLAG_FAIRNESS_ASSUMPTIONS) { 
    if (   GAME_ENVR_EXP->u.mexp.weak_fairness_count == 0
        && GAME_ENVR_EXP->u.mexp.strong_fairness_count == 0 
        && GAME_MODL_EXP->u.mexp.weak_fairness_count == 0
        && GAME_MODL_EXP->u.mexp.strong_fairness_count == 0 
        && GAME_SPEC_EXP->u.mexp.weak_fairness_count == 0
        && GAME_SPEC_EXP->u.mexp.strong_fairness_count == 0 
        ) {
      GSTATUS[INDEX_FAIRNESS] 
      = GSTATUS[INDEX_FAIRNESS] & ~FLAG_FAIRNESS_ASSUMPTIONS; 
      sr = (struct sim_check_return_type *) 
        malloc(sizeof(struct sim_check_return_type)); 
      sr->status = FLAG_BISIM_USE_PLAIN_NONZENO; 
      sr->iteration_count = 0; 
      sr->initial_state_pair_diagram = dinit; 
      sr->counter_example_tree = NULL;  
      commit_branching_sim_result(FLAG_A_BRANCHING_SIM_EXISTS, 0, 
        dinvariance, sr
      ); 
      return (sr); 
  } } 

  push_reachable_utilities(
    TASK_MODEL_CHECK, 
    RED_NO_PARAMETRIC_ANALYSIS, 
    RED_GAME_ROLES, 
    flag_complete_greatest_fixpoint, 
    flag_fixpoint_iteration_bound, 
    
    flag_counter_example, 
    RED_TIME_PROGRESS, 
    RED_NORM_ZONE_CLOSURE, 
    flag_action_approx, 
    flag_reduction, 
    
    flag_state_approx, 
    RED_NO_SYMMETRY, 
    flag_zeno, 
    flag_experiment, 
    flag_print 
  ) ; 

  clear_working(FLAG_SPEC_REFERENCED); 

  RT[init = RT_TOP++] = dinit; 
  RT[inv = RT_TOP++] = dinvariance; 
//  sr = red_simulation_check(init, sim); 
  sr = red_fair_sim_check(RT[init], RT[inv], 
    TYPE_FALSE // Not bisimulation checking 
  ); 
  RT_TOP = RT_TOP-2; /* init, inv */ 
  pop_reachable_utilities() ; 

  return(sr); 
}
  /* red_sim_check() */ 
  
  
  
  
struct sim_check_return_type	*red_bisim_check(
	redgram  dinit, 
	redgram  dinit_sim, 
	int	 flag_complete_greatest_fixpoint, 
	int	 flag_fixpoint_iteration_bound, 
	int	 flag_counter_example, 
	int 	 flag_time_progress, 
	int	 flag_normality, 
	int	 flag_action_approx, 
	int	 flag_reduction, 
	int	 flag_state_approx, 
	int	 flag_symmetry, 
	int	 flag_zeno, 
	int	 flag_experiment, 
	int	 flag_print,  
	char	 *role_spec, ... 
	) {
  char				*real_f; 
  int				init, sim; 
  struct sim_check_return_type	*br; 
  va_list			args; 

  string_var(real_f, "role ", "", role_spec, args); 

  GSTATUS[INDEX_TASK] 
  = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
  | TASK_BRANCHING_BISIM_CHECKING; 
  GSTATUS[INDEX_FAIRNESS] 
  = GSTATUS[INDEX_FAIRNESS] & ~FLAG_FAIRNESS_ASSUMPTIONS; 
  parse_roles(real_f); 
  if (GSTATUS[INDEX_FAIRNESS] & FLAG_FAIRNESS_ASSUMPTIONS) { 
    if (   GAME_ENVR_EXP->u.mexp.weak_fairness_count == 0
        && GAME_ENVR_EXP->u.mexp.strong_fairness_count == 0 
        && GAME_SPEC_EXP->u.mexp.weak_fairness_count == 0
        && GAME_SPEC_EXP->u.mexp.strong_fairness_count == 0 
        && GAME_MODL_EXP->u.mexp.weak_fairness_count == 0
        && GAME_MODL_EXP->u.mexp.strong_fairness_count == 0 
        ) {
      br = (struct sim_check_return_type *) 
        malloc(sizeof(struct sim_check_return_type)); 
      br->status = FLAG_BISIM_USE_PLAIN_NONZENO; 
      br->iteration_count = 0; 
      br->initial_state_pair_diagram = dinit; 
      br->counter_example_tree = NULL;  
      commit_branching_sim_result(FLAG_A_BRANCHING_BISIM_EXISTS, 0, 
        dinit_sim, br
      ); 
      return (br); 
  } } 

  push_reachable_utilities(
    TASK_MODEL_CHECK, 
    RED_NO_PARAMETRIC_ANALYSIS, 
    RED_GAME_ROLES, 
    flag_complete_greatest_fixpoint, 
    flag_fixpoint_iteration_bound, 
    
    flag_counter_example, 
    RED_TIME_PROGRESS, 
    RED_NORM_ZONE_CLOSURE, 
    flag_action_approx, 
    flag_reduction, 
    
    flag_state_approx, 
    RED_NO_SYMMETRY, 
    flag_zeno, 
    flag_experiment, 
    flag_print 
  ) ; 

  clear_working(FLAG_SPEC_REFERENCED); 
  
  RT[init = RT_TOP++] = dinit; 
  RT[sim = RT_TOP++] = dinit_sim; 
  br = red_fair_sim_check(RT[init], RT[sim], 
    TYPE_TRUE // Bisimulation checking 
  ); 
//   br = red_bisimulation_check(init, sim); 
  RT_TOP = RT_TOP-2; /* init, sim */ 
  
  pop_reachable_utilities() ; 

  return(br); 
}
  /* red_bisim_check() */ 



redgram	red_query_diagram_enhanced_global_invariance() { 
  return(RT[REFINED_GLOBAL_INVARIANCE]); 
} 
  /* red_query_diagram_enhanced_global_invariance() */ 



redgram	red_query_diagram_global_invariance() { 
  return(RT[DECLARED_GLOBAL_INVARIANCE]); 
} 
  /* red_query_diagram_global_invariance() */ 



redgram	red_query_diagram_goal() { 
  return(RT[INDEX_GOAL]); 
} 
  /* red_query_diagram_goal() */ 



redgram	red_query_diagram_deadlock() { 
  int		pi, sxi; 
  redgram	conj; 

  if (RT[INDEX_DEADLOCK] != NULL) 
    return(RT[INDEX_DEADLOCK]); 
    
  RT[INDEX_DEADLOCK] = red_all_trigger(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    if (SYNC_XTION[sxi].party_count <= 0) 
      continue; 
    RT[INDEX_DEADLOCK] = red_bop(OR, RT[INDEX_DEADLOCK], 
      SYNC_XTION[sxi].red_trigger
    ); 
  }
  RT[INDEX_DEADLOCK] = red_bop(AND, RT[REFINED_GLOBAL_INVARIANCE], RT[INDEX_DEADLOCK]);
  RT[INDEX_DEADLOCK] = red_complement(RT[INDEX_DEADLOCK]);
  RT[INDEX_DEADLOCK] = red_bop(AND, RT[REFINED_GLOBAL_INVARIANCE], RT[INDEX_DEADLOCK]);
  RT[INDEX_DEADLOCK] = red_hull_normalize(INDEX_DEADLOCK);
  if (RT[INDEX_DEADLOCK] != NORM_FALSE) {
    fprintf(RED_OUT, "\nA possible deadlock state space is detected:\n");
    red_print_graph(RT[INDEX_DEADLOCK]);
  }
  return(RT[INDEX_DEADLOCK]); 
} 
  /* red_query_diagram_deadlock() */ 
  
  


  

redgram	red_query_diagram_zeno() {
  int		pi, xi; 
  redgram	conj; 

  if (RT[INDEX_ZENO] != NULL) 
    return(RT[INDEX_ZENO]); 
    
  
}
  /* red_query_diagram_zeno() */ 
  
  
  

void 	push_abstract_options(
  int	flag_state_approx 
) { 
  int	gi; 
  
  TOP_STATUS++; 
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    stack_status[TOP_STATUS][gi] = GSTATUS[gi]; 
  } 

  switch (flag_state_approx & RED_MASK_APPROX) { 
  case RED_NOAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_NOAPPROX; 
    break; 
  case RED_UAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_UAPPROX; 
    break; 
  case RED_OAPPROX: 
    GSTATUS[INDEX_APPROX] = FLAG_ROOT_OAPPROX; 
    switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) { 
    case RED_OAPPROX_STRATEGY_GAME: 
      GSTATUS[INDEX_APPROX] 
      = GSTATUS[INDEX_APPROX] 
      | FLAG_OAPPROX_STRATEGY_GAME; 
      switch (flag_state_approx & MASK_OAPPROX_SPEC_GAME) { 
      case RED_NOAPPROX_SPEC_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_SPEC_GAME; 
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAG_MAG;
        break;  
      case RED_OAPPROX_SPEC_GAME_DIAGONAL: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_SPEC_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_SPEC_GAME_UNTIMED: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_UNTIMED; 
        break;  
      case RED_OAPPROX_SPEC_GAME_MODE_ONLY: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_MODE_ONLY;
        break;  
      case RED_OAPPROX_SPEC_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_SPEC_GAME_NONE;
        break;  
      }     
    
      switch (flag_state_approx & MASK_OAPPROX_MODL_GAME) { 
      case RED_NOAPPROX_MODL_GAME: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_MODL_GAME; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_MODL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_MODL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_MODL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_MODL_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_MODL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_MODL_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_ENVR_GAME) {
      case RED_NOAPPROX_ENVR_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_NOAPPROX_ENVR_GAME;
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_ENVR_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_DIAGONAL; 
        break;  
      case RED_OAPPROX_ENVR_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MAGNITUDE;
        break;  
      case RED_OAPPROX_ENVR_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_ENVR_GAME_MODE_ONLY:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_MODE_ONLY; 
        break;  
      case RED_OAPPROX_ENVR_GAME_NONE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
	| FLAG_OAPPROX_ENVR_GAME_NONE;
        break;  
      }

      switch (flag_state_approx & MASK_OAPPROX_GLOBAL_GAME) {
      case RED_NOAPPROX_GLOBAL_GAME:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_NOAPPROX_GLOBAL_GAME; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAG_MAG:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_DIAGONAL:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_MAGNITUDE:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE; 
        break;  
      case RED_OAPPROX_GLOBAL_GAME_UNTIMED:
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_UNTIMED;
        break;  
      case RED_OAPPROX_GLOBAL_GAME_NONE: 
        GSTATUS[INDEX_APPROX] = GSTATUS[INDEX_APPROX] 
        | FLAG_OAPPROX_GLOBAL_GAME_NONE;
        break;  
      }
      break; 
    } // switch (flag_state_approx & RED_MASK_OAPPROX_STRATEGY) 
    break; 
  } //  switch (flag_state_approx & RED_MASK_APPROX) { 
}
  /* push_abstract_options() */ 
  
  
  
void	pop_abstract_options() { 
  int	gi; 
  
  for (gi = 0; gi < GSTATUS_SIZE; gi++) { 
    GSTATUS[gi] = stack_status[TOP_STATUS][gi]; 
  } 
  TOP_STATUS--; 
}
  /* pop_abstract_options() */ 
  
  
  
redgram red_abstract(
  redgram	d, 
  int		flag_oapprox, 
  char		*role_spec, 
  ... 
) { 
  int		*pstatus, pi; 
  char		*real_f; 
  va_list	args; 

  pstatus = (int *) malloc((PROCESS_COUNT+1)*sizeof(int)); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    pstatus[pi] = PROCESS[pi].status; 	
  } 
  string_var(real_f, "role ", "", role_spec, args); 
  parse_roles(real_f); 

  fprintf(RED_OUT, "\nRoles: "); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    fprintf(RED_OUT, "%1d:%1d; ", pi, red_query_process_role(pi)); 	
  } 
  fprintf(RED_OUT, "\n\n"); 
  
  push_abstract_options(flag_oapprox); 
  d = rec_abs_game(d); 
  pop_abstract_options(); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    PROCESS[pi].status = pstatus[pi]; 	
  } 
  free(pstatus); 
  return(d); 
}
  /* red_abstract() */ 
  
  
  
redgram red_reduce_symmetry(
	redgram	d, 
	int	flag_symmetry
	) 
{ 
  int	tmp_flag_symmetry, w; 
  
  tmp_flag_symmetry = GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY; 
  GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY) 
			  | (flag_symmetry & MASK_SYMMETRY);  
  RT[w = RT_TOP++] = d; 
  reduce_symmetry(w); 
  RT_TOP--; // w
  GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY) 
			  | tmp_flag_symmetry;  
  return(RT[w]); 
} 
  /* red_reduce_symmetry() */  
  
  
  
redgram red_reduce_inactive(
	redgram	d
	) { 
  int	w; 
  
  RT[w = RT_TOP++] = d; 
  RT[w] = inactive_variable_eliminate(w);
  RT_TOP--; // w 
  
  return(RT[w]); 
} 
  /* red_reduce_inactive() */  
  
  
  
  
int 	red_garbage_collect() {
  garbage_collect(FLAG_GC_SILENT); 
}
  /* red_garbage_collect() */ 
  
  
  
#if RED_DEBUG_LIB_MODE
int	count_user_stack_push = 0; 
#endif 

int 	red_push(
	redgram	d
	) {
  int	result; 

  #if RED_DEBUG_LIB_MODE
  ++count_user_stack_push;
  fprintf(RED_OUT, "\ncount_user_stack_push = %1d at USER_TOP=%1d/%1d\n", 
    count_user_stack_push, USER_TOP, USER_LIMIT
  );  
  #endif 
  if (USER_TOP >= USER_LIMIT) { 
    struct red_type	**ns; 
    int			i; 
    
    if (USER_TOP > USER_LIMIT) { 
      fprintf(RED_OUT, 
        "\nError: Some increment operation to the user stack pointer\n"
      ); 
      fprintf(RED_OUT, 
        "       is not done through red_push().\n"
      );  
      fflush(RED_OUT); 
      bk(0); 
    } 
    ns = (struct red_type **) malloc(2*USER_LIMIT*sizeof(struct red_type *)); 
    for (i = 0; i < USER_LIMIT; i++) 
      ns[i] = RED_USER_STACK[i]; 
    free(RED_USER_STACK); 
    RED_USER_STACK = ns; 
    USER_LIMIT = 2*USER_LIMIT; 
    for (; i < USER_LIMIT; i++) 
      RED_USER_STACK[i] = NULL; 
  } 

  RED_USER_STACK[result = USER_TOP++] = d; 
  return(result); 
}
  /* red_push() */  
  
  
  
redgram red_pop(
	int	i
	) {
  if (i >= 0 && i == USER_TOP - 1) { 
    USER_TOP--; 
    return(RED_USER_STACK[i]); 
  } 
  else 
    return(NULL); 		
}
  /* red_pop() */  
  
  
  
redgram red_stack(
	int	i
	) {
  if (i >= 0 && i < USER_TOP) { 
    return(RED_USER_STACK[i]); 
  } 
  else 
    return(NULL); 		
}
  /* red_stack() */  
  


void 	red_set_stack(
	int	i, 
	redgram	d
	) {
  if (i >= 0 && i < USER_TOP) { 
    RED_USER_STACK[i] = d; 
  } 
}
  /* red_set_stack() */  
  
  
void	red_protect_from_gc(redgram d) { 
  red_mark(d, FLAG_GC_USER_STATIC1); 
}
  /* red_protect_from_gc() */ 

void	red_unprotect_all_from_gc() { 
  red_unmark_all(FLAG_GC_USER_STATIC1); 
}
  /* red_unprotect_all_from_gc() */ 

void	red_protect_aux_from_gc(redgram d) { 
  red_mark(d, FLAG_GC_USER_STATIC2); 
}
  /* red_protect_aux_from_gc() */ 

void	red_unprotect_all_aux_from_gc() { 
  red_unmark_all(FLAG_GC_USER_STATIC2); 
}
  /* red_unprotect_all_aux_from_gc() */ 

  
/* The following three procedures are for token-based protection 
 * from garbage-collection. 
 */ 
int	red_get_a_protection_token() { 
  return(get_a_new_gc_token(&USER_TOKEN_PROTECTION_LIST)); 
}
  /* red_get_a_protection_token() */  
  
  
void	red_protect_with_token(d, t) 
  redgram	d; 
  int		t; 
{ 
  protect_from_gc_with_token(d, t, USER_TOKEN_PROTECTION_LIST); 
}
  /* red_protect_with_token() */ 



void	red_release_token(t) 
  int	t; 
{
  release_gc_token(t, &USER_TOKEN_PROTECTION_LIST); 
}
  /* red_release_token() */ 
  
  
void    red_print_variables() {   
  print_variables(); 
}
  /* red_print_variables() */ 
  
  
  
void    red_print_variable(int vi) 
{ 
  print_variable(vi); 
}
  /* red_print_variable() */  



void	red_print_inline_declarations() { 
  int			i; 
  struct ps_bunit_type	*bu; 
  
  fprintf(RED_OUT, "There are %1d inline declarations:\n", 
    declare_inline_exp_count
  ); 
  fflush(RED_OUT); 
  for (i = 1, bu = declare_inline_exp_list; bu; i++, bu = bu->bnext) { 
    fprintf(RED_OUT, "===<inline declaration %1d>=======", i); 
    print_inline_declare(bu->subexp); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
  } 
  fprintf(RED_OUT, "\n\n"); 
  fflush(RED_OUT); 
}
  /* red_print_inline_decalrations() */ 
  
  
  
void    red_print_xtions_details() { 
  print_xtions(); 
}
  /* red_print_xtions_details() */  
  
void    red_print_xtions() { 
  int	xi; 
  
  fprintf(RED_OUT, "\n%1d xtions\n", XTION_COUNT); 
  for (xi = 0; xi < XTION_COUNT; xi++) {
    fprintf(RED_OUT, "xi%1d: ", xi); 
    print_xtion_line(xi, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n"); 
  } 
}
  /* red_print_xtions() */  
  
  
void  red_print_xtion_details(int xi) {
  print_xtion(xi); 
} 
  /* red_print_xtion_details() */  
  
  
void  red_print_xtion(int xi, int pi) {
  print_xtion_line(xi, pi); 
} 
  /* red_print_xtion() */  
  
  
void	red_print_sync_xtion_compositions() { 
  int	sxi, ipi; 
  
  fprintf(RED_OUT, "\n%1d sync xtions\n", SYNC_XTION_COUNT); 
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    fprintf(RED_OUT, "sxi=%1d with %1d parties.\n", 
      sxi, SYNC_XTION[sxi].party_count
    ); 
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) {
      fprintf(RED_OUT, "  %1d: (p%1d:x%1d)", 
        ipi, 
        SYNC_XTION[sxi].party[ipi].proc, 
        SYNC_XTION[sxi].party[ipi].xtion
      ); 
      print_xtion_line(
        SYNC_XTION[sxi].party[ipi].xtion, 
        SYNC_XTION[sxi].party[ipi].proc
      );
      fprintf(RED_OUT, "\n");
  } } 
  fflush(RED_OUT); 
} 
  /* red_print_sync_xtion_compositions() */ 
  
  
  
  
void    red_print_sync_xtions() { 
  print_sync_xtions("", SYNC_XTION, SYNC_XTION_COUNT); 
}
  /* red_print_sync_xtions() */ 
  
  
  
  
void    red_print_sync_xtion(int sxi) { 
  if (sxi >= SYNC_XTION_COUNT || sxi < 0) { 
    fprintf(RED_OUT, 
      "\nError: a synchronization transition index %1d out of bound.\n", 
      sxi
    ); 
    exit(0); 
  } 
  print_sync_xtion(sxi, SYNC_XTION); 
}
  /* red_print_sync_xtion() */  
  
  
  
void    red_print_sync_xtion_lines(int sxi) { 
  if (sxi >= SYNC_XTION_COUNT || sxi < 0) { 
    fprintf(RED_OUT, 
      "\nError: a synchronization transition index %1d out of bound.\n", 
      sxi
    ); 
    exit(0); 
  } 
  print_sync_xtion_lines(sxi, SYNC_XTION); 
}
  /* red_print_sync_xtion_lines() */  
  
  
  
void    red_print_game_sync_xtions() { 
  print_sync_xtions("GAME", SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME); 
}
  /* red_print_game_sync_xtions() */ 
  
  
  
  
void    red_print_game_sync_xtion(int sxi) { 
  if (sxi >= SYNC_XTION_COUNT_GAME || sxi < 0) { 
    fprintf(RED_OUT, 
      "\nError: a game synchronization transition index %1d out of bound.\n", 
      sxi
    ); 
    exit(0); 
  } 
  print_sync_xtion(sxi, SYNC_XTION_GAME); 
}
  /* red_print_game_sync_xtion() */  
  
  
  
void    red_print_game_sync_xtion_lines(int sxi) { 
  if (sxi >= SYNC_XTION_COUNT_GAME || sxi < 0) { 
    fprintf(RED_OUT, 
      "\nError: a game synchronization transition index %1d out of bound.\n", 
      sxi
    ); 
    exit(0); 
  } 
  print_sync_xtion_lines(sxi, SYNC_XTION_GAME); 
}
  /* red_print_game_sync_xtion_lines() */  
  
  
  
void    red_print_modes() { 
  print_modes(); 
} 
  /* red_print_modes() */   
  
  
  
  
void    red_print_mode(int mi) { 
  print_mode(mi); 
} 
  /* red_print_mode() */  
  
  
  
void    red_print_summary() {
  print_summary(0.0); 
}
  /* red_print_summary() */  
  
  
  
inline void    red_print_diagram(redgram d) { 
  red_print_graph(d); 
}
  /* red_print_diagram() */ 
  
  
  
  
void    red_print_diagram_formula(redgram d) { 
  red_print_line(d); 
}
  /* red_print_diagram_formula() */ 
  
  
  
  
  
int 	red_query_diagram_root_var(
	redgram	d
	) {
  return(d->var_index); 		
}
  /* red_query_diagram_root_var() */   
  
  
  
int 	red_query_diagram_child_count(
	redgram	d
	) {
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return (0); 
  else switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
    if (d->u.bdd.zero_child == NORM_FALSE) 
      return(1); 
    else if (d->u.bdd.one_child == NORM_FALSE) 
      return(1); 
    else 
      return(2); 
  case TYPE_CRD: 
    return(d->u.crd.child_count); 
  case TYPE_HRD: 
    return(d->u.hrd.child_count); 
  case TYPE_FLOAT: 
    return(d->u.fdd.child_count); 
  case TYPE_DOUBLE: 
    return(d->u.dfdd.child_count); 
  default: 
    return(d->u.ddd.child_count); 
  } 		
}  
  /* red_query_diagram_child_count() */  
  
  
  
redgram red_query_diagram_child(d,ci) 
	redgram	d; 
	int	ci; 
{ 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
    switch (ci) { 
    case 0: 
      return(d->u.bdd.zero_child); 
    case 1: 
      return(d->u.bdd.one_child);  
    default: 
      return(NULL); 
    } 
  case TYPE_CRD: 
    if (ci >= d->u.crd.child_count) 
      return(NULL); 
    else 
      return(d->u.crd.arc[ci].child); 
  case TYPE_HRD: 
    if (ci >= d->u.hrd.child_count) 
      return(NULL); 
    else 
      return(d->u.hrd.arc[ci].child); 
  case TYPE_FLOAT: 
    if (ci >= d->u.fdd.child_count) 
      return(NULL); 
    else 
      return(d->u.fdd.arc[ci].child); 
  case TYPE_DOUBLE: 
    if (ci >= d->u.dfdd.child_count) 
      return(NULL); 
    else 
      return(d->u.dfdd.arc[ci].child); 
  default: 
    if (ci >= d->u.ddd.child_count) 
      return(NULL); 
    else 
      return(d->u.ddd.arc[ci].child); 
  }
}
  /* red_query_diagram_child() */ 
  
  
  
redgram red_query_diagram_arc_constraint(d,ci) 
	redgram	d; 
	int	ci; 
{ 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    if (ci >= d->u.crd.child_count) 
      return(NORM_FALSE); 
    else 
      return(crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
  case TYPE_HRD: 
    if (ci >= d->u.hrd.child_count) 
      return(NORM_FALSE); 
    else 
      return(hrd_atom(
    		d->u.hrd.hrd_exp, 
    		d->u.hrd.arc[ci].ub_numerator, 
    		d->u.hrd.arc[ci].ub_denominator 
    		)
    	   ); 
  case TYPE_FLOAT: 
    if (ci >= d->u.fdd.child_count) 
      return(NORM_FALSE); 
    else 
      return(fdd_atom(d->var_index, 
    	d->u.fdd.arc[ci].lower_bound, 
    	d->u.fdd.arc[ci].upper_bound
      ) ); 
  case TYPE_DOUBLE: 
    if (ci >= d->u.dfdd.child_count) 
      return(NORM_FALSE); 
    else 
      return(dfdd_atom(d->var_index, 
    	d->u.dfdd.arc[ci].lower_bound, 
    	d->u.dfdd.arc[ci].upper_bound
      ) ); 
  default: 
    if (ci >= d->u.ddd.child_count) 
      return(NORM_FALSE); 
    else 
      return(ddd_atom(
    		d->var_index, 
    		d->u.ddd.arc[ci].lower_bound, 
    		d->u.ddd.arc[ci].upper_bound
    		)
    	   ); 
  }
}
  /* red_query_diagram_arc_constraint() */ 
  
  
  
  
int red_diagram_discrete_arc_lb(d,ci) 
	redgram	d; 
	int	ci; 
{ 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_discrete_arc_lb().\n"); 
    exit(0); 
  }
  if (ci >= d->u.ddd.child_count) { 
    fprintf(RED_OUT, "Error: \n"); 
    exit(0); 
  }
  else {
    return(d->u.ddd.arc[ci].lower_bound);    	
  } 
} 
  /* red_diagram_discrete_arc_lb() */  
  
  
  
int red_query_diagram_discrete_arc_ub(d,ci)
	redgram	d; 
	int	ci; 
{ 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_discrete_arc_ub().\n"); 
    exit(0); 
  }
  if (ci >= d->u.ddd.child_count) { 
    fprintf(RED_OUT, "Error: \n"); 
    exit(0); 
  }
  else {
    return(d->u.ddd.arc[ci].upper_bound);    	
  } 
} 
  /* red_query_diagram_discrete_arc_ub() */  
  

  
float red_query_diagram_float_arc_lb(d,ci) 
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_FLOAT) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_float_arc_lb().\n"); 
    exit(0); 
  }
  else if (ci >= d->u.fdd.child_count) { 
    fprintf(RED_OUT, 
      "Error: child index %1d out of bound in red_query_diagram_float_arc_lb().\n", 
      ci
    ); 
    exit(0); 
  }
  else {
    return(d->u.fdd.arc[ci].lower_bound);    	
  } 
} 
  /* red_query_diagram_float_arc_lb() */  
  
  
  
float red_query_diagram_float_arc_ub(d,ci)
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_FLOAT) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_discrete_arc_ub().\n"); 
    exit(0); 
  }
  else  if (ci >= d->u.fdd.child_count) { 
    fprintf(RED_OUT, 
      "Error: child index %1d out of bound in red_query_diagram_float_arc_ub().\n", 
      ci
    ); 
    exit(0); 
  }
  else {
    return(d->u.fdd.arc[ci].upper_bound);    	
  } 
} 
  /* red_query_diagram_discrete_arc_ub() */  
  
  
  
double red_query_diagram_double_arc_lb(d,ci) 
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_DOUBLE
      ) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_discrete_arc_lb().\n"); 
    exit(0); 
  }
  else if (ci >= d->u.dfdd.child_count) { 
    fprintf(RED_OUT, "Error: child index %1d out of bound.\n", ci); 
    exit(0); 
  }
  else {
    return(d->u.dfdd.arc[ci].lower_bound);    	
  } 
} 
  /* red_query_diagram_double_arc_lb() */  
  
  
  
double red_query_diagram_double_arc_ub(d,ci)
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE == TYPE_DOUBLE
	   ) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_discrete_arc_ub().\n"); 
    exit(0); 
  }
  else  if (ci >= d->u.dfdd.child_count) { 
    fprintf(RED_OUT, "Error: child index %1d out of bound.\n", ci); 
    exit(0); 
  }
  else {
    return(d->u.dfdd.arc[ci].upper_bound);    	
  } 
} 
  /* red_query_diagram_double_arc_ub() */  
  
  
  
int red_query_diagram_zone_arc_ub(d,ci)
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_CRD) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_zone_arc_ub().\n"); 
    exit(0); 
  }
  else if (ci >= d->u.crd.child_count) { 
    fprintf(RED_OUT, "Error: \n"); 
    exit(0); 
  }
  else {
    return(d->u.crd.arc[ci].upper_bound);    	
  } 
} 
  /* red_query_diagram_zone_arc_ub() */  
  
  
int red_query_diagram_hybrid_arc_ubn(d, ci)
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_HRD) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_zone_arc_ubn().\n"); 
    exit(0); 
  }
  else if (ci >= d->u.hrd.child_count) { 
    fprintf(RED_OUT, "Error: \n"); 
    exit(0); 
  }
  else {
    return(d->u.hrd.arc[ci].ub_numerator);    	
  } 
} 
  /* red_query_diagram_hybrid_arc_ubn() */  
  


int red_query_diagram_hybrid_arc_ubd(d, ci)
	redgram	d; 
	int	ci; 
{ 
  if (VAR[d->var_index].TYPE != TYPE_HRD) { 
    fprintf(RED_OUT, "Error: mismatched variable type in red_diagram_hybrid_arc_ubd().\n"); 
    exit(0); 
  }
  else if (ci >= d->u.hrd.child_count) { 
    fprintf(RED_OUT, "Error: \n"); 
    exit(0); 
  }
  else {
    return(d->u.hrd.arc[ci].ub_denominator);    	
  } 
} 
  /* red_query_diagram_hybrid_arc_ubd() */  
  

redgram	*DP_PARENT_STACK; 
int	PS_TOP; 
struct red_type	(*DP_PROCESS)(); 

struct red_type	*rec_diagram_process(); 



redgram red_diagram_process_parent() {
  return(DP_PARENT_STACK[PS_TOP]); 	
}
  /* red_diagram_process_parent() */ 
  
  
  
  
redgram red_diagram_processed_child(d, ci) 
	redgram	d; 
	int	ci; 
{ 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    if (ci >= d->u.crd.child_count) 
      return(NORM_FALSE); 
    else 
      return(rec_diagram_process(d->u.crd.arc[ci].child)); 
  case TYPE_HRD: 
    if (ci >= d->u.hrd.child_count) 
      return(NORM_FALSE); 
    else 
      return(rec_diagram_process(d->u.hrd.arc[ci].child)); 
  default: 
    if (ci >= d->u.ddd.child_count) 
      return(NORM_FALSE); 
    else 
      return(rec_diagram_process(d->u.ddd.arc[ci].child)); 
  }
}
  /* red_diagram_processed_child() */ 
  
  
  

redgram red_diagram_skip_the_level(d) 
	redgram	d; 
{ 
  int		ci; 
  redgram	result; 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
      result = red_bop(OR, result, 
		       crd_one_constraint(
		         rec_diagram_process(d->u.crd.arc[ci].child), 
		         d->var_index, 
		         d->u.crd.arc[ci].upper_bound
		         ) 
		       ); 
    } 
    break; 
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) { 
      result = red_bop(OR, result, 
		       hrd_one_constraint(
		         rec_diagram_process(d->u.hrd.arc[ci].child), 
		         d->u.hrd.hrd_exp, 
		         d->u.hrd.arc[ci].ub_numerator, 
		         d->u.hrd.arc[ci].ub_denominator 
		         ) 
		       ); 
    } 
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      result = red_bop(OR, result, 
		       ddd_one_constraint(
		         rec_diagram_process(d->u.ddd.arc[ci].child), 
		         d->var_index, 
		         d->u.ddd.arc[ci].lower_bound, 
		         d->u.ddd.arc[ci].upper_bound
		         ) 
		       ); 
    }
  }
  return (result); 
}
  /* red_diagram_skip_the_level() */  



redgram	rec_diagram_process(d) 
	redgram	d; 
{ 
  // to be filled in. 
}
  /* rec_diagram_process() */  
  
  
  
redgram red_diagram_process(d, proc) 
	struct red_type	*d, (*proc)(); 
{ 
  redgram	result; 
  
  DP_PARENT_STACK = (redgram *) malloc(VARIABLE_COUNT * sizeof(redgram)); 
  PS_TOP = -1; 
  DP_PROCESS = proc; 
  result = rec_diagram_process(d); 
  
  free(DP_PARENT_STACK); 
  return(result); 
}
  /* red_diagram_process() */ 
  


void	red_timeless(redgram d, redgram *timeless_ptr, redgram *timed_ptr) { 
  gfp_guess_timeless(d, timeless_ptr, timed_ptr); 
}
  /* red_timeless() */  
  
 



  
/* The following procedures are for the control of transition firing. 
 */ 
int red_disable_xtion(xi) 
	int	xi; 
{ 
  int	ipi, pi, *fx, ixi, ixj; 
  
  check_xi(xi, "red_disable_xtion"); 
  for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
    pi = XTION[xi].process[ipi]; 
    fx = (int *) malloc((PROCESS[pi].firable_xtion_count - 1)*sizeof(int)); 
    for (ixi = 0, ixj = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) 
      if (PROCESS[pi].firable_xtion[ixi] != xi) { 
    	fx[ixj++] = PROCESS[pi].firable_xtion[ixi]; 
      } 
    free(PROCESS[pi].firable_xtion); 
    PROCESS[pi].firable_xtion = fx; 
    PROCESS[pi].firable_xtion_count--; 
  } 
  free(XTION[xi].process); 
  XTION[xi].process_count = 0; 
  XTION[xi].process = NULL; 
} 
  /* red_disable_xtion() */  
  
  
  
int 	red_enable_xtion(xi) 
	int	xi; 
{ 
  int	ipi, pi, *fx, ixi, ixj, *fp; 
  
  check_xi(xi, "red_enable_xtion"); 
  fp = (int *) malloc((PROCESS_COUNT+1)*sizeof(int)); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    fp[pi] = TYPE_TRUE; 	
  } 
  
  for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
    pi = XTION[xi].process[ipi]; 
    fp[pi] = TYPE_FALSE; 
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    if (fp[pi]) { 
      fx = (int *) malloc((PROCESS[pi].firable_xtion_count + 1)*sizeof(int)); 
      for (ixi = 0, ixj = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) 
        if (PROCESS[pi].firable_xtion[ixi] < xi) { 
    	  fx[ixj++] = PROCESS[pi].firable_xtion[ixi]; 
        } 
        else 
          break; 
      fx[ixj++] = xi; 
      for (; ixi < PROCESS[pi].firable_xtion_count; ixi++, ixj++) 
    	fx[ixj] = PROCESS[pi].firable_xtion[ixi]; 

      free(PROCESS[pi].firable_xtion); 
      PROCESS[pi].firable_xtion = fx; 
      PROCESS[pi].firable_xtion_count++; 
    } 
  free(XTION[xi].process); 
  XTION[xi].process_count = PROCESS_COUNT; 
  XTION[xi].process = (int *) malloc(PROCESS_COUNT * sizeof(int)); 
  for (ipi = 0; ipi < PROCESS_COUNT; ipi++) 
    XTION[xi].process[ipi] = ipi+1; 
  free(fp); 
}
  /* red_enable_xtion() */  
  
  
  
int 	red_check_xtion_enabled(xi)
	int	xi; 
{ 
  int 	pi, ixi; 
  
  check_xi(xi, "red_check_xtion_enabled"); 
  if (XTION[xi].process_count != 0 || XTION[xi].process != NULL) 
    return(TYPE_FALSE); 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      if (PROCESS[pi].firable_xtion[ixi] == xi) { 
      	fprintf(RED_OUT, "Error: mismatch in transition disabling \n"); 
      	fprintf(RED_OUT, "       in red_check_xtion_enabled_all().\n"); 
      	exit(0); 
      }
    } 	
  } 	
} 
  /* red_check_xtion_enabled() */  
  
  
  
  
int 	red_disable_proc(pi)
	int	pi; 
{ 
  int	ixi, xi, *pc, ipi, ipj; 
  
  check_pi(pi, "red_disable_proc"); 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
    xi = PROCESS[pi].firable_xtion[ixi]; 
    pc = (int *) malloc((XTION[xi].process_count - 1)*sizeof(int)); 
    for (ipi = 0, ipj = 0; ipi < XTION[xi].process_count; ipi++) 
      if (XTION[xi].process[ipi] != pi) { 
    	pc[ipj++] = XTION[xi].process[ipi]; 
      } 
    free(XTION[xi].process); 
    XTION[xi].process = pc; 
    XTION[xi].process_count--; 
  } 
  free(PROCESS[pi].firable_xtion); 
  PROCESS[pi].firable_xtion_count = 0; 
  PROCESS[pi].firable_xtion = NULL; 
}
  /* red_enable_proc() */  
  
  
int 	red_enable_proc(pi)
	int	pi; 
{ 
  int	ixi, xi, *fp, ipi, ipj, *fx; 
  
  check_pi(pi, "red_enable_proc"); 
  // We first allocate an array of flags for the transitions. 
  fx = (int *) malloc(XTION_COUNT*sizeof(int)); 
  for (xi = 0; xi < XTION_COUNT; xi++) { 
    fx[xi] = TYPE_TRUE; 
  } 
  // xtion xi is flagged true if it is not executable by pi. 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
    xi = PROCESS[pi].firable_xtion[ixi]; 
    fx[xi] = TYPE_FALSE; 
  } 
  for (xi = 0; xi < XTION_COUNT; xi++) 
    if (fx[xi]) { 
      fp = (int *) malloc((XTION[xi].process_count + 1)*sizeof(int)); 
      for (ipi = 0, ipj = 0; ipi < XTION[xi].process_count; ipi++) 
        if (XTION[xi].process[ipi] < pi) { 
    	  fx[ipj++] = XTION[xi].process[ipi]; 
        } 
        else 
          break; 
      fp[ipj++] = pi; 
      for (; ipi < XTION[xi].process_count; ipi++, ipj++) 
    	fp[ipj] = XTION[xi].process[ipi]; 

      free(XTION[xi].process); 
      XTION[xi].process = fp; 
      XTION[xi].process_count++; 
    } 
  free(PROCESS[pi].firable_xtion); 
  PROCESS[xi].firable_xtion_count = XTION_COUNT; 
  PROCESS[xi].firable_xtion = (int *) malloc(XTION_COUNT * sizeof(int)); 
  for (ixi = 0; ixi < XTION_COUNT; ixi++) 
    PROCESS[pi].firable_xtion[ixi] = ixi+1; 
  free(fx); 
}
  /* red_enable_proc() */  
  
  
int red_check_proc_enabled(pi)
	int	pi; 
{ 
  int 	xi, ipi; 
  
  check_pi(pi, "red_check_proc_enabled"); 
  if (   PROCESS[pi].firable_xtion_count != 0 
      || PROCESS[pi].firable_xtion != NULL
      ) 
    return(TYPE_FALSE); 
  
  for (xi = 1; xi <= XTION_COUNT; xi++) { 
    for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
      if (XTION[pi].process[ipi] == pi) { 
      	fprintf(RED_OUT, "Error: mismatch in process disabling \n"); 
      	fprintf(RED_OUT, "       in red_check_proc_enabled_all().\n"); 
      	exit(0); 
      }
    } 	
  } 	
} 
  /* red_check_proc_enabled() */  
  
  
int red_disable_sync_xtion(
  int	sxi, 
  int	flag_sync_xtion_table_choice
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_disable_sync_xtion"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 

    SYNC_XTION[sxi].status = SYNC_XTION[sxi].status & ~FLAG_SXI_ENABLED; 
  }
  else { 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 

    SYNC_XTION_GAME[sxi].status = SYNC_XTION_GAME[sxi].status & ~FLAG_SXI_ENABLED; 
  }
}
  /* red_disable_sync_xtion() */ 
  
  
  
int 	red_enable_sync_xtion(
  int	sxi, 
  int	flag_sync_xtion_table_choice
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_enable_sync_xtion"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 
    SYNC_XTION[sxi].status = SYNC_XTION[sxi].status | FLAG_SXI_ENABLED; 
  }
  else { 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 
    SYNC_XTION_GAME[sxi].status = SYNC_XTION_GAME[sxi].status | FLAG_SXI_ENABLED; 
  } 
}
  /* red_enable_sync_xtion() */ 
  
  
  
int 	red_check_sxi_enabled(
  int	sxi, 
  int	flag_sync_xtion_table_choice
) {
  check_sxi(sxi, flag_sync_xtion_table_choice, 
    "red_check_sxi_enabled"
  ); 
  if (flag_sync_xtion_table_choice == RED_USE_DECLARED_SYNC_XTION) { 
    if (sxi == SYNC_XTION_COUNT) 
      return(RED_FLAG_UNKNOWN); 
    if (SYNC_XTION[sxi].status & FLAG_SXI_ENABLED)
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  }
  else { 
    if (sxi == SYNC_XTION_COUNT_GAME) 
      return(RED_FLAG_UNKNOWN); 
    if (SYNC_XTION_GAME[sxi].status & FLAG_SXI_ENABLED)
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  } 
}
  /* red_check_sxi_enabled() */ 
  
  
  
int red_disable_proc_xtion(xi, pi)
	int	xi, pi; 
{ 
  int	ixi, ixj, *fx, ipi, ipj, *fp, sxi; 
  
  check_xi(xi, "red_disable_proc_xtion"); 
  check_pi(pi, "red_disable_proc_xtion"); 
  
  // first remove xi from the array of firable transitions of process pi. 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) 
    if (xi == PROCESS[pi].firable_xtion[ixi]) {   	
      fx = (int *) malloc((PROCESS[pi].firable_xtion_count-1) * sizeof(int)); 
      for (ixj = 0; ixj < ixi; ixj++) { 
      	fx[ixj] = PROCESS[pi].firable_xtion[ixj]; 
      } 
      for (ixj = ixi+1; ixj < PROCESS[pi].firable_xtion_count; ixj++) 
        fx[ixj-1] = PROCESS[pi].firable_xtion[ixj]; 
        
      free(PROCESS[pi].firable_xtion); 
      PROCESS[pi].firable_xtion_count--; 
      PROCESS[pi].firable_xtion = fx; 
      break; 
    } 
  // Then remove pi from the array of processes of xtion xi. 
  for (ipi = 0; ipi < XTION[xi].process_count; ipi++) 
    if (pi == XTION[xi].process[ipi]) {   	
      fp = (int *) malloc((XTION[xi].process_count-1) * sizeof(int)); 
      for (ipj = 0; ipj < ipi; ipj++) { 
      	fp[ipj] = XTION[xi].process[ipj]; 
      } 
      for (ipj = ipi+1; ipj < XTION[xi].process_count; ipj++) 
        fp[ipj-1] = XTION[xi].process[ipj]; 
        
      free(XTION[xi].process); 
      XTION[xi].process_count--; 
      PROCESS[pi].firable_xtion = fp; 
      break; 
    } 
  
  // Then disable all sync xtions with the combination of pi and xi.  
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) {
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) 
      if (   SYNC_XTION[sxi].party[ipi].proc == pi 
          && SYNC_XTION[sxi].party[ipi].xtion == xi 
          ) {
        SYNC_XTION[sxi].status = SYNC_XTION[sxi].status & ~FLAG_SXI_ENABLED; 
        break; 
      } 	
  } 
}
  /* red_disable_proc_xtion() */  
  
  
  
  
int red_enable_proc_xtion(xi, pi)
	int	xi, pi; 
{ 
  int	ixi, ixj, *fx, ipi, ipj, *fp, sxi; 
  
  check_xi(xi, "red_disable_proc_xtion"); 
  check_pi(pi, "red_disable_proc_xtion"); 
  
  // first add xi to the array of firable transitions of process pi. 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) 
    if (xi == PROCESS[pi].firable_xtion[ixi]) 
      break; 
  if (ixi == PROCESS[pi].firable_xtion_count) { 
    fx = (int *) malloc((PROCESS[pi].firable_xtion_count+1) * sizeof(int)); 
    for (ixi = 0; PROCESS[pi].firable_xtion[ixi] < xi; ixi++) { 
      fx[ixi] = PROCESS[pi].firable_xtion[ixi]; 
    } 
    fx[ixi++] = xi; 
    for (; ixi <= PROCESS[pi].firable_xtion_count; ixi++) 
      fx[ixi] = PROCESS[pi].firable_xtion[ixi-1]; 
        
    free(PROCESS[pi].firable_xtion); 
    PROCESS[pi].firable_xtion_count++; 
    PROCESS[pi].firable_xtion = fx; 
  }   
  // Then add pi to the array of processes of xtion xi. 
  for (ipi = 0; ipi < XTION[xi].process_count; ipi++) 
    if (pi == XTION[xi].process[ipi]) 
      break; 
  if (ipi == XTION[xi].process_count) { 
    fp = (int *) malloc((XTION[xi].process_count+1) * sizeof(int)); 
    for (ipi = 0; XTION[xi].process[ipi] < pi; ipi++) { 
      fp[ipi] = XTION[xi].process[ipi]; 
    } 
    fp[ipi++] = pi; 
    for (; ipi <= XTION[xi].process_count; ipi++) 
      fp[ipi] = XTION[xi].process[ipi-1]; 
        
    free(XTION[xi].process); 
    XTION[xi].process_count++; 
    XTION[xi].process = fp; 
  }   
  
  // Then disable all sync xtions with the combination of pi and xi.  
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) {
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) 
      if (   SYNC_XTION[sxi].party[ipi].proc == pi 
          && SYNC_XTION[sxi].party[ipi].xtion == xi 
          ) {
        SYNC_XTION[sxi].status = SYNC_XTION[sxi].status | FLAG_SXI_ENABLED; 
        break; 
      } 	
  } 
}
  /* red_enable_proc_xtion() */  
  
  
  
  
  
int red_check_enabled_specific(xi, pi)
	int	xi, pi; 
{ 
  int	ixi, ixj, *fx, ipi, ipj, *fp, sxi; 
  
  check_xi(xi, "red_disable_proc_xtion"); 
  check_pi(pi, "red_disable_proc_xtion"); 
  
  // first add xi to the array of firable transitions of process pi. 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) 
    if (xi == PROCESS[pi].firable_xtion[ixi]) 
      break; 
  if (ixi == PROCESS[pi].firable_xtion_count) 
    return(TYPE_FALSE); 

  // Then add pi to the array of processes of xtion xi. 
  for (ipi = 0; ipi < XTION[xi].process_count; ipi++) 
    if (pi == XTION[xi].process[ipi]) 
      break; 
  if (ipi == XTION[xi].process_count) 
    return(TYPE_FALSE); 
  
  // Then disable all sync xtions with the combination of pi and xi.  
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) {
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) 
      if (   SYNC_XTION[sxi].party[ipi].proc == pi 
          && SYNC_XTION[sxi].party[ipi].xtion == xi 
          && !(SYNC_XTION[sxi].status & FLAG_SXI_ENABLED)
          )  
        return(TYPE_FALSE); 
  } 
  return(TYPE_TRUE); 
}
  /* red_check_enabled_specific() */  
  


int	PI_USER_SYNC_STATEMENT; 

void	rec_user_sync_statements(
  struct statement_type	*st,  
  void			(*base_statement_op)()
) {
  int			i, lvi, ipi, ci, result, pi, flag;
  struct red_type	*red_addr; 

  if (!st) 
    return; 
  
  switch (st->op) { 
  case UNCHANGED: 
    return;  
  case ST_IF: 
  case ST_WHILE: 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
  case ASSIGN_DISCRETE_CONSTANT:
  case ASSIGN_DISCRETE_POLYNOMIAL:
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 

  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
  case INCREMENT_BY_CONSTANT:
  case DECREMENT_BY_CONSTANT:
    fprintf(RED_OUT, 
      "\nERROR: rec_user_sync_statements(), at the moment, \n"
    ); 
    fprintf(RED_OUT, 
      "       only atomic and sequential statements are supported.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
    break; 

  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      rec_user_sync_statements(st->u.seq.statement[i], base_statement_op); 
    } 
    break; 

  case ST_GUARD: 
    base_statement_op(PI_USER_SYNC_STATEMENT, st->u.guard.red_cond[PI_USER_SYNC_STATEMENT], -1); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX != 0) { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        PI_USER_SYNC_STATEMENT, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE && pi != 0) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      } 
      else { 
      	fprintf(RED_OUT, "\nERROR: illegal variable process index %1d.\n", 
      	  pi
      	); 
      	fflush(RED_OUT); 
      	exit(0); 
      } 
    }
    base_statement_op(PI_USER_SYNC_STATEMENT, NULL, lvi); 
    break; 
  } 
}
  /* rec_user_sync_statements() */ 


void	red_user_sync_statements(
  int	sxi, 
  int	ipi, 
  void	(*base_statement_op)()
) { 
  PI_USER_SYNC_STATEMENT = SYNC_XTION[sxi].party[ipi].proc; 
  rec_user_sync_statements(SYNC_XTION[sxi].party[ipi].statement, 
    base_statement_op
  ); 
}
  /* red_user_sync_statements() */ 




struct red_type	*rec_first_cube(d, ci)
     struct red_type	*d;
     int		ci; 
{
  struct red_type	*result, *conj;

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(d);

  cube_child_index[ci] = 0; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    child_stack_level_push();
    conj = rec_first_cube(d->u.crd.arc[0].child, ci+1);
    bchild_stack_push(conj, d->u.crd.arc[0].upper_bound);
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    conj = rec_first_cube(d->u.hrd.arc[0].child, ci+1);
    hchild_stack_push(conj, 
      d->u.hrd.arc[0].ub_numerator,
      d->u.hrd.arc[0].ub_denominator
    ); 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  default: 
    child_stack_level_push();
    conj = rec_first_cube(d->u.ddd.arc[0].child, ci+1);
    ichild_stack_push(conj, 
      d->u.ddd.arc[0].lower_bound, 
      d->u.ddd.arc[0].upper_bound 
    ); 
    result = ddd_new(d->var_index);
  }
  return(result);
}
/* rec_first_cube() */




struct red_type	*red_first_cube(d) 
	struct red_type	*d; 
{ 
  if (d == NORM_FALSE) 
    return(d); 
  
  if (cube_child_index == NULL) { 
    cube_child_index = (int *) malloc(VARIABLE_COUNT * sizeof(int)); 	
  } 
  target_cube_set = d; 
  return(rec_first_cube(d, 0)); 
} 
  /* red_first_cube() */  
  
  
  
struct red_type	*rec_next_cube(d, ci)
     struct red_type	*d;
     int		ci; 
{
  struct red_type	*result, *conj;

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    child_stack_level_push(); 
    conj = rec_next_cube(d->u.crd.arc[cube_child_index[ci]].child, ci+1); 
    if (conj == NORM_FALSE) {
      cube_child_index[ci]++; 
      if (cube_child_index[ci] < d->u.crd.child_count) 
        conj = rec_first_cube(d->u.crd.arc[cube_child_index[ci]].child, ci+1);
      else {
        cube_child_index[ci] = 0; 
      } 
    } 
    bchild_stack_push(conj, d->u.crd.arc[cube_child_index[ci]].upper_bound);
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    conj = rec_next_cube(d->u.hrd.arc[cube_child_index[ci]].child, ci+1);
    if (conj == NORM_FALSE) {
      cube_child_index[ci]++; 
      if (cube_child_index[ci] < d->u.hrd.child_count) 
        conj = rec_first_cube(d->u.hrd.arc[cube_child_index[ci]].child, ci+1);
      else {
        cube_child_index[ci] = 0; 
      } 
    } 
    hchild_stack_push(conj, 
      d->u.hrd.arc[cube_child_index[ci]].ub_numerator,
      d->u.hrd.arc[cube_child_index[ci]].ub_denominator
    ); 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  default: 
    child_stack_level_push();
    conj = rec_next_cube(d->u.ddd.arc[cube_child_index[ci]].child, ci+1);
    if (conj == NORM_FALSE) {
      cube_child_index[ci]++; 
      if (cube_child_index[ci] < d->u.ddd.child_count) 
        conj = rec_first_cube(d->u.ddd.arc[cube_child_index[ci]].child, ci+1);
      else {
        cube_child_index[ci] = 0; 
      } 
    } 
    ichild_stack_push(conj, 
      d->u.ddd.arc[cube_child_index[ci]].lower_bound,
      d->u.ddd.arc[cube_child_index[ci]].upper_bound
    );
    result = ddd_new(d->var_index);
  }
  return(result);
}
/* rec_next_cube() */


struct red_type	*red_next_cube(d) 
	struct red_type	*d; 
{ 
  if (d == NORM_FALSE) 
    return(d); 
  else if (target_cube_set != d) { 
    fprintf(RED_OUT, "Error, cube set changed in red_next_cube()!\n");  
    exit(0); 
  } 
  
  return(rec_next_cube(d, 0)); 
} 
  /* red_next_cube() */  
  


int	UB_CUBE, LB_CUBE, VI_CUBE; 

struct red_type	*rec_get_cube_discrete_value(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
/*
  struct cache4_hash_entry_type	*ce; 
*/
  if (d == NORM_FALSE) {
    fprintf(RED_OUT, "Somehow, this is a false cube.\n"); 
    return; 
  }
  else if (d == NORM_NO_RESTRICTION || d->var_index > VI_CUBE) { 
    LB_CUBE = VAR[VI_CUBE].U.DISC.LB; 
    UB_CUBE = VAR[VI_CUBE].U.DISC.UB;  
    return; 
  } 
  else if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    if (d->result_stack->result)
      return; 
    else 
      d->result_stack->result = NORM_NO_RESTRICTION; 
    
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      child = rec_get_cube_discrete_value(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      child = rec_get_cube_discrete_value(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_get_cube_discrete_value(d->u.fdd.arc[ci].child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_get_cube_discrete_value(d->u.dfdd.arc[ci].child);
    }
    break;
  default: 
    if (VI_CUBE == d->var_index) {
      if (LB_CUBE > d->u.ddd.arc[0].lower_bound) 
        LB_CUBE = d->u.ddd.arc[0].lower_bound; 
      if (UB_CUBE < d->u.ddd.arc[d->u.ddd.child_count-1].upper_bound) 
        UB_CUBE = d->u.ddd.arc[d->u.ddd.child_count-1].upper_bound; 
    }
    else for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      child = rec_get_cube_discrete_value(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_get_cube_discrete_value() */



int	red_get_cube_discrete_value(d, vn, lbp, ubp)
	struct red_type	*d; 
	char		*vn; 
	int		*lbp, *ubp; 
{ 
  int	oi, pi; 
  
  VI_CUBE = red_query_var_index(vn); 	
  if (VI_CUBE < 0) {
    *lbp =0; 
    *ubp = -1; 
    return VI_CUBE; 
  }
  
  UB_CUBE = VAR[VI_CUBE].U.DISC.LB-1; 
  LB_CUBE = VAR[VI_CUBE].U.DISC.UB+1; 
  
  red_init_result(d); 
  rec_get_cube_discrete_value(d); 
  red_clear_result(d); 
  
  *lbp = LB_CUBE; 
  *ubp = UB_CUBE; 
  
  return(VI_CUBE); 
}
  /* red_get_cube_discrete_value() */  



redgram red_assign_valued_child(
  redgram	d, 
  int		vi, 
  int		value, 
  redgram	child
) { 
  switch (VAR[vi].TYPE) { 
  case TYPE_DISCRETE: 
    d = red_variable_eliminate(d, vi); 
    d = ddd_one_constraint(d, vi, value, value); 
    break; 
  case TYPE_BDD: 
    d = red_variable_eliminate(d, vi); 
    d = bdd_one_constraint(d, vi, value); 
    break; 
  case TYPE_CLOCK: 
    vi = VAR[vi].U.CLOCK.CLOCK_INDEX; 
    d = red_time_clock_eliminate(d, vi); 
    if (2*value < CLOCK_POS_INFINITY) { 
      d = crd_one_constraint(d, ZONE[0][vi], -2*value); 
      d = crd_one_constraint(d, ZONE[vi][0], 2*value); 
    } 
    break; 
  
  case TYPE_DENSE: 
    d = red_variable_eliminate(d, vi); 
    if (2*value < CLOCK_POS_INFINITY) { 
      d = hrd_one_constraint(d, VAR[vi].U.DENSE.HE_LB, -2*value, 1); 
      d = hrd_one_constraint(d, VAR[vi].U.DENSE.HE_UB, 2*value, 1); 
    } 
    break;   
  } 
  return(red_bop(AND, d, child)); 
} 
  /* red_assign_valued_child() */ 




/************************************************************************
  The following routines are for supporting the query and selection of 
  processes and transitions that appear in a sync bulk diagram.  
 */
#define RED_FLAG_NO_GC_TOKEN	-1 
struct index_pair_link_type	
  *redlib_pxpair[8] 
  = {NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL}, 
  *redlib_pxpair_pos[8] 
  = {NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL}; 



int	FLAG_REDLIB_RESTRICTION_DIRECTION = FLAG_BCK_ANALYSIS; 
/* The other value is FLAG_FWD_ANALYSIS
 */

int	token_for_redlib_sync_bulk_restriction = RED_FLAG_NO_GC_TOKEN; 
struct red_type	*redlib_sync_bulk_restriction = NULL; 


struct red_type	*red_query_diagram_current_state() { 
  return(redlib_sync_bulk_restriction); 
}
  /* red_query_diagram_current_state() */ 


void	red_set_discrete_current_state(
  char	*vn, 
  int	value
) { 
  int	ri, vi; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  for (ri = 1; ri <= 7; ri++) { 
    free_index_pair_list(redlib_pxpair[ri]); 
    redlib_pxpair[ri] = NULL; 
    redlib_pxpair_pos[ri] = NULL; 
  } 

  vi = red_query_var_index(vn); 
  
  redlib_sync_bulk_restriction = red_assign_valued_child(
    redlib_sync_bulk_restriction, vi, value, NORM_NO_RESTRICTION   
  ); 
  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
} 
  /* red_set_discrete_current_state() */ 
  




redgram	red_begin_sync_xtion_bulk_restriction_fwd(
  redgram	dsrc
) { 
  redlib_sync_bulk_restriction = red_add_lazy_trigger_sync_bulk(
    RT[XI_SYNC_ALL_WITH_PROC_HOLDERS], dsrc
  ); 
  FLAG_REDLIB_RESTRICTION_DIRECTION = FLAG_FWD_ANALYSIS;
  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST 
  ); 
  return(redlib_sync_bulk_restriction); 
}
  /* red_begin_sync_xtion_bulk_restriction_fwd() */ 



redgram	red_begin_sync_xtion_bulk_restriction_bck(
  redgram	dsrc
) { 
  redlib_sync_bulk_restriction 
  = red_bop(AND, dsrc, RT[XI_SYNC_ALL_WITH_PROC_HOLDERS]); 
  FLAG_REDLIB_RESTRICTION_DIRECTION = FLAG_BCK_ANALYSIS;
  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
  return(redlib_sync_bulk_restriction); 
}
  /* red_begin_sync_xtion_bulk_restriction_bck() */ 



void	red_end_sync_xtion_bulk_restriction() { 
  int	ri; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  for (ri = 1; ri <= 7; ri++) { 
    free_index_pair_list(redlib_pxpair[ri]); 
    redlib_pxpair_pos[ri] = NULL; 
  } 
  token_for_redlib_sync_bulk_restriction = RED_FLAG_NO_GC_TOKEN;
  redlib_sync_bulk_restriction = NULL;
  garbage_collect(FLAG_GC_SILENT);
}
  /* red_end_sync_xtion_bulk_restriction() */  



redgram	red_restrict_sync_bulk(pi, xi) { 
  int	ri; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  for (ri = 1; ri <= 7; ri++) { 
    free_index_pair_list(redlib_pxpair[ri]); 
    redlib_pxpair[ri] = NULL; 
    redlib_pxpair_pos[ri] = NULL; 
  } 

  redlib_sync_bulk_restriction 
  = ddd_one_constraint(redlib_sync_bulk_restriction, 
    variable_index[TYPE_XTION_INSTANCE][pi][0], xi, xi
  ); 
  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
  return(redlib_sync_bulk_restriction); 
} 
  /* red_restrict_sync_bulk() */ 
  


redgram	red_restrict_stream_sync_bulk(
  int			pi,
  int			xi, 
  int			soi,  
  int			value
) { 
  int			ri, vi, ci, pj; 
  struct ps_exp_type	*dest_exp; 
  struct red_type	*red_addr, *result; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  dest_exp = XTION[xi].stream_operation[soi].var; 
  red_addr = red_delayed_operand_indirection(dest_exp, pi, 
    redlib_sync_bulk_restriction
  ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
    for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
         vi <= red_addr->u.ddd.arc[ci].upper_bound; 
         vi++
           ) { 
      result = red_bop(OR, result, 
        red_assign_valued_child(
          redlib_sync_bulk_restriction, vi, 
          value, red_addr->u.ddd.arc[ci].child   
      ) ); 
    } 
  } 
  redlib_sync_bulk_restriction = result; 

  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
  return(redlib_sync_bulk_restriction); 
} 
  /* red_restrict_stream_sync_bulk() */ 
  

int	red_query_exp_sync_bulk(
  int			pi, 
  struct ps_exp_type	*exp
) {
  struct red_type	*red_value; 
  int			ci, value; 
  
  red_value = red_delayed_exp_value(exp, pi, redlib_sync_bulk_restriction); 
  ci = rand() % red_value->u.ddd.child_count; 
  redlib_sync_bulk_restriction = red_bop(AND, 
    redlib_sync_bulk_restriction, red_value->u.ddd.arc[ci].child
  ); 
  value = rand() % (
    red_value->u.ddd.arc[ci].upper_bound 
  - red_value->u.ddd.arc[ci].lower_bound 
  + 1
  ); 
  value = value + red_value->u.ddd.arc[ci].lower_bound; 
  return(value); 
}
  /* red_query_exp_sync_bulk() */ 



int	red_get_stream_output(
  int	pi,
  int	xi, 
  int	soi 
) { 
  return(red_query_exp_sync_bulk(pi, 
    XTION[xi].stream_operation[soi].value_exp
  ) ); 
}
  /* red_get_stream_output() */ 





int	red_heap_malloc(int size) {
  int			ci; 
  struct red_type	*result, *child; 
  int			addr, child_size, cc; 
  
  if (size <= 0) {
    fprintf(RED_OUT, 
      "\nWarning, allocation of non-positive size %1d of spaces.\n", 
      size
    ); 
    fflush(RED_OUT); 	
    return(0); 
  }
  addr = VARIABLE_COUNT + 1; 
  if (RT[INDEX_MALLOC_SPACE] == NORM_FALSE) { 
    if (MEMORY_SIZE >= size) { 
      RT[INDEX_MALLOC_SPACE] = ddd_one_constraint(
        ddd_atom(RHS_PI, size, size), 
        LHS_PI, MEMORY_START_VI, MEMORY_START_VI
      ); 
      return(MEMORY_START_VI); 
    } 
    else { 
      return(0); 
    } 
  } 
  // First, we check if there is free space available at the lower end. 
  if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[0].lower_bound - MEMORY_START_VI
      >= size
      ) { 
    RT[INDEX_MALLOC_SPACE] = red_bop(OR, RT[INDEX_MALLOC_SPACE], 
      ddd_one_constraint(ddd_atom(RHS_PI, size, size), 
        LHS_PI, MEMORY_START_VI, MEMORY_START_VI
    ) ); 
    return(addr); 
  } 
  // Then, we check if there is free space available at the upper end. 
  cc = RT[INDEX_MALLOC_SPACE]->u.ddd.child_count; 
  child = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[cc-1].child; 
  child_size = child->u.ddd.arc[0].lower_bound; 
  addr = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[cc-1].lower_bound + child_size; 
  if (VARIABLE_COUNT - addr >= size) { 
    RT[INDEX_MALLOC_SPACE] = red_bop(OR, RT[INDEX_MALLOC_SPACE], 
      ddd_one_constraint(ddd_atom(RHS_PI, size, size), 
        LHS_PI, addr, addr
    ) ); 
    return(addr); 
  } 
  // Finally, we check if there is an available free space in the middle.
  result = NORM_FALSE; 
  for (ci = 0; ci < RT[INDEX_MALLOC_SPACE]->u.ddd.child_count-1; ci++) { 
    child = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[ci].child; 
    child_size = child->u.ddd.arc[0].lower_bound; 
    if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[ci+1].lower_bound
        - (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[ci].lower_bound + child_size) 
        >= size) { 
      addr = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[ci].lower_bound + child_size; 
      RT[INDEX_MALLOC_SPACE] = red_bop(OR, RT[INDEX_MALLOC_SPACE], 
        ddd_one_constraint(ddd_atom(RHS_PI, size, size), 
          LHS_PI, addr, addr
      ) ); 
      return(addr); 
  } }
  return(0); 
}
  /* red_heap_malloc() */ 





redgram	red_malloc_exp_sync_bulk(
  int	pi,
  int	xi, 
  int	soi 
) { 
  int			vi, ci, size, maddr; 
  struct ps_exp_type	*dest_exp; 
  struct red_type	*red_addr, *result; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  dest_exp = XTION[xi].stream_operation[soi].var; 
  
  size = red_query_exp_sync_bulk(
    pi, XTION[xi].stream_operation[soi].value_exp
  );  
  
  maddr = red_heap_malloc(size); 
  if (!maddr) {
    fprintf(RED_OUT, 
      "\nERROR: out of heap space in malloc() of size %1d to ", 
      size
    ); 
    pcform(dest_exp); 
    return(redlib_sync_bulk_restriction); 
  }
  red_addr = red_delayed_operand_indirection(dest_exp, pi, 
    redlib_sync_bulk_restriction
  ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
    for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
         vi <= red_addr->u.ddd.arc[ci].upper_bound; 
         vi++
         ) { 
      result = red_bop(OR, result, 
        red_assign_valued_child(
          redlib_sync_bulk_restriction, vi, 
          maddr, red_addr->u.ddd.arc[ci].child   
      ) ); 
    } 
  } 
  redlib_sync_bulk_restriction = result; 

  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
  return(redlib_sync_bulk_restriction); 
} 
  /* red_malloc_exp_sync_bulk() */ 
  


void	red_heap_free(int addr) {
  int			ci, cj, mid; 
  struct red_type	*result, *child; 
  
  if (RT[INDEX_MALLOC_SPACE] == NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR, Illegal free operation on unalloc'd space 0x%x.\n", 
      addr
    );
    fflush(RED_OUT); 
    bk(0); 
  }
  ci = 0; 
  cj = RT[INDEX_MALLOC_SPACE]->u.ddd.child_count-1;
  for (; ci <= cj; ) { 
    mid = (ci+cj)/2; 
    if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].lower_bound == addr) { 
      child = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].child; 
      redlib_sync_bulk_restriction = red_multi_variables_eliminate( 
        redlib_sync_bulk_restriction, 
        addr, addr + child->u.ddd.arc[0].lower_bound - 1
      ); 
      RT[INDEX_MALLOC_SPACE] = red_bop(SUBTRACT, 
        RT[INDEX_MALLOC_SPACE], ddd_atom(LHS_PI, addr, addr)
      ); 
      return; 
    } 
    else if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].lower_bound < addr) {
      ci = mid+1; 
    } 
    else { 
      cj = mid-1; 
    } 
  } 
  fprintf(RED_OUT, 
    "\nERROR, Illegal free operation on unalloc'd space %x.\n", 
    addr
  );
  fflush(RED_OUT); 
  bk(0); 
  return; 
}
  /* red_heap_free() */ 




redgram	red_free_exp_sync_bulk(
  int	pi,
  int	xi, 
  int	soi 
) { 
  int			ri, vi, ci, pj, size, maddr; 
  struct ps_exp_type	*dest_exp; 
  struct red_type	*red_addr, *result; 
  
  release_gc_token(
    token_for_redlib_sync_bulk_restriction, 
    &TOKEN_PROTECTION_LIST
  ); 
  maddr = red_query_exp_sync_bulk(
    pi, XTION[xi].stream_operation[soi].value_exp
  );  
  
  red_heap_free(maddr); 

  token_for_redlib_sync_bulk_restriction 
  = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  protect_from_gc_with_token(
    redlib_sync_bulk_restriction, 
    token_for_redlib_sync_bulk_restriction, 
    TOKEN_PROTECTION_LIST
  ); 
  return(redlib_sync_bulk_restriction); 
} 
  /* red_free_exp_sync_bulk() */ 
  

struct red_type	*red_query_malloc_space() {
  return(RT[INDEX_MALLOC_SPACE]); 
}
  /* red_query_malloc_space() */  


void 	red_set_malloc_space(
  struct red_type	*d  
) {
  RT[INDEX_MALLOC_SPACE] = d; 
} 
  /* red_set_malloc_space() */ 


 

struct a23tree_type		*redlib_pxpair_tree; 
struct index_pair_link_type	*REDLIB_PXPAIR_LIST; 
int				redlib_restriction_roles; 

int	redlib_roles_2_red_roles(int redlib_roles) {
  int	ans = 0; 
  
  if (redlib_roles & RED_GAME_MODL) 
    ans = ans | FLAG_GAME_MODL; 
  if (redlib_roles & RED_GAME_SPEC) 
    ans = ans | FLAG_GAME_SPEC; 
  if (redlib_roles & RED_GAME_ENVR) 
    ans = ans | FLAG_GAME_ENVR; 

  return(ans); 
}
  /* redlib_roles_2_red_roles() */ 
  
  
  
int			*PX_COUNT = NULL; 
struct index_link_type	**PX = NULL; 

struct red_type	*rec_fillin_pxpairs(d)
     struct red_type	*d;
{
  int			xi, ci;
  struct rec_type	*nrec, *rec;

  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
      || d->var_index > variable_index[TYPE_XTION_INSTANCE][PROCESS_COUNT][0]
      )
    return; 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, redlib_pxpair_tree, 
    rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return; 
  }

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      rec_fillin_pxpairs(d->u.crd.arc[ci].child);
    }
    break; 
  case TYPE_HRD: 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_fillin_pxpairs(d->u.hrd.arc[ci].child);
    }
    break; 
  case TYPE_LAZY_EXP: 
    rec_fillin_pxpairs(d->u.lazy.false_child);
    rec_fillin_pxpairs(d->u.lazy.true_child);
    break; 
  default: 
    if (VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      	for (xi = d->u.ddd.arc[ci].lower_bound; 
      	     xi <= d->u.ddd.arc[ci].upper_bound; 
      	     xi++
      	     ) { 
      	  PX[VAR[d->var_index].PROC_INDEX] = add_index_count(
      	    PX[VAR[d->var_index].PROC_INDEX], xi, 
      	    &(PX_COUNT[VAR[d->var_index].PROC_INDEX]) 
      	  ); 
      	} 
      	rec_fillin_pxpairs(d->u.ddd.arc[ci].child);
      }
    }
    else for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_fillin_pxpairs(d->u.ddd.arc[ci].child);
    }
  }
}
/* rec_fillin_pxpairs() */


int	*pxi_buffer; 

void	red_fillin_pxpairs(int *pxcount, int **px) {
  int				pi, pos; 
  struct index_link_type	*il, *ilp; 
  
  if (pxcount == NULL || px == NULL) { 
    fprintf(RED_OUT, "\nERROR: illegal null array to pxcount and px.\n"); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  PX_COUNT = pxcount; 
  if (PX == NULL) { 
    PX = (struct index_link_type **) 
      malloc((PROCESS_COUNT + 1)* sizeof(struct index_link_type *)); 
    pxi_buffer = (int *) malloc(PROCESS_COUNT * XTION_COUNT * sizeof(int)); 
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    PX_COUNT[pi] = 0; 
    PX[pi] = NULL; 
  } 
  init_23tree(&redlib_pxpair_tree); 
  rec_fillin_pxpairs(redlib_sync_bulk_restriction); 
  free_entire_23tree(redlib_pxpair_tree, rec_free); 
  
  for (pos = 0, pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if (pxcount[pi]>0) { 
      px[pi] = &(pxi_buffer[pos]); 
      for (il = PX[pi]; 
           il; 
           pos++, ilp = il, il = il->next_index_link, free(ilp) 
           ) { 
      	pxi_buffer[pos] = il->index; 
      } 
      PX[pi] = NULL; 
    } 
    else 
      px[pi] = NULL; 
  } 
}
  /* red_fillin_pxpairs() */ 




struct red_type	*rec_check_pxpairs_roles(d)
     struct red_type	*d;
{
  int			xi, ci;
  struct rec_type	*nrec, *rec;

  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
      || d->var_index > variable_index[TYPE_XTION_INSTANCE][PROCESS_COUNT][0]
      )
    return; 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, redlib_pxpair_tree, 
    rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return; 
  }

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      rec_check_pxpairs_roles(d->u.crd.arc[ci].child);
    }
    break; 
  case TYPE_HRD: 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_check_pxpairs_roles(d->u.hrd.arc[ci].child);
    }
    break; 
  case TYPE_LAZY_EXP: 
    rec_check_pxpairs_roles(d->u.lazy.false_child);
    rec_check_pxpairs_roles(d->u.lazy.true_child);
    break; 
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE
        && (  PROCESS[VAR[d->var_index].PROC_INDEX].status 
            & redlib_restriction_roles
            )
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      	for (xi = d->u.ddd.arc[ci].lower_bound; 
      	     xi <= d->u.ddd.arc[ci].upper_bound; 
      	     xi++
      	     ) { 
      	  if (xi) 
      	    REDLIB_PXPAIR_LIST = add_index_pair(
      	      REDLIB_PXPAIR_LIST, VAR[d->var_index].PROC_INDEX, xi
      	    ); 
      	} 
      	rec_check_pxpairs_roles(d->u.ddd.arc[ci].child);
      }
    }
    else for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_check_pxpairs_roles(d->u.ddd.arc[ci].child);
    }
  }
}
/* rec_check_pxpairs_roles() */



int	red_first_pxpair_for_roles(int flag_game_roles) {
  int	ri; 
  
  if (flag_game_roles & ~RED_ALL_ROLES) { 
    fprintf(RED_OUT, 
      "Illegal game role specification %1d in red_begin_xi_for_roles().\n", 
      flag_game_roles
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  redlib_restriction_roles = redlib_roles_2_red_roles(flag_game_roles); 
  ri = flag_game_roles / RED_GAME_MODL; 
  REDLIB_PXPAIR_LIST = NULL; 
  init_23tree(&redlib_pxpair_tree); 
  rec_check_pxpairs_roles(redlib_sync_bulk_restriction); 
  free_entire_23tree(redlib_pxpair_tree, rec_free); 
  redlib_pxpair[ri] = REDLIB_PXPAIR_LIST; 
  redlib_pxpair_pos[ri] = redlib_pxpair[ri]; 
  if (redlib_pxpair[ri] == NULL) 
    return(TYPE_FALSE); 
  else 
    return(TYPE_TRUE); 
}
  /* red_first_pxpair_for_roles() */ 


int	red_next_pxpair_for_roles(int flag_game_roles) {
  int	ri; 
  
  if (flag_game_roles & ~RED_ALL_ROLES) { 
    fprintf(RED_OUT, 
      "Illegal game role specification %1d in red_begin_xi_for_roles().\n", 
      flag_game_roles
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  ri = flag_game_roles / RED_GAME_MODL; 
  if (redlib_pxpair_pos[ri]) { 
    redlib_pxpair_pos[ri] = redlib_pxpair_pos[ri]->next_index_pair_link; 
    if (redlib_pxpair_pos[ri]) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  } 
  else 
    return(TYPE_FALSE); 
}
  /* red_next_pxpair_for_roles() */ 


int	red_query_current_pi_for_roles(int flag_game_roles) {
  int	ri; 
  
  if (flag_game_roles & ~RED_ALL_ROLES) { 
    fprintf(RED_OUT, 
      "Illegal game role specification %1d in red_begin_xi_for_roles().\n", 
      flag_game_roles
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  ri = flag_game_roles / RED_GAME_MODL; 
  if (redlib_pxpair_pos[ri]) { 
    return(redlib_pxpair_pos[ri]->index1); 
  } 
  else 
    return(RED_FLAG_UNKNOWN); 
}
  /* red_query_current_pi_for_roles() */ 
  
  
int	red_query_current_xi_for_roles(int flag_game_roles) {
  int	ri; 
  
  if (flag_game_roles & ~RED_ALL_ROLES) { 
    fprintf(RED_OUT, 
      "Illegal game role specification %1d in red_begin_xi_for_roles().\n", 
      flag_game_roles
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  ri = flag_game_roles / RED_GAME_MODL; 
  if (redlib_pxpair_pos[ri]) { 
    return(redlib_pxpair_pos[ri]->index2); 
  } 
  else 
    return(RED_FLAG_UNKNOWN); 
}
  /* red_query_current_pi_for_roles() */ 




redgram	red_execute_sync_bulk_restriction(
  redgram 	dpath, 
  int		*last_time_progress_lb_ptr, 
  int		*last_time_progress_ub_ptr, 
  int		flag_game_roles,  
  int		flag_time_progress, 
  int		flag_normality, 
  int		flag_action_approx, 
  int		flag_reduction, 
  int		flag_state_approx, 
  int		flag_symmetry 
) { 
  int		t; 
  redgram	d; 
  
  if (FLAG_REDLIB_RESTRICTION_DIRECTION == FLAG_BCK_ANALYSIS) {
    fprintf(RED_OUT, "\nSorry, backward sync bulk restricted execution is not supported now.\n"); 
    exit(0); 
/*
    d = red_sync_xtion_given_bulk_bck( 
      redlib_sync_bulk_restriction, 
      dpath, 
      redlib_sync_bulk_restriction, 
      flag_game_roles,  
      RED_NO_TIME_PROGRESS, 
      flag_normality, 
      flag_action_approx, 
      flag_reduction, 
      flag_state_approx, 
      flag_symmetry
    );  
*/
  }
  else
    d = red_sync_xtion_given_bulk_fwd( 
      redlib_sync_bulk_restriction, 
      dpath, 
      redlib_sync_bulk_restriction, 
      RED_TASK_GOAL, 
      flag_game_roles,  
      RED_NO_TIME_PROGRESS, 
      flag_normality, 
      flag_action_approx, 
      flag_reduction, 
      flag_state_approx, 
      flag_symmetry, 
      0 // no experiment flags  
    ); 
  
  red_measure_last_time(d, 
    last_time_progress_lb_ptr, last_time_progress_ub_ptr
  );  

  d = red_measured_time_fwd(d, dpath); 

  return(d); 
}
  /* red_execute_sync_bulk_restriction() */  
















