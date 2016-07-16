/*
   RED version 7.0

   * why do we want to drop assignment of clocks to clocks ? 
   * The nondeterminacy created by concurrent assignments is difficult
   * to handle at this moment.   
   * Instead, we shall forbid the race condition on clocks.

-- Things to do for 23/07/02:

check the red_bypass used for consistency in

1. red_hull_inactive,
2. assignment,
	red_bypass_fwd(): array technology
3. saturate

 */

#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
#include <string.h> 
#include <float.h> 
#include <sys/time.h>
#include <sys/resource.h>
/*
#include <sys/wait.h>
#include <unistd.h>
*/
#include <math.h>

#include "redbasics.h" 

#include "redparse.h"
#include "redparse.e"

#include "redbop.h" /* hybrid.h, mtred.h & fmdd.h are included here. */ 
#include "redbop.e"
#include "hybrid.e"

#include "redgram.e" 

#include "vindex.e"

#include "fxp.h"
#include "fxp.e"

#include "counter.e"

#include "zone.h"  
#include "zone.e" 

#include "zapprox.e"

#include "exp.e" 

#include "bisim.h" 
#include "bisim.e" 

#include "redgame.h" 
#include "redgame.e" 

#include "treeman.h"
#include "treeman.e"

#include "hashman.h" 
#include "hashman.e" 

#include "redsymmetry.e"

#include "action.e"

#include "inactive.e"

extern char
  *red_query_mode_src_lines(int), 
  *red_query_xtion_src_lines(int); 
 
void	print_sync_xtion(int, struct sync_xtion_type *); 

int 	GSTATUS[GSTATUS_SIZE];
inline int	check_oapprox_lazy_exp() { 
  return(
     (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) == FLAG_ROOT_OAPPROX
  && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_DISCRETE) 
     == FLAG_OAPPROX_DISCRETE_LAZY
  ); 
}
  /* check_oapprox_lazy_exp() */ 

char	*TASK_TYPE_NAME;

#define GARBAGE_INITIAL_VALUES -2  

struct red_type	**RT, **RED_USER_STACK; // The two stack pointer 
                                        // are initialized to NULL 
                                        // in red_begin_session().  
int		RT_TOP = GARBAGE_INITIAL_VALUES, 
		RT_LIMIT = GARBAGE_INITIAL_VALUES, 
		RT_DYNAMIC = GARBAGE_INITIAL_VALUES, 
		USER_TOP = GARBAGE_INITIAL_VALUES, 
		USER_LIMIT = GARBAGE_INITIAL_VALUES;

#define	ERROR_CHECK		10000
#define REACHABLE_DIFFERENCE	30000


int	MASK_MARK, MASK_CLEAR; 

int			MEMORY_SIZE, 
			MEMORY_DISCRETE_SIZE, MEMORY_FLOAT_SIZE, 
			MEMORY_DOUBLE_SIZE, 
			MEMORY_START_VI, 
			DEPTH_CALL, HEIGHT_STACK_FRAME, STACK_START_OFFSET; 

int			MODE_COUNT; 
struct mode_type	*MODE; 

int			MODULE_COUNT; 
struct module_type	*MODULE; 

int			XTION_COUNT, REDUCTION_XTION_COUNT;
struct xtion_type	*XTION;

int			SYNC_XTION_COUNT, 
			DEPTH_ENUMERATIVE_SYNCHRONIZATION 
			= DEPTH_ENUMERATIVE_DEFAULT;
struct sync_xtion_type	*SYNC_XTION;
int			SYNC_XTION_COUNT_GAME;
struct sync_xtion_type	*SYNC_XTION_GAME;

struct ps_exp_type	*SPEC_EXP;

int			DEBUG_RED_COUNT, DISTANCE_ZENO;

float			cpu_time_parsing; 

struct red_type
  **RED_INVARIANCE,
  **DEBUG_RED,

  **FILTER_NOT_NONZERO_XTIVE_LEFT,
  **FILTER_NOT_NONZERO_XTIVE_RIGHT,
  ***FILTER_NOT_DIRECT_ZERO_EQUIVALENCE,
  ***FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE,
  ***FILTER_NEITHER_LAST_NOR_FIRST_ZERO_EQUIVALENCE,
  ***FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE,

  *FILTER_AI_FINAL,
  *FILTER_AI_INTER;

struct red_type	*RED_PLAIN_NONZENO, *RED_APPROX_NONZENO;


int	bug_flag1 = 0, bug_flag2, bug_flag3, bug_flag4;

int	ITERATE_PI, ITERATE_XI, ITERATE_SXI;


int			PROCESS_COUNT;
struct process_type	*PROCESS;


int			*CLOCK, **ZONE, ***variable_index;
struct sync_type	*GSYNC;


int	ITERATION_COUNT, 
	*GLOBAL_COUNT,
	*LOCAL_COUNT,
        CUR_VAR_COUNT,
	CLOCK_COUNT,
	CLOCK_INEQUALITY_COUNT,
	MAX_ATTACH_COUNT,
	MAX_SYNC_ACTION_COUNT,
	MAX_OP_CLOCK_COUNT,
	GLOBAL_DECLARE_COUNT, GLOBAL_SYSTEM_OVERHEAD_COUNT,
  	LOCAL_DECLARE_COUNT, LOCAL_SYSTEM_OVERHEAD_COUNT;

int	OFFSET_MODE, OFFSET__SP, OFFSET__RETMODE, 
	CLOCK_POS_INFINITY, CLOCK_NEG_INFINITY,
	ALL_CLOCK_TIMING_BOUND, 
	ALL_RATE_BOUND; 

struct dfs_stack_type	*DFS_STACK_TOP;


FILE	*RED_OUT, *tmp_out;

struct red_type	*tf1, *tf2, *tf3;


int			BUG_VI, BUG_UB, BUG_UB_NUMERATOR, BUG_UB_DENOMINATOR;
struct hrd_exp_type	*BUG_HRD_EXP;

struct trace_frame_type	*TRACE_FRAME_STACK;
int			TRACE_FRAME_COUNT;

char	*inbuf = NULL; 
int	inbuf_size = 0; 

int	CPLUG_IN_W, CPLUG_IN_PI; 

// Special variable indices 
int	VI_TIME, VI_PROB_DENSE; 

typedef	char	*charptr_type;


int	REDLIB_ARGC = 0; 
char	**REDLIB_ARGV = NULL; 


struct ps_exp_type	*exp_mode; 
int	count_tpsubve = 0; 

void	tpsubve(struct ps_exp_type *psub) { 
  fprintf(RED_OUT, "\ntpsubve %1d (%x): vs %x: es %x from old exp_mode %x\n", 
    ++count_tpsubve, 
    (unsigned int) psub, (unsigned int) psub->var_status, 
    (unsigned int) psub->exp_status, 
    (unsigned int) exp_mode
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
} 
  /* tpsubve() */ 




void 	red_register_arg(int argc, char **argv) { 
  int	i; 
  
  if (REDLIB_ARGV != NULL) { 	
    for (i = 0; i < REDLIB_ARGC; i++) { 
      free(REDLIB_ARGV[i]); 
    } 
    free(REDLIB_ARGV); 
  } 
  REDLIB_ARGC = argc; 
  REDLIB_ARGV = (char **) malloc(argc * sizeof(char *)); 
  for (i = 0; i < argc; i++) { 
    REDLIB_ARGV[i] = malloc(strlen(argv[i])+2);	
    sprintf(REDLIB_ARGV[i], "%s\0", argv[i]); 	
  }
}
  /* red_register_arg() */ 
  
  
int	red_argc() { 
  return (REDLIB_ARGC); 
} 
  /* red_argc() */ 
 
char	**red_argv() { 
  return (REDLIB_ARGV); 
}
  /* red_argv() */  



int	check_trace_xi[250] = {
-1, 
2,3,4,5,6,
7,8,1,16,17,
18,19,20,21,23,
24,25,26,27,28,
23,24,25,26,27,

// (25)
28,23,24,25,26,
27,28,22,29,30,
32,33,35,37,38,
43,44,45,35,36,
39,40,41,42,43,

// (50)
44,45,35,36,39,
40,41,42,43,44,
45,34,46,47,32,
33,35,36,39,40,
41,42,43,44,45,

// (75)
35,37,38,43,44,
45,35,36,39,40,
41,42,43,44,45,
34,46,47,32,33,
35,36,39,40,41,

// (100)
42,43,44,45,35,
36,39,40,41,42,
43,44,45,35,37,
38,43,44,45,34,
46,47,31,48,49,

// (125)
50,51,53,54,56,
78,79,80,55,60,
63,64,66,69,73,
75,66,69,73,75,
65,76,77,61,78,

// (150)
79,80,56,78,79,
80,55,60,63,64,
66,67,71,66,67,
71,65,76,77,59,
57,61,78,79,82,

// (175)
83,53,54,55,60,
56,78,79,80,56,
78,79,80,56,78,
79,80,63,64,66,
67,71,65,76,77,

// (200)
61,78,79,82,83,
52,84,85,86,87,
9,10,11,10,11,
10,12,13,10,11,
10,11,10,12,13,

// (225)
10,11,10,11,10,
12,14,15
}; 

int	check_trace_pi[250] = {
-1, 
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

// (100)
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

// (125)
1,1,1,1,5,
5,5,5,3,3,
3,3,3,3,3,
3,3,3,3,3,
3,3,3,3,3,

// (150)
3,3,4,4,4,
4,2,2,2,2,
2,2,2,2,2,
2,2,2,2,2,
2,2,2,2,1,

// (175)
1,1,1,2,2,
3,3,3,3,5,
5,5,5,4,4,
4,4,2,2,2,
2,2,2,2,2,

// (200)
2,2,2,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,
1,1,1,1,1,

// (225)
1,1,1,1,1,
1,1,1
}; 

int	check_trace(int ic, int sxi) {
  int	i; 
  
  for (i = 0; i < SYNC_XTION[sxi].party_count; i++) { 
    if (   check_trace_pi[ic] == SYNC_XTION[sxi].party[i].proc
        && check_trace_xi[ic] == SYNC_XTION[sxi].party[i].xtion
        ) 
      return(TYPE_TRUE); 
  }
  return(TYPE_FALSE); 
}
  /* check_trace() */ 
  
  
int	check_print_trace(int ic, int sxi, struct red_type *d) { 
  if (!check_trace(ic, sxi))
    return; 
  fprintf(RED_OUT, "==[IC:%1d, sxi = %1d]================\n", ic, sxi); 
  print_sync_xtion(sxi, SYNC_XTION); 
  fprintf(RED_OUT, "post condition: \n"); 
  red_print_graph(d); 
} 
  /* check_print_trace() */ 



/* This routine has the final say in option setting. 
 */ 
void	check_options() {
  /* rights announce */
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
    printf("\n");
    printf("+---------------------------------------------+\n");
    printf("| Region-Encoding Diagram Verification System |\n");
    printf("|                RED version 7.0              |\n");
    printf("| for timed systems and linear hybrid systems |\n");
    printf("+---------------------------------------------+\n");
    printf("Farn Wang at EE, National Taiwan University, Taiwan, ROC.\n");
    printf("farn@cc.ee.ntu.edu.tw; http://cc.ee.ntu.edu.tw/~val/\n");
    printf("\nVerifying file %s against file %s.\n", model_file_name, spec_file_name);
  }

  if (stdout != RED_OUT 
      && !(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)
      ) {
    fprintf(RED_OUT, "\n");
    fprintf(RED_OUT, "+---------------------------------------------+\n");
    fprintf(RED_OUT, "| Region-Encoding Diagram Verification System |\n");
    fprintf(RED_OUT, "|                RED version 7.0              |\n");
    fprintf(RED_OUT, "| for timed systems and linear hybrid systems |\n");
    fprintf(RED_OUT, "+---------------------------------------------+\n");
    fprintf(RED_OUT, "Farn Wang at EE, National Taiwan University, Taiwan, ROC.\n");
    fprintf(RED_OUT, "farn@cc.ee.ntu.edu.tw; http://cc.ee.ntu.edu.tw/~val/\n");
    fprintf(RED_OUT, "\nVerifying file %s against file %s.\n", 
      model_file_name, 
      spec_file_name
    );
  }

  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
    fprintf(RED_OUT, "\nOutput to %s in ", output_file_name);
    if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) {
      fprintf(RED_OUT, "BACKWARD analysis.\n");
    }
    else {
      fprintf(RED_OUT, "FORWARD analysis.\n");
    }
    switch(GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
    case FLAG_SYSTEM_TIMED:
      fprintf(RED_OUT, "\n** Timed Systems **\n");
      break;
    case FLAG_SYSTEM_HYBRID:
      fprintf(RED_OUT, "\n** Hybrid Systems **\n");
      break;
    case FLAG_SYSTEM_UNTIMED:
      fprintf(RED_OUT, "\n** Untimed Systems **\n");
      break;
    default:
      fprintf(RED_OUT, "\n** ??? Systems **\n");
      break;
    }
  } 
  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_SIMULATE:
    RED_OUT = stdout;
    output_file_name = "STDOUT";
    GSTATUS[INDEX_INFERENCE_DIRECTION] = GSTATUS[INDEX_INFERENCE_DIRECTION] & ~FLAG_BCK_ANALYSIS;
    GSTATUS[INDEX_MODAL_CLOCK] = GSTATUS[INDEX_MODAL_CLOCK] & ~FLAG_MODAL_CLOCK; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    break; 
  case TASK_RISK: 
  case TASK_DEADLOCK: 
  case TASK_GOAL: 
  case TASK_SAFETY: 
    GSTATUS[INDEX_MODAL_CLOCK] = GSTATUS[INDEX_MODAL_CLOCK] & ~FLAG_MODAL_CLOCK; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    break; 
  case TASK_ZENO: 
    GSTATUS[INDEX_MODAL_CLOCK] = GSTATUS[INDEX_MODAL_CLOCK] & ~FLAG_MODAL_CLOCK; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE)
    | FLAG_USE_PLAIN_NONZENO; 
    break; 
  case TASK_MODEL_CHECK: 
  
    break; 
  case TASK_BRANCHING_BISIM_CHECKING:
  case TASK_BRANCHING_SIM_CHECKING: 
    GSTATUS[INDEX_NORM_ZONE] = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
			     | FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_USE_PLAIN_NONZENO; 
    break; 
  }
  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
    if (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) {
      fprintf(RED_OUT, "\nSorry, task PARAMETRIC ANALYSIS nullified option COUNTER-EXAMPLE generation.\n");
      GSTATUS[INDEX_COUNTER_EXAMPLE] = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE;
    }
    else if (GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY) {
      fprintf(RED_OUT, "\nSorry, option FULL-REACHABILITY nullified option COUNTER-EXAMPLE generation.\n");
      GSTATUS[INDEX_COUNTER_EXAMPLE] = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE;
    }
    else if (!(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)) {
      fprintf(RED_OUT, "\nSorry, currently we do not support counter-example generation in forward analysis.\n");
      GSTATUS[INDEX_INFERENCE_DIRECTION] = (GSTATUS[INDEX_INFERENCE_DIRECTION] & ~FLAG_BCK_ANALYSIS) | FLAG_BCK_ANALYSIS;
    }
  }

  /*
  if (GSTATUS[ & FLAG_BCK_ANALYSIS)
    GSTATUS[ = GSTATUS[ & ~FLAG_SYNC_BULK_EXECUTION;
  */


  if (GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY) {
    fprintf(RED_OUT, "\nNote: it is the user's responbility to make sure that \n");
    fprintf(RED_OUT, "      the system is a symmetric system to get the verification \n");
    fprintf(RED_OUT, "      performance of symmetry reduction.\n");
    fprintf(RED_OUT, "      And it is the user's responbility to make sure that the \n");
    fprintf(RED_OUT, "      specification (risk condition) is symmetric to guarantee the\n");
    fprintf(RED_OUT, "      correctness of the answer.\n\n");
    if (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE) {
      fprintf(RED_OUT, "Sorry that we don't do coverage analysis with symmetry reduction.\n");
      GSTATUS[INDEX_COVERAGE] = GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE;
    }
  }


  if (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS)
    GSTATUS[INDEX_FULL_REACHABILITY] = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY;

  switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
          & MASK_DISCRETE_DENSE_INTERLEAVING
          ) { 
  case FLAG_DISCRETE_DENSE_BOTTOM: 
  case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING: 
  case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING: 
    break; 
  default: 
    GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING]
    = (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] & ~MASK_DISCRETE_DENSE_INTERLEAVING)
    | FLAG_DISCRETE_DENSE_FULL_INTERLEAVING;
    break; 
  } 

  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_HYBRID:
    /* The default variable ordering for hybrid systems. */
    // set up the default variable ordering. 
    switch (GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) { 
    case FLAG_HYBRID_ENCODING_NORMALIZED_STRING: 
    case FLAG_HYBRID_ENCODING_NORMALIZED_MAGNITUDES: 
    case FLAG_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS: 
      break; 
    default: 
      GSTATUS[INDEX_HYBRID_ENCODING]
      = (GSTATUS[INDEX_HYBRID_ENCODING] & ~MASK_HYBRID_ENCODING)
      | FLAG_HYBRID_ENCODING_NORMALIZED_MAGNITUDES;
      break; 
    } 
    break;
  case FLAG_SYSTEM_TIMED:
    /* The default variable ordering for dense-time systems. */
    // set up the default variable ordering. 
    break;
  case FLAG_SYSTEM_UNTIMED:
    /* The default variable ordering for dense-time systems. */
    GSTATUS[INDEX_MODAL_CLOCK] 
    = GSTATUS[INDEX_MODAL_CLOCK] & ~FLAG_MODAL_CLOCK; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    break;
  }
  
  if (DISTANCE_ZENO >= 0) 
    DISTANCE_ZENO = CLOCK_NEG_INFINITY; 
/*
  print_resources("after parsing");
*/
  fflush(RED_OUT);
}
  /* check_options() */



inline int	valid_mode_index(mi) { 
  return(mi >= 0 && mi < MODE_COUNT); 	
} 
  /* valid_mode_index() */  
  
  
#define	FLT_EXP_DOWN	22
#define	DBL_EXP_DOWN	51

int	status_initialize() { 
  int	i; 
  
  RED_OUT = stdout;
  /* Open the input and output files. */
  for (i = 0; i < 10; i++)
    GSTATUS[i] = 0;

  PROCESS_COUNT = -1; 
  
  GSTATUS[INDEX_INFERENCE_DIRECTION] 
  = GSTATUS[INDEX_INFERENCE_DIRECTION] | FLAG_BCK_ANALYSIS;
  GSTATUS[INDEX_SYNCHRONIZATION] 
  = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_NO_SYNCHRONIZERS;
  GSTATUS[INDEX_SYNCHRONIZATION] 
  = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_ALL_SYNC_XTIONS;
  GSTATUS[INDEX_MODAL_CLOCK] 
  = GSTATUS[INDEX_MODAL_CLOCK] & ~FLAG_MODAL_CLOCK;
  GSTATUS[INDEX_ZENO_CYCLE] 
  = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
  | FLAG_ZENO_CYCLE_OK;

  GSTATUS[INDEX_ACTION_APPROX] 
  = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
  | FLAG_NO_ACTION_APPROX;  
  GSTATUS[INDEX_REDUCTION_INACTIVE] 
  = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
  | FLAG_REDUCTION_INACTIVE;  
  GSTATUS[INDEX_XTION_INSTANCE] 
  = GSTATUS[INDEX_XTION_INSTANCE] & ~FLAG_XTION_INSTANCE_MAINTAIN; 
  
  GSTATUS[INDEX_SYSTEM_TYPE] 
  = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) 
  | FLAG_SYSTEM_UNTIMED;
  GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] & ~MASK_SPEC;  

  GSTATUS[INDEX_NORM_ZONE] 
  = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
  | FLAG_NORM_ZONE_CLOSURE_REDUCTION;

  GSTATUS[INDEX_NORM_HYBRID] 
  = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID) 
  | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD 
/*
    | MASK2_HYBRID_PROOF_OBLIGATIONS
    | MASK2_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD
    | MASK2_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD
    | MASK2_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD
*/; 
  GSTATUS[INDEXX_HYBRID_ORDERING] 
  = (GSTATUS[INDEXX_HYBRID_ORDERING] & ~MASKK_HYBRID_ORDERING);  
//  | FLAG_HYBRID_DISCRETE_DENSE_FULL_INTERLEAVING; 
  GSTATUS[INDEX_HYBRID_ENCODING] 
  = (GSTATUS[INDEX_HYBRID_ENCODING] & ~MASK_HYBRID_ENCODING);  
//  | FLAG_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS; 
  GSTATUS[INDEX_HYBRID_STRATEGY]
  = GSTATUS[INDEX_HYBRID_STRATEGY]
  | FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING; 

  GSTATUS[INDEX_REDUCTION_INACTIVE]
  = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
  | FLAG_REDUCTION_INACTIVE;  

  GSTATUS[INDEX_TIME_PROGRESS] 
  = GSTATUS[INDEX_TIME_PROGRESS]
  | FLAG_TIME_PROGRESS 
  | FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED 
  | FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS
//  | FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES; 
//  | FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES; 
  | FLAG_TIME_PROGRESS_FULL_FORMULATION; 

  GSTATUS[INDEX_ACTION_APPROX]
  =(GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX)
  | FLAG_NO_ACTION_APPROX; 
    
  // the option of the variable ordering, 
  // if not set with the command-line options, 
  // then it will have to be set by default value in 
  // vindex_init_management() in redparse.c. 

  GSTATUS[INDEX_GFP] = GSTATUS[INDEX_GFP] 
  | FLAG_IN_GFP_EASY_STRONG_FAIRNESS; 

  GSTATUS[INDEX_FLOATING_DISPLAY] 
  = (GSTATUS[INDEX_FLOATING_DISPLAY] & ~MASK_FLOATING_DISPLAY_FORMAT)
  | FLAG_FLOATING_DISPLAY_SHORTEST; 
  
  model_file_name = "STDIN"; 
  spec_file_name = "STDIN"; 
  output_file_name = "STDOUT"; 

  DISTANCE_ZENO = 0; 
  
} 
  /* status_initialize() */ 
  
  
int	process_command_line(argc, argv) 
	int	argc; 
	char	**argv; 
{ 
  int	i, j, k, file_count, value; 
  
  status_initialize(); 
  
  for (file_count = 0, i = 1; i < argc; i++)
    if (argv[i][0] != '-') {
      switch (file_count) {
      case 0: 
        model_file_name = argv[i]; 
        break; 
      case 1: 
        spec_file_name = argv[i]; 
        break; 
      case 2: 
        output_file_name = argv[i]; 
        RED_OUT = fopen(argv[i], "w");
        break; 
      } 
      file_count++;
    }
    else {
      for (j = 1; j < strlen(argv[i]); j++)
	switch (argv[i][j]) {
	case '?': 
	  
	  exit(0); 
	case '0':
	  GSTATUS[INDEX_INITIAL_ZERO] = GSTATUS[INDEX_INITIAL_ZERO] | FLAG_INITIAL_ZERO;
	  break;
	case 'A':
	  switch (argv[i][++j]) { 
	  case 'o': 
	    GSTATUS[INDEX_APPROX] 
	    = (GSTATUS[INDEX_APPROX] & ~MASK_ROOT_POLARITY)
	     | FLAG_ROOT_OAPPROX;
	    break; 
	  case 'u': /* underapproximation */ 
	    GSTATUS[INDEX_APPROX] 
	    = (GSTATUS[INDEX_APPROX] & ~MASK_ROOT_POLARITY)
	     | FLAG_ROOT_UAPPROX;
	    break; 
	  } 
	  break;
	  
	case 'c':
	  GSTATUS[INDEX_COUNTER_EXAMPLE] = GSTATUS[INDEX_COUNTER_EXAMPLE] 
					 | FLAG_COUNTER_EXAMPLE;
	  break;
	case 'C': /* coverage estimation */ 
	  switch (argv[i][++j]) {
	  case 'r': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_REGION_COVERAGE;
	    break; 
	  case 't': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_TRIGGER_COVERAGE;
	    break; 
	  case 'R': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_DISCRETE_COVERAGE;
	    break; 
	  case 'T': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_DISCRETE_TRIGGER_COVERAGE;
	    break; 
	  case 'a': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_ARC_COVERAGE;
	    break; 
	  case '*': 
	    GSTATUS[INDEX_COVERAGE] = (GSTATUS[INDEX_COVERAGE] & ~MASK_COVERAGE) | FLAG_ALL_COVERAGE;
	    break; 
	  } 
	  break;
	case 'D':
	  switch (argv[i][++j]) { 
	  case 'g':
	    GSTATUS[INDEX_DEBUG] 
	    = (GSTATUS[INDEX_DEBUG] & ~MASK_DEBUG) | FLAG_DEBUG_GOAL;
	    TRACE_FRAME_STACK = NULL;
	    TRACE_FRAME_COUNT = 0;
	    break; 
	  case 'i':
	    GSTATUS[INDEX_DEBUG] 
	    = GSTATUS[INDEX_DEBUG] | FLAG_DEBUG_INITIAL;
	    break; 
	  case 's': 
	    GSTATUS[INDEX_DEBUG] 
	    = GSTATUS[INDEX_DEBUG] | FLAG_DEBUG_INITIAL_STOP;
	    break; 	  
	  case 't': 
	    GSTATUS[INDEX_DEBUG] 
	    = (GSTATUS[INDEX_DEBUG] & ~MASK_DEBUG) | FLAG_DEBUG_TRACE;
	    TRACE_FRAME_STACK = NULL;
	    TRACE_FRAME_COUNT = 0;
	    break; 
	  case 'x':
	    GSTATUS[INDEX_TASK] 
	    = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_DEADLOCK;
	    TASK_TYPE_NAME = "deadlock";
	    break; 
	  case 'z': 
	    GSTATUS[INDEX_TASK] 
	    = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_ZENO;
	    TASK_TYPE_NAME = "zeno";
	    break; 
	  }
	  break;
	case 'E':
	  for (k = j+1; argv[i][k] >= '0' && argv[i][k] <= '9'; k++) {
	    argv[i][k-1] = argv[i][k];
	  }
          argv[i][k-1] = '\0';
          DEPTH_ENUMERATIVE_SYNCHRONIZATION = atoi(&(argv[i][j]));
          j = k;
	  break;
	case 'e': /* early exit */ 
	  switch (argv[i][++j]) { 
	  case 'a':  
	    GSTATUS[INDEX_EXIT] 
	    = (GSTATUS[INDEX_EXIT] & ~MASK_EXIT) | FLAG_EXIT_AFTER_QUOTIENT; 
	    break; 
	  case 'p': 
	    GSTATUS[INDEX_EXIT] 
	    = (GSTATUS[INDEX_EXIT] & ~MASK_EXIT) | FLAG_EXIT_AFTER_PARSING;
	    break; 
	  case 's': 
	    GSTATUS[INDEX_EXIT] 
	    = (GSTATUS[INDEX_EXIT] & ~MASK_EXIT) | FLAG_EXIT_AFTER_SYNC_XTION_COUNTING;
	    break; 
	  } 
	  break;
	  	  
	case 'f':
	  GSTATUS[INDEX_INFERENCE_DIRECTION] = GSTATUS[INDEX_INFERENCE_DIRECTION] & ~FLAG_BCK_ANALYSIS;
	  break;

/*
	case 'F':
	  switch (argv[i][++j]) {
	  case 's': 
	    GSTATUS[INDEX_FAIRNESS] 
	    = (GSTATUS[INDEX_FAIRNESS] & ~MASK_FAIRNESS)
	    | FLAG_FAIRNESS_SEQUENTIAL; 
	    break; 
	  case 'l': 
	    GSTATUS[INDEX_FAIRNESS] 
	    = (GSTATUS[INDEX_FAIRNESS] & ~MASK_FAIRNESS) 
	    | FLAG_FAIRNESS_LOG; 
	    break; 
	  } 
	  break;
*/

	case 'G': /* for greatest fixpoint evaluation. */ 
	  switch (argv[i][++j]) { 
	  case 'e': /* for option early decision */
	    GSTATUS[INDEX_GFP_NO_EARLY_DECISION]
	    = GSTATUS[INDEX_GFP_NO_EARLY_DECISION] & ~FLAG_GFP_NO_EARLY_DECISION;
	    break; 
	  case 'f':
	    GSTATUS[INDEX_GFP_NO_EARLY_DECISION]
	    = GSTATUS[INDEX_GFP_NO_EARLY_DECISION] | FLAG_GFP_NO_EARLY_DECISION;
	    break; 
	  case 's': 
	    GSTATUS[INDEX_GFP] 
	    = GSTATUS[INDEX_GFP] | FLAG_GFP_FORCED_LONG_DEST_WITH_UAPPROX; 
	    break; 
	  case 'z': 
	    for (k = j+1; argv[i][k] >= '0' && argv[i][k] <= '9'; k++) {
              argv[i][k-1] = argv[i][k];
            }
            argv[i][k-1] = '\0';
            DISTANCE_ZENO = -2*atoi(&(argv[i][j]));
            j = k; 
	  }
	  break; 
	case 'H':
/*
#define	MASK2_HYBRID_STRATEGY					(0xFFC00)
#define	MASK2_HYBRID_STRATEGY_PARAMETER_PRUNING			(0x400)
#define MASK2_HYBRID_DOUBLE_REDUNDANCY_ELIMINATION_DOWNWARD	(0x800)
#define MASK2_HYBRID_REDUNDANCY_ELIMINATION_LOOKAHEAD		(0x1000)
*/
	  switch (argv[i][++j]) {
	  case '2': 
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case '3': 
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    | FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case '4': 
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    | FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case 'l': 
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    | FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD;
	    break;
	  case 'o': 
	    GSTATUS[INDEX_HYBRID_STRATEGY]
	    = GSTATUS[INDEX_HYBRID_STRATEGY] 
	    | FLAG_NORM_HYBRID_PROOF_OBLIGATIONS;
	    break;
	  case 'p':
	    GSTATUS[INDEX_HYBRID_STRATEGY]
	    = GSTATUS[INDEX_HYBRID_STRATEGY] 
	    | FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING;
	    break;
	  case 'r':
	    GSTATUS[INDEX_HYBRID_STRATEGY]
	    = GSTATUS[INDEX_HYBRID_STRATEGY] 
	    | FLAG_HYBRID_REACHABLE_COMPLEMENT;
	    break;
	  }
	  break;
	case 'I': /* The reduction Inhibiting option */ 
/*
#define	MASK2_HYBRID_STRATEGY					(0xFFC00)
#define	MASK2_HYBRID_STRATEGY_PARAMETER_PRUNING			(0x400)
#define MASK2_HYBRID_DOUBLE_REDUNDANCY_ELIMINATION_DOWNWARD	(0x800)
#define MASK2_HYBRID_REDUNDANCY_ELIMINATION_LOOKAHEAD		(0x1000)
*/
	  switch (argv[i][++j]) {
	  case '2':
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    & ~FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case '3':
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    & ~FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case '4':
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    & ~FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case 'l':
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    & ~FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD;
	    break;
	  case 'o':
	    GSTATUS[INDEX_NORM_HYBRID]
	    = GSTATUS[INDEX_NORM_HYBRID] 
	    & ~FLAG_NORM_HYBRID_PROOF_OBLIGATIONS;
	    break;
/*
	  case 'a':
	    GSTATUS[INDEX_REDUCTION]
	    = GSTATUS[INDEX_REDUCTION] & ~FLAG_ACTIVE_CHECKING;
	    break;
*/
	  case 'c': /* inhibiting the clock-shielding option */ 
	  
	    break; 
	  case 'p':
	    GSTATUS[INDEX_HYBRID_STRATEGY]
	    = GSTATUS[INDEX_HYBRID_STRATEGY] & ~FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING;
	    break;
	  case 'r':
	    GSTATUS[INDEX_HYBRID_STRATEGY]
	    = GSTATUS[INDEX_HYBRID_STRATEGY] & ~FLAG_HYBRID_REACHABLE_COMPLEMENT;
	    break; 
	  }
	  break;
	case 'm': // For the number of processes to override the one in the 
		  // the template. 
	  for (k = j+1; argv[i][k] >= '0' && argv[i][k] <= '9'; k++) {
	    argv[i][k-1] = argv[i][k];
	  }
          argv[i][k-1] = '\0';
          PROCESS_COUNT = atoi(&(argv[i][j]));
          j = k;   	
          GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
          = GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
          | FLAG_TEMPLATE_PROCESS_COUNT_OVERRIDDEN; 
	  break; 
	case 'N':
	  switch (argv[i][++j]) {
	  case '2':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_2REDUNDANCY_ELIMINATION_DOWNWARD;
	    break;
	  case 't':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE;
	    break;
	  case 'r':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_REDUCED;
	    break;
	  case 'm':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_MAGNITUDE;
	    break;
	  case 'n':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_MAGNITUDE_WITH_NO_TABLE_LOOKUP;
	    break;
	  case 'c':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_CLOSURE;
	    break;
	  case 'y':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_CLOSURE_EQ;
	    break;
	  case 'w':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_CLOSURE_REDUCTION;
	    break;
	  case 'p':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_CLOSURE_PROPAGATE;
	    break;
	  case 'z':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_NONE;
	    break;
	  case 'o':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP;
	    break;
	  case 'v':
	    GSTATUS[INDEX_NORM_ZONE] 
	    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
	    | FLAG_NORM_ZONE_MAGNITUDE_REDUCTION;
	    break; 
	  }
	  break;
	case 'O':
	  switch (argv[i][++j]) {
	  case 'b':
	    GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING]
	    = (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
	       & ~MASK_DISCRETE_DENSE_INTERLEAVING
	       )
	    | FLAG_DISCRETE_DENSE_BOTTOM;
	    break;
	  case 'h':
	    GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING]
	    = (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
	       & ~MASK_DISCRETE_DENSE_INTERLEAVING
	       )
	    | FLAG_DISCRETE_DENSE_HALF_INTERLEAVING;
	    break;
	  case 'f':
	    GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING]
	    = (  GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
	       & ~MASK_DISCRETE_DENSE_INTERLEAVING
	       )
	    | FLAG_DISCRETE_DENSE_FULL_INTERLEAVING;
	    break;
/*
#define	MASK2_HYBRID_ENCODING				(32+64+128+256+512)
#define MASK2_DENSE_ENCODING				(32+128+256+512)
#define MASK2_HYBRID_DISCRETE_DENSE_INTERLEAVING	(32+64)
#define	MASK2_HYBRID_ENCODING_NORMALIZED_STRING		(32+128)
#define	MASK2_HYBRID_ENCODING_NORMALIZED_MAGNITUDES	(32+256)
#define	MASK2_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS	(32+128+256)
*/
	  case 's':
	    GSTATUS[INDEX_HYBRID_ENCODING]
	    = (GSTATUS[INDEX_HYBRID_ENCODING] & ~MASK_HYBRID_ENCODING)
	    | FLAG_HYBRID_ENCODING_NORMALIZED_STRING;
	    break;
	  case 'm':
	    GSTATUS[INDEX_HYBRID_ENCODING]
	    = (GSTATUS[INDEX_HYBRID_ENCODING] & ~MASK_HYBRID_ENCODING)
	    | FLAG_HYBRID_ENCODING_NORMALIZED_MAGNITUDES;
	    break;
	  case 'c':
	    GSTATUS[INDEX_HYBRID_ENCODING]
	    = (GSTATUS[INDEX_HYBRID_ENCODING] & ~MASK_HYBRID_ENCODING)
	    | FLAG_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS;
	    break;
	  }
	  break;
	case 'P': /* SEARCH priority */
	  if (argv[i][++j] == 'd') {
	    GSTATUS[INDEX_SEARCH] 
	    = (GSTATUS[INDEX_SEARCH] & ~MASK_SEARCH) 
	    | FLAG_FIRST_DEPTH;
	  }
	  else if (argv[i][j] == 'g') {
	    GSTATUS[INDEX_SEARCH] 
	    = (GSTATUS[INDEX_SEARCH] & ~MASK_SEARCH) 
	    | FLAG_FIRST_MODE_DISTANCE;
	  }
	  else if (argv[i][j] == 'b') /* the default is breadth first */ {
	    GSTATUS[INDEX_SEARCH] 
	    = GSTATUS[INDEX_SEARCH] & ~MASK_SEARCH;
	  }
	  break; 
	  
	case 'r':
	  GSTATUS[INDEX_FULL_REACHABILITY] = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY;
	  break;
	case 'R': /* Abstraction scheme in representations. */ 
	  switch (argv[i][++j]) { 
	  case 'g': /* an overapproximation */ 
	    break; 
	  case 'd': /* an overapproximation */ 
	    break; 
	  case 't': /* an overapproximation */ 
	    break; 
	  case 'm': /* an overapproximation */ 
	    break;
	  }  
	  break;
	case 's':
	  GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SIMULATE;
	  break;
	case 'S':
	  if (argv[i][++j] == 'z')
	    GSTATUS[INDEX_SYMMETRY] 
	    = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY) | FLAG_SYMMETRY_ZONE;
	  else if (argv[i][j] == 'd')
	    GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY) 
				    | FLAG_SYMMETRY_DISCRETE_GENERAL;
	  else if (argv[i][j] == 'p') {
	    switch (argv[i][++j]) {
	    case '1':
	      GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
				      | FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE;
	      break;
	    case 'n':
	      GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
				      | FLAG_SYMMETRY_POINTER_FIXPOINT_ONLINE;
	      break;
	    case 'f':
	      GSTATUS[INDEX_SYMMETRY] = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY)
				      | FLAG_SYMMETRY_POINTER_FIXPOINT_OFFLINE;
	      break;
	    default:
	      j--;
	    }
	  }
	  else if (argv[i][j] == 's')
	    GSTATUS[INDEX_SYMMETRY] 
	    = (GSTATUS[INDEX_SYMMETRY] & ~MASK_SYMMETRY) | FLAG_SYMMETRY_STATE;
	  else {
	    fprintf(RED_OUT, "\nCommand-line error: unrecognized symmetry option 'S%c'\n", argv[i][j]);
	    fflush(RED_OUT);
	    exit(0);
	  }
	  break;
	  
	case 'W': 
	  switch (argv[i][++j]) {
	  case 'g': 
	    for (k = j+1; argv[i][k] >= '0' && argv[i][k] <= '9'; k++) {
	      argv[i][k-1] = argv[i][k];
	    }
            argv[i][k-1] = '\0';
            value = atoi(&(argv[i][j]));
            if (value <= 0 || value > 255) { 
              fprintf(RED_OUT, "Error: out-of-range bound %1d for progression estimation.\n", 
		      value
		      ); 
	      exit(0); 	
            } 
            j = k;   	
            GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
            = (GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
            & ~MASK_REACHABILITY_DEPTH_BOUND) 
            | FLAG_REACHABILITY_DEPTH_BOUND
            | value; 
	    break; 
	  case 'm':
	    GSTATUS[INDEX_PRINT] = GSTATUS[INDEX_PRINT] | FLAG_PRINT_MEMORY;
	    break;
	  case 'p':
	    GSTATUS[INDEX_PRINT] = GSTATUS[INDEX_PRINT] | FLAG_PRINT_POSTPROCESSING;
	    break;
	  case 'r':
	    GSTATUS[INDEX_PRINT] = GSTATUS[INDEX_PRINT] | FLAG_PRINT_RED_INTERMEDIATE; 
	    break; 
	  case 't':
	    GSTATUS[INDEX_PRINT] = GSTATUS[INDEX_PRINT] | FLAG_PRINT_TIME;
	    break;
	  }
	  break;
	case 'Z':
	  GSTATUS[INDEX_ZENO_CYCLE] 
	  = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
	  | FLAG_USE_PLAIN_NONZENO;
	  break;
        default:
	  fprintf(RED_OUT, "\nCommand-line error: unrecognized option '%c'\n", argv[i][j]);
	  fflush(RED_OUT);
	  exit(0);
	}
    }

  return(file_count); 
}
  /* process_command_line() */ 
  



struct name_link_type	*push_name_stack(
  char			*n, 
  struct name_link_type	*nstack 
) { 
  struct name_link_type	*nl; 
  
  nl = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
  nl->next_name_link = nstack; 
  nl->name = n; 
  return(nl);  
} 
  /* push_name_stack() */ 


struct name_link_type *pop_name_stack(
  struct name_link_type	*nstack 
) { 
  struct name_link_type	*nl; 
  
  if (nstack == NULL) 
    return(NULL); 
  
  nl = nstack; 
  nstack = nstack->next_name_link; 
  free(nl); 
  return(nstack); 	
} 
  /* pop_name_stack() */ 



int	check_name_list(
  char			*n, 
  struct name_link_type	*nl
) {
  for (; nl; nl = nl->next_name_link) 
    if (!strcmp(n, nl->name))
      return(TYPE_TRUE); 
  
  return(TYPE_FALSE); 
}
  /* check_file_name_stack() */ 

 



void	print_name_list(struct name_link_type *nl) { 
  fprintf(RED_OUT, "\nName list:"); 
  for (; nl; nl = nl->next_name_link) { 
    fprintf(RED_OUT, " '%s'", nl->name); 	
  } 
  fprintf(RED_OUT, "\n"); 
}
  /* print_name_list() */ 



struct name_link_type	*insert_name_cycle(
  struct name_link_type	*cycle, 
  char			*name, 
  int			*cptr
) { 
  int			l, i; 
  struct name_link_type	*nl; 

  l = strlen(name); 
  nl = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
  nl->name = malloc(l+1); 
  for (i = 0; i < l; i++) 
    nl->name[i] = name[i]; 
  nl->name[i] = '\0'; 
  if (cycle == NULL) { 
    *cptr = 1; 
    nl->next_name_link = nl; 
    return(nl); 	
  } 
  else { 
    (*cptr)++; 
    nl->next_name_link = cycle->next_name_link; 
    cycle->next_name_link = nl; 
    cycle = nl; 
    return(nl); 
  } 
}
  /* insert_name_cycle() */ 




char	*combine_name_cycle(
  struct name_link_type	**cycle_ptr, 
  int			*cptr
) { 
  int			l, i; 
  struct name_link_type	*nl, *cycle; 
  char			*b; 
  
  if (*cptr == 0) 
    return(NULL); 
  l = 1; 
  cycle = *cycle_ptr; 
  for (i = 0, nl = cycle->next_name_link; 
       i < *cptr; 
       i++, nl = nl->next_name_link
       ) { 
    l = l + strlen(nl->name); 
  } 
  b = malloc(l); 
  i = 0; 
  nl = cycle; 
  cycle = cycle->next_name_link; 
  nl->next_name_link = NULL; 
  for (; cycle; nl = cycle, cycle = cycle->next_name_link, free(nl)) { 
    sprintf(&(b[i]), "%s", cycle->name); 
    i = i + strlen(cycle->name); 
    free(cycle->name); 
  }
  b[i] = '\0'; 
  
  *cptr = 0; 
  *cycle_ptr = NULL; 
  
  return(b); 
}
  /* combine_name_cycle() */






inline int	arith_operation(
  int	op, 
  int	lhs, 
  int	rhs
) {
  switch (op) { 
  case ARITH_ADD: 
    return(lhs + rhs); 
  case ARITH_MINUS: 
    return(lhs - rhs); 
  case ARITH_MULTIPLY: 
    return(lhs * rhs); 
  case ARITH_DIVIDE: 
    return(lhs / rhs); 
  case ARITH_MODULO: 
    return(lhs % rhs); 
  case ARITH_EQ: 
    if (lhs == rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_NEQ: 
    if (lhs != rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_LESS: 
    if (lhs < rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_LEQ: 
    if (lhs <= rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_GEQ: 
    if (lhs >= rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_GREATER: 
    if (lhs > rhs) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  } 
}
  /* arith_operation() */  





struct index_link_type	*add_index(list, i)
     struct index_link_type	*list;
     int			i; 
{
  struct index_link_type	*ip, *nip; 

  if (list == NULL || list->index > i) { 
    nip = (struct index_link_type *) malloc(sizeof(struct index_link_type));
    nip->index = i; 
    nip->next_index_link = list; 
    return(nip);  
  }
  else if (list->index == i)
    return(list); 
  else { 
    for (ip = list;
	 ip->next_index_link != NULL && ip->next_index_link->index < i; 
	 ip = ip->next_index_link
	 ); 

    if (ip->next_index_link == NULL || ip->next_index_link->index > i) { 
      nip = (struct index_link_type *) malloc(sizeof(struct index_link_type));
      nip->index = i; 
      nip->next_index_link = ip->next_index_link; 
      ip->next_index_link = nip; 
    }
    return(list); 
  }
}
/* add_index() */ 



struct index_link_type	*add_index_count(list, i, icp)
     struct index_link_type	*list; 
     int			i, *icp; 
{
  struct index_link_type	*ip, *nip; 

  if (list == NULL || list->index > i) {
    nip = (struct index_link_type *) malloc(sizeof(struct index_link_type)); 
    nip->index = i; 
    nip->next_index_link = list;
    (*icp)++; 
    return(nip);  
  }
  else if (list->index == i) 
    return(list); 
  else {
    for (ip = list; 
	 ip->next_index_link != NULL && ip->next_index_link->index < i; 
	 ip = ip->next_index_link
	 ); 

    if (ip->next_index_link == NULL || ip->next_index_link->index > i) {
      nip = (struct index_link_type *) malloc(sizeof(struct index_link_type)); 
      nip->index = i; 
      nip->next_index_link = ip->next_index_link; 
      ip->next_index_link = nip; 
      (*icp)++; 
    }
    return(list); 
  }
}
/* add_index_count() */ 


struct index_link_type	*remove_index_head(
  struct index_link_type	*list
) { 
  if (list) { 
    struct index_link_type	*tail; 
    
    tail = list->next_index_link; 
    free(list); 
    return (tail); 	
  } 
  return(NULL); 
} 
  /* remove_index_head() */ 



free_index_list(list) 
     struct index_link_type	*list; 
{
  struct index_link_type	*ip, *nip; 

  for (ip = list; ip; ) {
    nip = ip;
    ip = ip->next_index_link; 
    free(nip); 
  }
}
/* free_index_list() */ 


void 	print_index_list(list) 
  struct index_link_type	*list; 
{
  struct index_link_type	*ip; 
  int				count; 

  count = 0; 
  if (list) { 
    fprintf(RED_OUT, "\n%1d", list->index); 
    count++; 
    for (list = list->next_index_link; list; list = list->next_index_link) {
      fprintf(RED_OUT, ", %1d", list->index);  
    }
  } 
  fprintf(RED_OUT, "\n%1d indices in the list.\n", count); 
}
/* print_index_list() */ 


struct index_pair_link_type	*add_index_pair(list, i1, i2)
     struct index_pair_link_type	*list;
     int				i1, i2; 
{
  struct index_pair_link_type	*ip, *nip, dummy_ip, *pip; 

  dummy_ip.next_index_pair_link = list; 
  pip = &dummy_ip; 
  for (pip = &dummy_ip, ip = list; 
       ip && (ip->index1 < i1 || (ip->index1 == i1 && ip->index2 < i2));
       pip = ip, ip = pip->next_index_pair_link
       ) ; 
       
  if ((!ip) || ip->index1 > i1 || (ip->index1 == i1 && ip->index2 > i2)) { 
    nip = (struct index_pair_link_type *) malloc(sizeof(struct index_pair_link_type));
    nip->index1 = i1; 
    nip->index2 = i2; 
    nip->next_index_pair_link = ip; 
    pip->next_index_pair_link = nip; 
  }
  return(dummy_ip.next_index_pair_link); 
}
/* add_index_pair() */ 





free_index_pair_list(list) 
     struct index_pair_link_type	*list; 
{
  struct index_pair_link_type	*ip, *nip; 

  for (ip = list; ip; ) {
    nip = ip;
    ip = ip->next_index_pair_link; 
    free(nip); 
  }
}
/* free_index_pair_list() */ 



struct index_triple_link_type	*add_index_triple(list, i1, i2, i3)
     struct index_triple_link_type	*list;
     int				i1, i2, i3; 
{
  struct index_triple_link_type	*ip, *nip, dummy_ip, *pip; 

  dummy_ip.next_index_triple_link = list; 
  pip = &dummy_ip; 
  for (pip = &dummy_ip, ip = list; 
          ip 
       && (   ip->index1 < i1 
           || (   ip->index1 == i1 
               && (   ip->index2 < i2
                   || (   ip->index2 == i2 
                       && ip->index3 < i3
                       )
                   )
               )
           );
       pip = ip, ip = pip->next_index_triple_link
       ) ; 
       
  if (   (!ip) 
      || ip->index1 > i1 
      || (ip->index1 == i1 && ip->index2 > i2)
      || (ip->index1 == i1 && ip->index2 == i2 && ip->index3 > i3)
      ) { 
    nip = (struct index_triple_link_type *) 
      malloc(sizeof(struct index_triple_link_type));
    nip->index1 = i1; 
    nip->index2 = i2; 
    nip->index3 = i3; 
    nip->next_index_triple_link = ip; 
    pip->next_index_triple_link = nip; 
  }
  return(dummy_ip.next_index_triple_link); 
}
/* add_index_triple() */ 





free_index_triple_list(list) 
     struct index_triple_link_type	*list; 
{
  struct index_triple_link_type	*ip, *nip; 

  for (ip = list; ip; ) {
    nip = ip;
    ip = ip->next_index_triple_link; 
    free(nip); 
  }
}
/* free_index_triple_list() */ 




struct indexed_structure_link_type	*add_indexed_structure_count
					(list, i, structure, icp)
     struct indexed_structure_link_type	*list; 
     int				i, *icp; 
     char				*structure; 
{
  struct indexed_structure_link_type	*ip, *nip; 

  if (list == NULL || list->index > i) {
    nip = (struct indexed_structure_link_type *) 
	malloc(sizeof(struct indexed_structure_link_type)); 
    nip->index = i; 
    nip->structure = structure; 
    nip->next_indexed_structure_link = list;
    (*icp)++; 
    return(nip);  
  }
  else if (list->index == i) 
    return(list); 
  else {
    for (ip = list; 
	 ip->next_indexed_structure_link != NULL && ip->next_indexed_structure_link->index < i; 
	 ip = ip->next_indexed_structure_link
	 ); 

    if (ip->next_indexed_structure_link == NULL || ip->next_indexed_structure_link->index > i) {
      nip = (struct indexed_structure_link_type *) malloc(sizeof(struct indexed_structure_link_type)); 
      nip->index = i; 
      nip->structure = structure; 
      nip->next_indexed_structure_link = ip->next_indexed_structure_link; 
      ip->next_indexed_structure_link = nip; 
      (*icp)++; 
    }
    return(list); 
  }
}
/* add_indexed_structure_count() */ 



free_indexed_structure_list(list) 
     struct indexed_structure_link_type	*list; 
{
  struct indexed_structure_link_type	*ip, *nip; 

  for (ip = list; ip; ) {
    nip = ip;
    ip = ip->next_indexed_structure_link; 
    free(nip); 
  }
}
/* free_indexed_structure_list() */ 




struct red_link_type	*add_red_tail(
  struct red_link_type	*tail, 
  struct red_type 	*d
) { 
  struct red_link_type	*rl; 
  
  rl = (struct red_link_type *) malloc(sizeof(struct red_link_type)); 
  rl->result = d; 
  tail->next_red_link = rl; 
  rl->next_red_link = NULL; 
  
  return(rl); 
} 
  /* add_red_tail() */ 




void	free_red_list(struct red_link_type *list) { 
  struct red_link_type	*rl; 
  
  for (; list; ) { 
    rl = list; 
    list = list->next_red_link; 
    free(rl); 	
  }   
} 
  /* free_red_list() */ 
  
  


void	print_red_list(struct red_link_type *list) { 
  int			i; 
  struct red_link_type	*ol; 
  
  for (i = 0, ol = list; ol; ol = ol->next_red_link, i++); 
  
  fprintf(RED_OUT, "\n==[A list of %1d diagrams]======\n", i); 
  for (i = 1; list; list = list->next_red_link, i++) { 
    fprintf(RED_OUT, "--[Diagram %1d]---\n", i); 
    red_print_graph(list->result); 	
  } 
  fprintf(RED_OUT, "\n"); 
} 
  /* print_red_list() */ 
  
  





/*******************************************************
*/
void	print_op(op) 
	int 	op; 
{
  switch (op) {
  case LESS: 
  case ARITH_LESS: 
    fprintf(RED_OUT, "<"); 
    break;
  case LEQ: 
  case ARITH_LEQ: 
    fprintf(RED_OUT, "<="); 
    break; 
  case EQ: 
  case ARITH_EQ: 
    fprintf(RED_OUT, "=="); 
    break; 
  case NEQ: 
  case ARITH_NEQ: 
    fprintf(RED_OUT, "!="); 
    break;
  case GEQ:
  case ARITH_GEQ: 
    fprintf(RED_OUT, ">="); 
    break;
  case GREATER:
  case ARITH_GREATER: 
    fprintf(RED_OUT, ">"); 
    break;
  case ARITH_ADD: 
    fprintf(RED_OUT, "+"); 
    break; 
  case ARITH_MINUS: 
    fprintf(RED_OUT, "-"); 
    break;
  case ARITH_MULTIPLY: 
    fprintf(RED_OUT, "*"); 
    break; 
  case ARITH_DIVIDE: 
    fprintf(RED_OUT, "/"); 
    break;
  case ARITH_MODULO: 
    fprintf(RED_OUT, "%%"); 
    break;
  case BIT_NOT: 
    fprintf(RED_OUT, "~"); 
    break;

  case BIT_OR: 
    fprintf(RED_OUT, "|"); 
    break;

  case BIT_AND:  
    fprintf(RED_OUT, "&"); 
    break;

  case BIT_SHIFT_RIGHT: 
    fprintf(RED_OUT, ">>"); 
    break;

  case BIT_SHIFT_LEFT: 
    fprintf(RED_OUT, "<<"); 
    break;

  case TYPE_FALSE: 
    fprintf(RED_OUT, "FALSE"); 
    break; 
  case TYPE_TRUE: 
    fprintf(RED_OUT, "TRUE"); 
    break; 
  case TYPE_CONSTANT: 
    fprintf(RED_OUT, "CONSTANT"); 
    break; 
  case TYPE_INDIRECT_PI: 
    fprintf(RED_OUT, "INDIRECT_PI"); 
    break;
  case TYPE_PATH_ENDPOINT: 
    fprintf(RED_OUT, "PATH ENDPOINT"); 
    break; 
  case TYPE_VALUE:
    fprintf(RED_OUT, "VALUE");
    break; 
  case TYPE_OP: 
    fprintf(RED_OUT, "OP");
    break; 
  case TYPE_XTION_INSTANCE: 
    fprintf(RED_OUT, "XTION_INS"); 
    break; 
  case TYPE_ACTION_INSTANCE: 
    fprintf(RED_OUT, "ACTION_INS");
    break; 
  case TYPE_CLOCK:
    fprintf(RED_OUT, "CLOCK");
    break;
  case TYPE_DENSE:
    fprintf(RED_OUT, "DENSE");
    break;
  case TYPE_POINTER:
    fprintf(RED_OUT, "POINTER");
    break; 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, "SYNC"); 
    break; 
  case TYPE_DISCRETE: 
    fprintf(RED_OUT, "DISCRETE");
    break; 
  case TYPE_FLOAT: 
    fprintf(RED_OUT, "FLOAT");
    break; 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "DOUBLE");
    break; 
  case TYPE_STREAM: 
    fprintf(RED_OUT, "STREAM");
    break; 
  case TYPE_QSYNC_HOLDER: 
    fprintf(RED_OUT, "QSYNC HOLDER");
    break; 
  case TYPE_CRD:
    fprintf(RED_OUT, "CLOCK INEQ");
    break;
  case TYPE_CDD:
    fprintf(RED_OUT, "FILTER INEQ");
    break; 
  case TYPE_HRD:
    fprintf(RED_OUT, "HYBRID INEQ");
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "HYBRID FILTER");
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "LAZY-EXP"); 
    break; 
  default:
    fprintf(RED_OUT, "\nError: wrong inequality operator op = %1d\n", op);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
/* print_op() */




int	op_length(op) {
  switch (op) {
  case LESS: 
  case ARITH_LESS: 
  case GREATER:
  case ARITH_GREATER: 
  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case BIT_NOT:  
  case BIT_OR: 
  case BIT_AND:  

    return (1);  

  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case LEQ: 
  case ARITH_LEQ: 
  case EQ: 
  case ARITH_EQ: 
  case NEQ: 
  case ARITH_NEQ: 
  case GEQ:
  case ARITH_GEQ: 
    return(2); 
  case TYPE_FALSE: 
    return(5); 
  case TYPE_TRUE: 
    return(4); 
  case TYPE_CONSTANT: 
    return(8); 
  case TYPE_INDIRECT_PI: 
    return(11); 
  case TYPE_PATH_ENDPOINT: 
    return(13); 
  case TYPE_VALUE:
    return(5); 
  case TYPE_OP: 
    return(2); 
  case TYPE_XTION_INSTANCE: 
    return(9); 
  case TYPE_ACTION_INSTANCE: 
    return(20); 
  case TYPE_CLOCK:
    return(5); 
  case TYPE_DENSE:
    return(5); 
    break;
  case TYPE_POINTER:
    return(7); 
  case TYPE_SYNCHRONIZER: 
    return(4); 
  case TYPE_DISCRETE: 
    return(8); 
  case TYPE_FLOAT: 
    return(5); 
  case TYPE_DOUBLE: 
    return(6); 
  case TYPE_QSYNC_HOLDER: 
    return(12); 
  case TYPE_CRD:
    return(10); 
  case TYPE_CDD: 
    return(11); 
  case TYPE_HRD: 
    return(11); 
  case TYPE_HDD: 
    return(13); 
  default:
    fprintf(RED_OUT, "\nError: wrong inequality operator op = %1d\n", op);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
  /* op_length() */




void	bk(word) 
  char	*word; 
{ 
  char	*a; 

  fflush(RED_OUT); 
  fprintf(RED_OUT, "%s\n", word); 
  fflush(RED_OUT); 
  fflush(stdout); 
  a = 0; 
  *a = 'a'; 
  exit(0); 
} 
  /* bk() */ 
  

int	*dummy_memory; 

void	allocdmy() { 
  int	i; 
  
  dummy_memory = (int *) malloc(5*sizeof(int)); 
  for (i = 0; i < 5; i++) 
    dummy_memory[i] = 0; 
}
  /* dummy_alloc() */   


void 	freedmy() { 
  free(dummy_memory);  	
}
  /* freedmy() */ 
  
  

int	dirtydmy() { 
  int	i; 
  
  for (i = 0; i < 5; i++) 
    if (dummy_memory[i]) {
      fprintf(RED_OUT, " -- Dirty cell %1d with value %1d.\n", i, dummy_memory[i]); 
      return(1); 
    }
  fprintf(RED_OUT, " -- Clean cells!\n"); 
  return(0); 
}
  /* dirty_dummy() */ 
  
  

void test_alloc()
{
  char	***t;
  int	i, j;

  t = (char ***) malloc(10 * sizeof(char **));
  for (i = 0; i < 10; i++) {
    t[i] = (char **) malloc(100 * sizeof(char *));
    for (j = 0; j < 100; j++)
      t[i][j] = (char *) malloc(10000);
  }
  for (i = 0; i < 10; i++) {
    for (j = 0; j < 100; j++)
      free(t[i][j]);
    free(t[i]);
  }

  free(t);
}
  /* test_alloc() */


void sw_stdout()
{
  tmp_out = RED_OUT;
  RED_OUT = stdout;
}
  /* sw_stdout() */

void 	sw_out(FILE* temp)
{
  tmp_out = RED_OUT;
  RED_OUT = temp;
}
  /* sw_stdout() */


void sw_restore()
{
  RED_OUT = tmp_out;
}
  /* sw_restore() */ 



FILE	*ORIG_STDOUT, *ORIG_REDOUT, *redtmp; 

void	new_tmp_out() {
  ORIG_STDOUT = stdout; 
  ORIG_REDOUT = RED_OUT; 
  
  RED_OUT = stdout = fopen("redtmp", "w"); 
}
  /* new_tmp_out() */ 


void	sw_tmp_out() {
  ORIG_STDOUT = stdout; 
  ORIG_REDOUT = RED_OUT; 
  
  RED_OUT = stdout = redtmp; 
}
  /* sw_tmp_out() */ 


void	restore_tmp_out() { 
  redtmp = RED_OUT; 
  stdout = ORIG_STDOUT; 
  RED_OUT = ORIG_REDOUT; 
}
  /* restore_tmp_out() */ 


void get_line(s, lim)
	char	*s;
	int	lim;
{ 
  int 	i; 
  
  for (i = 0, s[i] = getchar(); 
       i < lim && s[i] != '\n' && s[i] != EOF;
       s[++i] = getchar()
       ) 
    if (s[i] = '\\') { 
      s[++i] = getchar(); 
      if (s[i] = '\n') 
        i = i - 2;
    } 
  s[i] = '\0'; 
}
/* get_line() */



void	print_variable(vi) 
     int	vi; 
{
  int	i;

  if (VAR[vi].TYPE >= LESS && VAR[vi].TYPE <= GREATER) {
    fprintf(RED_OUT, "vi=%3d;", vi); 
    if (VAR[vi].STATUS & FLAG_LOCAL_VARIABLE)
      fprintf(RED_OUT, "LOCAL (%1d) ", VAR[vi].PROC_INDEX); 
    else
      fprintf(RED_OUT, "GLOBAL(%1d) ", VAR[vi].PROC_INDEX);
    fprintf(RED_OUT, "%s;", VAR[vi].NAME); 
  }
  else if (VAR[vi].TYPE == TYPE_CRD) {
    fprintf(RED_OUT, "vi=%3d;", vi); 
    if (VAR[vi].STATUS & FLAG_LOCAL_VARIABLE) 
      fprintf(RED_OUT, "LOCAL (%1d) ", VAR[vi].PROC_INDEX); 
    else 
      fprintf(RED_OUT, "GLOBAL(%1d) ", VAR[vi].PROC_INDEX); 
    fprintf(RED_OUT, "%s;", VAR[vi].NAME); 
  }
  else {
    fprintf(RED_OUT, "vi=%3d;", vi); 
    if (VAR[vi].STATUS & FLAG_VAR_STACK)
      fprintf(RED_OUT, "STACK (%1d) %s;", VAR[vi].PROC_INDEX, VAR[vi].NAME); 
    else if (VAR[vi].PROC_INDEX) 
      fprintf(RED_OUT, "LOCAL (%1d) %s;", VAR[vi].PROC_INDEX, VAR[vi].NAME);
    else
      fprintf(RED_OUT, "GLOBAL(%1d) %s;", VAR[vi].PROC_INDEX, VAR[vi].NAME); 
  }

  print_op(VAR[vi].TYPE); 
  switch (VAR[vi].TYPE) {
  case TYPE_CRD: 
    fprintf(RED_OUT, "; C1=%1d; C2=%1d;", 
      VAR[vi].U.CRD.CLOCK1, VAR[vi].U.CRD.CLOCK2 
    ); 
    break; 
  case TYPE_FLOAT: 
    fprintf(RED_OUT, "; O=%1d; LB=%.4f; UB=%.4f; S=%x;", 
      VAR[vi].OFFSET, VAR[vi].U.FLT.LB, VAR[vi].U.FLT.UB, 
      VAR[vi].STATUS 
    );
    break; 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "; O=%1d; LB=%.4f; UB=%.4f; S=%x;", 
      VAR[vi].OFFSET, VAR[vi].U.DBLE.LB, VAR[vi].U.DBLE.UB, 
      VAR[vi].STATUS 
    );
    break; 
  default: 
    fprintf(RED_OUT, "; O=%1d; LB=%1d; UB=%1d; S=%x;", 
      VAR[vi].OFFSET, VAR[vi].U.DISC.LB, VAR[vi].U.DISC.UB, 
      VAR[vi].STATUS 
    );
    break; 
  }
  fprintf(RED_OUT, "\n"); 
}
/* print_variable() */ 




void	print_variables()
{
  int	vi, ci, si; 

  fprintf(RED_OUT, "\n===================================================\n{%1d VARIABLES}\n", VARIABLE_COUNT); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    print_variable(vi);
  }

  fprintf(RED_OUT, "\n===================================================\n{%1d CLOCKS}\n", CLOCK_COUNT);
  for (ci = 0; ci < CLOCK_COUNT; ci++) {
    fprintf(RED_OUT, "CLOCK %1d == ", ci); 
    print_variable(CLOCK[ci]); 
  }
}
/* print_variables() */



void	print_gsync(si) 
	int	si; 
{ 
  int	ixi; 
  
/*
  fprintf(RED_OUT, "%1d:%1d:", si, GSYNC[si].VAR_INDEX); 
  fprintf(RED_OUT, "%s:", VAR[GSYNC[si].VAR_INDEX].NAME); 
  fprintf(RED_OUT, "%x, ", GSYNC[si].STATUS); 
  fprintf(RED_OUT, "%1d Q[", GSYNC[si].Q_XTION_COUNT); 
*/
  fprintf(RED_OUT, "%1d:%1d:%s:%x, %1d Q[", si, GSYNC[si].VAR_INDEX, 
	  VAR[GSYNC[si].VAR_INDEX].NAME, GSYNC[si].STATUS, GSYNC[si].Q_XTION_COUNT
	  );                                                                                                                   
  if (GSYNC[si].Q_XTION_COUNT) { 
    fprintf(RED_OUT, "xi=%1d?%1d", GSYNC[si].Q_XTION[0].XTION_INDEX, 
	    GSYNC[si].Q_XTION[0].PLACE_INDEX
	    ); 
    for (ixi = 1; ixi < GSYNC[si].Q_XTION_COUNT; ixi++) { 
      fprintf(RED_OUT, ", xi=%1d?%1d", GSYNC[si].Q_XTION[ixi].XTION_INDEX, GSYNC[si].Q_XTION[ixi].PLACE_INDEX); 
    } 
  }
  fprintf(RED_OUT, "]; %1d X[", GSYNC[si].X_XTION_COUNT); 
  if (GSYNC[si].X_XTION_COUNT) { 
    fprintf(RED_OUT, "xi=%1d!%1d", GSYNC[si].X_XTION[0].XTION_INDEX, 
	    GSYNC[si].X_XTION[0].PLACE_INDEX
	    ); 
    for (ixi = 1; ixi < GSYNC[si].X_XTION_COUNT; ixi++) { 
      fprintf(RED_OUT, ", xi=%1d!%1d", GSYNC[si].X_XTION[ixi].XTION_INDEX, GSYNC[si].X_XTION[ixi].PLACE_INDEX); 
    } 
  }
  fprintf(RED_OUT, "]\n"); 
} 
  /* print_gsync() */ 
  
  
  
void	print_gsyncs() { 
  int	si; 
  
  fprintf(RED_OUT, "\n%1d GSYNCs:\n", GLOBAL_COUNT[TYPE_SYNCHRONIZER]); 
  for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) { 
    print_gsync(si); 
  } 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
} 
  /* print_gsyncs() */ 


void	print_processes()
{
  int	i, j; 

  fprintf(RED_OUT, "\n-----(%d Process)---------------------\n", 
	  PROCESS_COUNT); 
  for (i = 1; i <= PROCESS_COUNT; i++) { 
    fprintf(RED_OUT, "id %d; name %s; status %1x, grouped to %1d\n", 
    	    i, PROCESS[i].name, PROCESS[i].status, 
    	    PROCESS[i].group_process_index
    	    );
    
    fprintf(RED_OUT, "\n  %1d reachable modes: ", PROCESS[i].reachable_mode_count);
    if (PROCESS[i].reachable_mode_count > 0) {
      fprintf(RED_OUT, "%1d", PROCESS[i].reachable_mode[0]); 
      for (j = 1; j < PROCESS[i].reachable_mode_count; j++) 
	fprintf(RED_OUT, ", %1d", PROCESS[i].reachable_mode[j]); 
    }
    
    fprintf(RED_OUT, "\n  %1d firable xtions: ", PROCESS[i].firable_xtion_count); 
    if (PROCESS[i].firable_xtion_count > 0) {
      fprintf(RED_OUT, "%1d", PROCESS[i].firable_xtion[0]);
      for (j = 1; j < PROCESS[i].firable_xtion_count; j++)
	fprintf(RED_OUT, ", %1d", PROCESS[i].firable_xtion[j]);
    }
    fprintf(RED_OUT, "\n");
    
  }
}
  /* print_procs() */



int	mode_index_value(act) 
  struct statement_type	*act; 
{ 
  return (   act->u.act.term_count == 1 
	  && act->u.act.term[0].coeff->type == TYPE_CONSTANT 
	  && act->u.act.term[0].coeff->u.value == 1
	  && act->u.act.term[0].operand->type == TYPE_DISCRETE 
	  && (act->u.act.term[0].operand->u.atom.var->status & FLAG_LOCAL_VARIABLE) 
	  && (act->u.act.term[0].operand->u.atom.var->index == OFFSET_MODE) 
	  && act->u.act.offset->type == TYPE_CONSTANT
	  && act->u.act.offset->u.value >= 0
	  && act->u.act.offset->u.value < MODE_COUNT 
	  ); 
}
  /* mode_index_value() */ 



#if RED_DEBUG_BASICS_MODE
int	count_fst = 0; 
#endif 

void	print_statement_line(); 

int	FLAG_FREE_SYNC_STATEMENT; 

void 	free_statement(st) 
	struct statement_type	*st; 
{ 
  int	i; 
  
  #if RED_DEBUG_BASICS_MODE
  fprintf(RED_OUT, "===<count_fst = %1d, ", ++count_fst); 
  #endif 
  
  if (!st) {
    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, "NULL st>=======\n"); 
    fflush(RED_OUT); 
    #endif 
    
    return; 
  }

  #if RED_DEBUG_BASICS_MODE
  fprintf(RED_OUT, "st->op %1d>=======\n", st->op); 
  print_statement_line(st, 1); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
  #endif 
  
  if (   FLAG_FREE_SYNC_STATEMENT 
      && !(st->st_status & FLAG_ACTION_QUANTIFIED_SYNC)
      ) 
    return; 
    
  switch (st->op) { 
  case UNCHANGED: 
    break; 
  case ST_IF: 
    free_statement(st->u.branch.if_statement); 
    if (st->u.branch.else_statement) 
      free_statement(st->u.branch.else_statement); 
    free(((struct red_type **) st->u.branch.red_cond)+1); 
    free(((struct red_type **) st->u.branch.red_uncond)+1); 
    break; 
  case ST_WHILE: 
    free_statement(st->u.loop.statement); 
    free(((struct red_type **) st->u.loop.red_cond)+1);     
    free(((struct red_type **) st->u.loop.red_uncond)+1);     
    free(((struct red_type **) st->u.loop.red_gfp)+1);     
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\nst seq %1d \n", i); 
      fflush(RED_OUT); 
      #endif 
      
      free_statement(st->u.seq.statement[i]);  
    } 
    free(st->u.seq.statement); 
    break; 
  case ST_GUARD: 
    free(((struct red_type **) st->u.guard.red_cond)+1);     
    free(((struct red_type **) st->u.guard.red_uncond)+1);     
    break; 
    
  case ST_ERASE: 
  
    break; 
  case ASSIGN_DISCRETE_CONSTANT:
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) { 
    case FLAG_ACTION_OFFSET_CONSTANT: 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      free(st->u.act.offset_numerator+1);
      free(st->u.act.offset_denominator+1);
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL: 
      break; 
    }
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, "to free st:%x->u.act.lhs:%x\n", st, st->u.act.lhs); 
    #endif 
//    free_ps_exptree(st->u.act.lhs); 
    st->u.act.lhs = NULL; 
//    free_ps_exptree(st->u.act.rhs_exp); 
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) { 
    case FLAG_ACTION_OFFSET_CONSTANT: 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      free(st->u.act.offset_numerator+1);
      free(st->u.act.offset_denominator+1);
      free(st->u.act.single_coeff_numerator+1); 
      free(st->u.act.single_coeff_denominator+1); 
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL: 
      break; 
    } 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    for (i = 0; i < st->u.act.term_count; i++) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "freeing coeeficient %x:%1d * %x:%s\n", 
        st->u.act.term[i].coeff, 
        st->u.act.term[i].coeff->u.value, 
        st->u.act.term[i].operand, 
        st->u.act.term[i].operand->u.atom.var->name
      ); 
      #endif 
//      free_ps_exptree(st->u.act.term[i].coeff); 
      if (st->u.act.term[i].operand == st->u.act.lhs) 
        st->u.act.lhs = NULL; 
//      free_ps_exptree(st->u.act.term[i].operand); 
    }
    free(st->u.act.term); 
    if (st->u.act.lhs) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "to free st:%x->u.act.lhs:%x\n", st, st->u.act.lhs); 
      #endif 
//      free_ps_exptree(st->u.act.lhs); 
      st->u.act.lhs = NULL; 
    }
    if (st->u.act.rhs_exp) { 
      if (st->u.act.rhs_exp == st->u.act.offset) 
        st->u.act.offset = NULL; 
//      free_ps_exptree(st->u.act.rhs_exp); 
    }
    if (st->u.act.offset) { 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\n  to free offset %x\n", st->u.act.offset); 
      pcform(st->u.act.offset); 
      fflush(RED_OUT); 
      #endif 
      
//      free_ps_exptree(st->u.act.offset); 
    }
    break; 
  case ASSIGN_HYBRID_EXP: 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) { 
    case FLAG_ACTION_OFFSET_CONSTANT: 
      break;  
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      free(st->u.act.offset_numerator+1);
      free(st->u.act.offset_denominator+1);
      free(st->u.act.single_coeff_numerator+1); 
      free(st->u.act.single_coeff_denominator+1); 
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL: 
      break; 
    } 
    for (i = 0; i < st->u.act.term_count; i++) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "freeing coefficient %x:%1d * %x:%s\n", 
        st->u.act.term[i].coeff, 
        st->u.act.term[i].coeff->u.value, 
        st->u.act.term[i].operand, 
        st->u.act.term[i].operand->u.atom.var->name
      ); 
      #endif 
//      free_ps_exptree(st->u.act.term[i].coeff); 
      if (st->u.act.term[i].operand == st->u.act.lhs) 
        st->u.act.lhs = NULL; 
//      free_ps_exptree(st->u.act.term[i].operand); 
    }
    free(st->u.act.term); 
    if (st->u.act.lhs) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "to free st:%x->u.act.lhs:%x\n", st, st->u.act.lhs); 
      #endif 
//      free_ps_exptree(st->u.act.lhs); 
      st->u.act.lhs = NULL; 
    }
    if (st->u.act.rhs_exp) { 
      if (st->u.act.rhs_exp == st->u.act.offset) 
        st->u.act.offset = NULL; 
//      free_ps_exptree(st->u.act.rhs_exp); 
    }
    if (st->u.act.offset) { 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\n  to free offset %x\n", st->u.act.offset); 
      pcform(st->u.act.offset); 
      fflush(RED_OUT); 
      #endif 
//      free_ps_exptree(st->u.act.offset); 
    }
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) {
    case FLAG_ACTION_OFFSET_CONSTANT: 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL:  
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      free(st->u.act.offset_numerator + 1);
      free(st->u.act.offset_denominator + 1);
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
      fprintf(RED_OUT, "Error: Illegal increment types:\n"); 
      pcform(st->u.act.rhs_exp); 
      fflush(RED_OUT); 
      bk(0); 
      break; 
    }
    st->u.act.term = NULL;
    st->u.act.term_count = 0; 
    st->u.act.offset = NULL;
    st->u.act.single_coeff_numerator = NULL; 
    st->u.act.single_coeff_denominator = NULL; 

    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, "to free st:%x->u.act.lhs:%x\n", st, st->u.act.lhs); 
    #endif 
//    free_ps_exptree(st->u.act.lhs); 
    st->u.act.lhs = NULL; 
//    free_ps_exptree(st->u.act.rhs_exp); 
    break; 
  default: 

    break; 
  } 
    
  free(st); 
  return; 
}
  /* free_statement() */ 
  
  
void 	free_sync_statement(st) 
	struct statement_type	*st; 
{ 
  FLAG_FREE_SYNC_STATEMENT = TYPE_TRUE; 
  free_statement(st); 
}
  /* free_sync_statement() */ 
  
  
void 	free_xtion_statement(st) 
	struct statement_type	*st; 
{ 
  FLAG_FREE_SYNC_STATEMENT = TYPE_FALSE; 
  free_statement(st); 
}
  /* free_xtion_statement() */ 
  
  
  
void	print_mode(mi)
	int mi;
{
  int	ipi, pi, ixi, zbi;

  fprintf(RED_OUT, "---[MODE %1d:%s]----: s:%x -------------\n",
  	  mi, MODE[mi].name, MODE[mi].status
  	  ); 
  if (red_query_mode_src_lines(mi)) 
    fprintf(RED_OUT, "SRC LINES:\n%s\n", red_query_mode_src_lines(mi)); 
  
  if (MODE[mi].xtion_count == 0) { 
    fprintf(RED_OUT, "--- %1d xtions.\n", MODE[mi].xtion_count);
  }
  else { 
    fprintf(RED_OUT, "--- %1d xtions: %1d", MODE[mi].xtion_count, MODE[mi].xtion[0]);
    for (ixi = 1; ixi < MODE[mi].xtion_count; ixi++)
      fprintf(RED_OUT, ", %1d", MODE[mi].xtion[ixi]);
    fprintf(RED_OUT, "\n");
  }
  fflush(RED_OUT);

  if (MODE[mi].process_count == 0) { 
    fprintf(RED_OUT, "--- %1d processes.\n", MODE[mi].process_count);
  } 
  else { 
    fprintf(RED_OUT, "--- %1d processes: %1d", MODE[mi].process_count, MODE[mi].process[0]);
    for (ipi = 1; ipi < MODE[mi].process_count; ipi++)
      fprintf(RED_OUT, ", %1d", MODE[mi].process[ipi]);
    fprintf(RED_OUT, "\n");
  }
  fflush(RED_OUT);

  for (ipi = 0; ipi < MODE[mi].process_count; ipi++) {
    pi = MODE[mi].process[ipi];
    fprintf(RED_OUT, "------ pi: %1d ----\n------ invariance red: \n", pi);
    red_print_graph(MODE[mi].invariance[pi].red);
    fflush(RED_OUT);
    fprintf(RED_OUT, "       untimed invariance red: \n");
    red_print_graph(MODE[mi].invariance[pi].untimed_red);
    fflush(RED_OUT);
    fprintf(RED_OUT, "------ %1d zone bounds: \n", MODE[mi].invariance[pi].zone_bound_count);
    for (zbi = 0; zbi < MODE[mi].invariance[pi].zone_bound_count; zbi++) {
      fprintf(RED_OUT, "(%1d:%1s, %1d)\n",
	      MODE[mi].invariance[pi].zone_bound[zbi].var_index,
      	      VAR[MODE[mi].invariance[pi].zone_bound[zbi].var_index].NAME,
      	      MODE[mi].invariance[pi].zone_bound[zbi].upper_bound
      	      );
    }
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
  }
}
/* print_mode() */




void	print_modes() {
  int	mi;

  fprintf(RED_OUT, "\n========(%1d MODES)=====================================\n", MODE_COUNT);
  for (mi = 0; mi < MODE_COUNT; mi++) {
    print_mode(mi);
  }
}
/* print_modes() */




int	pointer_dirty_value(act) 
  struct statement_type	*act; 
{ 
  return (   act->u.act.term_count == 1 
	  && act->u.act.term[0].coeff->type == TYPE_CONSTANT 
	  && act->u.act.term[0].coeff->u.value == 1
	  && act->u.act.term[0].operand->type == TYPE_POINTER 
	  && act->u.act.offset->type == TYPE_CONSTANT
	  && act->u.act.offset->u.value == PROCESS_COUNT+1
	  ); 
}
  /* pointer_dirty_value() */ 



print_linear_action_line(st, pi)
     struct statement_type	*st; 
     int 			pi;
{
  int   		i, numerator, denominator;
  struct red_type	*red_offset; 

  print_parse_subformula(st->u.act.term[0].operand, pi);
  fprintf (RED_OUT, "=");
/*
  if (st->u.act.term_count == 2) {
    if (st->u.act.term[1].coeff->type == TYPE_CONSTANT) {
      numerator = -1*st->u.act.term[1].coeff->u.value;
      denominator = 1;
    }
    else {
      numerator = -1*st->u.act.single_coeff_numerator[pi];
      denominator = st->u.act.single_coeff_denominator[pi];
    }
    if (denominator != 1){
      if (numerator < 0)
        fprintf(RED_OUT, "-(%1d/%1d)", abs(numerator), denominator);
      else if(i>1)
        fprintf(RED_OUT, "+(%1d/%1d)", numerator, denominator);
      else
        fprintf(RED_OUT, "%1d/%1d", numerator, denominator);
    }
    else if(numerator !=1){
      if (numerator < 0)
        fprintf(RED_OUT, "%1d*", numerator);
      else if(i>1)
        fprintf(RED_OUT, "+%1d*", numerator);
      else
        fprintf(RED_OUT, "%1d*", numerator);
    }
    print_parse_subformula(st->u.act.term[1].operand, pi);
  }
  else 
*/
  for (i = 1; i < st->u.act.term_count; i++) {
    if (st->u.act.term[i].coeff->type == TYPE_CONSTANT) {
      numerator = -1*st->u.act.term[i].coeff->u.value;
      denominator = 1;
    }
    else {
      rec_get_rationals(st->u.act.term[i].coeff, &numerator, &denominator);
      numerator = -1 * numerator;
    }
    if (denominator != 1){
      if (numerator < 0)
        fprintf(RED_OUT, "-(%1d/%1d)", abs(numerator), denominator);
      else if(i>1)
        fprintf(RED_OUT, "+(%1d/%1d)", numerator, denominator);
      else
        fprintf(RED_OUT, "%1d/%1d", numerator, denominator);
    }
    else if(numerator !=1){
      if (numerator < 0)
        fprintf(RED_OUT, "%1d*", numerator);
      else if(i>1)
        fprintf(RED_OUT, "+%1d*", numerator);
      else
        fprintf(RED_OUT, "%1d*", numerator);
    }
    print_parse_subformula(st->u.act.term[i].operand, pi);
  }

  if (st->u.act.offset->type == TYPE_CONSTANT) {
    if (mode_index_value(st)) {
      fprintf(RED_OUT, "%s", MODE[st->u.act.offset->u.value].name); 
    }
    else if (pointer_dirty_value(st)) { 
      fprintf(RED_OUT, "DIRTY"); 
    } 
    else if (st->u.act.offset->u.value <= 0)
      fprintf(RED_OUT, "%1d", st->u.act.offset->u.value);
    else if(st->u.act.offset->u.value > 0)
      fprintf(RED_OUT, "+%1d", st->u.act.offset->u.value);
  }
  else if (st->u.act.offset->type == TYPE_INTERVAL) {
    if (st->u.act.offset->u.interval.status & INTERVAL_LEFT_UNBOUNDED)
      fprintf(RED_OUT, "+(-oo,");
    else {
      if (st->u.act.offset->u.interval.status & INTERVAL_LEFT_OPEN)
        fprintf(RED_OUT, "(");
      else
        fprintf(RED_OUT, "[");
      get_rationals(st->u.act.offset->u.interval.lbound_exp, pi, &numerator, &denominator);
      if (denominator == 1 || numerator == 0)
        fprintf(RED_OUT, "%1d,", numerator);
      else
        fprintf(RED_OUT, "%1d/%1d,", numerator, denominator);
    }
    if (st->u.act.offset->u.interval.status & INTERVAL_RIGHT_UNBOUNDED)
      fprintf(RED_OUT, "oo)");
    else {
      get_rationals(st->u.act.offset->u.interval.rbound_exp, pi, &numerator, &denominator);
      if (denominator == 1 || numerator == 0)
        fprintf(RED_OUT, "%1d,", numerator);
      else
        fprintf(RED_OUT, "%1d/%1d,", numerator, denominator);
      if (st->u.act.offset->u.interval.status & INTERVAL_RIGHT_OPEN)
        fprintf(RED_OUT, ")");
      else
        fprintf(RED_OUT, "]");
    }
  }
  else /* if (st->u.act.offset->status & FLAG_QUANTIFIED_SYNC) */ { 
    print_parse_subformula(st->u.act.offset, pi); 
  } 
/* 
  else switch (st->op) { 
  case ASSIGN_DISCRETE_CONSTANT:
  case ASSIGN_DISCRETE_LINEAR:
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    
    break; 
  default: 
    if (st->u.act.offset_numerator[pi] != 0) {
      numerator = st->u.act.offset_numerator[pi];
      denominator = st->u.act.offset_denominator[pi];
      if (denominator !=1){
        if (numerator < 0)
          fprintf(RED_OUT, "-(%1d/%1d)", abs(numerator), denominator);
        else
          fprintf(RED_OUT, "+(%1d/%1d)", numerator, denominator);
      }
      else{
        if (numerator < 0)
          fprintf(RED_OUT, "%1d", numerator);
        else if(i>0)
          fprintf(RED_OUT, "+%1d", numerator);
      }
    }
    break; 
  }
*/
  fprintf(RED_OUT, "; "); 
}
/* print_linear_action_line() */





void	print_action_line(st, pi)
     struct statement_type	*st; 
     int			pi;
{
  int 	i, numerator, denominator;

  switch (st->op) {
  case UNCHANGED: 
    fprintf(RED_OUT, ";"); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT:
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    if (   st->u.act.lhs->type == TYPE_DISCRETE
        && st->u.act.lhs->u.atom.var == var_mode
        && st->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER
        ) { 
      if (st->u.act.rhs_exp->type == TYPE_MODE_INDEX) { 
        fprintf(RED_OUT, "goto %s;", 
          st->u.act.rhs_exp->u.mode_index.mode_name
        ); 
        break; 
      }
      else if (   MODE 
               && st->u.act.rhs_exp->type == TYPE_CONSTANT 
               && st->u.act.rhs_exp->u.value >= 0 
               && st->u.act.rhs_exp->u.value < MODE_COUNT
               ) { 
        fprintf(RED_OUT, "goto %s;", 
          MODE[st->u.act.rhs_exp->u.value].name
        ); 
        break; 
      } 
    } 
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "=");
    print_parse_subformula(st->u.act.rhs_exp, pi);
    fprintf(RED_OUT, "; "); 
    break;
  case INCREMENT_BY_CONSTANT:
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "++%1d;", st->u.act.rhs_exp->u.value);
    break;
  case DECREMENT_BY_CONSTANT:
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "--%1d;", st->u.act.rhs_exp->u.value);
    break;
  case ASSIGN_TRASH:
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "=?;");
    break;
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    print_linear_action_line(st, pi);
    break;
  }
}
/* print_action_line() */








void	print_detailed_action_line(st, pi)
     struct statement_type	*st; 
     int			pi;
{
  int 	i, numerator, denominator;

  fprintf(RED_OUT, "      "); 
  
  switch (st->op) {
  case UNCHANGED: 
    fprintf(RED_OUT, "ASSIGN TRASH: ;"); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
    fprintf(RED_OUT, "ASSIGN DISCRETE EXP: %x; ", st->st_status);
    if (   st->u.act.lhs->type == TYPE_DISCRETE 
        && st->u.act.lhs->u.atom.var == var_mode 
        && st->u.act.lhs->u.atom.exp_base_proc_index->type 
           == TYPE_LOCAL_IDENTIFIER 
        && st->u.act.rhs_exp->type == TYPE_CONSTANT 
      ) {
      fprintf(RED_OUT, "goto %s; ", MODE[st->u.act.rhs_exp->u.value].name); 
    }
    else {
      print_linear_action_line(st, pi);
    }
    break; 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "=");
    print_parse_subformula(st->u.act.rhs_exp, pi); 
    break;
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    fprintf(RED_OUT, "ASSIGN CLOCK EXP: %x; ", st->st_status);
    print_linear_action_line(st, pi);
    break;
  case INCREMENT_BY_CONSTANT:
    fprintf(RED_OUT, "INC BY CONSTANT: %x; ", st->st_status);
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "++%1d;", st->u.act.rhs_exp->u.value);
    break;
  case DECREMENT_BY_CONSTANT:
    fprintf(RED_OUT, "DEC BY CONSTANT: %x; ", st->st_status);
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "++%1d;", st->u.act.rhs_exp->u.value);
    break;
  case ASSIGN_TRASH:
    fprintf(RED_OUT, "ASSIGN TRASH: %x; ", st->st_status);
    print_parse_subformula(st->u.act.lhs, pi);
    fprintf(RED_OUT, "=?;");
    break;
  case ASSIGN_HYBRID_EXP:
    fprintf(RED_OUT, "ASSIGN HYBRID EXP: %x; ", st->st_status);
    print_linear_action_line(st, pi);
    break;
  }
}
/* print_detailed_action_line() */




void	print_statement_line(st, pi) 
	struct statement_type	*st; 
	int			pi; 
{ 
  int	i; 
  
  if (!st) {
    fprintf(RED_OUT, ";"); 
    return; 
  }
    
  switch (st->op) { 
  case UNCHANGED: 
    fprintf(RED_OUT, ";"); 
  case ST_IF: 
    fprintf(RED_OUT, "if ("); 
    if (   pi >= 1
        && pi <= PROCESS_COUNT  
        && red_path_count(st->u.branch.red_cond[pi]) <= 5
        )
      red_print_line(st->u.branch.red_cond[pi]); 
    else 
      print_parse_subformula(
        st->parse_statement->u.branch.cond, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
    fprintf(RED_OUT, ")"); 
    if (st->u.branch.if_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      fprintf(RED_OUT, "{"); 
      print_statement_line(st->u.branch.if_statement, pi); 
      fprintf(RED_OUT, "}"); 
    }
    else 
      print_statement_line(st->u.branch.if_statement, pi); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      fprintf(RED_OUT, " else "); 
      if (st->u.branch.else_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
        fprintf(RED_OUT, "{"); 
        print_statement_line(st->u.branch.else_statement, pi); 
        fprintf(RED_OUT, "}"); 
      }
      else 
        print_statement_line(st->u.branch.else_statement, pi); 
    } 
    break; 
  case ST_WHILE: 
    fprintf(RED_OUT, "while ("); 
    if (   pi >= 1
        && pi <= PROCESS_COUNT  
        && red_path_count(st->u.loop.red_cond[pi]) <= 5
        )
      red_print_line(st->u.loop.red_cond[pi]); 
    else  
      print_parse_subformula(
        st->parse_statement->u.loop.cond, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
    fprintf(RED_OUT, ")"); 
    if (st->u.loop.statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      fprintf(RED_OUT, "{"); 
      print_statement_line(st->u.loop.statement, pi); 
      fprintf(RED_OUT, "}"); 
    }
    else 
      print_statement_line(st->u.loop.statement, pi); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      print_statement_line(st->u.seq.statement[i], pi); 
    } 
    break; 
  case ST_CALL: 
    fprintf(RED_OUT, "call %s to %s;", 
      MODE[st->u.call.call_mode_index].name, 
      MODE[st->u.call.ret_mode_index].name
    );
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, "return;");
    break; 
  case ST_GUARD: 
    fprintf(RED_OUT, "guard ("); 
    if (   pi >= 1
        && pi <= PROCESS_COUNT  
        && red_path_count(st->u.guard.red_cond[pi]) <= 5
        )
      red_print_line(st->u.guard.red_cond[pi]); 
    else  
      print_parse_subformula(
        st->parse_statement->u.guard.cond, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
    fprintf(RED_OUT, ");"); 
    break; 
  case ST_ERASE: 
    fprintf(RED_OUT, "erase "); 
    print_parse_subformula(
      st->parse_statement->u.erase.var, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
    fprintf(RED_OUT, ";"); 
    break; 
  default: 
    print_action_line(st, pi); 
    break; 	
  } 
}
  /* print_statement_line() */ 





  
void	print_xtion_line(xi, pi) 
     int	xi, pi; 
{
  int	ci, ai, idi, lvi, rvi, si; 

  fprintf(RED_OUT, "when");
  for (ai = 0; ai < XTION[xi].stream_operation_count; ai++) { 
    switch (XTION[xi].stream_operation[ai].operation) {
    case OP_STREAM_OPEN_INPUT: 
      fprintf(RED_OUT, " open input %s;",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      break; 
    case OP_STREAM_OPEN_OUTPUT: 
      fprintf(RED_OUT, " open output %s;",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      break; 
    case OP_STREAM_CLOSE: 
      fprintf(RED_OUT, " close %s;",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      break; 
    case OP_MALLOC: 
      fprintf(RED_OUT, " malloc("); 
      print_parse_subformula(XTION[xi].stream_operation[ai].value_exp, pi);   
      fprintf(RED_OUT, ") >> ");   
      print_parse_subformula(XTION[xi].stream_operation[ai].var, pi);   
      fprintf(RED_OUT, ";"); 
      break; 
    case OP_FREE: 
      fprintf(RED_OUT, " free("); 
      print_parse_subformula(XTION[xi].stream_operation[ai].value_exp, pi);   
      fprintf(RED_OUT, ");"); 
      break; 
    case OP_STREAM_INPUT: 
      fprintf(RED_OUT, " input %s >> ",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      print_parse_subformula(XTION[xi].stream_operation[ai].var, pi);
      fprintf(RED_OUT, ";"); 
      break; 
    case OP_STREAM_OUTPUT: 
      fprintf(RED_OUT, " output %s << ", 
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      print_parse_subformula(XTION[xi].stream_operation[ai].value_exp, pi);
      fprintf(RED_OUT, ";"); 
      break; 
  } }
  for (ci = 0; ci < XTION[xi].sync_count; ci++) {
    si = XTION[xi].sync[ci].sync_index; 
    if (XTION[xi].sync[ci].type > 0) 
      fprintf(RED_OUT, " ?%s", VAR[GSYNC[si].VAR_INDEX].NAME); 
    else 
      fprintf(RED_OUT, " !%s", VAR[GSYNC[si].VAR_INDEX].NAME); 
    if (XTION[xi].sync[ci].exp_quantification) 
      if (XTION[xi].sync[ci].exp_quantification->type == TYPE_QSYNC_HOLDER) {
        fprintf(RED_OUT, "@"); 
        print_parse_subformula(XTION[xi].sync[ci].exp_quantification, pi); 
      }
      else { 
        fprintf(RED_OUT, "@("); 
        print_parse_subformula(XTION[xi].sync[ci].exp_quantification, pi); 
      	fprintf(RED_OUT, ")"); 
      } 
  }
  fprintf(RED_OUT, " ("); 
  if (   pi >= 1
      && pi <= PROCESS_COUNT  
      && !red_path_threshold(XTION[xi].red_trigger[pi], 6)
      )
    red_print_line(XTION[xi].red_trigger[pi]); 
  else 
    print_parse_subformula(XTION[xi].parse_xtion->trigger_exp, pi); 
  fprintf(RED_OUT, ") may ");
  print_statement_line(XTION[xi].statement, pi); 
}
/* print_xtion_line() */ 	






void	print_xtion(xi)
     int	xi;
{
  int	ci, si, pi, lvi, rvi, vci, ai;

  fprintf(RED_OUT, "\n***********************************************************\n");
  if (red_query_xtion_src_lines(xi))
    fprintf(RED_OUT, "XTION SRC LINES:\n%s\n", red_query_xtion_src_lines(xi)); 
  if (xi < XTION_COUNT)
    fprintf(RED_OUT, "XI=%1d; ", xi);
  else
    fprintf(RED_OUT, "Peer XI=%1d; ", xi);

  if (!valid_mode_index(XTION[xi].src_mode_index))
    fprintf(RED_OUT, "[-]->");
  else
    fprintf(RED_OUT, "[%1d:%s]->",
	    XTION[xi].src_mode_index, MODE[XTION[xi].src_mode_index].name
	    );

  if (!valid_mode_index(XTION[xi].dst_mode_index))
    fprintf(RED_OUT, "[-];");
  else
    fprintf(RED_OUT, "[%1d:%s];", XTION[xi].dst_mode_index, MODE[XTION[xi].dst_mode_index].name);

  fprintf(RED_OUT, "S=%x;%1d[", XTION[xi].status, XTION[xi].sync_count);
  for (ci = 0; ci < XTION[xi].sync_count; ci++) {
    si = XTION[xi].sync[ci].sync_index;
    fprintf(RED_OUT, "%1d:%1d:", si, GSYNC[si].VAR_INDEX);
    if (XTION[xi].sync[ci].type > 0) 
      fprintf(RED_OUT, "?"); 
    else 
      fprintf(RED_OUT, "!"); 
    fprintf(RED_OUT, "%s:%1d:%1d;", VAR[GSYNC[si].VAR_INDEX].NAME, ci, XTION[xi].sync[ci].qsync_vi);
    if (XTION[xi].sync[ci].exp_quantification) 
      print_parse_subformula(XTION[xi].sync[ci].exp_quantification, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
  }
  fprintf(RED_OUT, "]; P:%1d:", XTION[xi].process_count);
  for (ci = 0; ci < XTION[xi].process_count; ci++)
    fprintf(RED_OUT, "(%1d)", XTION[xi].process[ci]);
  fprintf(RED_OUT, "\n");

  print_parse_xtion(XTION[xi].parse_xtion, 0 /* depth */);
  fflush(RED_OUT);
  if (XTION[xi].status & FLAG_LOCAL_IDENTIFIER) {
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      fprintf(RED_OUT, "\n-----------------------------------------------\n");
      print_statement_line(XTION[xi].statement, pi);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
      fprintf(RED_OUT, "XTION[%1d].red_trigger[%1d]=\n", xi, pi);
      red_print_graph(XTION[xi].red_trigger[pi]);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
    }
  }
  else {
    fprintf(RED_OUT, "\n-----------------------------------------------\n");
    print_statement_line(XTION[xi].statement, 1);
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      fprintf(RED_OUT, "XTION[%1d].red_trigger[%1d]=\n", xi, pi);
      red_print_graph(XTION[xi].red_trigger[pi]);
      fprintf(RED_OUT, "\n");
      fprintf(RED_OUT, "XTION[%1d].red_events[%1d]=\n", xi, pi);
      red_print_graph(XTION[xi].red_events[pi]);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
    }
  }

}
/* print_xtion() */




void	print_simple_xtion(xi)
     int	xi;
{
  int	ci, si, pi, lvi, rvi, vci, ai;

  fprintf(RED_OUT, "\n***********************************************************\n");
  if (xi < XTION_COUNT)
    fprintf(RED_OUT, "XI=%1d; ", xi); 
  else 
    fprintf(RED_OUT, "Peer XI=%1d; ", xi);

  if (!valid_mode_index(XTION[xi].src_mode_index)) 
    fprintf(RED_OUT, "[-]->");
  else
    fprintf(RED_OUT, "[%1d:%s]->", 
	    XTION[xi].src_mode_index, MODE[XTION[xi].src_mode_index].name 
	    );

  if (!valid_mode_index(XTION[xi].dst_mode_index)) 
    fprintf(RED_OUT, "[-]; ");
  else 
    fprintf(RED_OUT, "[%1d:%s]; ", XTION[xi].dst_mode_index, MODE[XTION[xi].dst_mode_index].name);

  fprintf(RED_OUT, "S=%x;?:%1d[", XTION[xi].status, XTION[xi].sync_count);
  for (ci = 0; ci < XTION[xi].sync_count; ci++) {
    si = XTION[xi].sync[ci].sync_index; 
    fprintf(RED_OUT, "%1d:%1d:", si, GSYNC[si].VAR_INDEX); 
    if (XTION[xi].sync[ci].type > 0) 
      fprintf(RED_OUT, "?"); 
    else 
      fprintf(RED_OUT, "!"); 
    fprintf(RED_OUT, "%s:%1d:%1d;", VAR[GSYNC[si].VAR_INDEX].NAME, ci, XTION[xi].sync[ci].qsync_vi); 
    if (XTION[xi].sync[ci].exp_quantification) 
      print_parse_subformula(XTION[xi].sync[ci].exp_quantification, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
  }
  fprintf(RED_OUT, "]; P:%1d:", XTION[xi].process_count); 
  for (ci = 0; ci < XTION[xi].process_count; ci++)
    fprintf(RED_OUT, "(%1d)", XTION[xi].process[ci]); 
  fprintf(RED_OUT, "\n"); 

  print_parse_xtion(XTION[xi].parse_xtion, 1);
}
/* print_simple_xtion() */ 



void 	print_xtions()
{
  int	xi; 

  fprintf(RED_OUT, "\n==(%1d xtions)============================================\n", XTION_COUNT); 
  for (xi = 0; xi < XTION_COUNT; xi++)
    print_xtion(xi); 
}
/* print_xtions() */ 




void	print_constraint(c, cc)
     struct constraint_type	*c; 
     int			cc; 
{
  int	ci;

  fprintf(RED_OUT, "%1d constraints: ", cc); 
  for (ci = 0; ci < cc; ci++) {
    if (c[ci].cstart) 
      fprintf(RED_OUT, "[%1d:%s", c[ci].cstart, VAR[CLOCK[c[ci].cstart]].NAME);
    else 
      fprintf(RED_OUT, "(%1d:0", c[ci].cstart); 
    
    if (c[ci].cstop) 
      fprintf(RED_OUT, " - %1d:%s <= %1d] ", c[ci].cstop, VAR[CLOCK[c[ci].cstop]].NAME, c[ci].bound);
    else 
      fprintf(RED_OUT, " - %1d:0 <= %1d] ", c[ci].cstop, c[ci].bound);
  }
  fprintf(RED_OUT, "\n"); 

}
/* print_constraint() */ 





void	print_sync_xtion(
	int			ixi, 
	struct sync_xtion_type	*sync_table
	)
{
  int	pi, ci, ai; 

  fprintf(RED_OUT, "++++(SYNC XTION %1d with %1d parties, status %x)+++++++++++++++++++++++++\n", 
          ixi, sync_table[ixi].party_count, sync_table[ixi].status   
          ); 
  if (sync_table[ixi].ec_representative) { 
    fprintf(RED_OUT, "ec_rep[MODL]=%1d, ec_rep[SPEC]=%1d\n", 
      sync_table[ixi].ec_representative[FLAG_GAME_MODL], 
      sync_table[ixi].ec_representative[FLAG_GAME_SPEC]
    ); 
  } 
  for (pi = 0; pi < sync_table[ixi].party_count; pi++) {
    fprintf(RED_OUT, "  %1d: (p%1d:x%1d) ", 
      pi, 
      sync_table[ixi].party[pi].proc, 
      sync_table[ixi].party[pi].xtion
    ); 
    print_xtion_line(
      sync_table[ixi].party[pi].xtion, 
      sync_table[ixi].party[pi].proc
    );
    fprintf(RED_OUT, "\n");
/*
    fprintf(RED_OUT, "  %1d: (p%1d:x%1d): the prepared sync statement:\n", 
      pi, 
      sync_table[ixi].party[pi].proc, 
      sync_table[ixi].party[pi].xtion
    ); 
    print_statement_line(
      sync_table[ixi].party[pi].statement, 
      sync_table[ixi].party[pi].proc
    );
    fprintf(RED_OUT, "\n");
*/
    fflush(RED_OUT);
  }
  fprintf(RED_OUT, "  %1d quantified sync variables: \n    ", 
    sync_table[ixi].qfd_sync_count
  ); 
  for (ai = 0; ai < sync_table[ixi].qfd_sync_count; ai++) 
    fprintf(RED_OUT, "(%1d:%s:%1d)", sync_table[ixi].qfd_sync[ai].vi, 
	    VAR[sync_table[ixi].qfd_sync[ai].vi].NAME, 
	    sync_table[ixi].qfd_sync[ai].value
	    ); 
  fprintf(RED_OUT, "\n"); 

  fprintf(RED_OUT, "  %1d fairness checks: ", sync_table[ixi].occ_vi_count); 
  for (ci = 0; ci < sync_table[ixi].occ_vi_count; ci++) 
    fprintf(RED_OUT, "%1d:%s; ", sync_table[ixi].occ_vi[ci], 
	    VAR[sync_table[ixi].occ_vi[ci]].NAME
	    ); 
  fprintf(RED_OUT, "\n  red_events:\n"); 
  red_print_graph(sync_table[ixi].red_events);
  fprintf(RED_OUT, "  red_trigger:\n"); 
  red_print_graph(sync_table[ixi].red_trigger);
  fprintf(RED_OUT, "  red_post:\n"); 
  red_print_graph(sync_table[ixi].red_post);
  fprintf(RED_OUT, "\n"); 

  fprintf(RED_OUT, "\n-----------------------------------------------\n");

}
/* print_sync_xtion() */





void	print_sync_xtion_lines(
	int			ixi, 
	struct sync_xtion_type	*sync_table
	)
{
  int	pi, ci, ai; 

  fprintf(RED_OUT, "++++(SYNC XTION %1d with %1d parties, status %x)+++++++++++++++++++++++++\n", 
          ixi, sync_table[ixi].party_count, sync_table[ixi].status   
          ); 
  for (pi = 0; pi < sync_table[ixi].party_count; pi++) {
    fprintf(RED_OUT, "  %1d: (p%1d:x%1d) ", 
      pi, 
      sync_table[ixi].party[pi].proc, 
      sync_table[ixi].party[pi].xtion
    ); 
    print_xtion_line(
      sync_table[ixi].party[pi].xtion, 
      sync_table[ixi].party[pi].proc
    );
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
  }
}
/* print_sync_xtion_lines() */


void	print_sync_xtion_ptr(
  struct sync_xtion_type	*sxp
) {
  int	pi, ci, ai; 

  fprintf(RED_OUT, "++++(SYNC XTION %1d with %1d parties, status %x)+++++++++++++++++++++++++\n", 
          sxp->index, sxp->party_count, sxp->status  
          ); 
  for (pi = 0; pi < sxp->party_count; pi++) {
    fprintf(RED_OUT, "  %1d: (p%1d:x%1d)", pi, sxp->party[pi].proc, sxp->party[pi].xtion); 
    print_xtion_line(sxp->party[pi].xtion, sxp->party[pi].proc);
    fprintf(RED_OUT, "\n");
    print_statement_line(sxp->party[pi].statement, sxp->party[pi].proc);
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
  }
  fprintf(RED_OUT, "  %1d quantified sync variables: \n    ", sxp->qfd_sync_count); 
  for (ai = 0; ai < sxp->qfd_sync_count; ai++) 
    fprintf(RED_OUT, "(%1d:%s:%1d)", sxp->qfd_sync[ai].vi, 
	    VAR[sxp->qfd_sync[ai].vi].NAME, 
	    sxp->qfd_sync[ai].value
	    ); 
  fprintf(RED_OUT, "\n"); 
  
  fprintf(RED_OUT, "  %1d fairness checks: ", sxp->occ_vi_count); 
  for (ci = 0; ci < sxp->occ_vi_count; ci++) 
    fprintf(RED_OUT, "%1d:%s; ", sxp->occ_vi[ci], 
	    VAR[sxp->occ_vi[ci]].NAME
	    ); 
  fprintf(RED_OUT, "\n  red_events:\n"); 
  red_print_graph(sxp->red_events);
  fprintf(RED_OUT, "  red_trigger:\n"); 
  red_print_graph(sxp->red_trigger);
  fprintf(RED_OUT, "  red_post:\n"); 
  red_print_graph(sxp->red_post);
  fprintf(RED_OUT, "\n"); 

  fprintf(RED_OUT, "\n-----------------------------------------------\n");

}
/* print_sync_xtion_ptr() */



void	print_sync_xtions(sname, sync_table, sxi_count) 
  char				*sname; 
  struct sync_xtion_type	*sync_table; 
  int				sxi_count; 
{ 
  int	si; 
  
  fprintf(RED_OUT, "\n\n***%1d %s SYNC XTIONS:\n\n", sxi_count, sname); 
  for (si = 0; si < sxi_count; si++) 
    print_sync_xtion(si, sync_table); 
  fprintf(RED_OUT, "\n"); 
}
  /* print_sync_xtions() */ 





// The following structures are for the computation of system elapsed time.
struct timeval 		SYSTEM_START_TIME;
struct timezone 	TIME_ZONE_P;


double	red_system_time() { 
  struct timeval  	system_end_time;
  double         	f;
  int			len_s, len_us; 

  /* get system ending time */
  gettimeofday(&system_end_time, &TIME_ZONE_P);
  if (system_end_time.tv_usec >= SYSTEM_START_TIME.tv_usec >= 0) {
    len_s = system_end_time.tv_sec - SYSTEM_START_TIME.tv_sec; 
    len_us = system_end_time.tv_usec - SYSTEM_START_TIME.tv_usec;
  }
  else {
    len_s = system_end_time.tv_sec - SYSTEM_START_TIME.tv_sec-1; 
    len_us = system_end_time.tv_usec - SYSTEM_START_TIME.tv_usec +1000000;
  }	
  f = ((double) len_s) + (((double) len_us) / 1000000);
  return(f); 
} 
  /* red_system_time() */ 





double 	red_user_time() {
  struct rusage 	usage;
  double         	f;
  int			i, fr; 

  getrusage(RUSAGE_SELF, &usage);

  i = usage.ru_utime.tv_sec; 
  fr = usage.ru_utime.tv_usec; 
/*
  fprintf(RED_OUT, "user time %1d + (%1d/1000000) = \n", 
    i, fr
  ); 
*/
  do { 
    f = ((double) i) + (((double) fr) / 1000000);
/*
    fprintf(RED_OUT, "  %f\n", f); 
*/
  } 
  while (isnan(f)); 

  return(f); 
}
/* red_user_time() */





void 	pps(struct ps_exp_type *psub) {
  print_parse_subformula(psub); 
  printf("\n"); 
}
  /* pps() */ 


void	pnl() { 
  printf("\n"); 
} 
  /* pnl() */ 


void	phex(int i) { 
  printf("%x\n", i); 
} 
  /* phex() */ 


void	psl(
  struct statement_type 	*st, 
  int				pi
) { 
  print_statement_line(st, pi); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
}
  /* psl() */ 


int	leng_string_var(head, tail, f, args) 
	char	*head, *tail, *f; 
	va_list	args; 
{ 
  int		i, len, real_len, j, v, d; 
  char		*real_f, *s; 
  double	dfl; 
  float 	fl;
  
  real_len = len = strlen(f);  
  if (head) 
    real_len = real_len + strlen(head); 
  if (tail) 
    real_len = real_len + strlen(tail); 
    
//  fprintf(RED_OUT, "** red_diagraming format %s:", f); 
  for (i = 0; i < len; i++) { 
    if (f[i] == '%') { 
      for (; f[i+1] >= '0' && f[i+1] <= '9'; i++, real_len--) ;  
      switch (f[i+1]) { 
      case '\0': 
      	real_len--; 
      	i = len; 
      	break; 
      case 'd': 
      	v = va_arg(args, int); 
//      fprintf(RED_OUT, " %1d", v); 
      	real_len = real_len - 2 + intlen(v); 
        i++; 
      	break;       	
      case 's': 
      	s = va_arg(args, char *); 
//      	fprintf(RED_OUT, " '%s'", s); 
      	real_len = real_len - 2 + strlen(s); 
        i++; 
      	break; 
      case 'f': 
      	dfl = va_arg(args, double); 
      	v = (int) dfl; 
      	real_len = real_len 
      	- 2 // %f
      	+ intlen(v) // integer part 
      	+ 1 // decimal points
      	+ 6 ; // 6-digit precision in the fractional part.  
      	break; 
      default: 
        real_len--; 
        i++; 
        break; 
      }
    } 	
  } 
  return(real_len); 
}
  /* leng_string_var() */ 




  
char	*string_var_given_length(real_len, head, tail, f, args) 
	int	real_len; 
	char	*head, *tail, *f; 
	va_list	args; 
{ 
  float		fl;
  int		i, len, j, v, d; 
  char		*s; 
  double	dfl; 
  
//  fprintf(RED_OUT, "\n"); 
//  fprintf(RED_OUT, "real_len = %1d\n", real_len); 
  if (inbuf_size < real_len + 3) { 
    free(inbuf); 
    inbuf_size = 2*inbuf_size; 
    if (inbuf_size < real_len + 3) 
      inbuf_size = real_len + 3; 
    inbuf = (char *) malloc(inbuf_size); 	
  } 
/*
  fprintf(RED_OUT, "The size of inbuf=%1d\n", real_len+19); 
*/
  len = strlen(f); 
  if (head) {
    sprintf(inbuf, "%s", head); 
    j = strlen(head); 
  }
  else 
    j = 0; 
  for (i = 0; i < len; i++) { 
    if (f[i] != '%') { 
//      fprintf(RED_OUT, "fill '%c' to position %1d\n", f[i], j); 
      inbuf[j] = f[i]; 
      j++; 
    }
    else { 
      for (; f[i+1] >= '0' && f[i+1] <= '9'; i++) ;  
      switch (f[i+1]) { 
      case '\0': 
//        fprintf(RED_OUT, "end of the format string at position %1d\n", i); 
      	i = len; 
      	break; 
      case 'd': 
      	v = va_arg(args, int); 
//        fprintf(RED_OUT, "fill %d to position %1d\n", v, j); 
        sprintf(&(inbuf[j]), "%1d", v); 
      	j = j + intlen(v); 
        i++; 
      	break;       	
      case 's': 
      	s = va_arg(args, char *); 
//        fprintf(RED_OUT, "fill %s to position %1d\n", s, j); 
      	sprintf(&(inbuf[j]), "%s", s); 
      	j = j + strlen(s);  
        i++; 
      	break; 
      case 'f': 
      	dfl = va_arg(args, double); 
      	sprintf(&(inbuf[j]), "%.6f", dfl); 
      	break; 
      default: 
//        fprintf(RED_OUT, "fill %c to position %1d\n", f[i], j); 
        inbuf[j] = f[i]; 
        i++; 
        break; 
      }
    } 	
  } 
  if (tail) {
    sprintf(&(inbuf[j]), "%s", tail); 
    j = j + strlen(tail); 
  }
  sprintf(&(inbuf[j]), "\0\0"); 
  j = j + 2; 
  inbuf[j] = '\0'; 
  
  return(inbuf); 
}
  /* string_var_given_length() */ 
  




double 
  acc_hash_time = (double) 0, 
  start_hash_time = (double) 0, 
  acc_act_time = 0, 
  start_act_time = 0, 
  acc_norm_time = 0, 
  start_norm_time = 0, 
  acc_time_time = 0,  
  start_time_time = 0; 

int 
  count_acc_hash = 0, 
  count_acc_act = 0, 
  count_acc_norm = 0, 
  count_acc_time = 0; 


double	reset_acc_time(
  int	flag_acc
) { 
  switch (flag_acc) { 
  case FLAG_ACC_HASH_TIME: 
    start_hash_time = red_user_time(); 
/*
    fprintf(RED_OUT, ">> reset time %f <<\n", start_hash_time); 
*/
    return(start_hash_time); 
    break; 	
  case FLAG_ACC_ACT_TIME: 
    start_act_time = red_user_time(); 
    return(start_act_time); 
    break; 	
  case FLAG_ACC_NORM_TIME: 
    start_norm_time = red_user_time(); 
    return(start_norm_time); 
    break; 	
  case FLAG_ACC_TIME_TIME: 
    start_time_time = red_user_time(); 
    return(start_time_time); 
    break; 
  } 
} 
  /* reset_acc_time() */ 



double	update_acc_time(
  int	flag_acc, 
  int	flag_report 
) { 
  double	now, inctime; 

  ++count_acc_hash; 
  now = red_user_time(); 
/*
  fprintf(RED_OUT, "\n** st %f, now %f **, acc %f\n", 
    start_hash_time, now, acc_hash_time
  ); 
*/  
  switch (flag_acc) { 
  case FLAG_ACC_HASH_TIME: 
    inctime = now - start_hash_time; 
    start_hash_time = now; 
    acc_hash_time = acc_hash_time + inctime; 
    if (flag_report) 
      fprintf(RED_OUT, "\nTime HASH %1d, inc %f, acc %f\n", 
        count_acc_hash, inctime, acc_hash_time
      ); 
    break; 	
  case FLAG_ACC_ACT_TIME: 
    inctime = now - start_act_time; 
    start_act_time = now; 
    acc_act_time = acc_act_time + inctime; 
    if (flag_report) 
      fprintf(RED_OUT, "\nTime ACT %1d, inc %1.3f, acc %1.3f\n", 
        count_acc_act, inctime, acc_act_time
      ); 
    break; 	
  case FLAG_ACC_NORM_TIME: 
    inctime = now - start_norm_time; 
    start_norm_time = now; 
    acc_norm_time = acc_norm_time + inctime; 
    if (flag_report) 
      fprintf(RED_OUT, "\nTime NORM %1d, inc %1.3f, acc %1.3f\n", 
        count_acc_norm, inctime, acc_norm_time
      ); 
    break; 	
  case FLAG_ACC_TIME_TIME: 
    inctime = now - start_time_time; 
    start_time_time = now; 
    acc_time_time = acc_time_time + inctime; 
    if (flag_report) 
      fprintf(RED_OUT, "\nTime TIME %1d, inc %1.3f, acc %1.3f\n", 
        count_acc_time, inctime, acc_time_time
      ); 
    break; 
  } 
} 
  /* update_acc_time() */ 
  

void	print_acc_time(
  int	flag_acc  
) { 
  switch (flag_acc) { 
  case FLAG_ACC_HASH_TIME: 
    fprintf(RED_OUT, "\nTime HASH %1d, acc %1.3f\n", 
      count_acc_hash, acc_hash_time
    ); 
    break; 	
  case FLAG_ACC_ACT_TIME: 
    fprintf(RED_OUT, "\nTime ACT %1d, acc %1.3f\n", 
      count_acc_act, acc_act_time
    ); 
    break; 	
  case FLAG_ACC_NORM_TIME: 
    fprintf(RED_OUT, "\nTime NORM %1d, acc %1.3f\n", 
      count_acc_norm, acc_norm_time
    ); 
    break; 	
  case FLAG_ACC_TIME_TIME: 
    fprintf(RED_OUT, "\nTime TIME %1d, acc %1.3f\n", 
      count_acc_time, acc_time_time
    ); 
    break; 
  } 
} 
  /* print_acc_time() */ 
  


void 	print_simple_time()
{
  printf("RED TIME: user:%1fsec;\n", red_user_time());
}
/* print_simple_time() */




void 	print_cpu_time(char *f, ...)
{
  char		*real_f; 
  va_list	args; 
  
  string_var(real_f, NULL, NULL, f, args);  
  fprintf(RED_OUT, "RED TIME:system:%1fsec; user:%1fsec; %s\n", 
    red_system_time(), red_user_time(), real_f 
  );
  /*
  fprintf(RED_OUT, "[SHARED:%1d; DATA:%1d; STACK:%1d]%%%%\n", usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
  */
  fflush(RED_OUT); 
}
/* print_cpu_time() */




void 	old_print_cpu_time(char *f, ...)
{
  struct timeval  	system_end_time;
  struct rusage 	usage;
  float         	fl;
  int			i, len, real_len, j, v; 
  char			*real_f, *stfile_name, *s; 
  FILE			*stfile; 
  struct ps_exp_type	*e; 
  
  va_list		args; 
  
  real_len = len = strlen(f);  
//  fprintf(RED_OUT, "** red_diagraming format %s:", f); 
  va_start(args, f); 
  for (i = 0; i < len; i++) { 
    if (f[i] == '%') { 
      switch (f[i+1]) { 
      case '\0': 
      	real_len--; 
      	i = len; 
      	break; 
      case 'd': 
      	v = va_arg(args, int); 
//      fprintf(RED_OUT, " %1d", v); 
      	real_len = real_len - 2 + intlen(v); 
        i++; 
      	break;       	
      case 's': 
      	s = va_arg(args, char *); 
//      	fprintf(RED_OUT, " '%s'", s); 
      	real_len = real_len - 2 + strlen(s); 
        i++; 
      	break; 
      default: 
        real_len--; 
        i++; 
        break; 
      }
    } 	
  } 
  va_end(args); 
//  fprintf(RED_OUT, "\n"); 
//  fprintf(RED_OUT, "real_len = %1d\n", real_len); 
  real_f = malloc(real_len + 1); 
  va_start(args, f); 
  for (i = 0, j = 0; i < len; i++) { 
    if (f[i] != '%') { 
//      fprintf(RED_OUT, "fill '%c' to position %1d\n", f[i], j); 
      real_f[j] = f[i]; 
      j++; 
    }
    else { 
      switch (f[i+1]) { 
      case '\0': 
//        fprintf(RED_OUT, "end of the format string at position %1d\n", i); 
      	i = len; 
      	break; 
      case 'd': 
      	v = va_arg(args, int); 
//        fprintf(RED_OUT, "fill %d to position %1d\n", v, j); 
        sprintf(&(real_f[j]), "%1d", v); 
      	j = j + intlen(v); 
        i++; 
      	break;       	
      case 's': 
      	s = va_arg(args, char *); 
//        fprintf(RED_OUT, "fill %s to position %1d\n", s, j); 
      	sprintf(&(real_f[j]), "%s", s); 
      	j = j + strlen(s);  
        i++; 
      	break; 
      default: 
//        fprintf(RED_OUT, "fill %c to position %1d\n", f[i], j); 
        real_f[j] = f[i]; 
        i++; 
        break; 
      }
    } 	
  } 
  real_f[j] = '\0'; 
  va_end(args); 
  
  fprintf(RED_OUT, "~~(time: %s, system:%1fsec; user:%1fsec)~~~~~~~~~~~\n", 
    real_f, red_system_time(), red_user_time()
  );
  /*
  fprintf(RED_OUT, "[SHARED:%1d; DATA:%1d; STACK:%1d]%%%%\n", usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
  */
  fflush(RED_OUT); 
}
/* print_cpu_time() */





int	red_memory() { 
  return(MAX_MEM); 
}
  /* red_memory() */  





void	print_resources(char *f, ...) { 
  char		*real_f; 
  va_list	args; 
  
  string_var(real_f, NULL, NULL, f, args);  
  fprintf(RED_OUT, "** red[%s]: sys-time: %1.6fs, user-time: %1.6fs, memory: %1dbytes.\n", 
    real_f, red_system_time(), red_user_time(), red_memory() 
  ); 
}
  /* print_resources() */ 





memory_fault_test()
{
  int	i;
  char	*c;

  fprintf(RED_OUT, "\nStarting memory fault testing.\n");
  for (i = 10000; i; i--) {
    if (malloc(1) == NULL) {
      fprintf(RED_OUT, "\nFault detected.\n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0); 
    }
  }

  fprintf(RED_OUT, "\nMemory allocation test OK!\n"); 
}
/* memory_fault_test() */






char	*str_arith_op(op) 
     int	op;
{
  switch (op) {
  case ARITH_ADD: 
    return("+"); 
  case ARITH_MINUS: 
    return("-"); 
  case ARITH_MULTIPLY: 
    return("*");
  case ARITH_DIVIDE:
    return("/"); 
  default: 
    return("???"); 
  }
}
/* str_arith_op() */


char	*str_ineq_op(op) 
     int	op; 
{
  switch (op) {
  case LESS: 
    return("<");
  case LEQ: 
    return("<="); 
  case EQ: 
    return("="); 
  case NEQ:
    return("!="); 
  case GEQ: 
    return(">=");
  case GREATER:
    return(">"); 
  default: 
    return("???"); 
  }
}
/* str_ineq_op() */ 


int	intlen(i)
     int	i; 
{
  int	d; 

  if (i==0)
    return(1); 
  else if (i < 0) 
    d = 1; 
  else 
    d = 0; 

  for (; i; i = i / 10, d++) ; 

  return(d);
}
/* intlen() */ 



int	hexlen(x)
     int	x; 
{
  int	len, m; 

  if (x & 0xF0000000) 
    return(8); 
  
  m = 0x0F000000; 
  for (len = 7; len > 1; len--) 
    if (x & m)
      return(len); 
    else 
      m = m >> 4; 
  return(1);
}
/* hexlen() */ 



char	*itos(i)
     int	i;
{
  int	len;
  char	*s; 

  len = intlen(i)+1; 
  s = (char *) malloc(len); 
  s[len-1] = '\0'; 

  if (i < 0) 
    s[0] = '-';

  for (len = len-2; i; len--) {
    s[len] = (char) ((int) '0' + (i % 10)); 
    i = i / 10;
  }
  return(s); 
}
/* itos() */ 



compare_CDD(d) 
	struct red_type	*d; 
{ 
  float f;
  fprintf(RED_OUT, "\nCompare the sizes of CRD and CDD of %x.\n", 
    (unsigned int) d
  ); 
  fprintf(RED_OUT, "\nFor CRD:\n"); 
  f = red_size(d, SIZE_REPORT, NULL, NULL);
  fprintf(RED_OUT, "\nFor CDD:\n"); 
  f = red_size(red_CDD(d), SIZE_REPORT, NULL, NULL)/f; 
  fprintf(RED_OUT, "\nratio CDD/CRD = %1f\n", f);
}
/* compare_CDD() */ 










struct red_type	*debug_filter(d)
	struct red_type	*d;
{
  struct red_type	*filter;

  filter = NORM_NO_RESTRICTION;
  filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_POINTER][0][0], 2, 2));
  filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][1][0], 1, 1));
  filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 6, 6));
  filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 6, 6));
  filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][4][0], 7, 7));
  return(red_bop(AND, d, filter));
}
  /* debug_filter() */










int	int_min(a,b)
     int	a, b;
{
  if (a < b)
    return(a);
  else
    return(b);
}
/* int_min() */


int	int_max(a,b)
     int	a, b; 
{
  if (a < b)
    return(b); 
  else 
    return(a);
}
/* int_max() */



float	flt_min(
  float	a,
  float	b
) {
  if (a < b)
    return(a);
  else
    return(b);
}
/* flt_min() */


float	flt_max(
  float	a,
  float	b
) {
  if (a < b)
    return(b); 
  else 
    return(a);
}
/* flt_max() */



float	feps_plus(float f) { 
  int	e; 
  float	m, rfm; 
  
  if (f == 0.0) 
    return(FLT_MIN); 
  else if (f == -1 * FLT_MIN) 
    return(0.0); 
    
  // m = 
  frexp(f, &e); 
//  fprintf(RED_OUT, "\n==========\nf=%e, \nf=%f\n", f, f); 
//  fprintf(RED_OUT, "m=%e, \nm=%f\n", m, m); 
//  fprintf(RED_OUT, "e=%1d\n", e); 
  rfm = ldexp(0.5, e-FLT_EXP_DOWN); 
//  fprintf(RED_OUT, "rfm=%e, \nrfm=%f\n", rfm, rfm); 
  rfm = f+rfm; 
//  fprintf(RED_OUT, "f+rfm=%e, \nf+rfm=%f\n", rfm, rfm); 
  if (rfm == f) { 
    fprintf(RED_OUT, "\nFail to get epsilon plus of %.40f\n", f); 
    bk(0); 
  } 
  return(rfm); 
} 
  /* feps_plus() */ 





float	feps_minus(float f) { 
  int	e; 
  float	rfm, t; 
  
  if (f == 0.0) 
    return(-1*FLT_MIN); 
  else if (f == FLT_MIN) 
    return(0.0); 
    
  frexp(f, &e); 
  rfm = ldexp(0.5, e-FLT_EXP_DOWN); 
  t = f-rfm; 
  if (t == f) { 
    fprintf(RED_OUT, "\nFailed to get at e-%1d=%1d-%1d=%1d\n", 
      FLT_EXP_DOWN, e, FLT_EXP_DOWN, e-FLT_EXP_DOWN 
    ); 
    fprintf(RED_OUT, " epsilon %.50e\n", rfm); 
    fprintf(RED_OUT, " plus    %.50e\n", t); 
    fprintf(RED_OUT, " of      %.50e\n", f); 
    bk(0); 
  } 
  return(t); 
} 
  /* feps_minus() */ 





double	dble_min(
  double	a,
  double 	b
) {
  if (a < b)
    return(a);
  else
    return(b);
}
/* dble_min() */


int	dble_max(
  double	a, 
  double 	b
) {
  if (a < b)
    return(b); 
  else 
    return(a);
}
/* dble_max() */








double	dfeps_plus(double f) { 
  int		e; 
  double	rfm; 
  
  if (f == 0.0) 
    return(DBL_MIN); 
  else if (f == -1 * DBL_MIN) 
    return(0.0); 
    
  frexp(f, &e); 
  rfm = ldexp(0.5, e-DBL_EXP_DOWN); 
  rfm = f+rfm; 
  if (rfm == f) { 
    fprintf(RED_OUT, "\nFail to get epsilon plus of %.40f\n", f); 
    bk(0); 
  } 
  return(rfm); 
} 
  /* dfeps_plus() */ 





double	dfeps_minus(double f) { 
  int		e; 
  double	rfm; 
  
  if (f == 0.0) 
    return(-1*DBL_MIN); 
  else if (f == DBL_MIN) 
    return(0.0); 
    
  frexp(f, &e); 
  rfm = ldexp(0.5, e-DBL_EXP_DOWN); 
  rfm = f-rfm; 
  if (rfm == f) { 
    fprintf(RED_OUT, "\nFail to get epsilon plus of %.40f\n", f); 
    bk(0); 
  } 
  return(rfm); 
} 
  /* dfeps_minus() */ 








test_clocks(cc) 
int	cc;
{
  struct red_type	*conj, *result; 
  int	i, j; 

  result = NORM_FALSE; 
  for (i = 1; i <= cc; i++) { 
    conj = NORM_NO_RESTRICTION; 
    for (j = 1; j <= cc; j++) 
      conj = red_bop(AND, conj, 
        ddd_atom(VAR[ZONE[j][0]].U.CRD.CORRESPONDING_CDD_VI, 
        10*((i+j)%cc), 20*cc+10*((i+j)%cc))
      ); 

    if (cc < 4) {
      fprintf(RED_OUT, "\n%1d:============================\nTest Restriction\n==========================\n", i); 
      fprintf(RED_OUT, "conj:\n");
      red_print_graph(conj);
    }
    result = red_bop(OR, result, conj); 
  }

  fprintf(RED_OUT, "\nresult of %1d clocks:", cc);
  red_size(result, SIZE_REPORT, NULL, NULL);
  if (cc < 4) 
    red_print_graph(result); 

  fflush(RED_OUT);
}
/* test_clocks() */


struct red_type	*extract_one_instance(w)
     int	w;
{
  struct red_type		*d, *result;
  int				ci;
  /*
  fprintf(RED_OUT, "\nIn locate an instance() with d:\n");
  red_print_graph(d);
  */
  if (RT[w] == NORM_FALSE)
    return(RT[w]);

  result = NORM_NO_RESTRICTION;

  for (d = RT[w]; d != NORM_NO_RESTRICTION; ) {
    switch (VAR[d->var_index].TYPE) {
    case TYPE_CRD:
      ci = d->u.crd.child_count-1;
      result = red_bop(AND, result,
		       crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)
		       );
      d = d->u.crd.arc[ci].child;
      break;
    case TYPE_HRD:
      ci = d->u.hrd.child_count-1;
      result = hrd_one_constraint(result, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      d = d->u.hrd.arc[ci].child;
      break;
    case TYPE_FLOAT:
      ci = d->u.fdd.child_count-1;
      result = fdd_one_constraint(result, d->var_index, 
        d->u.fdd.arc[ci].upper_bound, d->u.fdd.arc[ci].upper_bound
      );
      d = d->u.fdd.arc[ci].child;
      break;
    case TYPE_DOUBLE:
      ci = d->u.dfdd.child_count-1;
      result = fdd_one_constraint(result, d->var_index, 
        d->u.dfdd.arc[ci].upper_bound, d->u.dfdd.arc[ci].upper_bound
      );
      d = d->u.dfdd.arc[ci].child;
      break;
    default:
      ci = d->u.ddd.child_count-1;
      result = ddd_one_constraint(result, d->var_index, 
        d->u.ddd.arc[ci].upper_bound, d->u.ddd.arc[ci].upper_bound
      );
      d = d->u.ddd.arc[ci].child;
    }
  }

  RT[w] = red_bop(EXCLUDE, RT[w], result);

  return(result);
}
/* extract_one_instance() */




void	debug_trace_bck(sxi, initial_trace_index)
	int	sxi, initial_trace_index;
{
  struct trace_frame_type	*cur_tf, *prev_tf, *old_stack;
  int				tfi, w, explore, tmp_reachable, flag, 
				flag_result;
  struct red_type		*conj;

  RT[tmp_reachable = RT_TOP++] = RT[REACHABLE];
  RT[REACHABLE] = NORM_FALSE;

  TRACE_FRAME_STACK->sync_xtion_index = sxi;
  RT[w = RT_TOP++] = TRACE_FRAME_STACK->sync_xtion[sxi].red_precond;
  for (tfi = 0; tfi <= initial_trace_index; tfi++) {
    TRACE_FRAME_STACK->sync_xtion[sxi].red_precond = extract_one_instance(w);
/*
    fprintf(RED_OUT, "\nThe initial trace at %1d:\n", tfi);
    red_print_graph(TRACE_FRAME_STACK->sync_xtion[sxi].red_precond);
*/
  }
  red_mark(TRACE_FRAME_STACK->sync_xtion[sxi].red_precond, FLAG_GC_STABLE);
  fprintf(RED_OUT, "\nThe initial trace:\n");
  red_print_graph(TRACE_FRAME_STACK->sync_xtion[sxi].red_precond);

  for (cur_tf = TRACE_FRAME_STACK; cur_tf->nr > 1; ) {
/*
    fprintf(RED_OUT, "tfi=%1d, TF4.SXI10: postcondition:\n", cur_tf->nr);
    red_print_graph(TF4->sync_xtion[10].red_postcond);
*/
    sxi = cur_tf->sync_xtion_index;
    RT[w] = cur_tf->sync_xtion[sxi].red_postcond;
/*
    fprintf(RED_OUT, "===== tfi=%1d =================================\nChecking sync xtion consistency with precondition:\n",
	    cur_tf->nr
	    );
    red_print_graph(cur_tf->sync_xtion[sxi].red_precond);
*/
    RT[explore = RT_TOP++] = extract_one_instance(w);
/*
    fprintf(RED_OUT, "1. against postcondition:\n");
    red_print_graph(RT[explore]);
*/
    conj = red_precondition_sync_SPECIFIC(
      explore, 
      NULL, DECLARED_GLOBAL_INVARIANCE, 
      NORM_FALSE, NORM_FALSE, 
      &(SYNC_XTION[sxi]), 
      &flag_result, 
      TYPE_TRUE // for postprocessing  
    );
/*
    fprintf(RED_OUT, "2. against postcondition execution result:\n");
    red_print_graph(conj);
*/
    for (;
	    RT[explore] != NORM_FALSE
	 && red_bop(INTERSECT, conj, cur_tf->sync_xtion[sxi].red_precond)
	    != cur_tf->sync_xtion[sxi].red_precond;
	 ) {
/*
      fprintf(RED_OUT, "\n\n\n****************************\nComparing precondition: \n");
      red_print_graph(cur_tf->sync_xtion[sxi].red_precond);
*/
      RT[explore] = extract_one_instance(w);
/*
      fprintf(RED_OUT, "1. against postcondition:\n");
      red_print_graph(RT[explore]);
*/
      conj = red_precondition_sync_SPECIFIC(
      	explore, 
      	NULL, DECLARED_GLOBAL_INVARIANCE, 
      	NORM_FALSE, 
      	NORM_FALSE, 
      	&(SYNC_XTION[sxi]), 
      	&flag_result, 
      	TYPE_TRUE // for postprocessing  
      );
/*
      fprintf(RED_OUT, "2. against postcondition execution result:\n");
      red_print_graph(conj);
*/
    }
    if (RT[explore] == NORM_FALSE) {
      bk("Error: fails to locate the postcondition for the precondition.\n"); 
    }
    cur_tf->sync_xtion[sxi].red_postcond = RT[explore];
    RT_TOP--; /* explore */
    red_mark(cur_tf->sync_xtion[sxi].red_postcond, FLAG_GC_STABLE);

    prev_tf = cur_tf->prev_trace_frame;

    fprintf(RED_OUT, "===== tfi=%1d at sxi=%1d's postcondition =====\n",
	    cur_tf->nr, cur_tf->sync_xtion_index
	    );
    red_print_graph(cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_postcond);

    for (sxi = 0; sxi <= SYNC_XTION_COUNT; sxi++) {
/*
      fprintf(RED_OUT, "Testing with sxi=%1d's precondition:\n", sxi);
      red_print_graph(prev_tf->sync_xtion[sxi].red_precond);
*/
      RT[w] = prev_tf->sync_xtion[sxi].red_precond;
      RT[explore = RT_TOP++] = extract_one_instance(w);
      for (;
	      RT[explore] != NORM_FALSE
	   && red_bop(AND, RT[explore],
		      cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_postcond
		      )
	      != cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_postcond
	   ; ) {
	RT[explore] = extract_one_instance(w);
      }
      if (RT[explore] == NORM_FALSE) {
        RT_TOP--; /* explore */
      }
      else {
        prev_tf->sync_xtion[sxi].red_precond = RT[explore];
	RT_TOP--; /* explore */
	red_mark(prev_tf->sync_xtion[sxi].red_precond, FLAG_GC_STABLE);
	prev_tf->sync_xtion_index = sxi;
	cur_tf = prev_tf;
        break;
      }
    }
    if (sxi > SYNC_XTION_COUNT) {
      bk("\nThere is something wrong in debug_trace_bck().\n"); 
    }
  }
  RT_TOP--; /* w */

  for (old_stack = TRACE_FRAME_STACK, TRACE_FRAME_STACK = NULL; old_stack; ) {
    prev_tf = old_stack;
    old_stack = prev_tf->prev_trace_frame;
    prev_tf->prev_trace_frame = TRACE_FRAME_STACK;
    TRACE_FRAME_STACK = prev_tf;
  }

  fprintf(RED_OUT, "\n========================\nDebug trace: \n");
  for (cur_tf = TRACE_FRAME_STACK; cur_tf; cur_tf = cur_tf->prev_trace_frame) {
    int	pti;

    sxi = cur_tf->sync_xtion_index;
    fprintf(RED_OUT, "\n************************\nPOST CONDITION %1d:\n", cur_tf->nr);
    red_print_line(cur_tf->sync_xtion[sxi].red_postcond);
    fprintf(RED_OUT, "\n---------------\n  ^\n  |SXI:%1d\n", sxi);
    fflush(RED_OUT);
    for (pti = 0; pti < SYNC_XTION[sxi].party_count; pti++) {
      fprintf(RED_OUT, "  | ");
      print_xtion_line(SYNC_XTION[sxi].party[pti].xtion, SYNC_XTION[sxi].party[pti].proc);
      fprintf(RED_OUT, "\n");
    }
    fprintf(RED_OUT, "  |\n  |\n  |\nPRE CONDITION %1d:\n", cur_tf->nr);
    red_print_line(cur_tf->sync_xtion[sxi].red_precond);
    fflush(RED_OUT);
  }

  RT_TOP--; /* tmp_reachable */
  exit(0);
}
  /* debug_trace_bck() */



void	debug_trace_fwd(sxi, initial_trace_index)
	int	sxi, initial_trace_index;
{
  struct trace_frame_type	*cur_tf, *prev_tf, *old_stack;
  int				tfi, exi, w, explore, tmp_reachable, flag;
  struct red_type		*conj;

  RT[tmp_reachable = RT_TOP++] = RT[REACHABLE];
  RT[REACHABLE] = NORM_FALSE;

  TRACE_FRAME_STACK->sync_xtion_index = sxi;
  RT[w = RT_TOP++] = TRACE_FRAME_STACK->sync_xtion[sxi].red_postcond;
  for (tfi = 0; tfi <= initial_trace_index; tfi++) {
    TRACE_FRAME_STACK->sync_xtion[sxi].red_postcond = extract_one_instance(w);

    fprintf(RED_OUT, "\nThe final trace at %1d:\n", tfi);
    red_print_graph(TRACE_FRAME_STACK->sync_xtion[sxi].red_postcond);

  }
  red_mark(TRACE_FRAME_STACK->sync_xtion[sxi].red_postcond, FLAG_GC_STABLE);
  fprintf(RED_OUT, "\nThe final trace:\n");
  red_print_graph(TRACE_FRAME_STACK->sync_xtion[sxi].red_postcond);

  for (cur_tf = TRACE_FRAME_STACK; cur_tf->nr > 1; ) {
/*
    fprintf(RED_OUT, "tfi=%1d, TF4.SXI10: postcondition:\n", cur_tf->nr);
    red_print_graph(TF4->sync_xtion[10].red_precond);
*/
    sxi = cur_tf->sync_xtion_index;
    RT[w] = cur_tf->sync_xtion[sxi].red_precond;

    fprintf(RED_OUT, "===== tfi=%1d =================================\nChecking sync xtion consistency with precondition:\n",
	    cur_tf->nr
	    );
    red_print_graph(cur_tf->sync_xtion[sxi].red_postcond);

    exi = 0;
    RT[explore = RT_TOP++] = extract_one_instance(w);
/*
    fprintf(RED_OUT, "%1d:%1d:1. against precondition:\n", tfi, exi);
    red_print_graph(RT[explore]);
*/
    conj = red_postcondition_sync_SPECIFIC(
      explore, REFINED_GLOBAL_INVARIANCE, 
      NORM_FALSE, NORM_FALSE, 
      &(SYNC_XTION[sxi]), 
      TYPE_TRUE 
    );

    fprintf(RED_OUT, "%1d:%1d:2. against extracted precondition's strongest postconditon:\n", tfi, exi);
    red_print_graph(conj);

    for (exi++;
	    RT[explore] != NORM_FALSE
	 && red_bop(INTERSECT, conj, cur_tf->sync_xtion[sxi].red_postcond)
	    != cur_tf->sync_xtion[sxi].red_postcond;
	 exi++
	 ) {
/*      if (tfi == 45 && exi == 48) {
        fprintf(RED_OUT, "Caught!\n");
	fflush(RED_OUT);
        for (flag = 1; flag; );
      }
      fprintf(RED_OUT, "\n\n\n****************************\n%1d:%1d:Comparing with postcondition:\n",
	      tfi, exi
	      );
      red_print_graph(cur_tf->sync_xtion[sxi].red_postcond);
*/
      RT[explore] = extract_one_instance(w);
/*
      fprintf(RED_OUT, "%1d:%1d:1. against porecondition:\n", tfi, exi);
      red_print_graph(RT[explore]);
*/
      conj = red_postcondition_sync_SPECIFIC(
      	explore, REFINED_GLOBAL_INVARIANCE, 
      	NORM_FALSE, NORM_FALSE, 
      	&(SYNC_XTION[sxi]), 
      	TYPE_TRUE // for postprocessing 
      );

      fprintf(RED_OUT, "%1d:%1d:2. against extracted precondition's strongest postcondition:\n",
	      tfi, exi
	      );
      red_print_graph(conj);

    }
    if (RT[explore] == NORM_FALSE) {
      bk("Error: fails to locate the precondition for the postcondition.\n"); 
    }
    cur_tf->sync_xtion[sxi].red_precond = RT[explore];
    RT_TOP--; /* explore */
    red_mark(cur_tf->sync_xtion[sxi].red_precond, FLAG_GC_STABLE);

    prev_tf = cur_tf->prev_trace_frame;

    fprintf(RED_OUT, "===== tfi=%1d at sxi=%1d's precondition =====\n",
	    cur_tf->nr, cur_tf->sync_xtion_index
	    );
    red_print_graph(cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_precond);

    for (sxi = 0; sxi <= SYNC_XTION_COUNT; sxi++) {
/*
      fprintf(RED_OUT, "Testing with sxi=%1d's precondition:\n", sxi);
      red_print_graph(prev_tf->sync_xtion[sxi].red_postcond);
*/
      RT[w] = prev_tf->sync_xtion[sxi].red_postcond;
      RT[explore = RT_TOP++] = extract_one_instance(w);
      for (;
	      RT[explore] != NORM_FALSE
	   && red_bop(AND, RT[explore],
		      cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_precond
		      )
	      != cur_tf->sync_xtion[cur_tf->sync_xtion_index].red_precond
	   ; ) {
	RT[explore] = extract_one_instance(w);
      }
      if (RT[explore] == NORM_FALSE) {
        RT_TOP--; /* explore */
      }
      else {
        prev_tf->sync_xtion[sxi].red_postcond = RT[explore];
	RT_TOP--; /* explore */
	red_mark(prev_tf->sync_xtion[sxi].red_postcond, FLAG_GC_STABLE);
	prev_tf->sync_xtion_index = sxi;
	cur_tf = prev_tf;
        break;
      }
    }
    if (sxi > SYNC_XTION_COUNT) {
      bk("\nThere is something wrong in debug_trace_bck().\n"); 
    }
  }
  RT_TOP--; /* w */

  for (old_stack = TRACE_FRAME_STACK, TRACE_FRAME_STACK = NULL; old_stack; ) {
    prev_tf = old_stack;
    old_stack = prev_tf->prev_trace_frame;
    prev_tf->prev_trace_frame = TRACE_FRAME_STACK;
    TRACE_FRAME_STACK = prev_tf;
  }

  fprintf(RED_OUT, "\n========================\nDebug trace: \n");
  for (cur_tf = TRACE_FRAME_STACK; cur_tf; cur_tf = cur_tf->prev_trace_frame) {
    int	pti;

    sxi = cur_tf->sync_xtion_index;
    fprintf(RED_OUT, "\n************************\nPRE CONDITION %1d:\n", cur_tf->nr);
    red_print_line(cur_tf->sync_xtion[sxi].red_precond);
    fprintf(RED_OUT, "\n---------------\n  ^\n  |SXI:%1d\n", sxi);
    fflush(RED_OUT);
    for (pti = 0; pti < SYNC_XTION[sxi].party_count; pti++) {
      fprintf(RED_OUT, "  | ");
      print_xtion_line(SYNC_XTION[sxi].party[pti].xtion, SYNC_XTION[sxi].party[pti].proc);
      fprintf(RED_OUT, "\n");
    }
    fprintf(RED_OUT, "  |\n  |\n  |\nPOST CONDITION %1d:\n", cur_tf->nr);
    red_print_line(cur_tf->sync_xtion[sxi].red_postcond);
    fflush(RED_OUT);
  }

  RT_TOP--; /* tmp_reachable */
  exit(0);
}
  /* debug_trace_fwd() */





 


void	exit_with_summary(cpu_time_parsing, ic) 
  float	cpu_time_parsing; 
  int	ic; 
{
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
    /* calculate cpu time */
    print_resources("exit report after %1d iterations\n", ic);
    fprintf(RED_OUT, "Max data-structure memory in CRD maniplulations is %1d bytes.\n", MAX_MEM);
    fprintf(RED_OUT, "Max data-structure memory in tree maniplulations is %1d bytes.\n", MAX_TREE_USAGE);
    fprintf(RED_OUT, "Max data-structure memory in result maniplulations is %1d bytes.\n", MAX_RESULT_USAGE);
    fprintf(RED_OUT, "Max result stack height is %1d.  ", MAX_RESULT_STACK_HEIGHT);
    fprintf(RED_OUT, "Max RT height is %1d.\n", MAX_RT_HEIGHT);
  }
  fclose(RED_OUT);

  exit(0); 
} 
  /* exit_with_summary() */ 
  



void	print_summary(cpu_time_parsing) 
  float	cpu_time_parsing; 
{
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
    /* calculate cpu time */
    fprintf(RED_OUT,"** ****[Resource Summary Report after %1d Iterations]********************* **\n", 
	    ITERATION_COUNT
	    );
    print_resources("summary");
    fprintf(RED_OUT, "Max data-structure memory in CRD maniplulations is %1d bytes.\n", MAX_MEM);
    fprintf(RED_OUT, "Max data-structure memory in tree maniplulations is %1d bytes.\n", MAX_TREE_USAGE);
    fprintf(RED_OUT, "Max data-structure memory in result maniplulations is %1d bytes.\n", MAX_RESULT_USAGE);
    fprintf(RED_OUT, "Max result stack height is %1d.  ", MAX_RESULT_STACK_HEIGHT);
    fprintf(RED_OUT, "Max RT height is %1d.\n", MAX_RT_HEIGHT);
  }
} 
  /* print_summary() */ 
  


void	print_time_memory(cpu_time_parsing) 
  float	cpu_time_parsing; 
{
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
    /* calculate cpu time */
    print_resources("time & memory after %1d iterations", ITERATION_COUNT);
    fprintf(RED_OUT, "Max data-structure memory in CRD maniplulations is %1d bytes.\n", MAX_MEM);
    fprintf(RED_OUT, "Max data-structure memory in tree maniplulations is %1d bytes.\n", MAX_TREE_USAGE);
    fprintf(RED_OUT, "Max data-structure memory in result maniplulations is %1d bytes.\n", MAX_RESULT_USAGE);
    fprintf(RED_OUT, "Max result stack height is %1d.  ", MAX_RESULT_STACK_HEIGHT);
    fprintf(RED_OUT, "Max RT height is %1d.\n", MAX_RT_HEIGHT);
  }
} 
  /* print_summary() */ 
  



  

int 	GARBAGE_OVERHEAD;

void	report_red_management()
{
  int cur_mem;

  fprintf(RED_OUT, "==(I%1d;SXI%1d;SPACE REPORT)====================================================",
	  ITERATION_COUNT, ITERATE_SXI
	  );

  cur_mem = report_23tree_management(FLAG_GC_REPORT);
  cur_mem
    = cur_mem
    + GARBAGE_OVERHEAD
    + red_count*sizeof(struct red_type)
    + ichild_count*sizeof(struct ddd_child_type)
    + bchild_count*sizeof(struct crd_child_type)
    + hchild_count*sizeof(struct hrd_child_type)
    + hrd_exp_count*sizeof(struct hrd_exp_type)
    + hrd_term_count*sizeof(struct hrd_term_type)
    + rec_count*sizeof(struct rec_type)
    + drec_count * sizeof(struct double_rec_type);

  if (cur_mem > MAX_MEM)
    MAX_MEM = cur_mem;

  fprintf(RED_OUT, "Max memory used in bytes so far: %1d\n", MAX_MEM);
  fprintf(RED_OUT, "Current memory used in bytes so far: %1d\n", cur_mem);
  fprintf(RED_OUT, "Starting garbage collection at RT_TOP= %1d; red:%1d\n  ic:%1d, bc:%1d, hcd:%1d, he:%1d, ht:%1d\n  rec:%1d, drec:%1d. \n\n",
	  RT_TOP, red_count, ichild_count, bchild_count, hchild_count, hrd_exp_count, hrd_term_count, rec_count, drec_count
	  );
  fflush(RED_OUT);

}
/* report_redbop_management() */


int	simple_red_memory() { 
  int cur_mem; 
  
  cur_mem = report_23tree_management(FLAG_GC_SILENT);
  cur_mem
    = cur_mem
    + GARBAGE_OVERHEAD
    + red_count*sizeof(struct red_type)
    + ichild_count*sizeof(struct ddd_child_type)
    + bchild_count*sizeof(struct crd_child_type)
    + hchild_count*sizeof(struct hrd_child_type)
    + hrd_exp_count*sizeof(struct hrd_exp_type)
    + hrd_term_count*sizeof(struct hrd_term_type)
    + rec_count*sizeof(struct rec_type)
    + drec_count * sizeof(struct double_rec_type);

  if (cur_mem > MAX_MEM)
    MAX_MEM = cur_mem;
    
  return(cur_mem); 
} 
  /* simple_red_memory() */ 





init_garbage_management() {
  int	i;

  if (RT == NULL) { 
    RT_LIMIT = 1000+20*CLOCK_COUNT;
    RT = (struct red_type **) malloc(RT_LIMIT * sizeof(struct red_type *));
    USER_LIMIT = 1000;
    RED_USER_STACK = (struct red_type **) malloc(USER_LIMIT * sizeof(struct red_type *));
  }
  RT_TOP= INDEX_BOTTOM_OF_RUNTIME_STACK; 
  RT_DYNAMIC = 2;
  RT[INDEX_FALSE] = NORM_FALSE; 
  RT[INDEX_TRUE] = NORM_NO_RESTRICTION; 
  for (i = REFINED_GLOBAL_INVARIANCE+1; i < RT_LIMIT; i++)
    RT[i] = NORM_FALSE;
  for (i = 1; i < INDEX_BOTTOM_OF_RUNTIME_STACK; i++) { 
    RT[i] = NORM_NO_RESTRICTION;
  }
  RT[INDEX_MALLOC_SPACE] = NORM_FALSE; 
  RT[INDEX_GOAL] = NORM_FALSE; 

  if (  GSTATUS[INDEX_REDLIB_CONTROL] 
      & (  FLAG_REDLIB_DECLARE_FULL_MODEL 
         | FLAG_REDLIB_RENEW_VARS
         )
      ) { 
    USER_TOP = 0; 
    GARBAGE_OVERHEAD
    = CLOCK_COUNT*CLOCK_COUNT*(2*sizeof(struct red_type **)) 
    + CLOCK_COUNT * (2*sizeof(struct red_type *)); 
    
    for (i = 0; i < USER_LIMIT; i++)
      RED_USER_STACK[i] = NORM_FALSE;
  } 
}
/* init_garbage_management() */



#if RED_DEBUG_BASICS_MODE
int	count_mode_bound_free = 0; 
#endif 

void	release_all_rule_related_space(
  int 	flag_unmark_diagrams
) { 
  int					sxi, xi, si, ipi, pi, mi, vi; 
  struct parse_xtion_type		*psx, *psx_tmp; 
  struct parse_xtion_sync_type		*pxs, *pxs_tmp; 
  struct parse_mode_type		*psm, *psm_tmp; 
  struct parse_xtion_link_type		*pxl, *pxl_tmp; 
  struct parse_rate_spec_link_type	*prsl, *prsl_tmp; 
  struct parse_variable_type		*pv; 

  // This implies that this is only a parsed model. 
  // no array generation. 
  if (MODE == NULL) 
    return; 
    
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    if (SYNC_XTION[sxi].ec_representative) 
      free(SYNC_XTION[sxi].ec_representative); 
    if (SYNC_XTION[sxi].qfd_sync) 
      free(SYNC_XTION[sxi].qfd_sync); 
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) { 
      xi = SYNC_XTION[sxi].party[ipi].xtion; 
      if (XTION[xi].statement) {  
/*
        fprintf(RED_OUT, "\nFreeing XTION[xi=%1d].statement with status %x\n", 
          xi, XTION[xi].statement->st_status
        ); 
        psl(XTION[xi].statement, 1); 
        fprintf(RED_OUT, "\n"); 
        fflush(RED_OUT); 
*/
        if (XTION[xi].statement->st_status & FLAG_ACTION_QUANTIFIED_SYNC) {
          #if RED_DEBUG_BASICS_MODE
          fprintf(RED_OUT, 
            "\nTo free SYNC_XTION[sxi=%1d].party[ipi=%1d].statement=%x, status=%x\n", 
            sxi, ipi, XTION[xi].statement, 
            XTION[xi].statement->status 
          ); 
          fflush(RED_OUT); 
          #endif 
          free_sync_statement(SYNC_XTION[sxi].party[ipi].statement); // QQQQ
      } }
    } 
    free(SYNC_XTION[sxi].party); 
/* 
    if (SYNC_XTION[sxi].red_ec_ineq_representative) 
      free(SYNC_XTION[sxi].red_ec_ineq_representative); 
    if (SYNC_XTION[sxi].red_ec_ineq_weak_fairness_representative) 
      free(SYNC_XTION[sxi].red_ec_ineq_weak_fairness_representative); 
*/
  } 
  free(SYNC_XTION); 
  SYNC_XTION = NULL; 
  SYNC_XTION_COUNT = 0; 
  
  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    if (SYNC_XTION_GAME[sxi].ec_representative) 
      free(SYNC_XTION_GAME[sxi].ec_representative); 
    if (SYNC_XTION_GAME[sxi].qfd_sync) 
      free(SYNC_XTION_GAME[sxi].qfd_sync); 
    for (ipi = 0; ipi < SYNC_XTION_GAME[sxi].party_count; ipi++) { 
      xi = SYNC_XTION_GAME[sxi].party[ipi].xtion; 
      if (   XTION[xi].statement 
          && (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC)
          ) 
        free_sync_statement(SYNC_XTION_GAME[sxi].party[ipi].statement); 
    } 
    free(SYNC_XTION_GAME[sxi].party); 
/*
    if (SYNC_XTION_GAME[sxi].red_ec_ineq_representative) 
      free(SYNC_XTION_GAME[sxi].red_ec_ineq_representative); 
    if (SYNC_XTION_GAME[sxi].red_ec_ineq_weak_fairness_representative) 
      free(SYNC_XTION_GAME[sxi].red_ec_ineq_weak_fairness_representative); 
*/
  } 
  if (SYNC_XTION_GAME) { 
    free(SYNC_XTION_GAME); 
    SYNC_XTION_GAME = NULL; 
    SYNC_XTION_COUNT_GAME = 0; 
  }
  
  for (xi = 0; xi < XTION_COUNT; xi++) { 
/*
    for (si = 0; si < XTION[xi].sync_count; si++) { 
      if (XTION[xi].sync[si].exp_quantification)
        free_ps_exptree(XTION[xi].sync[si].exp_quantification); 
    } 
*/
    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, "\nreleasing XTION[xi=%1d].statement=%x\n", 
      xi, XTION[xi].statement
    ); 
    fflush(RED_OUT); 
    #endif 
    free(XTION[xi].sync); 

    free_xtion_statement(XTION[xi].statement); // QQQ
    if (XTION[xi].red_trigger) 
      free(XTION[xi].red_trigger + 1); 
  } 
  free(XTION); 
  XTION = NULL; 
  XTION_COUNT = 0; 
  
  for (psx = declare_xtion_list; 
    psx; 
    psx_tmp = psx, psx = psx->next_parse_xtion, free(psx_tmp) 
  ) { 
    for (pxs = psx->sync_list; 
      pxs; 
      pxs_tmp = pxs, pxs = pxs->next_parse_xtion_sync, free(pxs_tmp)
    ); 
    free_ps_st(psx->statement); 
//    free_ps_exptree(psx->trigger_exp); 
  } 
  declare_xtion_list = NULL; 
  declare_xtion_count = 0; 

  for (mi = 0; mi < MODE_COUNT; mi++) { 
    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, "\nmi=%1d:\n", mi); 
    fflush(RED_OUT); 
    #endif 
    
    if (CLOCK_COUNT) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\ncount_mode_bound_free=%1d\n", 
        ++count_mode_bound_free
      ); 
      #endif 
      free(MODE[mi].bound); 
    } 
    free(MODE[mi].name); 
//    free_ps_exptree(MODE[mi].invariance_exp); 
    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
        == FLAG_SYSTEM_TIMED
        ) { 
      for (ipi = 0; ipi < MODE[mi].process_count; ipi++) { 
        pi = MODE[mi].process[ipi]; 
        #if RED_DEBUG_BASICS_MODE
        fprintf(RED_OUT, "mi=%1d\n", mi); 
        fprintf(RED_OUT, "  pi=%1d, MODE[mi=%1d].clock_bound=%x\n", 
          pi, mi, pi, MODE[mi].clock_bound
        ); 
        fprintf(RED_OUT, "    bound_count=%1d\n", 
          MODE[mi].clock_bound[pi].bound_count
        ); 
        fflush(RED_OUT); 
        #endif 

        if (MODE[mi].clock_bound[pi].bound_count > 0)
          free(MODE[mi].clock_bound[pi].bound); 
      }
      free(MODE[mi].clock_bound + 1); 
    }
    free(MODE[mi].xtion); 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      free(MODE[mi].invariance[pi].zone_bound); 
      free(MODE[mi].process_rate_spec[pi].rate_spec); 
    } 
    free(MODE[mi].process); 
    free(MODE[mi].invariance + 1); 
    free(MODE[mi].process_rate_spec); 
  } 
  free(MODE); 
  MODE = NULL; 
  MODE_COUNT = 0; 
  
  for (psm = declare_mode_list; psm; 
    psm_tmp = psm, psm = psm->next_parse_mode, free(psm_tmp)
  ) { 
    // psm->name is freed with MODE[].  
    for (pxl = psm->parse_xtion_list; 
      pxl; 
      pxl_tmp = pxl, pxl = pxl->next_parse_xtion_link, free(pxl_tmp) 
    ) ; 
    for (prsl = psm->parse_rate_spec_list; 
      prsl; 
      prsl_tmp = prsl, prsl = prsl->next_parse_rate_spec_link, free(prsl_tmp) 
    ) {
/*    free(prsl->rate_var_name); The variable name is in the decalred 
      variable list.  So don't release it here. 
 */
//      free_ps_exptree(prsl->rate_lb); 
//      free_ps_exptree(prsl->rate_ub); 
    }
  } 
  declare_mode_list = NULL; 
  declare_mode_count = 0; 
    
  for (vi = 0; vi < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; vi++) { 
    if (GSYNC[vi].X_XTION_COUNT > 0) {
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\ntrying to free GSYNC[vi=%1d].X_XTION\n", vi); 
      fflush(RED_OUT); 
      #endif 
      free(GSYNC[vi].X_XTION); 
    } 
    if (GSYNC[vi].Q_XTION_COUNT > 0) { 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\ntrying to free GSYNC[vi=%1d].X_XTION\n", vi); 
      fflush(RED_OUT); 
      #endif 
      free(GSYNC[vi].Q_XTION); 
    } 
  } 
  #if RED_DEBUG_BASICS_MODE
  fprintf(RED_OUT, "after freeing all GSYNC entries.\n"); 
  #endif 
  free(GSYNC); 
  GSYNC = NULL; 
  
  for (vi = 2; vi < VARIABLE_COUNT; vi++) { 
    #if RED_DEBUG_BASICS_MODE
    fprintf(RED_OUT, 
      "\nfreeing diagrams of VAR[vi=%1d:%s], MODE_RATE_SPEC=%x, MODE_TIMED_INACTIVE=%x\n", 
      vi, VAR[vi].NAME, VAR[vi].MODE_RATE_SPEC, VAR[vi].MODE_TIMED_INACTIVE
    ); 
    #endif 
    
    pi = VAR[vi].PROC_INDEX; 
    fflush(RED_OUT); 
    switch (VAR[vi].TYPE) {
    case TYPE_CLOCK: 
      VAR[vi].U.CLOCK.MODE_RATE_SPEC_COUNT = 0;
      if (VAR[vi].U.CLOCK.MODE_RATE_SPEC) 
        free(VAR[vi].U.CLOCK.MODE_RATE_SPEC); 
      VAR[vi].U.CLOCK.MODE_RATE_SPEC = NULL; 
      break; 
    case TYPE_DENSE: 
      VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT = 0;
      if (VAR[vi].U.DENSE.MODE_RATE_SPEC) 
        free(VAR[vi].U.DENSE.MODE_RATE_SPEC); 
      VAR[vi].U.DENSE.MODE_RATE_SPEC = NULL; 
      break; 
    case TYPE_DISCRETE: 
      break; 
    case TYPE_FLOAT: 
      break; 
    case TYPE_DOUBLE: 
      break; 
    }
    if (pi && VAR[vi].MODE_TIMED_INACTIVE) 
      free(VAR[vi].MODE_TIMED_INACTIVE + PROCESS[pi].reachable_lower_mode); 
    VAR[vi].MODE_TIMED_INACTIVE = NULL; 
    VAR[vi].RED_ACTIVE = NULL;  
    VAR[vi].RED_INACTIVE = NULL; 
    VAR[vi].RED_TIMED_ACTIVE = NULL;  
    VAR[vi].RED_TIMED_INACTIVE = NULL;  	
  } 
  
  // The following fields are used to allocate GSYNC[].X_XTION[] and 
  // GSYNC[].Q_XTION[].  
  for (pv = declare_global_synchronizer_list;
       pv;
       pv = pv->next_parse_variable
       ) {
    pv->X_xtion_count = 0; 
    pv->Q_xtion_count = 0; 
  }

  if (flag_unmark_diagrams) 
    reset_hash_diagram_status();  

  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    free(PROCESS[pi].mode_distance_from_initial); 
    free(PROCESS[pi].reachable_mode); 
    free(PROCESS[pi].firable_xtion);
    PROCESS[pi].mode_distance_from_initial = NULL; 
    PROCESS[pi].reachable_mode_count = 0; 
    PROCESS[pi].reachable_mode = NULL; 
    PROCESS[pi].reachable_lower_mode = -1; 
    PROCESS[pi].reachable_upper_mode = -1;  
    PROCESS[pi].firable_xtion_count = 0; 
    PROCESS[pi].firable_xtion = NULL;
    PROCESS[pi].red_stop = NULL;  
  } 
} 
  /* release_all_rule_related_space() */ 
  




void	free_declare_variable_list(vlist) 
	struct parse_variable_type	*vlist; 
{
  struct parse_variable_type	*pv, *pv_tmp; 
  
  for (pv = vlist; 
    pv; 
    pv_tmp = pv, pv = pv->next_parse_variable, free(pv_tmp)
  ) { 
    	
  } 
}
  /* free_declare_variable_list() */ 
  
  
  
  
void	release_all_space() { 
  int			pi, vi; 
  struct ps_bunit_type	*bu, *pbu; 
  struct name_link_type	*nl, *pnl; 
  struct ps_exp_type	*gm; 
  
  #if RED_DEBUG_BASICS_MODE
  fprintf(RED_OUT, "\nbefore freeing everything\n"); 
  fflush(RED_OUT); 
  #endif 
  
  release_all_rule_related_space(0); 
  #if RED_DEBUG_BASICS_MODE
  fprintf(RED_OUT, "\nafter freeing all rules\n"); 
  fflush(RED_OUT); 
  #endif 

  release_all_hash_tables(); 
  #if RED_DEBUG_BASICS_MODE  
  fprintf(RED_OUT, "\nafter freeing all hash tables\n"); 
  fflush(RED_OUT); 

  fprintf(RED_OUT, "\nafter freeing GSYNC\n"); 
  fflush(RED_OUT); 
  #endif 
  
  if (GLOBAL_COUNT[TYPE_CLOCK] > 0) { 
    for (vi = GLOBAL_SYSTEM_OVERHEAD_COUNT; vi < VARIABLE_COUNT-1; vi++) { 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "freeing all space VAR[vi=%1d:%s]\n", 
        vi, VAR[vi].NAME
      ); 
      #endif 
      
      if (   VAR[vi].TYPE == TYPE_CDD
          || (VAR[vi].TYPE == TYPE_HRD && VAR[vi].PROC_INDEX == 0) 
          || (VAR[vi].TYPE == TYPE_HDD && VAR[vi].PROC_INDEX == 0) 
	  || vi == variable_index[TYPE_DENSE][0][0] // PROB_DENSE, 
	  || vi == variable_index[TYPE_CLOCK][0][0] // 0, 
          || vi == variable_index[TYPE_CLOCK][0][1] // TIME 
          || vi == variable_index[TYPE_CLOCK][0][2] // delta
          || vi == variable_index[TYPE_CLOCK][0][3] // deltap
          || vi == variable_index[TYPE_CLOCK][0][4] // -delta
          || vi == variable_index[TYPE_CLOCK][0][5] // -deltap
          || vi == variable_index[TYPE_CLOCK][0][6] // MODAL_CLOCK
          || vi == variable_index[TYPE_CLOCK][0][7] // PLAYTIME
          || vi == variable_index[TYPE_CLOCK][0][8] // ZENO_CLOCK
          ) 
        continue; 
      #if RED_DEBUG_BASICS_MODE
      fprintf(RED_OUT, "\ntrying to free VAR[vi=%1d].NAME %s\n", 
        vi, VAR[vi].NAME
      ); 
      fflush(RED_OUT); 
      #endif 
      
      free(VAR[vi].NAME); 
    }
  } 
  
  free(VAR); 
  VAR = NULL; 
  VARIABLE_COUNT = 0; 
  
  if (CLOCK) {
    free(CLOCK); 
    CLOCK = NULL; 
    CLOCK_COUNT = 0; 
  } 
  if (ZONE) { 
    for (vi = 0; vi < CLOCK_COUNT; vi++) { 
      if (ZONE[vi]) 
        free(ZONE[vi]); 
    } 
    free(ZONE); 
    ZONE = NULL; 
  }
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if (PROCESS[pi].name) 
      free(PROCESS[pi].name); 
  } 
  free(PROCESS + DEBUG_PROCESS_OFFSET); 
  PROCESS = NULL; 
  PROCESS_COUNT = -1; 
  
  // release all parsing structures. 
  free_declare_variable_list(declare_global_synchronizer_list); 
  declare_global_synchronizer_list = NULL; 
  
  free_declare_variable_list(declare_global_dense_list); 
  declare_global_dense_list = NULL;

  free_declare_variable_list(declare_global_clock_list);
  declare_global_clock_list = NULL;
  
  free_declare_variable_list(declare_global_discrete_list);
  declare_global_discrete_list = NULL;
  
  free_declare_variable_list(declare_global_pointer_list);
  declare_global_pointer_list = NULL;

  free_declare_variable_list(declare_local_qsholder_list); 
  declare_local_qsholder_list = NULL;  

  free_declare_variable_list(declare_local_synchronizer_list);
  declare_local_synchronizer_list = NULL;
  
  free_declare_variable_list(declare_local_dense_list);
  declare_local_dense_list = NULL;

  free_declare_variable_list(declare_local_clock_list);
  declare_local_clock_list = NULL;

  free_declare_variable_list(declare_local_discrete_list);
  declare_local_discrete_list = NULL;

  free_declare_variable_list(declare_local_pointer_list);
  declare_local_pointer_list = NULL;

  var_mode = NULL;    
  for (pi = TYPE_SYNCHRONIZER; pi <= TYPE_QSYNC_HOLDER; pi++) {
    GLOBAL_COUNT[pi] = 0; 
    LOCAL_COUNT[pi] = 0; 
  } 
  free(GLOBAL_COUNT + TYPE_SYNCHRONIZER); 
  free(LOCAL_COUNT + TYPE_SYNCHRONIZER); 
  
  for (bu = declare_inline_exp_list; 
       bu;
       pbu = bu, bu = bu->bnext, free(pbu) 
    ) { 
    free(bu->subexp->u.inline_declare.inline_exp_name); 
    for (nl = bu->subexp->u.inline_declare.formal_argument_list; 
         nl; 
         pnl = nl, nl = nl->next_name_link, free(pnl)
         ) 
      free(nl->name); 
//    free_ps_exptree(bu->subexp->u.inline_declare.declare_exp); 
    free(bu->subexp); 
  } 
  release_all_ps_exp(); 
  
  declare_inline_exp_list = NULL; 
  declare_inline_exp_count = 0; 
  CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 
  CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
  
  for (pi = 0; pi < GSTATUS_SIZE; pi++) 
    GSTATUS[GSTATUS_SIZE] = 0;
} 
  /* release_all_speace() */ 
  
  
  
  
int		count_gbg_c = 0; 
extern int 	count_ec_g; 






struct red_type	*red_simple_role_deadlock(d, roles) 
	struct red_type	*d; 
	int		roles; 
{ 
  int	w, deadlock; 
  
  RT[w = RT_TOP++] = d; 
  if ((roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)) 
      == (FLAG_GAME_MODL | FLAG_GAME_SPEC)
      ) 
    RT[deadlock = RT_TOP++] = RT[XI_SYNC_ALL]; 
  else if (roles & FLAG_GAME_MODL) 
    RT[deadlock = RT_TOP++] = red_game_eliminate_roles(
      RT[XI_SYNC_ALL], FLAG_GAME_SPEC
    ); 
  else if (roles & FLAG_GAME_SPEC) 
    RT[deadlock = RT_TOP++] = red_game_eliminate_roles(
      RT[XI_SYNC_ALL], FLAG_GAME_MODL
    ); 
  else { 
    fprintf(RED_OUT, 
      "Incorrect role specification %x in red_simple_role_deadlock().\n", 
      roles
    ); 	
    exit(0); 
  } 
  RT[deadlock] = red_bop(AND, red_all_trigger(RT[deadlock]), RT[w]);
  RT[deadlock] = red_complement(RT[deadlock]);
  RT[deadlock] = red_bop(AND, RT[w], RT[deadlock]);
  RT[deadlock] = red_hull_normalize(deadlock);
  RT_TOP--; // deadlock 
  RT_TOP--; // w 
  
  return(RT[deadlock]); 
}
  /* red_simple_role_deadlock() */ 
  
  
  
    
struct red_type	*red_role_deadlock(d, roles) 
	struct red_type	*d; 
	int		roles; 
{ 
  struct cache2_hash_entry_type	*ce; 

  if (!(roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC))) {
    fprintf(RED_OUT, 
      "Incorrect role specification %x in red_simple_role_deadlock().\n", 
      roles
    ); 	
    exit(0); 
  } 

  if (d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_ROLE_DEADLOCK, d, (struct red_type *) roles); 

  if (ce->result) {
    return(ce->result); 
  } 
  
  d = red_simple_role_deadlock(d, roles); 
  if (d != NORM_FALSE) {
    fprintf(RED_OUT, "\nA possible deadlock state space is detected:\n");
    red_print_graph(d);
  }
  red_mark(d, FLAG_GC_STABLE);
  
  ce->result = d; 
  
  return(d); 
}
  /* red_role_deadlock() */ 
  



struct red_type	*red_role_simple_zeno(d, roles) 
	struct red_type	*d; 
	int		roles; 
{ 
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_ROLE_SIMPLE_ZENO, d, (struct red_type *) roles); 

  if (ce->result) { 
    return(ce->result); 
  } 

  if (roles & FLAG_GAME_MODL) {
    if (!(roles & FLAG_GAME_SPEC)) 
      d = red_game_eliminate_roles(d, FLAG_GAME_SPEC); 
  }
  else if (roles & FLAG_GAME_SPEC)  
    d = red_game_eliminate_roles(d, FLAG_GAME_MODL); 
  else { 
    fprintf(RED_OUT, "Incorrect role specification %x in red_simple_zeno().\n", 
      roles
    ); 	
    exit(0); 
  } 
  d = red_time_upperbounded(d); 
  d = red_simple_role_deadlock(d, roles); 
  if (d != NORM_FALSE) {
    fprintf(RED_OUT, "\nA possible zeno state space is detected:\n");
    red_print_graph(d);
  }
  red_mark(d, FLAG_GC_STABLE);

  ce->result = d; 
  
  return(d);   
}
  /* red_role_simple_zeno() */ 
  
  
float	t1_float(
  char	*s, 
  int	i1, 
  int	i2, 
  float	f1, 
  float	f2
) { 
  fprintf(RED_OUT, "\n%s: %1d, %1d, %.4f, %.4f\n", 
    s, i1, i2, f1, f2
  ); 

} 
  /* t1_float() */ 




void	test_float() { 
  int	i1, i2, ifm; 
  float	f1, f2, rfm; 
  
  
  f1 = 1; 
  f2 = feps_plus(f1); 
  rfm = feps_minus(f1); 
  
  fprintf(RED_OUT, 
    "\n==================\n"
  ); 
  fprintf(RED_OUT, "%e, %f\n", f1, f1); 
  fprintf(RED_OUT, "epsilon plus:  %e, %.20f\n", f2, f2); 
  fprintf(RED_OUT, "epsilon minus: %e, %.20f\n", rfm, rfm); 
  
  fprintf(RED_OUT, 
    "FLT_MIN=%e, \n1+FLT_MIN=%e, \n1-FLT_MIN=%e\n", 
    FLT_MIN, 1+FLT_MIN, 1-FLT_MIN
  ); 
  if (1+FLT_MIN == 1) { 
    fprintf(RED_OUT, "1+%e==1!\n", FLT_MIN); 
  } 
  else { 
    fprintf(RED_OUT, "1+%e!=1!\n", FLT_MIN); 	
  } 
  fprintf(RED_OUT, "FLT_MAX=%.10f\n", FLT_MAX); 
  fprintf(RED_OUT, "DBL_MIN=%.20f, \n1+DBL_MIN=%.20f, \n1-DBL_MIN=%.20f\n", 
    DBL_MIN, 1+DBL_MIN, 1-DBL_MIN
  ); 
  fprintf(RED_OUT, "DBL_MAX=%.20f\n", DBL_MAX); 
  
  f1 = frexp(FLT_MIN, &i1); 
  f2 = frexp(3.5, &i2); 
  ifm = 1; 
  rfm = *((float *) &ifm); 
  fprintf(RED_OUT, "rfm = %.40f\n%.40f*2^%1d=", rfm, rfm, i2); 
  rfm = ldexp(rfm, i2); 
  fprintf(RED_OUT, "%.40f\n", rfm); 
  fprintf(RED_OUT, "3.5+%.40f=%.40f\n", rfm, rfm+3.5); 
  if (rfm == rfm+3.5) {
    fprintf(RED_OUT, "\nDoes not tell!\n"); 	
  } 
  else { 
    fprintf(RED_OUT, "\nWorks to tell!\n"); 	
  } 

  i1 = 100; 
  i2 = 220; 
  f1 = 3.3; 
  f2 = 433.88; 
  t1_float("A", i1, i2, f1, f2); 
  t1_float("B", (int) f1, (int) f2, (float) i1, (float) i2); 
  t1_float("C", i1, (int) f2, f1, (float) i2); 
  t1_float("D", f1, f2, i1,  i2); 
  t1_float("E", i1, f2, f1, i2); 
  
  exit(0); 
} 
  /* test_float() */ 

  
int	redlib_main()
{
  int				NEGATED_SPEC, assume, pi, xi, 
  				deadlock, wreach;
  struct reachable_return_type	*analysis_result; 
  struct sim_check_return_type	*sr; 
  struct rlimit			limit;
  struct red_type		*red_tmp, *conj; 

//  test_float(); 

  /* goal processing */ 
//  cpu_time_parsing = red_user_time(); 
  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_DEADLOCK:
    if (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS) {
      RT[INDEX_DEADLOCK] = NORM_FALSE;
      for (pi = 1; pi <= PROCESS_COUNT; pi++)
        for (xi = 1; xi < XTION_COUNT; xi++) { 
          conj = XTION[xi].red_trigger[pi]; 
          if (valid_mode_index(XTION[xi].src_mode_index)) 
            conj = red_bop(AND, conj, 
	      MODE[XTION[xi].src_mode_index].invariance[pi].red 
	    ); 
          RT[INDEX_DEADLOCK] = red_bop(OR, RT[INDEX_DEADLOCK], conj); 
        }
    }
    else {
      RT[INDEX_DEADLOCK] = red_all_trigger(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
    }
    RT[INDEX_DEADLOCK] = red_bop(AND, RT[REFINED_GLOBAL_INVARIANCE], RT[deadlock]);
    RT[INDEX_DEADLOCK] = red_complement(RT[deadlock]);
    RT[INDEX_DEADLOCK] = red_bop(AND, RT[REFINED_GLOBAL_INVARIANCE], RT[deadlock]);
    RT[INDEX_DEADLOCK] = red_hull_normalize(deadlock);
    if (RT[INDEX_DEADLOCK] != NORM_FALSE) {
      fprintf(RED_OUT, "\nA possible deadlock state space is detected:\n");
      red_print_graph(RT[INDEX_DEADLOCK]);
    }
    SPEC_EXP->u.rpred.red = RT[INDEX_DEADLOCK];
    ps_exp_mark(SPEC_EXP, FLAG_GC_STABLE);
  
    break; 
  }

  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_SIMULATE:
    fprintf(RED_OUT, "Sorry that simulator has been temporarily disabled. \n"); 
    exit(0); 
/*
    if (red_simulate_fwd(INDEX_INITIAL)) {
      fprintf(RED_OUT, "\nThe %s state is reachable from the initial states.\n", TASK_TYPE_NAME);
    }
    else
      fprintf(RED_OUT, "\nSo far, the %s state is NOT reachable from the initial states in the simulation.\n",
	      TASK_TYPE_NAME
	      );

    fprintf(RED_OUT, "\nEnd of simulation session!\n");
*/
    break;
  case TASK_BRANCHING_BISIM_CHECKING: 
    RT[REFINED_GLOBAL_INVARIANCE] = RT[DECLARED_GLOBAL_INVARIANCE]; 
    sr = red_fair_sim_check(
      RT[INDEX_INITIAL], 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      TYPE_TRUE // flag_bisim_check 
    ); 
/*
    fprintf(RED_OUT, "\nThe equivalence states:\n"); 
    red_print_graph(RT[wreach]); 
*/
    print_sim_check_return(sr); 
    return (sr->iteration_count); 
  case TASK_BRANCHING_SIM_CHECKING: 
    RT[REFINED_GLOBAL_INVARIANCE] = RT[DECLARED_GLOBAL_INVARIANCE]; 
    sr = red_fair_sim_check(
      RT[INDEX_INITIAL], 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      TYPE_FALSE // flag_bisim_check 
    ); 
/*
    fprintf(RED_OUT, "\nThe equivalence states:\n"); 
    red_print_graph(RT[wreach]); 
*/
    print_sim_check_return(sr); 
    return (sr->iteration_count); 
    break; 
  case TASK_DEADLOCK:
  case TASK_SAFETY:
  case TASK_RISK:
  case TASK_GOAL:
  case TASK_ZENO: 
    if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) 
      RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_bck(
	INDEX_INITIAL, 
	DECLARED_GLOBAL_INVARIANCE, 
	INDEX_GOAL, 
	GSTATUS[INDEX_TASK] & MASK_TASK, 
	GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
	0 // no print options are used. 
	); 
    else 
      RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_fwd(
	INDEX_INITIAL, 
	DECLARED_GLOBAL_INVARIANCE, 
	INDEX_GOAL, 
	GSTATUS[INDEX_TASK] & MASK_TASK, 
	GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
	0 // no print options are used. 
	); 
    fprintf(RED_OUT, "\n===========================\nafter red_analysis_abstract\n"); 
    red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 

    GSTATUS[INDEX_GAME_ROLES] = (GSTATUS[INDEX_GAME_ROLES] & ~MASK_GAME_ROLES)
			    | FLAG_GAME_MODL 
			    | FLAG_GAME_SPEC
			    | FLAG_GAME_ENVR 
			    | FLAG_GAME_ROLES_CHANGED; 
    GSTATUS[INDEX_APPROX] = (GSTATUS[INDEX_APPROX] & ~MASK_ROOT_POLARITY)
			  | FLAG_ROOT_NOAPPROX; 
    GSTATUS[INDEX_FULL_REACHABILITY] 
    = GSTATUS[INDEX_FULL_REACHABILITY] & ~FLAG_FULL_REACHABILITY; 
    GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
    = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
    & ~FLAG_REACHABILITY_DEPTH_BOUND; 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
    GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
    = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
    & ~FLAG_PARAMETRIC_ANALYSIS; 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = GSTATUS[INDEX_TIME_PROGRESS]
    | FLAG_TIME_PROGRESS
    | FLAG_TIME_PROGRESS_FULL_FORMULATION; 
//    | FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES; 
    GSTATUS[INDEX_ZENO_CYCLE] 
    = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
    | FLAG_ZENO_CYCLE_OK; 
    // FOR flag_prints, we use the users' options. 
    
    if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) { 
      RT[wreach = RT_TOP++] = RT[INDEX_GOAL]; 
      analysis_result = red_reachable_bck( 
        INDEX_INITIAL, 
        DECLARED_GLOBAL_INVARIANCE, 
        wreach, // This is to be destroyed. 
        SYNC_XTION, 
        SYNC_XTION_COUNT, 
        XI_SYNC_BULK, 
        XI_SYNC_BULK_WITH_TRIGGERS
      );
      RT_TOP--; /* wreach */ 
    }
    else {
      RT[wreach = RT_TOP++] = RT[INDEX_INITIAL]; 
      analysis_result = red_reachable_fwd(
        wreach, 
        REFINED_GLOBAL_INVARIANCE, 
        INDEX_GOAL, 
        SYNC_XTION, 
        SYNC_XTION_COUNT, 
        XI_SYNC_BULK
      ); 
      RT_TOP--; /* wreach */ 
    }

    print_reachable_return(analysis_result); 
    return (analysis_result->iteration_count); 
    break;

  case TASK_MODEL_CHECK:
    if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) 
      RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_bck(
	INDEX_INITIAL, 
	DECLARED_GLOBAL_INVARIANCE, 
	INDEX_GOAL, 
	GSTATUS[INDEX_TASK] & MASK_TASK, 
	GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
	0 // no print options are used. 
	); 
    else 
      RT[REFINED_GLOBAL_INVARIANCE] = red_abstract_space_fwd(
	INDEX_INITIAL, 
	DECLARED_GLOBAL_INVARIANCE, 
	INDEX_GOAL, 
	GSTATUS[INDEX_TASK] & MASK_TASK, 
	GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY, 
	0 // no print options are used. 
	); 
    fprintf(RED_OUT, "\n===========================\nafter red_analysis_abstract\n"); 
    red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
    GSTATUS[INDEX_GAME_ROLES] = (GSTATUS[INDEX_GAME_ROLES] & ~MASK_GAME_ROLES)
			    | FLAG_GAME_MODL; 
    if ((GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK) {
      if (GSTATUS[INDEX_ZENO_CYCLE] & FLAG_USE_PLAIN_NONZENO) {
        PEXP_EREACHABLE->u.mexp.strong_fairness_count = 0;
        PEXP_EREACHABLE->u.mexp.strong_fairness_list = NULL;
        PEXP_EREACHABLE->u.mexp.weak_fairness_count = 0;
        PEXP_EREACHABLE->u.mexp.weak_fairness_list = NULL;
        RED_PLAIN_NONZENO = NORM_NO_RESTRICTION;
/*
        fprintf(RED_OUT, "\n================================================\n");
        fprintf(RED_OUT, "RED_PLAIN_NONZENO:\n");
        red_print_graph(RED_PLAIN_NONZENO);
*/
      }
      if (GSTATUS[INDEX_ZENO_CYCLE] & FLAG_USE_APPROX_NONZENO) {
        PEXP_EREACHABLE->u.mexp.strong_fairness_count = 0;
        PEXP_EREACHABLE->u.mexp.strong_fairness_list = NULL;
        PEXP_EREACHABLE->u.mexp.weak_fairness_count = 0;
        PEXP_EREACHABLE->u.mexp.weak_fairness_list = NULL;
        RED_APPROX_NONZENO = NORM_NO_RESTRICTION;
      }
    }

    RT[NEGATED_SPEC = RT_TOP++] = NORM_FALSE;
    RT[assume = RT_TOP++] = NORM_NO_RESTRICTION; 
    RT[NEGATED_SPEC] = red_label_bck(
      SPEC_EXP, assume, 
      DECLARED_GLOBAL_INVARIANCE, 
      REFINED_GLOBAL_INVARIANCE, 
      GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY
    );
    RT_TOP--; /* assume */
    RT[NEGATED_SPEC] = red_bop(AND, RT[NEGATED_SPEC], RT[INDEX_INITIAL]);
    if (CLOCK_COUNT > 1)
      SPEC_EXP->u.rpred.red = red_hull_normalize(NEGATED_SPEC);

    if (SPEC_EXP->u.rpred.red == NORM_FALSE)
      fprintf(RED_OUT,
              "\nThe specification formulus is satisfied from the initial states!\n"
              );
    else {
      fprintf(RED_OUT,
              "\nThe specification formulus MAY NOT be satisfied from the initial states!\n"
              );
    }
    RT_TOP--; /* NEGATED_SPEC */
  }
}
/* redlib_main() */





 
