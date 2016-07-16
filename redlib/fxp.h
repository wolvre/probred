
/* The following constants are used by red_euntil_bck() */ 

/* This is the same the one in redbasics.h. */ 
// #define MASK_EC_ROLS			(0x000F) 
#define FLAG_ENUTIL_EXCLUSION		(0x0040) 


#define MASK_EUNTIL_APPROX		(0x0F00)
#define FLAG_EUNTIL_EXACT		(0x0000)
#define	FLAG_EUNTIL_OVER_APPROX		(0x0100)
#define	FLAG_EUNTIL_UNDER_APPROX	(0x0200) 

#define MASK_EUNTIL_NONZENO		(0x1000)
#define FLAG_EUNTIL_NONZENO		(0x1000)
#define FLAG_EUNTIL_ZENO		(0x0000)

#define	FLAG_EUNTIL_SYMMETRY		(0x2000)
#define	FLAG_EUNTIL_NOSYMMETRY		(0x0000) 

#define FLAG_EUNTIL_EXCLUSION		(0x4000)
#define	FLAG_EUNTIL_NOEXCLUSION		(0x0000)

#define	MASK_EUNTIL_DEBUG_REDUCED	(0x8000) 
#define	FLAG_EUNTIL_DEBUG_NOREDUCED	(0x8000)
#define	FLAG_EUNTIL_DEBUG_REDUCED	(0x0000)

#define	FLAG_EUNTIL_GARBAGE_COLLECT	(0x10000) 

#define FLAG_ANY_XTION	-1


#ifndef _REDLIB_REACH_RETURN_STRUCTURES 
#define _REDLIB_REACH_RETURN_STRUCTURES 

/***************************************************************
 *  The following structures are for the return value of reachability analysis. 
 *  
 */
struct path_xtion_type {
  int			party_count;
  int			*pi, *xi; 
  struct red_type	*prestate; 
};

struct counter_example_party_type { 
  int	proc, xtion; 	
}; 

struct counter_example_node_type { 
  int					exit_sync_xtion_party_count; 
  struct counter_example_party_type	*exit_sync_xtion_party; 
  char					*exit_sync_xtion_string; 
  struct red_type 			*prestate; 
  struct counter_example_node_type	*next_counter_example_node; 
}; 



struct reachable_return_type { 
  int                                   status, 

#define MASK_REACHABLE_RETURN                   (0xF) 
#define FLAG_RESULT_EARLY_REACHED               1
#define FLAG_RESULT_FULL_FIXPOINT               2 
#define FLAG_RESULT_DEPTH_BOUND_FINISHED        4 

#define FLAG_COUNTER_EXAMPLE_GENERATED          (0x10)
#define FLAG_COUNTER_EXAMPLE_NOT_GENERATED      (0x00) 

#define FLAG_RESULT_PARAMETRIC_ANALYSIS         (0x20) 
#define FLAG_RESULT_NO_PARAMETRIC_ANALYSIS      (0x00) 

#define MASK_REACHABILITY_RESULT                (0xF00) 
#define FLAG_REACHABILITY_UNDECIDED             0
#define FLAG_NOT_REACHABLE                      (0x100)
#define FLAG_REACHABILITY_INCONCLUSIVE          (0x200)
#define FLAG_REACHABILITY_DETECTED              (0x300)

#define MASK_LFP_TASK_TYPE                      (0xF0000)
#define FLAG_LFP_TASK_RISK                      (0x10000)
#define FLAG_LFP_TASK_GOAL                      (0x20000)
#define FLAG_LFP_TASK_SAFETY                    (0x30000)
#define FLAG_LFP_TASK_ZENO                      (0x50000)
#define FLAG_LFP_TASK_DEADLOCK                  (0x60000)

                                        iteration_count, 
                                        counter_example_length; 	
  struct counter_example_node_type      *counter_example; 
  struct red_type                       *reachability, 
                                        *risk_parameter; 
}; 

#endif 



#ifndef _REDLIB_MCHECK_RETURN_STRUCTURES 
#define _REDLIB_MCHECK_RETURN_STRUCTURES 


/*****************************************************************
 *  
 */

struct model_check_return_type { 
  int			status; 
#define	FLAG_MODEL_CHECK_SATISFIED	1
#define	FLAG_MODEL_CHECK_UNSATISFIED	0

  struct red_type	*initial_state_diagram, *failed_state_diagram; 
  struct ps_exp_type	*neg_formula; 
}; 
  /* model_check_return_type */ 

#endif 

