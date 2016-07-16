#define	FLAG_FROM_DEST_AT_CMAX		-2
#define	FLAG_GAME_SYNC_BULK		-1
#define	FLAG_GAME_SYNC_ITERATIVE	0

#ifndef _REDLIB_BISIM_RETURN_STRUCTURES 
#define _REDLIB_BISIM_RETURN_STRUCTURES 

/*****************************************************************
 *  This part is reserved for the future research. 
 *  We have no clue how to do it now. 
 */
 
/*****************************************************************
 *  This part is reserved for the future research. 
 *  We have no clue how to do it now. 
 */
 
struct counter_example_sync_party_type { 
  int	proc, xi; 
}; 

struct matching_sync_xtion_type { 
  int						matching_sync_xtion_party_count; 
  struct counter_example_sync_party_type	*matching_sync_xtion_party; 
  struct counter_example_tree_node_type		*poststate; 
}; 

struct counter_example_tree_node_type { 
  int						iteration_index, 
						status;  
  struct red_type 				*prestate; 
/*  Flag values FLAG_EC_SPEC and FLAG_EC_MODL specify that 
 *  whose this is a transition. 
 */ 
  int                                       	sync_xtion_party_count; 
  struct counter_example_sync_party_type	*sync_xtion_party; 
  int                                      	matching_sync_xtion_count; 
  struct matching_sync_xtion_type		*matching_sync_xtion; 
}; 

struct sim_check_return_type { 
  int                           status, 
#define MASK_SIM_CHECK_RETURN                 (0x0000000F) 
#define MASK_BISIM_CHECK_RETURN               (0x0000000F) 
// The following five constants are also defined in fxp.h. 
// #define FLAG_RESULT_EARLY_REACHED             (0x00000001)
// #define FLAG_RESULT_FULL_FIXPOINT             (0x00000002) 
// #define FLAG_RESULT_DEPTH_BOUND_FINISHED      (0x00000004) 

// #define FLAG_COUNTER_EXAMPLE_GENERATED        (0x00000010)
// #define FLAG_COUNTER_EXAMPLE_NOT_GENERATED    (0x00000000) 

#define MASK_BRANCHING_SIM_RESULT          (0x00000F00) 
#define MASK_BRANCHING_BISIM_RESULT        (0x00000F00) 

#define FLAG_BRANCHING_SIM_UNDECIDED       (0x00000000)
#define FLAG_BRANCHING_BISIM_UNDECIDED     (0x00000000)

#define FLAG_NO_BRANCHING_SIM              (0x00000100)
#define FLAG_NO_BRANCHING_BISIM            (0x00000100) 

#define FLAG_BRANCHING_SIM_INCONCLUSIVE    (0x00000200)
#define FLAG_BRANCHING_BISIM_INCONCLUSIVE  (0x00000200)

#define FLAG_A_BRANCHING_SIM_EXISTS        (0x00000300)
#define FLAG_A_BRANCHING_BISIM_EXISTS      (0x00000300)

#define MASK_FAIR_SIM_RESULT               (0x0000F000) 
#define MASK_FAIR_BISIM_RESULT             (0x0000F000) 

#define FLAG_FAIR_SIM_UNDECIDED            (0x00000000)
#define FLAG_FAIR_BISIM_UNDECIDED          (0x00000000) 

#define FLAG_NO_FAIR_SIM                   (0x00001000)
#define FLAG_NO_FAIR_BISIM                 (0x00001000) 

#define FLAG_FAIR_SIM_INCONCLUSIVE         (0x00002000)
#define FLAG_FAIR_BISIM_INCONCLUSIVE       (0x00002000) 

#define FLAG_A_FAIR_SIM_EXISTS             (0x00003000)
#define FLAG_A_FAIR_BISIM_EXISTS           (0x00003000) 

#define MASK_GFP_TASK_TYPE                    (0x000F0000)
#define FLAG_GFP_TASK_BISIM_CHECK             (0x00010000)
#define FLAG_GFP_TASK_SIM_CHECK               (0x00000000) 

#define MASK_SIM_ZENO_CYCLE                   (0x00F00000)
#define FLAG_SIM_USE_PLAIN_NONZENO            (0x00000000)
#define FLAG_SIM_USE_APPROX_NONZENO           (0x00100000)
#define FLAG_SIM_ZENO_CYCLE_OK                (0x00200000)

#define MASK_BISIM_ZENO_CYCLE                 (0x00F00000)
#define FLAG_BISIM_USE_PLAIN_NONZENO          (0x00000000)
#define FLAG_BISIM_USE_APPROX_NONZENO         (0x00100000)
#define FLAG_BISIM_ZENO_CYCLE_OK              (0x00200000)

                                        iteration_count; 
  struct red_type                       *initial_state_pair_diagram, 
                                        *final_neg_sim_relation_diagram; 
#define final_bisim_relation_diagram    final_sim_relation_diagram 

  struct red_type                       **iteratively_removed_diagram; 
  struct counter_example_tree_node_type *counter_example_tree; 
}; 
  /* bisim_check_return_type */ 



#endif 

