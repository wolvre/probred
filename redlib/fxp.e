#include "fxp.h" 


/* return values of red_reachable_fwd() and red_reachable_bck(), 
 * When it is non-negative, then it means the iteration count at which 
 * a goal state is reached. 
 */ 
#define	FLAG_UNREACHABLE			-1
#define	FLAG_PROGRESS_ESTIMATION_FINISHED	-2

#define	FLAG_GOAL_EARLY_REACHED	1
#define FLAG_GOAL_NORMAL	0


extern int		REACHABLE, 
			PARAMETER_COMPLEMENT, REACHABLE_COMPLEMENT,
			**current_firable_xtion;
extern struct index_link_type	**fx_list;

extern struct red_type	*RED_XI_SYNC_SIGNIFICANT;

/* assume that the pi is recorded in ascending order. */
extern int	*px;

extern void 
  init_iterate_management(), 
  get_all_firable_xtions(int, int); 

extern struct red_type	
  *red_NZF(), 
  *red_eliminate_proc_qfd_sync(), 
  *red_ealways_bck(), 
  *red_eliminate_all_qfd_sync();



#define FLAG_POST_PROCESSING	1
#define FLAG_NO_POST_PROCESSING	0

#define FLAG_OPPONENT_ELIMINATE	1
#define FLAG_OPPONENT_KEEP	0

#define FLAG_NO_CUR_REACHABLE_EXCLUSION	-1 

extern void	gfp_guess_timeless( 
  struct red_type	*d, 
  struct red_type	**timeless_ptr, 
  struct red_type	**timed_ptr 
); 


extern struct red_type	
  *red_abstraction_game_based_significant(),

  *red_postcondition_sync_ITERATIVE(
    struct reachable_return_type *, // 	*rr,  
    int				, // src, // RT[src] describes the source state. 
    int				, // path, // RT[path] is an invariance condition for reachable states
    int				, // goal, // RT[goal] is the goal for reachability 
    struct red_type		*, // red_cur_reachable, 
    struct red_type		*, // red_reachable, 
    struct sync_xtion_type	*, // *sync_xtion, 
    int				, // sync_xtion_count
    int				, // flag_postprocessing 
    int				* // result_status_ptr 
  ),
  *red_postcondition_sync_bulk(
    struct reachable_return_type *, // 	*rr,  
    int				, // src, 
    int				, // path, // RT[path] is an invariance condition for reachable states
    int				, // goal, // RT[goal] is the goal for reachability 
    struct red_type		*, // red_cur_reachable, 
    struct red_type		*, // red_reachable, 
    int				, // sxi_bulk // RT[sxi_bulk] is the bulk representation of the 
                          		// sync transitions.  
    int				, // flag_postprocessing 
    int				* // result_status_ptr
  ),
  *red_postcondition_sync_SPECIFIC(
    int, //			explore, 
    int, // 			path, 
    struct red_type		*, // red_cur_reachable, 
    struct red_type		*, // red_reachable, 
    struct sync_xtion_type	*, 
    int				// flag_postprocessing 
  ),
  *red_precondition_sync_ITERATIVE(
    struct reachable_return_type *, 	// *rr, 
    int, 				// explore, 
    struct ps_exp_type *, 		// path_exp, 
    int, 				// path, 
    int, 				// init, 
    struct red_type			*, // red_cur_reachable, 
    struct red_type			*, // red_reachable, 
    struct sync_xtion_type *, 		// *sync_xtion, 
    int,				// sync_xtion_count, 
    int	*,				// *flag_result_ptr, 
    int					// flag_postprocessing 
  ),
  *red_precondition_sync_bulk(
    struct reachable_return_type *, 	// *rr, 
    int,				// dst, 
					// index of diagram for destination 
    struct ps_exp_type *, 		// path_exp, 
    int,				// path, 
    int,				// init, 
    struct red_type			*, // red_cur_reachable, 
    struct red_type			*, // red_reachable, 
    int,				// sxi_bulk, 
    int,				// sxi_bulk_with_trigger,  
		// This is an index to RT. 
	        // RT[sxi_bulk_with_trigger] is only used in sync bulk evaluation  
	        // in preconditon evaluation when trigger-action interference is 
		// is possible. 
                // In sync bulk evaluation with trigger-action evaluation, we will 
	        // postpone the conjunction of the triggering condition to the postprocessing
	        // after all processes have done their actions precondition evaluation.  
    int	*,	// *flag_result_ptr 
    int		// flag_postprocessing 
  ),
  *red_precondition_sync_SPECIFIC(
    int,			// explore, 
    struct ps_exp_type *, 	// path_exp, 
    int,			// path, 
    struct red_type		*, // red_cur_reachable, 
    struct red_type		*, // red_reachable, 
    struct sync_xtion_type *, 	// *sync_xtion_ptr, 
    int *,			// *flag_result_ptr 
    int				// flag_postprocessing 
  ), 

/* When the following standard precondition routine is used, 
 * it is important to know that there is a side-effect of 
 * state exclusion from RT[RESULT_ITERATE] and RT[REACHABLE]. 
 * If you do not use this side-effect, please set RESULT_ITERATE to 
 * FLAG_NO_CUR_REACHABLE_EXCLUSION and REACHABLE to zero. 
 */ 
  *red_sync_bulk_from_event_diagram(
    struct red_type	*, // *red_events, 
    int			 // sync_bulk
  ), 

  *red_role_event_precondition_sync_specific(
    struct ps_exp_type			*, // *event_exp, 
    struct red_type			*, // *red_precond, 
    int 				,  // dst, 
    struct ps_exp_type			*, // *path_exp, 
    int					,  // path, 
    
    struct red_type			*, // red_cur_reachable, 
    struct red_type			*, // red_reachable, 
    int					,  // sync_xtion_index, 
    struct sync_xtion_type		*, // *sync_xtion_table, 
    struct ps_fairness_link_type	*, // *weak_fairness_list,  

    int					,  // flag_roles, 
    int					,  // flag_opp_eok, 
    int					,  // flag_polarity, 
    int					   // flag_postprocessing 
  ),  

  *red_role_event_precondition_sync_bulk(
    struct red_type			*, // *red_sync_bulk_from_event_exp, 
    struct red_type			*, // *red_precond, 
    int 				, // dst, 
    struct ps_exp_type			*, // *path_exp, 
    int					, // path, 
    
    struct red_type			*, // red_cur_reachable, 
    struct red_type			*, // red_reachable, 
    int					, // sync_bulk, 
    struct ps_fairness_link_type	*, // *weak_fairness_list,  
    int					, // flag_roles, 

    int					, // flag_opp_eok, // eliminate or keep
    int					, // flag_polarity,     
    int					 // flag_postprocessing 
  ), 

  *red_role_event_precondition(
    struct ps_exp_type			*, 
    struct red_type 			*, 
    struct red_type			*,  
    int 				, 
    struct ps_exp_type			*, 
    
    int					, 
    struct red_type			*, // red_cur_reachable, 
    struct red_type			*, // red_reachable, 
    struct sync_xtion_type		*, 
    int					, 

    int					, 
    struct ps_fairness_link_type	*, 
    int				 	,     
    int					, 
    int					, 
    
    int				 
  ),  
  *red_untimed_reachable_fwd(),
  *red_untimed_reachable_bck(),
  *REDLIB_one_weakest_precondition_sync_bulk(), 
  *red_precondition_postprocessing(
    int				, // explore, 
    struct ps_exp_type		*, // *spec_exp, 
    int				, // path, 
					// RT[cur_reachable] is the accummulated 
	                                // image of the current round of 
	                                // postcondition evaluation. 
	                                // If the postprocessing is done 
	                                // for only one sync transition, 
	                                // then we will not use this 
	                                // parameter and we set 
	                                // cur_reachable to FLAG_NO_CUR_REACHABLE_EXCLUSION.  
	                                // Otherwise, it should always be 
	                                // RESULT_ITERATE. 
    struct red_type 		*, // red_cur_reachable, // red_cur_reachable is the accummulated 
    struct red_type 		*, // red_reachable, // red_cur_reachable is the accummulated 
	                                // image of the current round of 
	                                // postcondition evaluation. 
	                                // If the postprocessing is done 
	                                // for only one sync transition, 
	                                // then we will not use this 
	                                // parameter and we set 
	                                // cur_reachable to FLAG_NO_CUR_REACHABLE_EXCLUSION.  
	                                // Otherwise, it should always be 
	                                // RESULT_ITERATE.   
    struct sync_xtion_type	*, // *sxt_ptr, // This is a pointer to a 
	                                // sync_xtion in a sync_xtion table. 	
	                                // If this is NULL, it means that 
	                                // sxi_bulk must be greater than zero and 
	                                // RT[sxi_bulk] must be a meaningful 
	                                // diagram for sync_xtion restrictions.  
	                                // since we must be doing postprocessing 
	                                // for sync bulk evaluation. 
    int				, // sxi_bulk_with_trigger,   
				  // This is an index to RT. 
	                          // RT[sxi_bulk_with_trigger] is 
	                          // only used in sync bulk evaluation  
	                          // in preconditon evaluation when 
	                          // trigger-action interference is 
				  // is possible. 
                                  // In sync bulk evaluation with 
                                  // trigger-action evaluation, we will 
	                          // postpone the conjunction of the 
	                          // triggering condition to the postprocessing
	                          // after all processes have done 
	                          // their actions precondition evaluation. 
    int				  // flag_postprocessing 
  ), 
			

  *red_weak_event_precond_filter_sync_bulk(
    struct red_type			*, // *red_src, 
    struct ps_fairness_link_type	* // *weak_fairness_list
  ), 
  
  *red_weak_event_postcond_filter_sync_bulk(
    struct red_type		*, // *red_dest, 
    struct ps_fairness_link_type	* // *weak_fairness_list
  ), 

  *red_action_abstraction_bck(), 
  *red_action_abstraction_fwd(),
  *red_action_clock_eliminate(),
  *red_action_assign_variable_fwd(),
  *red_action_assign_variable_bck(),
  *red_action_LRindirect_assign_variable(),
  *red_action_Lindirect_assign_variable(),
  *red_action_Rindirect_assign_variable(),
  *red_action_assign_constant_fwd(),
  *red_assign_interval_fwd(),
  *red_assign_interval_bck(),
  *red_action_indirect_assign_constant(),
  *red_action_indirect_inc(),
  *red_action_indirect_dec(),
  *red_label_bck(
	struct ps_exp_type	*spec, 
	int			reset_inheritance, 
	int			path, 
	int			early_decision,  
	int			flag_polarity 	// -1 for under-approx
						// 0 for no-approx 
						// 1 for over-approx 
  );

extern struct model_check_return_type	*red_model_chk(
  int			init, 
  int			path, 
  struct ps_exp_type	*nspec
); 

extern struct dfs_stack_type	*DFS_STACK_TOP;

extern struct trace_frame_type	*TF4;

#define MASK_LFP	0
#define	MASK_GFP	1
#define	MASK_FXPOINT	1

#define MASK_NO_EVENT	0
#define	MASK_EVENT	2

#define MASK_LFP_NO_EVENT	0
#define	MASK_GFP_NO_EVENT	1
#define	MASK_LFP_EVENT		2
#define	MASK_GFP_EVENT		3

extern struct reachable_return_type	
  *red_reachable_bck( 
    int, 
    int, 
    int, 
    struct sync_xtion_type	*, 
    int, 
    int, // an index to the RT statck 
    int // an index to the RT stack
  ), 
  
  *red_reachable_fwd(
    int, // the initial state of the reachability 
    int, // the invariance condition of the reachability 
    int, // the goal state of the reachability, 
    struct sync_xtion_type	*, 
    int, 
    int 
  ); 

extern void	print_reachable_return(); 


extern struct red_type	
  *role_fairness_bck(
    struct ps_exp_type		*, 
    int				, // reset_inheritance 
    int				, // path 
    int				, 
    int				, 
    int				, 
    int  
  ),  

  *red_role_euntil_bck(
    int				, 
    int				, 
    int				, 
    int				, 
    int				, 
    struct sync_xtion_type	*, 
    int				, 
    int				, 
    int				, 
    int  
  ), 
  
  *red_abstract_space_bck(
    int, 
    int, 
    int, 
    int, 
    int, // This is the approx flag for the final 
	 // reachability or model-checking task.  
    int    
  ), 
  
  *red_abstract_space_fwd(
    int, 
    int, 
    int, 
    int, 
    int,   
    int	
  ); 

