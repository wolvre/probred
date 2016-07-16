#define	FLAG_FAIR_SIM	1
#define FLAG_BRANCH_SIM	0 

extern int
	FLAG_GAME_ONE_PLANT_ONLY, 
	PREIMAGE_GAME_ONE_PLANT_ONLY, 
	IMAGE_GAME_ONE_PLANT_ONLY, 
	ACC_IMAGE_GAME_ONE_PLANT_ONLY; 

extern int	
  NZF, 
  FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, 
  MODL_FAIRNESS, SPEC_FAIRNESS; 


extern struct red_type	
  **construct_red_array_from_one( 
    struct red_link_type *, 	// *list,  
    int 		    	// rc
  );  
  

extern inline int	flag_opponent(
  int 	// flag_roles 
); 


extern struct red_type 
  *red_neg_sim_universe(
    struct red_type	*, 	// *red_event_precond
    int, 			// sxi 
    struct red_type	*, 	// *red_dest 
    int  		,	// flag_role 
    int			, 	// flag_fair_sim, 
    int			, 	// time_distance_lb, 
    int				// flag_step_time    
  ); 


extern struct red_type 
  *red_neg_sim_universe_sync_bulk(
    struct red_type	*, 	// *red_event_precond
    struct red_type	*, 	// *red_dest 
    int  		,	// flag_role 
    int			, 	// flag_fair_sim, 
    int			, 	// time_distance_lb, 
    int				// flag_step_time    
  ); 


extern struct red_type 
  *red_game_opponent_precondition_one_ITERATIVE(
    struct red_type 			*, 
    struct red_type 			*, 
    int					, 
    int					,  
    struct ps_fairness_link_type	* // *weak_fairness_list   
  ); 


extern struct sim_check_return_type	
  *red_fair_sim_check(
    struct red_type	*, // red_init, 
    struct red_type	*, // red_fxp, 
    int			// flag_bisim_checking  
); 

extern void
  print_sim_check_return(); 


extern void	
  commit_branching_sim_result(
    int, 
    int, 
    struct red_type			*, 
    struct sim_check_return_type	* 
  ), 
  commit_fair_sim_result( 
    int, 
    int, 
    struct red_type			*, 
    struct sim_check_return_type	*
  ); 



