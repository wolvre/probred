/*****************************************************************
 *
 */
extern struct red_type	*red_all_event_precondition_to_forced_neg_sim(
  struct red_type		*, // *red_events, 
  struct red_type		*, // *red_event_precond, 
  struct red_type		*, // *red_neg_sim, 
  struct red_type		*, // *red_path, 
  struct red_type		*, // *red_neg_sim_wfair, 
  struct ps_fairness_link_type	*, // *weak_fairness_list, 
  int				, // flag_role, 
  int				// flag_fair_sim //,  
//  int				flag_avoid_as_dest   
); 


extern struct red_type	*red_game_auntil_bck(
  struct red_type		*, // *red_neg_fsim_base, 
  struct red_type		*, // *red_path, 
  struct red_type		*, // *red_neg_sim_wfair, 
  struct ps_fairness_link_type	*, // *weak_fairness_list, 
  int				, // time_distance_lb, 
  int				// flag_role  
); 










