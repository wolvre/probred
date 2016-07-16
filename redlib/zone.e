extern int      INDEX_CONVEX_START_FROM_INVARIANCE, 
        	INDEX_CONVEX_STOP_FROM_INVARIANCE; 

extern int	ZONE_TOP, ZONE_STACK_LIMIT, *ZONE_STACK; 




extern int 	bchild_count, bchild_link_count;

struct index_link_type	***ZONE_CONSTANT; 




extern int		ZM_DOWNWARD, ZB_DOWNWARD; 
extern struct red_type	*rec_tight_differences_DOWNWARD(),
			*rec_eliminate_redundant_differences_DOWNWARD(),
			*rec_inactive_clock_tight_magnitudes_DOWNWARD();

extern int
  zone_ub_add(), zone_ub_add_unbounded(), 
  zone_ub_subtract(), zone_lb_subtract(), 
  red_inequality_relevance_extract(), 
  red_double_inequality_relevance_extract(), 
  check_time_convexity(); 

extern void	init_zone_management(); 

extern struct red_type	
  *zone_extract_interval(), 
  *zone_intersect(), 
  *red_track_pveq(), 
  *red_track_pbound(),  
  *red_time_saturate(), 
  *red_transitive_pair(), 
  *red_path_eliminate(), 
  *red_time_clock_eliminate_closure_eq(), 
  *red_hull_normalize(), 
  *red_tight_all_pairs(), 
  *red_hull_test_emptiness(), 
  *red_zone_reduce(), 
  *red_eliminate_magnitude_redundancy_DOWNWARD(), 
  *red_hull_eliminate_negative_cycles(), 
  *red_eliminate_simple_negative_cycles(), 
  *red_hull_assign_bck(), 
  *red_hull_assign_bck_simple(), 
  *red_hull_assign_magnitude_bck(), 
  *red_hull_assign_fwd(), 
  *red_hull_assign_magnitude_fwd(), 
  *red_time_progress_fwd(), 
  *red_time_progress_noxtive_fwd(), 
  *red_time_progress_noxtive_bck(), 
  *red_bypass_DOWNWARD(), 
  *red_zone_subsume(), 
  *red_time_progress_by_amount(), 
  *red_eliminate_magnitude_redundancy(), 
  *red_hull_inactive(), 
  *red_tight_DOWNWARD(), 
  *red_clock_upper_extend(
    struct red_type	* // *d 
  ), 
  *red_clock_lower_extend(
    struct red_type	* // *d 
  );  




#define	FLAG_PATH_INCLUDES_DEST		TYPE_TRUE
#define	FLAG_PATH_MAY_NOT_INCLUDE_DEST	TYPE_FALSE 
extern struct red_type 
  *red_game_time_progress_bck(
    struct ps_exp_type	*, 	// path_exp, 
    int, 			// destination 
    int, 			// path, 
    int, 			// flag_role, 
    int	 			// flag_path_includes_dest 
    				// TYPE_FALSE actually means maybe not.
                                // This is used specifically in the 
                                // evaluation of EU. 
  ); 
  
extern inline struct red_type	
  *red_game_time_progress_bck_option(
    int	w, 
    int	path, 
    int	flag_role, 
    int	option
  ); 


extern struct red_type	*(*RED_BYPASS_BCK)(), *(*RED_BYPASS_FWD)(); 

extern void 
  filter_not_nonzero_transitivities(), 
  filter_not_equivalences(), 
  filter_minimal_not_equivalences(), 
  analyze_clock_lubs(); 

extern int	test_bypass_fwd(); 

