extern void	init_zapprox_management();
extern struct red_type	*zone_hull_filter(), 
			*zone_union_filter(), *zone_convex_hull(); 
extern struct red_type	*red_abstraction_game_based(),  
			*red_abstraction_game_based_significant(),
			*red_abstraction_game_based_significant_time(),	
			*red_abstraction_game_based_significant_magnitude(),
			*red_abstraction_game_based_insig(),
			*red_abstraction_game_based_insig_time(),
			*red_abstraction_game_based_insig_discrete(),
			*red_abstraction_game_based_insig_magnitude(), 
			*red_abs_game(), *rec_abs_game();

extern void	red_abs(), union_abstract(), zapprox_test(); 
