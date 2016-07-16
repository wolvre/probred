extern struct variable_type	*VAR;
extern struct vop_type		*VAR_OP;
extern int			VARIABLE_COUNT, VOP_LIMIT;

extern int	*OMAP, *RMAP, *OMAP_BOTTOM, *OMAP_HALF_INTERLEAVING, *OMAP_FULL_INTERLEAVING; 

extern int	mbug_flag, FLAG_ZONE_REPRESENTATION;

extern int	red_gc_all_count, red_gc_mark_count, red_gc_unmarked_count, flag_red_management;

extern int	MAX_MEM, MAX_TREE_USAGE, MAX_RESULT_USAGE, MEMORY_START_VI, 
		MAX_RESULT_STACK_HEIGHT, MAX_RT_HEIGHT, MASK_MARK;


extern int	ichild_count, ichild_link_count; 
extern int 	bchild_count, bchild_link_count;

extern struct red_type	*NORM_FALSE, *NORM_TRUE, *NORM_NO_RESTRICTION;

extern struct child_stack_frame_type *CHILD_STACK; 

extern int	TOP_CHILD_STACK; 
extern int	TOP_LEVEL_CHILD_STACK, *LEVEL_CHILD_COUNT; 
extern int	HEIGHT_CHILD_STACK, HEIGHT_LEVEL_CHILD_STACK; 

extern int 
  flag_reduce, 
  red_count, 
  result_count, 
  ichild_count; 
  
extern int	count_top_level_child_stack, 
		count_top_child_stack; 
		  
extern int    USER_TOP, USER_LIMIT;
extern int		TOP_LEVEL_RESULT_STACK,
			*MASK_STACK, *MASK_STACK_REFERENCED, *MASK_STACK_MULTIPLE;

extern char	BUFFER_LINE[256];

extern int
  red_count_clear(), 
  red_free(), 
  red_count_test(), 
  red_parent_set(), 
  red_parent_get(), 
  red_print(), 
  red_check_ooo(); 
  

extern void
  red_init_result(), red_clear_result(), 
  red_init_result_array(), red_clear_result_array(), 
  red_init_result_with_bounds(), red_clear_result_with_bounds(),
  red_clear_result_references(),
  red_clear_references(),
  red_init_double_result(), red_clear_double_result();


#define red_shared	hash_share_diagram_add
#define red_register	hash_share_diagram_add

extern struct red_type 
  *red_CDD(), 
  *red_bottom_ordering(struct red_type *d), 
  *red_bop(int, struct red_type *, struct red_type *), 
    /* red_bop(op, dx, dy) returns a new red as the result of a binary operation. */
  *red_complement(struct red_type *), 
  *zone_complement(struct red_type *), 
  *red_space_subtract(struct red_type *, struct red_type *), 
  *red_subtract_iterative(
    int, 
    int 
  ),  
  *red_super_intersect_self(), *red_super_intersect_external(),
  *bdd_atom(
    int, 	// vid, 
    int	 	// value
  ), 
  *ddd_atom(
    int, 	// vi, 
    int, 	// lb, 
    int  	// ub
  ), /* create a literal ddd_atom(vi, lb, ub); */
  *fdd_atom(
    int, 	// vi, 
    float, 	// lb, 
    float  	// ub
  ), /* create a literal fdd_atom(vi, lb, ub); */
  *dfdd_atom(
    int, 	// vi, 
    double, 	// lb, 
    double  	// ub
  ), /* create a literal dfdd_atom(vi, lb, ub); */
  *crd_atom(
    int, // vi
    int  // ub 
  ), /* create a literal crd_atom(vi, ub); */

  *red_alloc(),
  *red_subsume(), *red_exclude_with_reduction(),
  *red_register(),
  *bdd_new(
    int			, 
    struct red_type	*, 
    struct red_type	*
  ), 
  *ddd_new(int),
  *crd_new(int),
  *fdd_new(int), 
  *dfdd_new(int), 
  *bdd_lone_subtree(
    struct red_type *, 
    int, 
    int
  ), 
  *bdd_one_constraint(
    struct red_type	*, 	// *d, 
    int			, 	// vid, 
    int				// value 
  ), 
  *bdd_2_constraints(
    struct red_type	*, // *false_child, 
    struct red_type	*, // *true_child, 
    int			// vi
  ),
  *ddd_lone_subtree(
    struct red_type	*, 	// *d
    int			, 	// vi
    int			, 	// lb,  
    int				// ub 
  ), 
  *fdd_lone_subtree(
    struct red_type	*, 	// *d
    int			, 	// vi
    float		, 	// lb,  
    float			// ub 
  ), 
  *dfdd_lone_subtree(
    struct red_type	*, 	// *d
    int			, 	// vi
    double		, 	// lb,  
    double			// ub 
  ), 
  *red_assign_interval(
    struct red_type	*, 
    int			, 
    int			, 
    int
  ), 
  *red_assign_float_interval(
    struct red_type	*, 
    int			, 
    float		, 
    float
  ), 
  *red_assign_double_interval(
    struct red_type	*, 
    int			, 
    double		, 
    double
  ), 
  *ddd_root_one_child(), 
  *ddd_one_constraint(
    struct red_type	*, 	// *d, 
    int			, 	// vid, 
    int			, 	// lb, 
    int				// ub
  ), 
  *ddd_project_through_one_constraint(), 
  *fdd_one_constraint(
    struct red_type	*, 	// *d, 
    int			, 	// vid, 
    float		, 	// lb, 
    float			// ub
  ), 
  *dfdd_one_constraint(
    struct red_type	*, 	// *d, 
    int			, 	// vid, 
    double		, 	// lb, 
    double			// ub
  ), 
  *crd_lone_subtree(
    struct red_type	*, 	// *d
    int			, 	// vi
    int				// ub 
  ),
  *crd_one_constraint(
    struct red_type	*, 	// d, 
    int			, 	// zid, 
    int				// ub
  ), 
  *zone_assign_bound(), 
  *zone_subtract_interval(), *zone_extract_interval(), *zone_subtract(), 
  *zone_untimed_subtract(), 
  *red_eliminate_magnitudes(), 
  *red_convex_hull();

extern int	red_size(), variable_occurrence_check(), simple_red_memory();

extern void
  init_red_management(), init_reorder_management(), 
  report_red_management(), update_memory_usage(),
  print_op(), red_clear_useful(),
  red_print_graph(), /* print a red structure in tree format. */
  red_print_graph_with_templates(), /* print a red structure in tree format. */
  red_print_formulus(),
  red_print_graph_depth(),
  red_print_line(), /* print a red formulus in one line */
  red_print_line_break();
  
extern int
  op_length(), string_op(); 


extern int 
  clear_vop(), red_time_inactive();

extern void 
  last_ichild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    int			*, 
    int			*
  ), 
  advance_ichild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    int			*, 
    int			*
  );

extern void 
  last_fchild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    float		*, 
    float		*
  ), 
  advance_fchild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    float		*, 
    float		*
  );

extern void 
  last_dfchild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    double		*, 
    double		*
  ), 
  advance_dfchild( 
    struct red_type	*, 
    struct red_type	*, 
    int			*, 
    int			*, 
    double		*, 
    double		*
  );

extern struct red_type	*red_through_all_invariance();

extern struct red_type
   *red_process(),
   *red_variable_eliminate(
     struct red_type	*, 
     int	
   ),
   *red_multi_variables_eliminate(
     struct red_type	*, // *d, 
     int		, // vix, 
     int		// viy
   ), 
   *red_variable_sim_eliminate(
     struct red_type	*, 
     int 
   ), 
   *red_time_clock_sim_eliminate(
     struct red_type	*, 
     int 
   ), 
   *red_type_eliminate(),
   *red_pi_type_eliminate(),
   *red_switch_primed_and_umprimed(), 
   *red_lower_all_primed(
     struct red_type *d
   ),
   *red_lift_all_umprimed(
     struct red_type *d
   ), 
   *red_qsync_eliminate(), 
   *red_local_eliminate(),
   *red_proc_eliminate(
     struct red_type	*, // *d, 
     int		, // pi_lb_proc
     int		// pi_ub_proc
   ),
   *red_peer_eliminate(
     struct red_type	*, // *d, 
     int		// pi_peer
   ),
   *red_time_eliminate(),
   *red_abstract_lazy(
     struct red_type * 
   ), 
   *red_nonmodal_clock_eliminate(),
   *red_time_clock_eliminate(struct red_type *, int),
   *red_diagonal_eliminate(), 
   *red_time_clock_eliminate_replace(),
   *red_time_clock_inc(),
   *red_pi_eliminate(), *red_sync_place_eliminate(), *red_all_trigger(),
   *red_role_type_eliminate(
     struct red_type	*, // *d 
     int, 		// type, 
     int		// flag_roles
   ), 
   *red_pi_permute(),
   *red_switch_vi(),
   *red_inc(), *red_inc_clock(), *red_inc_off(), *red_to_frac(),
   *red_inc_mod(), *red_inc_mod_given(), *red_inc_digit(), *red_inc_digit_by_one(),
   *red_frac_smooth(), *red_infinity_smooth(),
   *red_all_infinity_smooth(),
   *red_clock_int_equal(),
   *red_clock_int_less(),
   *red_action_assign_variable_bck(),
   *red_action_assign_variable_fwd(),

  *red_trigger_abstraction(),
   *red_only_xi();

extern void
  red_measure_time_clock(
    struct red_type *d, 
    int ci, 
    int *lb_ptr, 
    int *ub_ptr
  ); 
  
extern void 
  ichild_stack_push(
    struct red_type	*, 	// *d, 
    int			, 	// lb 
    int				// ub 
  ), 
  fchild_stack_push(
    struct red_type	*, 	// *d, 
    float		, 	// lb 
    float			// ub 
  ), 
  dfchild_stack_push(
    struct red_type	*, 	// *d, 
    double		, 	// lb 
    double			// ub 
  ), 
  bchild_stack_push(
    struct red_type	*, 	// *d, 
    int				// ub 
  ), 
  bchild_stack_insert(
    struct red_type	*, 	// *d, 
    int				// ub 
  ), 
  bchild_stack_restrict(
    int			, 	// evi, 
    struct red_type	*, 	// *d, 
    int				// ub 
  ), 
  bchild_stack_checkpush(
    struct red_type	*, 	// *d, 
    int				// ub 
  );
  
extern char	*string_diagram(); 


extern int	red_test(), red_order_check();

extern int	red_trigger_xtion_count(), red_path_count(), 
		red_discrete_model_count(); 
extern float	red_volume_CDD();


extern struct red_type	
  *red_time_upperbounded(), 
  *red_var_absence(), 
  *red_var_presence(); 

