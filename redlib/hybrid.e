#define	FLAG_PRIMED	1
#define	FLAG_UMPRIMED	0

extern int
	DENSE_COUNT,
	MASK_HYBRID_LENGTH,
	MASK_HYBRID_LIFTED_VI,
	MASK_HYBRID_VI_BASE,
	FLAG_HRD_EXP_STATIC, 
	FLAG_LOCAL_HYBRID_VARIABLES, 
	hchild_count, hfchild_count, hrd_exp_count, hrd_term_count;

extern struct a23tree_type
	*hrd_exp_tree;

extern int
	*w_hybrid_coeff_numerator, *w_hybrid_coeff_denominator, *w_hybrid_vi,
	w_hybrid_offset_numerator, w_hybrid_offset_denominator;

extern struct action_type	*W_ACT;
extern struct parse_term_type	*W_TERM;
extern int			W_TERM_COUNT;
extern struct hrd_exp_type	**HE_CLOCK_LB;

extern struct red_type		*red_test_hybrid;

extern char
	*linear_name();

extern void
	hrd_exp_free(),
	hrd_exp_parent_set(),
	hrd_exp_print(),
	hybrid_ub_add(),
	free_hrd_term_list(),
	print_rational(),
	hybrid_prepare_primed_invariance(),
	test_hybrid_time_progress(),
	test_hybrid();

extern struct hrd_term_link_type
	*hrd_term_insert();

extern int
	hrd_exp_comp(),
	hrd_comp(),
	rational_comp(),
	hrd_term_coeff_extract(),
	hrd_converse_test(),
	hrd_exp_converse_test(),
	hrd_exp_nop();

extern struct hrd_exp_type
	*converse_hrd_exp(),
	*test_hrd_exp,
	*hrd_exp_negative(),
	*hrd_exp_permute(),
	*hrd_exp_add(),
	*hrd_exp_alloc(),
	*hrd_exp_converse(),
	*hrd_exp_new(),
	*hrd_exp_array_new(),
	*hrd_exp_fillin(), 
	*hrd_exp_switch_vi(
	  struct hrd_exp_type *, //	*he;
	  int,			// vi, 
	  int			// vj
	) 
;


extern char
	*hfchild_stack_push(),
	*hchild_stack_push(),
	*hchild_stack_restrict(),
	*hchild_stack_checkpush();



extern struct red_type
	*hdd_one_constraint(),
	*hrd_new(),
	*hdd_new(),
	*hrd_atom(),
	*red_hybrid_ineq(
	  struct ps_exp_type	*, 	// *psub, 
	  int 				// pi, 
	),
	*hrd_one_constraint(),
	*hrd_one_constraint_with_map(), 
	*hybrid_extract_upperhalf(),
	*hybrid_extract_lowerhalf(),
	*hybrid_root_extract_upperhalf(),
	*hrd_lone_subtree(),
	*hdd_lone_subtree(
	  struct red_type	*, 
	  int			, 
	  struct hrd_exp_type	*, 
	  int			, 
	  int			, 
	  int			, 
	  int
	), 
	*hybrid_bypass_DOWNWARD(),
	*hybrid_delta_transitivity_for_umprimed_variables(),
	*hybrid_delta_extend(),
	*hybrid_time_progress(),
	*hybrid_relative_eliminate(),
	*red_action_hybrid(
	  int, 
	  struct action_type *, 
	  int
	),
	*hybrid_parameter_extract(),
	*hybrid_given_primed_replace(),
	*hybrid_constant_replace(),
	*hybrid_eliminate_inconsistency_DOWNWARD(),
	*hybrid_eliminate_redundancy_DOWNWARD(),
	*hybrid_eliminate_redundancy_LOOKAHEAD(),
	*hybrid_abstract_precision(),
	*hybrid_abstract_magnitude(),
	*hybrid_subsume(),
	*hybrid_normalize(),
	*hybrid_parameter_reduce();


extern int	(*HRD_EXP_COMP)();
