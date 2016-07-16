#define FLAG_DELAYED_EVALUATION	1
#define FLAG_LAZY_EVALUATION	0

#define FLAG_DELAYED_EVALUATION	1
#define FLAG_LAZY_EVALUATION	0

#define	FLAG_XVI_TIME_ELIMINATE		-1 
#define	FLAG_XVI_QSYNC_ELIMINATE	-2 
#define	FLAG_XVI_CLOCK_LOWER_EXTEND	-3 
#define	FLAG_XVI_CLOCK_UPPER_EXTEND	-4 
#define	FLAG_XVI_LOCAL_ELIMINATE	-5 

extern int	W_PI; 
extern int	FLAG_POLICY_EVALUATION; 

extern struct a23tree_type 
  *EXP_TREE; 
extern struct ps_exp_type 
  *PS_EXP_TRUE, 
  *PS_EXP_FALSE,  
  *PS_EXP_LOCAL_IDENTIFIER, 
  *PS_EXP_GLOBAL_IDENTIFIER, 
  *PS_EXP_MODE, 
  *PS_EXP__SP, 
  *PS_EXP__SP_PLUS, 
  *PS_EXP__SP_MINUS, 
  *PS_EXP__RETMODE, 
  *PS_EXP_ONE, 
  *PS_EXP_NEG_ONE, 
  *PS_EXP_ZERO; 


extern int 
  op_ineq_reverse(int); 

extern char 
  *flexible_parse_mode_name(int); 


extern void 
  collect_value_intervals(
    int			, // pi, 
    struct ps_exp_type	*, // lhs to be evaluated in an assignment. 
    struct ps_exp_type	*, // exp to be evaluated. 
    struct red_type	* // *red_lazy_space 
  ),
  decollect_value_intervals(); 





extern void 
  get_rationals(), get_rational_range(), 
  get_interval_rationals(); 


extern struct ps_exp_type 
  *spec_from_string(); 

 
extern void 
  init_exp_pre_management(), 
  init_exp_management(), 
  ps_exp_free(), free_ps_st(), 
  free_ps_exp_list(), free_ps_exptree_list(), 
  ps_fairness_free_list(), 
  fillin_indirect_reference(
    int			, // pi, 
    struct ps_exp_type	* // *psub 
  );



extern struct red_type
  *lazy_subtree(
    struct red_type	*, // *false_child, 
    struct red_type	*, // *true_child, 
    int			, // pi, 
    struct ps_exp_type	* // *lazy_exp
  ), 
  *lazy_2_cases(
    struct red_type	*, // *false_child, 
    struct red_type	*, // *true_child, 
    int			, // pi, 
    struct ps_exp_type	* // *lazy_exp
  ), 
  *lazy_atom(
    int			, // pi, 
    struct ps_exp_type	* // *lazy_exp
  ), 
  *lazy_one_constraint(
     struct red_type	*, // *d, 
     int		, // pi, 
     struct ps_exp_type	* // *lazy_exp
  ), 
  *lazy_one_neg_constraint(
     struct red_type	*, // *d, 
     int		, // pi, 
     struct ps_exp_type	* // *lazy_exp
  ); 

extern int
  print_parse_subformula_structure(), 
  print_parse_subformula(), 
  pcform(); 
  
extern void 
  print_ps_exp_list(), 
  release_all_ps_exp(); 

extern int
  parse_subformula_length(); 


extern struct parse_indirect_type	*ps_exp_indirect_list_copy(
  struct parse_indirect_type	* // *list
);


extern struct ps_exp_type 
  *ps_exp_copy(
    struct ps_exp_type	*
  ), 
  *spec_global(
    struct ps_exp_type	*, // *psub, 
    int			, // pi, 
    int			, // flag_delayed_evaluation, 
    int			// depth  
  ), 
  *ps_exp_alloc(int), 
  *ps_exp_share(struct ps_exp_type *), 
  *ps_exp_instantiate(), 
  *add_neg(), 
  *push_neg(), 
  *rewrite_modal_timing(), 
  *exp_atom(
    int, //	type, 
    int, //	value, 
    char * //	*name
  ), 
  *exp_boolean( 
    int 		, //  type,  
    struct ps_exp_type 	*, // *e1, 
    struct ps_exp_type	*  // *e2   
  ), 
  *exp_arith(
    int 		, // 	op, 
    struct ps_exp_type	*, // *lhs, 
    struct ps_exp_type	*  // *rhs 
  ), 
  *ps_exp_project(
    int			, // type, 
    struct ps_exp_type	*, // *child, 
    int			 // vi
  ), 
  *exp_qexp(
    int			, // path,  
    char		*, // *qname, 
    struct ps_exp_type	*, // *lb_exp, 
    struct ps_exp_type	*, // *ub_exp, 
    struct ps_exp_type	*  // *qchild 
  );   

extern struct red_type	
  *red_lazy_project(
    struct red_type	*, // *false_child, 
    struct red_type	*, // *true_child, 
    struct red_type	*, // *root, 
    int			, // op_project, 
    int			// arg_project   
  ); 

extern void	insert_sorted_blist_dummy_head(
  int			, // type, 
  struct ps_exp_type	*, // *subexp, 
  struct ps_bunit_type	*, // *dummy_head, 
  int			* // *bcount_ptr 
);

extern struct ps_fairness_link_type	*insert_sorted_flist(
  struct ps_exp_type		*, // *fairness, 
  int				,  // status,  
  struct ps_fairness_link_type	*, // *list, 
  int				*  // *fcount_ptr  
); 


// The return flag values of get_value() and get_exp_value().  
#define FLAG_EXP_NO_VALUE	0
#define	FLAG_EXP_SPECIFIC_VALUE	1
#define FLAG_EXP_ANY_VALUE	2 
extern int
  get_value(
    struct ps_exp_type	*, // *psub, 
    int			, // pi, 
    int			* // *flag_ptr
  ), 
  get_exp_value(
    struct ps_exp_type	*, // *psub, 
    int			, // pi, 
    int			, // control_flag, 
    int			* // *result_flag_ptr
  );  
  

extern int 
  ps_exp_comp(), 
  qfd_variable_index(
    struct parse_variable_type 	*, 	// *var, 
    char			*	// *qname
  ), 
  qfd_value(
    char * // *qname
  ), 
  clock_index(), rec_get_clock_value(), 
  get_variable_index(  
    struct ps_exp_type	*, // *var, 
    int			 // wpi
  ), 
  get_address(
    struct ps_exp_type	*, 
    int			, // pi
    int			* // *flag_ptr 
  ), 
  get_vi(
    struct ps_exp_type	*, 
    int			, // pi
    int			* // *flag_ptr 
  ), 
  check_proc_and_global_in_exp(
    struct ps_exp_type	*, 
    int	
  ); 


extern struct red_type	
  *red_discrete_value(
    int			, // pi, 
    struct ps_exp_type	* // *psub  
  ), 
  *red_discrete_value_top_level(
    int			, // pi, 
    struct ps_exp_type	*, // *psub, 
    int			, // lb, 
    int			 // ub   
  ), 
  *red_add_value(
    int			, // cx, 
    struct red_type	*, // *dx, 
    int			, // cy, 
    struct red_type	* // *dy 
  ), 
  *red_add_value_top_level(
    int			, // cx, 
    struct red_type	*, // *dx, 
    int			, // cy, 
    struct red_type	*, // *dy, 
    int			, // lb, 
    int			 // ub  
  ), 
  *red_multiply_value(
    struct red_type	*, // *dx, 
    struct red_type	* // *dy  
  ), 
  *red_multiply_value_top_level(
    struct red_type	*, // *dx, 
    struct red_type	*, // *dy, 
    int			, // lb, 
    int			 // ub 
  ), 
  *rec_delayed_operand_indirection(
    struct ps_exp_type	*
  ), 
  *red_operand_indirection( 
    struct ps_exp_type	*, // *var,  
    int			// wpi 
  ), 
  *red_delayed_operand_indirection( 
    struct ps_exp_type	*, // *var,  
    int			, // wpi 
    struct red_type	* // *red_lazy_space 
  ), 
  *red_discrete_ineq(
    struct ps_exp_type	*, // *psub, 
    int			   // pi 
  ),  
  *red_clock_ineq(
    struct ps_exp_type	*, // *psub, 
    int			   // pi 
  ),
  *red_local(
    struct ps_exp_type	*, // *psub, 
    int			, // pi, 
    int			// depth
  ), 
  *rec_local(
    struct ps_exp_type	*, // *psub, 
    int			// depth
  ), 
  *red_global(
    struct ps_exp_type	*, // *psub, 
    int			, // flag_delayed_evaluation, 
    int			// depth 
  ), 
  *rec_delayed_exp_value(
    struct ps_exp_type	* // *psub 
  ), 
  *red_delayed_exp_value(
    struct ps_exp_type	*, // *psub, 
    int			, // pi, 
    struct red_type	* // *red_lazy_space
  ),  
  *red_delayed_eval(
    struct red_type	*, // *red_lazy_predicate, 
    int			, // pi, 
    struct red_type	* // *red_lazy_space 
  );


extern char 
  *ps_exp_type_name(); 

extern void 
  clear_working(
    int // mask
  ), 
  mark_working_in_red(
    struct red_type	*, // the red in which vi's are to be marked 
    int			, // mask
    int			*, // vi_min, 
    int			*  // vi_max
  ), 
  mark_working(
    struct ps_exp_type	*, // the exp in which vi's are to be marked.  
    int			, // mask
    int			*, // vi_min
    int			* // vi_max
  ); 

extern struct ps_exp_type 
  *adjust_specific_pi(
    struct ps_exp_type	*, 
    int
  ); 


 
