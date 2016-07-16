// Special variable indices 
extern int	VI_TIME, VI_PROB_DENSE; 

extern void 	red_register_arg(int, char **); 
extern int	red_argc(); 
extern char	**red_argv(); 

extern struct ps_exp_type	*exp_mode; 

extern void	test_float(), tpsubve(struct ps_exp_type *); 

extern inline int	valid_mode_index(int mi);   

extern struct name_link_type 
  *push_name_stack(
    char			*, 
    struct name_link_type	*
  ), 
  *pop_name_stack(
    struct name_link_type	*
  ), 
  *insert_name_cycle(
    struct name_link_type	*, 
    char			*, 
    int				*
  ); 


extern char
  *combine_name_cycle(
    struct name_link_type	**, 
    int				*
  ); 


extern int
  check_name_list(
    char			*, 
    struct name_link_type	*
  ); 
  

extern void 
  print_name_list(); 

extern struct index_link_type	
  *add_index(
    struct index_link_type	*, // *list, 
    int				// i 
  ), 
  *add_index_count(
    struct index_link_type	*, // *list, 
    int			  	, // i, 
    int			 	* // *count_ptr 
  ), 
  *remove_index_head(
    struct index_link_type	* // *list
  ); 

extern void 	print_index_list( 
  struct index_link_type	* // *list
); 

extern int
  check_trace(
    int , // iteration count 
    int   // synchronous transition index
  ), 
  check_print_trace(
    int, 		// iteration count
    int,   		// synchronous transition index, 
    struct red_type * 	// d
  ); 

extern int			free_index_list();

extern struct index_pair_link_type	
  *add_index_pair(
    struct index_pair_link_type	*, 
    int, 
    int 
  );
extern int 
  free_index_pair_list(
    struct index_pair_link_type	*
  );

extern struct indexed_structure_link_type	*add_indexed_structure_count();
extern int					free_indexed_structure_list();

extern struct red_link_type	*add_red_tail(
  struct red_link_type	*tail, 
  struct red_type 	*d
); 
extern void	free_red_list(struct red_link_type *list); 

extern void	print_red_list(struct red_link_type *list); 

extern struct ps_exp_type* CML_FORM;
extern struct red_type* RED_CML;

extern int			MEMORY_SIZE, 
				MEMORY_DISCRETE_SIZE, 
				MEMORY_FLOAT_SIZE, 
				MEMORY_DOUBLE_SIZE, 
				MEMORY_START_VI, 
				DEPTH_CALL, HEIGHT_STACK_FRAME, 
				STACK_START_OFFSET; 

extern int			MODE_COUNT; 
extern struct mode_type		*MODE;

extern int			MODULE_COUNT; 
extern struct module_type	*MODULE; 

extern int			XTION_COUNT, REDUCTION_XTION_COUNT;
extern struct xtion_type	*XTION;

extern struct ps_exp_type	*SPEC_EXP;

extern int			DEPTH_SIG_OPPONENT, DEBUG_RED_COUNT, DISTANCE_ZENO;


extern struct red_type	**RT, **RED_USER_STACK;
extern int		RT_TOP, RT_LIMIT, RT_DYNAMIC, USER_TOP, USER_LIMIT; 
 
extern struct red_type	*RED_INITIAL, *RED_CLOCK_INVARIANCE,
			*RED_GLOBAL_INVARIANCE, **RED_INVARIANCE,
			*RED_URGENT,
			*RED_PLAIN_NONZENO, *RED_APPROX_NONZENO,
			*RED_MONITOR, **DEBUG_RED,

			**FILTER_NOT_NONZERO_XTIVE_LEFT,
			**FILTER_NOT_NONZERO_XTIVE_RIGHT,
			***FILTER_NOT_DIRECT_ZERO_EQUIVALENCE,
			***FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE,
			***FILTER_NEITHER_LAST_NOR_FIRST_ZERO_EQUIVALENCE,
			***FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE,

		        **FILTER_INSTANCE_RESTRICTION,
			*FILTER_AI_FINAL,
			*FILTER_AI_INTER,
			***PROCESS_REVERSE, ***PROCESS_NEG_REVERSE;
			
extern int		FLAG_REACHABLE_CHANGE;

extern int	bug_flag1, bug_flag2, bug_flag3, bug_flag4;

extern int	ITERATION_COUNT, EXPLORE, ABSTRACT;
extern int	ITERATE_PI, ITERATE_XI, ITERATE_SXI;

extern int			PROCESS_COUNT;
extern struct process_type	*PROCESS;

extern int			MEMORY_COUNT;
extern struct memory_type	*MEMORY; 


extern int	*CLOCK, **ZONE, ***variable_index;
extern struct sync_type	*GSYNC;

extern int
	MODE_COUNT,
	*GLOBAL_COUNT,
	*LOCAL_COUNT,
        CUR_VAR_COUNT,
	CLOCK_COUNT,
	CLOCK_INEQUALITY_COUNT,
	MAX_ATTACH_COUNT,
	MAX_SYNC_ACTION_COUNT,
	MAX_OP_CLOCK_COUNT,
	GLOBAL_DECLARE_COUNT, GLOBAL_GROUP_COUNT, GLOBAL_SYSTEM_OVERHEAD_COUNT,
  	LOCAL_GROUP_COUNT, LOCAL_DECLARE_COUNT, LOCAL_SYSTEM_OVERHEAD_COUNT;

extern int	OFFSET_MODE, OFFSET__SP, OFFSET__RETMODE, 
		CLOCK_POS_INFINITY, CLOCK_NEG_INFINITY,
		ALL_CLOCK_TIMING_BOUND, 
		ALL_RATE_BOUND;

extern int	OFFSET_CLOCK, OFFSET_CONNECTING, OFFSET_MODE;

extern int 	GSTATUS[10]; 
extern inline int	check_oapprox_lazy_exp(); 


extern char	*TASK_TYPE_NAME;

extern int			SYNC_XTION_COUNT, DEPTH_ENUMERATIVE_SYNCHRONIZATION;
extern struct sync_xtion_type	*SYNC_XTION;
extern int			SYNC_XTION_COUNT_GAME;
extern struct sync_xtion_type	*SYNC_XTION_GAME;

extern struct dfs_stack_type	*DFS_STACK_TOP;

extern FILE	*RED_OUT;

int			BUG_VI, BUG_UB, BUG_UB_NUMERATOR, BUG_UB_DENOMINATOR;
struct hrd_exp_type	*BUG_HRD_EXP;

extern struct trace_frame_type	*TRACE_FRAME_STACK;
extern int			TRACE_FRAME_COUNT;

extern char	*inbuf; 
extern int	inbuf_size; 

extern inline int	arith_operation(
  int	op, 
  int	lhs, 
  int	rhs
); 

extern int	int_min(int, int), int_max(int, int); 
extern float	flt_min(float, float), flt_max(float, float); 
extern float	feps_plus(float), feps_minus(float); 
extern double	dble_min(double, double), dble_max(double, double); 
extern double	dfeps_plus(double), dfeps_minus(double); 

extern void	test_alloc(),
  get_line(), print_variables(), print_processes(), 
  print_gsyncs(), print_gsync(), 
  print_xtion(), print_xtions(), print_simple_xtion(), 
  print_sync_xtions(char *, struct sync_xtion_type *, int), 
  print_sync_xtion(int, struct sync_xtion_type *), 
  print_sync_xtion_lines(int, struct sync_xtion_type *), 
  print_sync_xtion_ptr(), 
  print_constraint(), report_status(),
  print_hyper_xtion(), print_hyper_xtions(),
  print_sync_hyper_xtion(), print_sync_hyper_xtions(),
  debug_trace_bck(); 
		
extern void	print_mode(), print_modes(), print_xtion_line(), print_action_line(); 

extern struct red_type	*debug_filter();

extern double	reset_acc_time(int), report_acc_time(int, int); 

extern float	simple_cpu_time(); 

extern void 	memory_fault_test(), sw_stdout(), sw_out(), 
		print_simple_time(), print_cpu_time();

extern int	compare_CDD(), intlen(), hexlen(), test_clocks();

extern char	*str_ineq_op(), *str_arith_op(), *strcat(), *itos();

extern struct red_type 	*red_variable_eliminate(), *red_pi_eliminate(), *extract_one_instance(),
			*probe();
			
extern struct red_type	*red_role_simple_zeno(), *red_role_deadlock(); 

extern struct red_type	*red_analysis_untimed(), *red_analysis_abstract(); 

extern void	bk(), 
		release_all_rule_related_space(int), 
		release_all_space(), 
		print_unreachable_result(), print_reachable_result(), 
		debug_trace_bck(), debug_trace_fwd(), 
		allocdmy(), freedmy(), exit_with_summary(), 
		memory_fault_test(), sw_stdout(), sw_out(), 
		free_statement(); 

extern float	cpu_time_parsing; 

extern int 
  GARBAGE_OVERHEAD, 
  MASK_MARK, 
  MASK_CLEAR; /* Used for garbage collection. */ 

extern int 
  dirtydmy(), 
  init_garbage_management(); 


extern int	
  redlib_parse(
    char	*mf_name, // model file name 
    char	*of_name, // output file name 
    int		process_count, 
    int		flag_task  
  ),  
  redlib_main(); 


extern int
  process_command_line(); 
  
extern void
  check_options(); 


// The following structures are for the computation of system elapsed time.
extern struct timeval 		SYSTEM_START_TIME;
extern struct timezone 	TIME_ZONE_P;

extern double	red_system_time(), red_user_time(); 

extern int	red_memory(); 


extern void	print_resources(); 

extern int	leng_string_var( 
  char		*head,  
  char		*tail, 
  char		*f, 
  va_list	args 
); 
extern char	*string_var_given_length(
  int		real_len,  
  char		*head, 
  char		*tail, 
  char		*f,  
  va_list	args 
);  
