// variable that tells us what we have parsed. 
extern char 			*model_file_name, 
				*spec_file_name, 
				*output_file_name;

extern struct red_type	*dt1, *dt2; 

extern int	TYPE_PARSE_RESULT; 

extern int	WINDOW_WIDTH, WINDOW_HEIGHT; 
extern int	FLAG_EXP_FLIPPING_PRIMED; 

extern struct parse_variable_type	
  *declare_local_discrete_list,
  *declare_local_float_list,
  *declare_local_double_list,
  *declare_local_pointer_list,
  *declare_local_bdd_list, 
  *declare_local_clock_list,
  *declare_local_dense_list,
  *declare_local_qsholder_list,
  *declare_local_synchronizer_list,
  *declare_global_discrete_list,
  *declare_global_float_list,
  *declare_global_double_list,
  *declare_global_pointer_list,
  *declare_global_bdd_list, 
  *declare_global_clock_list,
  *declare_global_dense_list,
  *declare_global_stream_list,
  *declare_global_synchronizer_list,
  *declare_global_rel_list,
  *declare_local_rel_list;

extern struct parse_variable_type 
  *declare_stack_discrete_list; 
extern int
  count_stack_discrete; 

extern struct parse_variable_type 
  *declare_stack_float_list; 
extern int
  count_stack_float; 

extern struct parse_variable_type 
  *declare_stack_double_list; 
extern int
  count_stack_double; 

extern int
  declare_global_rel_clock_count,
  declare_local_rel_clock_count,
  declare_spec_rel_clock_count,
  declare_global_rel_discrete_count,
  declare_local_rel_discrete_count,
  declare_spec_rel_discrete_count,
  declare_global_rel_count,
  declare_local_rel_count,
  declare_spec_rel_count, 
  sync_place_count; 
					
extern int					process_name_index; 
extern struct indexed_structure_link_type	*process_list; 


extern int			declare_inline_exp_count; 
extern struct ps_bunit_type	*declare_inline_exp_list; 
      

extern int	count_memory; 

extern struct ps_memory_link_type 
  *memory_list; 


extern struct parse_variable_type 
  *var_prob, 
  *var_probw, 
  *var_mode, 
  *var__sp, 
  *var__retmode, 
  *var_zero, 
  *var_time, 
  *var_modal_clock, *var_zeno_clock, 
  *var_delta, *var_neg_delta, 
  *var_deltap, *var_neg_deltap, 
  *var_play_time, 
  *var_prob_dense;

extern int	TYPE_PARSE_CHOICE; 
 
extern int	STATUS_FORMULA_CHOICE; 

extern struct ps_exp_type		*PARSER_INPUT_FORMULA; 
extern struct parse_redlib_sync_xtion_type 
  *PARSER_INPUT_SYNC_XTION; 
extern struct parse_xtion_type	
  *parse_xtion_list; 
extern struct parse_statement_type	*PARSER_INPUT_ACTIONS; 
extern struct ps_quantify_link_type	*PARSER_QUANTIFICATION_LIST; 

extern void
  get_rationals(), get_rational_range(), 
  get_interval_rationals(); 

extern int
  get_integer_range(
    struct ps_exp_type *, // psub
    int			, // pi
    int			*, // lbptr
    int			*, // ubptr
    float		*, // flbptr
    float		*  // fubptr 
  ); 

extern struct statement_type		*rec_statement_fillin(); 


extern struct parse_variable_type	*sync_place_start_var, 
					*sync_place_stop_var;

extern struct parse_assignment_type	*declare_clock_assign_pattern_list;
extern int				declare_clock_assign_pattern_count;

extern int  FLAG_ANY_PROCESS, /* = -1 - PROCESS_COUNT */ 
            INDEX_LOCAL_IDENTIFIER, /* = -2 - PROCESS_COUNT */ 
            FLAG_ANY_VALUE, /* = -3 - PROCESS_COUNT */ 
            FLAG_ANY_VARIABLE, /* = -4 - PROCESS_COUNT */ 
            FLAG_NO_VALUE; /* = -5 - PROCESS_COUNT */ 

extern struct parse_mode_type		*declare_mode_list;
extern int				declare_mode_count;

extern struct parse_module_type		*root_module, *module_stack; 
extern int				declare_module_count; 

extern struct parse_xtion_type		*declare_xtion_list, *XTION_NULL;
extern int				declare_xtion_count;

extern struct parse_hyper_xtion_type	*parse_hyper_xtion_list;
extern int				parse_hyper_xtion_count;

extern struct ps_exp_type		*PARSE_SPEC, 
					*PARSE_INITIAL_EXP, 
					*ORIG_PARSE_INITIAL_EXP;

extern struct ps_exp_type		*PEXP_EREACHABLE;

extern int				MAX_TERM_COUNT;

extern int				PARSE_GLOBAL_SEQ_COUNT;
extern struct ps_exp_type		**PARSE_DEBUG_EXP;


extern struct red_type	
	*local_diagram_from_string(), 
	*global_diagram_from_string(); 
extern struct ps_exp_type	*spec_from_string(); 

 
extern void 	free_ps_exp(), free_ps_st(), free_ps_exp_list();

extern void	print_parse_variables();

extern void 	print_parse_xtion(), print_parse_xtion_string();

extern void	print_parse_hyper_xtion(), print_parse_hyper_xtions();

extern void 	print_parse_procs();

#define	FLAG_GENERAL_PROCESS_IDENTIFIER	-1 

extern int
  print_parse_subformula_structure(), 
  print_parse_subformula(), 
  pcform(); 
  
extern void	print_ps_exp_list(); 

extern int
  exp_var_status_parse_variable(
    struct parse_variable_type	* // *pv
  ), 
  process_command_line(), 
  parse_subformula_length(); 


extern int			search_mode_index(char *mname); 
extern struct parse_mode_type	*search_parse_mode(char *mname); 

extern int 
  parse_mode_xtion_system_spec();


extern void 
  parse_system_description(
    char	*model_file_name,  
    char	*output_file_name, 
    int	process_count, 
    int	flag_task 
  ); 

extern void 
  PROCESS_fillin(); 
extern struct red_type	
  *red_no_event_set(
    struct red_type	*events 
  ); 

extern struct xtion_type	*xtion_entry_fillin();

extern struct ps_exp_type	*CLOCK_POS, *CLOCK_NEG; 

extern inline int	vi_in_primed_context(
  struct ps_exp_type	*psub, 
  int			pi
); 

extern struct red_type	
  *filter_sync_xi_restriction(),
  *prepare_sync_xtions(), 
  *red_global_rel_discrete(), *red_local_rel_discrete(), 
  *filter_symmetry_xi_restriction(), 
  *red_check_sync_proc_holders(), 
  *red_keep_pure_sync_bulk_with_qfd_syncs(struct red_type *d), 
  *red_keep_pure_sync_bulk(struct red_type *d), 
  *red_add_events(struct red_type *, int), 
  *add_trigger(), 
  *add_post_condition(), 
  *red_operand_indirection(), 
  *eliminate_simple_qfd_sync(), 
  *red_ec_one_strongest_postcondition_sync_bulk(), 
  *add_event_counts_from_xtions(), 
  *red_add_trigger_sync_bulk(
    struct red_type *
   ), 
  *red_add_lazy_trigger_sync_bulk(
    struct red_type *, 
    struct red_type *
  ) 
;

extern char		parse_error[256];

char			*input_file_name;

extern char		*rstring, *ps_exp_type_name(); 



