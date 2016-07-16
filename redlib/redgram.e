extern int			TYPE_PARSE_CHOICE; 
extern struct ps_exp_type	*PARSER_INPUT_FORMULA; 
extern struct parse_xtion_type	*PARSER_INPUT_XTION_RULE; 


extern int  
  CURRENT_INLINE_FORMAL_ARGUMENT_COUNT; 
extern struct name_link_type	
  *CURRENT_INLINE_FORMAL_ARGUMENT_LIST; 

extern 	int	lineno, flag_line_start, 
		flag_other_type, PI_GRAM, 
		COEFF_POS; 

extern struct ps_exp_type 
	*VAR_POS, *VAR_NEG, *VARP, *INEQ_EXP; 

extern int	CUR_SCOPE[], TOP_SCOPE, CUR_VAR_TYPE; 

extern int
	qfd_var_undefined(),   
 	rec_analyze_value(), rec_analyze_variables(), 
 	next_qfd_valuation(),  
 	rec_get_value_coeff(); 

extern struct parse_variable_type 	*var_search(), *register_variable(); 

extern struct parse_xtion_type		*initialize_xtion(); 
extern struct parse_xtion_sync_type 	*add_parse_xtion_sync(); 

extern struct ps_exp_type
	*pexp_remove_neg(),  
	*ineq_analyze(), 
	*rec_ineq_analyze(); 

extern void 	init_qfd_value(); 

#define	FLAG_NO_PI_STATIC_EVAL	-1 
extern struct ps_exp_type	
  *exp_static_evaluation(
    struct ps_exp_type		*, 
    int				, 
    struct sync_xtion_type	*
  ); 

extern struct ps_exp_type		*ineq_atom(), *ineq_atom_analyze(), 
					*exp_boolean(), 
					*qfd_atom_analyze(), *exp_qexp(); 
extern struct parse_mode_type		*add_mode(); 
extern struct parse_assignment_type	*add_assignment(); 

#define	FLAG_INPUT_FILE		0
#define	FLAG_INPUT_STRING	1 
extern int	flag_redlib_input_source; 
extern char	*redlib_input_string; 
extern int	redlib_input_string_len; 
extern FILE	*redlibin; 

extern struct ps_exp_type	*shorthand_analysis();


struct instantiated_argument_type { 
  char					*formal_argument_name; 
  struct ps_exp_type			*instantiated_argument; 
  struct instantiated_argument_type	*next_instantiated_argument; 
}; 

struct actual_argument_frame_type { 
  struct instantiated_argument_type	*instantiated_argument_list; 
  struct actual_argument_frame_type	*next_actual_argument_frame; 
}; 

extern struct actual_argument_frame_type  
  *top_inline_stack; 

