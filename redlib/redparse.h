/***********************************************************
 *  (061106) 
 *  The interpretation of W_PI (or pi in parse formula) is now confusing. 
 *  We need the following new rules. 
 *  From now on, all parse formula interpretation will follow rules below. 
 *  pi = GLOBAL, 
 *  pi in [1,#PS], a true local identifier. 
 *  pi in [-1,-#PS], a peer identifier to process pi.  
 */
// Parameter constants to parser. 
#define	FLAG_GRAM_MODE_XTION_SYSTEM	1
#define FLAG_GRAM_GLOBAL_FORMULA	2
#define	FLAG_GRAM_LOCAL_FORMULA		3
#define	FLAG_GRAM_ROLE_SPEC		4 
#define	FLAG_GRAM_XTION			5
#define	FLAG_GRAM_QBF			6
#define	FLAG_GRAM_TCTL			7 






struct parse_redlib_party_link_type { 
  int					proc; 
  struct xtion_type			*xtion; 
  struct parse_redlib_party_link_type	*next_parse_redlib_party_link; 
};
  /* parse_redlib_party_link_type */  


struct parse_redlib_sync_xtion_type { 
  int					status, party_count; 
  struct parse_redlib_party_link_type	*party_list; 
};
  /* parse_redlib_sync_xtion_type */ 
  
  

#define	FLAG_FORMULA_CHOICE_GLOBAL	1
#define	FLAG_FORMULA_CHOICE_LOCAL	2 


//========================================================
#define	TYPE_PARSE_MODE_XTION_SYSTEM		1 
#define	TYPE_PARSE_SYNC_XTION			2
#define	TYPE_PARSE_GAME_ROLES			3 
#define	TYPE_PARSE_FORMULA_GLOBAL		4 
#define	TYPE_PARSE_FORMULA_GLOBAL_EVENTS	5 
#define	TYPE_PARSE_FORMULA_LOCAL		6
#define	TYPE_PARSE_QUANTIFY			7
#define	TYPE_PARSE_DEADLOCK			8
#define	TYPE_PARSE_ZENO				9
#define	TYPE_PARSE_TCTL				10
#define	TYPE_PARSE_BRANCHING_SIM		11
#define	TYPE_PARSE_BRANCHING_BISIM		12
#define	TYPE_PARSE_REDLIB_SESSION		13


#define	TYPE_GLOBAL		0
#define TYPE_GLOBAL_EVENT	1
#define	TYPE_LOCAL		2
#define TYPE_INITIAL		3
#define TYPE_MEM_OPTIONS	4 

#define	USE_POINTER		10
#define	USE_DISCRETE		11
#define	USE_CLOCK		12
#define	USE_SYNCHRONIZER	13

#define FLAG_SPECIFIC_VALUE		0
#define FLAG_SPECIFIC_FLOAT_VALUE	1
#define FLAG_UNSPECIFIC_VALUE		2


#define FLAG_REDLIB_FULL_PARSING	0
#define FLAG_REDLIB_ONLY_VAR_PARSING	1


#define FLAG_WINDOW_SIZE_UNKNOWN	-1
#define FLAG_MODE_POSITION_UNKNOWN	-1
#define FLAG_MODE_RECTANGLE		1
#define FLAG_MODE_OVAL			2
#define FLAG_MODE_TRIANGLE		3
#define FLAG_MODE_SHAPE_UNKNOWN		-1

#define FLAG_TRIANGLE_LEFTWARD		1 
#define FLAG_TRIANGLE_RIGHTWARD		2
#define FLAG_TRIANGLE_UPWARD		3
#define FLAG_TRIANGLE_DOWNWARD		4



struct parse_xtivity_type {
  struct parse_variable_type	*xtive_var;
  struct parse_xtivity_type	*next_parse_xtivity;
};


struct parse_union_sync_type { 
  int	lb, ub; 	
}; 

struct parse_union_bdd_type { 
  int	lb, ub; 	
}; 

struct parse_union_disc_type { 
  int	lb, ub; 	
}; 

struct parse_union_clock_type { 
  int	lb, ub; 	
}; 

struct parse_union_dense_type { 
  int	lb, ub; 	
}; 

struct parse_union_float_type { 
  float	lb, ub; 	
}; 

struct parse_union_double_type { 
  double	lb, ub; 
}; 

union parse_union_type { 
  struct parse_union_bdd_type		bdd; 
  struct parse_union_sync_type		sync; 
  struct parse_union_disc_type		disc; 
  struct parse_union_clock_type		clock; 
  struct parse_union_dense_type		dense; 
  struct parse_union_float_type		flt; 
  struct parse_union_double_type	dble; 	
}; 


struct parse_variable_type {
  char				*name;
  int				type, index, 
				status, // coincides with variable_type 
				parsing_status, // coincides with ps_exp_type
				lineno, 
				Q_xtion_count, 
#define	VAR_STREAM_HEAD_POS_INDEX	Q_xtion_count 
#define	STREAM_VI			Q_xtion_count 
				X_xtion_count;
#define	VAR_STREAM_DIRECTION_INDEX	X_xtion_count 
  union parse_union_type	u; 
  
  struct mode_rate_spec_type	*rate_spec; /* when this is an occ variable 
					  * for event fairness evaluation, 
					  * we use this to coercefully 
					  * point to the event ps_exp_type 
					  * expression set by parser.  
					  * Later, this expression is to 
					  * be coercefully transfered to 
					  * VAR[].MODE_RATE_SPEC.
					  */
  struct parse_xtivity_type	*xtivity_list;
  struct parse_variable_type 	*next_parse_variable;
};


struct parse_xtion_link_type {
  struct parse_xtion_type	*parse_xtion;
  struct parse_xtion_link_type	*next_parse_xtion_link;
};


#define	FLAG_RATE_LB_OPEN	1
#define	FLAG_RATE_UB_OPEN	2

struct parse_rate_spec_link_type { 
  int					status;
  char					*rate_var_name;
  struct parse_variable_type		*rate_var; 
  struct ps_exp_type			*rate_lb, *rate_ub; 
  struct parse_rate_spec_link_type	*next_parse_rate_spec_link;
};



struct parse_mode_type {
  char					*name, *src_lines;
  int					index, status, lineno, rate_spec_count,
					xtion_count, over_bound, 
					bound_left_open, 
					position_x, position_y, 
					shape, 
					rectangle_width, 
#define	oval_xradius			rectangle_width
#define	triangle_radius			rectangle_width
					rectangle_height, 
#define	oval_yradius			rectangle_height 
#define	triangle_direction		rectangle_height 
					color;
  struct ps_exp_type			*invariance_exp, *orig_invariance_exp;
  struct parse_mode_type 		*next_parse_mode;
  struct parse_xtion_link_type		*parse_xtion_list;
  struct parse_rate_spec_link_type	*parse_rate_spec_list;
};



struct parse_mode_link_type { 
  struct parse_mode_type	*mode; 
  struct parse_mode_link_type	*next_parse_mode_link; 	
}; 



struct parse_variable_link_type { 
  struct parse_variable_type		*var; 
  struct parse_variable_link_type	*next_parse_variable_link; 
}; 

struct parse_local_type { 
  int					count; 
  struct parse_variable_link_type	*local_list; 
}; 



struct parse_sync_type {
  char				*sync_name;
  struct parse_variable_type	*sync_var;
  struct parse_sync_type	*next_parse_sync;
}; 


struct parse_assignment_type { 
  int				*simple_coeff, *simple_offset; 
  struct ps_exp_type		*lhs, *rhs_exp; 
  int				term_count;
  struct parse_term_type	*term;
  struct ps_exp_type		*offset;
};


struct parse_guard_type { 
  struct ps_exp_type		*cond; 
};


struct parse_erase_type { 
  struct ps_exp_type		*var; 
};


struct parse_cplug_statement_type { 
  int				cmod_index, cproc_index; 
  struct ps_exp_type		*lhs;
};


struct parse_call_statement_type { 
  int	call_mode_index, ret_mode_index; 
  char	*call_mode_name, *ret_mode_name; 
};


struct parse_statement_link_type { 
  struct parse_statement_type		*statement; 
  struct parse_statement_link_type	*next_parse_statement_link; 	
}; 


struct parse_seq_statement_type { 
  int					statement_count; 
  struct parse_statement_link_type	*statement_list; 	
}; 


struct parse_if_statement_type { 
  struct parse_statement_type	*if_statement, *else_statement; 
  struct ps_exp_type		*cond; 	
}; 


struct parse_while_statement_type { 
  struct parse_statement_type 	*statement; 	
  struct ps_exp_type		*cond; 
}; 

union	parse_statement_union	{
  struct parse_assignment_type		act;
  struct parse_guard_type		guard; 
  struct parse_erase_type		erase; 
  struct parse_call_statement_type	call;
  struct parse_seq_statement_type	seq; 
  struct parse_if_statement_type	branch; 
  struct parse_while_statement_type	loop; 
  struct parse_cplug_statement_type	cplug; 
}; 


struct parse_statement_type { 
  int 				op, type, st_status, lineno; 
  struct parse_statement_type	*parent; 
  union parse_statement_union	u;
}; 




struct parse_xtion_sync_type { 
  int				status, place_index, 
				type; /* +1 for ? and -1 for ! */
  struct parse_variable_type	*sync_var, *qsync_var, *place_holder_var; 
  struct ps_exp_type		*exp_multiplicity, 
				*exp_quantification;
                                /* Those with peer quantifications */ 
  struct parse_xtion_sync_type	*next_parse_xtion_sync; 
}; 

#define coordinate_x	index1
#define	coordinate_y	index2 


struct parse_stream_operation_type { 
  struct parse_variable_type		*stream; 
  struct ps_exp_type			*var, *value_exp; 
  int					operation; 
  struct parse_stream_operation_type	*next_parse_stream_operation; 
} ; 


struct parse_xtion_type {
  char					*src_lines; 
  int					index, status, lineno, 
					src_mode_index, dst_mode_index, 
					sync_count, stream_operation_count, 
					over_bound, bound_left_open, 
					intermediate_point_count; 
  struct index_pair_link_type		*intermediate_point_list; 
  struct parse_stream_operation_type	*stream_operation_list; 
  struct parse_xtion_sync_type		*sync_list; 
  struct parse_statement_type		*statement; 
  struct ps_exp_type			*trigger_exp, *orig_trigger_exp; 
  struct parse_mode_type		*src_mode; 
  struct parse_xtion_type 		*next_parse_xtion;
};



#ifndef _REDLIB_PS_EXP_STRUCTURES 
#define _REDLIB_PS_EXP_STRUCTURES 

/*********************************************************************
*
*       Data structures for parsing specification formulas 
*/


#define PROC_QUANTIFIED_SYNC	-4
#define PROC_GLOBAL_EVENT	-3
#define	PROC_LOCAL		-2
#define	PROC_QFD		-1
#define PROC_GLOBAL		0

struct parse_atom_type {
  int				var_index,
//				indirect_count, *indirect_vi,  
				status;
  struct ps_exp_type		// **indirect_exp, 
				*exp_base_proc_index; /* -2: P, -1: qfd, 0: global, [1,oo): local */
  struct parse_variable_type	*var; 		/* only used when arith_op == TYPE_DISCRETE,
						 or TYPE_CLOCK, TYPE_POINTER;
				      		*/
  char				*var_name;	/* only used when 
  						 arith_op == TYPE_DISCRETE,
						 or TYPE_CLOCK, TYPE_POINTER;
						 Note, qname is now moved to 
						 exp_base_proc_index on 2004/1/2.
				      		*/
};

struct parse_mode_index_type { 
  int				value; 
  struct parse_mode_type	*parse_mode; 
  char				*mode_name; 	
}; 

struct parse_qsync_holder_type { 
  int				place_index; 
  char				*qsync_var_name; 
  struct parse_variable_type	*qsync_var, *place_holder_var; 	
}; 



#define	INTERVAL_LEFT_UNBOUNDED		8
#define	INTERVAL_LEFT_OPEN		4
#define	INTERVAL_LEFT_CLOSED		0
#define	INTERVAL_RIGHT_UNBOUNDED	2
#define	INTERVAL_RIGHT_OPEN		1
#define	INTERVAL_RIGHT_CLOSED		0


struct parse_interval_type {
  int			status; 
  struct ps_exp_type	*lbound_exp, /* NULL means negative infinity. */ 
			*rbound_exp; /* NULL means positive infinity. */ 
};

/* The following constants are used for the specific types of inequalities. 
 */ 
#define	MASK_EXP_TYPE			(0xFF) 
#define FLAG_EXP_STATIC			(0x01)
#define FLAG_EXP_DISCRETE_CONSTANT	(0x02)	/* x ~ c */
#define	FLAG_EXP_DISCRETE_LINEAR	(0x03)	/* a1 x1 + ... + an xn ~ c */
#define	FLAG_EXP_DISCRETE_POLYNOMIAL	(0x04)	/* polynomial ~ c */
#define	FLAG_EXP_CLOCK_CONSTANT		(0x05)	/* x ~ c */
#define	FLAG_EXP_CLOCK_DIFFERENCE	(0x06)	/* x - y ~ c */
#define FLAG_EXP_CLOCK_MIXED		(0x07)	/* a1 x1 + ... + an xn ~ c */
#define FLAG_EXP_CLOCK_DIFFERENCE_MIXED	(0x08)	/* a1 x1 + ... + an xn ~ c */
#define FLAG_EXP_DENSE_CONSTANT		(0x09)	/* x ~ c */
#define FLAG_EXP_DENSE_LINEAR		(0x0A)	/* a1 x1 + ... + an xn ~ c */
#define FLAG_EXP_DENSE_MIXED		(0x0B)	/* a1 x1 + ... + an xn ~ c */
#define FLAG_EXP_DENSE_POLYNOMIAL	(0x0C)

struct parse_arith_type {
  int			status; 
  struct ps_exp_type	*lhs_exp, *rhs_exp;
};


struct parse_term_type {
  struct ps_exp_type	*coeff, *operand;
};

struct parse_ineq_type {
  int				type, term_count;
  struct parse_term_type	*term;
  struct ps_exp_type		*offset;
};


struct parse_conditional_arith_type {
  int			type; 
  struct ps_exp_type	*cond, *if_exp, *else_exp;
};


struct ps_bunit_type {
  struct ps_exp_type 	*subexp;
  struct ps_bunit_type 	*bnext;
};


struct ps_bexp_type {
  int 			len;
  struct ps_bunit_type 	*blist;
};



struct ps_rexp_type {
  char				*clock_name;
  int				clock_index;
  struct parse_variable_type	*var;  
  struct ps_exp_type		*child;
};


struct ps_qexp_type {
  char			*quantifier_name;
  int			value;
  struct ps_exp_type	*child, *lb_exp, *ub_exp;
};


struct ps_project_type {
  int			variable_index;
  struct ps_exp_type	*child;
};
#define	vsim_type_offset	variable_index 
#define	clock_offset		variable_index 
#define var_type		variable_index 
#define var_proc		variable_index 



struct ps_fairness_link_type	{
  int				status; 
  struct ps_exp_type		*fairness;
  struct red_type		*red_fairness; 
  struct ps_fairness_link_type	*next_ps_fairness_link;
};



struct ps_mexp_type {
  int				time_lb, time_ub,
  				strong_fairness_count, weak_fairness_count;
  struct ps_exp_type		*path_child, *dest_child,  
				*time_restriction, *event_restriction; 
  struct red_type		*red_early_decision_maker, 
				*red_time_restriction, 
				*red_xi_restriction; 
  struct ps_fairness_link_type	*strong_fairness_list, *weak_fairness_list;
};



struct ps_eexp_type {
  struct ps_exp_type		*postcond_exp, 
				*precond_exp, *event_exp; 
  struct red_type		*red_early_decision_maker, 
				*red_sync_bulk_from_event_exp, 
				*red_game_sync_bulk_from_event_exp, 
				*red_postcond, *red_precond; 
};


struct red_predicate_type { 
  struct red_type	*red, *original_red; 
}; 

#define	MASK_INLINE_TYPE	(0xF)
#define	FLAG_INLINE_CONSTANT	1
#define FLAG_INLINE_DISCRETE 	2
#define FLAG_INLINE_BOOLEAN 	3 

struct ps_inline_declare_type { 
  char			*inline_exp_name; 
  int			status, formal_argument_count; 
  struct name_link_type	*formal_argument_list; 
  struct ps_exp_type	*declare_exp; 
}; 


struct ps_inline_call_type { 
  char			*inline_exp_name; // This is to be shared with 
                                          // the corresponding inline_declare. 
                                          // So don't release here. 
  struct ps_exp_type	*inline_declare, *instantiated_exp; 
  struct ps_bunit_type	*actual_argument_list; 
}; 



union	ps_union {
  int					value; 
  float					float_value; 
  char					*argument; 
  struct ps_exp_type			*exp; 
  struct parse_atom_type		atom;
  struct parse_mode_index_type		mode_index; 
  struct parse_qsync_holder_type	qsholder;  
  struct parse_arith_type		arith;
  struct parse_conditional_arith_type   arith_cond; 
  struct ps_bexp_type			bexp;

  struct ps_inline_declare_type		inline_declare; 
  struct ps_inline_call_type		inline_call; 
  
  struct parse_interval_type		interval; 
  struct parse_ineq_type		ineq;
  struct red_predicate_type		rpred;
  struct ps_rexp_type			reset;
  struct ps_qexp_type			qexp;
  struct ps_mexp_type			mexp;
  struct ps_eexp_type			eexp; 
  struct ps_project_type		project; 
};

/* The following constants are used for status. */ 

/* The following two flags overlap with the FLAG_STATEMENT_ELSE and FLAG_STATEMENT_COMPOUND 
 * in redbasics.h.  
 * They are only used in simple statements and inequalities while 
 * FLAG_STATEMENT_ELSE and FLAG_STATEMENT_COMPOUND are only used for compound statements.  
 */
 
/* var_status 
 * The same as the status bits of VAR. 
 */ 

/* exp_status */ 
#define	FLAG_CONSTANT			(0x00000001) // This means 
						     // the expression 
/* This flag value is used only in type constant. */ 
#define MASK_MODE_INDEX			(0x00000002)
#define	FLAG_LOCAL_IDENTIFIER		(0x00000004)

#define	FLAG_HYBRID			(0x00000008)


// #define FLAG_VAR_FILLED_IN		(0x00000001)

#define FLAG_ONE_POS_CLOCK		(0x00000002) // These two flags are used to check if  
#define	FLAG_ONE_NEG_CLOCK		(0x00000004) // more clocks are not in difference form.
                                                     // This flag is only used in redgram.y  
                                                     // for assignment and 
                                                     // inequality analysis. 
                                                     // So we let it share 
                                                     // with flags fairness 
                                                     // occurrence and strengths. 



						     // evaluates to a constant. 
#define	FLAG_VAR_BOUNDS_DELAYED_EVAL	(0x00000010) //** used in VAR[]

#define FLAG_PATH_INSIDE		(0x00000040)
#define	FLAG_RESET_INSIDE		(0x00000080) 
#define FLAG_NEGATION_INSIDE		(0x00000100) 
#define	FLAG_DISJUNCTION_INSIDE		(0x00000200)
#define	FLAG_CONJUNCTION_INSIDE		(0x00000400) // we use this to detect time-convexity instead.
#define	FLAG_EXP_MODAL_INSIDE		(0x00000800)
#define FLAG_TCTCTL_SUBFORM		(0x00001000) 
#define FLAG_NOT_TCTCTL_SUBFORM		(0x00000000) 

#define FLAG_GFP_EARLY_DECISION		(0x00002000) 

#define	FLAG_TAIL_CONVEXITY_EVALUATION	(0x00004000) // used for modal operators
// The following constant is now replaced by FLAG_TCTCTL_SUBFORM
// #define	FLAG_PATH_CONVEXITY_EVALUATION	(0x20000000) // used for modal operators

#define	FLAG_INDIRECTION		(0x00008000)

#define FLAG_EVENT_XMIT			(0x00010000) 
#define FLAG_EVENT_RECV			(0x00020000) 

#define MASK_FAIRNESS_STRENGTH		(0x00100000) // used for modal expresions 
#define FLAG_FAIRNESS_STRONG		(0x00100000) // used for modal expresions
#define FLAG_FAIRNESS_WEAK		(0x00000000) // used for modal expresions


/*********************************
 * The following constants are used for exp_status. 
 */ 

struct	ps_exp_type	{
  int 			type, count, 
			var_status, 
			exp_status, 
			lineno; 
  union ps_union	u; 
  struct red_type	*diagram_label; 
  struct a23tree_type	*a23tree; 
};


#endif 



struct ps_quantify_link_type { 
  int				var_index, 
  				op, // FORALL, EXISTS
  				op_restriction; // AND, OR, IMPLIES, NOT 
  struct red_type		*red_restriction; 
  struct ps_exp_type		*exp_restriction; 
  struct ps_quantify_link_type	*next_ps_quantify_link; 
}; 


struct ps_memory_link_type { 
  int  
    type, 
    size; 
  struct ps_memory_link_type
    *next_ps_memory_link; 	
}; 

