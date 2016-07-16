#define	POS_INFINITY	(1024*1024*1024)
#define NEG_INFINITY	(-1024*1024*1024)


/********************************************************
 *  red variable & expression types 
 */
 

#define	FLAG_NO_USE		-1
#define DONT_CARE		-1
#define	TYPE_FALSE		INDEX_FALSE 
#define	TYPE_TRUE		INDEX_TRUE 
#define NO_RESTRICTION		INDEX_TRUE 

#define TYPE_NULL		2 /* Also for global scope */ 
#define	TYPE_LOCAL_IDENTIFIER	3
#define	TYPE_PEER_IDENTIFIER	4
#define	TYPE_TRASH		5
#define	TYPE_CONSTANT		6
#define	TYPE_FLOAT_CONSTANT	7
#define TYPE_QFD		8
#define	TYPE_INTERVAL		9
#define RED			10

/* Variable declaration type */
#define TYPE_SYNCHRONIZER	11
#define	TYPE_DISCRETE		12
#define TYPE_FLOAT		13
#define	TYPE_DOUBLE		14
#define TYPE_POINTER		15 // This is now not open to the users. 
#define	TYPE_BDD		16 // We assume that all BDD variables are global now. 
				   // BDD variables are only used for template sharing experiments. 
#define	TYPE_CLOCK		17
#define TYPE_DENSE		18
#define TYPE_QSYNC_HOLDER	19  /* This is the type for place holder. 
				     * A sync process id holder is of type TYPE_POINTER 
				     * with FLAG_QUANTIFIED_SYNC.  
				     */
#define	TYPE_PARAMETER		20
#define TYPE_STREAM		21 
#define	TYPE_MEMORY		22 

#define TYPE_CRD		30 
#define TYPE_CDD 		31 
#define	TYPE_HRD		32
#define	TYPE_HDD		33
#define	TYPE_RRD		34
#define TYPE_RDD		35
#define TYPE_LAZY_EXP		36 

#define TYPE_XTION_INSTANCE	41
#define TYPE_ACTION_INSTANCE	42
#define TYPE_MONITOR 		43
#define TYPE_INDIRECT_PI	44
#define TYPE_PATH_ENDPOINT	45
#define	TYPE_VALUE		46
#define	TYPE_OP			47

#define	LESS			51
#define	LEQ			52
#define	EQ			53
#define	NEQ			54
#define	GEQ			55
#define	GREATER			56


#define	ARITH_LESS		61
#define	ARITH_LEQ		62
#define	ARITH_EQ		63
#define	ARITH_NEQ		64
#define	ARITH_GEQ		65
#define	ARITH_GREATER		66


#define	ARITH_ADD		71
#define	ARITH_MINUS		72
#define	ARITH_MULTIPLY		73
#define	ARITH_DIVIDE		74
#define	ARITH_MODULO		75
#define	ARITH_MIN		76
#define	ARITH_MAX		77

#define ARITH_CONDITIONAL	78 
#define ARITH_SUM		79 

#define	BIT_NOT			81
#define	BIT_OR 			82
#define	BIT_AND			83 
#define	BIT_SHIFT_RIGHT		84
#define	BIT_SHIFT_LEFT		85

#define	AND		91
#define	OR		92
#define NOT		93
#define IMPLY		94
#define	NOR		95
#define	NAND		96
#define	XOR		97
#define	BUF		98
#define	REG		99

#define	INTERSECT			101
/* 
#define	RESTRICT			102
*/
#define	SUBTRACT			103
#define	EXCLUDE				104
#define	EXTRACT				105
/* 
#define	UNION				106
*/
#define	UNION_WITH_REDUCTION		107
#define	EXCLUDE_WITH_REDUCTION		108


#define	FORALL			111
#define	FORALL_ALWAYS		112
#define	FORALL_EVENTUALLY	113
#define	FORALL_UNTIL		114
#define FORALL_CHANGE		115
#define	FORALL_EVENT		116
#define FORALL_OFTEN		118
#define FORALL_ALMOST		119

#define EXISTS			121
#define EXISTS_ALWAYS		122
#define EXISTS_EVENTUALLY	123
#define EXISTS_UNTIL		124
#define EXISTS_CHANGE		125
#define	EXISTS_EVENT		126
#define EXISTS_OFTEN		128
#define EXISTS_ALMOST		129

#define	RESET			131

#define TYPE_MODE_INDEX		132
#define TYPE_PROCESS_COUNT	133
#define TYPE_MODE_COUNT		134
#define TYPE_XTION_COUNT	135

#define TYPE_INLINE_BOOLEAN_DECLARE	140 
#define TYPE_INLINE_DISCRETE_DECLARE	141 
#define TYPE_MACRO_CONSTANT		142
#define	TYPE_INLINE_CALL		143
#define	TYPE_INLINE_ARGUMENT		144

#define	LINEAR_EVENT		150 // These two are purely used for fairness 
#define	CONDITIONAL_EVENT       151 // assumptions with modal formulas.  
#define	TYPE_GAME_SIM		152

#define TYPE_MULTIPLE_FAIRNESS	153 

#define	PROJECT			160 
#define	PROJECT_TIME		161 
#define	PROJECT_QSYNC		162 
#define	PROJECT_TYPE		163 
#define	PROJECT_PROC		164 
#define	PROJECT_PEER		165 
#define	PROJECT_LOCAL		166 
#define	PROJECT_VAR_SIM		167
#define	PROJECT_CLOCK_SIM	168
#define	PROJECT_MCHUNK		169

#define	PROJECT_CLOCK_LOWER_EXTEND	170 
#define	PROJECT_CLOCK_UPPER_EXTEND	171 

#define TYPE_REFERENCE		200
#define TYPE_DEREFERENCE	201 

#define	ALWAYS		1
#define	EVENTUALLY	2
#define	UNTIL		3
#define CHANGE		4
#define ON_EVENT	5
#define	WITH_EVENT	6
#define OFTEN		7
#define	ALMOST		8

#define LHS_PI		2
#define RHS_PI		3
#define HF_PSTART_VI	4
#define HF_PSTOP_VI	5
#define VI_OP		6
#define VI_VALUE	7
#define FLOAT_VALUE	8 
#define DOUBLE_VALUE	9
#define PROB_VALUE	10
#define PROB_WORK_VALUE	11


#define	TIA_INCOMING_ASSIGNMENT_INVARIANCE_MATCH	1
#define	TIA_OUTGOING_ENDPOINT_TRIGGERING_MATCH		2

struct mode_timed_inactive_type {
  int			status, lb_numerator, lb_denominator, ub_numerator, ub_denominator;
  struct red_type	*red_timed_inactive;
};


struct mode_rate_spec_type {
  struct red_type	*red_mode_spec;
  int			rate_lb_numerator, rate_lb_denominator,
			rate_ub_numerator, rate_ub_denominator;
};



/* mask bits used for VAR type defined in redparse.h 
#define FLAG_QUANTIFIED_SYNC		(0x00000001) //** defined for GSTATUS in redbasics.h
*/ 
#define MASK_VARIABLE_FLAGS		(0x007FFFFF)
#define	FLAG_NONE 			0
#define FLAG_QUANTIFIED_SYNC		(0x00000001)  
#define FLAG_SYNCHRONIZER		(0x00000002) 
#define	FLAG_BDD			(0x00000004)
#define	FLAG_DISCRETE			(0x00000008)
#define	FLAG_POINTER			(0x00000010)
#define	FLAG_CLOCK 			(0x00000020)
#define FLAG_DENSE			(0x00000040)
#define	FLAG_FLOAT			(0x00000080)
#define	FLAG_DOUBLE			(0x00000100)
#define FLAG_QFD			(0x00000200)


#define FLAG_MODE			(0x00000400) //** used in VAR[]
#define FLAG_VAR_STACK			(0x00000800) //** used in VAR[]
#define	FLAG_VAR_STATIC			(0x00001000)
#define	FLAG_VAR_SYS_GEN		(0x00004000) 
#define FLAG_RANGE_ALL_VI		(0x00008000) //coincides with FLAG_ONE_POS_CLOCK

#define MASK_STREAM_TYPE		(0x00030000) 
#define FLAG_STREAM_ORDERED		(0x00010000) 
#define FLAG_STREAM_UNORDERED		(0x00020000) 

#define FLAG_WORKING_IN_LAZY_EXP	(0x00040000) 

#define	FLAG_LOCAL_VARIABLE		(0x00080000)

#define FLAG_ADDRESS_AFFECTING		(0x00100000) 

#define FLAG_SPEC_REFERENCED		(0x00200000)
#define FLAG_CROSS_REFERENCED		(0x01000000)
#define	FLAG_MONITOR			(0x02000000)
#define FLAG_MAYBE_BOUNDED		(0x04000000)
#define	FLAG_BOUND_DECLARED		(0x08000000)
#define	FLAG_VAR_PRIMED			(0x10000000)
#define	FLAG_SYNC_PLACE			(0x20000000)

#define FLAG_VAR_AUX_BOTTOM_ORDERING	(0x40000000) 



/* We should merge the following into var table and parse var list. 
 */ 

#define	FLAG_EXP_STATE_INSIDE		(  FLAG_DISCRETE \
					 | FLAG_POINTER	\
					 | FLAG_CLOCK \
					 | FLAG_DENSE \
					 | FLAG_FLOAT \
					 | FLAG_DOUBLE \
					 | FLAG_BDD \
					 )


#define	INDEX_START_USER_VAR		8 

struct var_union_sync_type { 
  int	LB, UB, SYNC_INDEX, DIFF, FLAG_EVENT_OCC; 
}; 

struct var_union_discrete_type { 
  int	
    LB, UB, 
    NEXT_DISCRETE_VI, 
    AUX_VI_BOTTOM_ORDERING, 
#define ORIG_VI_BOTTOM_ORDERING	AUX_VI_BOTTOM_ORDERING 
    CORRESPONDING_STREAM_VI, 
#define CORRESPONDING_PI 	CORRESPONDING_STREAM_VI 
    WORKING_QFD_SYNC_VALUE; 
}; 

struct var_union_bdd_type { 
  int	LB, UB; 
}; 

struct var_union_crd_type { 
  int	LB, UB, CORRESPONDING_CDD_VI, CONVERSE_CRD_VI, CLOCK1, CLOCK2; 
}; 

struct var_union_cdd_type { 
  int	LB, UB, CORRESPONDING_CRD_VI, CONVERSE_CDD_VI, CLOCK1, CLOCK2; 
}; 

struct var_union_hrd_type { 
  int	LB, UB, CORRESPONDING_HDD_VI; 
}; 

struct var_union_hdd_type { 
  int	LB, UB, CORRESPONDING_HRD_VI; 
}; 

struct var_union_clock_type { 
  int	LB, UB, CLOCK_INDEX, 
	MODE_RATE_SPEC_COUNT;
  struct mode_rate_spec_type
    *MODE_RATE_SPEC; /* when this is an 
			  * occ variable 
			  * for event fairness 
			  * evaluation, 
			  * we use this to 
			  * coercefully 
			  * point to the 
			  * event 
			  * ps_exp_type 
			  * expression set by 
			  * variable_fillin(). 
			  */
  struct hrd_exp_type
    *HE_LB, *HE_UB; // for a dense variable, this records the hybrid 
  			// expressions (inequality) for upper-bound and 
  			// lower-bound respectively. 
}; 

struct var_union_dense_type { 
  int
    MODE_RATE_SPEC_COUNT; 
  struct mode_rate_spec_type
    *MODE_RATE_SPEC; /* when this is an 
			  * occ variable 
			  * for event fairness 
			  * evaluation, 
			  * we use this to 
			  * coercefully 
			  * point to the 
			  * event 
			  * ps_exp_type 
			  * expression set by 
			  * variable_fillin(). 
			  */ 
  struct hrd_exp_type
    *HE_LB, *HE_UB; // for a dense variable, this records the hybrid 
  			// expressions (inequality) for upper-bound and 
  			// lower-bound respectively. 
}; 

struct var_union_float_type { 
  float LB, UB; 
  int
    AUX_VI_BOTTOM_ORDERING;  
}; 

struct var_union_double_type { 
  double	LB, UB; 
  int	
    AUX_VI_BOTTOM_ORDERING;  
}; 

struct var_union_stream_type { 
  int	HEAD_POS_VI, 
#define FLAG_STREAM_NOT_OPENED	-2
	DIRECTION_VI, 
#define MASK_STREAM_DIRECTION		(0x00100000) 
#define	FLAG_STREAM_INPUT		(0x00100000) 
#define	FLAG_STREAM_OUTPUT		(0x00000000) 

	SIZE_DATA, SIZE_BUFFER, *BUFFER; 
  FILE	*FILE_STREAM; 	
}; 

struct var_union_qsholder_type { 
  int	PI; 
}; 

union	variable_union_type {
  struct var_union_sync_type		SYNC;  
  struct var_union_discrete_type	DISC; 
  struct var_union_bdd_type		BDD; 
  struct var_union_crd_type		CRD; 
  struct var_union_cdd_type		CDD; 
  struct var_union_hrd_type		HRD; 
  struct var_union_hdd_type		HDD; 
  struct var_union_clock_type		CLOCK; 
  struct var_union_dense_type		DENSE; 
  struct var_union_float_type		FLT; 
  struct var_union_double_type		DBLE; 
  struct var_union_stream_type		STRM; 
  struct var_union_qsholder_type	QSHLDR; 
};

struct variable_type {
  int	
  	TYPE, PROC_INDEX, 
	OFFSET, STATUS, 

	PRIMED_VI;  
#define UMPRIMED_VI 	PRIMED_VI 

  union variable_union_type	U; 
  char
	*NAME;
  struct red_type
	*RED_ACTIVE, *RED_INACTIVE,
	*RED_TIMED_ACTIVE, 
	*RED_TIMED_INACTIVE;
  struct mode_timed_inactive_type
        *MODE_TIMED_INACTIVE;
};


struct bdd_type { 
  struct red_type	 *zero_child, *one_child; 	
}; 

struct lazy_exp_type { 
  struct ps_exp_type	*exp; 
  struct red_type	*false_child, *true_child; 	
}; 

struct ddd_child_type {
  int			lower_bound, upper_bound;
			/* notation for [lower_bound, upper_bound+1)
			 * These record the range of integer part
			 * of the clock reading.
			 * lower_bound <= upper_bound
			 */
  struct red_type	*child;
};


struct ddd_type { 
  int			child_count; 
  struct ddd_child_type	*arc; 	
}; 

struct fdd_child_type {
  float			lower_bound, upper_bound;
			/* notation for [lower_bound, upper_bound+1)
			 * These record the range of integer part
			 * of the clock reading.
			 * lower_bound <= upper_bound
			 */
  struct red_type	*child;
};


struct fdd_type { 
  int			child_count; 
  struct fdd_child_type	*arc; 	
}; 

struct dfdd_child_type {
  double		lower_bound, upper_bound;
			/* notation for [lower_bound, upper_bound+1)
			 * These record the range of integer part
			 * of the clock reading.
			 * lower_bound <= upper_bound
			 */
  struct red_type	*child;
};


struct dfdd_type { 
  int				child_count; 
  struct dfdd_child_type	*arc; 	
}; 

/* specification of ichild_lists
 * for any ichild node ic in an ichild_list,

	if (ic->next_ichild != NULL) then
	  ic->upper_bound + 1 == ic->next_ichild->lower_bound
	  must be true
*/



struct crd_child_type {
  int			upper_bound;
  struct red_type	*child;
};

struct crd_type { 
  int			child_count; 
  struct crd_child_type	*arc; 	
}; 



#include "hybrid.h" 

union	child_union_type {
  struct bdd_type	bdd;  
  struct ddd_type	ddd; 
  struct fdd_type	fdd; 
  struct dfdd_type	dfdd; 
  struct crd_type	crd;
  struct hrd_type	hrd;
  struct hdd_type	hdd; 
  struct lazy_exp_type	lazy; 
};




#define	SIZEOF_RED_BASIC	(1+sizeof(int)) 
#define SIZEOF_RED_BDD		(SIZEOF_RED_BASIC + sizeof(struct bdd_type)) 
#define SIZEOF_RED_BDD_CHILD	(sizeof(struct bdd_child_type)) 
#define SIZEOF_RED_DDD		(SIZEOF_RED_BASIC + sizeof(struct ddd_type)) 
#define SIZEOF_RED_DDD_CHILD	(sizeof(struct ddd_child_type)) 
#define	SIZEOF_RED_CRD		(SIZEOF_RED_BASIC + sizeof(struct crd_type))
#define	SIZEOF_RED_CRD_CHILD	(sizeof(struct crd_child_type))
#define	SIZEOF_RED_CDD		(SIZEOF_RED_BASIC + sizeof(struct ddd_type))
#define	SIZEOF_RED_CDD_CHILD	(sizeof(struct ddd_child_type))
#define	SIZEOF_RED_HRD		(SIZEOF_RED_BASIC + sizeof(struct hrd_type)) 
#define	SIZEOF_RED_HRD_CHILD	(sizeof(struct hrd_child_type)) 
#define SIZEOF_RED_HDD		(SIZEOF_RED_BASIC + sizeof(struct hdd_type)) 
#define SIZEOF_RED_HDD_CHILD	(sizeof(struct hdd_child_type)) 

#define MASK_GC				(0x1F) 
#define FLAG_GC_STABLE			(0x1)
#define FLAG_GC_SYSTEM_STACK		(0x2)
#define FLAG_GC_USER_STACK		(0x4)
#define FLAG_GC_WHILE_GFP		(0x8)
#define FLAG_GC_TEMP			(0x10)

#define FLAG_RED_LAZY			(0x20)
#define FLAG_GC_PRINT			(0x00000040)
#define FLAG_GC_WORK			(0x00000080)


#define FLAG_GC_USER_STATIC1		(0x00000100)
#define FLAG_GC_USER_STATIC2		(0x00000200)

#define MASK0_REFERENCED		(0x00000400)
#define MASK0_MULTIPLE			(0x00000800)

#define MASK1_REFERENCED		(0x00001000)
#define MASK1_MULTIPLE			(0x00002000)

#define MASK2_REFERENCED		(0x00004000)
#define MASK2_MULTIPLE			(0x00008000)

#define MASK3_REFERENCED		(0x00010000)
#define MASK3_MULTIPLE			(0x00020000)

#define MASK4_REFERENCED		(0x00040000)
#define MASK4_MULTIPLE			(0x00080000)

#define MASK5_REFERENCED		(0x00100000)
#define MASK5_MULTIPLE			(0x00200000)

#define MASK6_REFERENCED		(0x00400000)
#define MASK6_MULTIPLE			(0x00800000)

#define MASK7_REFERENCED		(0x01000000)
#define MASK7_MULTIPLE			(0x02000000)

#define MASK8_REFERENCED		(0x04000000)
#define MASK8_MULTIPLE			(0x08000000)

#define MASK9_REFERENCED		(0x10000000)
#define MASK9_MULTIPLE			(0x20000000)

#define MASK10_REFERENCED		(0x40000000)
#define MASK10_MULTIPLE			(0x80000000)

#define MASK_RED_ALL_REFERENCED		(  MASK0_REFERENCED\
					 | MASK1_REFERENCED\
					 | MASK2_REFERENCED\
					 | MASK3_REFERENCED\
					 | MASK4_REFERENCED\
					 | MASK5_REFERENCED\
					 | MASK6_REFERENCED\
					 | MASK7_REFERENCED\
					 | MASK8_REFERENCED\
					 | MASK9_REFERENCED\
					 | MASK10_REFERENCED\
					 ) 
/* 
#define FLAG_GC_PRINT			(0x40)
#define FLAG_GC_WORK0			(0x0100) 
#define FLAG_GC_WORK1			(0x0200) 
#define FLAG_GC_WORK2			(0x0400) 
#define FLAG_GC_WORK3			(0x0800) 
#define FLAG_GC_WORK4			(0x1000) 
#define FLAG_GC_WORK5			(0x2000) 
#define FLAG_GC_WORK6			(0x4000) 
#define FLAG_GC_WORK7			(0x8000) 
*/

struct red_link_type {
  struct red_type	*result;
  struct red_link_type	*next_red_link;
};


struct red_type	{
  int                    status; 
  struct red_link_type    *result_stack;
  int                     var_index; /* 0..n-1: variables */
  union child_union_type  u;
};




#define	SIZE_SILENT		0
#define SIZE_REPORT		1 

#define	VOP_NOTHING		0
#define	VOP_ELIMINATE		1
#define	VOP_SET_INTERVAL	2
#define	VOP_INC			3
#define	VOP_INC_MOD		4


struct vop_type {
  int	op, lower_bound, upper_bound;
};

struct child_stack_frame_disc_type { 
  int	lb, ub; 	
}; 

struct child_stack_frame_float_type { 
  float 	lb, ub; 	
}; 

struct child_stack_frame_double_type { 
  double	lb, ub; 	
}; 


struct child_stack_frame_crd_type { 
  int	ub; 	
}; 


struct child_stack_frame_hrd_type { 
  int	ub, ub_den; 	
}; 


struct child_stack_frame_hdd_type { 
  int	lb, ub, lb_den, ub_den; 	
}; 


union child_stack_frame_union_type { 
  struct child_stack_frame_disc_type	disc; 
  struct child_stack_frame_float_type	flt; 
  struct child_stack_frame_double_type	dble; 
  struct child_stack_frame_crd_type	crd; 
  struct child_stack_frame_hrd_type	hrd; 
  struct child_stack_frame_hdd_type	hdd; 
}; 

struct child_stack_frame_type { 
  struct red_type			*d; 
  int					level; 	
  union child_stack_frame_union_type	u; 
}; 

extern void	expand_child_stack(), expand_level_child_stack(); 

#define	child_stack_level_push() { \
  TOP_LEVEL_CHILD_STACK++; \
  if (TOP_LEVEL_CHILD_STACK >= HEIGHT_LEVEL_CHILD_STACK) \
    expand_level_child_stack(); \
  LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] = 0; \
}
//  count_top_level_child_stack++; \
//  fprintf(RED_OUT, "(%1d)TOP_LEVEL_CHILD_STACK>>%1d\n", \
//    count_top_level_child_stack, TOP_LEVEL_CHILD_STACK); \
//  for (; count_top_level_child_stack == -1; ); \
//}
  /* child_stack_level_push() */  


#define	child_stack_level_pop() { \
  TOP_LEVEL_CHILD_STACK--; \
}
//  count_top_level_child_stack++; \
//  fprintf(RED_OUT, "(%1d)TOP_LEVEL_CHILD_STACK<<%1d\n", \
//    count_top_level_child_stack, TOP_LEVEL_CHILD_STACK); \
//}
  /* child_stack_level_pop() */  



// This is the empty push since no contents of the frame is given. 
#define child_stack_epush() { \
  TOP_CHILD_STACK++; \
  if (TOP_CHILD_STACK >= HEIGHT_CHILD_STACK) \
    expand_child_stack(); \
  LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++; \
}
//  count_top_child_stack++; \
//  fprintf(RED_OUT, "    (%1d)TOP_CHILD_STACK[%1d]>>%1d\n", \
//    count_top_child_stack, TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK); \
//  for (; count_top_child_stack == -1; ); \
//} 
  /* child_stack_epush() */ 
  
#define child_stack_pop() { \
  if (TOP_CHILD_STACK < 0) { \
    fprintf(RED_OUT, "ERROR: child stack underflow.\n"); \
    bk(0); \
  } \
  TOP_CHILD_STACK--; \
  LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]--; \
}
//  count_top_child_stack++; \
//  fprintf(RED_OUT, "    (%1d)TOP_CHILD_STACK[%1d]<<%1d\n", \
//    count_top_child_stack, TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK); \
//}
  /* child_stack_pop() */  

#define get_to_next_valid_child() { \
  for (; \
          TOP_CHILD_STACK >= 0 \
       && CHILD_STACK[TOP_CHILD_STACK].d == NORM_FALSE\
       && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK; \
       ) { \
    child_stack_pop(); \
  } \
}
  /* get_to_next_valid_child() */  




