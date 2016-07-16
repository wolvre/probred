#define	HYBRID_POS_INFINITY	(1024*1024*1024+1)
#define	HYBRID_POS_BOUND	(1024*1024*512)
#define	HYBRID_NEG_INFINITY	(-1024*1024*1024-1)
#define	HYBRID_NEG_BOUND	(-1024*1024*512)

#define	TIME_FORWARD	-1
#define	TIME_BACKWARD	1



struct hrd_term_link_type {
  int				var_index, coeff_numerator, coeff_denominator;
  struct hrd_term_link_type	*next_hrd_term_link;
};




struct hrd_term_type {
  int			var_index, coeff;
};


/* The status field of hrd_exp_type is divided to the following three parts
   determined by the three variable values determined according to the variable_count.

   The least significant part, covered by variable MASK_HYBRID_LENGTH,
   is log2 (variable_count+1) bits long and records the length of expression.
   The medium significant part, covered by variable MASK_HYBRID_LIFTED_VI,
   is also log2 (variable_count+1) bits long and records the hybrid_inequality variable index.
   It is also lifted by multiple MASK_HYBRID_VI_BASE;
   The most significant part is bit MASK_DELTA_GENERATED.

int			MASK_HYBRID_LENGTH,
			MASK_HYBRID_LIFTED_VI,
			MASK_HYBRID_VI_BASE,
			MASK_DELTA_GENERATED;
*/
struct hrd_exp_type {
  int			count, 
			status;
  char			*name;
  struct hrd_term_type	*hrd_term;
};


struct hrd_child_type {
  int			ub_numerator, ub_denominator;
  struct red_type	*child;
};


struct hrd_type {
  int			child_count; 
  struct hrd_exp_type	*hrd_exp;
  struct hrd_child_type	*arc;
};



struct hdd_child_type {
  int			lb_numerator, lb_denominator, 
			ub_numerator, ub_denominator;
  struct red_type	*child;
};

struct hdd_type {
  int			child_count; 
  struct hrd_exp_type	*hrd_exp;
  struct hdd_child_type	*arc;
};



