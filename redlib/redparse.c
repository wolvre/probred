
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include <limits.h> 

#include "redbasics.h"  
#include "redbasics.e"  

#include "finclude.e" 

#include "redmaclex.e" 

#include "redgram.e"  

#include "vindex.e"  

#include "redbop.h"  
#include "redbop.e"  

#include "zone.h"  
#include "zone.e"  

#include "redparse.h"  
#include "exp.e" 

#include "tctctl.e" 

#include "access_analysis.e" 

#include "bisim.e" 
#include "redgame.e" 

#include "fxp.h"
#include "fxp.e"  

#include "action.e"  

#include "redsymmetry.e"

#include "inactive.e"

#include "hybrid.e"

#include "dmem.h" 
#include "dmem.e"

#include "hashman.h" 
#include "hashman.e" 

#include "treeman.h" 
#include "treeman.e" 


extern FILE			*redlibin; 

extern FILE			*cmlin;

char 				*model_file_name, 
				*spec_file_name, 
				*output_file_name;

/* extern FILE 	*fopen(); */

// variable that tells us what we have parsed. 
extern int	TYPE_PARSE_RESULT, GRAM_INPUT_TYPE; 

int		WINDOW_WIDTH, WINDOW_HEIGHT; 

struct parse_variable_type	*declare_local_discrete_list,
				*declare_local_pointer_list,
				*declare_local_float_list,
				*declare_local_double_list,
				*declare_local_bdd_list,
				*declare_local_clock_list,
				*declare_local_dense_list,
				*declare_local_qsholder_list,
				*declare_local_synchronizer_list,

				*declare_global_discrete_list,
				*declare_global_pointer_list,
				*declare_global_float_list,
				*declare_global_double_list,
				*declare_global_bdd_list,
				*declare_global_clock_list,
				*declare_global_dense_list,
				*declare_global_stream_list,
				*declare_global_synchronizer_list,
				*declare_global_rel_list,
				*declare_local_rel_list;


int				declare_global_rel_clock_count,
				declare_local_rel_clock_count,
				declare_spec_rel_clock_count,
				declare_global_rel_discrete_count,
				declare_local_rel_discrete_count,
				declare_spec_rel_discrete_count,
				declare_global_rel_count,
				declare_local_rel_count,
				declare_spec_rel_count,  
				sync_place_count;  
				
struct parse_variable_type	*declare_stack_discrete_list; 
int				count_stack_discrete; 

struct parse_variable_type	*declare_stack_float_list; 
int				count_stack_float; 

struct parse_variable_type	*declare_stack_double_list; 
int				count_stack_double; 

struct parse_variable_type	*sync_place_start_var, 
				*sync_place_stop_var;

struct parse_mode_type		*declare_mode_list;
int				declare_mode_count;

struct parse_assignment_type	*declare_clock_assign_pattern_list;
int				declare_clock_assign_pattern_count;

struct parse_xtion_type		*declare_xtion_list, *XTION_NULL;
int				declare_xtion_count;

int				MAX_TERM_COUNT, MEMORY_START_VI;

struct ps_exp_type		*PARSE_INITIAL_EXP, 
				*ORIG_PARSE_INITIAL_EXP, 
				*PARSE_SPEC;

int				max_party_count, MAX_GSYNC_COUNT;

char				parse_error[256];

int 				MAX_ACTION_COUNT = 0; 

int				PARSE_GLOBAL_SEQ_COUNT;
struct ps_exp_type		**PARSE_DEBUG_EXP;

int					process_name_index; 
struct indexed_structure_link_type	*process_list; 

int			declare_inline_exp_count = 0; 
struct ps_bunit_type	*declare_inline_exp_list; 
      
struct parse_variable_type 
  *var_prob, 
  *var_probw, 
  *var_mode, 
  *var__sp, 
  *var__retmode, 
//081225 CHANGE
  *var_zero, 
  *var_time, 
  *var_modal_clock, *var_zeno_clock, 
  *var_delta, *var_neg_delta, 
  *var_deltap, *var_neg_deltap, 
  *var_play_time, 
//130526 CHANGE 
  *var_prob_dense;


int	TYPE_PARSE_CHOICE; 
 
int	STATUS_FORMULA_CHOICE; 

struct ps_exp_type			*PARSER_INPUT_FORMULA; 
struct parse_redlib_sync_xtion_type 	*PARSER_INPUT_SYNC_XTION; 
struct ps_quantify_link_type		*PARSER_QUANTIFICATION_LIST; 

int	count_memory = 0; 

struct ps_memory_link_type 
  *memory_list = NULL; 

struct a23tree_type	*parse_tree;

struct ps_exp_type	*PEXP_EREACHABLE;

int 	count_ps_debug1 = 0, count_ps_debug2 = 0; 

// int	flag_red_initial = TYPE_FALSE; 

/*  The following variables are related to the interpretation of pi or (W_PI) in the 
 *  evaluation of parse formulas. 
 *  The rules are presented in redparse.h in 061106. 
 *  pi = GLOBAL, 
 *  pi in [1,#PS], a true local identifier. 
 *  pi in [-1,-#PS], a peer identifier to process pi.  
 *  pi = -1 - #PS, FLAG_ANY_PROCESS
 *  pi = -2 - #PS, INDEX_LOCAL_IDENTIFIER 
 *  pi = -3 - #PS, FLAG_ANY_VALUE
 *  pi = -4 - #PS, FLAG_ANY_VARIABLE 
 * 
 *  The values of FLAG_ANY_PROCESS, INDEX_LOCAL_IDENTIFIER, FLAG_ANY_VALUE, and FLAG_ANY_VARIABLE 
 *  are all set in redgram.y right after the number of processes is read in.  
 */
int 
  FLAG_ANY_PROCESS, /* = -1 - PROCESS_COUNT */ 
  INDEX_LOCAL_IDENTIFIER, /* = -2 - PROCESS_COUNT */ 
  FLAG_ANY_VALUE, /* = -3 - PROCESS_COUNT */ 
  FLAG_ANY_VARIABLE, /* = -4 - PROCESS_COUNT */
  FLAG_NO_VALUE  /* = -5 - PROCESS_COUNT */ ; 

struct red_type	*red_discrete_value(); 
 
#define	FLAG_GENERAL_PROCESS_IDENTIFIER	-1 // a constant to be used for print_parse_subformula

int	*testim; 

initm() { 
  int	i; 
  
  testim = (int *) malloc(10000*sizeof(int)); 
  for (i = 0; i < 10000; i++) 
    testim[i] = 0; 
} 
  /* initm() */ 
  
checkm() { 
  int	i; 
  
  for (i = 0; i < 10000; i++) 
    if (testim[i]) {
      fprintf(RED_OUT, "\n** a corrupted cell at address %x for testim[%1d]=%1d.\n", 
	(unsigned int) &(testim[i]), i, testim[i] 
      ); 
      return(1); 
    }
  return(0); 
} 
  /* checkm() */ 
  

int	exp_var_status_parse_variable(
  struct parse_variable_type	*pv
) { 
  int	vs; 
  
  vs = pv->status & (
    FLAG_QUANTIFIED_SYNC 
//  | FLAG_POINTER 
  | FLAG_LOCAL_VARIABLE 
  | FLAG_MODE
  | FLAG_VAR_STATIC 
  ); 
  switch (pv->type) { 
  case TYPE_SYNCHRONIZER: 
    return(vs | FLAG_SYNCHRONIZER); 
  case TYPE_BDD:
    return(vs | FLAG_BDD); 
  case TYPE_POINTER: 
    return(vs | FLAG_POINTER); 
  case TYPE_DISCRETE: 
    return(vs | FLAG_DISCRETE); 
  case TYPE_FLOAT: 
    return(vs | FLAG_FLOAT); 
  case TYPE_DOUBLE: 
    return(vs | FLAG_DOUBLE); 
  case TYPE_CLOCK:
    return(vs | FLAG_CLOCK); 
  case TYPE_DENSE:
    return(vs | FLAG_DENSE); 
  case TYPE_QSYNC_HOLDER:
    return(vs | FLAG_QUANTIFIED_SYNC); 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal status query for nonvariables.\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* exp_status_parse_variable() */ 


/*******************************************
*  the size of the array is in tc.
*  num[0], .. , num[tc-1] are the numerators
*  den[0], .. , den[tc-1] are the denominators
*  returns the value that to multiply to the all the coefficients that
*  makes all the denominators 1.
*/
void	rational_normalize(nptr, dptr) 
	int	*nptr, *dptr; 
{ 
  int	g; 
  
  g = gcd(*nptr, *dptr);
  *nptr = *nptr / g;
  *dptr = *dptr / g;	
}
  /* rational_normalize() */
  
  
  

void 	rec_get_rationals(psub, nptr, dptr)
  struct ps_exp_type 	*psub;
  int			*nptr /* pointer to numerator */, *dptr /* pointer to denominator */;
{
  int 	lnum, lden, rnum, rden;

  switch(psub->type){
  case TYPE_CONSTANT:
    *nptr = psub->u.value;
    *dptr = 1;
    return;
  case TYPE_MACRO_CONSTANT: 
    *nptr 
    = psub->u.inline_call.inline_declare
    ->u.inline_declare.declare_exp
    ->u.value; 
    *dptr = 1; 
    return; 

  case TYPE_LOCAL_IDENTIFIER:
    *nptr = W_PI;
    *dptr = 1;
    return;
  case TYPE_NULL:
  case TYPE_FALSE:
    *nptr = 0;
    *dptr = 1;
    return;
  case TYPE_TRUE:
    *nptr = 1;
    *dptr = 1;
    return;
  case TYPE_PROCESS_COUNT: 
    *nptr = PROCESS_COUNT; 
    *dptr = 1; 
    return; 
  case TYPE_MODE_INDEX: 
    *nptr = psub->u.mode_index.parse_mode->index; 
    *dptr = 1; 
    return; 
  case TYPE_QFD:
    *nptr = qfd_value(psub->u.atom.var_name);
    *dptr = 1;
    return;
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    *nptr = 0;
    *dptr = 1;
    return;
  case BIT_NOT: 
    lnum = rec_get_exp_value(psub->u.exp, 0, &lden); 
    *nptr = ~lnum; 
    *dptr =1; 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    lnum = rec_get_exp_value(psub->u.arith.lhs_exp, 0, &lden); 
    rnum = rec_get_exp_value(psub->u.arith.lhs_exp, 0, &rden); 
    *nptr = bit_op_value(psub->type, lnum, rnum); 
    *dptr =1; 
    return; 
  case ARITH_ADD:
    rec_get_rationals(psub->u.arith.lhs_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith.rhs_exp, &rnum, &rden);
    *nptr = lnum * rden + rnum *lden;
    *dptr = rden * lden;
    rational_normalize(nptr, dptr);
    return;
  case ARITH_MINUS:
    rec_get_rationals(psub->u.arith.lhs_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith.rhs_exp, &rnum, &rden);
    *nptr = lnum * rden - rnum *lden;
    *dptr = rden * lden;
    rational_normalize(nptr, dptr);
    return;
  case ARITH_MULTIPLY:
    rec_get_rationals(psub->u.arith.lhs_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith.rhs_exp, &rnum, &rden);
    *nptr = lnum * rnum;
    *dptr = lden * rden;
    rational_normalize(nptr, dptr);
    return;
  case ARITH_DIVIDE:
    rec_get_rationals(psub->u.arith.lhs_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith.rhs_exp, &rnum, &rden);

    if (rnum){
      *nptr = lnum * rden;
      *dptr = lden * rnum;
      rational_normalize(nptr, dptr);
      return;
    }
    else {
      fprintf(RED_OUT, "\nParser: Huh ? (parse 1) \n");
      bk(); 
    }
    break;
  case ARITH_MODULO:
    rec_get_rationals(psub->u.arith.lhs_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith.rhs_exp, &rnum, &rden);

    if (lden == 1 && rden == 1 && rnum){
      *nptr = lnum % rnum;
      *dptr = 1;
      rational_normalize(nptr, dptr);
      return;
    }
    else {
      fprintf(RED_OUT, "\nParser: Huh ? (parse 1) \n");
      bk(); 
    }
    break;
  case ARITH_CONDITIONAL: 
    rec_get_rationals(psub->u.arith_cond.if_exp, &lnum, &lden);
    rec_get_rationals(psub->u.arith_cond.else_exp, &rnum, &rden); 
    if (lnum == rnum && lden == rden) {
      *nptr = lnum; 
      *dptr = lden; 
      return; 	
    } 
    else {
      fprintf(RED_OUT, "\nERROR: We are not sure how to evaluate the \n"); 
      fprintf(RED_OUT, "       rationals from a conditional expresion.\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    break; 
  default:
    fprintf(RED_OUT, "\nParser: Huh ? (parse 1) \n");
    bk(); 
  }

}
/* rec_get_rationals() */


void	get_rationals(psub, pi, nptr, dptr)
	struct ps_exp_type	*psub;
	int			pi, *nptr, *dptr;
{
  W_PI = pi;
  rec_get_rationals(psub, nptr, dptr);
}
/* get_rationals() */



struct a23tree_type	*range_tree; 
int			VI_RED_RANGE = 0; 



struct vi_range_disc_type {
  int	lb, ub; 	
}; 


struct vi_range_float_type {
  float	lb, ub; 	
}; 


struct vi_range_double_type {
  double	lb, ub; 	
}; 


union vi_range_union { 
  struct vi_range_disc_type	disc; 
  struct vi_range_float_type	flt; 
  struct vi_range_double_type	dble; 
}; 


struct rec_vi_range_type { 
  struct a23tree_type	*parent; 
  struct red_type	*d; 
  int			flag, lb, ub; 
  union	vi_range_union	u; 
};  
  /* rec_vi_range_type */ 



struct rec_vi_range_type	*rec_vi_range_new(
  struct red_type	*d
) { 
  struct rec_vi_range_type	*rec; 
  
  rec = (struct rec_vi_range_type *) malloc(sizeof(struct rec_vi_range_type)); 	
  rec->d = d; 
  rec->flag = FLAG_ANY_VALUE; 
  switch (VAR[VI_RED_RANGE].TYPE) { 
  case TYPE_FLOAT: 
    rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    break; 
  case TYPE_DOUBLE: 
    rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    break; 
  default: 
    rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    break; 
  }
  
  return(rec); 
} 
  /* rec_vi_range_new() */ 


int	rec_vi_range_free(
  struct rec_vi_range_type	*rec
) { 
  free(rec); 
} 
  /* rec_vi_range_free() */ 



int	rec_vi_range_comp(rec1, rec2)
     struct rec_vi_range_type	*rec1, *rec2; 
{
  int	comp; 

  if (rec1->d < rec2->d)
    return(-1); 
  else if (rec1->d > rec2->d)
    return(1);
  else 
    return(0);     
}
/* rec_vi_range_comp() */


rec_vi_range_parent_set(rec, pa)
     struct rec_vi_range_type	*rec; 
     struct a23tree_type	*pa;
{
  rec->parent = pa; 
}
/* rec_vi_range_parent_set() */ 



rec_vi_range_nop(rec, depth)
     struct rec_vi_range_type	*rec; 
     int			depth;
{
}
/* rec_vi_range_nop() */ 



int	rec_get_vi_range(
  struct red_type	*d, 
  int			*lb_ptr, 
  int			*ub_ptr
) {
  int    	             	ci, lb, ub, local_flag; 
  struct rec_vi_range_type	*rec, *nrec; 

  if (d == NORM_FALSE) {
    *lb_ptr = VAR[VI_RED_RANGE].U.DISC.UB+1; 
    *ub_ptr = VAR[VI_RED_RANGE].U.DISC.LB-1; 
    return(FLAG_NO_VALUE); 
  }
  else if (d == NORM_NO_RESTRICTION || VI_RED_RANGE < d->var_index) {
    *lb_ptr = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = VAR[VI_RED_RANGE].U.DISC.UB; 
    return(FLAG_ANY_VALUE); 
  }
  rec = rec_vi_range_new(d); 
  nrec = (struct rec_vi_range_type *) add_23tree(
    (struct rec_type *) rec, 
    range_tree, rec_vi_range_comp, rec_vi_range_free,
    rec_vi_range_nop, rec_vi_range_parent_set, rec_vi_range_nop
  );
  if (rec != nrec) { 
    *lb_ptr = nrec->u.disc.lb; 
    *ub_ptr = nrec->u.disc.ub; 
    return(nrec->flag); 
  } 

  rec->flag = FLAG_NO_VALUE; 
  rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.UB+1; 
  rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.LB-1;   
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_vi_range(d->u.crd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_HRD: 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_vi_range(d->u.hrd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

    break; 

  case TYPE_LAZY_EXP: 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    local_flag = rec_get_vi_range(d->u.lazy.false_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) {  
      return(rec->flag = FLAG_ANY_VALUE); 
    } 
    local_flag = rec_get_vi_range(d->u.lazy.true_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) { 
      return(rec->flag = FLAG_ANY_VALUE); 
    }
    else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      if (rec->flag == FLAG_NO_VALUE)  
        rec->flag = FLAG_SPECIFIC_VALUE; 
        
      if (rec->flag == FLAG_SPECIFIC_VALUE) {  
        if (*lb_ptr > lb) 
          *lb_ptr = lb; 
        if (*ub_ptr < ub) 
          *ub_ptr = ub; 
      } 
      if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
          && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
          ) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      } 
    } 
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

  case TYPE_FLOAT: 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_vi_range(d->u.fdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_DOUBLE: 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_vi_range(d->u.dfdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  default: 
    if (d->var_index == VI_RED_RANGE) { 
      ci = d->u.ddd.child_count-1; 
      rec->u.disc.lb = *lb_ptr = d->u.ddd.arc[0].lower_bound; 
      rec->u.disc.ub = *ub_ptr = d->u.ddd.arc[ci].upper_bound; 
      if (   *lb_ptr == VAR[VI_RED_RANGE].U.DISC.LB
          && *ub_ptr == VAR[VI_RED_RANGE].U.DISC.UB
          ) 
        return(rec->flag = FLAG_ANY_VALUE); 
      else 
        return(rec->flag = FLAG_SPECIFIC_VALUE); 
    } 
    *lb_ptr = rec->u.disc.lb = VAR[VI_RED_RANGE].U.DISC.LB; 
    *ub_ptr = rec->u.disc.ub = VAR[VI_RED_RANGE].U.DISC.UB; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_vi_range(d->u.ddd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DISC.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.disc.lb = *lb_ptr; 
    rec->u.disc.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  }
/*
  fprintf(RED_OUT, "\n************\nadd sync place input:\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "add sync place computed output:\n"); 
  red_print_graph(result); 
*/
  return(rec->flag); 
}
/* rec_get_vi_range() */



int	red_get_vi_range(
  struct red_type	*d, 
  int			vi, 
  int			*lb_ptr, 
  int			*ub_ptr
) { 
  int	flag; 
  
  switch (VAR[vi].TYPE) { 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CRD: 
  case TYPE_HRD: 
    fprintf(RED_OUT, 
      "\nERROR: incompatible variable type of %1d:%s in red_get_vi_range().\n", 
      vi, VAR[vi].NAME
    ); 
    bk(0); 
  default: 
    break; 	
  } 
  VI_RED_RANGE = vi; 

  init_23tree(&range_tree);
  flag = rec_get_vi_range(d, lb_ptr, ub_ptr);
  free_entire_23tree(range_tree, rec_vi_range_free);

  return(flag); 
}
  /* red_get_vi_range() */ 






int	rec_get_float_range(
  struct red_type	*d, 
  float			*lb_ptr, 
  float			*ub_ptr
) {
  int                 		ci, local_flag; 
  float				lb, ub; 
  struct rec_vi_range_type	*rec, *nrec; 

  if (d == NORM_FALSE) {
    *lb_ptr = 0; 
    *ub_ptr = -1; 
    return(FLAG_NO_VALUE); 
  }
  else if (d == NORM_NO_RESTRICTION || VI_RED_RANGE < d->var_index) {
    *lb_ptr = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = VAR[VI_RED_RANGE].U.FLT.UB; 
    return(FLAG_ANY_VALUE); 
  }
  rec = rec_vi_range_new(d); 
  nrec = (struct rec_vi_range_type *) add_23tree(
    (struct rec_type *) rec, 
    range_tree, rec_vi_range_comp, rec_vi_range_free,
    rec_vi_range_nop, rec_vi_range_parent_set, rec_vi_range_nop
  );
  if (rec != nrec) { 
    *lb_ptr = nrec->u.flt.lb; 
    *ub_ptr = nrec->u.flt.ub; 
    return(nrec->flag); 
  } 

  rec->flag = FLAG_NO_VALUE; 
  rec->u.flt.lb = 0; 
  rec->u.flt.ub = -1;   
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_float_range(d->u.crd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_HRD: 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_float_range(d->u.hrd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

    break; 

  case TYPE_LAZY_EXP: 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    local_flag = rec_get_float_range(d->u.lazy.false_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) {  
      return(rec->flag = FLAG_ANY_VALUE); 
    } 
    local_flag = rec_get_float_range(d->u.lazy.true_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) { 
      return(rec->flag = FLAG_ANY_VALUE); 
    }
    else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      if (rec->flag == FLAG_NO_VALUE)  
        rec->flag = FLAG_SPECIFIC_VALUE; 
        
      if (rec->flag == FLAG_SPECIFIC_VALUE) {  
        if (*lb_ptr > lb) 
          *lb_ptr = lb; 
        if (*ub_ptr < ub) 
          *ub_ptr = ub; 
      } 
      if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
          && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
          ) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      } 
    } 
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

  case TYPE_FLOAT: 
    if (d->var_index == VI_RED_RANGE) { 
      ci = d->u.fdd.child_count-1; 
      rec->u.flt.lb = *lb_ptr = d->u.fdd.arc[0].lower_bound; 
      rec->u.flt.ub = *ub_ptr = d->u.fdd.arc[ci].upper_bound; 
      if (   *lb_ptr == VAR[VI_RED_RANGE].U.FLT.LB
          && *ub_ptr == VAR[VI_RED_RANGE].U.FLT.UB
          ) 
        return(rec->flag = FLAG_ANY_VALUE); 
      else 
        return(rec->flag = FLAG_SPECIFIC_VALUE); 
    } 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_float_range(d->u.fdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_DOUBLE: 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_float_range(d->u.dfdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  default: 
    *lb_ptr = rec->u.flt.lb = VAR[VI_RED_RANGE].U.FLT.LB; 
    *ub_ptr = rec->u.flt.ub = VAR[VI_RED_RANGE].U.FLT.UB; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_float_range(d->u.ddd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.FLT.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.flt.lb = *lb_ptr; 
    rec->u.flt.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  }
/*
  fprintf(RED_OUT, "\n************\nadd sync place input:\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "add sync place computed output:\n"); 
  red_print_graph(result); 
*/
  return(rec->flag); 
}
/* rec_get_float_range() */



int	red_get_float_range(
  struct red_type	*d, 
  int			vi, 
  float			*lb_ptr, 
  float			*ub_ptr
) { 
  int	flag; 
  
  if (VAR[vi].TYPE != TYPE_FLOAT) { 
    fprintf(RED_OUT, 
      "ERROR: non-floating variable %1d:%s in red_get_float_range().\n", 
      vi, VAR[vi].NAME
    ); 	
    bk(0); 
  } 
  VI_RED_RANGE = vi; 

  init_23tree(&range_tree);
  flag = rec_get_float_range(d, lb_ptr, ub_ptr);
  free_entire_23tree(range_tree, rec_vi_range_free);

  return(flag); 
}
  /* red_get_float_range() */ 







int	rec_get_double_range(
  struct red_type	*d, 
  double		*lb_ptr, 
  double		*ub_ptr
) {
  int      	           	ci, local_flag; 
  double			lb, ub; 
  struct rec_vi_range_type	*rec, *nrec; 

  if (d == NORM_FALSE) {
    *lb_ptr = 0; 
    *ub_ptr = -1; 
    return(FLAG_NO_VALUE); 
  }
  else if (d == NORM_NO_RESTRICTION || VI_RED_RANGE < d->var_index) {
    *lb_ptr = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = VAR[VI_RED_RANGE].U.DBLE.UB; 
    return(FLAG_ANY_VALUE); 
  }
  rec = rec_vi_range_new(d); 
  nrec = (struct rec_vi_range_type *) add_23tree(
    (struct rec_type *) rec, 
    range_tree, rec_vi_range_comp, rec_vi_range_free,
    rec_vi_range_nop, rec_vi_range_parent_set, rec_vi_range_nop
  );
  if (rec != nrec) { 
    *lb_ptr = nrec->u.dble.lb; 
    *ub_ptr = nrec->u.dble.ub; 
    return(nrec->flag); 
  } 

  rec->flag = FLAG_NO_VALUE; 
  rec->u.dble.lb = 0; 
  rec->u.dble.ub = -1;   
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_double_range(d->u.crd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_HRD: 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_double_range(d->u.hrd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

    break; 

  case TYPE_LAZY_EXP: 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    local_flag = rec_get_double_range(d->u.lazy.false_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) {  
      return(rec->flag = FLAG_ANY_VALUE); 
    } 
    local_flag = rec_get_double_range(d->u.lazy.true_child, &lb, &ub); 
    if (local_flag == FLAG_ANY_VALUE) { 
      return(rec->flag = FLAG_ANY_VALUE); 
    }
    else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      if (rec->flag == FLAG_NO_VALUE)  
        rec->flag = FLAG_SPECIFIC_VALUE; 
        
      if (rec->flag == FLAG_SPECIFIC_VALUE) {  
        if (*lb_ptr > lb) 
          *lb_ptr = lb; 
        if (*ub_ptr < ub) 
          *ub_ptr = ub; 
      } 
      if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
          && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
          ) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      } 
    } 
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

  case TYPE_DOUBLE: 
    if (d->var_index == VI_RED_RANGE) { 
      ci = d->u.dfdd.child_count-1; 
      rec->u.dble.lb = *lb_ptr = d->u.dfdd.arc[0].lower_bound; 
      rec->u.dble.ub = *ub_ptr = d->u.dfdd.arc[ci].upper_bound; 
      if (   *lb_ptr == VAR[VI_RED_RANGE].U.DBLE.LB
          && *ub_ptr == VAR[VI_RED_RANGE].U.DBLE.UB
          ) 
        return(rec->flag = FLAG_ANY_VALUE); 
      else 
        return(rec->flag = FLAG_SPECIFIC_VALUE); 
    } 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_double_range(d->u.fdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  case TYPE_FLOAT: 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_double_range(d->u.fdd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  default: 
    *lb_ptr = rec->u.dble.lb = VAR[VI_RED_RANGE].U.DBLE.LB; 
    *ub_ptr = rec->u.dble.ub = VAR[VI_RED_RANGE].U.DBLE.UB; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      local_flag = rec_get_double_range(d->u.ddd.arc[ci].child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        return(rec->flag = FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {
      	if (rec->flag == FLAG_NO_VALUE) 
      	  rec->flag = FLAG_SPECIFIC_VALUE; 

      	if (rec->flag == FLAG_SPECIFIC_VALUE) { 
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
        }
      	if (   *lb_ptr <= VAR[VI_RED_RANGE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_RED_RANGE].U.DBLE.UB
      	    ) { 
          return(rec->flag = FLAG_ANY_VALUE); 
        } 
      } 
    }
    rec->u.dble.lb = *lb_ptr; 
    rec->u.dble.ub = *ub_ptr; 
    return(rec->flag);

    break; 
    
  }
/*
  fprintf(RED_OUT, "\n************\nadd sync place input:\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "add sync place computed output:\n"); 
  red_print_graph(result); 
*/
  return(rec->flag); 
}
/* rec_get_double_range() */



int	red_get_double_range(
  struct red_type	*d, 
  int			vi, 
  double		*lb_ptr, 
  double		*ub_ptr
) { 
  int	flag; 
  
  if (VAR[vi].TYPE != TYPE_DOUBLE) { 
    fprintf(RED_OUT, 
      "ERROR: non-double variable %1d:%s in red_get_double_range().\n", 
      vi, VAR[vi].NAME
    ); 	
    bk(0); 
  } 
  VI_RED_RANGE = vi; 

  init_23tree(&range_tree);
  flag = rec_get_double_range(d, lb_ptr, ub_ptr);
  free_entire_23tree(range_tree, rec_vi_range_free);

  return(flag); 
}
  /* red_get_double_range() */ 






/***************************************************************
 *  The following procedure returns the following three values. 
 *  FLAG_SPECIFIC_VALUE: 
 *    This means that psub is evaluated to any integer value in 
 *    [*lbptr, *ubptr]. 
 *    There is no hole in the interval.  
 *  FLAG_SPECIFIC_FLOAT_VALUE: 
 *    This means taht psub is evaluated to any floating point number in 
 *    [*flbptr, *fubptr].  
 *    There is no hole in the interval. 
 *  FLAG_UNSPECIFIC_VALUE: 
 *    This could be the following cases. 
 *    There may be some holes in the interval returned throught the pointers.
 *    There may undecided lower or upper-bounds. 
 */

int	W_INTEGER_PI = 0; 

int 	rec_get_integer_range(
  struct ps_exp_type 	*psub,
  int			*lbptr, /* pointer to lowerbound */ 
  int			*ubptr, /* pointer to upperbound */
  float			*flbptr, 
  float 		*fubptr 
) {
  int 			lb1, ub1, lb2, ub2, 
			b_work, llb, lub, ulb, uub, 
			flag1, flag2;
  float			flb1, fub1, flb2, fub2; 
  struct ps_bunit_type	*b; 
  struct instantiated_argument_type	*ia; 

  switch(psub->type){
  case TYPE_CONSTANT:
    *lbptr = *ubptr = psub->u.value;
    return (FLAG_SPECIFIC_VALUE);
  case TYPE_FLOAT_CONSTANT:
    *flbptr = *fubptr = psub->u.float_value;
    return (FLAG_SPECIFIC_FLOAT_VALUE);
  case TYPE_MACRO_CONSTANT:
    *lbptr 
    = *ubptr 
    = psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value;
    return(FLAG_SPECIFIC_VALUE);
  case TYPE_LOCAL_IDENTIFIER:
    *lbptr = *ubptr = W_INTEGER_PI;
    return(FLAG_SPECIFIC_VALUE);
  case TYPE_NULL:
  case TYPE_FALSE:
    *lbptr = *ubptr = 0;
    return (FLAG_SPECIFIC_VALUE);
  case TYPE_TRUE:
    *lbptr = *ubptr = 1;
    return(FLAG_SPECIFIC_VALUE); 
  case TYPE_PROCESS_COUNT: 
    *lbptr = *ubptr = PROCESS_COUNT; 
    return (FLAG_SPECIFIC_VALUE); 
  case TYPE_MODE_INDEX: 
    *lbptr = *ubptr = psub->u.mode_index.parse_mode->index; 
    return (FLAG_SPECIFIC_VALUE); 
  
  case TYPE_INTERVAL: 
    flag1 = rec_get_integer_range(psub->u.interval.lbound_exp, 
      &lb1, &ub1, &flb1, &fub1 
    );
    flag2 = rec_get_integer_range(psub->u.interval.rbound_exp, 
      &lb2, &ub2, &flb2, &fub2  
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE || flag2 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    if (lb1 > lb2) { 
      lb1 = lb2; 
    } 
    if (ub1 < ub2) 
      ub1 = ub2; 
    *lbptr = lb1; 
    *ubptr = ub1; 
    return(FLAG_SPECIFIC_VALUE); 

  case TYPE_QFD:
    *lbptr = *ubptr = qfd_value(psub->u.atom.var_name);
    return (FLAG_SPECIFIC_VALUE); 
  case TYPE_QSYNC_HOLDER: 
    *lbptr = 1; 
    *ubptr = PROCESS_COUNT; 
    return(FLAG_UNSPECIFIC_VALUE); 
  case TYPE_INLINE_ARGUMENT: 
    if (top_inline_stack == NULL) { 
      fprintf(RED_OUT, "\nError: no inline instantiated arguments:\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    for (ia = top_inline_stack->instantiated_argument_list; 
         ia; 
         ia = ia->next_instantiated_argument
         ) { 
      if (!strcmp(ia->formal_argument_name, psub->u.argument)) 
        break;  
    } 
    if (ia && ia->instantiated_argument->type == TYPE_CONSTANT) { 
      *lbptr = *ubptr = ia->instantiated_argument->u.value; 
      return (FLAG_SPECIFIC_VALUE); 
    } 
    else if (ia && ia->instantiated_argument->type == TYPE_FLOAT_CONSTANT) { 
      *lbptr = *ubptr = ia->instantiated_argument->u.float_value; 
      return (FLAG_SPECIFIC_FLOAT_VALUE); 
    } 
    else { 
      fprintf(RED_OUT, "Error: undeclared inline argument %x at line %1d:%1d.\n", 
        (unsigned int) psub->u.argument, lineno, psub->lineno
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    break; 

  case TYPE_REFERENCE: 
    *lbptr = INT_MIN; 
    *ubptr = INT_MAX; 
    return (FLAG_UNSPECIFIC_VALUE); 
    break; 
    
  case TYPE_DEREFERENCE: 
    *lbptr = 0; 
    *ubptr = VARIABLE_COUNT-1;   
    return (FLAG_UNSPECIFIC_VALUE); 
    break; 

  case TYPE_CLOCK:
  case TYPE_DENSE:
    fprintf(RED_OUT, "\nError, variables in offset.\n"); 
    bk("Error!!!"); 
  case TYPE_DISCRETE:
    *lbptr = psub->u.atom.var->u.disc.lb;  
    *ubptr = psub->u.atom.var->u.disc.ub; 
    *flbptr = 0.0; 
    *fubptr = -1.0; 
    return (FLAG_UNSPECIFIC_VALUE); 
    
  case TYPE_FLOAT:
    *lbptr = -1*INT_MAX;   
    *ubptr = INT_MAX; 
    *flbptr = -1*FLT_MAX;  
    *fubptr = FLT_MAX; 
    return (FLAG_UNSPECIFIC_VALUE); 
    
  case TYPE_DOUBLE:
    *lbptr = -1*INT_MAX;   
    *ubptr = INT_MAX; 
    *flbptr = -1*FLT_MAX;  
    *fubptr = FLT_MAX; 
    return (FLAG_UNSPECIFIC_VALUE); 
    
  case TYPE_POINTER: 
    *lbptr = 0; 
    *ubptr = PROCESS_COUNT; 
    *flbptr = 0.0; 
    *fubptr = -1.0; 
    return (FLAG_UNSPECIFIC_VALUE); 
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    fprintf(RED_OUT, "\nERROR, computing range of bit values.\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case ARITH_ADD:
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE);
    }
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE); 
    }
    if (flag1 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) {
        /* first calculate the lowerbound */ 
        *flbptr = flb1 + flb2;
    
        /* second calculate the upperbound */ 
        *fubptr = fub1 + fub2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      }
      else { 
        /* first calculate the lowerbound */ 
        *flbptr = flb1 + lb2;
    
        /* second calculate the upperbound */ 
        *fubptr = fub1 + ub2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) { 
        /* first calculate the lowerbound */ 
        *flbptr = lb1 + flb2;
    
        /* second calculate the upperbound */ 
        *fubptr = ub1 + fub2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
      else { 
        /* first calculate the lowerbound */ 
        *lbptr = lb1 + lb2;
    
        /* second calculate the upperbound */ 
        *ubptr = ub1 + ub2;
        return (FLAG_SPECIFIC_VALUE);
    } }
    break; 
  case ARITH_MINUS:
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE);
    }
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE); 
    }
    if (flag1 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) {
        /* first calculate the lowerbound */ 
        *flbptr = flb1 - fub2;
    
        /* second calculate the upperbound */ 
        *fubptr = fub1 - flb2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      }
      else { 
        /* first calculate the lowerbound */ 
        *flbptr = flb1 - ub2;
    
        /* second calculate the upperbound */ 
        *fubptr = fub1 - lb2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) { 
        /* first calculate the lowerbound */ 
        *flbptr = lb1 - fub2;
    
        /* second calculate the upperbound */ 
        *fubptr = ub1 - flb2;
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
      else { 
        /* first calculate the lowerbound */ 
        *lbptr = lb1 - ub2;
    
        /* second calculate the upperbound */ 
        *ubptr = ub1 - lb2;
        return (FLAG_SPECIFIC_VALUE);
    } }
    break; 
  case ARITH_MULTIPLY:
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE);
    }
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE); 
    }
    if (flag1 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) {
      	float	c1, c2, c3, c4; 
      	
      	c1 = flb1*flb2; 
      	c2 = flb1*fub2; 
      	c3 = fub1*flb2; 
      	c4 = fub1*fub2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(flt_min(c1, c2), flt_min(c3, c4));
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(flt_max(c1, c2), flt_max(c3, c4));
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      }
      else { 
      	float	c1, c2, c3, c4; 
      	
      	c1 = flb1*lb2; 
      	c2 = flb1*ub2; 
      	c3 = fub1*lb2; 
      	c4 = fub1*ub2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(flt_min(c1, c2), flt_min(c3, c4));
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(flt_max(c1, c2), flt_max(c3, c4));
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      	float	c1, c2, c3, c4; 
      	
      	c1 = lb1*flb2; 
      	c2 = lb1*fub2; 
      	c3 = ub1*flb2; 
      	c4 = ub1*fub2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(flt_min(c1, c2), flt_min(c3, c4));
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(flt_max(c1, c2), flt_max(c3, c4));
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
      else { 
      	int	c1, c2, c3, c4; 
      	
      	c1 = lb1*lb2; 
      	c2 = lb1*ub2; 
      	c3 = ub1*lb2; 
      	c4 = ub1*ub2; 
      	
        /* first calculate the lowerbound */ 
        *lbptr = int_min(int_min(c1, c2), int_min(c3, c4));
    
        /* second calculate the upperbound */ 
        *ubptr = int_max(int_max(c1, c2), int_max(c3, c4));
        return (FLAG_SPECIFIC_VALUE);
    } }
    break; 
  case ARITH_DIVIDE:
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE);
    }
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) { 
      return(FLAG_UNSPECIFIC_VALUE); 
    }
    if (flag1 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) {
      	float	c1, c2, c3, c4; 
      	
      	if (flb2 <= 0 && fub2 >= 0) { 
      	  fprintf(RED_OUT, "ERROR: Division by zero.\n"); 
      	  bk(0); 
      	} 
      	c1 = flb1/flb2; 
      	c2 = flb1/fub2; 
      	c3 = fub1/flb2; 
      	c4 = fub1/fub2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(flt_min(c1, c2), flt_min(c3, c4));
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(flt_max(c1, c2), flt_max(c3, c4));
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      }
      else { 
      	float	c1, c2; 
      	
      	if (lb2 <= 0 && ub2 >= 0) { 
      	  fprintf(RED_OUT, "ERROR: Division by zero.\n"); 
      	  bk(0); 
      	} 
      	if (lb2 != ub2) 
      	  return(FLAG_UNSPECIFIC_VALUE); 
      	  
      	c1 = flb1/lb2; 
      	c2 = fub1/lb2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(c1, c2);
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(c1, c2);
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) { 
      	float	c1, c2; 
      	
      	if (flb2 <= 0 && fub2 >= 0) { 
      	  fprintf(RED_OUT, "ERROR: Division by zero.\n"); 
      	  bk(0); 
      	} 
      	if (lb1 != ub1) 
      	  return(FLAG_UNSPECIFIC_VALUE); 

      	c1 = lb1/flb2; 
      	c2 = lb1/fub2; 
      	
        /* first calculate the lowerbound */ 
        *flbptr = flt_min(c1, c2);
    
        /* second calculate the upperbound */ 
        *fubptr = flt_max(c1, c2);
        return (FLAG_SPECIFIC_FLOAT_VALUE);
      } 
      else { 
      	if (lb2 <= 0 && ub2 >= 0) { 
      	  fprintf(RED_OUT, "ERROR: Division by zero.\n"); 
      	  bk(0); 
      	} 
      	if (lb1 != ub1 || lb2 != ub2) 
      	  return(FLAG_UNSPECIFIC_VALUE); 

        /* first calculate the lowerbound */ 
        *ubptr = *lbptr = lb1/lb2;
        return (FLAG_SPECIFIC_VALUE);
    } }
    break; 

  case ARITH_MODULO:
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_SPECIFIC_FLOAT_VALUE) {
      fprintf(RED_OUT, 
        "\nERROR: Illegal modulo operations on floating points.\n"
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (   flag1 == FLAG_UNSPECIFIC_VALUE
             || (flag1 == FLAG_SPECIFIC_VALUE && lb1 != ub1) 
             ) { 
      return(FLAG_UNSPECIFIC_VALUE);
    }
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    ); 
    if (flag2 == FLAG_SPECIFIC_FLOAT_VALUE) {
      fprintf(RED_OUT, 
        "\nERROR: Illegal modulo operations on floating points.\n"
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (   flag2 == FLAG_UNSPECIFIC_VALUE
             || (flag2 == FLAG_SPECIFIC_VALUE && lb2 != ub2) 
             ) { 
      return(FLAG_UNSPECIFIC_VALUE); 
    }
    else if (lb2 == 0) { 
      fprintf(RED_OUT, "ERROR: Division by zero.\n"); 
      bk(0); 
    }  
    /* first calculate the lowerbound */ 
    *ubptr = *lbptr = lb1 % lb2;
    return (FLAG_SPECIFIC_VALUE);
    break; 

  case ARITH_CONDITIONAL: {
    int		clb, cub; 
    float	cflb, cfub; 
    
    flag1 = rec_get_integer_range(
      psub->u.arith_cond.if_exp, &lb1, &ub1, &flb1, &fub1 
    );
    flag2 = rec_get_integer_range(
      psub->u.arith_cond.else_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (   flag1 == FLAG_UNSPECIFIC_VALUE 
        || flag2 == FLAG_UNSPECIFIC_VALUE
        || flag1 != flag2
        ) 
      return(FLAG_UNSPECIFIC_VALUE); 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (lb1 < lb2)
        *lbptr = lb1; 
      else 
        *lbptr = lb2; 
      if (ub1 > ub2) 
        *ubptr = ub1; 
      else 
        *ubptr = ub2; 
      return (FLAG_SPECIFIC_VALUE); 
    } 
    else { 
      if (flb1 < flb2) 
        *flbptr = flb1; 
      else 
        *flbptr = flb2; 
      if (fub1 > fub2) 
        *fubptr = fub1; 
      else  
        *fubptr = fub2; 
      return (FLAG_SPECIFIC_FLOAT_VALUE); 
    } 
    flag1 = rec_get_integer_range(psub->u.arith_cond.cond, 
      &clb, &cub, &cflb, &cfub  
    ); 
    if (flag1 == FLAG_SPECIFIC_VALUE) {
      if (clb == TYPE_TRUE) { 
      	*lbptr = lb1; 
        *ubptr = ub1; 
        return (FLAG_SPECIFIC_VALUE); 
      }
      else { 
      	*lbptr = lb2; 
        *ubptr = ub2; 
        return (FLAG_SPECIFIC_VALUE); 
      }
    } 
    else { 
      return (FLAG_UNSPECIFIC_VALUE); 
    } 
    break; 
  }
  case ARITH_EQ: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
	int	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   lb1 == ub1 
            && lb2 == ub2  
            && lb1 == lb2 
            ) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (lb1 > lb2) {
          lbmax = lb1; 
        } 
        else { 
          lbmax = lb2; 
        }
        if (ub1 < ub2) { 
          ubmin = ub1; 
        }
        else { 
          ubmin = ub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 
		
        if (   lb1 == ub1 
            && flb2 == fub2  
            && lb1 == flb2 
            ) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (lb1 > flb2) {
          lbmax = lb1; 
        } 
        else { 
          lbmax = flb2; 
        }
        if (ub1 < fub2) { 
          ubmin = ub1; 
        }
        else { 
          ubmin = fub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   flb1 == fub1 
            && lb2 == ub2  
            && flb1 == lb2 
            ) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (flb1 > lb2) {
          lbmax = flb1; 
        } 
        else { 
          lbmax = lb2; 
        }
        if (fub1 < ub2) { 
          ubmin = fub1; 
        }
        else { 
          ubmin = ub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   flb1 == fub1 
            && flb2 == fub2  
            && flb1 == flb2 
            ) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (flb1 > flb2) {
          lbmax = flb1; 
        } 
        else { 
          lbmax = flb2; 
        }
        if (fub1 < fub2) { 
          ubmin = fub1; 
        }
        else { 
          ubmin = fub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
    } }
    	
    break; 

  case ARITH_NEQ: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
	int	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   lb1 == ub1
            && lb2 == ub2  
            && lb1 == lb2 
            ) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (lb1  > lb2) {
          lbmax = lb1; 
        } 
        else { 
          lbmax = lb2; 
        }
        if (ub1 < ub2) { 
          ubmin = ub1; 
        }
        else { 
          ubmin = ub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
      }
      else { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   lb1 == ub1
            && flb2 == fub2  
            && lb1 == flb2 
            ) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (lb1  > flb2) {
          lbmax = lb1; 
        } 
        else { 
          lbmax = flb2; 
        }
        if (ub1 < fub2) { 
          ubmin = ub1; 
        }
        else { 
          ubmin = fub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
      } 
    } 
    else {
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   flb1 == fub1
            && lb2 == ub2  
            && flb1 == lb2 
            ) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (flb1  > lb2) {
          lbmax = flb1; 
        } 
        else { 
          lbmax = lb2; 
        }
        if (ub1 < ub2) { 
          ubmin = fub1; 
        }
        else { 
          ubmin = ub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
      }
      else { 
	float	lbmin, ubmax, // for the union 
		lbmax, ubmin;  // for the intersection 

        if (   flb1 == fub1
            && flb2 == fub2  
            && flb1 == flb2 
            ) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
         
        // Now we calculate the intersection of the two interval. 
        if (flb1  > flb2) {
          lbmax = flb1; 
        } 
        else { 
          lbmax = flb2; 
        }
        if (fub1 < fub2) { 
          ubmin = fub1; 
        }
        else { 
          ubmin = fub2; 
        } 
        // Then the emptiness of the intersection implies 
        // that false is the only 
        // possible value. 
        if (lbmax <= ubmin) { 
        // There is an intersection. 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 	
        } 
        else { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
      } 
    }
    break; 
  case ARITH_LEQ: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (lb1 > ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 <= ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else {
        if (lb1 > fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 <= fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      } 
    } 
    else { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (flb1 > ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 <= ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else {
        if (flb1 > fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 <= fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return (FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      } 
    } 
    break; 
  case ARITH_LESS: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (lb1 >= ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 < ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (lb1 >= fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 < fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (flb1 >= ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 < ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (flb1 >= fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 < fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
    } 
    break; 
  case ARITH_GEQ: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (lb1 > ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 <= ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (lb1 > fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 <= fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      } 
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (flb1 > ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 <= ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (flb1 > fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 <= fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      } 
    } 
    break; 
  case ARITH_GREATER: 
    flag1 = rec_get_integer_range(
      psub->u.arith.lhs_exp, &lb1, &ub1, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    flag2 = rec_get_integer_range(
      psub->u.arith.rhs_exp, &lb2, &ub2, &flb2, &fub2
    );
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE); 
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (flag1 == FLAG_SPECIFIC_VALUE) { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (lb1 >= ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 < ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (lb1 >= fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (ub1 < fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
    }
    else { 
      if (flag2 == FLAG_SPECIFIC_VALUE) { 
        if (flb1 >= ub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 < ub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
      else { 
        if (flb1 >= fub2) { 
          *lbptr = *ubptr = TYPE_FALSE; 
          return(FLAG_SPECIFIC_VALUE); 
        }
        else if (fub1 < fub2) { 
          *lbptr = *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 
        } 
        else { 
          *lbptr = TYPE_FALSE; 
          *ubptr = TYPE_TRUE; 
          return(FLAG_SPECIFIC_VALUE); 	
        } 
      }
    } 
    break; 
  case EQ: 
  case NEQ: 
  case LEQ: 
  case LESS: 
  case GEQ: 
  case GREATER: 
    return(FLAG_UNSPECIFIC_VALUE); 
  
  case TYPE_INLINE_CALL: 
    if (psub->u.inline_call.instantiated_exp) 
      return(rec_get_integer_range( 
        psub->u.inline_call.instantiated_exp, 
        lbptr, ubptr, flbptr, fubptr 
      ) );
    else 
      return(rec_get_integer_range( 
        psub->u.inline_call.inline_declare->u.inline_declare.declare_exp, 
        lbptr, ubptr, flbptr, fubptr 
      ) ); 
    break;   
  
  case IMPLY: 
    flag1 = rec_get_integer_range(
      psub->u.bexp.blist->subexp, &lb1, &ub1, &flb1, &fub1
    );
    if (   flag1 == FLAG_SPECIFIC_VALUE 
        && ub1 == TYPE_FALSE 
        ) {
      *lbptr = *ubptr = TYPE_TRUE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    flag2 = rec_get_integer_range(
      psub->u.bexp.blist->bnext->subexp, &lb2, &ub2, &flb2, &fub2 
    );
    if (   flag2 == FLAG_SPECIFIC_VALUE 
        && lb1 == TYPE_TRUE 
        ) {
      *lbptr = *ubptr = TYPE_TRUE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    else if (   flag1 == FLAG_SPECIFIC_VALUE
             && lb1 == TYPE_TRUE
             && flag2 == FLAG_SPECIFIC_VALUE
             && ub2 == TYPE_FALSE
             ) { 
      *lbptr = *ubptr = TYPE_FALSE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    else { 
      return(FLAG_UNSPECIFIC_VALUE); 	
    }     	
    break; 
    
  case NOT: 
    return(rec_get_integer_range(
      psub->u.bexp.blist->subexp, ubptr, lbptr, &flb1, &fub1
    ) );
    break; 

  case AND: {
    int	lbmin; 
    
    lbmin = TYPE_TRUE; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      flag1 = rec_get_integer_range(b->subexp, &lb1, &ub1, &flb1, &fub1); 
      if (flag1 == FLAG_SPECIFIC_VALUE && ub1 == TYPE_FALSE) { 
        *lbptr = *ubptr = TYPE_FALSE; 
        return (FLAG_SPECIFIC_VALUE); 	
      } 
      else if (   flag1 == FLAG_UNSPECIFIC_VALUE 
               || (flag1 == FLAG_SPECIFIC_VALUE && lb1 == TYPE_FALSE) 
               )
        lbmin = TYPE_FALSE; 
    } 
    if (lbmin == TYPE_TRUE) { 
      *lbptr = *ubptr = TYPE_TRUE; 
      return (FLAG_SPECIFIC_VALUE); 	
    } 
    else { 
      *lbptr = TYPE_FALSE; 
      *ubptr = TYPE_TRUE; 
      return (FLAG_UNSPECIFIC_VALUE); 	
    }     	
    break; 
  }
  case OR: {
    int	ubmax; 
    
    ubmax = TYPE_FALSE; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      flag1 = rec_get_integer_range(b->subexp, &lb1, &ub1, &flb1, &fub1); 
      if (flag1 == FLAG_SPECIFIC_VALUE && lb1 == TYPE_TRUE) { 
        *lbptr = *ubptr = TYPE_TRUE; 
        return(FLAG_SPECIFIC_VALUE); 	
      } 
      else if (   flag1 == FLAG_UNSPECIFIC_VALUE 
               || (flag1 == FLAG_SPECIFIC_VALUE && ub1 == TYPE_TRUE) 
               ) 
        ubmax = TYPE_TRUE; 
    } 
    if (ubmax == TYPE_FALSE) { 
      *lbptr = *ubptr = TYPE_FALSE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    else { 
      *lbptr = TYPE_FALSE; 
      *ubptr = TYPE_TRUE; 
      return(FLAG_UNSPECIFIC_VALUE); 	
    } 
    break; 
  }
  case FORALL: {
    int	lbmin; 
    
    flag1 = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE);  
    flag2 = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE);  
    if (llb > uub) { 
      *lbptr = *ubptr = TYPE_TRUE; 
      return (FLAG_SPECIFIC_VALUE); 	
    } 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    lbmin = TYPE_TRUE; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      flag1 = rec_get_integer_range(
        psub->u.qexp.child, &lb1, &ub1, &flb1, &fub1
      ); 
      if (flag1 == FLAG_SPECIFIC_VALUE && ub1 == TYPE_FALSE) { 
        *lbptr = *ubptr = TYPE_FALSE; 
        pop_quantified_value_stack(psub); 
        return (FLAG_SPECIFIC_VALUE); 	
      } 
      else if (   flag1 == FLAG_UNSPECIFIC_VALUE 
               || (flag1 == FLAG_SPECIFIC_VALUE && lb1 == TYPE_FALSE) 
               ) 
        lbmin = TYPE_FALSE; 
    } 
    pop_quantified_value_stack(psub); 
    if (lbmin == TYPE_TRUE) { 
      *lbptr = *ubptr = TYPE_TRUE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    else { 
      *lbptr = TYPE_FALSE; 
      *ubptr = TYPE_TRUE; 
      return(FLAG_UNSPECIFIC_VALUE); 	
    }     	
    break; 
  }
  case EXISTS: {
    int	ubmax; 
    
    flag1 = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb1, &fub1
    ); 
    if (flag1 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE);  
    flag2 = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb2, &fub2
    ); 
    if (flag2 == FLAG_UNSPECIFIC_VALUE) 
      return(FLAG_UNSPECIFIC_VALUE);  
    if (llb > uub) { 
      *lbptr = *ubptr = TYPE_TRUE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    ubmax = TYPE_FALSE; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      flag1 = rec_get_integer_range(
        psub->u.qexp.child, &lb1, &ub1, &flb1, &fub1
      ); 
      if (flag1 == FLAG_SPECIFIC_VALUE && lb1 == TYPE_TRUE) { 
        *lbptr = *ubptr = TYPE_TRUE; 
        pop_quantified_value_stack(psub); 
        return(FLAG_SPECIFIC_VALUE); 	
      } 
      else if (   flag1 == FLAG_UNSPECIFIC_VALUE 
               || (flag1 == FLAG_SPECIFIC_VALUE && ub1 == TYPE_TRUE) 
               )
        ubmax = TYPE_TRUE; 
    } 
    pop_quantified_value_stack(psub); 
    if (ubmax == TYPE_FALSE) { 
      *lbptr = *ubptr = TYPE_FALSE; 
      return(FLAG_SPECIFIC_VALUE); 	
    } 
    else { 
      *lbptr = TYPE_FALSE; 
      *ubptr = TYPE_TRUE; 
      return(FLAG_UNSPECIFIC_VALUE); 	
    }     	
    break; 
  }
  default:
    fprintf(RED_OUT, "\nParser: Huh ? (parse 2) \n");
    bk(); 
  }

}
/* rec_get_integer_range() */ 




/***************************************************************
 *  The following procedure returns the following three values. 
 *  FLAG_SPECIFIC_VALUE: 
 *    This means that psub is evaluated to any integer value in 
 *    [*lbptr, *ubptr]. 
 *    There is no hole in the interval.  
 *  FLAG_SPECIFIC_FLOAT_VALUE: 
 *    This means taht psub is evaluated to any floating point number in 
 *    [*flbptr, *fubptr].  
 *    There is no hole in the interval. 
 *  FLAG_UNSPECIFIC_VALUE: 
 *    This could be the following cases. 
 *    There may be some holes in the interval returned throught the pointers.
 *    There may undecided lower or upper-bounds. 
 */

int	count_get_integer_range = 0; 

int	get_integer_range(psub, pi, lbptr, ubptr, flbptr, fubptr)
  struct ps_exp_type	*psub;
  int			pi, *lbptr, *ubptr;
  float			*flbptr, *fubptr; 
{
  int	result; 
  
/*
  fprintf(RED_OUT, "\nget integer range (%1d) for pi=%1d and exp:\n", 
    ++count_get_integer_range, pi
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
*/  
  W_INTEGER_PI = pi;
  result = rec_get_integer_range(psub, lbptr, ubptr, flbptr, fubptr); 
/*  
  fprintf(RED_OUT, "  get integer range (%1d) result = %1d: lb=%1d,ub=%1d; flb=%f,fub=%f\n", 
    count_get_integer_range, result, *lbptr, *ubptr, *flbptr, *fubptr 
  ); 
  fflush(RED_OUT); 
*/  
  return(result); 
}
/* get_integer_range() */









void 	rec_get_rational_range(psub, lnptr, ldptr, unptr, udptr)
  struct ps_exp_type 	*psub;
  int			*lnptr /* pointer to lowerbound, numerator */, 
			*ldptr /* pointer to lowerbound, denominator */,
			*unptr /* pointer to upperbound, numerator */, 
			*udptr /* pointer to upperbound, denominator */;
{
  int 			lnum1, lden1, unum1, uden1, lnum2, lden2, unum2, uden2, 
			n_work, d_work, llb, lub, ulb, uub, 
			lnmin, ldmin, unmax, udmax, // for the union 
			lnmax, ldmax, unmin, udmin, // for the intersection 
			clnum, clden, cunum, cuden; 
  struct ps_bunit_type	*b; 

  switch(psub->type){
  case TYPE_CONSTANT:
    *lnptr = *unptr = psub->u.value;
    *ldptr = *udptr = 1;
    return;
  case TYPE_MACRO_CONSTANT:
    *lnptr
    = *unptr 
    = psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value;
    *ldptr = *udptr = 1;
    return;
  case TYPE_LOCAL_IDENTIFIER:
    *lnptr = *unptr = W_PI;
    *ldptr = *udptr = 1;
    return;
  case TYPE_NULL:
  case TYPE_FALSE:
    *lnptr = *unptr = 0;
    *ldptr = *udptr = 1;
    return;
  case TYPE_TRUE:
    *lnptr = *unptr = 1;
    *ldptr = *udptr = 1;
    return; 
  case TYPE_PROCESS_COUNT: 
    *lnptr = *unptr = PROCESS_COUNT; 
    *ldptr = *udptr = 1; 
    return; 
  case TYPE_MODE_INDEX: 
    *lnptr = *unptr = psub->u.mode_index.parse_mode->index; 
    *ldptr = *udptr = 1; 
    return; 
  
  case TYPE_INTERVAL: 
    rec_get_rational_range(psub->u.interval.lbound_exp, 
      &lnum1, &lden1, &unum1, &uden1 
    );
    rec_get_rational_range(psub->u.interval.rbound_exp, 
      &lnum2, &lden2, &unum2, &uden2 
    ); 
    if (lnum1 * lden2 > lnum2 * lden1) { 
      lnum1 = lnum2; 
      lden1 = lden2; 
    } 
    if (unum1 * uden2 < unum2 * uden1) {
      unum1 = unum2; 
      uden1 = uden2; 
    } 
    *lnptr = lnum1;
    *ldptr = lden1;  
    *unptr = unum1; 
    *udptr = uden1; 
    return; 
  case TYPE_QFD:
    *lnptr = *unptr = qfd_value(psub->u.atom.var_name);
    *ldptr = *udptr = 1;
    return; 
  case TYPE_QSYNC_HOLDER: 
    *lnptr = 1; 
    *ldptr = 1; 
    *unptr = PROCESS_COUNT; 
    *udptr = 1; 
    return; 
  case TYPE_REFERENCE: 
    *lnptr = INT_MIN; 
    *ldptr = 1; 
    *unptr = INT_MAX; 
    *udptr = 1; 
    return; 

  case TYPE_DEREFERENCE: 
    *lnptr = 0; 
    *ldptr = 1; 
    *unptr = VARIABLE_COUNT-1; 
    *udptr = 1; 
    return; 

  case TYPE_CLOCK:
  case TYPE_DENSE:
    fprintf(RED_OUT, "\nError, variables in offset.\n"); 
    bk("Error!!!"); 
  case TYPE_DISCRETE:
    *lnptr = psub->u.atom.var->u.disc.lb; 
    *ldptr = 1; 
    *unptr = psub->u.atom.var->u.disc.ub; 
    *udptr = 1; 
    return; 
    
  case TYPE_POINTER: 
    *lnptr = 0; 
    *ldptr = 1; 
    *unptr = PROCESS_COUNT; 
    *udptr = 1; 
    return; 
    
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    fprintf(RED_OUT, "\nERROR, computing range of bit values.\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case ARITH_ADD:
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    /* first calculate the lowerbound */ 
    *lnptr = lnum1 * lden2 + lnum2 *lden1;
    *ldptr = lden2 * lden1;
    rational_normalize(lnptr, ldptr);
    
    /* second calculate the upperbound */ 
    *unptr = unum1 * uden2 + unum2 *uden1;
    *udptr = uden2 * uden1;
    rational_normalize(unptr, udptr);
    return;
  case ARITH_MINUS:
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    /* first calculate the lowerbound */ 
    *lnptr = lnum1 * uden2 - unum2 *lden1;
    *ldptr = uden2 * lden1;
    rational_normalize(lnptr, ldptr);
    
    /* second calculate the upperbound */ 
    *unptr = unum1 * lden2 - lnum2 *uden1;
    *udptr = uden2 * uden1;
    rational_normalize(unptr, udptr);
    return;
  case ARITH_MULTIPLY:
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2); 

    /* first calcuate the lower lower corner. */ 
    *lnptr = lnum1 * lnum2;
    *ldptr = lden2 * lden1;
    rational_normalize(lnptr, ldptr);
    *unptr = *lnptr; 
    *udptr = *ldptr; 
    
    /* second calculate the lower upper corner. */ 
    n_work = lnum1 * unum2;
    d_work = uden2 * lden1;
    rational_normalize(&n_work, &d_work); 
    if (n_work/d_work < (*lnptr)/(*ldptr)) {
      *lnptr = n_work; 
      *ldptr = d_work; 
    }
    if (n_work/d_work > (*unptr)/(*udptr)) {
      *unptr = n_work; 
      *udptr = d_work; 
    }
    
    /* third calculate the lower upper corner. */ 
    n_work = unum1 * unum2;
    d_work = uden2 * uden1;
    rational_normalize(&n_work, &d_work); 
    if (n_work/d_work < (*lnptr)/(*ldptr)) {
      *lnptr = n_work; 
      *ldptr = d_work; 
    }
    if (n_work/d_work > (*unptr)/(*udptr)) {
      *unptr = n_work; 
      *udptr = d_work; 
    }
    
    /* fourth calculate the lower upper corner. */ 
    n_work = unum1 * lnum2;
    d_work = lden2 * uden1;
    rational_normalize(&n_work, &d_work); 
    if (n_work/d_work < (*lnptr)/(*ldptr)) {
      *lnptr = n_work; 
      *ldptr = d_work; 
    }
    if (n_work/d_work > (*unptr)/(*udptr)) {
      *unptr = n_work; 
      *udptr = d_work; 
    }
    
    return;
  case ARITH_DIVIDE:
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);

    if (lnum2/lden2 <= 0 && unum2/uden2 >= 0) {
      fprintf(RED_OUT, "\nUnexpected divisor zero in a division operation! \n");
      bk(); 
    }
    else {
      /* first calcuate the lower lower corner. */ 
      *lnptr = lnum1 * lden2;
      *ldptr = lnum2 * lden1;
      rational_normalize(lnptr, ldptr);
      *unptr = *lnptr; 
      *udptr = *ldptr; 
    
      /* second calculate the lower upper corner. */ 
      n_work = lnum1 * uden2;
      d_work = unum2 * lden1;
      rational_normalize(&n_work, &d_work); 
      if (n_work/d_work < (*lnptr)/(*ldptr)) {
        *lnptr = n_work; 
        *ldptr = d_work; 
      }
      if (n_work/d_work > (*unptr)/(*udptr)) {
        *unptr = n_work; 
        *udptr = d_work; 
      }
    
      /* third calculate the lower upper corner. */ 
      n_work = unum1 * uden2;
      d_work = unum2 * uden1;
      rational_normalize(&n_work, &d_work); 
      if (n_work/d_work < (*lnptr)/(*ldptr)) {
        *lnptr = n_work; 
        *ldptr = d_work; 
      }
      if (n_work/d_work > (*unptr)/(*udptr)) {
        *unptr = n_work; 
        *udptr = d_work; 
      }
    
      /* fourth calculate the lower upper corner. */ 
      n_work = unum1 * lden2;
      d_work = lnum2 * uden1;
      rational_normalize(&n_work, &d_work); 
      if (n_work/d_work < (*lnptr)/(*ldptr)) {
        *lnptr = n_work; 
        *ldptr = d_work; 
      }
      if (n_work/d_work > (*unptr)/(*udptr)) {
        *unptr = n_work; 
        *udptr = d_work; 
      }
    
      return;
    }
  case ARITH_MODULO:
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);

    if (lnum2/lden2 <= 0 && unum2/uden2 >= 0){ 
      fprintf(RED_OUT, "\nUnexpected divisor zero in a modulo operation! \n");
      bk(); 
    }
    else { 
      /* first calcuate the lower lower corner. */ 
      lnum2 = lnum2/lden2; 
      if (lnum2 < 0) 
        lnum2 = -1 * lnum2; 
      unum2 = unum2/uden2; 
      if (unum2 < 0) 
        unum2 = -1 * unum2; 
      if (lnum2 < unum2)
        lnum2 = unum2; 
        
      *lnptr = 0; 
      *ldptr = 1; 
      *unptr = lnum2-1; 
      *udptr = 1; 
    
      return;
    }
  case ARITH_CONDITIONAL: 
    rec_get_rational_range(psub->u.arith_cond.if_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith_cond.else_exp, &lnum2, &lden2, &unum2, &uden2);
    if (lnum1*lden2 == lnum2*lden1 && unum1*uden2 == unum2*uden1) { 
      *lnptr = lnum1; 
      *ldptr = lden1; 
      *unptr = unum1; 
      *udptr = uden1; 
      return; 
    } 
    rec_get_rational_range(psub->u.arith_cond.cond, 
      &clnum, &clden, &cunum, &cuden 
    ); 
    if (clnum == TYPE_TRUE) { 
      *lnptr = lnum1; 
      *ldptr = lden1; 
      *unptr = unum1; 
      *udptr = uden1; 
      return; 
    } 
    else if (cunum == TYPE_FALSE) { 
      *lnptr = lnum2; 
      *ldptr = lden2; 
      *unptr = unum2; 
      *udptr = uden2; 
      return; 
    } 
    else { 
      if (lnum1*lden2 < lnum2*lden1) { 
      	*lnptr = lnum1; 
      	*ldptr = lden1; 
      }
      else { 
      	*lnptr = lnum2; 
      	*ldptr = lden2; 
      } 
      if (unum1*uden2 > unum2*uden1) { 
      	*unptr = unum1; 
      	*udptr = uden1; 
      }
      else { 
      	*unptr = unum2; 
      	*udptr = uden2; 
      } 
      return; 
    } 
    break; 
  case ARITH_EQ: 
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (   lnum1 == unum1 && lden1 == uden1
        && lnum2 == unum2 && lden2 == uden2 
        && lnum1 == lnum2 && lden1 == lden2
        ) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
         
    // Now we calculate the intersection of the two interval. 
    if (lnum1 * lden2 > lnum2 * lden2) {
      lnmax = lnum1; 
      ldmax = lden1; 
    } 
    else { 
      lnmax = lnum2; 
      ldmax = lden2; 
    }
    if (unum1 * uden2 < unum2 * uden1) { 
      unmin = unum1; 
      udmin = uden1; 
    }
    else { 
      unmin = unum2; 
      udmin = uden2; 
    } 
    // Then the emptiness of the intersection implies 
    // that false is the only 
    // possible value. 
    if (lnmax * udmin <= unmin * ldmax) { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    else { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    break; 
  case ARITH_NEQ: 
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (   lnum1 == unum1 && lden1 == uden1
        && lnum2 == unum2 && lden2 == uden2 
        && lnum1 == lnum2 && lden1 == lden2
        ) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
         
    // Now we calculate the intersection of the two interval. 
    if (lnum1 * lden2 > lnum2 * lden2) {
      lnmax = lnum1; 
      ldmax = lden1; 
    } 
    else { 
      lnmax = lnum2; 
      ldmax = lden2; 
    }
    if (unum1 * uden2 < unum2 * uden1) { 
      unmin = unum1; 
      udmin = uden1; 
    }
    else { 
      unmin = unum2; 
      udmin = uden2; 
    } 
    // Then the emptiness of the intersection implies 
    // that false is the only 
    // possible value. 
    if (lnmax * udmin <= unmin * ldmax) { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    else { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    break; 
  case ARITH_LEQ: 
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    if (lnum1 * uden2 > unum2 * lden1) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 
    }
    else if (unum1 * lden2 <= unum2 * lden1) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case ARITH_LESS: 
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum2, &lden2, &unum2, &uden2);
    if (lnum1 * uden2 >= unum2 * lden1) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 
    }
    else if (unum1 * lden2 < unum2 * lden1) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case ARITH_GEQ: 
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum2, &lden2, &unum2, &uden2);
    if (lnum1 * uden2 > unum2 * lden1) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 
    }
    else if (unum1 * lden2 <= unum2 * lden1) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case ARITH_GREATER: 
    rec_get_rational_range(psub->u.arith.rhs_exp, &lnum1, &lden1, &unum1, &uden1);
    rec_get_rational_range(psub->u.arith.lhs_exp, &lnum2, &lden2, &unum2, &uden2);
    if (lnum1 * uden2 >= unum2 * lden1) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 
    }
    else if (unum1 * lden2 < unum2 * lden1) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case EQ: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (lnum1 == 0 && unum1 == 0) {
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (lnum1 > 0 || unum1 < 0) {  
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case NEQ: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (lnum1 == 0 && unum1 == 0) {
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (lnum1 > 0 || unum1 < 0) {  
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case LEQ: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (lnum1 >= 0) {
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (unum1 < 0) {  
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case LESS: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (lnum1 > 0) {
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (unum1 <= 0) {  
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    } 
    break; 
  case GEQ: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (unum1 <= 0) {
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (lnum1 > 0) {  
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }   
    break; 
  case GREATER: 
    if (psub->u.ineq.term_count > 0) { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 
      return; 	
    } 
    rec_get_rational_range(psub->u.ineq.offset, &lnum1, &lden1, &unum1, &uden1);
    // Then we check if truth is the only possibility. 
    // This is the case when both interval are identical to a singular. 
    if (unum1 < 0) {
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (lnum1 >= 0) {  
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
    // There is an intersection. 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }   
    break; 
  case IMPLY: 
    rec_get_rational_range(psub->u.bexp.blist->subexp, 
      &lnum1, &lden1, &unum1, &uden1
    );
    rec_get_rational_range(psub->u.bexp.blist->bnext->subexp, 
      &lnum2, &lden2, &unum2, &uden2
    );
    if (lnum1 == TYPE_TRUE && unum2 == TYPE_FALSE) {
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else if (unum1 == TYPE_FALSE || lnum2 == TYPE_TRUE) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }     	
    break; 
    
  case NOT: 
    rec_get_rational_range(psub->u.bexp.blist->subexp, 
      &lnum1, &lden1, &unum1, &uden1
    );
    *lnptr = unum1; 
    *ldptr = uden1; 
    *unptr = lnum1; 
    *udptr = lden1; 	
    return; 	
    break; 

  case AND: 
    lnmin = TYPE_TRUE; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      rec_get_rational_range(b->subexp, 
        &lnum1, &lden1, &unum1, &uden1
      ); 
      if (unum1 == TYPE_FALSE) { 
        *lnptr = *unptr = TYPE_FALSE; 
        *ldptr = *udptr = 1; 
        return; 	
      } 
      else if (lnum1 == TYPE_FALSE) 
        lnmin = TYPE_FALSE; 
    } 
    if (lnmin == TYPE_TRUE) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }     	
    break; 

  case OR: 
    unmax = TYPE_FALSE; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      rec_get_rational_range(b->subexp, 
        &lnum1, &lden1, &unum1, &uden1
      ); 
      if (lnum1 == TYPE_TRUE) { 
        *lnptr = *unptr = TYPE_TRUE; 
        *ldptr = *udptr = 1; 
        return; 	
      } 
      else if (unum1 == TYPE_TRUE) 
        unmax = TYPE_TRUE; 
    } 
    if (unmax == TYPE_FALSE) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }     	
    break; 

  case FORALL: { 
    int		flag; 
    float 	flb, fub; 
    
    flag = get_integer_range(
      psub->u.qexp.lb_exp, W_PI, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = get_integer_range(
      psub->u.qexp.ub_exp, W_PI, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    lnmin = TYPE_TRUE; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      rec_get_rational_range(psub->u.qexp.child, 
        &lnum1, &lden1, &unum1, &uden1 
      ); 
      if (unum1 == TYPE_FALSE) { 
        *lnptr = *unptr = TYPE_FALSE; 
        *ldptr = *udptr = 1; 
        pop_quantified_value_stack(psub); 
        return; 	
      } 
      else if (lnum1 == TYPE_FALSE) 
        lnmin = TYPE_FALSE; 
    } 
    pop_quantified_value_stack(psub); 
    if (lnmin == TYPE_TRUE) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }     	
    break; 
  }  
  case EXISTS: {
    float	flb, fub; 
    int		flag; 
    
    flag = get_integer_range(
      psub->u.qexp.lb_exp, W_PI, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = get_integer_range(
      psub->u.qexp.ub_exp, W_PI, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      *lnptr = *unptr = TYPE_TRUE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    unmax = TYPE_FALSE; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      rec_get_rational_range(psub->u.qexp.child, 
        &lnum1, &lden1, &unum1, &uden1  
      ); 
      if (lnum1 == TYPE_TRUE) { 
        *lnptr = *unptr = TYPE_TRUE; 
        *ldptr = *udptr = 1; 
        pop_quantified_value_stack(psub); 
        return; 	
      } 
      else if (unum1 == TYPE_TRUE) 
        unmax = TYPE_TRUE; 
    } 
    pop_quantified_value_stack(psub); 
    if (unmax == TYPE_FALSE) { 
      *lnptr = *unptr = TYPE_FALSE; 
      *ldptr = *udptr = 1; 
      return; 	
    } 
    else { 
      *lnptr = TYPE_FALSE; 
      *ldptr = 1; 
      *unptr = TYPE_TRUE; 
      *udptr = 1; 	
      return; 	
    }     	
    break; 
  }
  default:
    fprintf(RED_OUT, "\nParser: Huh ? (parse 3) \n");
    bk(); 
  }

}
/* rec_get_rational_range() */ 






void	get_rational_range(psub, pi, lnptr, ldptr, unptr, udptr)
	struct ps_exp_type	*psub;
	int			pi, *lnptr, *ldptr, *unptr, *udptr;
{
  W_PI = pi;
  rec_get_rational_range(psub, lnptr, ldptr, unptr, udptr);
}
/* get_rational_range() */






void	get_interval_rationals(psub, pi, lnptr, ldptr, rnptr, rdptr)
	struct ps_exp_type	*psub;
	int			pi, *lnptr, *ldptr, *rnptr, *rdptr;
{
  if (psub->u.interval.status & INTERVAL_LEFT_UNBOUNDED) {
    *lnptr = HYBRID_NEG_INFINITY;
    *ldptr = 1;
  }
  else {
    get_rationals(psub->u.interval.lbound_exp, pi, lnptr, ldptr);
    if (psub->u.interval.status & INTERVAL_LEFT_OPEN)
      *lnptr = 2*(*lnptr)-1;
    else
      *lnptr = 2*(*lnptr);
  }
  if (psub->u.interval.status & INTERVAL_RIGHT_UNBOUNDED) {
    *rnptr = HYBRID_POS_INFINITY;
    *rdptr = 1;
  }
  else {
    get_rationals(psub->u.interval.rbound_exp, pi, rnptr, rdptr);
    if (psub->u.interval.status & INTERVAL_RIGHT_OPEN)
      *rnptr = 2*(*rnptr)-1;
    else
      *rnptr = 2*(*rnptr);
  }
}
  /* get_interval_rationals() */








void  	print_linear_parse_action_line(as)
     struct parse_statement_type	*as;
{
  int 	i, numerator, denominator;

  print_parse_subformula(as->u.act.term[0].operand, 
    FLAG_GENERAL_PROCESS_IDENTIFIER
  );
  fprintf (RED_OUT, "=");
  for (i=1; i<as->u.act.term_count; i++) {
    rec_get_rationals(as->u.act.term[i].coeff, &numerator, &denominator);
    numerator = -1 * numerator;
    if (  (as->u.act.lhs->exp_status | as->u.act.rhs_exp->exp_status) 
        & FLAG_LOCAL_IDENTIFIER
        ) {
      if (denominator != 1){
        if (numerator < 0)
          fprintf(RED_OUT, "-(%1d/%1d)@P", abs(numerator), denominator);
        else if(i>1)
          fprintf(RED_OUT, "+(%1d/%1d)@P", numerator, denominator);
        else
	  fprintf(RED_OUT, "%1d/%1d@P", numerator, denominator);
      }
      else if(numerator !=1){
        if (numerator < 0)
          fprintf(RED_OUT, "%1d@P", numerator);
        else if(i>1)
          fprintf(RED_OUT, "+%1d@P", numerator);
        else
     	  fprintf(RED_OUT, "%1d@P", numerator);
      }
    }
    else {
      if (denominator != 1){
        if (numerator < 0)
          fprintf(RED_OUT, "-(%1d/%1d)", abs(numerator), denominator);
        else if(i>1)
          fprintf(RED_OUT, "+(%1d/%1d)", numerator, denominator);
        else
	  fprintf(RED_OUT, "%1d/%1d", numerator, denominator);
      }
      else if(numerator !=1){
        if (numerator < 0)
          fprintf(RED_OUT, "%1d", numerator);
        else if(i>1)
          fprintf(RED_OUT, "+%1d", numerator);
        else
	  fprintf(RED_OUT, "%1d", numerator);
      }
    }
    print_parse_subformula(as->u.act.term[i].operand, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    );
  }
}
/* print_linear_parse_action_line() */



void	print_parse_action_line(as)
     struct parse_statement_type	*as;
{
  struct parse_indirect_type	*pt; 
  
  switch (as->op) {
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "=");
    print_parse_subformula(as->u.act.rhs_exp, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    );
    fprintf(RED_OUT, ";");
    break;

  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
/*
    if (as->type != FLAG_DISCRETE_POLYNOMIAL){
      print_linear_parse_action_line(as);
    }
    else{
*/
    if (   as->u.act.lhs->type == TYPE_DISCRETE
        && as->u.act.lhs->u.atom.var == var_mode
        && as->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER
        && as->u.act.rhs_exp->type == TYPE_MODE_INDEX
        ) { 
      fprintf(RED_OUT, "goto %s", as->u.act.rhs_exp->u.mode_index.mode_name); 
    } 
    else if (   MODE
        && as->u.act.lhs->type == TYPE_DISCRETE
        && as->u.act.lhs->u.atom.var == var_mode
        && as->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER
        && as->u.act.rhs_exp->type == TYPE_CONSTANT
        && as->u.act.rhs_exp->u.value >= 0
        && as->u.act.rhs_exp->u.value < MODE_COUNT 
        ) { 
      fprintf(RED_OUT, "goto %s", MODE[as->u.act.rhs_exp->u.value].name); 
    } 
    else { 
      print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER);
      fprintf(RED_OUT, "=");
      print_parse_subformula(as->u.act.rhs_exp, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      );
    }
    fprintf(RED_OUT, ";");
    break;
    
  case ST_CALL: 
    fprintf(RED_OUT, "call %s to %s;", 
      MODE[as->u.call.call_mode_index].name, 
      MODE[as->u.call.ret_mode_index].name
    ); 
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, "return;"); 
    break; 
    
  case ST_CPLUG: 
    fprintf(RED_OUT, "Cplug %1d %1d;", 
      as->u.cplug.cmod_index, as->u.cplug.cproc_index
    ); 
    break; 
    
  case INCREMENT_BY_CONSTANT:
    print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "++%1d;", as->u.act.rhs_exp->u.value);
    break;
  case DECREMENT_BY_CONSTANT:
    print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "--%1d;", as->u.act.rhs_exp->u.value);
    break;
  }
}
/* print_parse_action_line() */



print_parse_statement_line(st) 
	struct parse_statement_type	*st; 
{ 
  struct parse_statement_link_type	*stl; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case UNCHANGED: 
    fprintf(RED_OUT, ";"); 
    return; 
  case ST_IF: 
    fprintf(RED_OUT, "if ("); 
    print_parse_subformula(st->u.branch.cond, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
    fprintf(RED_OUT, ")"); 
    if (st->u.branch.if_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      fprintf(RED_OUT, "{"); 
      print_parse_statement_line(st->u.branch.if_statement); 
      fprintf(RED_OUT, "}"); 
    }
    else 
      print_parse_statement_line(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      if (st->u.branch.else_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
        fprintf(RED_OUT, "{"); 
        print_parse_statement_line(st->u.branch.else_statement); 
        fprintf(RED_OUT, "}"); 
      }
      else 
        print_parse_statement_line(st->u.branch.else_statement); 
    } 
    break; 
  case ST_WHILE: 
    fprintf(RED_OUT, "while ("); 
    print_parse_subformula(st->u.loop.cond, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
    fprintf(RED_OUT, ")"); 
    if (st->u.loop.statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      fprintf(RED_OUT, "{"); 
      print_parse_statement_line(st->u.loop.statement); 
      fprintf(RED_OUT, "}"); 
    }
    else 
      print_parse_statement_line(st->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (stl = st->u.seq.statement_list; stl; stl = stl->next_parse_statement_link) { 
      print_parse_statement_line(stl->statement); 
    } 
    break; 
  case ST_CALL: 
    fprintf(RED_OUT, "call %s", st->u.call.call_mode_name); 
    if (   st->u.call.ret_mode_index < 0 
        || st->u.call.ret_mode_index >= MODE_COUNT
        ) { 
      fprintf(RED_OUT, " to %s", st->u.call.ret_mode_name); 
    }
    fprintf(RED_OUT, ";"); 
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, "return;"); 
    break; 

  case ST_CPLUG: 
    fprintf(RED_OUT, "Cplug %1d %1d;", 
      st->u.cplug.cmod_index, st->u.cplug.cproc_index
    ); 
    break; 
    
  default: 
    print_parse_action_line(st); 
    break; 	
  } 
}
  /* print_parse_statement_line() */ 





void	print_parse_xtion_string(px)
     struct parse_xtion_type	*px;
{
  int				si, pi;
  struct parse_sync_type	*ps;
  struct parse_assignment_type	*as;
  struct parse_indirect_type	*pt;

  print_parse_subformula(px->trigger_exp, 
    FLAG_GENERAL_PROCESS_IDENTIFIER
  );
  fprintf(RED_OUT, " may "); 
  print_parse_statement_line(px->statement); 
}
/* print_parse_xtion_string() */





void	print_parse_xtion(px, depth)
     struct parse_xtion_type	*px;
     int			depth;
{
  int				si, pi;
  struct parse_xtion_sync_type	*pxs;
  struct parse_indirect_type	*pt;

  for (; depth; depth--)
    fprintf(RED_OUT, "    ");

  if (px==XTION_NULL) { 
    fprintf(RED_OUT, "NULL:"); 	
  } 
  fprintf(RED_OUT, "PXI=%1d:?:%1d[", px->index, px->sync_count);
  for (pxs = px->sync_list; pxs; pxs = pxs->next_parse_xtion_sync) {
    si = pxs->sync_var->index; 
    if (   GSYNC == NULL
	|| GSYNC[si].VAR_INDEX == 0
	|| VAR == NULL
	|| VAR[GSYNC[si].VAR_INDEX].NAME == NULL
	)
      if (pxs->type > 0) 
        fprintf(RED_OUT, "%1d:??:", si);
      else 
        fprintf(RED_OUT, "%1d:!?:", si);
    else
      if (pxs->type > 0) 
	fprintf(RED_OUT, "%1d:?%s:", si, VAR[GSYNC[si].VAR_INDEX].NAME);
      else 
	fprintf(RED_OUT, "%1d:?%s:", si, VAR[GSYNC[si].VAR_INDEX].NAME);
    if (pxs->exp_quantification) 
      print_parse_subformula(pxs->exp_quantification, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
    fprintf(RED_OUT, ";"); 
  }
  fprintf(RED_OUT, "];\n    when (");
  print_parse_subformula(px->trigger_exp, 
    FLAG_GENERAL_PROCESS_IDENTIFIER
  );
  fprintf(RED_OUT, ") may ");
  print_parse_statement_line(px->statement);
  fprintf(RED_OUT, "\n");

}
/* print_parse_xtion() */










char	*itoa(n)
     int	n; 
{
  int	on, len; 
  char	*s;

  if (!n)
    return("0\0"); 
  else {
    on = n; 
    for (len = 0; on; len++)
      on = on / 10; 
    s = (char *) malloc(len + 1); 
    s[len] = '\0'; 
    for (on = n, len--; on; len--) {
      s[len] = on % 10 + '0';
      on = on / 10; 
    }
    return(s);
  }
}
  /* itoa() */









/****************************************************************
 *
 *  Filling in the variable indices of the BDD-structures
 *  assumption:
 *
 *   This procedure is to be defined later. 
 */
int	local_defined(type, pi, loi) 
	int	type, pi, loi; 
{ 
  return(TYPE_TRUE); 
}
  /* local_defined() */ 
  
  
/*******************************************************************
 *
 *  GLOBAL_DECLARE_COUNT: the number of declared global variables. 
 *  GLOBAL_BASIC_COUNT: the number of system overhead, declared variables, 
 */
  
void	variable_alloc() { 
  int	i, pi; 
  
  // Allocate the space. 
  variable_index = (int ***) malloc(57*sizeof(int **));
  variable_index[TYPE_FALSE] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_FALSE][0] = (int *) malloc(sizeof(int));

  variable_index[TYPE_TRUE] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_TRUE][0] = (int *) malloc(sizeof(int));

  for (i = TYPE_TRUE+1; i < TYPE_INDIRECT_PI; i++)
    variable_index[i] = NULL;

  variable_index[TYPE_INDIRECT_PI] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_INDIRECT_PI][0] = (int *) malloc(2*sizeof(int));

  variable_index[TYPE_OP] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_OP][0] = (int *) malloc(sizeof(int));

  variable_index[TYPE_PATH_ENDPOINT] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_PATH_ENDPOINT][0] = (int *) malloc(2*sizeof(int));

  variable_index[TYPE_VALUE] = (int **) malloc(sizeof(int *));
  variable_index[TYPE_VALUE][0] = (int *) malloc(3*sizeof(int));

  variable_index[TYPE_STREAM] = (int **) malloc(sizeof(int *));
  if (GLOBAL_COUNT[TYPE_STREAM]) 
    variable_index[TYPE_STREAM][0] 
    = (int *) malloc(GLOBAL_COUNT[TYPE_STREAM]*sizeof(int)); 
  else
    variable_index[TYPE_STREAM][0] = NULL;

  variable_index[TYPE_SYNCHRONIZER] 
  = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_SYNCHRONIZER]) 
    variable_index[TYPE_SYNCHRONIZER][0] 
    = (int *) malloc(GLOBAL_COUNT[TYPE_SYNCHRONIZER]*sizeof(int)); 
  else
    variable_index[TYPE_SYNCHRONIZER][0] = NULL;

  variable_index[TYPE_DENSE] 
  = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_DENSE]) 
    variable_index[TYPE_DENSE][0] = (int *) malloc(GLOBAL_COUNT[TYPE_DENSE]*sizeof(int)); 
  else
    variable_index[TYPE_DENSE][0] = NULL;

  variable_index[TYPE_FLOAT] 
  = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE) 
    variable_index[TYPE_FLOAT][0] = (int *) malloc(
      (GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE)*sizeof(int)
    ); 
  else
    variable_index[TYPE_FLOAT][0] = NULL;

  variable_index[TYPE_DOUBLE] 
  = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE) 
    variable_index[TYPE_DOUBLE][0] = (int *) malloc(
      (GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE)*sizeof(int)
    ); 
  else
    variable_index[TYPE_DOUBLE][0] = NULL;

/*
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_HYBRID: 
*/
    variable_index[TYPE_HRD] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *)); 
    variable_index[TYPE_HRD][0] = (int *) malloc(sizeof(int)); 
    variable_index[TYPE_HDD] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *)); 
    variable_index[TYPE_HDD][0] = (int *) malloc(sizeof(int)); 
/*
    break; 
  }
*/  
  variable_index[TYPE_DISCRETE] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE) 
    variable_index[TYPE_DISCRETE][0] = (int *) malloc(
      (GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE)*sizeof(int)
    );
  else
    variable_index[TYPE_DISCRETE][0] = NULL;

  variable_index[TYPE_POINTER] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_POINTER]) 
    variable_index[TYPE_POINTER][0] = (int *) malloc(GLOBAL_COUNT[TYPE_POINTER]*sizeof(int)); 
  else
    variable_index[TYPE_POINTER][0] = NULL;

  variable_index[TYPE_CLOCK] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  if (GLOBAL_COUNT[TYPE_CLOCK]) 
    variable_index[TYPE_CLOCK][0] 
    = (int *) malloc(GLOBAL_COUNT[TYPE_CLOCK]*sizeof(int));
  else
    variable_index[TYPE_CLOCK][0] = NULL; 
    
  variable_index[TYPE_LAZY_EXP] = (int **) malloc((1+PROCESS_COUNT)*sizeof(int *));
  variable_index[TYPE_LAZY_EXP][0] = (int *) malloc(sizeof(int));
  
  // Now we decide the variable indices of all the local variables. 
  variable_index[TYPE_XTION_INSTANCE] = ((int **) malloc(PROCESS_COUNT*sizeof(int *)))-1;
  variable_index[TYPE_ACTION_INSTANCE] = ((int **) malloc(PROCESS_COUNT*sizeof(int *)))-1;
  variable_index[TYPE_QSYNC_HOLDER] = ((int **) malloc(PROCESS_COUNT*sizeof(int *)))-1; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    variable_index[TYPE_XTION_INSTANCE][pi] = (int *) malloc(sizeof(int *));

    variable_index[TYPE_ACTION_INSTANCE][pi] = (int *) malloc(sizeof(int *));
    if (GLOBAL_COUNT[TYPE_SYNCHRONIZER]) 
      variable_index[TYPE_SYNCHRONIZER][pi] 
      = (int *) malloc(GLOBAL_COUNT[TYPE_SYNCHRONIZER]*sizeof(int)); 
    else
      variable_index[TYPE_SYNCHRONIZER][pi] = NULL;

    if (LOCAL_COUNT[TYPE_QSYNC_HOLDER]) 
      variable_index[TYPE_QSYNC_HOLDER][pi] 
      = (int *) malloc(LOCAL_COUNT[TYPE_QSYNC_HOLDER]*sizeof(int));
    else
      variable_index[TYPE_QSYNC_HOLDER][pi] = NULL;

    if (LOCAL_COUNT[TYPE_DISCRETE]) 
      variable_index[TYPE_DISCRETE][pi] = (int *) malloc(LOCAL_COUNT[TYPE_DISCRETE]*sizeof(int));
    else
      variable_index[TYPE_DISCRETE][pi] = NULL;

    if (LOCAL_COUNT[TYPE_POINTER]) 
      variable_index[TYPE_POINTER][pi] 
      = (int *) malloc(LOCAL_COUNT[TYPE_POINTER]*sizeof(int));
    else
      variable_index[TYPE_POINTER][pi] = NULL;

    if (LOCAL_COUNT[TYPE_FLOAT]) 
      variable_index[TYPE_FLOAT][pi] = (int *) malloc(LOCAL_COUNT[TYPE_FLOAT]*sizeof(int));
    else
      variable_index[TYPE_FLOAT][pi] = NULL;

    if (LOCAL_COUNT[TYPE_DOUBLE]) 
      variable_index[TYPE_DOUBLE][pi] 
      = (int *) malloc(LOCAL_COUNT[TYPE_DOUBLE]*sizeof(int));
    else
      variable_index[TYPE_DOUBLE][pi] = NULL;


    if (LOCAL_COUNT[TYPE_CLOCK]) 
      variable_index[TYPE_CLOCK][pi] 
      = (int *) malloc(LOCAL_COUNT[TYPE_CLOCK]*sizeof(int));
    else 
      variable_index[TYPE_CLOCK][pi] = NULL;

    if (LOCAL_COUNT[TYPE_DENSE]) 
      variable_index[TYPE_DENSE][pi] 
      = (int *) malloc(LOCAL_COUNT[TYPE_DENSE]*sizeof(int));
    else
      variable_index[TYPE_DENSE][pi] = NULL;
/*
    switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
    case FLAG_SYSTEM_HYBRID: 
*/
      variable_index[TYPE_HRD][pi] = (int *) malloc(sizeof(int)); 
      variable_index[TYPE_HDD][pi] = (int *) malloc(sizeof(int)); 
/*
      break; 
    }
*/
    variable_index[TYPE_LAZY_EXP][pi] = (int *) malloc(sizeof(int));
  } 

  variable_index[TYPE_LAZY_EXP] = (int **) 
    malloc((PROCESS_COUNT+1)*sizeof(int *)); 
  for (i = 0; i<= PROCESS_COUNT; i++) 
    variable_index[TYPE_LAZY_EXP][i] = (int *) malloc(sizeof(int)); 
  
  CLOCK = (int *) malloc(CLOCK_COUNT * sizeof(int)); 
  ZONE = (int **) malloc(CLOCK_COUNT * sizeof(int *)); 
  for (i = 0; i < CLOCK_COUNT; i++) 
    ZONE[i] = (int *) malloc(CLOCK_COUNT *sizeof(int)); 
}
  /* variable_alloc() */ 
  
  
  
  
#define	FLAG_VI_BOTTOM		0 
#define	FLAG_VI_INTERLEAVING	1

int	assign_zone_indices(
	int	gvi, 
	int	cvi, 
	int	flag_pos
	) {
  int	ci, cj; 
  
/*
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED:
  case FLAG_SYSTEM_HYBRID: 
    return(gvi); 
  case FLAG_SYSTEM_TIMED: 
*/
    switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
      & MASK_DISCRETE_DENSE_INTERLEAVING
    ) {
    case FLAG_DISCRETE_DENSE_BOTTOM: 
      if (flag_pos != FLAG_VI_BOTTOM) 
        return(gvi); 
      for (ci = 0; ci < CLOCK_COUNT; ci++) { 
      	for (cj = 0; cj < ci; cj++) { 
      	  ZONE[cj][ci] = gvi++; // for CRD
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	            cj, ci, ZONE[cj][ci]
	            );
	  #endif 
      	  gvi++; // for CDD 
      	  ZONE[ci][cj] = gvi++; // for CRD 
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	            ci, cj, ZONE[ci][cj]
	            );
	  #endif 
      	  gvi++; // for CDD 
      	} 
      	ZONE[ci][ci] = gvi++; // for CRD 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	          ci, ci, ZONE[ci][ci]
	          );
	#endif 
      	gvi++; // for CDD 
      } 
      return(gvi); 
      break;
    case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING:
      switch (flag_pos) { 
      case FLAG_VI_INTERLEAVING: 
      	ZONE[0][ci-1] = gvi++; // for CRD 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "ZONE[0][%1d] = %1d\n",
	          ci-1, ZONE[0][ci-1]
	          );
	#endif 
      	gvi++; // for CDD
      	if (ci > 1) {
      	  ZONE[ci-1][0] = gvi++; // for CRD 
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][0] = %1d\n",
	            ci-1, ZONE[ci-1][0]
	            );
	  #endif 
       	  gvi++; // for CDD
      	} 
      	return(gvi); 
      case FLAG_VI_BOTTOM: 
      	for (ci = 1; ci < CLOCK_COUNT; ci++) { 
      	  for (cj = 1; cj < ci; cj++) { 
      	    ZONE[cj][ci] = gvi++; // for CRD
            #ifdef RED_DEBUG_PARSE_MODE 
              fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	              cj, ci, ZONE[cj][ci]
	              );
	    #endif 
      	    gvi++; // for CDD 
      	    ZONE[ci][cj] = gvi++; // for CRD 
            #ifdef RED_DEBUG_PARSE_MODE 
              fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	              ci, cj, ZONE[ci][cj]
	              );
	    #endif 
      	    gvi++; // for CDD 
      	  } 
      	  ZONE[ci][ci] = gvi++; // for CRD 
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	            ci, ci, ZONE[ci][ci]
	            ); 
	  #endif 
      	  gvi++; // for CDD 
        } 
        return(gvi); 
      }
      break;
    case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING:
      switch (flag_pos) { 
      case FLAG_VI_INTERLEAVING: 
        ci = cvi-1; 
        for (cj = 0; cj < ci; cj++) { 
      	  ZONE[cj][ci] = gvi++; // for CRD
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	            cj, ci, ZONE[cj][ci]
	            ); 
	  #endif 
      	  gvi++; // for CDD 
      	  ZONE[ci][cj] = gvi++; // for CRD 
          #ifdef RED_DEBUG_PARSE_MODE 
            fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	            ci, cj, ZONE[ci][cj]
	            ); 
	  #endif 
      	  gvi++; // for CDD 
        } 
        ZONE[ci][ci] = gvi++; // for CRD 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "ZONE[%1d][%1d] = %1d\n",
	          ci, ci, ZONE[ci][ci]
	          ); 
	#endif 
        gvi++; // for CDD  
        break; 
      case FLAG_VI_BOTTOM: 
        break; 
      }
      return(gvi); 
    }
/*
  } 
*/
}
  /* assign_zone_indices() */ 
  
  
  	
int	OFFSET_AUX_DISCRETE_IN_BOTTOM_ORDERING; 

void	vindex_init_management()
{
  int				gvi, i, pi, oi, pj, oj, ci, cj, cvi, cvj;
  struct parse_variable_type	*pv, *tpv;
  struct ps_memory_link_type	*m; 
  int				offset_discrete, offset_float, offset_double; 

/*
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED:
    GLOBAL_COUNT[TYPE_CLOCK] = 0;
    LOCAL_COUNT[TYPE_CLOCK] = 0;
    for (pv = declare_global_clock_list; pv; ) {
      tpv = pv;
      pv = tpv->next_parse_variable;
      free(tpv);
    }
    declare_global_clock_list = NULL;
    for (pv = declare_local_clock_list; pv; ) {
      tpv = pv;
      pv = tpv->next_parse_variable;
      free(tpv); 
    }
    declare_local_clock_list = NULL;
    break;
  } 
*/
  GLOBAL_SYSTEM_OVERHEAD_COUNT = 12;  /* TYPE_FALSE=0, TYPE_TRUE=1, 
                                       * LHS_PI=2, RHS_PI=3, HF_PSTART=4, 
                                       * HF_PSTOP=5, VI_OP=6, VALUE =7, 
                                       * FLOAT_VALUE=8, DOUBLE_VALUE=9, 
                                       * PROB=10, PROB_WORK=11, 
                                       */ 
  GLOBAL_DECLARE_COUNT
    = 2*GLOBAL_COUNT[TYPE_POINTER] // one for primed, one for umprimed
    + 2*GLOBAL_COUNT[TYPE_DISCRETE]// one for primed, one for umprimed
    + 2*GLOBAL_COUNT[TYPE_FLOAT]// one for primed, one for umprimed
    + 2*GLOBAL_COUNT[TYPE_DOUBLE]// one for primed, one for umprimed
    + 2*GLOBAL_COUNT[TYPE_CLOCK]// one for primed, one for umprimed
    + 2*GLOBAL_COUNT[TYPE_DENSE]// one for primed, one for umprimed
    + GLOBAL_COUNT[TYPE_SYNCHRONIZER]
    + GLOBAL_COUNT[TYPE_STREAM];

  LOCAL_SYSTEM_OVERHEAD_COUNT = 2; /* for TYPE_XTION_INSTANCE, TYPE_ACTION_INSTANCE */

  LOCAL_DECLARE_COUNT
    = 2*LOCAL_COUNT[TYPE_POINTER]// one for primed, one for umprimed
    + 2*LOCAL_COUNT[TYPE_DISCRETE]// one for primed, one for umprimed
    + 2*LOCAL_COUNT[TYPE_FLOAT]// one for primed, one for umprimed
    + 2*LOCAL_COUNT[TYPE_DOUBLE]// one for primed, one for umprimed
    + 2*LOCAL_COUNT[TYPE_CLOCK]// one for primed, one for umprimed
    + 2*LOCAL_COUNT[TYPE_DENSE]// one for primed, one for umprimed
    + GLOBAL_COUNT[TYPE_SYNCHRONIZER]
    + LOCAL_COUNT[TYPE_QSYNC_HOLDER];

  /* Fill in the VAR and CLOCK array. */
  CLOCK_COUNT 
  = 2*GLOBAL_COUNT[TYPE_CLOCK] // one for primed, one for umprimed
  + 2*PROCESS_COUNT*LOCAL_COUNT[TYPE_CLOCK];  // one for primed, one for umprimed 
  CLOCK_INEQUALITY_COUNT = CLOCK_COUNT*CLOCK_COUNT; 

  DENSE_COUNT 
  = 2*GLOBAL_COUNT[TYPE_DENSE] // one for primed, one for umprimed
  + 2*PROCESS_COUNT * LOCAL_COUNT[TYPE_DENSE]; // one for primed, one for umprimed
/*
  if (GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL)
    fprintf(RED_OUT, "CLOCK_COUNT=%1d; CLOCK_INEQUALITY_COUNT = %1d\n",
	    CLOCK_COUNT, CLOCK_INEQUALITY_COUNT
	    );

  fprintf(RED_OUT, "In calculating the variable count\n"); 
  fprintf(RED_OUT, "GLOBAL_SYSTEM_OVERHEAD_COUNT=%1d\n", 
          GLOBAL_SYSTEM_OVERHEAD_COUNT
          ); 
  fprintf(RED_OUT, "GLOBAL_DECLARE_COUNT=%1d\n", 
          GLOBAL_DECLARE_COUNT
          );  
  fprintf(RED_OUT, "PROCESS_COUNT=%1d\n", 
          PROCESS_COUNT
          );  
  fprintf(RED_OUT, "LOCAL_SYSTEM_OVERHEAD_COUNT=%1d\n", 
          LOCAL_SYSTEM_OVERHEAD_COUNT
          );  
  fprintf(RED_OUT, "LOCAL_DECLARE_COUNT=%1d\n", 
          LOCAL_DECLARE_COUNT
          );  
  fprintf(RED_OUT, "CLOCK_INEQUALITY_COUNT=%1d\n", 
          CLOCK_INEQUALITY_COUNT
          );  
*/ 
/* 
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_TIMED:
  case FLAG_SYSTEM_UNTIMED:
*/
    VARIABLE_COUNT
    = GLOBAL_SYSTEM_OVERHEAD_COUNT
    + GLOBAL_DECLARE_COUNT // one for unprimed, one for primed. 
    + 2 /* for global hybrid inequalities */ 
    + 1 /* for TYPE_LAZY_EXP of global */ 
    + LOCAL_COUNT[TYPE_POINTER] * PROCESS_COUNT // for the aux copies of local 
    + LOCAL_COUNT[TYPE_DISCRETE] * PROCESS_COUNT // discretes used in bottom ordering. 
    + LOCAL_COUNT[TYPE_FLOAT] * PROCESS_COUNT // discretes used in bottom ordering. 
    + LOCAL_COUNT[TYPE_DOUBLE] * PROCESS_COUNT // discretes used in bottom ordering. 
    + PROCESS_COUNT * (
        LOCAL_SYSTEM_OVERHEAD_COUNT 
      + LOCAL_DECLARE_COUNT 
      + 2 /* for hybrid inequalities */
      + 1 /* for TYPE_LAZY_EXP of local */
      )
    + 2*CLOCK_INEQUALITY_COUNT // One for CRD, one for CDD 
    + MEMORY_SIZE  /* the memory variable of type discrete 
                      * and its allocation length 
                      */
    ;

    #ifdef RED_DEBUG_PARSE_MODE 
    if (GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL)
      fprintf(RED_OUT, "ALL_CLOCK_TIMING_BOUND = %1d\n", ALL_CLOCK_TIMING_BOUND);
    #endif 
    
    CLOCK_POS_INFINITY = 2*ALL_CLOCK_TIMING_BOUND + 1;
    CLOCK_NEG_INFINITY = -2*ALL_CLOCK_TIMING_BOUND - 1;

//    #ifdef RED_DEBUG_PARSE_MODE 
//    if (GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL)
      fprintf(RED_OUT, 
        "\nCLOCK POSITIVE INFINITY = %1d; CLOCK NEGATIVE INFINITY = %1d\n", 
        CLOCK_POS_INFINITY, CLOCK_NEG_INFINITY
      );
//    #endif 
    
/*
    break; 
    
  case FLAG_SYSTEM_HYBRID:
    VARIABLE_COUNT
    = GLOBAL_SYSTEM_OVERHEAD_COUNT
    + GLOBAL_DECLARE_COUNT
*/
//    + LOCAL_COUNT[TYPE_POINTER] * PROCESS_COUNT // for the aux copies of local 
//    + LOCAL_COUNT[TYPE_DISCRETE] * PROCESS_COUNT // discretes used in bottom ordering. 
//    + LOCAL_COUNT[TYPE_FLOAT] * PROCESS_COUNT // discretes used in bottom ordering. 
//    + LOCAL_COUNT[TYPE_DOUBLE] * PROCESS_COUNT // discretes used in bottom ordering. 
//    + 2 /* for global hybrid */ 
//    + 1 /* for TYPE_LAZY_EXP of global */
//    + PROCESS_COUNT 
//      * (
//           LOCAL_SYSTEM_OVERHEAD_COUNT 
//         + LOCAL_DECLARE_COUNT 
//         + 2 /* for hybrid */
//         + 1 /* for TYPE_LAZY_EXP of local */
//         )
//    + MEMORY_SIZE /* for the memory cells of type discrete 
//                     * and its allocation length 
//                     */
//    ; 
    
//    #ifdef RED_DEBUG_PARSE_MODE 
//    fprintf(RED_OUT, "hybrid hybrid encoding:%x/%x\n", 
//      GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING, 
//      MASK_HYBRID_ENCODING
//    ); 
//    fflush(RED_OUT); 
//    #endif 
//    
//    break; 
    
//  default: 
//    fprintf(RED_OUT, "Error: unrecognized system type.\n"); 
//    exit(0); 
//  } 
  
  FLAG_ANY_VARIABLE = -1 - VARIABLE_COUNT; 
  
  if (GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL)
    fprintf(RED_OUT, "\nVariable count = %1d\n", VARIABLE_COUNT);

  variable_alloc(); 
  
  // We now decide the variable indices of all global variables. 
  variable_index[TYPE_FALSE][0][0] = 0;
  variable_index[TYPE_TRUE][0][0] = 1;
  variable_index[TYPE_INDIRECT_PI][0][0] = 2; /* for LHS_PI */
  variable_index[TYPE_INDIRECT_PI][0][1] = 3; /* for RHS_PI */

  variable_index[TYPE_PATH_ENDPOINT][0][0] = 4; /* for HF_PSTART_VI */
  variable_index[TYPE_PATH_ENDPOINT][0][1] = 5; /* for HF_PSTOP_VI */

  variable_index[TYPE_OP][0][0] = 6; /* for VI_OP */

  gvi = GLOBAL_SYSTEM_OVERHEAD_COUNT; 
  cvi = 0; 
  if (GLOBAL_COUNT[TYPE_STREAM]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_STREAM]; i++) {
      variable_index[TYPE_STREAM][0][i] = gvi++; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "variable_index[TYPE_STREAM=%1d][0][%1d] = %1d\n",
	      TYPE_STREAM, i, variable_index[TYPE_STREAM][0][i]
	      );
      #endif 
    }
  }

  if (GLOBAL_COUNT[TYPE_SYNCHRONIZER]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; i++) {
      variable_index[TYPE_SYNCHRONIZER][0][i] = gvi++; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "variable_index[TYPE_SYNCHRONIZER=%1d][0][%1d] = %1d\n",
	      TYPE_SYNCHRONIZER, i, variable_index[TYPE_SYNCHRONIZER][0][i]
	      );
      #endif 
    }
  }

  if (GLOBAL_COUNT[TYPE_DISCRETE]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_DISCRETE]; i++) {
      variable_index[TYPE_DISCRETE][0][i] = gvi; 
      gvi = gvi + 2; // one for primed, one for umprimed 
      #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_DISCRETE=%1d][0][%1d] = %1d\n",
	      TYPE_DISCRETE, i, variable_index[TYPE_DISCRETE][0][i]
	      );
      #endif 
    }
  }

  if (GLOBAL_COUNT[TYPE_POINTER]) { 
    for (i = 0; i < GLOBAL_COUNT[TYPE_POINTER]; i++) {
      variable_index[TYPE_POINTER][0][i] = gvi; // one for primed, one for umprimed 
      gvi = gvi + 2; // one for primed, one for umprimed 
      #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_POINTER=%1d][0][%1d] = %1d\n",
	      TYPE_POINTER, i, variable_index[TYPE_POINTER][0][i]
	      );
      #endif 
    }
  }
  
  if (GLOBAL_COUNT[TYPE_FLOAT]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_FLOAT]; i++) {
      variable_index[TYPE_FLOAT][0][i] = gvi; 
      gvi = gvi + 2; // one for primed, one for umprimed 
      #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_FLOAT=%1d][0][%1d] = %1d\n",
	  TYPE_FLOAT, i, variable_index[TYPE_FLOAT][0][i]
	);
      #endif 
    }
  }

  if (GLOBAL_COUNT[TYPE_DOUBLE]) { 
    for (i = 0; i < GLOBAL_COUNT[TYPE_DOUBLE]; i++) {
      variable_index[TYPE_DOUBLE][0][i] = gvi; // one for primed, one for umprimed 
      gvi = gvi + 2; // one for primed, one for umprimed 
      #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_DOUBLE=%1d][0][%1d] = %1d\n",
	      TYPE_DOUBLE, i, variable_index[TYPE_DOUBLE][0][i]
	      );
      #endif 
    }
  }
  
  OFFSET_AUX_DISCRETE_IN_BOTTOM_ORDERING = gvi; 
  gvi = gvi 
  + PROCESS_COUNT 
  * (LOCAL_COUNT[TYPE_DISCRETE] + LOCAL_COUNT[TYPE_POINTER]); 

  if (GLOBAL_COUNT[TYPE_DENSE]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_DENSE]; i++) {
      variable_index[TYPE_DENSE][0][i] = gvi;  
      gvi = gvi+2; // one for primed, one for umprimed 
      #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_DENSE=%1d][0][%1d] = %1d\n",
	      TYPE_DENSE, i, variable_index[TYPE_DENSE][0][i]
	      );
      #endif 
    } 
  }

  for (i = 0; i < GLOBAL_COUNT[TYPE_CLOCK]; i++) {
    variable_index[TYPE_CLOCK][0][i] = gvi; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "variable_index[TYPE_CLOCK=%1d][0][%1d] = %1d\n",
	     TYPE_CLOCK, i, variable_index[TYPE_CLOCK][0][i]
	      );
      #endif 
    CLOCK[cvi++] = gvi++; // for the umprimed 
    CLOCK[cvi++] = gvi++; // for the primed. 
    gvi = assign_zone_indices(
      gvi, cvi-1 /* for the umprimed */, 
      FLAG_VI_INTERLEAVING
    ); 
    gvi = assign_zone_indices(
      gvi, cvi /* for the primed*/, 
      FLAG_VI_INTERLEAVING
    ); 
  }

/*
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
      == FLAG_SYSTEM_HYBRID
      ) {
*/
    variable_index[TYPE_HRD][0][0] = gvi++; 
    variable_index[TYPE_HDD][0][0] = gvi++; 
//  } 
  variable_index[TYPE_LAZY_EXP][0][0] = gvi++; 

  // Now we decide the variable indices of all the local variables. 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    variable_index[TYPE_XTION_INSTANCE][pi][0] = gvi++; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "variable_index[TYPE_XTION_INSTANCE=%1d][%1d][0] = %1d\n",
	    TYPE_XTION_INSTANCE, pi, variable_index[TYPE_XTION_INSTANCE][pi][0]
	    ); 
      #endif 

    variable_index[TYPE_ACTION_INSTANCE][pi][0] = gvi++; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "variable_index[TYPE_ACTION_INSTANCE=%1d][%1d][0] = %1d\n",
	    TYPE_ACTION_INSTANCE, pi, variable_index[TYPE_ACTION_INSTANCE][pi][0]
	    );
      #endif 

    if (GLOBAL_COUNT[TYPE_SYNCHRONIZER]) {
      for (i = 0; i < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; i++) {
        variable_index[TYPE_SYNCHRONIZER][pi][i] = gvi++; 
        #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, "variable_index[TYPE_SYNCHRONIZER=%1d][%1d][%1d] = %1d\n",
          TYPE_SYNCHRONIZER, pi, i, variable_index[TYPE_SYNCHRONIZER][pi][i]
        );
        #endif 
      }
    }

    if (LOCAL_COUNT[TYPE_QSYNC_HOLDER]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_QSYNC_HOLDER]; i++) {
	variable_index[TYPE_QSYNC_HOLDER][pi][i] = gvi++; 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_QSYNC_HOLDER=%1d][%1d][%1d] = %1d\n",
	        TYPE_QSYNC_HOLDER, pi, i, variable_index[TYPE_QSYNC_HOLDER][pi][i]
	        );
	#endif 
      }
    }

    if (LOCAL_COUNT[TYPE_DISCRETE]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_DISCRETE]; i++) {
	variable_index[TYPE_DISCRETE][pi][i] = gvi++; // for umprimed 
	gvi++; // for primed 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_DISCRETE=%1d][%1d][%1d] = %1d\n",
	        TYPE_DISCRETE, pi, i, variable_index[TYPE_DISCRETE][pi][i]
	        );
	#endif 
      }
    }

    if (LOCAL_COUNT[TYPE_POINTER]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_POINTER]; i++) {
	variable_index[TYPE_POINTER][pi][i] = gvi++; // for umprimed 
	gvi++; // for primed 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_POINTER=%1d][%1d][%1d] = %1d\n",
	        TYPE_POINTER, pi, i, variable_index[TYPE_POINTER][pi][i]
	        );
	#endif 
      }
    }

    if (LOCAL_COUNT[TYPE_FLOAT]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_FLOAT]; i++) {
	variable_index[TYPE_FLOAT][pi][i] = gvi++; // for umprimed 
	gvi++; // for primed 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_FLOAT=%1d][%1d][%1d] = %1d\n",
	    TYPE_FLOAT, pi, i, variable_index[TYPE_FLOAT][pi][i]
	  );
	#endif 
      }
    }

    if (LOCAL_COUNT[TYPE_DOUBLE]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_DOUBLE]; i++) {
	variable_index[TYPE_DOUBLE][pi][i] = gvi++; // for umprimed 
	gvi++; // for primed 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_DOUBLE=%1d][%1d][%1d] = %1d\n",
	    TYPE_DOUBLE, pi, i, variable_index[TYPE_DOUBLE][pi][i]
	  );
	#endif 
      }
    }

    if (LOCAL_COUNT[TYPE_CLOCK]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_CLOCK]; i++) {
	variable_index[TYPE_CLOCK][pi][i] = gvi; 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_CLOCK=%1d][%1d][%1d] = %1d\n",
	          TYPE_CLOCK, pi, i, variable_index[TYPE_CLOCK][pi][i]
	          );
	#endif 
	
        CLOCK[cvi++] = gvi++; // for the umprimed 
        CLOCK[cvi++] = gvi++; // for the primed. 
        gvi = assign_zone_indices(gvi, cvi-1, FLAG_VI_INTERLEAVING); 
        gvi = assign_zone_indices(gvi, cvi, FLAG_VI_INTERLEAVING); 
      }
    }

    if (LOCAL_COUNT[TYPE_DENSE]) {
      for (i = 0; i < LOCAL_COUNT[TYPE_DENSE]; i++) {
        variable_index[TYPE_DENSE][pi][i] = gvi;  
        gvi = gvi+2; // one for primed, one for umprimed 
        #ifdef RED_DEBUG_PARSE_MODE 
          fprintf(RED_OUT, "variable_index[TYPE_DENSE=%1d][%1d][%1d] = %1d\n",
	          TYPE_DENSE, pi, i, variable_index[TYPE_DENSE][pi][i]
	          );
	#endif 
      } 
    }
    else
      variable_index[TYPE_DENSE][pi] = NULL;
    if (   pi == PROCESS_COUNT 
        && (GLOBAL_COUNT[TYPE_CLOCK] > 0 || LOCAL_COUNT[TYPE_CLOCK] > 0)
        ) { 
      gvi = assign_zone_indices(gvi, cvi, FLAG_VI_BOTTOM); 
    } 
/*
    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
        == FLAG_SYSTEM_HYBRID
        ) {
*/
      variable_index[TYPE_HRD][pi][0] = gvi++; 
      variable_index[TYPE_HDD][pi][0] = gvi++; 
//    }
    variable_index[TYPE_LAZY_EXP][pi][0] = gvi++; 
  } 

  MEMORY_START_VI = gvi; 
  #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "MEMORY_START_VI =  %1d\n", MEMORY_START_VI);
  #endif 

  offset_discrete = GLOBAL_COUNT[TYPE_DISCRETE]; 
  offset_float = GLOBAL_COUNT[TYPE_FLOAT]; 
  offset_double = GLOBAL_COUNT[TYPE_DOUBLE]; 
  for (m = memory_list; m; m = m->next_ps_memory_link) { 
    switch (m->type) { 
    case TYPE_DISCRETE: 
      for (i = 0; i < m->size; i++) { 
        variable_index[TYPE_DISCRETE][0][offset_discrete++] = gvi++;  
      }
      break; 
    case TYPE_FLOAT: 
      for (i = 0; i < m->size; i++) { 
        variable_index[TYPE_FLOAT][0][offset_float++] = gvi++;  
      }
      break; 
    case TYPE_DOUBLE: 
      for (i = 0; i < m->size; i++) { 
        variable_index[TYPE_DOUBLE][0][offset_double++] = gvi++;  
      }
      break; 
    default: 
      bk(0); 
  } }

  VI_TIME = variable_index[TYPE_CLOCK][0][var_time->index]; 
  VI_PROB_DENSE = variable_index[TYPE_DENSE][0][var_prob_dense->index]; 
/*
  exit(0);
*/
}
/* vindex_init_management() */







int	clock_index(pi, offset)
     int	pi, offset;
{
  if (pi)
    return(
        2*GLOBAL_COUNT[TYPE_CLOCK] 
      + 2*(pi-1)*LOCAL_COUNT[TYPE_CLOCK] 
      + 2*offset
    );
  else
    return(2*offset);
}
/* clock_index() */




inline init_var_fields(int vi) { 
  switch (VAR[vi].TYPE) { 
  case TYPE_CLOCK: 
    VAR[vi].U.CLOCK.MODE_RATE_SPEC_COUNT = 0;
    VAR[vi].U.CLOCK.MODE_RATE_SPEC = NULL; 
    break; 
  case TYPE_DENSE: 
    VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT = 0;
    VAR[vi].U.DENSE.MODE_RATE_SPEC = NULL; 
    break; 
  case TYPE_DISCRETE: 
    break; 
  case TYPE_FLOAT: 
    break; 
  case TYPE_DOUBLE: 
    break; 
  }
  VAR[vi].MODE_TIMED_INACTIVE = NULL; 
}
  /* init_var_fields() */ 
  
  
  
print_parse_variables(list)
     struct parse_variable_type	*list;
{
  print_parse_list(declare_global_discrete_list);
  print_parse_list(declare_global_pointer_list);
  print_parse_list(declare_global_clock_list);
  print_parse_list(declare_global_synchronizer_list); 
  print_parse_list(declare_local_discrete_list); 
  print_parse_list(declare_stack_discrete_list); 
  print_parse_list(declare_local_pointer_list);
  print_parse_list(declare_local_clock_list);
  print_parse_list(declare_local_synchronizer_list); 
}
  /* print_parse_variables() */





variable_fillin() {
  struct parse_variable_type	*pv;
  int				si, vi, mvi, ci, cj, civ, pi, v, bi, agvi, 
				rel_clock_index, rel_discrete_index;
  struct ps_memory_link_type	*m; 
  int				offset_discrete, offset_float, offset_double; 
  
/*
  fprintf(RED_OUT, "\nStarting varaible_fillin() \n");
  print_parse_variables();
*/
  vindex_init_management();

  VAR = (struct variable_type *)
    malloc(VARIABLE_COUNT*sizeof(struct variable_type));
  /*
  fprintf(RED_OUT, "\nVARIABLE_COUNT=%1d; size=%1d; VAR=%x\n",
	  VARIABLE_COUNT, sizeof(struct var_declare_type), VAR
	  );
  */
  for (si = 0; si < DEBUG_RED_COUNT; si++)
    var_index_fillin(PARSE_DEBUG_EXP[si]); 
  var_index_fillin(PS_EXP_MODE); 
  var_index_fillin(PS_EXP__SP); 
  if (DEPTH_CALL > 0) 
    var_index_fillin(PS_EXP__RETMODE); 

  VAR[0].TYPE = TYPE_FALSE;
  VAR[0].PROC_INDEX = 0;
  VAR[0].OFFSET = 0;
  VAR[0].STATUS = 0;
  VAR[0].U.DISC.LB = 0;
  VAR[0].U.DISC.UB = 0;
  VAR[0].NAME = "TYPE_FALSE";  
  init_var_fields(0); 
  
  VAR[1].TYPE = TYPE_TRUE;
  VAR[1].PROC_INDEX = 0;
  VAR[1].OFFSET = 0;
  VAR[1].STATUS = 0;
  VAR[1].U.DISC.LB = 0;
  VAR[1].U.DISC.UB = 0;
  VAR[1].NAME = "TYPE_TRUE";
  init_var_fields(1); 

//  LHS_PI = 2;
  VAR[2].TYPE = TYPE_INDIRECT_PI;
  VAR[2].PROC_INDEX = 0;
  VAR[2].OFFSET = 0;
  VAR[2].STATUS = 0;
  VAR[2].U.DISC.LB = 0;
  VAR[2].U.DISC.UB = VARIABLE_COUNT-1;
  VAR[2].NAME = "LHS_PI";
  init_var_fields(2); 

//  RHS_PI = 3;
  VAR[3].TYPE = TYPE_INDIRECT_PI;
  VAR[3].PROC_INDEX = 0;
  VAR[3].OFFSET = 1;
  VAR[3].STATUS = 0;
  VAR[3].U.DISC.LB = 0;
  VAR[3].U.DISC.UB = VARIABLE_COUNT-1;
  VAR[3].NAME = "RHS_PI";
  init_var_fields(3); 

//  HF_PSTART_VI = 4;
  VAR[4].TYPE = TYPE_PATH_ENDPOINT;
  VAR[4].PROC_INDEX = 0;
  VAR[4].OFFSET = 0;
  VAR[4].STATUS = 0;
  VAR[4].U.DISC.LB = 0;
  VAR[4].U.DISC.UB = int_max(CLOCK_COUNT-1, PROCESS_COUNT);
  VAR[4].NAME = "HF_PSTART";
  init_var_fields(4); 

//  HF_PSTOP_VI = 5;
  VAR[5].TYPE = TYPE_PATH_ENDPOINT;
  VAR[5].PROC_INDEX = 0;
  VAR[5].OFFSET = 1;
  VAR[5].STATUS = 0;
  VAR[5].U.DISC.LB = 0;
  VAR[5].U.DISC.UB = int_max(CLOCK_COUNT-1, PROCESS_COUNT);
  VAR[5].NAME = "HF_PSTOP";
  init_var_fields(5); 

//  VI_OP = 6;
  VAR[6].TYPE = TYPE_OP;
  VAR[6].PROC_INDEX = 0;
  VAR[6].OFFSET = 0;
  VAR[6].STATUS = 0;
  VAR[6].U.DISC.LB = 0;
  VAR[6].U.DISC.UB = 100;
  VAR[6].NAME = "VI_OP";
  init_var_fields(6); 

//  VI_VALUE = 7;
  VAR[7].TYPE = TYPE_DISCRETE;
  VAR[7].PROC_INDEX = 0;
  VAR[7].OFFSET = 0;
  VAR[7].STATUS = FLAG_VAR_SYS_GEN;
  VAR[7].U.DISC.LB = INT_MIN;
  VAR[7].U.DISC.UB = INT_MAX;
  VAR[7].NAME = "VALUE";
  init_var_fields(7); 

//  FLOAT_VALUE = 8;
  VAR[8].TYPE = TYPE_FLOAT;
  VAR[8].PROC_INDEX = 0;
  VAR[8].OFFSET = FLAG_VAR_SYS_GEN;
  VAR[8].STATUS = FLAG_VAR_SYS_GEN;
  VAR[8].U.FLT.LB = -1*FLT_MAX;
  VAR[8].U.FLT.UB = FLT_MAX;
  VAR[8].NAME = "FLOAT_VALUE";
  init_var_fields(8); 

//  DOUBLE_VALUE = 9;
  VAR[9].TYPE = TYPE_DOUBLE;
  VAR[9].PROC_INDEX = 0;
  VAR[9].OFFSET = FLAG_VAR_SYS_GEN;
  VAR[9].STATUS = FLAG_VAR_SYS_GEN;
  VAR[9].U.DBLE.LB = -1*DBL_MAX;
  VAR[9].U.DBLE.UB = DBL_MAX;
  VAR[9].NAME = "DOUBLE_VALUE";
  init_var_fields(9); 

//  PROB_VALUE = 10; 
  VAR[10].TYPE = TYPE_FLOAT;
  VAR[10].PROC_INDEX = 0;
  VAR[10].OFFSET = FLAG_VAR_SYS_GEN;
  VAR[10].STATUS = FLAG_VAR_SYS_GEN;
  VAR[10].U.FLT.LB = -1*FLT_MAX;
  VAR[10].U.FLT.UB = FLT_MAX;
  VAR[10].NAME = "PROB";
  init_var_fields(10); 

//  PROB_WORK_VALUE = 11; 
  VAR[11].TYPE = TYPE_FLOAT;
  VAR[11].PROC_INDEX = 0;
  VAR[11].OFFSET = FLAG_VAR_SYS_GEN;
  VAR[11].STATUS = FLAG_VAR_SYS_GEN;
  VAR[11].U.FLT.LB = -1*FLT_MAX;
  VAR[11].U.FLT.UB = FLT_MAX;
  VAR[11].NAME = "PROB_WORK";
  init_var_fields(11); 

  for (pv = declare_global_stream_list;
       pv;
       pv = pv->next_parse_variable
       ) {
    vi = variable_index[TYPE_STREAM][0][pv->index];
    VAR[vi].TYPE = TYPE_STREAM;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.DISC.LB = 0;
    VAR[vi].U.DISC.UB = 1; /* this value is temporally set for event fainress analysis 
		     * used in spec_global(). 
		     * The TYPE_TRUE value will be set in filter_sync_xtion_restriction(). 
		     */
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    VAR[vi].U.STRM.SIZE_BUFFER = 0; 
    VAR[vi].U.STRM.SIZE_DATA = 0; 
    VAR[vi].U.STRM.BUFFER = NULL; 
    VAR[vi].U.STRM.FILE_STREAM = NULL; 
    init_var_fields(vi); 
  }
  
  for (pv = declare_global_synchronizer_list;
       pv;
       pv = pv->next_parse_variable
       ) {
    vi = variable_index[TYPE_SYNCHRONIZER][0][pv->index];
    VAR[vi].U.SYNC.SYNC_INDEX = pv->index;
    VAR[vi].TYPE = TYPE_SYNCHRONIZER;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.SYNC.LB = 0;
    VAR[vi].U.SYNC.UB = 1; /* this value is temporally set for event fainress analysis 
		     * used in spec_global(). 
		     * The TYPE_TRUE value will be set in filter_sync_xtion_restriction(). 
		     */
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  rel_clock_index = 0;
  rel_discrete_index = 0;

  for (pv = declare_global_discrete_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_DISCRETE][0][pv->index];
    VAR[vi].TYPE = TYPE_DISCRETE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    if (pv->status & FLAG_RANGE_ALL_VI) { 
      VAR[vi].U.DISC.LB = 0;
      VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
    }
    else { 
      VAR[vi].U.DISC.LB = pv->u.disc.lb;
      VAR[vi].U.DISC.UB = pv->u.disc.ub;
    }
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].TYPE = TYPE_DISCRETE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    if (pv->status & FLAG_RANGE_ALL_VI) { 
      VAR[vi].U.DISC.LB = 0;
      VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
    }
    else { 
      VAR[vi].U.DISC.LB = pv->u.disc.lb;
      VAR[vi].U.DISC.UB = pv->u.disc.ub;
    }
    VAR[vi].NAME = (char *) malloc(3+strlen(pv->name));
    sprintf(VAR[vi].NAME, "%s'", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  for (pv = declare_global_float_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_FLOAT][0][pv->index];
    VAR[vi].TYPE = TYPE_FLOAT;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].U.FLT.LB = -1*FLT_MAX; 
    VAR[vi].U.FLT.UB = FLT_MAX; 
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].TYPE = TYPE_FLOAT;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].NAME = (char *) malloc(3+strlen(pv->name));
    sprintf(VAR[vi].NAME, "%s'", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].U.FLT.LB = -1*FLT_MAX; 
    VAR[vi].U.FLT.UB = FLT_MAX; 
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  for (pv = declare_global_double_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_DOUBLE][0][pv->index];
    VAR[vi].TYPE = TYPE_DOUBLE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].U.DBLE.LB = -1*DBL_MAX; 
    VAR[vi].U.DBLE.UB = DBL_MAX; 
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].TYPE = TYPE_DOUBLE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].NAME = (char *) malloc(3+strlen(pv->name));
    sprintf(VAR[vi].NAME, "%s'", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].U.DBLE.LB = -1*DBL_MAX; 
    VAR[vi].U.DBLE.UB = DBL_MAX; 
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  // Cross reference setup for the stream variable 
  // and its head position variable. 
  for (pv = declare_global_pointer_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_POINTER][0][pv->index];
    VAR[vi].TYPE = TYPE_POINTER;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.DISC.LB = pv->u.disc.lb /* or FLAG_POINTER_DIRTY */;
    VAR[vi].U.DISC.UB = pv->u.disc.ub;
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].TYPE = TYPE_POINTER;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.DISC.LB = 0 /* FLAG_POINTER_DIRTY*/;
    VAR[vi].U.DISC.UB = PROCESS_COUNT;
    VAR[vi].NAME = (char *) malloc(3+strlen(pv->name));
    sprintf(VAR[vi].NAME, "%s'", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  for (pv = declare_global_clock_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_CLOCK][0][pv->index];
    VAR[vi].U.CLOCK.CLOCK_INDEX = clock_index(0, pv->index);

    VAR[vi].TYPE = TYPE_CLOCK;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.CLOCK.LB = 0;
    VAR[vi].U.CLOCK.UB = CLOCK_COUNT-1;
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].U.CLOCK.CLOCK_INDEX = VAR[vi-1].U.CLOCK.CLOCK_INDEX+1;
    VAR[vi].TYPE = TYPE_CLOCK;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
    VAR[vi].U.CLOCK.LB = 0;
    VAR[vi].U.CLOCK.UB = CLOCK_COUNT-1;
    VAR[vi].NAME = (char *) malloc(3+strlen(pv->name));
    sprintf(VAR[vi].NAME, "%s'", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

  for (pv = declare_global_dense_list; pv; pv = pv->next_parse_variable) {
    vi = variable_index[TYPE_DENSE][0][pv->index];
    VAR[vi].TYPE = TYPE_DENSE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
//    VAR[vi].U.DNS.LB = 0;
//    VAR[vi].U.DNS.UB = CLOCK_COUNT-1;
    VAR[vi].NAME = pv->name;
    VAR[vi].STATUS = pv->status;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    VAR[vi].PRIMED_VI = ++vi; 
    VAR[vi].UMPRIMED_VI = vi-1; 
    VAR[vi].TYPE = TYPE_DENSE;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = pv->index;
//    VAR[vi].U.DNS.LB = 0;
//    VAR[vi].U.DNS.UB = CLOCK_COUNT-1;
    VAR[vi].NAME = (char *) malloc(4+strlen(pv->name));
    sprintf(VAR[vi].NAME, "d.%s", pv->name);
    VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
  }

//  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    vi = variable_index[TYPE_HRD][0][0];
    VAR[vi].TYPE = TYPE_HRD;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = 0;
    VAR[vi].STATUS = 0;
    VAR[vi].U.HRD.LB = HYBRID_NEG_INFINITY;
    VAR[vi].U.HRD.UB = HYBRID_POS_INFINITY;
    VAR[vi].NAME = "HYBRID-0";
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 

    vi = variable_index[TYPE_HDD][0][0];
    VAR[vi].TYPE = TYPE_HDD;
    VAR[vi].PROC_INDEX = 0;
    VAR[vi].OFFSET = 0;
    VAR[vi].STATUS = 0;
    VAR[vi].U.HRD.LB = HYBRID_NEG_INFINITY;
    VAR[vi].U.HRD.UB = HYBRID_POS_INFINITY;
    VAR[vi].NAME = "HYBRID FILTER-0";
    VAR[vi].RED_ACTIVE = NULL;
    init_var_fields(vi); 
//  }

  agvi = OFFSET_AUX_DISCRETE_IN_BOTTOM_ORDERING; 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\naux global variable index starts from %1d.\n", agvi); 
  #endif 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    vi = variable_index[TYPE_XTION_INSTANCE][pi][0];
    VAR[vi].TYPE = TYPE_XTION_INSTANCE;
    VAR[vi].PROC_INDEX = pi;
    VAR[vi].OFFSET = 0; 
    VAR[vi].NAME = (char *) malloc(intlen(pi)+5);
    sprintf(VAR[vi].NAME, "XI-%1d", pi);
    VAR[vi].U.DISC.LB = 0;
    VAR[vi].U.DISC.UB = declare_xtion_count-1;
    VAR[vi].STATUS = 0;
    init_var_fields(vi); 

    vi = variable_index[TYPE_ACTION_INSTANCE][pi][0];
    VAR[vi].TYPE = TYPE_ACTION_INSTANCE;
    VAR[vi].PROC_INDEX = pi;
    VAR[vi].OFFSET = 0;
    VAR[vi].NAME = (char *) malloc(intlen(pi)+5);
    sprintf(VAR[vi].NAME, "AI-%1d", pi);
    VAR[vi].U.DISC.LB = 0;
    if (PROCESS_COUNT < XTION_COUNT) 
      VAR[vi].U.DISC.UB = XTION_COUNT;
    else 
      VAR[vi].U.DISC.UB = PROCESS_COUNT; 
    VAR[vi].STATUS = 0;
    init_var_fields(vi); 

    for (pv = declare_global_synchronizer_list;
         pv;
         pv = pv->next_parse_variable
         ) {
      vi = variable_index[TYPE_SYNCHRONIZER][pi][pv->index];
      VAR[vi].U.SYNC.SYNC_INDEX = pv->index;
      VAR[vi].TYPE = TYPE_SYNCHRONIZER;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.DISC.LB = 0;
      VAR[vi].U.DISC.UB = 1; /* this value is temporally set for event fainress analysis 
		     * used in spec_global(). 
		     * The TYPE_TRUE value will be set in filter_sync_xtion_restriction(). 
		     */
      VAR[vi].NAME = malloc(strlen(pv->name)+2/*@(*/+intlen(pi)+2/*)*/);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi); 
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
    }

    for (pv = declare_local_qsholder_list; pv; pv = pv->next_parse_variable) { 
      vi = variable_index[TYPE_QSYNC_HOLDER][pi][pv->index];
      VAR[vi].TYPE = TYPE_QSYNC_HOLDER;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.DISC.LB = 0;
      VAR[vi].U.DISC.UB = VARIABLE_COUNT;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "\nLOCAL_COUNT[TYPE_QSYNC_HOLDER=%1d]=%1d\n", 
        TYPE_QSYNC_HOLDER, LOCAL_COUNT[TYPE_QSYNC_HOLDER]
      ); 
      fprintf(RED_OUT, "\nqsync holder vi=%1d:%s, pi=%1d, pv->index=%1d\n", 
        vi, VAR[vi].NAME, pi, pv->index
      ); 
      #endif 
      
    } 
    for (pv = declare_local_discrete_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_DISCRETE][pi][pv->index];
      VAR[vi].TYPE = TYPE_DISCRETE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      if (pv->status & FLAG_RANGE_ALL_VI) { 
        VAR[vi].U.DISC.LB = 0;
        VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
      }
      else { 
        VAR[vi].U.DISC.LB = pv->u.disc.lb;
        VAR[vi].U.DISC.UB = pv->u.disc.ub;
      }
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL; 
      VAR[vi].U.DISC.AUX_VI_BOTTOM_ORDERING = agvi; 
      init_var_fields(vi); 

      // Now fill in the auxiliary discrete variable for bottom ordering. 
      VAR[agvi].TYPE = TYPE_DISCRETE;
      VAR[agvi].PROC_INDEX = 0;
      VAR[agvi].OFFSET = pv->index; 
      VAR[agvi].U.DISC.LB = pv->u.disc.lb;
      VAR[agvi].U.DISC.UB = pv->u.disc.ub;
      VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+11);
      sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d)", pv->name, pi);
      VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
      VAR[agvi].RED_ACTIVE = NULL;
      VAR[agvi].U.DISC.ORIG_VI_BOTTOM_ORDERING = vi; 
      init_var_fields(agvi); 
      agvi++; 

      // Now fill in the primed variable. 
      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].TYPE = TYPE_DISCRETE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      if (pv->status & FLAG_RANGE_ALL_VI) { 
        VAR[vi].U.DISC.LB = 0;
        VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
      }
      else { 
        VAR[vi].U.DISC.LB = pv->u.disc.lb;
        VAR[vi].U.DISC.UB = pv->u.disc.ub;
      }
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+5);
      sprintf(VAR[vi].NAME, "%s'@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
    }

    for (pv = declare_local_float_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_FLOAT][pi][pv->index];
      VAR[vi].TYPE = TYPE_FLOAT	;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL; 
      VAR[vi].U.FLT.AUX_VI_BOTTOM_ORDERING = agvi; 
      VAR[vi].U.FLT.LB = -1*FLT_MAX;
      VAR[vi].U.FLT.UB = FLT_MAX;
      init_var_fields(vi); 

      // Now fill in the auxiliary float variable for bottom ordering. 
      VAR[agvi].TYPE = TYPE_FLOAT;
      VAR[agvi].PROC_INDEX = 0;
      VAR[agvi].OFFSET = pv->index; 
      VAR[agvi].U.FLT.LB = -1*FLT_MAX;
      VAR[agvi].U.FLT.UB = FLT_MAX;
      VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+11);
      sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d)", pv->name, pi);
      VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
      VAR[agvi].RED_ACTIVE = NULL;
      VAR[agvi].U.FLT.ORIG_VI_BOTTOM_ORDERING = vi; 
      init_var_fields(agvi); 
      agvi++; 

      // Now fill in the primed variable. 
      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].TYPE = TYPE_FLOAT;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+5);
      sprintf(VAR[vi].NAME, "%s'@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      VAR[vi].U.FLT.LB = -1*FLT_MAX;
      VAR[vi].U.FLT.UB = FLT_MAX;
      init_var_fields(vi); 
    }

    for (pv = declare_local_double_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_DOUBLE][pi][pv->index];
      VAR[vi].TYPE = TYPE_DOUBLE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL; 
      VAR[vi].U.DBLE.AUX_VI_BOTTOM_ORDERING = agvi; 
      VAR[vi].U.DBLE.LB = -1*DBL_MAX;
      VAR[vi].U.DBLE.UB = DBL_MAX;
      init_var_fields(vi); 

      // Now fill in the auxiliary double variable for bottom ordering. 
      VAR[agvi].TYPE = TYPE_DOUBLE;
      VAR[agvi].PROC_INDEX = 0;
      VAR[agvi].OFFSET = pv->index; 
      VAR[agvi].U.DBLE.LB = -1*DBL_MAX;
      VAR[agvi].U.DBLE.UB = DBL_MAX;
      VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+11);
      sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d)", pv->name, pi);
      VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
      VAR[agvi].RED_ACTIVE = NULL;
      VAR[agvi].U.DBLE.ORIG_VI_BOTTOM_ORDERING = vi; 
      init_var_fields(agvi); 
      agvi++; 

      // Now fill in the primed variable. 
      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].TYPE = TYPE_DOUBLE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+5);
      sprintf(VAR[vi].NAME, "%s'@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      VAR[vi].U.DBLE.LB = -1*DBL_MAX;
      VAR[vi].U.DBLE.UB = DBL_MAX;
      init_var_fields(vi); 
    }

    for (si = 0; si < DEPTH_CALL; si++) { 
      for (pv = declare_stack_discrete_list; 
           pv; 
           pv = pv->next_parse_variable
           ) { 
        vi = variable_index[TYPE_DISCRETE][pi][pv->index+si*HEIGHT_STACK_FRAME];
        VAR[vi].TYPE = TYPE_DISCRETE;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        if (pv->status & FLAG_RANGE_ALL_VI) { 
          VAR[vi].U.DISC.LB = 0;
          VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
        }
        else { 
          VAR[vi].U.DISC.LB = pv->u.disc.lb;
          VAR[vi].U.DISC.UB = pv->u.disc.ub;
        }
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+5);
        sprintf(VAR[vi].NAME, "%s@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status;
        VAR[vi].RED_ACTIVE = NULL; 
        VAR[vi].U.DISC.AUX_VI_BOTTOM_ORDERING = agvi; 
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "==========================================\n"); 
        fprintf(RED_OUT, "filling in vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/

        // Now fill in the auxiliary discrete variable for bottom ordering. 
        VAR[agvi].TYPE = TYPE_DISCRETE;
        VAR[agvi].PROC_INDEX = 0;
        VAR[agvi].OFFSET = pv->index; 
        VAR[agvi].U.DISC.LB = pv->u.disc.lb;
        VAR[agvi].U.DISC.UB = pv->u.disc.ub;
        VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+12);
        sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d,%1d)", pv->name, pi, si);
        VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
        VAR[agvi].RED_ACTIVE = NULL;
        VAR[agvi].U.DISC.ORIG_VI_BOTTOM_ORDERING = vi; 
        init_var_fields(agvi); 
/*
        fprintf(RED_OUT, "filling in agvi=%1d:%s\n", agvi, VAR[agvi].NAME); 
*/
        agvi++; 

        // Now fill in the primed variable. 
        VAR[vi].PRIMED_VI = ++vi; 
        VAR[vi].UMPRIMED_VI = vi-1; 
        VAR[vi].TYPE = TYPE_DISCRETE;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        if (pv->status & FLAG_RANGE_ALL_VI) { 
          VAR[vi].U.DISC.LB = 0;
          VAR[vi].U.DISC.UB = VARIABLE_COUNT-1;
        }
        else { 
          VAR[vi].U.DISC.LB = pv->u.disc.lb;
          VAR[vi].U.DISC.UB = pv->u.disc.ub;
        }
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+6);
        sprintf(VAR[vi].NAME, "%s'@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
        VAR[vi].RED_ACTIVE = NULL;
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "filling in primed vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/
      }

      for (pv = declare_stack_float_list; 
           pv; 
           pv = pv->next_parse_variable
           ) { 
        vi = variable_index[TYPE_FLOAT][pi][pv->index+si*HEIGHT_STACK_FRAME];
        VAR[vi].TYPE = TYPE_FLOAT;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+5);
        sprintf(VAR[vi].NAME, "%s@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status;
        VAR[vi].RED_ACTIVE = NULL; 
        VAR[vi].U.FLT.AUX_VI_BOTTOM_ORDERING = agvi; 
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "==========================================\n"); 
        fprintf(RED_OUT, "filling in vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/

        // Now fill in the auxiliary discrete variable for bottom ordering. 
        VAR[agvi].TYPE = TYPE_FLOAT;
        VAR[agvi].PROC_INDEX = 0;
        VAR[agvi].OFFSET = pv->index; 
        VAR[agvi].U.FLT.LB = pv->u.flt.lb;
        VAR[agvi].U.FLT.UB = pv->u.flt.ub;
        VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+12);
        sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d,%1d)", pv->name, pi, si);
        VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
        VAR[agvi].RED_ACTIVE = NULL;
        VAR[agvi].U.FLT.ORIG_VI_BOTTOM_ORDERING = vi; 
        init_var_fields(agvi); 
/*
        fprintf(RED_OUT, "filling in agvi=%1d:%s\n", agvi, VAR[agvi].NAME); 
*/
        agvi++; 

        // Now fill in the primed variable. 
        VAR[vi].PRIMED_VI = ++vi; 
        VAR[vi].UMPRIMED_VI = vi-1; 
        VAR[vi].TYPE = TYPE_FLOAT;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+6);
        sprintf(VAR[vi].NAME, "%s'@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
        VAR[vi].RED_ACTIVE = NULL;
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "filling in primed vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/
      }
      for (pv = declare_stack_double_list; 
           pv; 
           pv = pv->next_parse_variable
           ) { 
        vi = variable_index[TYPE_DOUBLE][pi][pv->index+si*HEIGHT_STACK_FRAME];
        VAR[vi].TYPE = TYPE_DOUBLE;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+5);
        sprintf(VAR[vi].NAME, "%s@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status;
        VAR[vi].RED_ACTIVE = NULL; 
        VAR[vi].U.DBLE.AUX_VI_BOTTOM_ORDERING = agvi; 
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "==========================================\n"); 
        fprintf(RED_OUT, "filling in vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/

        // Now fill in the auxiliary discrete variable for bottom ordering. 
        VAR[agvi].TYPE = TYPE_DOUBLE;
        VAR[agvi].PROC_INDEX = 0;
        VAR[agvi].OFFSET = pv->index; 
        VAR[agvi].U.DBLE.LB = pv->u.dble.lb;
        VAR[agvi].U.DBLE.UB = pv->u.dble.ub;
        VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+12);
        sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d,%1d)", pv->name, pi, si);
        VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
        VAR[agvi].RED_ACTIVE = NULL;
        VAR[agvi].U.DBLE.ORIG_VI_BOTTOM_ORDERING = vi; 
        init_var_fields(agvi); 
/*
        fprintf(RED_OUT, "filling in agvi=%1d:%s\n", agvi, VAR[agvi].NAME); 
*/
        agvi++; 

        // Now fill in the primed variable. 
        VAR[vi].PRIMED_VI = ++vi; 
        VAR[vi].UMPRIMED_VI = vi-1; 
        VAR[vi].TYPE = TYPE_DOUBLE;
        VAR[vi].PROC_INDEX = pi;
        VAR[vi].OFFSET = pv->index+si*HEIGHT_STACK_FRAME;
        VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+intlen(si)+6);
        sprintf(VAR[vi].NAME, "%s'@(%1d,%1d)", pv->name, pi, si);
        VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
        VAR[vi].RED_ACTIVE = NULL;
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "filling in primed vi=%1d:%s\n", vi, VAR[vi].NAME); 
*/
      }
    }

    for (pv = declare_local_pointer_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_POINTER][pi][pv->index];
      VAR[vi].TYPE = TYPE_POINTER;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.DISC.LB = pv->u.disc.lb /* FLAG_POINTER_DIRTY */;
      VAR[vi].U.DISC.UB = pv->u.disc.ub;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL;
      VAR[vi].U.DISC.AUX_VI_BOTTOM_ORDERING = agvi; 
      init_var_fields(vi); 

      // Now fill in the auxiliary discrete variable for bottom ordering. 
      VAR[agvi].TYPE = TYPE_POINTER;
      VAR[agvi].PROC_INDEX = 0;
      VAR[agvi].OFFSET = pv->index; 
      VAR[agvi].U.DISC.LB = pv->u.disc.lb;
      VAR[agvi].U.DISC.UB = pv->u.disc.ub;
      VAR[agvi].NAME = malloc(strlen(pv->name)+intlen(pi)+11);
      sprintf(VAR[agvi].NAME, "%s_aux_bo@(%1d)", pv->name, pi);
      VAR[agvi].STATUS = pv->status | FLAG_VAR_AUX_BOTTOM_ORDERING;
      VAR[agvi].RED_ACTIVE = NULL;
      VAR[agvi].U.DISC.ORIG_VI_BOTTOM_ORDERING = vi; 
      init_var_fields(agvi); 
      agvi++; 

      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].TYPE = TYPE_POINTER;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.DISC.LB = 0 /* FLAG_POINTER_DIRTY */;
      VAR[vi].U.DISC.UB = PROCESS_COUNT;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+5);
      sprintf(VAR[vi].NAME, "%s'@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
    }

    for (pv = declare_local_clock_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_CLOCK][pi][pv->index];
      VAR[vi].U.CLOCK.CLOCK_INDEX = clock_index(pi, pv->index);

      VAR[vi].TYPE = TYPE_CLOCK;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.CLOCK.LB = 0;
      VAR[vi].U.CLOCK.UB = CLOCK_COUNT-1;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 

      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].U.CLOCK.CLOCK_INDEX = VAR[vi-1].U.CLOCK.CLOCK_INDEX+1;
      VAR[vi].TYPE = TYPE_CLOCK;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
      VAR[vi].U.CLOCK.LB = 0;
      VAR[vi].U.CLOCK.UB = CLOCK_COUNT-1;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+5);
      sprintf(VAR[vi].NAME, "%s'@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
    }

    for (pv = declare_local_dense_list; pv; pv = pv->next_parse_variable) {
      vi = variable_index[TYPE_DENSE][pi][pv->index];
      VAR[vi].TYPE = TYPE_DENSE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
//      VAR[vi].U.DENSE.LB = 0;
//      VAR[vi].U.DENSE.UB = CLOCK_COUNT-1;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+4);
      sprintf(VAR[vi].NAME, "%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 

      VAR[vi].PRIMED_VI = ++vi; 
      VAR[vi].UMPRIMED_VI = vi-1; 
      VAR[vi].TYPE = TYPE_DENSE;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].OFFSET = pv->index;
//      VAR[vi].U.DENSE.LB = 0;
//      VAR[vi].U.DENSE.UB = CLOCK_COUNT-1;
      VAR[vi].NAME = malloc(strlen(pv->name)+intlen(pi)+6);
      sprintf(VAR[vi].NAME, "d.%s@(%1d)", pv->name, pi);
      VAR[vi].STATUS = pv->status | FLAG_VAR_PRIMED;
      VAR[vi].RED_ACTIVE = NULL;
      init_var_fields(vi); 
    }

//    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
      vi = variable_index[TYPE_HRD][pi][0];
      VAR[vi].TYPE = TYPE_HRD;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].STATUS = FLAG_DENSE | FLAG_HYBRID; 
      VAR[vi].OFFSET = 0;
      VAR[vi].NAME = (char *) malloc(intlen(pi)+9);
      sprintf(VAR[vi].NAME, "HYBRID-%1d", pi);
      VAR[vi].U.HRD.LB = HYBRID_NEG_INFINITY;
      VAR[vi].U.HRD.UB = HYBRID_POS_INFINITY;
      VAR[vi].RED_ACTIVE = NULL;
      VAR[vi].U.HRD.CORRESPONDING_HDD_VI = variable_index[TYPE_HDD][pi][0]; 
      init_var_fields(vi); 

      vi = variable_index[TYPE_HDD][pi][0];
      VAR[vi].TYPE = TYPE_HDD;
      VAR[vi].PROC_INDEX = pi;
      VAR[vi].STATUS = FLAG_DENSE | FLAG_HYBRID; 
      VAR[vi].OFFSET = 0;
      VAR[vi].NAME = (char *) malloc(intlen(pi)+16);
      sprintf(VAR[vi].NAME, "HYBRID FILTER-%1d", pi);
      VAR[vi].U.HDD.LB = HYBRID_NEG_INFINITY;
      VAR[vi].U.HDD.UB = HYBRID_POS_INFINITY;
      VAR[vi].RED_ACTIVE = NULL;
      VAR[vi].U.HDD.CORRESPONDING_HRD_VI = variable_index[TYPE_HRD][pi][0]; 
      init_var_fields(vi); 
//    }
  }

//  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED) {
    for (ci = 0; ci < CLOCK_COUNT; ci++) {
      for (cj = 0; cj < CLOCK_COUNT; cj++) {
        vi = ZONE[ci][cj];
/*
        fprintf(RED_OUT, "caught one ZONE[ci=%1d][cj=%1d]=vi:%1d\n", ci, cj, vi);
*/
        VAR[vi].TYPE = TYPE_CRD;
        VAR[vi].PROC_INDEX = 0;
        VAR[vi].STATUS = FLAG_CLOCK; 
        VAR[vi].OFFSET = 0;
        VAR[vi].U.CRD.CLOCK1 = ci;
        VAR[vi].U.CRD.CLOCK2 = cj;
        VAR[vi].U.CRD.LB = CLOCK_NEG_INFINITY;
        VAR[vi].U.CRD.UB = CLOCK_POS_INFINITY;
        VAR[vi].U.CRD.CORRESPONDING_CDD_VI = vi+1; 
        VAR[vi].RED_ACTIVE = NULL;
        VAR[vi].U.CRD.CONVERSE_CRD_VI = ZONE[cj][ci];  // an acronym for SPEC_INDE
        VAR[vi].NAME 
        = malloc( strlen(VAR[CLOCK[ci]].NAME)
        	 +strlen(VAR[CLOCK[cj]].NAME)+5
        	 ); 
        init_var_fields(vi); 
/*
        fprintf(RED_OUT, "space for ineq=%1d of [clock%1d:%1d:%s]-[clock%1d:%1d:%s] of %1d bytes.\n", 
        	vi, 
        	ci, CLOCK[ci], VAR[CLOCK[ci]].NAME, 
        	cj, CLOCK[cj], VAR[CLOCK[cj]].NAME, 
        	strlen(VAR[CLOCK[ci]].NAME)+strlen(VAR[CLOCK[cj]].NAME)+5
        	); 
*/
        switch (ci) { 
        case 0:
	  switch (cj) { 
	  case 0:
	    sprintf(VAR[vi].NAME, "(0-0)"); 
	    break; 
	  case NEG_DELTA: 
            sprintf(VAR[vi].NAME, "delta");
            break; 
	  case NEG_DELTA+1: 
            sprintf(VAR[vi].NAME, "delta'");
            break; 
          case NEG_DELTAP: 
	    sprintf(VAR[vi].NAME, "deltap");	  
	    break; 
          case NEG_DELTAP+1: 
	    sprintf(VAR[vi].NAME, "deltap'");	  
	    break; 
	  default: 
	    sprintf(VAR[vi].NAME, "-%s", VAR[CLOCK[cj]].NAME);
	    break; 
	  }
	  break; 
	default: 
	  switch (cj) { 
	  case 0:
	    sprintf(VAR[vi].NAME, "%s", VAR[CLOCK[ci]].NAME); 
	    break; 
	  case NEG_DELTA: 
            sprintf(VAR[vi].NAME, "%s+delta", VAR[CLOCK[ci]].NAME);
            break; 
	  case NEG_DELTA+1: 
            sprintf(VAR[vi].NAME, "%s+delta'", VAR[CLOCK[ci]].NAME);
            break; 
          case NEG_DELTAP: 
	    sprintf(VAR[vi].NAME, "%s+deltap", VAR[CLOCK[ci]].NAME);	  
	    break; 
          case NEG_DELTAP+1: 
	    sprintf(VAR[vi].NAME, "%s+deltap'", VAR[CLOCK[ci]].NAME);	  
	    break; 
	  default: 
	    sprintf(VAR[vi].NAME, "%s-%s", VAR[CLOCK[ci]].NAME, VAR[CLOCK[cj]].NAME);
	    break; 
	  }
	  break; 
        }

        vi = 1+vi;
        VAR[vi].TYPE = TYPE_CDD;
        VAR[vi].PROC_INDEX = 0;
        VAR[vi].STATUS = FLAG_CLOCK; 
        VAR[vi].OFFSET = 0;
        VAR[vi].U.CDD.CLOCK1 = ci;
        VAR[vi].U.CDD.CLOCK2 = cj;
        VAR[vi].U.CDD.LB = CLOCK_NEG_INFINITY;
        VAR[vi].U.CDD.UB = CLOCK_POS_INFINITY;
        VAR[vi].U.CDD.CORRESPONDING_CRD_VI = vi-1; 
        VAR[vi].U.CDD.CONVERSE_CDD_VI = ZONE[cj][ci]+1; // an acronym for SPEC_INDEX
        VAR[vi].NAME = VAR[vi-1].NAME; 

        VAR[vi].RED_ACTIVE = NULL;
        init_var_fields(vi); 
      }
    }
//  }
  offset_discrete = GLOBAL_COUNT[TYPE_DISCRETE]; 
  offset_float = GLOBAL_COUNT[TYPE_FLOAT]; 
  offset_double = GLOBAL_COUNT[TYPE_DOUBLE]; 
  for (m = memory_list, vi = MEMORY_START_VI; 
       m; 
       m = m->next_ps_memory_link 
       ) { 
    switch (m->type) { 
    case TYPE_DISCRETE: 
      for (v = 0; v < m->size; v++, vi++) { 
        VAR[vi].TYPE = m->type; 
        VAR[vi].PROC_INDEX = 0; 
        VAR[vi].OFFSET = offset_discrete++;
        VAR[vi].STATUS = 0;
        VAR[vi].RED_ACTIVE = NULL;
        VAR[vi].U.DISC.UB = INT_MAX;
        VAR[vi].U.DISC.LB = INT_MIN;
        VAR[vi].NAME = malloc(4+intlen(vi)); 
        sprintf(VAR[vi].NAME, "_M%1dD", vi);  
        init_var_fields(vi); 
      }
      break; 
    case TYPE_FLOAT: 
      for (v = 0; v < m->size; v++, vi++) { 
        VAR[vi].TYPE = m->type; 
        VAR[vi].PROC_INDEX = 0; 
        VAR[vi].OFFSET = offset_float++;
        VAR[vi].STATUS = 0;
        VAR[vi].RED_ACTIVE = NULL;
        VAR[vi].U.FLT.UB = FLT_MAX;
        VAR[vi].U.FLT.LB = -1*FLT_MAX;
        VAR[vi].NAME = malloc(4+intlen(vi)); 
        sprintf(VAR[vi].NAME, "_M%1dF", vi);  
        init_var_fields(vi); 
      }
      break; 
    case TYPE_DOUBLE: 
      for (v = 0; v < m->size; v++, vi++) { 
        VAR[vi].TYPE = m->type; 
        VAR[vi].PROC_INDEX = 0; 
        VAR[vi].OFFSET = offset_double++;
        VAR[vi].STATUS = 0;
        VAR[vi].RED_ACTIVE = NULL;
        VAR[vi].U.DBLE.UB = DBL_MAX;
        VAR[vi].U.DBLE.LB = -1*DBL_MAX;
        VAR[vi].NAME = malloc(5+intlen(vi)); 
        sprintf(VAR[vi].NAME, "_M%1dDF", vi);  
        init_var_fields(vi); 
      }
      break; 
    default: 
      bk(0); 
  } }
/*
  if (MEMORY_SIZE > 0) { 
    fprintf(RED_OUT, "\nmemory %s: lb = %1d, ub = %1d\n", 
      VAR[MEMORY_START_VI].NAME, 
      VAR[MEMORY_START_VI].LB, VAR[MEMORY_START_VI].UB
    );
    fprintf(RED_OUT, "check %s: lb-1 = %1d, ub+1 = %1d\n", 
      VAR[MEMORY_START_VI].NAME, 
      VAR[MEMORY_START_VI].LB-1, VAR[MEMORY_START_VI].UB+1
    );
  }
*/
  for (pi = 0; pi <= PROCESS_COUNT; pi++) {
    vi = variable_index[TYPE_LAZY_EXP][pi][0]; 
    VAR[vi].TYPE = TYPE_LAZY_EXP; 
    VAR[vi].PROC_INDEX = pi; 
    VAR[vi].OFFSET = 0;
    VAR[vi].STATUS = 0;
    VAR[vi].RED_ACTIVE = NULL;
    VAR[vi].U.BDD.LB = 0;
    VAR[vi].U.BDD.UB = 0;
    VAR[vi].NAME = malloc(9+intlen(pi)); 
    sprintf(VAR[vi].NAME, "LAZY-EXP%1d", pi); 
    init_var_fields(vi); 
  }
  if (   GLOBAL_COUNT[TYPE_DISCRETE] || GLOBAL_COUNT[TYPE_POINTER]
      || (GLOBAL_COUNT[TYPE_CLOCK] > 2 && (GSTATUS[INDEX_MODAL_CLOCK] & FLAG_MODAL_CLOCK))
      || (GLOBAL_COUNT[TYPE_CLOCK] > 1 && !(GSTATUS[INDEX_MODAL_CLOCK] & FLAG_MODAL_CLOCK))
      )
    GSTATUS[INDEX_GLOBAL_VARIABLE] = GSTATUS[INDEX_GLOBAL_VARIABLE] | FLAG_GLOBAL_VARIABLE;
  else
    GSTATUS[INDEX_GLOBAL_VARIABLE] = GSTATUS[INDEX_GLOBAL_VARIABLE] & ~FLAG_GLOBAL_VARIABLE;
  init_exp_management(); 

  #ifdef RED_DEBUG_PARSE_MODE
  print_parse_variables();
  print_variables(); 
  #endif 
}
  /* variable_fillin() */





/* This procedure create an array GSYNC to records the synchronization 
 * structures for each global synchronizer. 
 */
void	gsync_fillin() { 
  struct parse_variable_type	*pv; 
  int				vi, ci; 
  
  GSYNC = (struct sync_type *)
    malloc(GLOBAL_COUNT[TYPE_SYNCHRONIZER] * sizeof(struct sync_type));
  for (pv = declare_global_synchronizer_list;
       pv;
       pv = pv->next_parse_variable
       ) {
    vi = variable_index[TYPE_SYNCHRONIZER][0][pv->index];
    GSYNC[pv->index].VAR_INDEX = vi; 
    GSYNC[pv->index].STATUS = 0; 
    GSYNC[pv->index].X_XTION_COUNT = 0;
    GSYNC[pv->index].Q_XTION_COUNT = 0;
    GSYNC[pv->index].X_XTION = (struct sync_from_xtion_type *)
      malloc(pv->X_xtion_count * sizeof(struct sync_from_xtion_type));
    for (ci = 0; ci < pv->X_xtion_count; ci++) {
      GSYNC[pv->index].X_XTION[ci].XTION_INDEX = -1; 
      GSYNC[pv->index].X_XTION[ci].PLACE_INDEX = -1; 
    } 
      
    GSYNC[pv->index].Q_XTION = (struct sync_from_xtion_type *)
      malloc(pv->Q_xtion_count * sizeof(struct sync_from_xtion_type));
    for (ci = 0; ci < pv->Q_xtion_count; ci++) {
      GSYNC[pv->index].Q_XTION[ci].XTION_INDEX = -1; 
      GSYNC[pv->index].Q_XTION[ci].PLACE_INDEX = -1; 
    } 
  }
  #ifdef RED_DEBUG_PARSE_MODE
  print_gsyncs(); 
  #endif 
}
  /* gsync_fillin() */ 
  
  







int	search_mode_index(mname)
     char			*mname;
{
  struct parse_mode_type	*pm;

  for (pm = declare_mode_list; pm; pm = pm->next_parse_mode)
    if (!strcmp(pm->name, mname)) {
      return(pm->index);
  } 
  return(-1); 
}
/* search_mode_index() */




struct parse_mode_type	*search_parse_mode(mname)
     char			*mname;
{
  struct parse_mode_type	*pm;

  for (pm = declare_mode_list; pm; pm = pm->next_parse_mode)
    if (!strcmp(pm->name, mname)) {
      return(pm);
  } 
  return(NULL); 
}
/* search_parse_mode() */




struct ps_exp_type	*CLOCK_POS, *CLOCK_NEG;

int	deduce_vi_simple_equal(
  int			vi, 
  struct ps_exp_type	*exp, 
  int			pi
) {
  int	value, local_flag; 
  
  if (VAR[vi].TYPE != exp->type) 
    return(TYPE_FALSE); 
  else switch (exp->type) { 
  case TYPE_CLOCK: 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_DENSE: 
    if (   VAR[vi].OFFSET != exp->u.atom.var->index
        || (   VAR[vi].PROC_INDEX == 0 
            && (exp->u.atom.var->status & FLAG_LOCAL_VARIABLE)
            )
        || (   VAR[vi].PROC_INDEX > 0 
            && !(exp->u.atom.var->status & FLAG_LOCAL_VARIABLE)
        )   )
      return(TYPE_FALSE); 
    value = get_value(exp->u.atom.exp_base_proc_index, pi, &local_flag); 
    if (local_flag == FLAG_SPECIFIC_VALUE) {
      if (value == VAR[vi].PROC_INDEX)  
      	return(TYPE_TRUE); 
      else 
      	return(TYPE_FALSE); 
    } 
    else 
      return(TYPE_FALSE); 
  case TYPE_QFD: 
  default: 
    return(TYPE_FALSE); 
  } 
} 
  /* deduce_vi_simple_equal() */ 
  


  

/*****************************************************
 *  The following set of procedures deduce simple bounds 
 *  for discrete variables. 
 *    deduce_vi_simple_range() 
 */




int	PI_DEDUCE_VI_SIMPLE_VALUE; 
int	VI_DEDUCE_SIMPLE_VALUE; 


int	deduce_vi_simple_range_from_term( 
  struct ps_exp_type	*psub, 
  int			*offset_ptr 
) { 
  int	coeff, offset, local_flag; 
  
  if (   psub->u.ineq.term_count > 1
      || !deduce_vi_simple_equal(
            VI_DEDUCE_SIMPLE_VALUE, 
            psub->u.ineq.term[0].operand, 
            PI_DEDUCE_VI_SIMPLE_VALUE 
      )   ) { 
    return(FLAG_ANY_VALUE); 
  }
 
  coeff = get_value(psub->u.ineq.term[0].coeff, 
    PI_DEDUCE_VI_SIMPLE_VALUE, 
    &local_flag
  ); 
  if (local_flag != FLAG_SPECIFIC_VALUE) {
    return(FLAG_ANY_VALUE); 
  }
  offset= get_value(psub->u.ineq.offset, 
    PI_DEDUCE_VI_SIMPLE_VALUE, 
    &local_flag
  ); 
  if (   local_flag != FLAG_SPECIFIC_VALUE
      || coeff == 0 
      || (offset % coeff)
      ) {
    return(FLAG_ANY_VALUE); 
  }
  *offset_ptr = offset / coeff; 
  return(FLAG_SPECIFIC_VALUE); 
} 
  /* deduce_vi_simple_range_from_term() */ 




int	deduce_vi_simple_range_from_arith( 
  struct ps_exp_type	*psub, 
  int			*offset_ptr 
) { 
  int	local_flag; 

  if (deduce_vi_simple_equal(
        VI_DEDUCE_SIMPLE_VALUE, 
        psub->u.arith.lhs_exp, 
        PI_DEDUCE_VI_SIMPLE_VALUE 
      ) ) { 
    *offset_ptr = get_value(
      psub->u.arith.rhs_exp, PI_DEDUCE_VI_SIMPLE_VALUE, 
      &local_flag
    ); 
    if (local_flag == FLAG_SPECIFIC_VALUE) 
      return(FLAG_SPECIFIC_VALUE); 
    else 
      return(FLAG_ANY_VALUE); 
  } 
  else if (deduce_vi_simple_equal(
             VI_DEDUCE_SIMPLE_VALUE, 
             psub->u.arith.rhs_exp, 
             PI_DEDUCE_VI_SIMPLE_VALUE 
           ) ) { 
    *offset_ptr = get_value(
      psub->u.arith.lhs_exp, PI_DEDUCE_VI_SIMPLE_VALUE, 
      &local_flag
    ); 
    if (local_flag == FLAG_SPECIFIC_VALUE)  
      return(FLAG_SPECIFIC_VALUE); 
    else 
      return(FLAG_ANY_VALUE); 
  } 
  else { 
    return(FLAG_ANY_VALUE); 
  } 
} 
  /* deduce_vi_simple_range_from_arith() */ 




  
int	rec_deduce_vi_simple_range( 
  struct ps_exp_type	*psub, 
  int			*lb_ptr, 
  int			*ub_ptr  
) {
  int				i, lb, ub, 
				result_flag, local_flag, coeff, offset;
  struct parse_variable_type	*v1, *v2;
  struct ps_bunit_type		*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
    return(FLAG_NO_VALUE); 

  case TYPE_TRUE :
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
  case NEQ:
  case ARITH_NEQ:
  case NOT :
  case IMPLY :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    return(FLAG_ANY_VALUE); 

  case RED: 
    return(red_get_vi_range(psub->u.rpred.red, 
      VI_DEDUCE_SIMPLE_VALUE, lb_ptr, ub_ptr
    ) ); 
    
  case EQ : 
    if (deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LEQ:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LESS:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GREATER:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GEQ: 
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_EQ :
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nred_local = %1d\n", ++count_red_local); 
    pcform(psub); 
    fflush(RED_OUT); 
    #endif 
    if (deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE) {
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

/*
    fprintf(RED_OUT, "\nred_local = %1d, psub->u.arith.type=%1d\n", 
      ++count_red_local, psub->u.arith.type 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/
    break; 
  case ARITH_LEQ:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_LESS:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GREATER:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GEQ: 
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_CONDITIONAL: 
  case TYPE_INLINE_BOOLEAN_DECLARE:     
  case TYPE_INLINE_DISCRETE_DECLARE: 
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "\nError: This should not be in rec_get_var_simple_value()!\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case TYPE_INLINE_CALL: 
    return(rec_deduce_vi_simple_range(
      psub->u.inline_call.instantiated_exp, lb_ptr, ub_ptr 
    ) ); 

  case AND :
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_vi_simple_range(pbu->subexp, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case OR :
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_vi_simple_range(pbu->subexp, &lb, &ub);  
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case FORALL: 
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_vi_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(result_flag);
    break;

  case EXISTS :
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB-1; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_vi_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DISC.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(local_flag);
    break;

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
/* rec_deduce_vi_simple_range() */ 





// In this function, we try to deduce the value of variable vi from 
// the local constraint of exp at process pi's point of view. 
int	deduce_vi_simple_range(
  struct ps_exp_type	*exp, 
  int			vi, 
  int			pi, 
  int			*lb_ptr, 
  int			*ub_ptr 
) {
  switch (VAR[vi].TYPE) { 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "\nERROR: Illegal floating-point range query for %1d:%s\n", 
      vi, VAR[vi].NAME
    ); 	
    bk(0); 
  } 
  PI_DEDUCE_VI_SIMPLE_VALUE = pi; 
  if (VAR[vi].PROC_INDEX > 0 && pi > 0) 
    VI_DEDUCE_SIMPLE_VALUE = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET]; 
  else 
    VI_DEDUCE_SIMPLE_VALUE = vi; 
  
  return(rec_deduce_vi_simple_range(exp, lb_ptr, ub_ptr)); 
}
  /* deduce_vi_simple_range() */  






/*****************************************************
 *  The following set of procedures deduce simple bounds 
 *  for floating point variables. 
 *    deduce_float_simple_range() 
 */

  
int	rec_deduce_float_simple_range( 
  struct ps_exp_type	*psub, 
  float			*lb_ptr, 
  float			*ub_ptr  
) {
  int				i,  
				result_flag, local_flag, coeff, offset;
  float				lb, ub; 
  struct parse_variable_type	*v1, *v2;
  struct ps_bunit_type		*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
    return(FLAG_NO_VALUE); 

  case TYPE_TRUE :
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
  case NEQ:
  case ARITH_NEQ:
  case NOT :
  case IMPLY :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    return(FLAG_ANY_VALUE); 

  case RED: 
    return(red_get_float_range(psub->u.rpred.red, 
      VI_DEDUCE_SIMPLE_VALUE, lb_ptr, ub_ptr
    ) ); 
    
  case EQ : 
    if (deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LEQ:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LESS:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GREATER:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GEQ: 
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_EQ :
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nred_local = %1d\n", ++count_red_local); 
    pcform(psub); 
    fflush(RED_OUT); 
    #endif 
    if (deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE) {
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

/*
    fprintf(RED_OUT, "\nred_local = %1d, psub->u.arith.type=%1d\n", 
      ++count_red_local, psub->u.arith.type 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/
    break; 
  case ARITH_LEQ:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_LESS:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GREATER:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GEQ: 
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_CONDITIONAL: 
  case TYPE_INLINE_BOOLEAN_DECLARE:     
  case TYPE_INLINE_DISCRETE_DECLARE: 
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "\nError: This should not be in rec_get_var_simple_value()!\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case TYPE_INLINE_CALL: 
    return(rec_deduce_float_simple_range(
      psub->u.inline_call.instantiated_exp, lb_ptr, ub_ptr 
    ) ); 

  case AND :
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_float_simple_range(pbu->subexp, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case OR :
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_float_simple_range(pbu->subexp, &lb, &ub);  
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case FORALL: 
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_float_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(result_flag);
    break;

  case EXISTS :
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB-1; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_float_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.FLT.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(local_flag);
    break;

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
/* rec_deduce_float_simple_range() */ 





// In this function, we try to deduce the value of variable vi from 
// the local constraint of exp at process pi's point of view. 
int	deduce_float_simple_range(
  struct ps_exp_type	*exp, 
  int			vi, 
  int			pi, 
  float			*lb_ptr, 
  float			*ub_ptr 
) {
  switch (VAR[vi].TYPE) { 
  case TYPE_FLOAT: 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal floating-point range query for %1d:%s\n", 
      vi, VAR[vi].NAME
    ); 	
    bk(0); 
  } 
  PI_DEDUCE_VI_SIMPLE_VALUE = pi; 
  if (VAR[vi].PROC_INDEX > 0 && pi > 0) 
    VI_DEDUCE_SIMPLE_VALUE = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET]; 
  else 
    VI_DEDUCE_SIMPLE_VALUE = vi; 
  
  return(rec_deduce_float_simple_range(exp, lb_ptr, ub_ptr)); 
}
  /* deduce_float_simple_range() */  









/*****************************************************
 *  The following set of procedures deduce simple bounds 
 *  for double precision floating point variables. 
 *    deduce_double_simple_range() 
 */

  
int	rec_deduce_double_simple_range( 
  struct ps_exp_type	*psub, 
  double		*lb_ptr, 
  double		*ub_ptr  
) {
  int				i,  
				result_flag, local_flag, coeff, offset;
  double			lb, ub; 
  struct parse_variable_type	*v1, *v2;
  struct ps_bunit_type		*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
    return(FLAG_NO_VALUE); 

  case TYPE_TRUE :
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
  case NEQ:
  case ARITH_NEQ:
  case NOT :
  case IMPLY :
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    return(FLAG_ANY_VALUE); 

  case RED: 
    return(red_get_double_range(psub->u.rpred.red, 
      VI_DEDUCE_SIMPLE_VALUE, lb_ptr, ub_ptr
    ) ); 
    
  case EQ : 
    if (deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LEQ:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case LESS:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GREATER:
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case GEQ: 
    if (   deduce_vi_simple_range_from_term(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_EQ :
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nred_local = %1d\n", ++count_red_local); 
    pcform(psub); 
    fflush(RED_OUT); 
    #endif 
    if (deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE) {
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (   offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB
             || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
             ) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

/*
    fprintf(RED_OUT, "\nred_local = %1d, psub->u.arith.type=%1d\n", 
      ++count_red_local, psub->u.arith.type 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/
    break; 
  case ARITH_LEQ:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset < VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB;  
    *ub_ptr = offset; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_LESS:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB;  
    *ub_ptr = offset-1; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GREATER:
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset+1;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_GEQ: 
    if (   deduce_vi_simple_range_from_arith(psub, &offset) == FLAG_ANY_VALUE
        || offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
        ) {  
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
      return(FLAG_ANY_VALUE); 
    } 
    else if (offset > VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB) { 
      *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
      *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
      return(FLAG_NO_VALUE); 
    }
    *lb_ptr = offset;  
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    return(FLAG_SPECIFIC_VALUE); 
    break; 

  case ARITH_CONDITIONAL: 
  case TYPE_INLINE_BOOLEAN_DECLARE:     
  case TYPE_INLINE_DISCRETE_DECLARE: 
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "\nError: This should not be in rec_get_var_simple_value()!\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case TYPE_INLINE_CALL: 
    return(rec_deduce_double_simple_range(
      psub->u.inline_call.instantiated_exp, lb_ptr, ub_ptr 
    ) ); 

  case AND :
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_double_simple_range(pbu->subexp, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case OR :
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      local_flag = rec_deduce_double_simple_range(pbu->subexp, &lb, &ub);  
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    return(result_flag);

  case FORALL: 
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_ANY_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_double_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_NO_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
        return(FLAG_NO_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_ANY_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr < lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr > ub) 
      	    *ub_ptr = ub; 
      	}
      	if (*lb_ptr > *ub_ptr) {  
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
          return(FLAG_NO_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(result_flag);
    break;

  case EXISTS :
    lb = get_value(psub->u.qexp.lb_exp, -1, &i); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &i); 
    push_quantified_value_stack(psub); 
    result_flag = FLAG_NO_VALUE; 
    *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB+1; 
    *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB-1; 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      local_flag = rec_deduce_double_simple_range(psub->u.qexp.child, &lb, &ub); 
      if (local_flag == FLAG_ANY_VALUE) { 
        *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
        *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
        return(FLAG_ANY_VALUE); 
      }
      else if (local_flag == FLAG_SPECIFIC_VALUE) {  
      	if (result_flag == FLAG_NO_VALUE)  
      	  result_flag = FLAG_SPECIFIC_VALUE; 

      	if (result_flag == FLAG_SPECIFIC_VALUE) {  
      	  if (*lb_ptr > lb) 
      	    *lb_ptr = lb; 
      	  if (*ub_ptr < ub) 
      	    *ub_ptr = ub; 
      	}
      	if (   *lb_ptr <= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB 
      	    && *ub_ptr >= VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB
      	    ) { 
          *lb_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.LB; 
          *ub_ptr = VAR[VI_DEDUCE_SIMPLE_VALUE].U.DBLE.UB; 
          return(FLAG_ANY_VALUE); 
        } 
      } 
    }
    pop_quantified_value_stack(psub); 
    return(local_flag);
    break;

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
/* rec_deduce_double_simple_range() */ 





// In this function, we try to deduce the value of variable vi from 
// the local constraint of exp at process pi's point of view. 
int	deduce_double_simple_range(
  struct ps_exp_type	*exp, 
  int			vi, 
  int			pi, 
  double		*lb_ptr, 
  double		*ub_ptr 
) {
  switch (VAR[vi].TYPE) { 
  case TYPE_DOUBLE: 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal floating-point range query for %1d:%s\n", 
      vi, VAR[vi].NAME
    ); 	
    bk(0); 
  } 
  PI_DEDUCE_VI_SIMPLE_VALUE = pi; 
  if (VAR[vi].PROC_INDEX > 0 && pi > 0) 
    VI_DEDUCE_SIMPLE_VALUE = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET]; 
  else 
    VI_DEDUCE_SIMPLE_VALUE = vi; 
  
  return(rec_deduce_double_simple_range(exp, lb_ptr, ub_ptr)); 
}
  /* deduce_double_simple_range() */  













inline int	vi_in_primed_context(
  struct ps_exp_type	*psub, 
  int			vi
) { 
  if (psub->var_status & FLAG_VAR_PRIMED) {
    vi = VAR[vi].PRIMED_VI; 
  }
  return(vi); 
} 
  /* vi_in_primed_context() */ 



inline int	clock_index_from_exp( 
  struct ps_exp_type	*cexp,  
  int			pi
) { 
   int	ci; 
   
   ci = variable_index[TYPE_CLOCK][pi][VAR[cexp->u.atom.var_index].OFFSET]; 
   return(VAR[ci].U.CLOCK.CLOCK_INDEX); 
}
  /* clock_index_from_exp() */  






int			VARX_PATH_LENGTH;
struct ps_exp_type	**VARX_PATH, *VARX;
struct red_type		*VARX_RED_RHS;

int 	locate_1st_variable(psub, depth)
  struct ps_exp_type 	*psub;
  int 			depth;
{
  switch(psub->type){
  case TYPE_CONSTANT:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_NULL:  
  case TYPE_MACRO_CONSTANT: 
    return(TYPE_FALSE); 

  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER:
  case TYPE_CLOCK:
  
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

    fprintf(RED_OUT, "\nHuh ? (in locate_1st_variable) \n");
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
    if (VARX) {
      fprintf(RED_OUT, "\nParser: Huh ? (parse 11) \n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);

    }
    else { 
      VARX = psub; 
      VARX_PATH_LENGTH = depth + 1; 
      VARX_PATH = (struct ps_exp_type **) malloc(VARX_PATH_LENGTH * sizeof(struct ps_exp_type *)); 
      VARX_PATH[depth] = psub; 
      return(TYPE_TRUE); 
    }
    break; 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE:
    if (locate_1st_variable(psub->u.arith.lhs_exp)) {
      VARX_PATH[depth] = psub; 
      return(TYPE_TRUE); 
    }
    else if (locate_1st_variable(psub->u.arith.rhs_exp)) {
      VARX_PATH[depth] = psub; 
      return(TYPE_TRUE); 
    }
    else 
      return(TYPE_FALSE); 

  case ARITH_MODULO: 
    return(TYPE_FALSE); 

  default: 
    fprintf(RED_OUT, "\nParser: Huh ? (parse 12) \n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 

  } 

}
/* locate_1st_variables() */























struct red_type	*red_spec_clock_simple_relation(ci, op, rvalue) 
     int	ci, op, rvalue;
{
  switch (op) { 
  case EQ:
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[ci][0] = add_index(ZONE_CONSTANT[ci][0], 2*rvalue);
      ZONE_CONSTANT[0][ci] = add_index(ZONE_CONSTANT[0][ci], -2*rvalue);
    }
    return(red_bop(AND, 
		   crd_atom(ZONE[0][ci], -2*rvalue), 
		   crd_atom(ZONE[ci][0], 2*rvalue)
		   )
	   ); 
  case NEQ: 
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[ci][0] = add_index(ZONE_CONSTANT[ci][0], 2*rvalue-1); 
      ZONE_CONSTANT[0][ci] = add_index(ZONE_CONSTANT[0][ci], -2*rvalue-1); 
    }
    return(red_bop(OR, 
		   crd_atom(ZONE[0][ci], -2*rvalue-1),
		   crd_atom(ZONE[ci][0], 2*rvalue-1)
		   )
	   ); 
  case LESS : 
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[ci][0] = add_index(ZONE_CONSTANT[ci][0], 2*rvalue-1);
    }
    return(crd_atom(ZONE[ci][0], 2*rvalue-1));
  case LEQ :
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[ci][0] = add_index(ZONE_CONSTANT[ci][0], 2*rvalue);
    }
    return(crd_atom(ZONE[ci][0], 2*rvalue));
  case GEQ :
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[0][ci] = add_index(ZONE_CONSTANT[0][ci], -2*rvalue);
    }
    return(crd_atom(ZONE[0][ci], -2*rvalue));
  case GREATER :
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP: 
      ZONE_CONSTANT[0][ci] = add_index(ZONE_CONSTANT[0][ci], -2*rvalue-1);
    }
    return(crd_atom(ZONE[0][ci], (-2*rvalue)-1));
  }
}
/* red_spec_clock_simple_relation() */









struct red_type	*RED_SYNC_CURRENT; 

struct red_type	*rec_get_event_xtions(fx, dc) 
     struct red_type	*fx, *dc;
{
  int				ci, xi, igi, gvi; 
  struct red_type		*conj, *result;
  struct rec_type		*rec, *nrec; 

  if (fx == NORM_FALSE) 
    return(fx); 
  else if (fx == NORM_NO_RESTRICTION) 
    if (red_bop(EXTRACT, dc, RED_SYNC_CURRENT) != NORM_FALSE)
      return(NORM_NO_RESTRICTION);
    else 
      return(NORM_FALSE); 
      
  rec = rec_new(fx, dc); 
  nrec = (struct rec_type *) add_23tree(rec, parse_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					); 
  if (rec != nrec) { 
    return(nrec->result); 
  }

  result = NORM_FALSE; 
  switch (VAR[fx->var_index].TYPE) { 
  case TYPE_XTION_INSTANCE:
    for (ci = 0; ci < fx->u.ddd.child_count; ci++) { 
      for (xi = fx->u.ddd.arc[ci].lower_bound; 
           xi <= fx->u.ddd.arc[ci].upper_bound; 
           xi++
           ) { 
      	conj = dc; 
      	if (xi) {
      	  for (igi = 0; igi < XTION[xi].sync_count; igi++) 
      	    if (XTION[xi].sync[igi].type < 0) { 
	      gvi = XTION[xi].sync[igi].sync_index;
	      gvi = variable_index[TYPE_SYNCHRONIZER][0][gvi];
	      conj = red_inc_off(conj, gvi, 1, 1);
	    }
	}
        conj = rec_get_event_xtions(fx->u.ddd.arc[ci].child, conj);
        conj = ddd_one_constraint(conj, fx->var_index, 
          fx->u.ddd.arc[ci].lower_bound, fx->u.ddd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_CRD:
    for (ci = 0; ci < fx->u.crd.child_count; ci++) {
      conj = rec_get_event_xtions(fx->u.crd.arc[ci].child, dc);
      conj = crd_one_constraint(conj, fx->var_index, fx->u.crd.arc[ci].upper_bound);
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < fx->u.fdd.child_count; ci++) {
      conj = rec_get_event_xtions(fx->u.fdd.arc[ci].child, dc);
      conj = fdd_one_constraint(conj, fx->var_index, 
        fx->u.fdd.arc[ci].lower_bound, fx->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < fx->u.dfdd.child_count; ci++) {
      conj = rec_get_event_xtions(fx->u.dfdd.arc[ci].child, dc);
      conj = dfdd_one_constraint(conj, fx->var_index, 
        fx->u.dfdd.arc[ci].lower_bound, fx->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  default:
    for (ci = 0; ci < fx->u.ddd.child_count; ci++) {
      conj = rec_get_event_xtions(fx->u.ddd.arc[ci].child, dc);
      conj = ddd_one_constraint(conj, fx->var_index, 
        fx->u.ddd.arc[ci].lower_bound, fx->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
  } 
  return(rec->result = result);
}
  /* rec_get_event_xtions() */



struct red_type	*get_event_xtions(d)
	struct red_type	*d;
{
  int 			gi;
  struct red_type	*conj;

  RED_SYNC_CURRENT = d;
  conj = NORM_NO_RESTRICTION;
  for (gi = GLOBAL_COUNT[TYPE_SYNCHRONIZER]-1; gi >= 0; gi--)
    conj = ddd_one_constraint
	   (conj, variable_index[TYPE_SYNCHRONIZER][0][gi], 0, 0);
  init_23tree(&parse_tree);
  d = rec_get_event_xtions(RT[XI_SYNC_ALL], conj);
  free_entire_23tree(parse_tree, rec_free);

  return(d);
}
/* get_event_xtions() */





struct red_type	*rec_add_event_counts_from_xtions(fx, dc) 
     struct red_type	*fx, *dc;
{
  int				ci, xi, igi, gvi; 
  struct red_type		*conj, *result;
  struct cache2_hash_entry_type	*ce; 

  if (fx == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (fx == NORM_NO_RESTRICTION) 
    return(dc); 
      
  ce = cache2_check_result_key(OP_ADD_EVENT_COUNTS_FROM_XTIONS, fx, dc); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[fx->var_index].TYPE) { 
  case TYPE_XTION_INSTANCE:
    for (ci = 0; ci < fx->u.ddd.child_count; ci++) { 
      for (xi = fx->u.ddd.arc[ci].lower_bound; xi <= fx->u.ddd.arc[ci].upper_bound; xi++) { 
      	conj = dc; 
      	if (xi) {
      	  for (igi = 0; igi < XTION[xi].sync_count; igi++) 
      	    if (XTION[xi].sync[igi].type < 0) { 
	      gvi = XTION[xi].sync[igi].sync_index;
	      gvi = variable_index[TYPE_SYNCHRONIZER][0][gvi];
	      conj = red_inc_off(conj, gvi, 1, 1); 
	    }
	}
        conj = rec_add_event_counts_from_xtions(fx->u.ddd.arc[ci].child, conj);
        conj = ddd_one_constraint(conj, fx->var_index, fx->u.ddd.arc[ci].lower_bound, fx->u.ddd.arc[ci].upper_bound);
        result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_CRD:
    fprintf(RED_OUT, "Well I did not expect to see this.\n"); 
    exit(0); 
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < fx->u.fdd.child_count; ci++) {
      conj = rec_add_event_counts_from_xtions(fx->u.fdd.arc[ci].child, dc);
      conj = fdd_one_constraint(conj, fx->var_index, 
        fx->u.fdd.arc[ci].lower_bound, fx->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < fx->u.dfdd.child_count; ci++) {
      conj = rec_add_event_counts_from_xtions(fx->u.dfdd.arc[ci].child, dc);
      conj = fdd_one_constraint(conj, fx->var_index, 
        fx->u.dfdd.arc[ci].lower_bound, fx->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  default:
    for (ci = 0; ci < fx->u.ddd.child_count; ci++) {
      conj = rec_add_event_counts_from_xtions(fx->u.ddd.arc[ci].child, dc);
      conj = ddd_one_constraint(conj, fx->var_index, fx->u.ddd.arc[ci].lower_bound, fx->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result);
}
  /* rec_add_event_counts_from_xtions() */



struct red_type	*add_event_counts_from_xtions(d)
	struct red_type	*d;
{
  int 			gi;
  struct red_type	*conj;

  conj = NORM_NO_RESTRICTION;
  for (gi = GLOBAL_COUNT[TYPE_SYNCHRONIZER]-1; gi >= 0; gi--) {
    conj = ddd_one_constraint
	   (conj, variable_index[TYPE_SYNCHRONIZER][0][gi], 0, 0);
  } 
  d = rec_add_event_counts_from_xtions(d, conj);
  
  return(d);
}
/* add_event_counts_from_xtions() */




  


/********************************************************************************************  
 *
 */
struct red_type		*SPLIT_ZONE_START; 
int			*SPLIT_TCC_PTR; 
struct constraint_type	**SPLIT_TC_PTR; 


struct red_type	*rec_identify_unique_zone(d)
  struct red_type	*d; 
{
  int				ci;
  struct red_type		*conj, *new_child;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(d);
  else if (VAR[d->var_index].TYPE == TYPE_CRD) {
    if (d == SPLIT_ZONE_START)
      return(NORM_NO_RESTRICTION);
    else if (SPLIT_ZONE_START) {
      fprintf(RED_OUT, "\nDisjunctive BDD with different zones has not been implemented at this moment. Sorry!\n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);

    }
    else {
      *SPLIT_TCC_PTR = 0;
      SPLIT_ZONE_START = d;
      for (conj = d; conj != NORM_NO_RESTRICTION; conj = conj->u.crd.arc[0].child) {
	if (conj->u.crd.child_count > 1) {
	  fprintf(RED_OUT, "\nDisjunctive zone constraint has not been implemented at this moment. Sorry!\n");
	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
	}
	else if (VAR[conj->var_index].TYPE == TYPE_CRD) {
	  if (conj->u.crd.arc[0].upper_bound < CLOCK_POS_INFINITY)
	    (*SPLIT_TCC_PTR)++;
	}
      }

      *SPLIT_TC_PTR = (struct constraint_type *) malloc((*SPLIT_TCC_PTR) * sizeof(struct constraint_type));
      *SPLIT_TCC_PTR = 0;
      for (conj = d; conj != NORM_NO_RESTRICTION; conj = conj->u.crd.arc[0].child) {
	if (   VAR[conj->var_index].TYPE == TYPE_CRD
	    && conj->u.crd.arc[0].upper_bound < CLOCK_POS_INFINITY
	    ) {
	  (*SPLIT_TC_PTR)[*SPLIT_TCC_PTR].cstart 
	  = VAR[conj->var_index].U.CRD.CLOCK1;
	  (*SPLIT_TC_PTR)[*SPLIT_TCC_PTR].cstop 
	  = VAR[conj->var_index].U.CRD.CLOCK2;
	  (*SPLIT_TC_PTR)[*SPLIT_TCC_PTR].bound 
	  = conj->u.crd.arc[0].upper_bound;
	  (*SPLIT_TCC_PTR)++;
	}
      }

      return(NORM_NO_RESTRICTION);
    }
  }

  ce = cache1_check_result_key(OP_IDENTIFY_UNIQUE_ZONE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  child_stack_level_push();
  for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
    new_child = rec_identify_unique_zone(d->u.ddd.arc[ci].child);
    ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
		      d->u.ddd.arc[ci].upper_bound 
		      );
  }

  return(ce->result = ddd_new(d->var_index));
}
/* rec_identify_unique_zone() */





struct red_type	*red_identify_unique_zone(d, tcc_ptr, tc_ptr)
     struct red_type		*d;
     int			*tcc_ptr;
     struct constraint_type	**tc_ptr; 
{
  SPLIT_TCC_PTR = tcc_ptr; 
  SPLIT_TC_PTR =  tc_ptr; 

  SPLIT_ZONE_START = NULL; 
  *SPLIT_TCC_PTR = 0; 

  cache1_clear(OP_IDENTIFY_UNIQUE_ZONE, OP_IDENTIFY_UNIQUE_ZONE); 
  d = rec_identify_unique_zone(d); 

  return(d); 
}
/* red_identify_unique_zone() */




mode_fillin()
{
  struct parse_mode_type		*pm;
  int					mi, ri, pi, ixi, vi, bn, bd;
  struct parse_rate_spec_link_type	*rsl;
  struct parse_xtion_link_type		*pxl;

  MODE = (struct mode_type *) malloc(MODE_COUNT*sizeof(struct mode_type));
  /*
  fprintf(RED_OUT, "\nMODE=%x\n", MODE);
  */
  if (CLOCK_COUNT)
    ALL_RATE_BOUND = 1;
  for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) {
    mi = pm->index;
    MODE[mi].status = pm->status;
    MODE[mi].src_lines = pm->src_lines; 
    MODE[mi].name = pm->name;
    MODE[mi].xtion_count = pm->xtion_count;
    MODE[mi].over_bound = pm->over_bound;
    MODE[mi].bound_left_open = pm->bound_left_open;
    MODE[mi].invariance_exp = pm->invariance_exp;
    var_index_fillin(MODE[mi].invariance_exp);
/*
    fprintf(RED_OUT, "\nmode %1d:%s: invariance:\n", mi, MODE[mi].name); 
    pcform(MODE[mi].invariance_exp); 
*/
    MODE[mi].rate_spec_count = pm->rate_spec_count;
    MODE[mi].process_rate_spec = (struct process_rate_spec_type *)
	malloc((PROCESS_COUNT+1)*sizeof(struct process_rate_spec_type));
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      MODE[mi].process_rate_spec[pi].status = 0;
      MODE[mi].process_rate_spec[pi].rate_spec = (struct rate_spec_type *)
	malloc(pm->rate_spec_count * sizeof(struct rate_spec_type));
      for (ri = 0, rsl = pm->parse_rate_spec_list; rsl; ri++, rsl = rsl->next_parse_rate_spec_link) {
	MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index = variable_index[TYPE_DENSE][pi][rsl->rate_var->index];
	get_rationals(rsl->rate_lb, pi, &bn, &bd);
	MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator = bn;
	MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator = bd;
	if (bn % bd)
	  bn = abs(bn/bd) + 1;
	else
	  bn = abs(bn/bd);
	if (bn > ALL_RATE_BOUND)
	  ALL_RATE_BOUND = bn;
/* 	if (rsl->status & FLAG_RATE_LB_OPEN)
	  MODE[mi].rate_spec[ri][pi].lb_numerator = 2*MODE[mi].rate_spec[ri][pi].lb_numerator + 1;
	else
*/
	MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
	  = /* 2* */ MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;

	get_rationals(rsl->rate_ub, pi, &bn, &bd);
	MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator = bn;
	MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator = bd;
	if (bn % bd)
	  bn = abs(bn/bd) + 1;
	else
	  bn = abs(bn/bd);
	if (bn > ALL_RATE_BOUND)
	  ALL_RATE_BOUND = bn;

/* 	if (rsl->status & FLAG_RATE_UB_OPEN)
	  MODE[mi].rate_spec[ri][pi].ub_numerator = 2*MODE[mi].rate_spec[ri][pi].lb_numerator - 1;
	else
*/
	MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
	  = /* 2* */ MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;

	if (  MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
	      * MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
	    - MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
	      * MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
	    > 0
	    ) {
	  fprintf(RED_OUT, "\nError: empty rate spec for variable %s in mode %s of process %1d.\n",
		  VAR[MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index].NAME,
		  MODE[mi].name, pi
		  );
	  fflush(RED_OUT);
	  exit(0);
	}
	else if (   MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
	            != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
		 || MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
		    != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
		 )
	  MODE[mi].process_rate_spec[pi].status = MODE[mi].process_rate_spec[pi].status | FLAG_RATE_INTERVAL;
      }
    }
    MODE[mi].xtion = (int *) malloc(pm->xtion_count* sizeof(int));
    for (ixi = 0, pxl = pm->parse_xtion_list;
         ixi < pm->xtion_count;
         ixi++, pxl = pxl->next_parse_xtion_link
         )
      MODE[mi].xtion[ixi] = pxl->parse_xtion->index;
  }
/*
  fprintf(RED_OUT, "ALL_RATE_BOUND:%1d\n", ALL_RATE_BOUND);
*/
/*
  for (mi=0; mi < MODE_COUNT; mi++) {
    fprintf(RED_OUT, "\n===(%1d:%s)===============================================\n",
    	    mi, MODE[mi].name
    	    );
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      fprintf(RED_OUT, "MODE[%1d:%s].invariance[%1d]:\n", mi, MODE[mi].name, pi);
      red_print_graph(MODE[mi].invariance[pi].red);
    }
  }
*/
  /*
  fprintf(RED_OUT, "%1d modes in total\n", MODE_COUNT);
  for (mi = 0; mi < MODE_COUNT; mi++)
    if (MODE[mi].bound_left_open)
      fprintf(RED_OUT, "MODE %1d: %s; OB=%1d:LO\n", mi, MODE[mi].name, MODE[mi].over_bound);
    else
      fprintf(RED_OUT, "MODE %1d: %s; OB=%1d:  \n", mi, MODE[mi].name, MODE[mi].over_bound);
  */

  /* fill in the variable rate spec. */
  
}
/* mode_fillin() */





struct index_triple_link_type	*CB_LIST; 
int				CB_COUNT; 
struct a23tree_type		*process_clock_bound_tree; 
  
#define clk_index	index1
#define clk_lb		index2
#define clk_ub		index3  

inline void	update_clock_lb_list(int ci, int lb) { 
  struct index_triple_link_type	dummy_head, *p, *c, *n; 
 
  dummy_head.next_index_triple_link = CB_LIST; 
  for (p = &dummy_head, c = CB_LIST; c; ) { 
    if (c->clk_index > ci) 
      break; 
    else if (c->clk_index < ci) { 
      p = c; 
      c = c->next_index_triple_link; 
    } 
    else { 
      if (lb < c->clk_lb)  
        c->clk_lb = lb; 
      return;       	
    } 	
  } 
  
  n = (struct index_triple_link_type *) 
    malloc(sizeof(struct index_triple_link_type)); 
  n->clk_index = ci; 
  n->clk_lb = lb; 
  n->clk_ub = CLOCK_NEG_INFINITY; 
  p->next_index_triple_link = n; 
  n->next_index_triple_link = c; 
  CB_LIST = dummy_head.next_index_triple_link; 
  CB_COUNT++; 
}
  /* update_clock_lb_list() */ 
  
  
  
inline void	update_clock_ub_list(int ci, int ub) { 
  struct index_triple_link_type	dummy_head, *p, *c, *n; 
 
  dummy_head.next_index_triple_link = CB_LIST; 
  for (p = &dummy_head, c = CB_LIST; c; ) { 
    if (c->clk_index > ci) 
      break; 
    else if (c->clk_index < ci) { 
      p = c; 
      c = c->next_index_triple_link; 
    } 
    else { 
      if (ub > c->clk_ub)  
        c->clk_lb = ub; 
      return;       	
    } 	
  } 
  
  n = (struct index_triple_link_type *) 
    malloc(sizeof(struct index_triple_link_type)); 
  n->clk_index = ci; 
  n->clk_lb = CLOCK_POS_INFINITY; 
  n->clk_ub = ub; 
  p->next_index_triple_link = n; 
  n->next_index_triple_link = c; 
  CB_LIST = dummy_head.next_index_triple_link; 
  CB_COUNT++; 
}
  /* update_clock_ub_list() */ 
  
  
  
extern int	rec_comp_path_bounds(); 

void	rec_collect_process_clock_bounds(struct red_type *d) { 
  int					ci, cj, c1, c2; 
  struct hrd_exp_type			*he;
  struct crd_child_type			*bc;
  struct hrd_child_type			*hc;
  struct ddd_child_type			*ic;
  struct rec_type			*nrec, *rec;
    
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return; 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, process_clock_bound_tree, 
    rec_comp_path_bounds, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return; 
  }
  
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0) { 
      update_clock_lb_list(
        c2, -1 * d->u.crd.arc[d->u.crd.child_count-1].upper_bound
      ); 
    } 
    else if (c2 == 0) { 
      update_clock_ub_list(
        c1, d->u.crd.arc[d->u.crd.child_count-1].upper_bound
      ); 
    } 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      rec_collect_process_clock_bounds(d->u.crd.arc[ci].child); 
    } 
    break; 
  case TYPE_HRD: 
  case TYPE_HDD: 
    fprintf(RED_OUT, 
      "Error: Unexpected data types in collect_process_clock_bounds()!\n"  
    ); 
    fflush(RED_OUT); 
    exit(0); 

    break; 
  case TYPE_LAZY_EXP: 
    rec_collect_process_clock_bounds(d->u.lazy.false_child); 
    rec_collect_process_clock_bounds(d->u.lazy.true_child); 
    break;   
  case TYPE_FLOAT	: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) { 
      rec_collect_process_clock_bounds(d->u.fdd.arc[ci].child); 
    } 
    break; 
  case TYPE_DOUBLE	: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) { 
      rec_collect_process_clock_bounds(d->u.dfdd.arc[ci].child); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      rec_collect_process_clock_bounds(d->u.ddd.arc[ci].child); 
    } 
    break; 
    
  } 
} 
  /* rec_collect_process_clock_bounds() */ 
  
  
  

  
  


struct clock_bound_type	*collect_process_clock_bounds(
  struct red_type	*d, 
  int			*bound_count_ptr
) { 
  struct clock_bound_type	*cb; 
  int				i; 
  struct index_triple_link_type	*p, *c; 
  
  CB_LIST = NULL; 
  CB_COUNT = 0; 
  init_23tree(&process_clock_bound_tree); 
  rec_collect_process_clock_bounds(d); 
  free_entire_23tree(process_clock_bound_tree, rec_free);
  
  if (CB_LIST == NULL) {
    *bound_count_ptr = 0; 
    return(NULL); 
  }
  cb = (struct clock_bound_type *) 
    malloc(CB_COUNT * sizeof(struct clock_bound_type)); 
  for (i = 0, c = CB_LIST; c; i++) { 
    cb[i].clock_index = c->clk_index; 
    cb[i].lower_bound = c->clk_lb; 
    cb[i].upper_bound = c->clk_ub; 
    p = c; 
    c = c->next_index_triple_link; 
    free(p); 
  } 
  *bound_count_ptr = CB_COUNT; 
  return(cb); 
}
  /* collect_process_clock_bounds() */ 
  
  
  




int	*lcb; 

void	statement_local_clock_bound_analysis(st) 
	struct statement_type	*st; 
{
  int	i, lci, rci; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case ST_IF: 
    statement_local_clock_bound_analysis(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      statement_local_clock_bound_analysis(st->u.branch.else_statement); 
    break; 
  case ST_WHILE: 
    statement_local_clock_bound_analysis(st->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      statement_local_clock_bound_analysis(st->u.seq.statement[i]); 
    } 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    switch (st->u.act.rhs_exp->type) { 
    case TYPE_CONSTANT: 
      if (VAR[st->u.act.lhs->u.atom.var_index].PROC_INDEX) { 
        lci = VAR[st->u.act.lhs->u.atom.var_index].OFFSET; 
        lcb[lci] = 0; 
      }
      break; 
    case TYPE_CLOCK: 
      lci = VAR[st->u.act.lhs->u.atom.var_index].OFFSET; 
      if (VAR[st->u.act.rhs_exp->u.atom.var_index].PROC_INDEX) { 
        rci = VAR[st->u.act.rhs_exp->u.atom.var_index].OFFSET; 
        if (VAR[st->u.act.rhs_exp->u.atom.var_index].PROC_INDEX) { 
	  lcb[rci] = CLOCK_POS_INFINITY - 1; 
	}
	else if (lcb[lci] > lcb[rci]) 
	  lcb[rci] = lcb[lci]; 
      }
    } 
  }
}
  /* statement_local_clock_bound_analysis() */ 





  
local_clock_bound_analysis()
{
  int	mi, ipi, pi, ci, xi, ai, flag_change, lci, rci, itr; 

  lcb = (int *) malloc(LOCAL_COUNT[TYPE_CLOCK] * sizeof(int));

  for (mi = 0; mi < MODE_COUNT; mi++) { 
    MODE[mi].local_clock_bound = (int *) malloc(LOCAL_COUNT[TYPE_CLOCK] * sizeof(int)); 
    for (ci = 0; ci < LOCAL_COUNT[TYPE_CLOCK]; ci++) { 
      /* 
      fprintf(RED_OUT, "\ngotcha a, mi=%1d, ci=%1d\n", mi, ci); 
      fflush(RED_OUT); 
      */ 
      MODE[mi].local_clock_bound[ci] = 0; 
    } 

    MODE[mi].clock_bound 
    = ((struct process_clock_bound_type *) 
       malloc(PROCESS_COUNT * sizeof(struct process_clock_bound_type))
       ) - 1; 
    for (ipi = 0; ipi < MODE[mi].process_count; ipi++) { 
      pi = MODE[mi].process[ipi]; 
    /* 
      fprintf(RED_OUT, "\ngotcha a, mi=%1d, ci=%1d\n", mi, ci); 
      fflush(RED_OUT); 
      */ 
      
      MODE[mi].clock_bound[pi].bound 
      = collect_process_clock_bounds(
        MODE[mi].invariance[pi].red, 
        &(MODE[mi].clock_bound[pi].bound_count) 
      ); 
    } 
    /*
    for (ci = 0; ci < MODE[mi].timed_constraint_count; ci++) {
      adjust_local_clock_bound(mi, &(MODE[mi].timed_constraint[1][ci])); 
    }
    */
  }
  /*
  for (xi = 0; xi < XTION_COUNT; xi++) {
    if (valid_mode_index(XTION[xi].src_mode_index)) 
      for (ci = 0; ci < XTION[xi].timed_constraint_count; ci++) {
        adjust_local_clock_bound(XTION[xi].src_mode_index, &(XTION[xi].timed_constraint[1][ci])); 
      }
  } 
  */
  for (flag_change = TYPE_TRUE; flag_change;) { 
    flag_change = TYPE_FALSE; 

    for (xi = 1; xi < XTION_COUNT; xi++) { 
      for (ci = 0; ci < LOCAL_COUNT[TYPE_CLOCK]; ci++) {
	if (valid_mode_index(XTION[xi].dst_mode_index)) 
	  lcb[ci] = MODE[XTION[xi].dst_mode_index].local_clock_bound[ci]; 
      }

      statement_local_clock_bound_analysis(XTION[xi].statement); 

      if (valid_mode_index(XTION[xi].src_mode_index)) 
        for (ci = 0; ci < LOCAL_COUNT[TYPE_CLOCK]; ci++) { 
	  if (MODE[XTION[xi].src_mode_index].local_clock_bound[ci] < lcb[ci]) {
	    flag_change = TYPE_TRUE; 
	    MODE[XTION[xi].src_mode_index].local_clock_bound[ci] = lcb[ci]; 
	  }
        }
    }
  }

  free(lcb); 
  /*
  fprintf(RED_OUT, "\nMODE local clock bound\n"); 
  for (mi = 0; mi < MODE_COUNT; mi++) { 
    fprintf(RED_OUT, "MODE %1d:%s: ", mi, MODE[mi].name); 
    for (ci = 0; ci < LOCAL_COUNT[TYPE_CLOCK]; ci++) 
      fprintf(RED_OUT, "%s:%1d; ", VAR[variable_index[TYPE_CLOCK][1][ci]].NAME, MODE[mi].local_clock_bound[ci]); 

    fprintf(RED_OUT, "\n"); 
  } 
  */
}
/* local_clock_bound_analysis() */ 


int	XI_ENTRY_FILLIN; 
int	count_free_ps_st = 0; 

void	free_ps_st(pst)
     struct parse_statement_type	*pst;
{ 
  int					pi, i; 
  struct parse_statement_link_type	*stl, *stl_tmp; 
  
  if (pst == NULL) 
    return; 
/*
  fprintf(RED_OUT, "\nfpst %1d, ", ++count_free_ps_st); 
  print_parse_statement_line(pst); 
  fprintf(RED_OUT, "\n"); 
*/  
  switch (pst->op) { 
  case UNCHANGED: 
    break; 
  case ST_IF: 
    free_ps_st(pst->u.branch.if_statement); 
    if (pst->st_status & FLAG_STATEMENT_ELSE) 
      free_ps_st(pst->u.branch.else_statement); 
//    free_ps_exptree(pst->u.branch.cond); 
    break; 
  case ST_WHILE: 
    free_ps_st(pst->u.loop.statement); 
//    free_ps_exptree(pst->u.loop.cond);     
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  case ST_SEQ: 
    #ifdef RED_DEBUG_PARSE_MODE
    fprintf(RED_OUT, "free ps st seq\n"); 
    #endif 
    
    for (i = 0, stl = pst->u.seq.statement_list; 
	 stl; 
	 stl_tmp = stl, 
	 stl = stl->next_parse_statement_link, 
	 i++, 
	 free(stl_tmp)
	 ) { 
      #ifdef RED_DEBUG_PARSE_MODE
      fprintf(RED_OUT, "free i:%1d\n", i); 
      #endif 
      
      free_ps_st(stl->statement);  
    } 
    break; 
  case ST_GUARD: 
    break; 
  case ST_ERASE: 
  
    break; 
  default: 
/*  The release of the term array is to be done in free_statement 
    since rec_statement_fillin() directly copies the array to 
    statement_type. 
    
    if (pst->u.act.lhs) 
      free_ps_exp(pst->u.act.lhs); 
    if (pst->u.act.rhs_exp) 
      free_ps_exp(pst->u.act.rhs_exp); 
    if (pst->u.act.offset) 
      free_ps_exp(pst->u.act.offset); 
    for (i = 0; i < pst->u.act.term_count; i++) {
      free_ps_exp(pst->u.act.term[i].coeff); 
      free_ps_exp(pst->u.act.term[i].operand); 
    }
    free(pst->u.act.term); 
*/
    break; 
  } 
  free(pst); 
  return; 
}
  /* free_ps_st() */ 




#ifdef RED_DEBUG_PARSE_MODE 
int count_action_fillin = 0; 
#endif 

/* Note that I removed the statement that changes the flag_qfd_sync of xtion according to 
 * each act.   
 * Please check whether we need to add that back in assignment_analyze(). 
 */
struct statement_type	*action_fillin(
  struct parse_statement_type	*pst 
) { 
  struct statement_type	*st; 
  int			pi, ti; 
  
/* 
  fprintf(RED_OUT, 
    "\nAction fillin %1d\n", ++count_action_fillin
  ); 
*/
  st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
  if (   pst->op >= ASSIGN_CLOCK_CONSTANT  
      && pst->op <= ASSIGN_CLOCK_DIFFERENCE_MIXED 
      && (GSTATUS[INDEX_SYSTEM_TYPE] & FLAG_SYSTEM_HYBRID)
      )
    st->op = ASSIGN_HYBRID_EXP;
  else
    st->op = pst->op;
  st->st_status = pst->st_status;
  if (pst->u.act.lhs) 
    var_index_fillin(pst->u.act.lhs); 
  st->u.act.lhs = pst->u.act.lhs;
  st->u.act.rhs_exp = pst->u.act.rhs_exp;
  st->u.act.term_count = pst->u.act.term_count; 
  st->u.act.term = pst->u.act.term; 
  for (ti = 0; ti < st->u.act.term_count; ti++) { 
    var_index_fillin(st->u.act.term[ti].operand); 	
  } 
  st->u.act.offset = pst->u.act.offset; 
  if (st->u.act.rhs_exp)
    var_index_fillin(pst->u.act.rhs_exp); 

  XTION[XI_ENTRY_FILLIN].status = XTION[XI_ENTRY_FILLIN].status | FLAG_CLOCK_RESET;
  if (   pst->u.act.lhs 
      && pst->u.act.lhs->type != TYPE_REFERENCE 
      && !pst->u.act.lhs->u.atom.var
      ) {
    fprintf(RED_OUT, "\nBug: pst->u.act.lhs->u.atom.var cannot be null\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
/*
    else if (pst->u.act.lhs->u.atom.var->status & FLAG_LOCAL_VARIABLE) { 
      if (   pst->u.act.lhs->u.atom.indirect_count == 0
	  && pst->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_CONSTANT
	  ) { 
        st->u.act.lhs->u.atom.var_index
	= variable_index[pst->u.act.lhs->u.atom.var->type][pst->u.act.lhs->u.atom.exp_base_proc_index->u.value][pst->u.act.lhs->u.atom.var->index];
      }
      else 
        st->u.act.lhs->u.atom.var_index
	= variable_index[pst->u.act.lhs->u.atom.var->type][1][pst->u.act.lhs->u.atom.var->index];
    else 
      st->u.act.lhs->u.atom.var_index
      = variable_index[pst->u.act.lhs->u.atom.var->type][0][pst->u.act.lhs->u.atom.var->index];
    print_cpu_time("after action allocation");
*/

/*
    fprintf(RED_OUT, " :: xef_count = %1d.\n", ++xef_count); 
    fflush(RED_OUT); 
*/    
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("before indirect ref for an action");
  #endif 
/*
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    fillin_indirect_reference(pi, st->u.act.lhs);
    if (st->u.act.rhs_exp)
      fillin_indirect_reference(pi, st->u.act.rhs_exp);
    for (ti = 0; ti < st->u.act.term_count; ti++) 
      fillin_indirect_reference(pi, st->u.act.term[ti].operand); 
    if (st->u.act.offset) 
      fillin_indirect_reference(pi, st->u.act.offset);
  }
*/
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after indirect ref for an action");
  #endif 
    /* Now set up the offset and single coeff */
/*
    fprintf(RED_OUT, " >> xef_count = %1d at xi=%1d, ai = %1d.\n", 
	    xef_count, xi, head
	    ); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, " ^^^^ XTION[xi=%1d].head[head=%1d].type == %1d\n", 
	    xi, head, st->u.act.type
	    ); 
    fprintf(RED_OUT, "      XTION[xi=%1d].head[head=%1d].rhs_exp->type == %1d\n", 
	    xi, head, st->u.act.rhs_exp->type
	    ); 
    fflush(RED_OUT); 
*/
  
  switch (st->op) { 
  case ASSIGN_DISCRETE_CONSTANT: 
    st->u.act.term = NULL;
    st->u.act.term_count = 0; 
    st->u.act.offset = NULL;
    st->u.act.single_coeff_numerator = NULL; 
    st->u.act.single_coeff_denominator = NULL; 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) {
    case FLAG_ACTION_OFFSET_CONSTANT: 
      st->u.act.offset_numerator = (int *) pst->u.act.rhs_exp->u.value;
      st->u.act.offset_denominator = (int *) 1; 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      st->u.act.offset_numerator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      st->u.act.offset_denominator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      for (pi = 1; pi <= PROCESS_COUNT; pi++) {
	get_rationals(pst->u.act.rhs_exp, pi,
		      &(st->u.act.offset_numerator[pi]),
		      &(st->u.act.offset_denominator[pi])
		      );
      }
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
      get_rationals(pst->u.act.rhs_exp->u.interval.lbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.offset_numerator = (int *) pi;
      st->u.act.offset_denominator = (int *) ti; 
      get_rationals(pst->u.act.rhs_exp->u.interval.rbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.single_coeff_numerator = (int *) pi; 
      st->u.act.single_coeff_denominator = (int *) ti; 
      break; 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL:  
      break; 
    }
    break; 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    st->u.act.term = NULL;
    st->u.act.term_count = 0; 
    st->u.act.offset = NULL;
    st->u.act.single_coeff_numerator = NULL; 
    st->u.act.single_coeff_denominator = NULL; 
    break; 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) {
    case FLAG_ACTION_OFFSET_CONSTANT: 
      st->u.act.offset_numerator = (int *) pst->u.act.rhs_exp->u.value;
      st->u.act.offset_denominator = (int *) 1; 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      st->u.act.offset_numerator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      st->u.act.offset_denominator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      for (pi = 1; pi <= PROCESS_COUNT; pi++) {
	get_rationals(pst->u.act.rhs_exp, pi,
		      &(st->u.act.offset_numerator[pi]),
		      &(st->u.act.offset_denominator[pi])
		      );
      }
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
      get_rationals(pst->u.act.rhs_exp->u.interval.lbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.offset_numerator = (int *) pi;
      st->u.act.offset_denominator = (int *) ti; 
      get_rationals(pst->u.act.rhs_exp->u.interval.rbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.single_coeff_numerator = (int *) pi; 
      st->u.act.single_coeff_denominator = (int *) ti; 
      break; 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL: 
      fprintf(RED_OUT, "Error: mismatch in assignment and offset type.\n"); 
      fflush(RED_OUT); 
      bk(0);  
      break; 
    }
    break; 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    break; 

  case ASSIGN_HYBRID_EXP: 
    st->u.act.single_coeff_numerator = NULL; 
    st->u.act.single_coeff_denominator = NULL; 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) {
    case FLAG_ACTION_OFFSET_CONSTANT: 
      st->u.act.offset_numerator = (int *) pst->u.act.rhs_exp->u.value;
      st->u.act.offset_denominator = (int *) 1; 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      st->u.act.offset_numerator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      st->u.act.offset_denominator 
      = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      for (pi = 1; pi <= PROCESS_COUNT; pi++) {
	get_rationals(pst->u.act.rhs_exp, pi,
		      &(st->u.act.offset_numerator[pi]),
		      &(st->u.act.offset_denominator[pi])
		      );
      }
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
      get_rationals(pst->u.act.rhs_exp->u.interval.lbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.offset_numerator = (int *) pi;
      st->u.act.offset_denominator = (int *) ti; 
      get_rationals(pst->u.act.rhs_exp->u.interval.rbound_exp, 0,
		    &pi,
		    &ti
		    );
      st->u.act.single_coeff_numerator = (int *) pi; 
      st->u.act.single_coeff_denominator = (int *) ti; 
      break; 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL:  
      break; 
    }
    break; 

  case ASSIGN_TRASH: 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    st->u.act.term = NULL;
    st->u.act.term_count = 0; 
    st->u.act.offset = NULL;
    st->u.act.single_coeff_numerator = NULL; 
    st->u.act.single_coeff_denominator = NULL; 
    switch (st->st_status & MASK_ACTION_OFFSET_TYPE) {
    case FLAG_ACTION_OFFSET_CONSTANT: 
      st->u.act.offset_numerator = (int *) pst->u.act.rhs_exp->u.value;
      st->u.act.offset_denominator = (int *) 1; 
      break; 
    case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
      st->u.act.offset_numerator = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      st->u.act.offset_denominator = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
      for (pi = 1; pi <= PROCESS_COUNT; pi++) {
	get_rationals(pst->u.act.rhs_exp, pi,
		      &(st->u.act.offset_numerator[pi]),
		      &(st->u.act.offset_denominator[pi])
		      );
      }
      break; 
    case FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL:  
      st->u.act.offset_numerator = NULL;
      st->u.act.offset_denominator = NULL;
      break; 
    case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
      fprintf(RED_OUT, "Error: Illegal increment types:\n"); 
      pcform(st->u.act.rhs_exp); 
      fflush(RED_OUT); 
      bk(0); 
      break; 
    }
    break; 
  } 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, 
    "\nAction_fillin %1d:st->status %x\n", 
    ++count_action_fillin, st->status 
  ); 
  print_statement_line(st, 1); 
  fflush(RED_OUT); 
  #endif 
  
  return(st); 
}
  /* action_fillin() */ 
  



struct statement_type	*rec_statement_fillin(pst)
     struct parse_statement_type	*pst;
{ 
  struct statement_type			*st, *st2, **stptr; 
  int					pi, i; 
  struct parse_statement_link_type	*stl; 
  
  if (pst == NULL) 
    return(NULL); 
    
  switch (pst->op) { 
  case UNCHANGED: 
    return(NULL); 
  case ST_IF: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst; 
  
    st->u.branch.if_statement = rec_statement_fillin(pst->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      st->u.branch.else_statement = rec_statement_fillin(pst->u.branch.else_statement); 
    else 
      st->u.branch.else_statement = NULL; 
    var_index_fillin(pst->u.branch.cond); 
    st->u.branch.red_cond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    st->u.branch.red_uncond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
//      fillin_indirect_reference(pi, pst->u.branch.cond);     
      st->u.branch.red_cond[pi] = red_local(pst->u.branch.cond, pi, 0); 
      st->u.branch.red_uncond[pi] = red_complement(st->u.branch.red_cond[pi]); 
      red_mark(st->u.branch.red_cond[pi], FLAG_GC_STABLE); 
      red_mark(st->u.branch.red_uncond[pi], FLAG_GC_STABLE); 
    } 
    st->u.branch.parse_cond_exp = pst->u.branch.cond; 
    return(st); 
    break; 
  case ST_WHILE: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst; 

    st->u.loop.statement = rec_statement_fillin(pst->u.loop.statement); 
    var_index_fillin(pst->u.loop.cond); 
    st->u.loop.red_cond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    st->u.loop.red_uncond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    st->u.loop.red_gfp = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
//      fillin_indirect_reference(pi, pst->u.loop.cond);     
      st->u.loop.red_gfp[pi] = NULL; 
      st->u.loop.red_cond[pi] = red_local(pst->u.loop.cond, pi, 0); 
      st->u.loop.red_uncond[pi] = red_complement(st->u.loop.red_cond[pi]); 
      red_mark(st->u.loop.red_cond[pi], FLAG_GC_STABLE); 
      red_mark(st->u.loop.red_uncond[pi], FLAG_GC_STABLE); 
    } 
    st->u.loop.parse_cond_exp = pst->u.loop.cond; 
    return(st); 
    break; 
  case ST_SEQ: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst; 
  
    st->u.seq.count = pst->u.seq.statement_count; 
    st->u.seq.statement = (struct statement_type **) 
	malloc(st->u.seq.count * sizeof(struct statement_type *)); 
    for (i = 0, stl = pst->u.seq.statement_list; 
	 stl; 
	 stl = stl->next_parse_statement_link
	 ) { 
      st->u.seq.statement[i] = rec_statement_fillin(stl->statement);  
      if (st->u.seq.statement[i]) { 
      	i++; 
      } 
    } 
    if (i == 1) { 
      st2 = st; 
      st = st->u.seq.statement[0]; 
      free(st2->u.seq.statement); 
      free(st2);  
    } 
    else if (i < st->u.seq.count) { 
      stptr = st->u.seq.statement; 
      st->u.seq.count = i; 
      st->u.seq.statement = (struct statement_type **) 
	malloc(st->u.seq.count * sizeof(struct statement_type *)); 
      for (i = 0; i < st->u.seq.count; i++) 
        st->u.seq.statement[i] = stptr[i]; 
      free(stptr); 
    } 
    return(st); 
    break; 
  case ST_CALL: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst;
    st->u.call.call_mode_index = pst->u.call.call_mode_index; 
    st->u.call.ret_mode_index = pst->u.call.ret_mode_index; 
    return(st); 
    break;  
  
  case ST_RETURN: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst; 
    return(st); 
    break; 

  case ST_CPLUG: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst;     
    st->u.cplug.lhs = pst->u.cplug.lhs; 
    st->u.cplug.cmod_index = pst->u.cplug.cmod_index; 
    st->u.cplug.cproc_index = pst->u.cplug.cproc_index; 
    return(st); 
  
  case ST_GUARD: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst;     
    var_index_fillin(pst->u.guard.cond); 
    st->u.guard.red_cond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    st->u.guard.red_uncond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
//      fillin_indirect_reference(pi, pst->u.loop.cond);     
      st->u.guard.red_cond[pi] = red_local(pst->u.guard.cond, pi, 0); 
      st->u.guard.red_uncond[pi] = red_complement(st->u.guard.red_cond[pi]); 
      red_mark(st->u.guard.red_cond[pi], FLAG_GC_STABLE); 
      red_mark(st->u.guard.red_uncond[pi], FLAG_GC_STABLE); 
    } 
    st->u.guard.cond = pst->u.guard.cond; 
    return(st); 
     break; 
  case ST_ERASE: 
    st = (struct statement_type *) malloc(sizeof(struct statement_type)); 
    st->op = pst->op; 
    st->st_status = pst->st_status; 
    st->parse_statement = pst;     
    var_index_fillin(pst->u.erase.var); 
    st->u.erase.var = pst->u.erase.var;
    return(st); 
    break; 
  default: 
    st = action_fillin(pst);  
    st->st_status = pst->st_status; 
    st->parse_statement = pst; 
    return(st); 
    break; 
  } 
}
  /* rec_statement_fillin() */ 


  
  


int 	exp_global_effect(psub)
     struct ps_exp_type	*psub; 
{
  int				i, jj, pi, flag; 
  struct ps_bunit_type		*pbu; 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER: 
  case TYPE_TRASH: 
  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_CONSTANT: 
    return(0); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(exp_global_effect(psub->u.exp)); 

  case TYPE_DENSE: 
    if (   VAR[psub->u.atom.var_index].PROC_INDEX == 0
        && (VAR[psub->u.atom.var_index].STATUS & FLAG_VAR_STATIC) 
        ) 
    // Filter out the static parameter cases. 
      return(0); 

  case TYPE_DISCRETE: 
  case TYPE_CLOCK: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
    if (VAR[psub->u.atom.var_index].PROC_INDEX == 0) { 
      return(FLAG_XTION_SRC_GLOBAL_READING | FLAG_XTION_DST_GLOBAL_READING); 
    } 
    else if (   VAR[psub->u.atom.var_index].PROC_INDEX
             && psub->u.atom.exp_base_proc_index->type 
                != TYPE_LOCAL_IDENTIFIER
             ) 
      return(FLAG_XTION_SRC_PEER_READING | FLAG_XTION_DST_PEER_READING); 
    else 
      return(0); 
    break; 

  case BIT_NOT: 
    return(exp_global_effect(psub->u.exp)); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:  
  case ARITH_EQ : 
  case ARITH_NEQ : 
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    return(  exp_global_effect(psub->u.arith.lhs_exp) 
           | exp_global_effect(psub->u.arith.rhs_exp)
           ); 
  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    flag = 0; 
    for (i = 0; i < psub->u.ineq.term_count; i++) { 
      flag = flag 
      | exp_global_effect(psub->u.ineq.term[i].coeff) 
      | exp_global_effect(psub->u.ineq.term[i].operand); 
    } 
    flag = flag | exp_global_effect(psub->u.ineq.offset); 
    return(flag); 

  case ARITH_CONDITIONAL: 
    return(
      exp_global_effect(psub->u.arith_cond.cond)
    | exp_global_effect(psub->u.arith_cond.if_exp)
    | exp_global_effect(psub->u.arith_cond.else_exp)
    ); 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    flag = 0; 
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist;  
	 jj; 
	 jj--, pbu = pbu->bnext
	 ) {
      flag = flag | exp_global_effect(pbu->subexp); 
    }
    return (flag);

  case FORALL: 
  case EXISTS: 
    return(exp_global_effect(psub->u.qexp.child)); 
 
  case RED: 
    if (psub == PS_EXP_TRUE || psub == PS_EXP_FALSE) 
      return(0); 
      
  case EXISTS_ALWAYS: 
  case FORALL_ALWAYS:
  case FORALL_EVENTUALLY:
  case FORALL_CHANGE:
  case EXISTS_EVENTUALLY:
  case EXISTS_CHANGE:
  case FORALL_EVENT: 
  case EXISTS_UNTIL:
  case FORALL_UNTIL:
    fprintf(RED_OUT, "\nexp_global_effect: How come there is still a FORALL UNTIL in the specification ?\n"); 
    fflush(RED_OUT); 
    bk(0); 
    for (; 1; ); 
    return; 
  }
}
  /* exp_global_effect() */ 


/*
int	xfge_count = 0; 
*/
int	xtion_fillin_global_effect(st) 
	struct statement_type	*st; 
{ 
  int	i, flag, lvi, rvi; 
/*
  fprintf(RED_OUT, "xfge_count=%1d, st=%x\n", ++xfge_count, st); 
  fflush(RED_OUT); 
  for (; xfge_count == 15; ) ; 
*/
  if (!st) 
    return(0); 
    
  switch (st->op) { 
  case UNCHANGED: 
    return(0); 
  case ST_IF: 
    flag = xtion_fillin_global_effect(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      flag = flag | xtion_fillin_global_effect(st->u.branch.else_statement);  
    } 
    return(flag); 
    break; 
  case ST_WHILE: 
    return(xtion_fillin_global_effect(st->u.loop.statement)); 
    break; 
  case ST_SEQ: 
    for (i = 0, flag = 0; i < st->u.seq.count; i++) { 
      flag = flag | xtion_fillin_global_effect(st->u.seq.statement[i]); 
    } 
    return(flag); 
    break; 
  
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    return(0); 
    break; 

  case ST_GUARD: 
    return(0); 
    break; 
    
  case ST_ERASE: 
    flag = 0; 
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      flag = flag | FLAG_GLOBAL_EFFECT | FLAG_XTION_GLOBAL_WRITING;
    } 
    else if (   VAR[lvi].PROC_INDEX 
             && st->u.erase.var->u.atom.exp_base_proc_index->type 
                != TYPE_LOCAL_IDENTIFIER
             )
      flag = flag | FLAG_GLOBAL_EFFECT | FLAG_XTION_PEER_WRITING; 
    return(flag); 
    break; 
   
  default: 
/*
#define MASK_XTION_SIDE_EFFECTS			(0xFF00000) 
#define FLAG_XTION_GLOBAL_WRITING		(0x0100000)
#define	FLAG_XTION_SRC_GLOBAL_READING		(0x0200000) 
#define	FLAG_XTION_DST_GLOBAL_READING		(0x0400000) 

#define FLAG_XTION_PEER_WRITING			(0X0800000) 
#define FLAG_XTION_SRC_PEER_READING		(0x1000000) 
#define FLAG_XTION_DST_PEER_READING		(0x2000000) 

#define	FLAG_XTION_FWD_ACTION_INV_INTERFERE	(0x4000000)
#define	FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE	(0x8000000)
*/
    if (st->u.act.lhs == NULL) 
      return(0); 
    else if (st->u.act.lhs->type == TYPE_REFERENCE
//              || st->u.act.lhs->u.atom.indirect_count > 0 
             ) { 
      return(FLAG_GLOBAL_EFFECT | FLAG_XTION_GLOBAL_WRITING);
    } 
    flag = 0; 
    lvi = st->u.act.lhs->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      flag = flag | FLAG_GLOBAL_EFFECT | FLAG_XTION_GLOBAL_WRITING;
    } 
    else if (   VAR[lvi].PROC_INDEX 
             && st->u.act.lhs->u.atom.exp_base_proc_index->type 
                != TYPE_LOCAL_IDENTIFIER
             )
      flag = flag | FLAG_GLOBAL_EFFECT | FLAG_XTION_PEER_WRITING; 
    return(flag); 
  }
} 
  /* xtion_fillin_global_effect() */ 




  
void	red_event_sets(int xi) {
  int	pi, si, vi; 
  
  XTION[xi].red_events = ((struct red_type **) 
    malloc(PROCESS_COUNT * sizeof(struct red_type *))
  ) - 1; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    XTION[xi].red_events[pi] = NORM_NO_RESTRICTION; 
    for (si = 0; si < XTION[xi].sync_count; si++) { 
      vi = XTION[xi].sync[si].sync_index; 
      vi = variable_index[TYPE_SYNCHRONIZER][pi][vi]; 
      XTION[xi].red_events[pi] = bdd_one_constraint(
        XTION[xi].red_events[pi], vi, TYPE_TRUE
      ); 
    } 
    red_mark(XTION[xi].red_events[pi], FLAG_GC_STABLE);
  }
}
  /* red_event_sets() */
  
  



int	FLAG_ROLE_ADD_EVENTS; 
  
struct red_type	*rec_add_events(d)
     struct red_type	*d;
{
  int				ci, xi;
  struct red_type		*child, *result, *sub;
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE 
      )
    return(d);

  ce = cache2_check_result_key(
    OP_ADD_ROLE_EVENTS, d, 
    (struct red_type *) FLAG_ROLE_ADD_EVENTS
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    if (PROCESS[VAR[d->var_index].PROC_INDEX].status & FLAG_ROLE_ADD_EVENTS) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]); 
        child = NORM_FALSE; 
        for (xi = ic->lower_bound; xi <= ic->upper_bound; xi++) { 
          sub = ddd_one_constraint(
            XTION[xi].red_events[VAR[d->var_index].PROC_INDEX], 
            d->var_index, xi, xi 
          ); 
          child = red_bop(OR, child, sub); 
        } 
        child = red_bop(AND, child, rec_add_events(ic->child));
        result = red_bop(OR, result, child);
      }
    } 
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_add_events(ic->child);
        result = red_bop(OR, result, child);
      }
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    child = bdd_one_constraint(
      rec_add_events(d->u.bdd.zero_child), 
      d->var_index, TYPE_FALSE
    );
    result = red_bop(OR, child, 
      bdd_one_constraint(
        rec_add_events(d->u.bdd.one_child), 
        d->var_index, TYPE_TRUE
    ) );
    break; 

  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_add_events(bc->child);
      child = crd_lone_subtree(child, d->var_index, bc->upper_bound);
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_HRD: 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      hc = &(d->u.hrd.arc[ci]);
      child = hrd_lone_subtree(rec_add_events(hc->child),
	d->var_index, d->u.hrd.hrd_exp,
	hc->ub_numerator, hc->ub_denominator
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_add_events(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, 
        d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_add_events(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, 
        d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_add_events(ic->child);
      child = ddd_one_constraint(child, 
        d->var_index, ic->lower_bound, ic->upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result); 
}
  /* rec_add_events() */





struct red_type	*red_add_events(d, flag_role) 
  struct red_type	*d; 
  int			flag_role; 
{
  struct red_type	*result;

  FLAG_ROLE_ADD_EVENTS = flag_role; 
  result = rec_add_events(d); 

  return(result); 
}
  /* red_add_events() */ 
  
 
 
 
 
 
struct red_type	*red_no_event_set_range( 
  struct red_type	*events, 
  int			parent_vi 
) { 
  int	pi, si, vi, pi_ub, vi_oub; 

  if (events == NORM_NO_RESTRICTION) { 
    pi_ub = PROCESS_COUNT; 
    vi_oub = VARIABLE_COUNT; 
  } 
  else { 
    pi_ub = VAR[events->var_index].PROC_INDEX; 
    vi_oub = events->var_index; 
  } 
  for (pi = pi_ub; pi >= VAR[parent_vi].PROC_INDEX; pi--) {
    for (si = GLOBAL_COUNT[TYPE_SYNCHRONIZER]-1; si >= 0; si--) {
      vi = variable_index[TYPE_SYNCHRONIZER][pi][si]; 
      if (vi <= parent_vi) 
        break; 
      else if (vi >= vi_oub) 
        continue; 
      events = bdd_lone_subtree(events, vi, TYPE_FALSE); 
    } 
  }
  return(events); 
} 
  /* red_no_event_set_range() */ 




struct red_type	*rec_no_event_set(
  struct red_type	*events, 
  int			parent_vi  
) {
  struct red_type	*result, *conj; 
  int			pi, si, vi, ci; 
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (events == NORM_FALSE) 
    return(events); 
      
  rec = rec_new(events, (struct red_type *) parent_vi); 
  nrec = (struct rec_type *) add_23tree(
    rec, parse_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  }
  
  switch (VAR[events->var_index].TYPE) { 
  case TYPE_TRUE: 
    result = NORM_NO_RESTRICTION; 
    break; 
  case TYPE_SYNCHRONIZER: 
    if (   VAR[events->var_index].PROC_INDEX > 0 
        && VAR[events->var_index].PROC_INDEX <= PROCESS_COUNT 
        ) { 
      result = bdd_new(events->var_index, 
        rec_no_event_set(events->u.bdd.zero_child, events->var_index), 
        rec_no_event_set(events->u.bdd.one_child, events->var_index)
      ); 
    } 
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal global event %s in event decision diagram.\n", 
        VAR[events->var_index].NAME
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    break; 
  default: 
    result = NORM_FALSE; 
    for (ci = events->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(events->u.ddd.arc[ci]);
      conj = rec_no_event_set(ic->child, events->var_index);
      conj = ddd_lone_subtree(conj, events->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, conj);
    } 
    break; 
  }  

  result = red_no_event_set_range(result, parent_vi); 
  return(rec->result = result);
}
/* rec_no_event_set() */




struct red_type	*red_no_event_set(
  struct red_type	*events 
) {
  struct red_type	*result; 

  init_23tree(&parse_tree);
  result = rec_no_event_set(
    events, variable_index[TYPE_XTION_INSTANCE][1][0]
  );
  free_entire_23tree(parse_tree, rec_free);

  return(result);
}
/* red_no_event_set() */




struct ps_exp_type	XSUB;
/*
int			xef_count = 0; 
*/
struct xtion_type	*xtion_entry_fillin(px)
     struct parse_xtion_type	*px;
{
  struct parse_assignment_type		*as;
  int					ai, pi, xi, reset_count, i, head, tail, 
					lvi, lci, lhs_pi, rvi, rci,
					rhs_pi, flag, lppi,llvi;
  struct parse_indirect_type		*pt;
  struct red_type			*lconj, *lchild, *rconj, *rchild, *result, *effect;
  struct ps_exp_type			tsub, tlhs_sub, trhs_sub;
  struct parse_stream_operation_type	*sl; 
  struct parse_xtion_sync_type		*pxs; 
  struct ps_bunit_type			*pb; 
/*
  fprintf(RED_OUT, "\n===========================\n");
  print_parse_xtion(px, 0);
*/
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("Entering xtion entry fillin for xi=%1d", px->index);
  #endif 
  
  XI_ENTRY_FILLIN = xi = px->index;
  XTION[xi].index = xi; 
  XTION[xi].status = px->status; 
  XTION[xi].src_lines = px->src_lines; 
/*
  fprintf(RED_OUT, "At the beginning of xtion_entry_fillin:\n"); 
  fprintf(RED_OUT, "px %1d -> status = %x.\n", px->index, px->status); 
  fprintf(RED_OUT, "1. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
  fflush(RED_OUT); 
*/
  XTION[xi].src_mode_index = px->src_mode_index;
  XTION[xi].dst_mode_index = px->dst_mode_index;
  
  XTION[xi].stream_operation_count = px->stream_operation_count; 
  XTION[xi].stream_operation = (struct stream_operation_type *) malloc(
    px->stream_operation_count * sizeof(struct stream_operation_type)
  ); 
  for (ai = 0, sl = px->stream_operation_list; 
       ai < XTION[xi].stream_operation_count; 
       ai++, sl = sl->next_parse_stream_operation 
       ) { 
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\nxef: xi=%1d, soc = %1d, soi=%1d, so-op=%1d.\n", 
      xi, XTION[xi].stream_operation_count, ai, sl->operation 
    ); 
    fflush(RED_OUT); 
    #endif 

    if (sl->stream)
      XTION[xi].stream_operation[ai].stream 
      = variable_index[TYPE_STREAM][0][sl->stream->index]; 
    else 
      XTION[xi].stream_operation[ai].stream = 0; 

    XTION[xi].stream_operation[ai].operation = sl->operation; 	
    XTION[xi].stream_operation[ai].var = sl->var; 
    if (XTION[xi].stream_operation[ai].var)
      var_index_fillin(XTION[xi].stream_operation[ai].var); 
    XTION[xi].stream_operation[ai].value_exp = sl->value_exp; 
    if (XTION[xi].stream_operation[ai].value_exp)
      var_index_fillin(XTION[xi].stream_operation[ai].value_exp); 
  } 
  XTION[xi].sync_count = px->sync_count;
  XTION[xi].sync = (struct sync_var_type *)
    malloc(px->sync_count * sizeof(struct sync_var_type));
  for (pxs = px->sync_list; pxs; pxs = pxs->next_parse_xtion_sync) { 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] & ~FLAG_NO_SYNCHRONIZERS;
    i = pxs->place_index; 
    ai = XTION[xi].sync[i].sync_index = pxs->sync_var->index; 
    XTION[xi].sync[i].type = pxs->type;
    XTION[xi].sync[i].status = pxs->status; 
    XTION[xi].sync[i].exp_quantification = pxs->exp_quantification; 
    if (XTION[xi].sync[i].exp_quantification)
      var_index_fillin(XTION[xi].sync[i].exp_quantification); 
    
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n=========================================\n"); 
    fprintf(RED_OUT, 
      "\nparse: x %1d, sync %1d, ai=%1d:%s, type %1d, status %1d\n", 
      xi, i, ai, pxs->sync_var->name, 
      XTION[xi].sync[i].type, XTION[xi].sync[i].status 
    ); 
    if (pxs->exp_quantification) 
      pcform(pxs->exp_quantification); 
    fflush(RED_OUT); 
    #endif 

    if (pxs->qsync_var) {
      XTION[xi].sync[i].qsync_vi = variable_index[TYPE_POINTER][1][pxs->qsync_var->index]; 
    }
    else 
      XTION[xi].sync[i].qsync_vi = -1; 
    if (XTION[xi].sync[i].type > 0 /* ? */) { 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "xi=%1d, si=%1d, ai=%1d:%s, qxc=%1d.\n", 
        xi, i, ai, pxs->sync_var->name, GSYNC[ai].Q_XTION_COUNT 
      ); 
      fprintf(RED_OUT, 
        "\nGSYNC[%1d].Q_XTION[%1d]={XTION_INDEX=%1d, PLACE_INDEX=%1d}\n", 
        ai, GSYNC[ai].Q_XTION_COUNT, xi, pxs->place_index
      ); 
      fflush(RED_OUT); 
      #endif 
      
      GSYNC[ai].Q_XTION[GSYNC[ai].Q_XTION_COUNT].XTION_INDEX = xi;
      GSYNC[ai].Q_XTION[GSYNC[ai].Q_XTION_COUNT++].PLACE_INDEX 
      = pxs->place_index; 
    }
    else if (XTION[xi].sync[i].type < 0 /* ? */) {
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "xi=%1d, si=%1d, ai=%1d:%s, xxc=%1d.\n", 
        xi, i, ai, pxs->sync_var->name, GSYNC[ai].X_XTION_COUNT 
      ); 
      fprintf(RED_OUT, 
        "\nGSYNC[%1d].X_XTION[%1d]={XTION_INDEX=%1d, PLACE_INDEX=%1d}\n", 
        ai, GSYNC[ai].X_XTION_COUNT, xi, pxs->place_index
      ); 
      fflush(RED_OUT); 
      #endif 

      GSYNC[ai].X_XTION[GSYNC[ai].X_XTION_COUNT].XTION_INDEX = xi;
      GSYNC[ai].X_XTION[GSYNC[ai].X_XTION_COUNT++].PLACE_INDEX 
      = pxs->place_index;
    }
  }
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after Q sync fillin for xi=%1d", px->index);
  #endif 

  if (xi && XTION[xi].sync_count == 0)
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] & ~FLAG_ALL_SYNC_XTIONS;
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after X sync fillin for xi=%1d", px->index);
  #endif 

  XTION[xi].parse_xtion = px;
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\n2: In entry fillin for xi=%1d", px->index);
  print_parse_xtion(px, 0);
  #endif 

  var_index_fillin(px->trigger_exp);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("before filling in triggers for xi=%1d", px->index);
  #endif 
  
  XTION[xi].red_trigger = ((struct red_type **)
    malloc(PROCESS_COUNT * sizeof(struct red_type *))
  ) - 1;
  red_event_sets(xi);
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("before indirect ref for xi=%1d, pi=%1d in triggers", 
      px->index, pi
    );
    #endif 
//    fillin_indirect_reference(pi, px->trigger_exp);
    
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after indirect ref for xi=%1d, pi=%1d in triggers", 
      px->index, pi
    );
    #endif 

/*
    for (sl = px->stream_operation_list; 
         sl; 
         sl = sl->next_parse_stream_operation 
         ) { 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "\nxef: xi=%1d, soc = %1d, soi=%1d, so-op=%1d.\n", 
        xi, XTION[xi].stream_operation_count, ai, sl->operation 
      ); 
      fflush(RED_OUT); 
      #endif 

      if (sl->var)
        fillin_indirect_reference(pi, sl->var); 
      if (sl->value_exp)
        fillin_indirect_reference(pi, sl->value_exp); 
    } 
*/

    if (xi) 
      XTION[xi].red_trigger[pi] = NORM_FALSE;
    else 
      XTION[xi].red_trigger[pi] = NORM_NO_RESTRICTION;

    if (   valid_mode_index(XTION[xi].src_mode_index)
	&& (MODE[XTION[xi].src_mode_index].status & FLAG_MODE_URGENT)
	) {
      if (   valid_mode_index(XTION[xi].dst_mode_index)
      	  && (MODE[XTION[xi].dst_mode_index].status & FLAG_MODE_URGENT)
      	  ) {
	fprintf(RED_OUT, "\nError: Consecutive urgent modes which may lead to race condition \n");
	fprintf(RED_OUT, "       from mode %1d:%s to mode %1d:%s.\n",
		XTION[xi].src_mode_index, MODE[XTION[xi].src_mode_index].name,
		XTION[xi].dst_mode_index, MODE[XTION[xi].dst_mode_index].name
		);
	fflush(RED_OUT);
	exit(0);
      }
      /*
      else if (XTION[xi].timed_constraint_count) {
	fprintf(RED_OUT, "\nError: Timing constraint is not allowed in the triggering condition of transitions\n");
	fprintf(RED_OUT, "       from urgent mode %1d:%s to mode %1d:%s.\n",
		XTION[xi].src_mode_index, MODE[XTION[xi].src_mode_index].name,
		XTION[xi].dst_mode_index, MODE[XTION[xi].dst_mode_index].name
		);
	fflush(RED_OUT);
	exit(0);
      }
      */
    }
  }
  garbage_collect(FLAG_GC_SILENT);

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after filling in triggers for xi=%1d", px->index);
  #endif 

  /*
  for (reset_count = 0, as = px->assignment_list;
       as;
       as = as->next_parse_assignment
       ) {
    if (as->op == RESET_TO_ZERO)
      reset_count++;
  }
  */

  /*
  if (reset_count)
    XTION[xi].action_count = px->assignment_count - reset_count + 1;
  else
  */

  XTION[xi].statement = rec_statement_fillin(px->statement); 
/*
  if (XTION[xi].statement) {
    fprintf(RED_OUT, "XTION[%1d].statement->status=%x\n", 
      xi, XTION[xi].statement->status
    ); 
    fflush(RED_OUT); 
  }
  else {
    fprintf(RED_OUT, "XTION[%1d].statement NULL\n", 
      xi 
    ); 
    fflush(RED_OUT); 
  }
*/  
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after filling in statement for xi=%1d", px->index);
  #endif 
  /*
  if (reset_count) {
    XTION[xi].action[ai].op = RESET_TO_ZERO;
    XTION[xi].action[ai].lhs->u.atom.var = variable_index[TYPE_CLOCK][1][0];
    XTION[xi].action[ai].rhs_value = 0;
  }
  */
/*   print_cpu_time("after action fillin");
*/
  XTION[xi].status = XTION[xi].status 
  | xtion_fillin_global_effect(XTION[xi].statement); 
/*
  fprintf(RED_OUT, "2. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
  fflush(RED_OUT); 
*/
  if (xi == 0) 
    XTION[xi].status = XTION[xi].status & ~MASK_XTION_SIDE_EFFECTS; 
  else {
    switch (XTION[xi].src_mode_index) { 
    case MODE_NO_SPEC: 
    case MODE_DYNAMIC: 
      fprintf(RED_OUT, 
        "\nThat is weird since we have not allowed wild-card transitions.\n"
      ); 
      fprintf(RED_OUT, 
        "But now transition xi=%1d seems a wild-card transition.\n", xi
      ); 
      fflush(RED_OUT); 
      exit(0); 
      break; 

    default: 
      XTION[xi].status = XTION[xi].status 
      | (  (FLAG_XTION_SRC_GLOBAL_READING | FLAG_XTION_SRC_PEER_READING)
         & (  exp_global_effect(
                MODE[XTION[xi].src_mode_index].invariance_exp
              )
            | exp_global_effect(XTION[xi].parse_xtion->trigger_exp)
         )  ); 
      break; 
    }
/*
    fprintf(RED_OUT, "3. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
    fflush(RED_OUT); 
*/
    switch (XTION[xi].dst_mode_index) { 
    case MODE_NO_SPEC: 
      XTION[xi].status = XTION[xi].status 
      | (  (FLAG_XTION_SRC_GLOBAL_READING | FLAG_XTION_SRC_PEER_READING)
         & exp_global_effect(MODE[XTION[xi].src_mode_index].invariance_exp)
         ); 
      break; 
    case MODE_DYNAMIC: 
      XTION[xi].status = XTION[xi].status 
      | FLAG_XTION_DST_GLOBAL_READING 
      | FLAG_XTION_DST_PEER_READING; 
      break; 
    default: 
      XTION[xi].status = XTION[xi].status 
      | (  (FLAG_XTION_SRC_GLOBAL_READING | FLAG_XTION_SRC_PEER_READING)
         & exp_global_effect(MODE[XTION[xi].dst_mode_index].invariance_exp)
         ); 
      break; 
    }
/*
    fprintf(RED_OUT, "4. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
    fflush(RED_OUT); 
*/
    if (XTION[xi].status & FLAG_XTION_GLOBAL_WRITING) {
      if (XTION[xi].status & FLAG_XTION_SRC_GLOBAL_READING) 
        XTION[xi].status = XTION[xi].status 
        | FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE; 
/*
      fprintf(RED_OUT, "5. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
      fflush(RED_OUT); 
*/
      if (XTION[xi].status & FLAG_XTION_DST_GLOBAL_READING) 
        XTION[xi].status = XTION[xi].status 
        | FLAG_XTION_FWD_ACTION_INV_INTERFERE; 
/*
      fprintf(RED_OUT, "6. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
      fflush(RED_OUT); 
*/
    }
    if (XTION[xi].status & FLAG_XTION_PEER_WRITING) {
      if (XTION[xi].status & FLAG_XTION_SRC_PEER_READING) 
        XTION[xi].status = XTION[xi].status 
        | FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE; 
/*
      fprintf(RED_OUT, "7. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
      fflush(RED_OUT); 
*/
      if (XTION[xi].status & FLAG_XTION_DST_PEER_READING) 
        XTION[xi].status = XTION[xi].status 
        | FLAG_XTION_FWD_ACTION_INV_INTERFERE; 
/*
      fprintf(RED_OUT, "8. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
      fflush(RED_OUT); 
*/
  } }
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after global effect fillin for xi=%1d", px->index);
  #endif 
/*
  print_xtion(xi);
*/

/*
  fprintf(RED_OUT, "At the end of xtion_entry_fillin:\n"); 
  fprintf(RED_OUT, "px %1d -> status = %x.\n", px->index, px->status); 
  fprintf(RED_OUT, "end. XTION[xi=%1d].status = %x.\n", xi, XTION[xi].status);
  fflush(RED_OUT); 
*/
  return(&(XTION[xi])); 
}
/* xtion_entry_fillin() */




struct ps_exp_type	*txvar; 

xtion_fillin()
{
  struct parse_xtion_type	*px;
  struct index_link_type		**xp, *ip, *nip;
  int				xi, xj, pi, vi;

  txvar = (struct ps_exp_type *) 0x8afaee0; 
  
  ACTION_SAVE_RETMODE = (struct statement_type *) 
    malloc(sizeof(struct statement_type)); 
  ACTION_SAVE_RETMODE->op = ASSIGN_DISCRETE_POLYNOMIAL; 
  ACTION_SAVE_RETMODE->u.act.lhs = PS_EXP__RETMODE; 
  ACTION_SAVE_RETMODE->u.act.rhs_exp = NULL; 
  ACTION_SAVE_RETMODE->u.act.offset = NULL; 
  
  ACTION_RESUME_RETMODE = (struct statement_type *) 
    malloc(sizeof(struct statement_type)); 
  ACTION_RESUME_RETMODE->op = ASSIGN_DISCRETE_POLYNOMIAL; 
  ACTION_RESUME_RETMODE->u.act.lhs = PS_EXP_MODE; 
  ACTION_RESUME_RETMODE->u.act.rhs_exp = PS_EXP__RETMODE; 
  ACTION_RESUME_RETMODE->u.act.offset = PS_EXP__RETMODE; 
    
  XTION_COUNT = declare_xtion_count;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    vi = variable_index[TYPE_ACTION_INSTANCE][pi][0];
    VAR[vi].U.DISC.UB = 2*PROCESS_COUNT*XTION_COUNT;
  }
/*
  fprintf(RED_OUT, "\nbefore all xtion_entry_fillin().\n"); 
  print_gsyncs(); 
*/  
  XTION = (struct xtion_type *)
    malloc(XTION_COUNT * sizeof(struct xtion_type));
  for (px = declare_xtion_list; px; px = px->next_parse_xtion) {
    xtion_entry_fillin(px);
  } 
/*  
  fprintf(RED_OUT, "\nafter all xtion_entry_fillin().\n"); 
  print_gsyncs(); 
*/  
/*
  fprintf(RED_OUT, "\nafter all peer_xtion_entry_fillin().\n"); 
  print_gsyncs(); 
  */
}
/* xtion_fillin() */





/******************************************************************
* Routines for process fillin and xtion triggering condition fillin.
*/

int	PI_ADDRESS_AFFECTING; 

void	rec_collect_address_affecting(
  struct statement_type	*st
) {
  int	pi, pi_flag, 
	rvalue, rv_flag, 
	i, lvi; 
    
  if (!st) 
    return; 
  
  switch (st->op) { 
  case UNCHANGED: 
    return;  
  case ST_IF: 
    rec_collect_address_affecting(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      rec_collect_address_affecting(st->u.branch.else_statement); 
    } 
    return; 
    break; 
  case ST_WHILE: 
    rec_collect_address_affecting(st->u.loop.statement); 
    return; 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      rec_collect_address_affecting(st->u.seq.statement[i]); 
    } 
    return; 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  case ASSIGN_DISCRETE_CONSTANT:
    return;
  case ASSIGN_DISCRETE_POLYNOMIAL:
    if (st->u.act.lhs->type == TYPE_REFERENCE) { 
      return; 
    } 
    lvi = st->u.act.lhs->u.atom.var_index; 
    if (   VAR[lvi].TYPE != TYPE_DISCRETE 
        || VAR[lvi].PROC_INDEX <= 0 
        || VAR[lvi].OFFSET != OFFSET_MODE
        ) 
      return; 
    pi = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
      PI_ADDRESS_AFFECTING, &pi_flag
    ); 
    if (pi_flag == FLAG_SPECIFIC_VALUE && (pi < 1 || pi > PROCESS_COUNT)) {
      return; 
    } 
    if (   st->u.act.rhs_exp->type == TYPE_DISCRETE
        || st->u.act.rhs_exp->type == TYPE_CLOCK 
        || st->u.act.rhs_exp->type == TYPE_POINTER 
        || st->u.act.rhs_exp->type == TYPE_DENSE 
        || st->u.act.rhs_exp->type == TYPE_BDD 
        ) { 
      pi = get_value(st->u.act.rhs_exp->u.atom.exp_base_proc_index, 
        PI_ADDRESS_AFFECTING, &pi_flag
      ); 
      if (pi_flag == FLAG_SPECIFIC_VALUE) { 
      	lvi = st->u.act.rhs_exp->u.atom.var_index; 
      	if (pi >= 1 && pi <= PROCESS_COUNT) { 
      	  lvi = variable_index[TYPE_DISCRETE][pi][VAR[lvi].OFFSET]; 
      	  VAR[lvi].STATUS = VAR[lvi].STATUS | FLAG_ADDRESS_AFFECTING; 
      	} 
      } 
      else { 
      	for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	  lvi = variable_index[TYPE_DISCRETE][pi][VAR[lvi].OFFSET]; 
      	  VAR[lvi].STATUS = VAR[lvi].STATUS | FLAG_ADDRESS_AFFECTING; 
      	} 
      } 
    } 
    return;

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    return;

  case INCREMENT_BY_CONSTANT: 
    return;
  case DECREMENT_BY_CONSTANT:
    return;
  case ST_GUARD: 
    return; 
    
  case ST_ERASE:
    return;
    
  default: 
    fprintf(RED_OUT, 
      "\nrec_collect_address_affecting(): Error op=%1d\n", 
      st->op
    ); 
    exit(0); 
    break; 
  } 
}
  /* rec_collect_address_affecting() */ 





void	collect_all_address_affecting_variables() { 
  int	vi, pi, xi; 

  // We first clear all variables' records. 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_ADDRESS_AFFECTING; 	
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    VAR[variable_index[TYPE_DISCRETE][pi][OFFSET_MODE]].STATUS 
    = VAR[variable_index[TYPE_DISCRETE][pi][OFFSET_MODE]].STATUS
    | FLAG_ADDRESS_AFFECTING; 
    VAR[variable_index[TYPE_DISCRETE][pi][OFFSET__SP]].STATUS 
    = VAR[variable_index[TYPE_DISCRETE][pi][OFFSET__SP]].STATUS
    | FLAG_ADDRESS_AFFECTING; 
    for (xi = 1; xi < XTION_COUNT; xi++) {
      PI_ADDRESS_AFFECTING = pi; 
      rec_collect_address_affecting(XTION[xi].statement); 
    } 	
  } 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\n"); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    if (VAR[vi].STATUS & FLAG_ADDRESS_AFFECTING) { 
      fprintf(RED_OUT, "%1d:%s is address affecting.\n", 
        vi, VAR[vi].NAME
      ); 
    }
  } 
  fflush(RED_OUT); 
  #endif 
}
  /* collect_all_address_affecting_variables() */ 





struct a23tree_type	*aaff_tree; 

struct red_type	*rec_abstract_address_affecting(d)
     struct red_type	*d;
{
  int			ci, c1, c2;
  struct red_type	*child, *result;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, aaff_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      child = rec_abstract_address_affecting(d->u.crd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      child = rec_abstract_address_affecting(d->u.hrd.arc[ci].child);
      result = red_bop(OR, result, child);	
    }
    break;
  case TYPE_LAZY_EXP: 
    result = red_bop(OR, 
      rec_abstract_address_affecting(d->u.lazy.false_child), 
      rec_abstract_address_affecting(d->u.lazy.true_child) 
    ); 
    break; 

  case TYPE_FLOAT:
    if (VAR[d->var_index].STATUS & FLAG_ADDRESS_AFFECTING) { 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.fdd.arc[ci].child);
        child = fdd_one_constraint(child, d->var_index, 
          d->u.fdd.arc[ci].lower_bound, 
          d->u.fdd.arc[ci].upper_bound
        ); 
        result = red_bop(OR, result, child); 
      }
    } 
    else {
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.fdd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
    break; 

  case TYPE_DOUBLE:
    if (VAR[d->var_index].STATUS & FLAG_ADDRESS_AFFECTING) { 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.dfdd.arc[ci].child);
        child = dfdd_one_constraint(child, d->var_index, 
          d->u.dfdd.arc[ci].lower_bound, 
          d->u.dfdd.arc[ci].upper_bound
        ); 
        result = red_bop(OR, result, child); 
      }
    } 
    else {
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.dfdd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
    break; 

  default:
    if (VAR[d->var_index].STATUS & FLAG_ADDRESS_AFFECTING) { 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.ddd.arc[ci].child);
        child = ddd_one_constraint(child, d->var_index, 
          d->u.ddd.arc[ci].lower_bound, 
          d->u.ddd.arc[ci].upper_bound
        ); 
        result = red_bop(OR, result, child); 
      }
    } 
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        child = rec_abstract_address_affecting(d->u.ddd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
  }

  return(rec->result = result);
}
  /* rec_abstract_address_affecting() */




struct red_type	*red_abstract_address_affecting(d)
     struct red_type	*d;
{
  struct red_type	*result;

/*
  print_cpu_time("Before red_abstract_address_affecting()");
  red_print_graph(RT[f]); 
*/  

  init_23tree(&aaff_tree); 
  result = rec_abstract_address_affecting(d);
  free_entire_23tree(aaff_tree, rec_free); 
  
  /* 
  print_cpu_time("After red_cdd()");
  fprintf(RED_OUT, "Leaving red_abstract_address_affecting()");
  red_print_graph(result); 
  */
  
  return(result);
}
/* red_abstract_address_affecting() */



  
void	plain_reachable() { 
  int 				pi, vi, imi, mi, ixi, xi, ixj, *mpc, 
				af, nf, f, type, offset;
  struct index_link_type	*mi_list, *ip;

  #ifdef RED_DEBUG_PARSE_MODE
  fprintf(RED_OUT, "\nentering plain_reachable() with RT_TOP=%1d.\n", 
    RT_TOP
  ); 
  #endif 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    /* Initialize the mode distance array. */
    PROCESS[pi].mode_distance_from_initial 
    = (int *) malloc(MODE_COUNT * sizeof(int));
/*
    fprintf(RED_OUT, 
      "\nPROCESS[pi=%1d].mode_distance_from_initial=%x allocated\n", 
      pi, PROCESS[pi].mode_distance_from_initial
    ); 
*/
    for (mi = 0; mi < MODE_COUNT; mi++)
      PROCESS[pi].mode_distance_from_initial[mi] = MODE_COUNT;
  }  
  
  collect_all_address_affecting_variables(); 
  for (xi = 0; xi < XTION_COUNT; xi++) {
    process_xtion_effect_alloc(XTION[xi].statement); 
  }  
  
  /* Second, calculate all the syntactically reachable modes of process pi */
  RT[af = RT_TOP++] = red_abstract_address_affecting(RT[INDEX_INITIAL]); 
  #ifdef RED_DEBUG_PARSE_MODE
  fprintf(RED_OUT, "\nThe initial RT[af=%1d]:\n", af); 
  red_print_graph(RT[af]); 
  #endif 

  RT[f = RT_TOP++] = RT[af]; // RT[INDEX_INITIAL]; 
  RT[INDEX_URGENT] = NORM_FALSE; 
  for (offset = 0; RT[f] != NORM_FALSE; offset++) { 
    /* First, collect the initial modes of process pi */
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      vi = variable_index[TYPE_DISCRETE][pi][OFFSET_MODE];
      for (mi = 0; mi < MODE_COUNT; mi++) {
        if (ddd_one_constraint(RT[f], vi, mi, mi) != NORM_FALSE) { 
          if (offset < PROCESS[pi].mode_distance_from_initial[mi]) 
            PROCESS[pi].mode_distance_from_initial[mi] = offset;
        }
      }
    }
    /* Now we calculate the fixpoint iteration. */ 
    RT[nf = RT_TOP++] = NORM_FALSE; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      #ifdef RED_DEBUG_PARSE_MODE
      fprintf(RED_OUT, "\nplain fxp %1d: after (pi=%1d):\n", offset, pi); 
      fflush(RED_OUT); 
      #endif 
      for (xi = 1; xi < XTION_COUNT; xi++) { 
      	if (XTION[xi].red_trigger[pi] == NORM_FALSE) { 
/*
      	  fprintf(RED_OUT, "\nRecalculating XTION[xi=%1d].red_trigger[pi=%1d]:\n", 
      	    xi, pi
      	  ); 
      	  pcform(XTION[xi].parse_xtion->trigger_exp); 
      	  fflush(RED_OUT); 
*/
          XTION[xi].red_trigger[pi] 
          = red_local(XTION[xi].parse_xtion->trigger_exp, pi, 0); 

          #ifdef RED_DEBUG_PARSE_MODE
          fprintf(RED_OUT, "\nXTION[%1d].red_trigger[%1d], constructed:\n", xi, pi); 
          red_print_graph(XTION[xi].red_trigger[pi]); 
          #endif 
      
          if (   valid_mode_index(XTION[xi].src_mode_index)
	      && !(MODE[XTION[xi].src_mode_index].status & FLAG_MODE_URGENT)
	      )
	    XTION[xi].red_trigger[pi] = red_bop(SUBTRACT, 
	      XTION[xi].red_trigger[pi], 
	      RT[INDEX_URGENT] 
	    ); 
      	  RT[ixi = RT_TOP++] = red_abstract_lazy( 
      	    red_bop(AND, RT[f], XTION[xi].red_trigger[pi]) 
      	  ); 
	  if (RT[ixi] == NORM_FALSE) {
	    XTION[xi].red_trigger[pi] = NORM_FALSE; 
	  } 
	  else { 
            process_xtion_statement_fillin(pi, XTION[xi].statement); 

            red_mark(XTION[xi].red_trigger[pi], FLAG_GC_STABLE); 
          }
      	}
      	else 
      	  RT[ixi = RT_TOP++] = red_abstract_lazy( 
      	    red_bop(AND, RT[f], XTION[xi].red_trigger[pi]) 
      	  ); 
      	if (RT[ixi] != NORM_FALSE) { 
          #ifdef RED_DEBUG_PARSE_MODE
      	  fprintf(RED_OUT, "\nplain fxp %1d: after (pi=%1d,xi=%1d) trigger:\n", 
      	    offset, pi, xi
      	  ); 
      	  print_xtion_line(xi, pi); 
      	  fprintf(RED_OUT, "\n"); 
          #endif 

          RT[ixi] = red_statement_untimed_fwd( 
      	    ixi, pi, XTION[xi].statement, 
      	      FLAG_ACTION_LAZY_EVAL 
      	    | FLAG_ACTION_ADDRESS_AFFECTING_ONLY
      	  ); 

          #ifdef RED_DEBUG_PARSE_MODE
          fprintf(RED_OUT, 
            "\nplain fxp %1d: after (pi=%1d,xi=%1d) statement:\n", 
            offset, pi, xi 
          ); 
      	  red_print_graph(RT[ixi]); 
          #endif 

      	  RT[ixi] = red_abstract_address_affecting(RT[ixi]); 

          #ifdef RED_DEBUG_PARSE_MODE
          fprintf(RED_OUT, 
            "\nplain fxp %1d: after (pi=%1d,xi=%1d) address affecting:\n", 
            offset, pi, xi 
          ); 
      	  red_print_graph(RT[ixi]); 
          #endif 

      	  RT[ixi] = red_bop(SUBTRACT, RT[ixi], RT[af]); 
      	  RT[f] = red_bop(OR, RT[f], RT[ixi]); 
      	  RT[nf] = red_bop(OR, RT[nf], RT[ixi]); 
      	  RT[af] = red_bop(OR, RT[af], RT[ixi]); 
      	} 
      	RT_TOP--; // ixi 
      }
    }
    RT[f] = RT[nf]; 
    RT_TOP--; // nf 
    garbage_collect(FLAG_GC_SILENT);
    
    #ifdef RED_DEBUG_PARSE_MODE
    fprintf(RED_OUT, "\n==[plain fxp %1d]===========\nRT[f=%1d]:\n", 
      offset, f
    ); 
    red_print_graph(RT[f]); 
    fprintf(RED_OUT, "--------------------------------\nRT[af=%1d]:\n", af); 
    red_print_graph(RT[af]);  
    #endif 
  } 
  RT_TOP--; // f 
  
  // Now RT[af] records an abstract reachability.  
  // Based on the RT[af], we then calculate the reachable_modes and 
  // firable_xtions. 
  
  /* Third, record the reachable modes in array. */ 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    PROCESS[pi].reachable_mode_count = 0; 
    PROCESS[pi].firable_xtion_count = 1; 
    vi = variable_index[TYPE_DISCRETE][pi][OFFSET_MODE]; 
    mi_list = NULL; 
    for (mi = MODE_COUNT-1; mi >= 0; mi--) { 
      if (ddd_one_constraint(RT[af], vi, mi, mi) != NORM_FALSE) { 
        mi_list = add_index_count(mi_list, mi, 
          &(PROCESS[pi].reachable_mode_count)
        ); 
      } 
    } 
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n==================================\n"); 
    fprintf(RED_OUT, "PI=%1d's mode index list:\n", pi); 
    print_index_list(mi_list); 
    #endif 

    PROCESS[pi].reachable_mode = (int *) 
      malloc(PROCESS[pi].reachable_mode_count * sizeof(int));
    PROCESS[pi].reachable_lower_mode = MODE_COUNT-1;
    PROCESS[pi].reachable_upper_mode = 0;
    for (imi = 0, ip = mi_list;
	 ip;
	 imi++, ip = ip->next_index_link
	 ) {
      PROCESS[pi].reachable_mode[imi] = ip->index;
      if (ip->index < PROCESS[pi].reachable_lower_mode)
        PROCESS[pi].reachable_lower_mode = ip->index;
      if (ip->index > PROCESS[pi].reachable_upper_mode)
        PROCESS[pi].reachable_upper_mode = ip->index; 
      PROCESS[pi].firable_xtion_count 
      = PROCESS[pi].firable_xtion_count
      + MODE[ip->index].xtion_count; 
    } 
    free_index_list(mi_list); 
    PROCESS[pi].group_process_index = pi; 

    /* Fourth, calculate the firable xtions of process pi */
    ixj = 1;
    PROCESS[pi].firable_xtion = (int *) 
      malloc(PROCESS[pi].firable_xtion_count * sizeof(int));
    PROCESS[pi].firable_xtion[0] = 0; 
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) { 
      mi = PROCESS[pi].reachable_mode[imi]; 
      for (ixi = 0; ixi < MODE[mi].xtion_count; ixi++) { 
        PROCESS[pi].firable_xtion[ixj++] = MODE[mi].xtion[ixi];
      }
    }
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n----------------------\n"); 
    fprintf(RED_OUT, "PI=%1d's %1d modes' indices:\n", 
      pi, PROCESS[pi].reachable_mode_count
    ); 
    if (PROCESS[pi].reachable_mode_count) { 
      fprintf(RED_OUT, "%1d", PROCESS[pi].reachable_mode[0]); 
      for (imi = 1; imi < PROCESS[pi].reachable_mode_count; imi++) { 
        fprintf(RED_OUT, ", %1d", PROCESS[pi].reachable_mode[imi]);
      } 
      fprintf(RED_OUT, "\n"); 
    }
    fprintf(RED_OUT, "\n----------------------\n"); 
    fprintf(RED_OUT, "PI=%1d's %1d xtions' indices:\n", 
      pi, PROCESS[pi].firable_xtion_count
    ); 
    if (PROCESS[pi].firable_xtion_count) { 
      fprintf(RED_OUT, "%1d", PROCESS[pi].firable_xtion[0]); 
      for (ixi = 1; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
        fprintf(RED_OUT, ", %1d", PROCESS[pi].firable_xtion[ixi]);
      } 
      fprintf(RED_OUT, "\n"); 
    }
    #endif 
  }
  RT_TOP--; // af 
  
  mpc = (int *) malloc(MODE_COUNT*sizeof(int));
  for (mi = 0; mi < MODE_COUNT; mi++)
    mpc[mi] = 0;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      mpc[PROCESS[pi].reachable_mode[imi]]++;
    }
  }
  for (mi = 0; mi < MODE_COUNT; mi++) {
    MODE[mi].process_count = mpc[mi];
    MODE[mi].process = (int *) malloc(mpc[mi]*sizeof(int));
    mpc[mi] = 0;
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      mi = PROCESS[pi].reachable_mode[imi];
      MODE[mi].process[mpc[mi]] = pi;
      mpc[mi]++;
    }
  }
  free(mpc);
  
  /* Group the processes */ 
  /* Step 1: constuct the parent trees according to the process lists 
   *         of each modes. 
   */
  for (mi = 0; mi < MODE_COUNT; mi++) { 
    int	ipi, ipj, pi, pj; 
    
    for (ipi = 0; ipi < MODE[mi].process_count; ipi++) { 
      pi = MODE[mi].process[ipi]; 
      for (ipj = ipi+1; ipj < MODE[mi].process_count; ipj++) { 
      	pj = MODE[mi].process[ipj]; 
      	if (PROCESS[pi].group_process_index 
	    != PROCESS[pj].group_process_index
	    ) { 
	  PROCESS[pj].group_process_index = PROCESS[pi].group_process_index; 
	}
      } 
    }	
  } 
  /* Step 2: compact the parent trees to depth one. */
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (; 
	 PROCESS[pi].group_process_index 
	 != PROCESS[PROCESS[pi].group_process_index].group_process_index; 
	 ) { 
      PROCESS[pi].group_process_index 
      = PROCESS[PROCESS[pi].group_process_index].group_process_index; 
    } 
  }
    
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (type = TYPE_DISCRETE; type <= TYPE_DENSE; type++) { 
      for (offset = 0; offset < LOCAL_COUNT[type]; offset++) 
        if (!local_defined(type, pi, offset)) 
          variable_index[type][pi][offset] = FLAG_NO_USE; 
    } 
  } 
  
  offset = 0; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    offset = offset + PROCESS[pi].firable_xtion_count; 
  } 
  if (offset > 100) { 
    GSTATUS[IDNEX_MANY_TRANSITIONS] 
    = GSTATUS[IDNEX_MANY_TRANSITIONS] 
    | FLAG_MANY_TRANSITIONS; 
  } 
  else {
    GSTATUS[IDNEX_MANY_TRANSITIONS] 
    = GSTATUS[IDNEX_MANY_TRANSITIONS] 
    & ~FLAG_MANY_TRANSITIONS; 
  }
/*
  print_processes(); 
*/
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\nleaving plain_reachable() with RT_TOP=%1d.\n", 
    RT_TOP
  ); 
  #endif 
}
  /* plain_reachable() */




/*
int	count_miae = 0; 
*/
int	CURRENT_MI, CURRENT_PI;
void	rec_mode_invariance_analyze(struct red_type *);

int 	rec_mode_invariance_analyze_in_exp(psub)
     struct ps_exp_type	*psub; 
{
  int				i, jj, pi, flag; 
  struct ps_bunit_type		*pbu; 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER: 
  case TYPE_TRASH: 
  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_CONSTANT: 
    return(TYPE_FALSE); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(rec_mode_invariance_analyze_in_exp(psub->u.exp)); 

  case TYPE_CLOCK: 
    MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count++;
  case TYPE_DENSE: 
    return(TYPE_TRUE); 

  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
    if (rec_mode_invariance_analyze_in_exp(psub->u.atom.exp_base_proc_index)) { 
      return(TYPE_TRUE); 
    } 
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      if (rec_mode_invariance_analyze_in_exp(
        psub->u.atom.indirect_exp[i]
      )   ) 
        return(TYPE_TRUE); 
    }
*/
    return(TYPE_FALSE);  
    break; 

  case BIT_NOT: 
    return(rec_mode_invariance_analyze_in_exp(psub->u.exp)); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:  
  case ARITH_EQ : 
  case ARITH_NEQ : 
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    return(  rec_mode_invariance_analyze_in_exp(psub->u.arith.lhs_exp) 
           | rec_mode_invariance_analyze_in_exp(psub->u.arith.rhs_exp)
           ); 
  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    flag = 0; 
    for (i = 0; i < psub->u.ineq.term_count; i++) { 
      flag = flag 
      | rec_mode_invariance_analyze_in_exp(psub->u.ineq.term[i].coeff) 
      | rec_mode_invariance_analyze_in_exp(psub->u.ineq.term[i].operand); 
    } 
    flag = flag | rec_mode_invariance_analyze_in_exp(psub->u.ineq.offset); 
    return(flag); 

  case ARITH_CONDITIONAL: 
    return(
      rec_mode_invariance_analyze_in_exp(psub->u.arith_cond.cond)
    | rec_mode_invariance_analyze_in_exp(psub->u.arith_cond.if_exp)
    | rec_mode_invariance_analyze_in_exp(psub->u.arith_cond.else_exp)
    ); 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist;  
	 jj; 
	 jj--, pbu = pbu->bnext
	 ) {
      if (rec_mode_invariance_analyze_in_exp(pbu->subexp))
        return(TYPE_TRUE); 
    }
    return (TYPE_FALSE);

  case FORALL: 
  case EXISTS: 
    return(rec_mode_invariance_analyze_in_exp(psub->u.qexp.child)); 
 
  case RED: 
    rec_mode_invariance_analyze(psub->u.rpred.red); 
    if (MODE[CURRENT_MI].status & FLAG_CLOCK_INACTIVE) 
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 
      
  case EXISTS_ALWAYS: 
  case FORALL_ALWAYS:
  case FORALL_EVENTUALLY:
  case FORALL_CHANGE:
  case EXISTS_EVENTUALLY:
  case EXISTS_CHANGE:
  case FORALL_EVENT: 
  case EXISTS_UNTIL:
  case FORALL_UNTIL:
    fprintf(RED_OUT, "\nrec_mode_invariance_analyze_in_exp: How come there is still a FORALL UNTIL in the specification ?\n"); 
    fflush(RED_OUT); 
    bk(0); 
    for (; 1; ); 
    return; 
  }
}
  /* rec_mode_invariance_analyze_in_exp() */ 




void	rec_mode_invariance_analyze(d)
     struct red_type	*d;
{
  int			ci;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) 
    return; 
    
  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, parse_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					); 
  if (rec != nrec) { 
    return; 
  }
/*  
  fprintf(RED_OUT, "count_miae=%1d\n", ++count_miae); 
  for (; count_miae == -1; ); 
*/  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count++;
    MODE[CURRENT_MI].status = MODE[CURRENT_MI].status & ~FLAG_CLOCK_INACTIVE;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_analyze(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD:
    MODE[CURRENT_MI].status = MODE[CURRENT_MI].status & ~FLAG_CLOCK_INACTIVE;
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_analyze(d->u.hrd.arc[ci].child);
    break;
  case TYPE_LAZY_EXP: 
    if (rec_mode_invariance_analyze_in_exp(d->u.lazy.exp)) 
      MODE[CURRENT_MI].status 
      = MODE[CURRENT_MI].status & ~FLAG_CLOCK_INACTIVE; 
    rec_mode_invariance_analyze(d->u.lazy.false_child);  
    rec_mode_invariance_analyze(d->u.lazy.true_child); 
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_analyze(d->u.dfdd.arc[ci].child);
    break; 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_analyze(d->u.fdd.arc[ci].child);
    break; 
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_analyze(d->u.ddd.arc[ci].child);
  }
}
/* rec_mode_invariance_analyze() */



void	mode_invariance_analyze(d)
     struct red_type	*d; 
{ 
  MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count = 0; 
  init_23tree(&parse_tree);
  rec_mode_invariance_analyze(d); 
  free_entire_23tree(parse_tree, rec_free);
} 
  /* mode_invariance_analyze() */






void	rec_mode_invariance_zone_bound_fillin(d)
     struct red_type	*d;
{
  int			ci, zbi;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) 
    return; 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, parse_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					); 
  if (rec != nrec) { 
    return; 
  }
/*  
  fprintf(RED_OUT, "count_miae=%1d\n", ++count_miae); 
  for (; count_miae == -1; ); 
*/  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    zbi = MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count++; 
    MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound[zbi].var_index 
    = d->var_index;
    MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound[zbi].upper_bound
    = d->u.crd.arc[d->u.crd.child_count-1].upper_bound;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) 
      rec_mode_invariance_zone_bound_fillin(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_zone_bound_fillin(d->u.hrd.arc[ci].child);
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_zone_bound_fillin(d->u.fdd.arc[ci].child);
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_zone_bound_fillin(d->u.dfdd.arc[ci].child);
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--)
      rec_mode_invariance_zone_bound_fillin(d->u.ddd.arc[ci].child);
  }
}
/* rec_mode_invariance_zone_bound_fillin() */



void	mode_invariance_zone_bound_fillin(d)
     struct red_type	*d; 
{ 
  MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count = 0; 
  init_23tree(&parse_tree);
  rec_mode_invariance_zone_bound_fillin(d); 
  free_entire_23tree(parse_tree, rec_free);
} 
  /* mode_invariance_zone_bound_fillin() */






#ifdef RED_DEBUG_PARSE_MODE 
int count_process_xtion_effect_alloc = 0; 
#endif 



int	check_simple_addresses(
  struct ps_exp_type	*exp
) { 
  int	pi; 
  
  switch(exp->type){
  case TYPE_CONSTANT: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_QFD: 
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_QSYNC_HOLDER:
    return(TYPE_TRUE); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(TYPE_FALSE); 

  case TYPE_POINTER:
  case TYPE_DISCRETE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
/*
    if (   (!(  exp->u.atom.exp_base_proc_index->status 
              & FLAG_EXP_STATE_INSIDE
            ) )
        || (   exp->u.atom.exp_base_proc_index->type == TYPE_POINTER
            && (  exp->u.atom.exp_base_proc_index->u.atom.var->status 
                & FLAG_LOCAL_VARIABLE
                ) 
            && (  exp->u.atom.exp_base_proc_index->u.atom.var->status 
                & FLAG_QUANTIFIED_SYNC
        )   )   ) 
      return(TYPE_TRUE); 
    else 
*/
    return(TYPE_FALSE); 
    
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    if (exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 

  case ARITH_ADD: 
  case ARITH_MINUS:
    if (   check_simple_addresses(exp->u.arith.lhs_exp)
        && check_simple_addresses(exp->u.arith.rhs_exp)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_MULTIPLY: 
    if (exp->u.arith.lhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE) 
        return(TYPE_FALSE); 
      else 
        return (check_simple_addresses(exp->u.arith.lhs_exp)); 
    else if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(check_simple_addresses(exp->u.arith.rhs_exp));
    else 
      return(TYPE_TRUE); 
  case ARITH_DIVIDE:
    if (exp->u.arith.lhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE) 
        return(TYPE_FALSE); 
      else 
        return (check_simple_addresses(exp->u.arith.lhs_exp)); 
    else if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(TYPE_FALSE);
    else 
      return(TYPE_TRUE); 
  case ARITH_MODULO:
    return(TYPE_FALSE); 

  case TYPE_INLINE_CALL: 
    return(check_simple_addresses(exp->u.inline_call.instantiated_exp)); 

  default:
    fprintf(RED_OUT, 
      "\nParser: Unexpected exp type %1d in rec_get_exp_value()\n", 
      exp->type
    );
    pcform(exp); 
    fflush(RED_OUT); 
    bk(); 
  }
} 
  /* check_simple_addresses() */  



int	check_simple_sync_addresses(
  struct ps_exp_type	*exp
) { 
  int	pi; 
  
  switch(exp->type){
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_QFD: 
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_QSYNC_HOLDER:
    return(TYPE_TRUE); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(TYPE_FALSE); 

  case TYPE_POINTER:
  case TYPE_DISCRETE: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
    if (check_simple_addresses(exp->u.atom.exp_base_proc_index)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
    
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    if (exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 

  case ARITH_ADD: 
  case ARITH_MINUS:
    if (   check_simple_sync_addresses(exp->u.arith.lhs_exp)
        && check_simple_sync_addresses(exp->u.arith.rhs_exp)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_MULTIPLY: 
    if (exp->u.arith.lhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE) 
        return(TYPE_FALSE); 
      else 
        return(check_simple_sync_addresses(exp->u.arith.lhs_exp)); 
    else if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(check_simple_sync_addresses(exp->u.arith.rhs_exp));
    else 
      return(TYPE_TRUE); 
  case ARITH_DIVIDE:
    if (exp->u.arith.lhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE) 
        return(TYPE_FALSE); 
      else 
        return (check_simple_sync_addresses(exp->u.arith.lhs_exp)); 
    else if (exp->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
      return(TYPE_FALSE);
    else 
      return(TYPE_TRUE); 
  case ARITH_MODULO:
    return(TYPE_FALSE); 

  case TYPE_INLINE_CALL: 
    return(check_simple_sync_addresses(exp->u.inline_call.instantiated_exp)); 

  default:
    fprintf(RED_OUT, 
      "\nParser: Unexpected exp type %1d in rec_get_exp_value()\n", 
      exp->type
    );
    pcform(exp); 
    fflush(RED_OUT); 
    bk(); 
  }
} 
  /* check_simple_sync_addresses() */  




int	check_simple_clock_statement(
  struct statement_type	*st
) { 
  int	pi, vi; 
  
  if (  (st->st_status 
         & (FLAG_ACTION_LHS_RECURSION | FLAG_ACTION_INDIRECTION)
         )
      ||((st->u.act.lhs->var_status | st->u.act.rhs_exp->var_status)
         & (FLAG_POINTER | FLAG_DISCRETE)
      )  ) 
    return(TYPE_FALSE); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    if (get_variable_index(st->u.act.lhs, pi) < 0) 
      return (TYPE_FALSE);  
  
  return (check_simple_sync_addresses(st->u.act.rhs_exp)); 
}
  /* check_simple_clock_statement() */ 






process_xtion_effect_alloc(st) 
	struct statement_type	*st; 
{ 
  int	i, pi, value; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case UNCHANGED: 
    break; 
  case ST_IF: 
    process_xtion_effect_alloc(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      process_xtion_effect_alloc(st->u.branch.else_statement);  
    } 
    break; 
  case ST_WHILE: 
    process_xtion_effect_alloc(st->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      process_xtion_effect_alloc(st->u.seq.statement[i]); 
    } 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
  case ST_GUARD: 
  case ST_ERASE: 
    break; 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
    if (check_simple_clock_statement(st)) {
      st->u.act.red_effect = ((struct red_type **) 
        malloc(PROCESS_COUNT * sizeof(struct red_type *))
      )-1;
      // This is crucial since latter steps depend on this. 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) 
        st->u.act.red_effect[pi] = NULL; 
    }
    else { 
      st->u.act.red_effect = NULL;
    }
    break;

  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    st->u.act.red_effect = NULL;
    break; 

  case ASSIGN_HYBRID_EXP:
/****************************************************************
*   For the full syntax of LHA, now we have to allow the following.  
*   We will now need to use the standard technique of assignment evaluation 
*   with primed variables for the next state variables.  
*   Thus we will use the following steps. 
*   
*    1. construct HRD for red_effect for x'==f(x,....)
*    2. conjunct cond && x'==f(x,....)
*    3. in forward analysis, 
*         switch_vi(exists x(cond && x'==f(x,....)), x, x')
*       in backward analysis
*         exists x(switch_vi(cond && x'==f(x,....), x, x'))
*
    if (   (st->status & (FLAG_LHS_RECURSION | FLAG_INDIRECTION))
        && !(   check_simple_sync_addresses(st->u.act.lhs)
             && check_simple_sync_addresses(st->u.act.rhs_exp) 
        )    ) {
      st->u.act.red_effect = NULL;
      return; 
    } 
*/
    for (i = 0; i < st->u.act.term_count; i++) { 
      if (   (st->u.act.term[i].coeff->var_status & FLAG_EXP_STATE_INSIDE)  
          || !check_simple_sync_addresses(st->u.act.term[i].operand)
          ) {
        st->u.act.red_effect = NULL; 
        return;      
      }
    } 
    st->u.act.red_effect = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    )-1;
    // This is crucial since latter steps depend on these NULL values 
    // as flags. 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      st->u.act.red_effect[pi] = NULL; 
    break;

  default:
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n%1d, st->status=%x\n", 
      ++count_process_xtion_effect_alloc, 
      st->status
    ); 
    if (count_process_xtion_effect_alloc == -1) { 
      fprintf(RED_OUT, "Caught!\n"); 
    }
    print_statement_line(st, 1); 
    fflush(RED_OUT); 
    #endif 
    
    if (   check_simple_sync_addresses(st->u.act.lhs)
        && !(st->u.act.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE)
        ) {
      st->u.act.red_effect = ((struct red_type **) 
        malloc(PROCESS_COUNT * sizeof(struct red_type *))
      )-1;
      // This is crucial since latter steps depend on this. 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) 
        st->u.act.red_effect[pi] = NULL; 
    }
    else 
      st->u.act.red_effect = NULL; 
    break; 
  }
}
  /* process_xtion_effect_alloc() */
  
  
  
process_xtion_statement_fillin(pi, st) 
	int			pi; 
	struct statement_type	*st; 
{ 
  int	i; 
  
  if (!st) 
    return; 
    
  switch (st->op) {
  case ST_IF: 
    process_xtion_statement_fillin(pi, st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      process_xtion_statement_fillin(pi, st->u.branch.else_statement);  
    } 
    break; 
  case ST_WHILE: 
    process_xtion_statement_fillin(pi, st->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      process_xtion_statement_fillin(pi, st->u.seq.statement[i]); 
    } 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    if (st->u.act.red_effect) {
      XSUB.type = ARITH_EQ;
      XSUB.u.arith.lhs_exp = st->u.act.lhs;
      XSUB.u.arith.rhs_exp = st->u.act.rhs_exp;
/*
      fprintf(RED_OUT, "\nred_effect pi %1d of : ", pi); 
      psl(st, pi); 
*/
      st->u.act.red_effect[pi] = red_discrete_ineq(&XSUB, pi);

      red_mark(st->u.act.red_effect[pi], FLAG_GC_STABLE);
/*
      red_print_graph(st->u.act.red_effect[pi]); 
*/
    }
    else 
      st->u.act.red_effect = NULL; 
    break;
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    if (st->u.act.red_effect) {
      XSUB.type = EQ;
      XSUB.u.ineq.term_count = st->u.act.term_count;
      XSUB.u.ineq.term = st->u.act.term;
      XSUB.u.ineq.offset = st->u.act.offset;
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID)
        st->u.act.red_effect[pi] = red_hybrid_ineq(&XSUB, pi);
      else
        st->u.act.red_effect[pi] = red_clock_ineq(&XSUB, pi);

      red_mark(st->u.act.red_effect[pi], FLAG_GC_STABLE);
    }
    break;
  case ASSIGN_HYBRID_EXP:
    if (st->u.act.red_effect == NULL) { 
      break; 
    }
    else if (st->u.act.rhs_exp->type == TYPE_INTERVAL) {
      st->u.act.red_effect[pi] = NORM_NO_RESTRICTION;
      XSUB.u.ineq.term_count = 1;
      XSUB.u.ineq.term = (struct parse_term_type *) malloc(sizeof(struct parse_term_type));
      XSUB.u.ineq.term[0].operand = st->u.act.lhs;
      XSUB.u.ineq.term[0].coeff = ps_exp_alloc(TYPE_CONSTANT);
      XSUB.u.ineq.term[0].coeff->u.value = 1;
      if (!(st->u.act.rhs_exp->u.interval.status & INTERVAL_LEFT_UNBOUNDED)) {
        if (st->u.act.rhs_exp->u.interval.status & INTERVAL_LEFT_OPEN)
          XSUB.type = GREATER;
        else
          XSUB.type = GEQ;
        XSUB.u.ineq.offset = st->u.act.rhs_exp->u.interval.lbound_exp;
        st->u.act.red_effect[pi]
        = red_bop(AND, st->u.act.red_effect[pi], red_hybrid_ineq(&XSUB, pi));
      }
      if (!(st->u.act.rhs_exp->u.interval.status & INTERVAL_RIGHT_UNBOUNDED)) {
        if (st->u.act.rhs_exp->u.interval.status & INTERVAL_RIGHT_OPEN)
          XSUB.type = LESS;
        else
          XSUB.type = LEQ;
        XSUB.u.ineq.offset = st->u.act.rhs_exp->u.interval.rbound_exp;
        st->u.act.red_effect[pi]
        = red_bop(AND, st->u.act.red_effect[pi], red_hybrid_ineq(&XSUB, pi));
      }
      red_mark(st->u.act.red_effect[pi], FLAG_GC_STABLE);
    }
    else {
      XSUB.type = EQ;
      XSUB.u.ineq.term_count = st->u.act.term_count;
      XSUB.u.ineq.term = st->u.act.term;
      XSUB.u.ineq.offset = st->u.act.offset;
      st->u.act.red_effect[pi] = red_hybrid_ineq(&XSUB, pi);
      red_mark(st->u.act.red_effect[pi], FLAG_GC_STABLE);
    }
    fprintf(RED_OUT, "\nhybrid action: pi=%1d with red_effect:\n", pi); 
    psl(st, pi); 
    red_print_graph(st->u.act.red_effect[pi]); 
    break; 
  default: 
    break; 
  } 
}
  /* process_xtion_statement_fillin() */
  
  
  
  
process_xtion_fillin() {
  int 	ipi, pi, ai, mi, imi, lusm, lum, ixi, xi;

  for (mi = 0; mi < MODE_COUNT; mi++) {
    MODE[mi].invariance
      = ((struct mode_invariance_type *)
	 malloc(PROCESS_COUNT * sizeof(struct mode_invariance_type))
	 ) - 1;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      MODE[mi].invariance[pi].red = NORM_FALSE; 
      MODE[mi].invariance[pi].untimed_red = NORM_FALSE;
      MODE[mi].invariance[pi].zone_bound_count = 0;
      MODE[mi].invariance[pi].zone_bound = NULL; 
    }
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      mi = PROCESS[pi].reachable_mode[imi];
//      fillin_indirect_reference(pi, MODE[mi].invariance_exp);
      MODE[mi].invariance[pi].red = red_local(
        MODE[mi].invariance_exp, pi, 0
      );
      MODE[mi].invariance[pi].untimed_red
      = red_time_eliminate(MODE[mi].invariance[pi].red);
      red_mark(MODE[mi].invariance[pi].red, FLAG_GC_STABLE);
      red_mark(MODE[mi].invariance[pi].untimed_red, FLAG_GC_STABLE);
      garbage_collect(FLAG_GC_SILENT); 
/*      
      fprintf(RED_OUT, "\n===============================\n"); 
      fprintf(RED_OUT, "original form of MODE[mi=%1d].invariance[pi=%1d].red:\n", mi, pi); 
      pcform(MODE[mi].invariance_exp); 
      fprintf(RED_OUT, "red:\n"); 
      red_print_line(MODE[mi].invariance[pi].red); 
      fprintf(RED_OUT, "\nuntimed red:\n"); 
      red_print_line(MODE[mi].invariance[pi].untimed_red); 
      fprintf(RED_OUT, "\n\n"); 
*/
    }
  }

  for (CURRENT_MI = 0; CURRENT_MI < MODE_COUNT; CURRENT_MI++) {
    MODE[CURRENT_MI].status = MODE[CURRENT_MI].status | FLAG_CLOCK_INACTIVE;
    for (ipi = 0; ipi < MODE[CURRENT_MI].process_count; ipi++) {
      CURRENT_PI = MODE[CURRENT_MI].process[ipi];
      mode_invariance_analyze(MODE[CURRENT_MI].invariance[CURRENT_PI].red);
    }
    if (   (MODE[CURRENT_MI].status & FLAG_MODE_URGENT)
        && !(MODE[CURRENT_MI].status & FLAG_CLOCK_INACTIVE)
        ) {
      fprintf(RED_OUT, "\nError: a timing constraint in the invariance condition of urgent mode %1d:%s\n",
	      mi, MODE[CURRENT_MI].name
	      );
      fflush(RED_OUT);
      exit(0);
    }
    if (MODE[CURRENT_MI].status & FLAG_CLOCK_INACTIVE)
      for (CURRENT_PI = 1; CURRENT_PI <= PROCESS_COUNT; CURRENT_PI++)
	MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound = NULL;
    else
      for (ipi = 0; ipi < MODE[CURRENT_MI].process_count; ipi++) {
        CURRENT_PI = MODE[CURRENT_MI].process[ipi];
        MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound
        = (struct zone_bound_type *)
          malloc(MODE[CURRENT_MI].invariance[CURRENT_PI].zone_bound_count
                 * sizeof(struct zone_bound_type)
      	         );
        mode_invariance_zone_bound_fillin(MODE[CURRENT_MI].invariance[CURRENT_PI].red);
      }
  }

  #ifdef RED_DEBUG_PARSE_MODE
  print_modes();
  #endif 

  /* calculate RT[INDEX_URGENT] */
  RT[INDEX_URGENT] = NORM_FALSE;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    lum = -2;
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      mi = PROCESS[pi].reachable_mode[imi];
      if (MODE[mi].status & FLAG_MODE_URGENT)
      	if (lum < mi-1)
      	  lusm = lum = mi;
      	else
      	  lum = mi;
      else if (lum >= 0) {
	RT[INDEX_URGENT] = red_bop(OR, RT[INDEX_URGENT],
			     ddd_atom(variable_index[TYPE_DISCRETE][pi][0], lusm, lum)
			     );
	lum = -2;
      }
    }
    if (lum >= 0)
      RT[INDEX_URGENT] = red_bop(OR, RT[INDEX_URGENT],
			   ddd_atom(variable_index[TYPE_DISCRETE][pi][0], lusm, lum)
			   );
  }

  red_mark(RT[INDEX_URGENT], FLAG_GC_STABLE);
  garbage_collect(FLAG_GC_SILENT);


  /*
  fprintf(RED_OUT, "MODE URGENT : \n");
  red_print_graph(RT[INDEX_URGENT]);
  */

  /* Since the indirection construction in the following loops may use quantified sync variables, 
   * we should prepare the SPEC_INDEX field of all quantified sync variables as 
   * FLAG_ANY_PROCESS.  
   */ 
  garbage_collect(FLAG_GC_SILENT);


/*
    fprintf(RED_OUT, "\nFinally, \n");
    red_print_graph(XTION[xi].red_trigger[pi]);
*/
  for (xi = 0; xi < XTION_COUNT; xi++) {
    if (   red_time_inactive(XTION[xi].red_trigger[1])
        && (   (!valid_mode_index(XTION[xi].src_mode_index))
            || (MODE[XTION[xi].src_mode_index].status & FLAG_CLOCK_INACTIVE)
            )
        && (   (!valid_mode_index(XTION[xi].dst_mode_index))
	    || (MODE[XTION[xi].dst_mode_index].status & FLAG_CLOCK_INACTIVE)
	    )
        && !(XTION[xi].status & FLAG_CLOCK_RESET)
        ) {
      XTION[xi].status = XTION[xi].status | FLAG_XTION_CLOCK_INACTIVE;
    }
    else
      XTION[xi].status = XTION[xi].status & ~FLAG_XTION_CLOCK_INACTIVE;
  }
}
  /* process_xtion_fillin() */




int	FLAG_POLARITY_SPEC_PROCESS; 
void	spec_process(struct ps_exp_type *, int); 

void rec_spec_process(d)
	struct red_type	*d;
{
  int				ci, vi; 
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return; 

  ce = cache1_check_result_key(OP_SPEC_PROCESS, d); 
  if (ce->result) {
    return; 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD:
    vi = CLOCK[VAR[d->var_index].U.CRD.CLOCK1];
    if (VAR[vi].PROC_INDEX)
      PROCESS[VAR[vi].PROC_INDEX].status = PROCESS[VAR[vi].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT;
    vi = CLOCK[VAR[d->var_index].U.CRD.CLOCK2];
    if (VAR[vi].PROC_INDEX)
      PROCESS[VAR[vi].PROC_INDEX].status = PROCESS[VAR[vi].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      rec_spec_process(d->u.crd.arc[ci].child);
    }
    break;

  case TYPE_CDD:
    vi = CLOCK[VAR[d->var_index].U.CDD.CLOCK1];
    if (VAR[vi].PROC_INDEX)
      PROCESS[VAR[vi].PROC_INDEX].status = PROCESS[VAR[vi].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT;
    vi = CLOCK[VAR[d->var_index].U.CDD.CLOCK2];
    if (VAR[vi].PROC_INDEX)
      PROCESS[VAR[vi].PROC_INDEX].status = PROCESS[VAR[vi].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      rec_spec_process(d->u.ddd.arc[ci].child);
    }
    break;

  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++) { 
      vi = d->u.hrd.hrd_exp->hrd_term[ci].var_index;
      if (VAR[vi].PROC_INDEX)
        PROCESS[VAR[vi].PROC_INDEX].status 
        = PROCESS[VAR[vi].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT;
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_spec_process(d->u.hrd.arc[ci].child);
    }
    break;

  case TYPE_LAZY_EXP: 
    spec_process(d->u.lazy.exp, FLAG_POLARITY_SPEC_PROCESS); 
    rec_spec_process(d->u.lazy.false_child);  
    rec_spec_process(d->u.lazy.true_child); 
    break; 

  case TYPE_FLOAT:
    if (VAR[d->var_index].PROC_INDEX) 
      PROCESS[VAR[d->var_index].PROC_INDEX].status = PROCESS[VAR[d->var_index].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) { 
      rec_spec_process(d->u.fdd.arc[ci].child); 
    }       
    break; 

  case TYPE_DOUBLE:
    if (VAR[d->var_index].PROC_INDEX) 
      PROCESS[VAR[d->var_index].PROC_INDEX].status = PROCESS[VAR[d->var_index].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) { 
      rec_spec_process(d->u.dfdd.arc[ci].child); 
    }       
    break; 

  default:
    if (VAR[d->var_index].PROC_INDEX) 
      PROCESS[VAR[d->var_index].PROC_INDEX].status = PROCESS[VAR[d->var_index].PROC_INDEX].status | FLAG_PROC_SIGNIFICANT; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      rec_spec_process(d->u.ddd.arc[ci].child); 
    }       
  }
}
/* rec_spec_process() */ 


void 	spec_process(psub, flag_polarity)
     struct ps_exp_type	*psub; 
     int		flag_polarity; 
{
  int				vi, i, jj, pi, lb, ub; 
  struct ps_bunit_type		*pbu; 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :

  case TYPE_NULL: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER: 
  case TYPE_TRASH: 
  case TYPE_CONSTANT: 
    
    return; 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      PROCESS[pi].status = PROCESS[pi].status | FLAG_PROC_SIGNIFICANT;
    return; 
    
  case TYPE_DISCRETE: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK: 
  case TYPE_POINTER: 
  case TYPE_BDD: {
    float	flb, fub; 
    int		flag; 
    
/*
    if (psub->u.atom.indirect_count) { 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) 
        PROCESS[pi].status = PROCESS[pi].status | FLAG_PROC_SIGNIFICANT;
      return; 
    } 
*/
    vi = psub->u.atom.var_index; 
    if (VAR[vi].PROC_INDEX) { 
      flag = get_integer_range(
        psub->u.atom.exp_base_proc_index, 0, &lb, &ub, &flb, &fub
      ); 
      if (lb <= 0) 
        lb = 1; 
      if (ub > PROCESS_COUNT) 
        ub = PROCESS_COUNT; 
      for (pi = lb; pi <= ub; pi++) 
        PROCESS[pi].status = PROCESS[pi].status | FLAG_PROC_SIGNIFICANT;
    } 
    else { 
      spec_process(psub->u.atom.exp_base_proc_index, flag_polarity); 
    } 
    return; 
  }
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
  
  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:  
  case ARITH_EQ : 
  case ARITH_NEQ : 
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    spec_process(psub->u.arith.lhs_exp, flag_polarity); 
    spec_process(psub->u.arith.rhs_exp, flag_polarity); 
    return; 
    
  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    for (i = 0; i < psub->u.ineq.term_count; i++) { 
      spec_process(psub->u.ineq.term[i].coeff, flag_polarity); 
      spec_process(psub->u.ineq.term[i].operand, flag_polarity); 
    } 
    spec_process(psub->u.ineq.offset, flag_polarity); 
    return; 

  case AND :
  case OR :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist;  
	 jj; 
	 jj--, pbu = pbu->bnext
	 ) {
      spec_process(pbu->subexp, flag_polarity); 
    }
    return;
  case NOT :
    spec_process(psub->u.bexp.blist->subexp, -1*flag_polarity); 
    return; 
  case IMPLY :
    spec_process(psub->u.bexp.blist->subexp, -1*flag_polarity); 
    spec_process(psub->u.bexp.blist->bnext->subexp, flag_polarity); 
    return;
  case FORALL: 
  case EXISTS: 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      PROCESS[pi].status = PROCESS[pi].status | FLAG_PROC_SIGNIFICANT; 
    spec_process(psub->u.qexp.child, flag_polarity); 
    return; 
  case EXISTS_ALWAYS: 
    if (flag_polarity == FLAG_ROOT_OAPPROX) 
      GSTATUS[INDEX_ZENO_CYCLE] 
      = GSTATUS[INDEX_ZENO_CYCLE] | FLAG_USE_APPROX_NONZENO;
    else
      GSTATUS[INDEX_ZENO_CYCLE] 
      = GSTATUS[INDEX_ZENO_CYCLE] | FLAG_USE_PLAIN_NONZENO;
    spec_process(psub->u.mexp.path_child, flag_polarity);
    return;
  case FORALL_ALWAYS:
  case FORALL_EVENTUALLY:
  case FORALL_CHANGE:
  case EXISTS_EVENTUALLY:
  case EXISTS_CHANGE:
  case FORALL_EVENT: 
    fprintf(RED_OUT, "\nHow come there is still such a modal operator in the specification ?\n");
    fflush(RED_OUT);
    exit(0);
    for (; 1; );
  case EXISTS_UNTIL:
    if (flag_polarity == FLAG_ROOT_OAPPROX)
      GSTATUS[INDEX_ZENO_CYCLE] 
      = GSTATUS[INDEX_ZENO_CYCLE] | FLAG_USE_APPROX_NONZENO;
    else
      GSTATUS[INDEX_ZENO_CYCLE] 
      = GSTATUS[INDEX_ZENO_CYCLE] | FLAG_USE_PLAIN_NONZENO;
    spec_process(psub->u.mexp.path_child, flag_polarity); 
    spec_process(psub->u.mexp.dest_child, flag_polarity); 
    return; 
  case FORALL_UNTIL:
    fprintf(RED_OUT, "\nspec_process: How come there is still a FORALL UNTIL in the specification ?\n"); 
    fflush(RED_OUT); 
    bk(0); 
    for (; 1; ); 
    return; 
  case RED: 
    FLAG_POLARITY_SPEC_PROCESS = flag_polarity; 
    rec_spec_process(psub->u.rpred.red); 
    return;
  }
}
  /* spec_process() */ 


void	sig_process_analyze() { 
  int	pi, xi, k; 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    PROCESS[pi].status = PROCESS[pi].status & MASK_GAME_ROLES; 

  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_DEADLOCK: 
  case TASK_ZENO: 
    if (SPEC_EXP ==  NULL) {
      SPEC_EXP = ps_exp_alloc(RED);
    }
    break; 
  default: 
    switch (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) {
    case FLAG_ROOT_OAPPROX: 
    case FLAG_ROOT_NOAPPROX: 
      spec_process(SPEC_EXP, FLAG_ROOT_NOAPPROX); 
      break; 
    default: 
      spec_process(SPEC_EXP, FLAG_ROOT_OAPPROX); 
    } 
  }

} 
/* sig_process_analyze() */ 



int	pfillin_count = 0; 

PROCESS_fillin()
{
  int 				pi, pj, vi, fmi, mi, imi, xi, ixi, ai;
  struct red_type		*filter; 
  struct index_link_type	*ip, *nip, *xip, **xp;

  /* The rest of the cases when symmetry or single local clock.
   */ 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    PROCESS[pi].depth_call = DEPTH_CALL; 	
  }
  plain_reachable();

  process_xtion_fillin(); 

/*
  fprintf(RED_OUT, "\nPROCESS's firable xtions:\n");
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    fprintf(RED_OUT, "\n---------------------------------------------------\nP%1d:%1d reachable modes:",
	    pi, PROCESS[pi].reachable_mode_count
	    );
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      fprintf(RED_OUT, "(%1d:%s)", PROCESS[pi].reachable_mode[imi], MODE[PROCESS[pi].reachable_mode[imi]].name);
    }
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);

    fprintf(RED_OUT, "mode distances:\n");
    for (mi = 0; mi < MODE_COUNT; mi++) {
      fprintf(RED_OUT, " %1d:%s:", mi, MODE[mi].name);
      if (PROCESS[pi].mode_distance_from_initial[mi] == MODE_COUNT)
        fprintf(RED_OUT, "oo;");
      else
        fprintf(RED_OUT, "%1d;", PROCESS[pi].mode_distance_from_initial[mi]);
    }
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);

    fprintf(RED_OUT, "P%1d:%1d:", pi, PROCESS[pi].firable_xtion_count);
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
      fprintf(RED_OUT, "(%1d)", PROCESS[pi].firable_xtion[ixi]);
    }
    fprintf(RED_OUT, "\n");
  }
  fprintf(RED_OUT, "\n");
  fflush(RED_OUT);
*/
  xp = (struct index_link_type **) malloc(XTION_COUNT*sizeof(struct index_link_type *));
  for (xi = 0; xi < XTION_COUNT; xi++) {
    xp[xi] = NULL;
    XTION[xi].process_count = 0;
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
      xi = PROCESS[pi].firable_xtion[ixi];
      XTION[xi].process_count++;
      xp[xi] = add_index(xp[xi], pi);
    }
    PROCESS[pi].red_stop = NORM_NO_RESTRICTION;
    if (   (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE)
        || ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_SIMULATE)
        || !(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
        ) {
      for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
        PROCESS[pi].red_stop
          = ddd_one_constraint
            (PROCESS[pi].red_stop, variable_index[TYPE_XTION_INSTANCE][pj][0], 0, 0);
      }

      red_mark(PROCESS[pi].red_stop, FLAG_GC_STABLE);
    } 
  }

  for (xi = 0; xi < XTION_COUNT; xi++) {
    XTION[xi].process = (int *) malloc(XTION[xi].process_count * sizeof(int));
    for (pi = 0, ip = xp[xi];
	 pi < XTION[xi].process_count;
	 pi++, ip = ip->next_index_link
	 ) {
      XTION[xi].process[pi] = ip->index;
    }
    free_index_list(xp[xi]);
  }
  free(xp);

  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
/*
    fprintf(RED_OUT, "VAR[vi=%1d].NAME:%s with PROC_INDEX=%1d\n", vi, VAR[vi].NAME, VAR[vi].PROC_INDEX); 
    fflush(RED_OUT); 
*/
    if (   (pi = VAR[vi].PROC_INDEX)
        && !(VAR[vi].STATUS & FLAG_VAR_PRIMED)
	) {
      int	imi, irs, vrs;

      switch (VAR[vi].TYPE) {
      case TYPE_DENSE:
	VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT = 0;
	VAR[vi].U.DENSE.MODE_RATE_SPEC = (struct mode_rate_spec_type *)
	  malloc(PROCESS[pi].reachable_mode_count * sizeof(struct mode_rate_spec_type));
	for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
	  mi = PROCESS[pi].reachable_mode[imi];
	  for (irs = 0; irs < MODE[mi].rate_spec_count; irs++) {
	    if (vi == MODE[mi].process_rate_spec[pi].rate_spec[irs].var_index) {
	      for (vrs = 0; vrs < VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT; vrs++)
	        if (   VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_lb_numerator
                       == MODE[mi].process_rate_spec[pi].rate_spec[irs].lb_numerator
                    && VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_lb_denominator
                       == MODE[mi].process_rate_spec[pi].rate_spec[irs].lb_denominator
                    && VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_ub_numerator
                       == MODE[mi].process_rate_spec[pi].rate_spec[irs].ub_numerator
                    && VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_ub_denominator
                       == MODE[mi].process_rate_spec[pi].rate_spec[irs].ub_denominator
                    )
                  break;

	      if (vrs >= VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT) {
                VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT++;
        	VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].red_mode_spec = ddd_atom(
        	  variable_index[TYPE_DISCRETE][pi][0], mi, mi
        	);
	        VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_lb_numerator
      	        = MODE[mi].process_rate_spec[pi].rate_spec[irs].lb_numerator;
                VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_lb_denominator
                = MODE[mi].process_rate_spec[pi].rate_spec[irs].lb_denominator;
                VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_ub_numerator
                = MODE[mi].process_rate_spec[pi].rate_spec[irs].ub_numerator;
                VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].rate_ub_denominator
                = MODE[mi].process_rate_spec[pi].rate_spec[irs].ub_denominator;
	      }
	      else
	        VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].red_mode_spec = red_bop(OR, 
	          VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs].red_mode_spec,
                  ddd_atom(variable_index[TYPE_DISCRETE][pi][0], mi, mi)
                );
	    }
	  }
	}
	if (VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT != PROCESS[pi].reachable_mode_count) {
	  struct mode_rate_spec_type	*mrs;
	  int				vrs;

	  mrs = (struct mode_rate_spec_type *)
	    malloc(VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT * sizeof(struct mode_rate_spec_type));
	  for (vrs = 0; vrs < VAR[vi].U.DENSE.MODE_RATE_SPEC_COUNT; vrs++) {
	    mrs[vrs] = VAR[vi].U.DENSE.MODE_RATE_SPEC[vrs];
	    red_mark(mrs[vrs].red_mode_spec, FLAG_GC_STABLE);
	  }
	  free(VAR[vi].U.DENSE.MODE_RATE_SPEC);
	  VAR[vi].U.DENSE.MODE_RATE_SPEC = mrs;
	}
        break;
      case TYPE_CLOCK:
        VAR[vi].U.CLOCK.MODE_RATE_SPEC_COUNT = 1;
	VAR[vi].U.CLOCK.MODE_RATE_SPEC = (struct mode_rate_spec_type *) malloc(sizeof(struct mode_rate_spec_type));
	VAR[vi].U.CLOCK.MODE_RATE_SPEC[0].red_mode_spec = NORM_NO_RESTRICTION;
	VAR[vi].U.CLOCK.MODE_RATE_SPEC[0].rate_lb_numerator = 1;
	VAR[vi].U.CLOCK.MODE_RATE_SPEC[0].rate_lb_denominator = 1;
	VAR[vi].U.CLOCK.MODE_RATE_SPEC[0].rate_ub_numerator = 1;
	VAR[vi].U.CLOCK.MODE_RATE_SPEC[0].rate_ub_denominator = 1;
	break;
      }
    }
  } 

  /* construct the condition for mode concavity & convexity */ 
  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED 
      && !(GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
      ) {
    GSTATUS[INDEX_TIME_MODE_SHAPES] 
    = GSTATUS[INDEX_TIME_MODE_SHAPES] | FLAG_TIME_MODE_ALL_TCONVEX; 
    for (mi = 0; mi < MODE_COUNT; mi++) { 
      int	ipi; 
    
      if (MODE[mi].status & FLAG_INVARIANCE_TIME_CONVEX) ; 
        continue; 
        
      for (ipi = 0; ipi < MODE[mi].process_count; ipi++) { 
        pi = MODE[mi].process[ipi]; 
        if (check_time_convexity(MODE[mi].invariance[pi].red)) 
          MODE[mi].status = MODE[mi].status | FLAG_INVARIANCE_TIME_CONVEX; 
        else 
          GSTATUS[INDEX_TIME_MODE_SHAPES] 
          = GSTATUS[INDEX_TIME_MODE_SHAPES] & ~FLAG_TIME_MODE_ALL_TCONVEX;
      } 
    } 	
  } 
  
  RT[INDEX_MODE_CONVEXITY] = NORM_NO_RESTRICTION; 
  RT[INDEX_MODE_CONCAVITY] = NORM_FALSE; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    struct red_type	*convex; 
    
    convex = NORM_FALSE; 
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) { 
      mi = PROCESS[pi].reachable_mode[imi]; 
      if (MODE[mi].status & FLAG_INVARIANCE_TIME_CONVEX) 
        convex = red_bop(OR, convex, 
          ddd_atom(variable_index[TYPE_DISCRETE][pi][OFFSET_MODE], 
            mi, mi
          )
        ); 
      else {
        RT[INDEX_MODE_CONCAVITY] = red_bop(OR, RT[INDEX_MODE_CONCAVITY], 
          ddd_atom(variable_index[TYPE_DISCRETE][pi][OFFSET_MODE], 
            mi, mi
          )
        ); 
      } 
    } 
    RT[INDEX_MODE_CONVEXITY] = red_bop(AND, convex, RT[INDEX_MODE_CONVEXITY]); 
  } 
  red_mark(RT[INDEX_MODE_CONVEXITY], FLAG_GC_STABLE);
}
  /* PROCESS_fillin() */
  



  
xtion_1st_reduce() { 
  int	xi, pc, ipi, pi, ipj, *arr, xc, ixi, ixj; 
  
  /* First delete those process that cannot fire some transitions. */ 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    PROCESS[pi].status = PROCESS[pi].status & ~FLAG_XTION_REDUCED; 
    
  for (xi = 1; xi < XTION_COUNT; xi++) { 
    pc = 0; 
    for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
      pi = XTION[xi].process[ipi]; 
      if (XTION[xi].red_trigger[pi] == NORM_FALSE) { 
      	XTION[xi].process[ipi] = 0; 
      	for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      	  if (PROCESS[pi].firable_xtion[ixi] == xi) { 
      	    PROCESS[pi].firable_xtion[ixi] = -1; 
      	    PROCESS[pi].status = PROCESS[pi].status | FLAG_XTION_REDUCED; 	
      	  } 
      	} 
      } 
      else 
        pc++; 
    } 
    if (pc != XTION[xi].process_count) { 
      arr = (int *) malloc(pc * sizeof(int)); 
      for (ipi = 0, ipj = 0; ipi < XTION[xi].process_count; ipi++) { 
      	if (XTION[xi].process[ipi]) { 
      	  arr[ipj++] = XTION[xi].process[ipi]; 	
      	} 
      } 
      free(XTION[xi].process); 
      XTION[xi].process_count = pc; 
      XTION[xi].process = arr; 
    } 
  } 
  
  /* 2nd, update the firable transitions. */ 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if (PROCESS[pi].status & FLAG_XTION_REDUCED) { 
      xc = 0; 
      for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
        if (PROCESS[pi].firable_xtion[ixi] >= 0) { 
          xc++; 	
        } 
      } 
      arr = (int *) malloc(xc * sizeof(int)); 
      for (ixi = 0, ixj = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
        if (PROCESS[pi].firable_xtion[ixi] >= 0) { 
      	  arr[ixj++] = PROCESS[pi].firable_xtion[ixi];  
        } 
      } 
      free(PROCESS[pi].firable_xtion); 
      PROCESS[pi].firable_xtion_count = xc; 
      PROCESS[pi].firable_xtion = arr; 
    }
  } 
  
  /* 3rd, delete those totally unfirable transitions. */ 
  
} 
  /* xtion_1st_reduce() */ 






/*********************************************************************************************************
 *
 */
 

struct red_type	*rec_add_necessary_lowerbound(d)
  struct red_type	*d;
{
  int				ci;
  struct red_type		*new_child, *result;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION)
      return(d);
  ce = cache1_check_result_key(OP_ADD_NECESSARY_LOWERBOUND, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      new_child = rec_add_necessary_lowerbound(bc->child);
      result = red_bop(OR, result, crd_one_constraint(new_child, d->var_index, bc->upper_bound));
    }
    if (VAR[d->var_index].U.CRD.CLOCK1) { 
      result = crd_one_constraint(result, 
        ZONE[0][VAR[d->var_index].U.CRD.CLOCK1], 0
      ); 
      if (VAR[d->var_index].U.CRD.CLOCK2) { 
        result = crd_one_constraint(result, 
          ZONE[0][VAR[d->var_index].U.CRD.CLOCK2], 0
        ); 
      }
    } 
    break; 
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_add_necessary_lowerbound(d->u.hrd.arc[ci].child);
      result = red_bop(OR, result, hrd_one_constraint(
          new_child, d->u.hrd.hrd_exp, d->u.hrd.arc[ci].ub_numerator, 
          d->u.hrd.arc[ci].ub_denominator
        )
      );
    }  	
    break; 
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_add_necessary_lowerbound(d->u.lazy.false_child), 
      rec_add_necessary_lowerbound(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    ); 
    break; 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_add_necessary_lowerbound(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, fdd_one_constraint(
        new_child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ) );
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_add_necessary_lowerbound(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, dfdd_one_constraint(
        new_child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ) );
    }
    break; 
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      new_child = rec_add_necessary_lowerbound(ic->child);
      result = red_bop(OR, result, ddd_one_constraint
			(new_child, d->var_index, ic->lower_bound, ic->upper_bound)
			);
    }
    break; 
  }

  return(ce->result = result);
}
/* rec_add_necessary_lowerbound() */





struct red_type	*red_add_necessary_lowerbound(d)
     struct red_type	*d;
{
  struct red_type	*result; 
  
  result = rec_add_necessary_lowerbound(d); 
  
  return(result); 
}
/* red_add_necessary_lowerbound() */




  
    
red_invariance()
{
  struct red_type		*disj;
  int				pi, imi, mi, gi, gi_spec_envr, gi_dscr_envr;
  struct parse_mode_type	*pm;

  RED_INVARIANCE = ((struct red_type **) malloc(PROCESS_COUNT * sizeof(struct red_type *)))-1;
  RT[gi = RT_TOP++] = NORM_NO_RESTRICTION;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    RED_INVARIANCE[pi] = NORM_FALSE;
/*
    fprintf(RED_OUT, "\n==[pi=%1d]===========================================\n", pi); 
*/
    for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
      mi = PROCESS[pi].reachable_mode[imi]; 
      /*
      fprintf(RED_OUT, "\n\nINVARIANCE RED[pi=%1d] at mi=%1d:\n", pi, mi);
      report_red_management();
      fflush(RED_OUT);
      */
      RED_INVARIANCE[pi] = red_bop(OR, RED_INVARIANCE[pi], 
        red_local(MODE[mi].invariance_exp, pi, 0)
      );
      /*
      red_print_graph(RED_INVARIANCE[pi]);
      fflush(RED_OUT);
      */
    }
/*
    fprintf(RED_OUT, "\n*****************\nRED_INVARIANCE[pi=%1d], before necessary lowerbound:\n", pi); 
    red_print_graph(RED_INVARIANCE[pi]); 
*/    
    RED_INVARIANCE[pi] = red_add_necessary_lowerbound(RED_INVARIANCE[pi]); 
/*    
    fprintf(RED_OUT, "RED_INVARIANCE[pi=%1d], after necessary lowerbound:\n", pi); 
    red_print_graph(RED_INVARIANCE[pi]); 
*/    
    RT[gi] = red_bop(AND, RT[gi], RED_INVARIANCE[pi]);
    /*
       fprintf(RED_OUT, "\nRT[DECLARED_GLOBAL_INVARIANCE] :\n");
       red_size(RT[gi], SIZE_REPORT, NULL, NULL);
    */
    red_mark(RED_INVARIANCE[pi], FLAG_GC_STABLE);
    garbage_collect(FLAG_GC_SILENT);
/*
    fprintf(RED_OUT, "\n----------------------------------\nINVARIANCE RED[pi=%1d]:\n", pi);
    red_print_graph(RED_INVARIANCE[pi]);
    fflush(RED_OUT); 
    */
  }
  RT[DECLARED_GLOBAL_INVARIANCE] = RT[gi]; 
  RT_TOP--; /* gi */ 
/*
  fprintf(RED_OUT, "\nThe invariance:\n"); 
  red_print_graph(RT[DECLARED_GLOBAL_INVARIANCE]); 
*/
  red_mark(RT[DECLARED_GLOBAL_INVARIANCE], FLAG_GC_STABLE); 
  garbage_collect(FLAG_GC_SILENT); 
  
  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
         == FLAG_SYSTEM_TIMED 
      && !(GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
      ) 
    if (check_time_convexity(RT[DECLARED_GLOBAL_INVARIANCE])) 
      GSTATUS[INDEX_TIME_MODE_SHAPES] 
      = GSTATUS[INDEX_TIME_MODE_SHAPES] | FLAG_TIME_MODE_ALL_TCONVEX; 
    else 
      GSTATUS[INDEX_TIME_MODE_SHAPES] 
      = GSTATUS[INDEX_TIME_MODE_SHAPES] & ~FLAG_TIME_MODE_ALL_TCONVEX;     
}
/* red_invariance() */ 





/***************************************************************************
 *
 */


struct sync_compound_rec_type { 
  int	count, max, 
  	status; 
#define FLAG_EVENT_QUANTIFIED_SYNC	1 
}; 

struct sync_xtion_rec_type { 
  struct a23tree_type		*parent; 
  int				count, *process; 
  struct sync_compound_rec_type	*sync; 
  struct red_type		*restriction; 
}; 


struct a23tree_type	*sync_xtion_tree; 


struct sync_xtion_rec_type	*sync_xtion_allocate()
{
  struct sync_xtion_rec_type	*sx; 
  int				pi, si; 

  sx = (struct sync_xtion_rec_type *) malloc(sizeof(struct sync_xtion_rec_type));
  sx->process = ((int *) malloc(PROCESS_COUNT*sizeof(int)))-1; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    sx->process[pi] = 0; 
  sx->sync = (struct sync_compound_rec_type *) malloc(GLOBAL_COUNT[TYPE_SYNCHRONIZER]*sizeof(struct sync_compound_rec_type)); 
  for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) {
    sx->sync[si].count = 0; 
    sx->sync[si].max = 0; 
    sx->sync[si].status = 0; 
  }
  sx->parent = NULL; 
  sx->count = 0;
  sx->restriction = NORM_FALSE; 
  return(sx); 
}
/* sync_xtion_allocate() */ 



sync_xtion_free(sx)
     struct sync_xtion_rec_type	*sx; 
{
  free(&(sx->process[1])); 
  free(sx->sync);  
  free(sx); 
}
/* sync_xtion_free() */




int	sync_xtion_comp(sx, sy)
	struct sync_xtion_rec_type	*sx, *sy; 
{
  int			flag, comp, pi, si; 

  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    if (sx->process[pi] < sy->process[pi]) 
      return(-1); 
    else if (sx->process[pi] > sy->process[pi])
      return(1); 

  for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
    if (sx->sync[si].count < sy->sync[si].count)
      return(-1); 
    else if (sx->sync[si].count > sy->sync[si].count)
      return(1); 

  return(0); 
}
  /* sync_xtion_comp() */ 




int	sync_xtion_count_inc(sx)
     struct sync_xtion_rec_type	*sx; 
{
  sx->count++;
}
/* sync_xtion_count_inc() */




sync_xtion_parent_set(sx, pa)
     struct sync_xtion_rec_type	*sx; 
     struct a23tree_type	*pa; 
{
  sx->parent = pa; 
}
  /* sync_xtion_parent_set() */ 



sync_xtion_print(sx, depth)
     struct sync_xtion_rec_type	*sx; 
     int			depth; 
{
  int			i, flag; 
  struct ddd_child_type	*ic; 

  for (i = depth; i; i--) 
    fprintf(RED_OUT, "    "); 

  if (!sx) {
    fprintf(RED_OUT, "NULL SYNC XTION\n"); 
    return; 
  } 

  fprintf(RED_OUT, "SX:%x;%d;%x;[", (unsigned int) sx, sx->count, (unsigned int) sx->parent);

  for (i = 1; i <= PROCESS_COUNT; i++) 
    if (sx->process[i]) 
      fprintf(RED_OUT, "(%1d)",i); 
    else 
      fprintf(RED_OUT, "-"); 

  fprintf(RED_OUT, "];["); 
  for (i = 0; i < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; i++) 
    fprintf(RED_OUT, "(%s:s%1d:m%1d:c%1d)", VAR[GSYNC[i].VAR_INDEX].NAME, sx->sync[i].status, sx->sync[i].max, sx->sync[i].count); 

  fprintf(RED_OUT, "];RESTRICTION=%x\n", (unsigned int) sx->restriction); 
}
  /* sync_xtion_print() */ 




struct sync_xtion_rec_type	*sync_xtion_copy(s) 
	struct sync_xtion_rec_type	*s; 
{
  struct sync_xtion_rec_type	*n;  
  int				pj, sip; 
	
  n = sync_xtion_allocate(); 
  for (pj = 1; pj <= PROCESS_COUNT; pj++) 
    n->process[pj] = s->process[pj]; 
  for (sip = 0; sip < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; sip++) {
    n->sync[sip].count = s->sync[sip].count; 
    n->sync[sip].max = s->sync[sip].max; 
    n->sync[sip].status = s->sync[sip].status; 
  }
  return(n); 
}
  /* sync_xtion_copy() */ 




int		*sync_party_proc, *sync_party_xtion; 

// The following array is important in the performance enhancement of 
// the synchronization exploration. 
// We starts #PS exploration in total from each of the processes. 
// The k'th exploration are for those synchronizations with no processes 
// indexed < k. 
// Thus each time when we add a new process to a synchronization exploration 
// frontier, we check if the process 
int		*PI_CONNECTING_LB, PI_CONNECTING_TOP; 

struct red_type	*red_sync_xi_one_proc( 
  int				pi,  
  struct sync_xtion_rec_type	*sx_parent, 
  int				depth
); 



struct red_type	*rec_sync_xi_restriction(sx, depth)
     struct sync_xtion_rec_type	*sx; 
     int			depth; 
{
  int				flag, si, sip, isip, ixi, xsi, xi, ipi, pi, pj, fxi, i; 
  struct sync_xtion_rec_type	*sy; 
  struct parse_xtion_sync_type	*pxs; 
  struct red_type		*result, *conj, *further_sync; 

/* 
  for (i = 0; i < depth; i++) 
    fprintf(RED_OUT, "  "); 
  fprintf(RED_OUT, "sx:"); 
  for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
    fprintf(RED_OUT, "%s:%1d; ", VAR[GSYNC[si].VAR_INDEX].NAME, sx->sync[si]);
  fprintf(RED_OUT, "\n"); 
*/   
  sy = (struct sync_xtion_rec_type *) add_23tree(sx, sync_xtion_tree, sync_xtion_comp, sync_xtion_free, 
    sync_xtion_count_inc, sync_xtion_parent_set, sync_xtion_print
  ); 
  if (sx != sy) {
/* 
    for (i = 0; i < depth; i++) 
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, "existing solution\n"); 
    red_print_graph_depth(sy->restriction, depth); 
*/ 
    return(sy->restriction); 
  }

  for (flag = TYPE_TRUE, si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
    if (sx->sync[si].count) {
      flag = TYPE_FALSE; 
      break; 
    } 

  if (flag) {
    for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
      if (   sx->sync[si].max > 1 
	  && (sx->sync[si].status & FLAG_EVENT_QUANTIFIED_SYNC)
	  ) {
        fprintf(RED_OUT, "Error: ambiguous quantified process identifier in \n"); 
        fprintf(RED_OUT, "       event %s while composing the following transitions:\n", VAR[variable_index[TYPE_SYNCHRONIZER][0][si]].NAME);
        for (pi = 0; pi < depth; pi++) { 
          print_xtion(sync_party_xtion[pi], sync_party_proc[pi]); 
        }
        fflush(RED_OUT); 
        exit(0); 
      } 

    result = NORM_TRUE; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      if (!sx->process[pi]) { 
	fxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
	result = ddd_one_constraint(result, fxi, 0, 0); 
      }
    for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
      if (sx->sync[si].max 
          > VAR[variable_index[TYPE_SYNCHRONIZER][0][si]].U.SYNC.UB
          ) {
        VAR[variable_index[TYPE_SYNCHRONIZER][0][si]].U.SYNC.UB 
        = sx->sync[si].max; 
      } 

    // The following are new patches for complex synchrnoizations 
    // that can only be determined by process address arithmetics and enforcers. 
    // In this case, we might first have to construct some synchronizations 
    // that seem the combination of several independent child 
    // synchronizations. 
    // On second thought of 2008.10.25, I think it is not necessary. 
    // So I removed it. 
/* 
    further_sync = NORM_FALSE; 
    for (pi = PI_CONNECTING_LB[PI_CONNECTING_TOP]+1; 
         pi <= PROCESS_COUNT; 
         pi++
         ) { 
      PI_CONNECTING_TOP++; 
      if (!sx->process[pi]) { 
        PI_CONNECTING_LB[PI_CONNECTING_TOP] = pi; 
	further_sync = red_bop(OR, further_sync, 
	  red_sync_xi_one_proc(pi, sx, depth)
	); 
      } 
      PI_CONNECTING_TOP--; 
    } 
    result = red_bop(AND, result, further_sync); 
*/
/* 
    for (i = 0; i < depth; i++) 
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, "a terminating successful solution\n");
    red_print_graph_depth(sy->restriction, depth); 
*/ 
    return(sx->restriction = result); 
  }

  result = NORM_FALSE; 
  if (sx->sync[si].count > 0) /* need an Xsync */ {
    for (ixi = 0; ixi < GSYNC[si].X_XTION_COUNT; ixi++) {
      xi = GSYNC[si].X_XTION[ixi].XTION_INDEX;        
      for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
	pi = XTION[xi].process[ipi]; 
	if (pi <= PI_CONNECTING_LB[PI_CONNECTING_TOP]) 
	  continue; 
	  
	fxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
	if (!sx->process[pi]) { 
	  sync_party_proc[depth] = pi; 
	  sync_party_xtion[depth] = xi; 
	  sy = sync_xtion_copy(sx); 
	  sy->process[pi] = TYPE_TRUE;
	  for (xsi = 0; xsi < XTION[xi].sync_count; xsi++) {
	    sip = XTION[xi].sync[xsi].sync_index; 
	    if (XTION[xi].sync[xsi].type > 0 /* ? */) { 
	      sy->sync[sip].count++;  
	      sy->sync[sip].max++;  
	    }
	    else 
	      sy->sync[sip].count--;  
	    if (   XTION[xi].sync[xsi].exp_quantification
	        && XTION[xi].sync[xsi].exp_quantification->type == TYPE_POINTER
	        ) 
	      sy->sync[sip].status = sy->sync[sip].status | FLAG_EVENT_QUANTIFIED_SYNC; 
	  } 
/* 
	  for (i = 0; i < depth; i++) 
	    fprintf(RED_OUT, "  "); 
	  fprintf(RED_OUT, "picking pi=%1d; xi=%1d;\n", pi, xi);
*/ 
	  conj = rec_sync_xi_restriction(sy, depth+1); 
	  if (conj != NORM_FALSE) {
	    conj = red_bop(AND, conj, ddd_atom(fxi, xi, xi)); 
	    result = red_bop(OR, result, conj); 
	  }
	}
      }
    } 
/* 
    for (i = 0; i < depth; i++) 
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, "a new X solution\n"); 
    red_print_graph_depth(result, depth); 
*/ 
    return(sx->restriction = result); 
  }
  else if (sx->sync[si].count < 0) /* need a Qsync */ {
    for (ixi = 0; ixi < GSYNC[si].Q_XTION_COUNT; ixi++) {
      xi = GSYNC[si].Q_XTION[ixi].XTION_INDEX; 
      for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
	pi = XTION[xi].process[ipi]; 
	if (pi <= PI_CONNECTING_LB[PI_CONNECTING_TOP]) 
	  continue; 

	fxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
	if (!sx->process[pi]) { 
	  sy = sync_xtion_copy(sx); 
	  sy->process[pi] = TYPE_TRUE; 
	  for (xsi = 0; xsi < XTION[xi].sync_count; xsi++) {
	    sip = XTION[xi].sync[xsi].sync_index; 
	    if (XTION[xi].sync[xsi].type > 0 /* ? */) { 
	      sy->sync[sip].count++;  
	      sy->sync[sip].max++;  
	    }
	    else 
	      sy->sync[sip].count--;  
	    if (   XTION[xi].sync[xsi].exp_quantification
	        && XTION[xi].sync[xsi].exp_quantification->type == TYPE_POINTER
	        ) 
	      sy->sync[sip].status = sy->sync[sip].status | FLAG_EVENT_QUANTIFIED_SYNC;  
	  } 
/* 
	  for (i = 0; i < depth; i++) 
	    fprintf(RED_OUT, "  "); 
	  fprintf(RED_OUT, "picking pi=%1d; xi=%1d;\n", pi, xi); 
*/ 
	  conj = rec_sync_xi_restriction(sy, depth+1); 
	  if (conj != NORM_FALSE) {
	    conj = red_bop(AND, conj, ddd_atom(fxi, xi, xi)); 
	    result = red_bop(OR, result, conj); 
	  }
	}
      }
    } 
/* 
    for (i = 0; i < depth; i++) 
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, "a new Q solution\n"); 
    red_print_graph_depth(result, depth); 
*/ 
    return(sx->restriction = result); 
  } 
}
  /* rec_sync_xi_restriction() */ 




struct red_type	*red_sync_xi_one_proc(pi, sx_parent, depth) 
	int				pi, depth; 
  	struct sync_xtion_rec_type	*sx_parent;
{
  int 				fxi, ixi, xi, isi, si;
  struct sync_xtion_rec_type	*sx;
  struct red_type		*conj, *result;
  
  result = NORM_FALSE; 
  sync_party_proc[depth] = pi; 
  fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];
  for (ixi = 1; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
    xi = PROCESS[pi].firable_xtion[ixi];
    sync_party_xtion[0] = xi; 
    sx = sync_xtion_copy(sx_parent);
    sx->process[pi] = TYPE_TRUE;

    /* This following loop setup the cache record. 
     */ 
    for (isi = 0; isi < XTION[xi].sync_count; isi++) {
      si = XTION[xi].sync[isi].sync_index;
      if (XTION[xi].sync[isi].type > 0 /* ? */) { 
        sx->sync[si].count++; 
        sx->sync[si].max++; 
      }
      else 
        sx->sync[si].count--; 
      if (   XTION[xi].sync[isi].exp_quantification
          && XTION[xi].sync[isi].exp_quantification->type == TYPE_POINTER
          ) 
        sx->sync[si].status = sx->sync[si].status | FLAG_EVENT_QUANTIFIED_SYNC;  
    }
/*
    fprintf(RED_OUT, "picking pi=%1d; xi=%1d;\n", pi, xi);
*/
    conj = rec_sync_xi_restriction(sx, 1);
    if (conj != NORM_FALSE) {
      conj = ddd_one_constraint(conj, fxi, xi, xi);
      result = red_bop(OR, result, conj);
    }
  }
  return(result); 
}
  /* red_sync_xi_one_proc() */ 
  
  
  
  

struct red_type	*red_sync_xi_restriction() { 
  struct sync_xtion_rec_type	*sx_root;
  int 				pc, pi; 
  
/*
  fprintf(RED_OUT,"sync_party_proc=%x..%x allocated.\n", 
	  sync_party_proc, sync_party_proc+PROCESS_COUNT
	  ); 
  fprintf(RED_OUT,"sync_party_xtion=%x..%x allocated.\n", 
	  sync_party_xtion, sync_party_xtion+PROCESS_COUNT
	  ); 
*/
  sync_party_proc = (int *) malloc(PROCESS_COUNT*sizeof(int));
  sync_party_xtion = (int *) malloc(PROCESS_COUNT*sizeof(int));

  init_23tree(&sync_xtion_tree);
  RT[XI_SYNC_ALL] = NORM_FALSE;

  /* Setup the initial mark of each processes as nodes in the graph. */
  sx_root = sync_xtion_allocate();
  PI_CONNECTING_LB = (int *) malloc((PROCESS_COUNT+1)*sizeof(int)); 
  PI_CONNECTING_TOP = 0; 
  for (PI_CONNECTING_LB[0] = 1; 
       PI_CONNECTING_LB[0] <= PROCESS_COUNT; 
       (PI_CONNECTING_LB[0])++
       ) { 
    RT[XI_SYNC_ALL] = red_bop(OR, RT[XI_SYNC_ALL], 
      red_sync_xi_one_proc(PI_CONNECTING_LB[0], sx_root, 0) 
    );
  }
  free(PI_CONNECTING_LB); 
  free_entire_23tree(sync_xtion_tree, sync_xtion_free);
  
  free(sync_party_proc); /* The two arrays on the left were allocated at the beginning of */
  free(sync_party_xtion);/* red_sync_xi_restriction() */ 
  
  return(RT[XI_SYNC_ALL]); 
} 
  /* red_sync_xi_restriction() */ 
  
  


struct red_type	*red_add_trigger_sync_bulk(d) 
	struct red_type	*d; 
{
  int			pi, fxi, ixi, xi; 
  struct red_type	*conj, *subresult; 
  
  if (d == NORM_FALSE) 
    return(d); 

  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\n**** adding trigger sync bulk ****\n"); 
  #endif 
   
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    subresult = NORM_FALSE;
    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n====(pi=%1d)====================\n", pi); 
    #endif 
    
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
      xi = PROCESS[pi].firable_xtion[ixi];
      #ifdef RED_DEBUG_PARSE_MODE 
      print_xtion(xi, pi); 
      #endif 
      
      conj = ddd_one_constraint(d, fxi, xi, xi); 
      conj = red_bop(AND, conj, XTION[xi].red_trigger[pi]); 
      if (xi && valid_mode_index(XTION[xi].src_mode_index)) {
        #ifdef RED_DEBUG_PARSE_MODE 
      	fprintf(RED_OUT, "MODE[XTION[xi=%1d].src_mode_index=%1d].invariance[pi=%1d].red:\n", 
      	  xi, XTION[xi].src_mode_index, pi
      	); 
      	red_print_graph(MODE[XTION[xi].src_mode_index].invariance[pi].red); 
        #endif 

        conj = red_bop(AND, conj, 
          MODE[XTION[xi].src_mode_index].invariance[pi].red
        ); 
      }
      subresult = red_bop(OR, subresult, conj);

      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "pi=%1d, xi=%1d, conj:\n", pi, xi); 
      red_print_graph(subresult); 
      #endif 
    }

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, 
      "\n------------------------------------\n"
    ); 
    fprintf(RED_OUT, "red_add_trigger_sync_bulk at pi=%1d\nd, before:", pi); 
    red_print_graph(d); 
    fprintf(RED_OUT, "subresult:\n"); 
    red_print_graph(subresult); 
    #endif 

    d = subresult;

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "pi=%1d, xrf:\n", pi); 
    red_print_graph(d); 
    #endif 
  } 
  return(d); 
}
  /* red_add_trigger_sync_bulk() */  
  
  



struct red_type	*red_add_lazy_trigger_sync_bulk(
  struct red_type	*d, 
  struct red_type	*space
) {
  int			pi, fxi, ixi, xi; 
  struct red_type	*conj, *bulk, *subresult; 
  
  if (d == NORM_FALSE || space == NORM_FALSE) 
    return(NORM_FALSE); 

  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\n**** adding lazy trigger sync bulk ****\n"); 
  #endif 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    subresult = NORM_FALSE;
    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\n====(pi=%1d)====================\n", pi); 
    #endif 

    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
      xi = PROCESS[pi].firable_xtion[ixi];

      #ifdef RED_DEBUG_PARSE_MODE 
      print_xtion(xi, pi); 
      #endif 

      bulk = ddd_one_constraint(d, fxi, xi, xi); 
      bulk = red_bop(AND, bulk, space); // Using the bulk&&space 
                                        // is helpful since the value of 
                                        // qfd sync variables is not in space
                                        // but in bulk. 
      if (XTION[xi].red_trigger[pi]->status & FLAG_RED_LAZY) { 
      	bulk = red_bop(AND, bulk, 
          red_abstract_lazy(XTION[xi].red_trigger[pi])
        ); 
        if (bulk == NORM_FALSE) 
          continue; 

        bulk = red_delayed_eval(XTION[xi].red_trigger[pi], pi, bulk); 
      }
      else { 
      	bulk = red_bop(AND, bulk, XTION[xi].red_trigger[pi]); 
        if (bulk == NORM_FALSE) 
          continue; 
      } 
      if (xi && valid_mode_index(XTION[xi].src_mode_index)) {
        #ifdef RED_DEBUG_PARSE_MODE 
      	fprintf(RED_OUT, "MODE[XTION[xi=%1d].src_mode_index=%1d].invariance[pi=%1d].red:\n", 
      	  xi, XTION[xi].src_mode_index, pi
      	); 
      	red_print_graph(MODE[XTION[xi].src_mode_index].invariance[pi].red); 
        #endif 

        bulk = red_delayed_eval(
          MODE[XTION[xi].src_mode_index].invariance[pi].red, 
          pi, 
          bulk
        ); 
      }
      subresult = red_bop(OR, subresult, bulk);

      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "pi=%1d, xi=%1d, conj:\n", pi, xi); 
      red_print_graph(subresult); 
      #endif 
    }

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, 
      "\n------------------------------------\n"
    ); 
    fprintf(RED_OUT, "red_add_trigger_sync_bulk at pi=%1d\nd, before:", pi); 
    red_print_graph(d); 
    fprintf(RED_OUT, "subresult:\n"); 
    red_print_graph(subresult); 
    #endif 
    
    d = subresult;

    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "pi=%1d, xrf:\n", pi); 
    red_print_graph(d); 
    #endif 
  } 
  return(d); 
}
  /* red_add_lazy_trigger_sync_bulk() */  
  
  



struct red_type	*red_holder_restriction(pi, xi, xsi) 
	int	pi, xi, xsi; 
{ 
  int			vi, ixj, xj, xsj, ipj, pj, vj, qsvi; 
  struct red_type	*subresult, *conj; 
  
  vi = variable_index[TYPE_QSYNC_HOLDER][pi][xsi]; 
  qsvi = XTION[xi].sync[xsi].qsync_vi; 
  qsvi = variable_index[TYPE_POINTER][pi][VAR[qsvi].OFFSET]; 
  if (XTION[xi].sync[xsi].type > 0 /* receive */) { 
    subresult = NORM_FALSE; 
    for (ixj = 0; ixj < GSYNC[XTION[xi].sync[xsi].sync_index].X_XTION_COUNT; ixj++) { 
      xj = GSYNC[XTION[xi].sync[xsi].sync_index].X_XTION[ixj].XTION_INDEX; 
      xsj = GSYNC[XTION[xi].sync[xsi].sync_index].X_XTION[ixj].PLACE_INDEX; 
      for (ipj = 0; ipj < XTION[xj].process_count; ipj++) { 
        pj = XTION[xj].process[ipj]; 
        vj = variable_index[TYPE_QSYNC_HOLDER][pj][xsj]; 
        conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
        conj = ddd_one_constraint(conj, vi, vj, vj); 
        conj = ddd_one_constraint(conj, vj, vi, vi); 
        conj = ddd_one_constraint(conj, qsvi, pj, pj);  
        subresult = red_bop(OR, subresult, conj); 
      }
    }
    return (subresult); 
  }
  else if (XTION[xi].sync[xsi].type < 0 /* xmission */) { 
    subresult = NORM_FALSE; 
    for (ixj = 0; ixj < GSYNC[XTION[xi].sync[xsi].sync_index].Q_XTION_COUNT; ixj++) { 
      xj = GSYNC[XTION[xi].sync[xsi].sync_index].Q_XTION[ixj].XTION_INDEX; 
      xsj = GSYNC[XTION[xi].sync[xsi].sync_index].Q_XTION[ixj].PLACE_INDEX; 
      for (ipj = 0; ipj < XTION[xj].process_count; ipj++) { 
        pj = XTION[xj].process[ipj]; 
        vj = variable_index[TYPE_QSYNC_HOLDER][pj][xsj]; 
        conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
        conj = ddd_one_constraint(conj, vi, vj, vj);         
        conj = ddd_one_constraint(conj, vj, vi, vi); 
        conj = ddd_one_constraint(conj, qsvi, pj, pj);  
        subresult = red_bop(OR, subresult, conj); 
      }
    }
    return (subresult); 
  }	      	
  else {
    fprintf(RED_OUT, "\nBug: how come we have a neutral synchronization %1d here at transtion %1d.\n", 
	    xi, xsi
	    ); 
    fflush(RED_OUT); 
    exit(0); 
  }  	
}
  /* red_holder_restriction() */ 




int	RER_PI, RER_XI, RER_XSI; 

struct red_type	*rec_quantified_address(psub)
     struct ps_exp_type	*psub;
{
  struct red_type	*result, *childx, *childy, *conj, *conjx, *conjy, *filter; 
  struct ps_bunit_type	*pbu; 
  int			vi, i, jj, ipi, si, 
			xi, xsi, cix, ciy, ixj, xj, xsj, ipj, pj, 
			vx, vy, v; 
/*
  fprintf(RED_OUT, " ** rir_count=%1d.\n", ++rir_count); 
  fprintf(RED_OUT, "\n >> "); 
  print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
*/
  switch (psub->type) { 
  case TYPE_PROCESS_COUNT: 
    return(ddd_atom(VI_VALUE, PROCESS_COUNT, PROCESS_COUNT)); 
  case TYPE_CONSTANT: 
    return(ddd_atom(VI_VALUE, psub->u.value, psub->u.value)); 
  case TYPE_FLOAT_CONSTANT: 
    return(fdd_atom(FLOAT_VALUE, psub->u.float_value, psub->u.float_value)); 
  case TYPE_NULL: 
    return(ddd_atom(VI_VALUE, 0, 0)); 
  case TYPE_LOCAL_IDENTIFIER: 
    return(ddd_atom(VI_VALUE, RER_PI, RER_PI)); 
  case TYPE_QSYNC_HOLDER: 
    result = NORM_FALSE; 
    if (XTION[RER_XI].sync[psub->u.qsholder.place_index].type > 0 /* receiving */) { 
      si = XTION[RER_XI].sync[psub->u.qsholder.place_index].sync_index; 
      for (ixj = 0; ixj < GSYNC[si].X_XTION_COUNT; ixj++) { 
        xj = GSYNC[si].X_XTION[ixj].XTION_INDEX; 
        xsj = GSYNC[si].X_XTION[ixj].PLACE_INDEX; 
        for (ipj = 0; ipj < XTION[xj].process_count; ipj++) { 
          pj = XTION[xj].process[ipj]; 
          conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
          conj = ddd_one_constraint(conj, VI_VALUE, pj, pj); 
          conj = ddd_one_constraint(conj, 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI], 	
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj], 
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj]
                                         );  
          conj = ddd_one_constraint(conj, 
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj], 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI], 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI]
                                         );  
           result = red_bop(OR, result, conj); 
        } 
      }
    }
    else if (XTION[RER_XI].sync[psub->u.qsholder.place_index].type < 0 /* transmitting */) { 
      si = XTION[RER_XI].sync[psub->u.qsholder.place_index].sync_index; 
      for (ixj = 0; ixj < GSYNC[si].Q_XTION_COUNT; ixj++) { 
        xj = GSYNC[si].Q_XTION[ixj].XTION_INDEX; 
        xsj = GSYNC[si].Q_XTION[ixj].PLACE_INDEX; 
        for (ipj = 0; ipj < XTION[xj].process_count; ipj++) { 
          pj = XTION[xj].process[ipj]; 
          conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
          conj = ddd_one_constraint(conj, VI_VALUE, pj, pj); 
          conj = ddd_one_constraint(conj, 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI], 	
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj], 
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj]
                                         );  
          conj = ddd_one_constraint(conj, 
                                         variable_index[TYPE_QSYNC_HOLDER][pj][xsj], 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI], 
                                         variable_index[TYPE_QSYNC_HOLDER][RER_PI][RER_XSI]
                                         );  
          result = red_bop(OR, result, conj); 
        } 
      }
    }
    else { 
      fprintf(RED_OUT, "\nBug: how come we have a neutral synchronization %1d here at transtion %1d.\n", 
	      xi, xsi
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    return(result); 

  case TYPE_REFERENCE:
  case TYPE_DEREFERENCE: 
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER:
    fprintf(RED_OUT, 
      "Error: Dynamic address computation in synchronizer enforcer.\n"
    ); 
    bk(" "); 
    return;

  case BIT_NOT: 
    childx = rec_quantified_address(psub->u.exp); 
    if (childx == NORM_FALSE || childx == NORM_NO_RESTRICTION) 
      return(childx); 
    result = NORM_FALSE; 
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) { 
      conjx = NORM_FALSE; 
      for (vx = childx->u.ddd.arc[cix].lower_bound; 
           vx <= childx->u.ddd.arc[cix].upper_bound; 
           vx++
           ) { 
        v = ~vx; 
        conjx = red_bop(OR, conjx, ddd_atom(VI_VALUE, v, v)); 
      } 
      result = red_bop(OR, result, 
        red_bop(AND, conjx, childx->u.ddd.arc[cix].child)
      ); 
    } 
    return(result); 
      
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp);
    if (childx->var_index != VI_VALUE || childy->var_index != VI_VALUE) {
      fprintf(RED_OUT, 
        "\nERROR: Unexected LHS or RHS of bitwise evaluation:\n"
      );  
      red_print_graph(childx); 
      red_print_graph(childy); 
      fflush(RED_OUT); 
      exit(0); 
    }
    result = NORM_FALSE; 
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) { 
      conjx = NORM_FALSE; 
      for (vx = childx->u.ddd.arc[cix].lower_bound; 
           vx <= childx->u.ddd.arc[cix].upper_bound; 
           vx++
           ) { 
        for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) { 
          conjy = NORM_FALSE; 
          for (vy = childy->u.ddd.arc[ciy].lower_bound; 
               vy <= childy->u.ddd.arc[ciy].upper_bound; 
               vy++
               ) { 
            v = bit_op_value(psub->type, vx, vy); 
            conjy = red_bop(OR, conjy, ddd_atom(VI_VALUE, v, v)); 
          }
          conjx = red_bop(OR, conjx, 
            red_bop(AND, conjy, childy->u.ddd.arc[ciy].child)
          ); 
        }
      }
      result = red_bop(OR, result, 
        red_bop(AND, conjx, childx->u.ddd.arc[cix].child)
      ); 
    }
    return(result);
  case ARITH_ADD:
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp);
    return(red_add_value(1, childx, 1, childy));
  case ARITH_MINUS:
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp);
    return(red_add_value(1, childx, -1, childy));
  case ARITH_MULTIPLY:
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp);
    return(red_multiply_value(childx, childy));
  case ARITH_DIVIDE:
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp); 
    result = NORM_FALSE;
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) 
      for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) {
	conj = red_bop(AND, childx->u.ddd.arc[cix].child, childy->u.ddd.arc[ciy].child); 
	if (conj != NORM_FALSE) {
	  filter = NORM_FALSE; 
	  for (vx = childx->u.ddd.arc[cix].lower_bound; vx <= childx->u.ddd.arc[cix].upper_bound; vx++) 
	    for (vy = childy->u.ddd.arc[ciy].lower_bound; vy <= childy->u.ddd.arc[ciy].upper_bound; vy++) 
	      if (vy) {
		v = vx / vy; 
		filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v, v));
	      }
	  conj = red_bop(AND, conj, filter); 
	  result = red_bop(OR, result, conj); 
	}
      }
    return(result); 
  case ARITH_MODULO:
    childx = rec_quantified_address(psub->u.arith.lhs_exp);
    childy = rec_quantified_address(psub->u.arith.rhs_exp); 
    result = NORM_FALSE;
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) 
      for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) {
	conj = red_bop(AND, childx->u.ddd.arc[cix].child, childy->u.ddd.arc[ciy].child); 
	if (conj != NORM_FALSE) {
	  filter = NORM_FALSE; 
	  for (vx = childx->u.ddd.arc[cix].lower_bound; vx <= childx->u.ddd.arc[cix].upper_bound; vx++) 
	    for (vy = childy->u.ddd.arc[ciy].lower_bound; vy <= childy->u.ddd.arc[ciy].upper_bound; vy++) 
	      if (vy) {
		v = vx % vy; 
		filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v, v));
	      }
	  conj = red_bop(AND, conj, filter); 
	  result = red_bop(OR, result, conj); 
	}
      }
    return(result); 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal exp type %1d in rec_quantified_address.\n", 
      psub->type
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
/* rec_quantified_address() */


struct red_type	*red_addr_holder_range(
  int	pi, 
  int	xi, 
  int	xsi, 
  int	pj_lb, 
  int	pj_ub
) { 
  struct red_type	*result, *conj; 
  int			gi, vi, pj, ixj, ipj, xj, xsj, vj; 
  
  gi = XTION[xi].sync[xsi].sync_index; 
  vi = variable_index[TYPE_QSYNC_HOLDER][pi][xsi]; 
  result = NORM_FALSE; 
  if (XTION[xi].sync[xsi].type > 0 /* receiving */) {
    for (pj = pj_lb; pj <= pj_ub; pj++) {  
      for (ixj = 0; ixj < GSYNC[gi].X_XTION_COUNT; ixj++) { 
        xj = GSYNC[gi].X_XTION[ixj].XTION_INDEX;
        for (ipj = 0; ipj < XTION[xj].process_count; ipj++) 
          if (XTION[xj].process[ipj] == pj) 
            break; 
        if (ipj >= XTION[xj].process_count) 
          continue; 
        xsj = GSYNC[gi].X_XTION[ixj].PLACE_INDEX; 

        vj = variable_index[TYPE_QSYNC_HOLDER][pj][xsj]; 
        conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
        conj = ddd_one_constraint(conj, vi, vj, vj); 
        conj = ddd_one_constraint(conj, vj, vi, vi); 
        result = red_bop(OR, result, conj); 
      }
    }
  }
  else { 
    for (pj = pj_lb; pj <= pj_ub; pj++) {  
      for (ixj = 0; ixj < GSYNC[gi].Q_XTION_COUNT; ixj++) { 
        xj = GSYNC[gi].Q_XTION[ixj].XTION_INDEX;
        for (ipj = 0; ipj < XTION[xj].process_count; ipj++) 
          if (XTION[xj].process[ipj] == pj) 
            break; 
        if (ipj >= XTION[xj].process_count) 
          continue; 
        xsj = GSYNC[gi].Q_XTION[ixj].PLACE_INDEX; 
        vj = variable_index[TYPE_QSYNC_HOLDER][pj][xsj]; 
        conj = ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj); 
        conj = ddd_one_constraint(conj, vi, vj, vj); 
        conj = ddd_one_constraint(conj, vj, vi, vi); 
        result = red_bop(OR, result, conj); 
      }
    }
  }
  return(result); 
} 
  /* red_addr_holder_range() */ 




struct red_type	*red_quantified_address(exp_address, pi, xi, xsi) 
	struct ps_exp_type	*exp_address; 
	int			pi, xi, xsi; 
{ 
  struct red_type	*conj, *result, *subresult; 
  int			pj, ci; 
  
  RER_PI = pi; 
  RER_XI = xi; 
  RER_XSI = xsi; 
  
  conj = rec_quantified_address(exp_address); 
  result = NORM_FALSE; 
  if (XTION[xi].sync[xsi].type) { 
    for (ci = 0; ci < conj->u.ddd.child_count; ci++) { 
      subresult = red_addr_holder_range(
        pi, xi, xsi, 
        conj->u.ddd.arc[ci].lower_bound, 
        conj->u.ddd.arc[ci].upper_bound
      );   
      subresult = red_bop(AND, conj->u.ddd.arc[ci].child, subresult); 
      result = red_bop(OR, result, subresult); 
    } 
    return(result); 
  } 
  else { 
    fprintf(RED_OUT, "\nBug: how come we have a neutral synchronization %1d here at transtion %1d.\n", 
	    xi, xsi
	    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  
  return(result);  
} 
  /* red_quantified_address() */  
  
  



struct a23tree_type	*qsync_tree; 

struct red_type	*rec_add_sync_proc_holders(d)
     struct red_type	*d; 
{
  int                 		ci, xi, xsi, pi, pj, qsvi, 
				local_flag, lb, ub; 
  struct red_type		*result, *conj, *subresult, *child;
  struct ddd_child_type 	*ic;
  struct crd_child_type		*bc; 
  struct rec_type		*rec, *nrec; 
  struct parse_variable_type	*pv; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) {
/*
    fprintf(RED_OUT, "\n************\nadd sync place input:\n"); 
    red_print_graph(d); 
    fprintf(RED_OUT, "add sync place trivial output:\n"); 
    red_print_graph(d); 
*/
    return(d);
  }
  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, qsync_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE : 
    pi = VAR[d->var_index].PROC_INDEX; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      subresult = NORM_FALSE; 
      for (xi = d->u.ddd.arc[ci].lower_bound; 
           xi <= d->u.ddd.arc[ci].upper_bound; 
           xi++
           ) { 
/*
      	fprintf(RED_OUT, "testing XTION[xi=%1d].status against=%x quantified sync\n", 
		    xi, XTION[xi].status
		    ); 
*/
      	conj = NORM_NO_RESTRICTION; 
      	for (xsi = 0; xsi < XTION[xi].sync_count; xsi++) { 
          switch (XTION[xi].sync[xsi].status) { 
          case FLAG_ADDRESS_HOLDER: 
            pv = XTION[xi].sync[xsi].exp_quantification->u.qsholder.qsync_var; 
            qsvi = variable_index[pv->type][pi][pv->index]; 
/*
            fprintf(RED_OUT, 
              "\nAdding address holder: pi %1d, xi %1d, xsi %1d, qsvi %1d:%s\n", 
              pi, xi, xsi, qsvi, VAR[qsvi].NAME
            ); 
*/
            local_flag = red_get_vi_range( 
              XTION[xi].red_trigger[pi], qsvi, &lb, &ub
            );  
/*
            fprintf(RED_OUT, 
              "extracting flag=%1d, lb=%1d, ub=%1d from trigger:\n", 
              local_flag, lb, ub
            ); 
            red_print_graph(XTION[xi].red_trigger[pi]); 
*/
            if (local_flag == FLAG_SPECIFIC_VALUE) {  
              if (lb < 1) 
                lb = 1; 
              child = red_addr_holder_range(pi, xi, xsi, lb, ub); 
/*
              red_print_graph(child); 
*/
              conj = red_bop(AND, conj, child); 
            }
            else if (local_flag == FLAG_NO_VALUE)  
              conj = NORM_FALSE; 
            else if (local_flag == FLAG_ANY_VALUE) {
              child = red_holder_restriction(pi, xi, xsi); 
/*
              red_print_graph(child); 
*/
              conj = red_bop(AND, conj, child);
            }
            break; 
          case FLAG_ADDRESS_ENFORCER: 
            child = red_quantified_address(
              XTION[xi].sync[xsi].exp_quantification, 
              pi, xi, xsi
            ); 
/*
            fprintf(RED_OUT, 
              "\nAdding address enforcer: pi %1d, xi %1d, xsi %1d, exp:\n", 
              pi, xi, xsi 
            ); 
            pcform(XTION[xi].sync[xsi].exp_quantification); 
            red_print_graph(child); 
*/
            conj = red_bop(AND, conj, child); 
            break; 
          default: 
            break; 
          }       	    
      	} 
      	for (; xsi < LOCAL_COUNT[TYPE_QSYNC_HOLDER]; xsi++) { 
      	  conj = ddd_one_constraint(
      	    conj, variable_index[TYPE_QSYNC_HOLDER][pi][xsi], 0, 0
      	  ); 
      	} 
        conj = ddd_one_constraint(conj, d->var_index, xi, xi); 
        subresult = red_bop(OR, subresult, conj); 
      }
      subresult = red_bop(AND, subresult, 
        rec_add_sync_proc_holders(ic->child)
      ); 
      result = red_bop(OR, result, subresult); 
    } 
    break; 

  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_add_sync_proc_holders(bc->child);
      result = red_bop(OR, result, crd_one_constraint(
        child, d->var_index, bc->upper_bound
      ) );
    }
    break; 
    
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_add_sync_proc_holders(
        d->u.hrd.arc[ci].child
      );
      result = red_bop(OR, result, hrd_one_constraint(
        child, d->u.hrd.hrd_exp, d->u.hrd.arc[ci].ub_numerator, 
        d->u.hrd.arc[ci].ub_denominator
      ) );
    }  	
    break; 

  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
//     result = lazy_subtree(
      rec_add_sync_proc_holders(d->u.lazy.false_child), 
      rec_add_sync_proc_holders(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_add_sync_proc_holders(d->u.fdd.arc[ci].child); 
      conj = ddd_one_constraint(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_add_sync_proc_holders(d->u.dfdd.arc[ci].child); 
      conj = ddd_one_constraint(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      conj = rec_add_sync_proc_holders(ic->child); 
      conj = ddd_one_constraint(conj, d->var_index, ic->lower_bound, ic->upper_bound); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  }
/*
  fprintf(RED_OUT, "\n************\nadd sync place input:\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "add sync place computed output:\n"); 
  red_print_graph(result); 
*/
  return(rec->result = result); 
}
/* rec_add_sync_proc_holders() */





struct red_type	*rec_replace_sync_proc_holders(d, xi) 
     struct red_type	*d; 
     int		xi; 
{
  int			ci, xsi, svi, qsvi, vj; 
  struct red_type	*result, *conj, *child, *subresult;
  struct ddd_child_type	*ic;
  struct crd_child_type	*bc; 
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, qsync_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(d->u.ddd.arc[ci]); 
      for (xi = ic->lower_bound; xi <= ic->upper_bound; xi++) { 
        conj = ddd_one_constraint(
          rec_replace_sync_proc_holders(ic->child, xi), 
          d->var_index, xi, xi
        ); 
        result = red_bop(OR, result, conj); 
      }
    } 
    break; 
  case TYPE_QSYNC_HOLDER: 
    xsi = VAR[d->var_index].OFFSET; 
    if (     xi 
    	  && xsi < XTION[xi].sync_count
    	  && (qsvi = XTION[xi].sync[xsi].qsync_vi) >= 0
    	  ) { 
      svi = variable_index[TYPE_POINTER]
            [VAR[d->var_index].PROC_INDEX]
            [VAR[qsvi].OFFSET]; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]); 
        for (vj = ic->lower_bound; vj <= ic->upper_bound; vj++) { 
          conj = ddd_one_constraint(
            rec_replace_sync_proc_holders(ic->child, xi), 
            svi, VAR[vj].PROC_INDEX, VAR[vj].PROC_INDEX 
          ); 
          conj = ddd_one_constraint(conj, d->var_index, vj, vj); 
          result = red_bop(OR, result, conj); 
        }
      }
    } 
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]); 
        conj = rec_replace_sync_proc_holders(ic->child, xi); 
        conj = ddd_one_constraint(conj, d->var_index, ic->lower_bound, ic->upper_bound); 
        result = red_bop(OR, result, conj); 
      }
    }
    break; 
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_replace_sync_proc_holders(bc->child);
      result = red_bop(OR, result, crd_one_constraint(
        child, d->var_index, bc->upper_bound
      ) );
    }
    break; 
    
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_replace_sync_proc_holders(
        d->u.hrd.arc[ci].child
      );
      result = red_bop(OR, result, hrd_one_constraint(
        child, d->u.hrd.hrd_exp, d->u.hrd.arc[ci].ub_numerator, 
        d->u.hrd.arc[ci].ub_denominator
      ) );
    }  	
    break; 

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_replace_sync_proc_holders(d->u.lazy.false_child), 
      rec_replace_sync_proc_holders(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
  
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_replace_sync_proc_holders(d->u.fdd.arc[ci].child); 
      conj = fdd_one_constraint(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_replace_sync_proc_holders(d->u.dfdd.arc[ci].child); 
      conj = dfdd_one_constraint(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      conj = rec_replace_sync_proc_holders(ic->child); 
      conj = ddd_one_constraint(conj, d->var_index, ic->lower_bound, ic->upper_bound); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  }
  return(rec->result = result); 
}
/* rec_replace_sync_proc_holders() */






int	SMS_PI, SMS_PJ, SMS_PI_LB, SMS_PI_UB; 

struct red_type	*rec_sync_master_proc_index_one_pair(d) 
     struct red_type	*d; 
{
  int			ci, lb, ub, b; 
  struct red_type	*result, *child, *conj;
  struct ddd_child_type	*ic;
  struct crd_child_type	*bc;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, (struct red_type *) (SMS_PI_LB*PROCESS_COUNT+SMS_PI_UB)); 
  nrec = (struct rec_type *) add_23tree(
    rec, qsync_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_sync_master_proc_index_one_pair(bc->child);
      result = red_bop(OR, result, crd_one_constraint(
        child, d->var_index, bc->upper_bound
      ) );
    }
    break; 
    
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_sync_master_proc_index_one_pair(
        d->u.hrd.arc[ci].child
      );
      result = red_bop(OR, result, hrd_one_constraint(
        child, d->u.hrd.hrd_exp, d->u.hrd.arc[ci].ub_numerator, 
        d->u.hrd.arc[ci].ub_denominator
      ) );
    }  	
    break; 

  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_sync_master_proc_index_one_pair(d->u.lazy.false_child), 
      rec_sync_master_proc_index_one_pair(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_XTION_INSTANCE: 
    if (d->u.ddd.arc[0].lower_bound == 0) { 
      ic = &(d->u.ddd.arc[0].child->u.ddd.arc[0]); 
      conj = rec_sync_master_proc_index_one_pair(ic->child); 
      conj = ddd_one_constraint(conj, 
        d->u.ddd.arc[0].child->var_index, 
        ic->lower_bound, 
        ic->upper_bound
      ); 
      conj = ddd_one_constraint(conj, d->var_index, 0, 0); 
      result = red_bop(OR, result, conj); 
    } 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      ic = &(d->u.ddd.arc[ci]); 
      lb = ic->lower_bound; 
      if (lb == 0) 
        lb = 1; 
      ub = ic->upper_bound; 
      if (lb > ub) 
        continue; 
      conj = rec_sync_master_proc_index_one_pair(ic->child); 
      conj = ddd_one_constraint(conj, d->var_index, lb, ub); 
      result = red_bop(OR, result, conj); 
    }
    break; 
    
  case TYPE_ACTION_INSTANCE: 
    if (VAR[d->var_index].PROC_INDEX == SMS_PI) { 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
        ic = &(d->u.ddd.arc[ci]); 
        SMS_PI_LB = ic->lower_bound; 
        SMS_PI_UB = ic->upper_bound; 
        child = rec_sync_master_proc_index_one_pair(ic->child); 
        result = red_bop(OR, result, child); 
      } 
      SMS_PI_LB = 0; 
      SMS_PI_UB = 0; 
      break; 
    } 
    else if (VAR[d->var_index].PROC_INDEX == SMS_PJ) { 
      ci = d->u.ddd.child_count-1; 
      for (; ci >= 0; ci--) { 
        ic = &(d->u.ddd.arc[ci]); 
        if (ic->upper_bound < SMS_PI_UB) 
          ub = ic->upper_bound; 
        else 
          ub = SMS_PI_UB; 
        if (ic->lower_bound < SMS_PI_LB) 
          lb = ic->lower_bound; 
        else 
          lb = SMS_PI_LB; 
        conj = NORM_FALSE; 
        for (b = lb; b <= ub; b++) 
          conj = red_bop(OR, conj, 
            ddd_one_constraint(ddd_atom(d->var_index, b, b), 
              variable_index[TYPE_ACTION_INSTANCE][SMS_PI][0], b, b
          ) ); 
        child = red_bop(AND, conj, ic->child); 
        result = red_bop(OR, result, child); 
      } 
      break; 
    } 
  
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_sync_master_proc_index_one_pair(d->u.fdd.arc[ci].child); 
      conj = fdd_one_constraint(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_sync_master_proc_index_one_pair(d->u.dfdd.arc[ci].child); 
      conj = dfdd_one_constraint(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      conj = rec_sync_master_proc_index_one_pair(ic->child); 
      conj = ddd_one_constraint(conj, d->var_index, 
        ic->lower_bound, ic->upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  }
  return(rec->result = result); 
}
/* rec_sync_master_proc_index_one_pair() */



struct red_type	*red_sync_master_proc_index_one_pair(
  struct red_type	*d, 
  int			pi, 
  int			pj
) {
  struct red_type	*result; 
  
  SMS_PI = pi; 
  SMS_PJ = pj; 
  SMS_PI_LB = 0; 
  SMS_PI_UB = 0; 
  
  init_23tree(&qsync_tree); 
  result = rec_sync_master_proc_index_one_pair(d); 
  free_entire_23tree(qsync_tree, rec_free);   

  return(result); 
}
  /* red_sync_master_proc_index_one_pair() */ 
  
  
  
struct red_type	*red_sync_master_proc_index_one_step(struct red_type *d) { 
  int			pi, pj, ipi, ipj, xi, xj, qi, qj, qvi, qvj, 
        		w, w_xi, w_xj, w_qij; 
  struct red_type	*conj; 
  
  RT[w = RT_TOP++] = d; 
  for (xi = 1; xi < XTION_COUNT; xi++) { 
    if (XTION[xi].sync_count <= 0) 
      continue; 
    for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
      pi = XTION[xi].process[ipi];  
    
      RT[w_xi = RT_TOP++] = ddd_one_constraint(RT[w], 
        variable_index[TYPE_XTION_INSTANCE][pi][0], xi, xi
      ); 
      
      RT[w] = red_bop(SUBTRACT, RT[w], 
        ddd_atom(variable_index[TYPE_XTION_INSTANCE][pi][0], xi, xi) 
      ); 
      
      for (xj = 1; xj < XTION_COUNT; xj++) { 
        if (XTION[xj].sync_count <= 0) 
          continue; 
        for (ipj = 0; ipj < XTION[xj].process_count; ipj++) { 
          pj = XTION[xj].process[ipj]; 
          if (pi >= pj) 
            continue; 
            
          RT[w_xj = RT_TOP++] = ddd_one_constraint(RT[w_xi], 
            variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj
          ); 
      
          RT[w_xi] = red_bop(SUBTRACT, RT[w_xi], 
            ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], xj, xj) 
          ); 
          for (qi = 0; qi < XTION[xi].sync_count; qi++) { 
            qvi = variable_index[TYPE_QSYNC_HOLDER][pi][qi]; 
            for (qj = 0; qj < XTION[xj].sync_count; qj++) { 
              if (   XTION[xi].sync[qi].type + XTION[xj].sync[qj].type == 0
                  && XTION[xi].sync[qi].sync_index 
                     == XTION[xj].sync[qj].sync_index 
                  ) { 
                qvj = variable_index[TYPE_QSYNC_HOLDER][pj][qj]; 
                conj = ddd_atom(qvi, qvj, qvj); 
                conj = ddd_one_constraint(conj, qvj, qvi, qvi);  
                RT[w_qij = RT_TOP++] = red_bop(EXTRACT, RT[w_xj], conj); 
                RT[w_xj] = red_bop(SUBTRACT, RT[w_xj], conj); 

                fprintf(RED_OUT, 
                  "\n>>>>>>>>>>>>>\nbefore red_sync_master_proc_index_one_pair()\n"
                ); 
                fprintf(RED_OUT, 
                  "pi=%1d:qvi=%1d, pj=%1d:qvj=%1d\n", 
                  pi, qvi, pj, qvj 
                ); 
                red_print_graph(RT[w_qij]); 

                RT[w_qij] = red_sync_master_proc_index_one_pair(
                  RT[w_qij], pi, pj
                ); 

                fprintf(RED_OUT, 
                  " after red_sync_master_proc_index_one_pair()\n"
                ); 
                fprintf(RED_OUT, 
                  "pi=%1d:qvi=%1d, pj=%1d:qvj=%1d\n", 
                  pi, qvi, pj, qvj 
                ); 
                red_print_graph(RT[w_qij]); 

                RT[w_xj] = red_bop(OR, RT[w_xj], RT[w_qij]); 
                RT_TOP--; // w_qij 
              } 
            } 	
          } 
          RT[w_xi] = red_bop(OR, RT[w_xi], RT[w_xj]); 
          RT_TOP--; // w_xj 
        }
      }
      RT[w] = red_bop(OR, RT[w], RT[w_xi]); 
      RT_TOP--; // w_xi 
    } 
  } 
  RT_TOP--; // w 
  return(RT[w]); 
}
  /* red_sync_master_proc_index_one_step() */ 
  
  




struct red_type	*red_sync_master_proc_index(struct red_type *d) { 
  struct red_type	*result, *prefix, *seq, *conj; 
  int			pi, pj; 
  
  for (result = NORM_FALSE; result != d; ) { 
    result = d; 
    d = red_sync_master_proc_index_one_step(result); 
  } 
  
  result = NORM_FALSE; 
  prefix = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    seq = ddd_one_constraint(prefix, 
      variable_index[TYPE_XTION_INSTANCE][pi][0], 1, XTION_COUNT-1
    ); 
    for (pj = pi+1; pj<= PROCESS_COUNT; pj++) { 
      conj = ddd_one_constraint(
        ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], 0, 0), 
        variable_index[TYPE_ACTION_INSTANCE][pj][0], pj, pj
      ); 
      if (XTION_COUNT > 1) { 
      	conj = red_bop(OR, conj, 
      	  ddd_one_constraint(
            ddd_atom(variable_index[TYPE_XTION_INSTANCE][pj][0], 
              1, XTION_COUNT-1
            ), 
            variable_index[TYPE_ACTION_INSTANCE][pj][0], pi, pi
        ) ); 
      } 
      seq = red_bop(AND, seq, conj); 
    } 
    result = red_bop(OR, result, red_bop(AND, seq, d)); 
    prefix = red_bop(AND, prefix, 
      ddd_one_constraint(
        ddd_atom(variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0), 
        variable_index[TYPE_ACTION_INSTANCE][pi][0], pi, pi
    ) );  
  } 

  return(result); 
}
  /* red_sync_master_proc_index() */ 





struct a23tree_type	*risx_tree; 

struct red_type	*rec_keep_pure_sync_bulk_with_qfd_syncs(d)
     struct red_type	*d;
{
  int			ci, c1, c2;
  struct red_type	*child, *result;
  struct hrd_exp_type	*he;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, risx_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(ic->child);
      child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(bc->child);
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(hc->child);
      result = red_bop(OR, result, child);	
    }
    break;
  case TYPE_LAZY_EXP: 
    result = red_bop(OR, 
      rec_keep_pure_sync_bulk_with_qfd_syncs(d->u.lazy.false_child), 
      rec_keep_pure_sync_bulk_with_qfd_syncs(d->u.lazy.true_child) 
    ); 
    break; 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, child); 
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, child); 
    }
    break; 
  case TYPE_POINTER: 
    if (   VAR[d->var_index].TYPE == TYPE_POINTER 
	&& (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
	) { 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
        ic = &(d->u.ddd.arc[ci]);
        child = rec_keep_pure_sync_bulk_with_qfd_syncs(ic->child);
        child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
        result = red_bop(OR, result, child);
      }
      break; 
    }
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_keep_pure_sync_bulk_with_qfd_syncs(ic->child);
      result = red_bop(OR, result, child); 
    }
  }

  return(rec->result = result);
}
  /* rec_keep_pure_sync_bulk_with_qfd_syncs() */




struct red_type	*red_keep_pure_sync_bulk_with_qfd_syncs(d)
     struct red_type	*d;
{
  int			pi, mi, fxi, ixi, xi; 
  struct red_type	*result, *conj;

/*
  print_cpu_time("Before red_keep_pure_sync_bulk_with_qfd_syncs()");
  red_print_graph(RT[f]); 
  */

  init_23tree(&risx_tree); 
  result = rec_keep_pure_sync_bulk_with_qfd_syncs(d);
  free_entire_23tree(risx_tree, rec_free); 
  
  /* 
  print_cpu_time("After red_cdd()");
  fprintf(RED_OUT, "Leaving red_keep_pure_sync_bulk_with_qfd_syncs()");
  red_print_graph(result); 
  */
  return(result);
}
/* red_keep_pure_sync_bulk_with_qfd_syncs() */






struct red_type	*rec_keep_pure_sync_bulk(d)
     struct red_type	*d;
{
  int			ci, c1, c2;
  struct red_type	*child, *result;
  struct hrd_exp_type	*he;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, risx_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(nrec->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_keep_pure_sync_bulk(ic->child);
      child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_keep_pure_sync_bulk(bc->child);
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_keep_pure_sync_bulk(hc->child);
      result = red_bop(OR, result, child);	
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_keep_pure_sync_bulk(d->u.lazy.false_child), 
      rec_keep_pure_sync_bulk(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_keep_pure_sync_bulk(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, child); 
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_keep_pure_sync_bulk(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, child); 
    }
    break; 

  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_keep_pure_sync_bulk(ic->child);
      result = red_bop(OR, result, child); 
    }
  }

  return(rec->result = result);
}
  /* rec_keep_pure_sync_bulk() */




struct red_type	*red_keep_pure_sync_bulk(d)
     struct red_type	*d;
{
  int			pi, mi, fxi, ixi, xi; 
  struct red_type	*result, *conj;

/*
  print_cpu_time("Before red_keep_pure_sync_bulk()");
  red_print_graph(RT[f]); 
*/  

  init_23tree(&risx_tree); 
  result = rec_keep_pure_sync_bulk(d);
  free_entire_23tree(risx_tree, rec_free); 
  
  /* 
  print_cpu_time("After red_cdd()");
  fprintf(RED_OUT, "Leaving red_keep_pure_sync_bulk()");
  red_print_graph(result); 
  */
  
  return(result);
}
/* red_keep_pure_sync_bulk() */






struct red_type	*red_check_sync_proc_holders(d) 
     struct red_type *d; 
{
  int	pi; 
  
//  if (!(GSTATUS[IDNEX_MANY_TRANSITIONS] & FLAG_MANY_TRANSITIONS)) 
  d = red_add_trigger_sync_bulk(d); 

  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "d, after adding all triggers and invariances:\n");
  red_print_graph(d);
  fflush(RED_OUT);
  #endif 
  
  init_23tree(&qsync_tree); 
  d = rec_add_sync_proc_holders(d); 
  free_entire_23tree(qsync_tree, rec_free); 
 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "In the middle of add sync proc holders\n"); 
  report_red_management();   
  fprintf(RED_OUT, "after sync proc holder insertion.\n"); 
  red_print_graph(d); 
  #endif 

  init_23tree(&qsync_tree); 
  d = rec_replace_sync_proc_holders(d, 0); 
  free_entire_23tree(qsync_tree, rec_free); 

  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\nAfter replace sync proc holders():\n"); 
  red_print_graph(d); 
  #endif 

  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    d =  ddd_one_constraint(d, 
      variable_index[TYPE_ACTION_INSTANCE][pi][0], pi, pi 
    ); 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\nAfter adding initial ACTION_INSTANCE():\n"); 
  red_print_graph(d); 
  #endif 

//  d = red_sync_master_proc_index(d); 
  
  d = red_keep_pure_sync_bulk_with_qfd_syncs(d); 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\nAfter keeping pure sync bulk with qfd syncs():\n"); 
  red_print_graph(d); 
  #endif 

  return(d); 
}
/* red_check_sync_proc_holders() */ 







struct red_type	*add_post_condition(d)
     struct red_type *d; 
{
  int	w, pi, ixi, fxi, result, xi, cur_pi, ai; 

  if (d == NORM_FALSE) 
    return(d); 
  RT[w = RT_TOP++] = d; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
    RT[result = RT_TOP++] = NORM_FALSE; 
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      xi = PROCESS[pi].firable_xtion[ixi];  
/*
      fprintf(RED_OUT, "In add post pi=%1d, xi=%1d, SYNC_XTION[0].qfd_sync=%x\n", 
	      pi, xi, SYNC_XTION[0].qfd_sync
	      ); 
      fflush(RED_OUT); 
*/
      RT[cur_pi = RT_TOP++] = ddd_one_constraint(RT[w], fxi, xi, xi); 
      if (xi && RT[cur_pi] != NORM_FALSE) { 
	RT[cur_pi] = red_statement_fwd(
	  cur_pi, pi, XTION[xi].statement, 
	  FLAG_ROOT_OAPPROX | FLAG_OAPPROX_DISCRETE_LAZY, 
	  FLAG_ACTION_LAZY_EVAL  
	); 
	if (valid_mode_index(XTION[xi].dst_mode_index)) 
	  RT[cur_pi] = ddd_one_constraint
			(RT[cur_pi], variable_index[TYPE_DISCRETE][pi][0],
			 XTION[xi].dst_mode_index, XTION[xi].dst_mode_index
			 ); 
/*
        fprintf(RED_OUT, "add_post_condition for pi=%1d, xi=%1d;\n", 
		pi, xi
		); 	
	print_xtion(xi,pi); 
        red_print_graph(RT[cur_pi]); 
        fflush(RED_OUT); 
*/
      } 
      RT[result] = red_bop(OR, RT[result], RT[cur_pi]); 
/*
      fprintf(RED_OUT, "RT[result]:\n"); 
      red_print_graph(RT[result]); 
      fflush(RED_OUT); 
*/
      RT_TOP--;
    }
    RT[w] = RT[result]; 
    RT_TOP--; 
  }
  RT_TOP--; 
  return(RT[w]); 
}
/* add_post_condition() */ 






/* Count how many paths there are. 
 * We expect only two types of variables: TYPE_XI_RESTRICTION, TYPE_QSYNC_HOLDER.
 */
 

struct a23tree_type	*sync_xtion_gen_tree; 

int	rec_party_count(d)
  struct red_type	*d; 
{
  int			s, ci, cpi, cxi, cai, t, cj, cpj, cxj, caj; 
  struct rec_type	*rec, *nrec; 

  if (d->var_index == TYPE_FALSE)
    return(0); 
  else if (VAR[d->var_index].TYPE != TYPE_ACTION_INSTANCE)
    return(1); 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, sync_xtion_gen_tree, 
                                        rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return((int) nrec->result); 
  } 

  for (s=0, ci=0; ci < d->u.ddd.child_count; ci++) { 
    for (cai = d->u.ddd.arc[ci].lower_bound; cai <= d->u.ddd.arc[ci].upper_bound; cai++) { 
      cpi = cai / XTION_COUNT; 
      cxi = cai % XTION_COUNT; 
      for (t = TYPE_TRUE, cj = 0; cj <= ci && t; cj++) {
	for (caj = d->u.ddd.arc[cj].lower_bound; caj < cai && caj <= d->u.ddd.arc[cj].upper_bound; caj++) {
	  cpj = caj / XTION_COUNT; 
	  cxj = caj % XTION_COUNT; 
	  if (   d->u.ddd.arc[cj].child == d->u.ddd.arc[ci].child 
	      && XTION[cxi].red_trigger[cpi] == XTION[cxj].red_trigger[cpj] 
	      ) {
	    t = TYPE_FALSE; 
	    break; 
	  }
	}
      }

      if (t) {
	s = s + rec_party_count(d->u.ddd.arc[ci].child); 
      }
    }
  }
  rec->result = (struct red_type *) s; 
  return(s); 
}
/* rec_party_count() */ 




int	red_party_count(d) 
     struct red_type *d; 
{
  int	s; 

  init_23tree(&sync_xtion_gen_tree); 
  s = rec_party_count(d); 
  free_entire_23tree(sync_xtion_gen_tree, rec_free); 
  
  return(s); 
}
/* red_party_count() */ 



int			PARTY_TOP; 
struct party_type	*PARTY; 

/* The following are side-effect parameters set by 
 * prepare_sync_xtions() and used by 
 * sync_party_count(), sync_party_malloc(), and sync_party_fillin().  
 */ 
struct sync_xtion_type	*PSX_NEW_TABLE; // These 
int			PSX_SYNC, PSX_NEW_COUNT; 





int	rec_sync_party_count(d, depth)
     struct red_type	*d; 
     int		depth; 
{
  int			ci, pc, lb, ub; 
  struct rec_type	*rec, *nrec; 

  if (d == NORM_FALSE || depth > DEPTH_ENUMERATIVE_SYNCHRONIZATION)
    return(0);
  else if (   d == NORM_NO_RESTRICTION 
           || VAR[d->var_index].TYPE == TYPE_LAZY_EXP
           ) 
    if (depth <= DEPTH_ENUMERATIVE_SYNCHRONIZATION) 
      return(1);  
    else 
      return(0);

  rec = rec_new(d, (struct red_type *) depth); 
  nrec = (struct rec_type *) add_23tree(rec, sync_xtion_gen_tree, 
  					rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return((int) nrec->result); 
  } 

  if (VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE) { 
    for (pc = 0, ci = 0; ci < d->u.ddd.child_count; ci++) {
      lb = d->u.ddd.arc[ci].lower_bound;
      ub = d->u.ddd.arc[ci].upper_bound;
      if (lb == 0) {
        pc = pc + rec_sync_party_count(d->u.ddd.arc[ci].child, depth);
        lb = 1;
      }
      if (lb <= ub)
        pc = pc + (ub - lb + 1)*rec_sync_party_count(d->u.ddd.arc[ci].child, depth+1);
    }
  }
  else if (   VAR[d->var_index].TYPE == TYPE_POINTER 
	   && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
	   ) { 
    for (pc = 0, ci = 0; ci < d->u.ddd.child_count; ci++) {
      lb = d->u.ddd.arc[ci].lower_bound;
      ub = d->u.ddd.arc[ci].upper_bound;
      pc = pc + (ub - lb + 1)*rec_sync_party_count(d->u.ddd.arc[ci].child, depth);
    }
  }
  else {
    fprintf(RED_OUT, "Bug XI-2: An unexpected variable types.\n");
    fflush(RED_OUT); 
    bk(0); 
  }
  rec->result = (struct red_type *) pc; 
  return(pc); 
}
/* rec_sync_party_count() */


int	sync_party_count(d) 
     struct red_type *d; 
{
  int	result; 
  
  init_23tree(&sync_xtion_gen_tree); 
  result = rec_sync_party_count(d, 0); 
  free_entire_23tree(sync_xtion_gen_tree, rec_free);
  
  return(result); 
}
/* sync_party_count() */ 



int			max_qfd_sync; 
struct qfd_sync_type	*qfd_sync; 

void	sync_party_print(char *s, int depth, int count_qfd_sync) {
  int ci; 
  
  fprintf(RED_OUT, "\n========================\n"); 
  fprintf(RED_OUT, 
    "SYNC %s(%1d) at depth=%1d/%1d, qfd_sync:%1d\n", 
    s, PSX_NEW_COUNT, depth, DEPTH_ENUMERATIVE_SYNCHRONIZATION, 
    count_qfd_sync 
  ); 
  for (ci = 0; ci < depth; ci++) {
    fprintf(RED_OUT, "(p%1d,x%1d)", 
      sync_party_proc[ci], sync_party_xtion[ci] 
    );
  }
  fprintf(RED_OUT, "\n"); 
  for (ci = 0; ci < count_qfd_sync; ci++) {
    fprintf(RED_OUT, "(v%1d@p%1d:%s,value:%1d)", 
      qfd_sync[ci].vi, VAR[qfd_sync[ci].vi].PROC_INDEX, 
      VAR[qfd_sync[ci].vi].NAME, qfd_sync[ci].value
    );
  }
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
}
  /* sync_party_print() */ 
  
  
    

void	sync_party_malloc(d, depth, count_qfd_sync)
     struct red_type	*d;
     int		depth, count_qfd_sync; 
{
  int	ci, b;

  if (d == NORM_FALSE) {
    return;
  }
  else if (   d == NORM_NO_RESTRICTION 
           || VAR[d->var_index].TYPE == TYPE_LAZY_EXP
           ) { 
    if (depth <= DEPTH_ENUMERATIVE_SYNCHRONIZATION) {
/*      sync_party_print("MALLOC", depth, count_qfd_sync); 
 */           
      PSX_NEW_TABLE[PSX_NEW_COUNT].party_count = depth;  
      PSX_NEW_TABLE[PSX_NEW_COUNT].party 
	= (struct sync_party_type *) malloc(depth*sizeof(struct sync_party_type)); 

      PSX_NEW_TABLE[PSX_NEW_COUNT].qfd_sync_count = count_qfd_sync;  
      PSX_NEW_TABLE[PSX_NEW_COUNT].qfd_sync 
	= (struct qfd_sync_type *) malloc(count_qfd_sync * sizeof(struct qfd_sync_type)); 
      PSX_NEW_TABLE[PSX_NEW_COUNT].ec_representative 
      = (int *) malloc(3*sizeof(int)); 
      PSX_NEW_TABLE[PSX_NEW_COUNT].ec_representee 
      = (int **) malloc(3*sizeof(int *)); 
/*
      PSX_NEW_TABLE[PSX_NEW_COUNT].red_ec_ineq_representative 
      = (struct red_type **) malloc(3*sizeof(struct red_type *)); 
      PSX_NEW_TABLE[PSX_NEW_COUNT].red_ec_ineq_weak_fairness_representative 
      = (struct red_type **) malloc(3*sizeof(struct red_type *)); 
*/
      PSX_NEW_COUNT++; 
    } 
    if (count_qfd_sync > max_qfd_sync) 
      max_qfd_sync = count_qfd_sync; 
    return; 
  }  

  if (VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE) { 
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      for (b = d->u.ddd.arc[ci].lower_bound; 
           b <= d->u.ddd.arc[ci].upper_bound; 
           b++
           )
	if (b) {
/*
	  sync_party_proc[depth] = VAR[d->var_index].PROC_INDEX;
	  sync_party_xtion[depth] = b; 
*/
	  sync_party_malloc(d->u.ddd.arc[ci].child, depth+1, count_qfd_sync);
	}
	else
	  sync_party_malloc(d->u.ddd.arc[ci].child, depth, count_qfd_sync);
  }
  else if (   VAR[d->var_index].TYPE == TYPE_POINTER 
	   && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
	   ) { 
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      for (b = d->u.ddd.arc[ci].lower_bound; 
           b <= d->u.ddd.arc[ci].upper_bound; 
           b++
           ) {
/*
        qfd_sync[count_qfd_sync].vi = d->var_index;
        qfd_sync[count_qfd_sync].value = b; 
*/
        sync_party_malloc(d->u.ddd.arc[ci].child, depth, count_qfd_sync+1);
      }
  }
  else {
    fprintf(RED_OUT, "Bug XI-2: An unexpected variable types.\n");
    fflush(RED_OUT); 
    bk(0); 
  }
}
/* sync_party_malloc() */



/* In the following procedure, we also fill in the sync qfd variable indices to 
 * the SYNCHRONOUS TRANSITION table
 */  
int	count_party_fillin = 0; 

struct red_type	*sync_party_fillin(d, depth, count_qfd_sync)
     struct red_type	*d;
     int		depth, count_qfd_sync; 
{
  int			ci, b;
  struct red_type	*result, *new_child; 

  if (d == NORM_FALSE || depth > DEPTH_ENUMERATIVE_SYNCHRONIZATION)
    return(d);
  else if (   d == NORM_NO_RESTRICTION
           || VAR[d->var_index].TYPE == TYPE_LAZY_EXP
           ) { 
    if (depth <= DEPTH_ENUMERATIVE_SYNCHRONIZATION) {
//      sync_party_print("FILLIN", depth, count_qfd_sync); 
            
      PSX_NEW_TABLE[PSX_NEW_COUNT].index = PSX_NEW_COUNT; 
      PSX_NEW_TABLE[PSX_NEW_COUNT].status = 0; 
      PSX_NEW_TABLE[PSX_NEW_COUNT].red_trigger = d; 
      PSX_NEW_TABLE[PSX_NEW_COUNT].red_post = NORM_NO_RESTRICTION; 
      for (ci = 0; ci < 3; ci++) { 
        PSX_NEW_TABLE[PSX_NEW_COUNT].ec_representative[ci] = 0; 
        PSX_NEW_TABLE[PSX_NEW_COUNT].ec_representee[ci] = NULL; 
/*
        PSX_NEW_TABLE[PSX_NEW_COUNT].red_ec_ineq_representative[ci] = NULL; 
        PSX_NEW_TABLE[PSX_NEW_COUNT].red_ec_ineq_weak_fairness_representative[ci] = NULL; 
*/
      } 
/*
      fprintf(RED_OUT, 
        "\nInside fillin, PSX_NEW_TABLE[%1d].status = %x\n", 
        PSX_NEW_COUNT, PSX_NEW_TABLE[PSX_NEW_COUNT].status
      ); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "SXI:%1d: ", SYNC_XTION_COUNT);
*/
      for (ci = 0; ci < depth; ci++) {
	PSX_NEW_TABLE[PSX_NEW_COUNT].party[ci].xtion = sync_party_xtion[ci];
	PSX_NEW_TABLE[PSX_NEW_COUNT].party[ci].proc = sync_party_proc[ci];
	PSX_NEW_TABLE[PSX_NEW_COUNT].status 
	= PSX_NEW_TABLE[PSX_NEW_COUNT].status 
	| (PROCESS[sync_party_proc[ci]].status & MASK_GAME_ROLES); 
/*
	fprintf(RED_OUT, "(xi=%1d, pi=%1d)",
		SYNC_XTION[SYNC_XTION_COUNT].party[ci].xtion,
		SYNC_XTION[SYNC_XTION_COUNT].party[ci].proc
		);
*/
      }
/*
      fprintf(RED_OUT, 
      "\nInside sync_fillin() adding roles, PSX_NEW_TABLE[%1d].status = %x\n", 
        PSX_NEW_COUNT, PSX_NEW_TABLE[PSX_NEW_COUNT].status
      ); 
      fflush(RED_OUT); 
*/
      for (ci = 0; ci < count_qfd_sync; ci++) { 
	PSX_NEW_TABLE[PSX_NEW_COUNT].qfd_sync[ci].vi = qfd_sync[ci].vi;
	PSX_NEW_TABLE[PSX_NEW_COUNT].qfd_sync[ci].value = qfd_sync[ci].value;
      } 
/*
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      PSX_NEW_COUNT++;
      return(NORM_FALSE);
    }
    else
      return(d);
  }
  

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) 
      for (b = d->u.ddd.arc[ci].lower_bound; 
           b <= d->u.ddd.arc[ci].upper_bound; 
           b++
           ) {
	if (b) { 
	  sync_party_proc[depth] = VAR[d->var_index].PROC_INDEX;
	  sync_party_xtion[depth] = b; 
	  new_child = sync_party_fillin(d->u.ddd.arc[ci].child, depth+1, count_qfd_sync); 
	}
	else 
	  new_child = sync_party_fillin(d->u.ddd.arc[ci].child, depth, count_qfd_sync); 
	result = red_bop(OR, result, ddd_one_constraint(new_child, d->var_index, b, b)); 
      } 
    return(result);
    break; 

  case TYPE_POINTER: 
    if (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) {
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (b = d->u.ddd.arc[ci].lower_bound; 
             b <= d->u.ddd.arc[ci].upper_bound; 
             b++
             ) { 
/*
      	fprintf(RED_OUT, "\ncount_party_fillin=%1d within with count_qfd_sync = %1d, max_qfd_sync = %1d\n", 
		count_party_fillin++, count_qfd_sync, max_qfd_sync
		); 
*/
          qfd_sync[count_qfd_sync].vi = d->var_index;
          qfd_sync[count_qfd_sync].value = b; 
          new_child = sync_party_fillin(
            d->u.ddd.arc[ci].child, depth, count_qfd_sync+1
          ); 
          result = red_bop(OR, result, ddd_one_constraint(new_child, d->var_index, b, b)); 
        }
      }
      return(result);
    }  
  default: 
    exit(0); 
  }
}
/* sync_party_fillin() */




struct red_type	*quantified_sync_xi_restriction(xri)
	int	xri; 
{
  int			xi, ipi, pi; 
  struct red_type	*result, *conj; 
  
  result = NORM_FALSE; 
  for (xi = 1; xi < XTION_COUNT; xi++) { 
    if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC) { 
      for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
      	pi = XTION[xi].process[ipi]; 
      	conj = ddd_one_constraint(RT[xri], variable_index[TYPE_XTION_INSTANCE][pi][0], xi, xi); 
      	RT[xri] = red_bop(EXCLUDE, RT[xri], conj); 
      	result = red_bop(OR, result, conj); 
      }     
    } 	
  } 
  return(result); 
}
  /* quantified_sync_xi_restriction() */ 
  




struct a23tree_type	*specific_qfd_sync_tree; 

struct red_type	*rec_eliminate_simple_qfd_sync(d)
     struct red_type	*d; 
{
  int			ci; 
  struct red_type	*result, *conj;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NULL); 
  nrec = (struct rec_type *) add_23tree(rec, specific_qfd_sync_tree, 
    rec_comp, rec_free, rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) { 
    return(nrec->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      conj = rec_eliminate_simple_qfd_sync(bc->child);
      conj = crd_lone_subtree(conj, d->var_index, bc->upper_bound);
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      conj = hrd_lone_subtree(rec_eliminate_simple_qfd_sync(hc->child),
				 d->var_index, d->u.hrd.hrd_exp,
				 hc->ub_numerator, hc->ub_denominator
				 );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_eliminate_simple_qfd_sync(d->u.lazy.false_child), 
      rec_eliminate_simple_qfd_sync(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
  
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = fdd_lone_subtree(
        rec_eliminate_simple_qfd_sync(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = dfdd_lone_subtree( 
        rec_eliminate_simple_qfd_sync(d->u.dfdd.arc[ci].child), 
	d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound 
      ); 
      result = red_bop(OR, result, conj);
    }
    break; 

  case TYPE_POINTER: 
    if (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
	  rec_eliminate_simple_qfd_sync(d->u.ddd.arc[ci].child) 
	);
      } 
      break; 
    }
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = ddd_lone_subtree(rec_eliminate_simple_qfd_sync(ic->child),
				   d->var_index, ic->lower_bound, ic->upper_bound
				   );
      result = red_bop(OR, result, conj);
    }
  }
  return(rec->result = result); 
}
/* rec_eliminate_simple_qfd_sync() */





struct red_type	*eliminate_simple_qfd_sync(d) 
     struct red_type *d; 
{
  init_23tree(&specific_qfd_sync_tree); 
  d = rec_eliminate_simple_qfd_sync(d); 
  free_entire_23tree(specific_qfd_sync_tree, rec_free); 

  return(d); 
}
/* eliminate_simple_qfd_sync() */ 



struct red_type	*rec_restrict_specific_qfd_sync(d)
     struct red_type	*d; 
{
  int			ci; 
  struct red_type	*result, *conj;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  rec = rec_new(d, NULL); 
  nrec = (struct rec_type *) add_23tree(rec, specific_qfd_sync_tree, 
    rec_comp, rec_free, rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      conj = rec_restrict_specific_qfd_sync(bc->child);
      conj = crd_lone_subtree(conj, d->var_index, bc->upper_bound);
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      conj = hrd_lone_subtree(rec_restrict_specific_qfd_sync(hc->child),
				 d->var_index, d->u.hrd.hrd_exp,
				 hc->ub_numerator, hc->ub_denominator
				 );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_restrict_specific_qfd_sync(d->u.lazy.false_child), 
      rec_restrict_specific_qfd_sync(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
  
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = fdd_lone_subtree(
        rec_restrict_specific_qfd_sync(d->u.fdd.arc[ci].child),
	d->var_index, 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound 
      ); 
      result = red_bop(OR, result, conj);
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) { 
      conj = dfdd_lone_subtree( 
        rec_restrict_specific_qfd_sync(d->u.dfdd.arc[ci].child), 
	d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound 
      ); 
      result = red_bop(OR, result, conj);
    }
    break; 

  case TYPE_POINTER: 
    if (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      	if (   VAR[d->var_index].U.DISC.CORRESPONDING_PI 
      	       < d->u.ddd.arc[ci].lower_bound
      	    || VAR[d->var_index].U.DISC.CORRESPONDING_PI 
      	       > d->u.ddd.arc[ci].upper_bound 
      	    )
      	  continue; 
        result = red_bop(OR, result, 
	  rec_restrict_specific_qfd_sync(d->u.ddd.arc[ci].child) 
	);
      } 
      break; 
    }
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = ddd_lone_subtree(rec_restrict_specific_qfd_sync(ic->child),
				   d->var_index, ic->lower_bound, ic->upper_bound
				   );
      result = red_bop(OR, result, conj);
    }
  }
  return(rec->result = result); 
}
/* rec_restrict_specific_qfd_sync() */




struct red_type	*red_restrict_specific_qfd_sync(
  struct red_type	*d
) { 
  init_23tree(&specific_qfd_sync_tree); 
  d = rec_restrict_specific_qfd_sync(d); 
  free_entire_23tree(specific_qfd_sync_tree, rec_free); 
  
  return(d); 
} 
  /* red_restrict_specific_qfd_sync() */ 




int	PI_QSYNC; 

exp_specific_qfd_sync(psub)
     struct ps_exp_type	*psub;
{
  int				vi;
  struct parse_indirect_type	*pt;
  struct ps_bunit_type 		*pbu;

  switch (psub->type) {
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QFD:
  case TYPE_INTERVAL:
    return(TYPE_FALSE); 
    break;
  case TYPE_QSYNC_HOLDER:
    if (psub->u.qsholder.qsync_var) {
      return(TYPE_TRUE); 
    } 
    else 
      return(TYPE_FALSE); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    return(exp_specific_qfd_sync(psub->u.exp)); 
    break; 
  case TYPE_CLOCK:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_DENSE:
  case TYPE_POINTER:
    return(exp_specific_qfd_sync(psub->u.atom.exp_base_proc_index)); 
    break;
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
  
  case ARITH_ADD :
  case ARITH_MINUS :
  case ARITH_MULTIPLY :
  case ARITH_DIVIDE :
  case ARITH_MODULO:   
    if (   exp_specific_qfd_sync(psub->u.arith.lhs_exp) 
    	|| exp_specific_qfd_sync(psub->u.arith.rhs_exp)
    	) 
      return(TYPE_TRUE); 
    return(TYPE_FALSE); 
    break;
  default:
    fprintf(RED_OUT, "\nHuh ? (in rec_catch concurrent accesses)\n");
    bk(); 
  }
}
/* exp_specific_qfd_sync() */


/*
int count_as_write = 0; 
*/

  


struct ps_exp_type	*adjust_specific_qfd_sync(psub)
     struct ps_exp_type	*psub;
{
  int				vi, flag, xsi;
  struct parse_indirect_type	*pt;
  struct ps_bunit_type 		*pbu;
  struct ps_exp_type		*newsub; 
  struct red_type		*conj; 

  switch (psub->type) {
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QFD:
  case TYPE_INTERVAL:
  case TYPE_MODE_INDEX: 
    return(psub); 
    break;

  case TYPE_QSYNC_HOLDER:
    if (psub->u.qsholder.qsync_var) { 
      vi = variable_index[TYPE_POINTER][ITERATE_PI][psub->u.qsholder.qsync_var->index]; 
      for (xsi = 0; xsi < SYNC_XTION[ITERATE_SXI].qfd_sync_count; xsi++) { 
      	if (SYNC_XTION[ITERATE_SXI].qfd_sync[xsi].vi == vi) 
      	  break; 
      } 
      if (xsi >= SYNC_XTION[ITERATE_SXI].qfd_sync_count) { 
      	fprintf(RED_OUT, "Error: An unrecorded quantified sync holder %1d:%1s at sync transition %1d.\n", 
		vi, VAR[vi].NAME, ITERATE_SXI
		); 
	bk(""); 
      } 
      newsub = ps_exp_alloc(TYPE_CONSTANT); 
      newsub->u.value = SYNC_XTION[ITERATE_SXI].qfd_sync[xsi].value; 
      return(ps_exp_share(newsub)); 
    } 
    else { 
      fprintf(RED_OUT, "\nError: There should not be an unnamed quantified sync variable here.\n"); 
      bk(""); 
    } 
    break; 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = adjust_specific_qfd_sync(psub->u.exp); 
    return(ps_exp_share(newsub)); 

  case TYPE_POINTER: 
    vi = psub->u.atom.var_index; 
    vi = variable_index[TYPE_POINTER][ITERATE_PI][VAR[vi].OFFSET]; 
    for (xsi = 0; xsi < SYNC_XTION[ITERATE_SXI].qfd_sync_count; xsi++) { 
      if (SYNC_XTION[ITERATE_SXI].qfd_sync[xsi].vi == vi) 
      	break; 
    } 
    if (xsi >= SYNC_XTION[ITERATE_SXI].qfd_sync_count) { 
      fprintf(RED_OUT, "Error: An unrecorded quantified sync holder %1d:%1s at sync transition %1d.\n", 
	vi, VAR[vi].NAME, ITERATE_SXI
      ); 
      bk(""); 
    } 
    if (VAR[psub->u.atom.var_index].STATUS & FLAG_QUANTIFIED_SYNC) { 
      newsub = ps_exp_alloc(TYPE_CONSTANT); 
      newsub->u.value = SYNC_XTION[ITERATE_SXI].qfd_sync[xsi].value; 
      return(ps_exp_share(newsub)); 
    } 
  case TYPE_DISCRETE: 
  case TYPE_DENSE: 
  case TYPE_CLOCK: 
    newsub = ps_exp_copy(psub); 
/* 
    for (xsi = 0; xsi < psub->u.atom.indirect_count; xsi++) { 
      newsub->u.atom.indirect_exp[xsi] 
      = adjust_specific_qfd_sync(psub->u.atom.indirect_exp[xsi]); 
    } 
*/
    switch (psub->u.atom.exp_base_proc_index->type) { 
    case TYPE_CONSTANT: 
      return(ps_exp_share(newsub)); 
      break; 
    default: 
      *newsub = *psub; 
      newsub->u.atom.exp_base_proc_index 
      = adjust_specific_qfd_sync(psub->u.atom.exp_base_proc_index); 
      return(ps_exp_share(newsub)); 
    } 
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD :
  case ARITH_MINUS :
  case ARITH_MULTIPLY :
  case ARITH_DIVIDE :
  case ARITH_MODULO: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = adjust_specific_qfd_sync(psub->u.arith.lhs_exp); 
    newsub->u.arith.rhs_exp = adjust_specific_qfd_sync(psub->u.arith.rhs_exp); 
    return(ps_exp_share(newsub)); 
    break; 

  default:
    fprintf(RED_OUT, "\nHuh ? (in rec_catch concurrent accesses)\n");
    bk(); 
  }
}
  /* adjust_specific_qfd_sync() */



int	qfd_sync_value, count_sync_st = 0; 


struct statement_type	*sync_statement( 
  struct statement_type	*st, 
  int			spi   
) { 
  struct statement_type	*nst; 
  int			i, pi; 
  
  if (!st) 
    return(NULL); 
    
  if (!(st->st_status & FLAG_ACTION_QUANTIFIED_SYNC)) 
    return(st); 

  nst = (struct statement_type *) malloc(sizeof(struct statement_type)); 
  *nst = *st; 
  switch (st->op) { 
  case ST_IF: 
    nst->u.branch.red_cond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    ) - 1; 
    nst->u.branch.red_uncond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    ) - 1; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      nst->u.branch.red_cond[pi] 
      = eliminate_simple_qfd_sync(red_bop(AND, st->u.branch.red_cond[pi], RT[qfd_sync_value])); 
      nst->u.branch.red_uncond[pi] 
      = eliminate_simple_qfd_sync(red_bop(AND, st->u.branch.red_uncond[pi], RT[qfd_sync_value])); 
      red_mark(nst->u.branch.red_cond[pi], FLAG_GC_STABLE); 
      red_mark(nst->u.branch.red_uncond[pi], FLAG_GC_STABLE); 
    }
    nst->u.branch.if_statement = sync_statement(
      st->u.branch.if_statement, spi
    ); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      nst->u.branch.else_statement = sync_statement(
        st->u.branch.else_statement, spi
      );  
    } 
    return(nst); 
    break; 
  case ST_WHILE: 
    nst->u.loop.red_cond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    ) - 1; 
    nst->u.loop.red_uncond = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    ) - 1; 
    st->u.loop.red_gfp = ((struct red_type **) 
      malloc(PROCESS_COUNT * sizeof(struct red_type *))
    ) - 1; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      nst->u.loop.red_gfp[pi] = NULL; 
      nst->u.loop.red_cond[pi] 
      = eliminate_simple_qfd_sync(red_bop(AND, st->u.loop.red_cond[pi], RT[qfd_sync_value])); 
      nst->u.loop.red_uncond[pi] 
      = eliminate_simple_qfd_sync(red_bop(AND, st->u.loop.red_uncond[pi], RT[qfd_sync_value])); 
      red_mark(nst->u.loop.red_cond[pi], FLAG_GC_STABLE); 
      red_mark(nst->u.loop.red_uncond[pi], FLAG_GC_STABLE); 
    }
    nst->u.loop.statement = sync_statement(st->u.loop.statement, spi); 
    return(nst);   
    break; 
  case ST_SEQ: 
    nst->u.seq.statement = (struct statement_type **) 
	malloc(st->u.seq.count * sizeof(struct statement_type *)); 
    for (i = 0; i < st->u.seq.count; i++) { 
      nst->u.seq.statement[i] = sync_statement(st->u.seq.statement[i], spi); 
    } 
    return(nst); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    break; 
  default: 
/*
    fprintf(RED_OUT, "\nsync st %1d: \n", ++count_sync_st); 
    pcform(st->u.act.lhs); 
    fflush(RED_OUT); 
*/    
    nst->u.act.lhs = adjust_specific_qfd_sync(st->u.act.lhs); 
    nst->u.act.lhs = adjust_specific_pi(nst->u.act.lhs, spi); 
    nst->u.act.rhs_exp = adjust_specific_qfd_sync(st->u.act.rhs_exp); 
    nst->u.act.rhs_exp = adjust_specific_pi(nst->u.act.rhs_exp, spi); 
    nst->u.act.term = (struct parse_term_type *) 
      malloc(st->u.act.term_count * sizeof(struct parse_term_type));  
    for (i = 0; i < st->u.act.term_count; i++) { 
      nst->u.act.term[i].operand = adjust_specific_qfd_sync(st->u.act.term[i].operand); 
      nst->u.act.term[i].coeff = adjust_specific_qfd_sync(st->u.act.term[i].coeff); 
    } 
    if (st->u.act.offset) 
      nst->u.act.offset = adjust_specific_qfd_sync(st->u.act.offset); 

    process_xtion_effect_alloc(nst); 
    if (nst->u.act.red_effect) { 
    /* This got be a simple address variable. 
     */ 
//      nst->u.act.lhs->u.atom.indirect_vi = NULL; 
      for (i = 1; i <= PROCESS_COUNT; i++) { 
/*
      	psl(st, i); 
*/      	
      	if (   st->u.act.red_effect == NULL 
      	    || st->u.act.red_effect[i] == NULL
      	    ) { 
          XSUB.type = ARITH_EQ;
          XSUB.u.arith.lhs_exp = nst->u.act.lhs;
          XSUB.u.arith.rhs_exp = nst->u.act.rhs_exp;
/*
      fprintf(RED_OUT, "\nred_effect pi %1d of : ", pi); 
      psl(st, pi); 
*/
          nst->u.act.red_effect[i] = red_discrete_ineq(&XSUB, i);

          red_mark(nst->u.act.red_effect[i], FLAG_GC_STABLE);
/*
      red_print_graph(st->u.act.red_effect[pi]); 
*/
      	} 
      	else { 
/*
      	  fprintf(RED_OUT, "\nst->u.act.red_effect[pi=%1d]:%x\n", 
      	    i, st->u.act.red_effect[i]
      	  ); 
*/
          nst->u.act.red_effect[i] = red_restrict_specific_qfd_sync(
            st->u.act.red_effect[i]
          ); 
	  nst->u.act.red_effect[i] = eliminate_simple_qfd_sync(
	    nst->u.act.red_effect[i]
	  ); 
          red_mark(nst->u.act.red_effect[i], FLAG_GC_STABLE);
/*
      	  fprintf(RED_OUT, "\nsync st->u.act.red_effect[pi=%1d]:%x\n", 
      	    i, nst->u.act.red_effect[i]
      	  ); 
      	  psl(nst, i); 
      	  fprintf(RED_OUT, "\nFrom st->u.act.red_effect[pi=%1d]:\n", i); 
      	  red_print_graph(st->u.act.red_effect[i]); 
      	  fprintf(RED_OUT, "  to sync st->u.act.red_effect[pi=%1d]:\n", i); 
      	  red_print_graph(nst->u.act.red_effect[i]); 
      	  fflush(RED_OUT); 
*/      	
        }
      }
    } 
    return(nst); 
  } 
}
  /* sync_statement() */ 
  
  
  


int	rec_event_path_evaluate(d)
     struct red_type	*d;
{
  struct ddd_child_type		*ic;
  int				result, ci, cj, cxi;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index 
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(TYPE_TRUE); 
  else if (d->var_index == TYPE_FALSE)
    return(TYPE_FALSE);

  ce = cache1_check_result_key(OP_EVENT_PATH_EVALUATE, d); 
  if (ce->result) {
    return(((int) ce->result)-1); 
  } 

  if (VAR[d->var_index].TYPE == TYPE_SYNCHRONIZER) { 
    result = TYPE_FALSE;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      if (d->u.ddd.arc[ci].lower_bound <= VAR[d->var_index].U.SYNC.DIFF 
          && VAR[d->var_index].U.SYNC.DIFF <= d->u.ddd.arc[ci].upper_bound
          ) { 
        result = rec_event_path_evaluate(d->u.ddd.arc[ci].child); 
      } 
    } 
  } 
  else { 
    fprintf(RED_OUT, "Hm ? \n"); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  ce->result = (struct red_type *) (result+1);
  
  return(result);
}
/* rec_event_path_evaluate() */



int	event_path_evaluate(d)
     struct red_type	*d; 
{
  int	result; 
  
  result = rec_event_path_evaluate(d);  

  return(result);
}
/* event_path_evaluate() */



int	rec_set_sxi_event_flag(psub)
	struct ps_exp_type	*psub;
{
    int				gvi, jj, rvalue, lvalue;
  struct ps_bunit_type		*pbu;
  struct ps_exp_link_type	*fl;

  switch(psub->type) {
  case TYPE_FALSE :
    return(0);
  case TYPE_TRUE :
    return(1);
  case TYPE_SYNCHRONIZER:
    gvi = variable_index[TYPE_SYNCHRONIZER][0][psub->u.atom.var->index];
    return(VAR[gvi].U.SYNC.DIFF);
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_DISCRETE:
  case TYPE_CLOCK:
  case TYPE_POINTER:
  case TYPE_QFD:
    fprintf(RED_OUT, 
      "Syntax error: an illegal variable type in event condition in on-phrase. \n"
    );
    fflush(RED_OUT);
    bk("Syntax error: an illegal variable type in event condition in on-phrase. \n");
    break;
  case TYPE_NULL:
    return(0);
  case TYPE_CONSTANT:
    return(psub->u.value);
  case BIT_NOT: 
    return(~rec_set_sxi_event_flag(psub->u.exp));
  case BIT_OR: 
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)|rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case BIT_AND:  
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)&rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case BIT_SHIFT_RIGHT: 
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)>>rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case BIT_SHIFT_LEFT: 
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)<<rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_ADD:
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)+rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_MINUS:
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)-rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_MULTIPLY:
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)*rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_DIVIDE:
    rvalue = rec_set_sxi_event_flag(psub->u.arith.rhs_exp);
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp)/rvalue);
  case ARITH_EQ :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) == rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_NEQ :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) != rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_LEQ :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) <= rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_LESS :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) < rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_GREATER :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) > rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case ARITH_GEQ :
    return(rec_set_sxi_event_flag(psub->u.arith.lhs_exp) >= rec_set_sxi_event_flag(psub->u.arith.rhs_exp));
  case EQ :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue == rec_set_sxi_event_flag(psub->u.ineq.offset)); 
  case NEQ :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue != rec_set_sxi_event_flag(psub->u.ineq.offset)); 
  case LEQ :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue <= rec_set_sxi_event_flag(psub->u.ineq.offset)); 
  case LESS :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue < rec_set_sxi_event_flag(psub->u.ineq.offset)); 
  case GREATER :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue > rec_set_sxi_event_flag(psub->u.ineq.offset)); 
  case GEQ :
    lvalue = 0; 
    for (jj = 0; jj < psub->u.ineq.term_count; jj++) { 
      lvalue = lvalue 
	     + rec_set_sxi_event_flag(psub->u.ineq.term[jj].operand) 
	     * rec_set_sxi_event_flag(psub->u.ineq.term[jj].coeff); 
    } 
    return (lvalue >= rec_set_sxi_event_flag(psub->u.ineq.offset)); 
    fprintf(RED_OUT, "Syntax error: illegal clock inequality for event conditions.\n");
    bk(); 
  case AND :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist; jj; jj--, pbu = pbu->bnext) {
      if (!(rec_set_sxi_event_flag(pbu->subexp)))
        return(TYPE_FALSE);
    }
    return(TYPE_TRUE);
  case OR :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist; jj; jj--, pbu = pbu->bnext) {
      if (rec_set_sxi_event_flag(pbu->subexp))
        return(TYPE_TRUE);
    }
    return(TYPE_FALSE);
  case NOT :
    return(!(rec_set_sxi_event_flag(psub->u.bexp.blist->subexp)));
  case IMPLY :
    if (!(rec_set_sxi_event_flag(psub->u.bexp.blist->subexp)))
      return(TYPE_TRUE);
    else
      return(rec_set_sxi_event_flag(psub->u.bexp.blist->bnext->subexp));
  case RED: 
    return(event_path_evaluate(psub->u.rpred.red)); 
  }
}
  /* rec_set_sxi_event_flag() */


void	psx_status(
  char				*s, 
  struct sync_xtion_type	*sxt, 
  int				sxc
) { 
  int	sxi, ipi, pi, xi; 
  
  fprintf(RED_OUT, "\n%s\n==SYNC XTION STATUS======\n", s); 
  for (sxi = 0; sxi < sxc; sxi++) { 
    fprintf(RED_OUT, "sxi %1d, s=0x%x, ", sxi, sxt[sxi].status); 
    for (ipi = 0; ipi < sxt[sxi].party_count; ipi++) { 
      pi = sxt[sxi].party[ipi].proc; 
      xi = sxt[sxi].party[ipi].xtion; 
      fprintf(RED_OUT, "%1d(p%1d,x%1d)ps=0x%x:%s ", 
        ipi, pi, xi, 
        (unsigned int) PROCESS[pi].status, 
        role_name(PROCESS[pi].status & MASK_GAME_ROLES)
      ); 
    } 
    fprintf(RED_OUT, "\n"); 
  } 
  fflush(RED_OUT); 
} 
  /* psx_status() */ 
  
  
void	psx(char *s) { 
  psx_status(s, SYNC_XTION, SYNC_XTION_COUNT); 	
} 
  /* psx() */ 




struct a23tree_type	*dep_es_tree; 
int			*a_bottom; 

rec_array_free(rec)
     struct rec_type	*rec;
{
  rec_count--;
  if (rec_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  free((int *) (rec->result)); 
  free(rec);
}
/* rec_array_free() */






int	*array_bottom() { 
  int	*a, pi; 
  
  a = (int *) malloc((PROCESS_COUNT + 1)*sizeof(int)); 
  a[0] = 1; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    a[pi] = 0; 
  return(a); 
} 
  /* array_bottom() */ 


int	*array_zero() { 
  int	*a, pi; 
  
  a = (int *) malloc((PROCESS_COUNT + 1)*sizeof(int)); 
  for (pi = 0; pi <= PROCESS_COUNT; pi++) 
    a[pi] = 0; 
  return(a); 
} 
  /* array_zero() */ 


int	*array_inherit(int *a, int *b) { 
  int	pi; 
  
  for (pi = 0; pi <= PROCESS_COUNT; pi++) 
    a[pi] = a[pi] + b[pi]; 
  return(a); 
} 
  /* array_inherit() */ 

void	print_dep_array(int *a) { 
  int	pi; 

  fprintf(RED_OUT, "\nThe spectrum of synchronization sizes:\n"); 
  for (pi = 0; pi <= PROCESS_COUNT; pi++) { 
    fprintf(RED_OUT, " %4d", pi); 	
  } 
  fprintf(RED_OUT, "\n"); 
  for (pi = 0; pi <= PROCESS_COUNT; pi++) { 
    fprintf(RED_OUT, " %4d", a[pi]); 	
  } 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
}
  /* print_dep_array() */ 



int	count_cdes = 0; 

int	*rec_calculate_depth_enumerative_synchronization(d)
     struct red_type	*d; 
{
  int			ci, m, pi, local_cdes; 
  int			*result, *child;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

//  local_cdes = ++count_cdes; 
  
  if (d == NORM_NO_RESTRICTION) 
    return(a_bottom);
  else if (d == NORM_FALSE) {
    fprintf(RED_OUT, 
      "\nERROR: There should be at least one trnasitions in sync_all.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  rec = rec_new(d, NULL); 
  nrec = (struct rec_type *) add_23tree(rec, dep_es_tree, 
    rec_comp, rec_free, rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) { 
    return((int *) nrec->result); 
  } 
  
  result = array_zero(); 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_calculate_depth_enumerative_synchronization(ic->child);
      m = ic->upper_bound - ic->lower_bound; 
      if (ic->lower_bound > 0 || ic->upper_bound < 0) { 
      	m++; 
      }
      else { 
        result = array_inherit(result, child);
      } 
      if (m > 0) { 
        for (pi = 0; pi < PROCESS_COUNT; pi++) { 
          result[pi+1] = result[pi+1] + m*child[pi];
        }
      }
    }
    break; 
  default:
    fprintf(RED_OUT, 
      "\nERROR: Unexpected variable type %1d:%s in calculating the depth.\n", 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
/*
  fprintf(RED_OUT, "\n-------------------------------------------------\n"); 
  fprintf(RED_OUT, 
    "(%1d) rec_calculate_depth_enumerative_synchronization:\n", 
    local_cdes 
  ); 
  red_print_graph(d); 
  print_dep_array(result); 
*/  
  rec->result = (struct red_type *) result; 
  
  return(result); 
}
/* rec_calculate_depth_enumerative_synchronization() */



int	calculate_depth_enumerative_synchronization(
  struct red_type	*s
) {
  int	pi, *r, sum, acc, t, tl, tu; 
  
  a_bottom = array_bottom(); 
    
  init_23tree(&dep_es_tree); 
  r = rec_calculate_depth_enumerative_synchronization(s); 
  for (pi = 0; pi <= PROCESS_COUNT; pi++) { 
    a_bottom[pi] = r[pi]; 
  } 
  free_entire_23tree(dep_es_tree, rec_array_free); 
/*
  fprintf(RED_OUT, "\nFor the following sync all:\n"); 
  red_print_graph(s); 
*/
  print_dep_array(a_bottom); 
    
  for (sum = 0, pi = 1; pi <= PROCESS_COUNT; pi++) 
    sum = sum + a_bottom[pi]; 
    
  if (sum <= 100) { 
    fprintf(RED_OUT, "Depth enumerative sync set at %1d.\n", PROCESS_COUNT+1); 
    fflush(RED_OUT); 
    return(PROCESS_COUNT+1); 
  }   
  for (tl = 1, tu = PROCESS_COUNT; tl < tu; ) {
    t = (tl+tu)/2; 
    if (t*t > PROCESS_COUNT) 
      tu = t; 
    else if (t*t <= PROCESS_COUNT) 
      tl = t+1; 
  } 
  if (t*t > PROCESS_COUNT) 
    t--; 
    
  t = t * PROCESS_COUNT * XTION_COUNT; 
  fprintf(RED_OUT, "Depth threshold set to %1d.\n", t); 
  if (sum <= t) { 
    fprintf(RED_OUT, "Depth enumerative sync set at %1d.\n", PROCESS_COUNT+1); 
    fflush(RED_OUT); 
    return(PROCESS_COUNT+1); 
  }   

  acc = 0; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    acc = acc + a_bottom[pi]; 
    if (acc > t) 
      break;  
  } 
  for (pi--; pi > 0 && a_bottom[pi] == 0; pi--) ; 
  if (a_bottom[pi+1] == 0) 
    pi++; 
    
  free(a_bottom); 
  fprintf(RED_OUT, "Depth enumerative sync set at %1d.\n", pi); 
  fflush(RED_OUT); 
//  exit(0); 
  
  return(pi); 	
}
  /* calculate_depth_enumerative_synchronization() */ 



struct red_type	*prepare_sync_xtions(
	int			xi_sync, 
	struct sync_xtion_type	**sxtable_ptr,  
	int			*sxt_count_ptr, 
	int			flag_bisim_analysis  
	) { 
  int 				xi_sync_bulk, pi, pj, ixi, xi, isi, si, xsi, 
				cur_pi, ci, iai, ai, ti, sx_trigger, events, 
				post; 
  struct sync_xtion_rec_type	*sx;
  struct red_type		*conj, *sub, *result;
  struct index_link_type	*filist; 

  sync_party_proc = (int *) malloc(PROCESS_COUNT*sizeof(int));
  sync_party_xtion = (int *) malloc(PROCESS_COUNT*sizeof(int));

  *sxt_count_ptr = 1 + /* SYNC_XTION_COUNT + */
  		sync_party_count(RT[xi_sync]);
  if (GSTATUS[INDEX_EXIT] & FLAG_EXIT_AFTER_SYNC_XTION_COUNTING) { 
    fprintf(RED_OUT, "\n%1d sync transtions alread generated.\n", SYNC_XTION_COUNT); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("psx: after sync_party_count");
  #endif 

  *sxtable_ptr = (struct sync_xtion_type *) 
	malloc((*sxt_count_ptr)*sizeof(struct sync_xtion_type));
  PSX_NEW_TABLE = *sxtable_ptr; 
  PSX_SYNC = xi_sync; 
  PSX_NEW_COUNT = 1; 
  
  // first fill in the null sync xtions. 
  PSX_NEW_TABLE[0].party_count = 0;  
  PSX_NEW_TABLE[0].party = NULL; 
  PSX_NEW_TABLE[0].qfd_sync_count = 0;  
  PSX_NEW_TABLE[0].qfd_sync = NULL; 
  PSX_NEW_TABLE[0].ec_representative = (int *) malloc(3*sizeof(int)); 
  PSX_NEW_TABLE[0].ec_representee = (int **) malloc(3*sizeof(int *)); 
/*
  PSX_NEW_TABLE[0].red_ec_ineq_representative 
  = (struct red_type **) malloc(3*sizeof(struct red_type *)); 
  PSX_NEW_TABLE[0].red_ec_ineq_weak_fairness_representative 
  = (struct red_type **) malloc(3*sizeof(struct red_type *)); 
*/

/*
  fprintf(RED_OUT, "RT[XI_RESTRICTION=%1d] to sync_party_malloc():\n", XI_RESTRICTION); 
  red_print_graph(RT[XI_RESTRICTION]); 
  fprintf(RED_OUT, "\nRT[xi_sync=%1d] before sync malloc:\n", 
    xi_sync
  ); 
  red_print_graph(RT[xi_sync]); 
  fflush(RED_OUT); 
*/  
  max_qfd_sync = 0; 
  sync_party_malloc(RT[xi_sync], 0, 0);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("psx: after sync_party_malloc");
  #endif 

  qfd_sync = (struct qfd_sync_type *) malloc(max_qfd_sync * sizeof(struct qfd_sync_type)); 
/*
  fprintf(RED_OUT, "%1d qfd_sync allocated at %x\n", max_qfd_sync, qfd_sync); 
  fprintf(RED_OUT, "Before sync party fillin\n"); 
  report_red_management(); 
*/
  PSX_NEW_COUNT = 1; 
/*
  fprintf(RED_OUT, "prepare sync xtion: input sync=%1d:%x\n", 
    xi_sync, RT[xi_sync]
  ); 
*/
  // first fill in the null sync xtions. 
  PSX_NEW_TABLE[0].index = 0; 
  PSX_NEW_TABLE[0].status = 0; 
  PSX_NEW_TABLE[0].red_trigger = NORM_NO_RESTRICTION; 
  PSX_NEW_TABLE[0].red_post = NORM_NO_RESTRICTION; 
  for (ci = 0; ci < 3; ci++) { 
    PSX_NEW_TABLE[0].ec_representative[ci] = 0; 
    PSX_NEW_TABLE[0].ec_representee[ci] = NULL; 
/*
    PSX_NEW_TABLE[0].red_ec_ineq_representative[ci] = NULL; 
    PSX_NEW_TABLE[0].red_ec_ineq_weak_fairness_representative[ci] = NULL; 
*/
  } 
/*
  fprintf(RED_OUT, "\nRT[xi_sync=%1d] before sync party fillin:\n", 
    xi_sync
  ); 
  red_print_graph(RT[xi_sync]); 
  fflush(RED_OUT); 
*/  
  RT[xi_sync_bulk = RT_TOP++] = sync_party_fillin(RT[xi_sync], 0, 0);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("psx: after sync_party_fillin");
  psx_status("after 1st fillin", PSX_NEW_TABLE, *sxt_count_ptr); 
  #endif 
/*
  fprintf(RED_OUT, "prepare sync xtion: writing to sync bulk=%1d+%1d=%1d:%x\n", 
    xi_sync, OFFSET_BULK, xi_sync+OFFSET_BULK, RT[xi_sync+OFFSET_BULK]
  ); 
  fprintf(RED_OUT, "After sync party fillin\n"); 
  red_print_graph(RT[xi_sync]); 
  report_red_management(); 
  */
  
  /* Now construct all the CRDs in the sync xtions. */   
  for (isi = 0; isi < *sxt_count_ptr; isi++) { 
/*
    fprintf(RED_OUT, "\n===[prepare SYNC XTION %1d proocessing, RT_TOP=%1d]==============\n", 
            isi, RT_TOP
            ); 
    fprintf(RED_OUT, "\n==========================\n"); 
*/
    RT[qfd_sync_value = RT_TOP++] = NORM_NO_RESTRICTION; 
    for (xsi = 0; xsi < PSX_NEW_TABLE[isi].qfd_sync_count; xsi++) 
      RT[qfd_sync_value] = ddd_one_constraint(RT[qfd_sync_value], 
	PSX_NEW_TABLE[isi].qfd_sync[xsi].vi, 
	PSX_NEW_TABLE[isi].qfd_sync[xsi].value, 
	PSX_NEW_TABLE[isi].qfd_sync[xsi].value 
      ); 
    /* first record the peer identifiers of quantified synchronizations 
     * in the CLOCK1 and CLOCK2 of synchronizers.
    fprintf(RED_OUT, 
      "\nThe initial RT[sx_trigger] is RT[qfd_sync_value]:\n"
    ); 
     */
    RT[sx_trigger = RT_TOP++] = RT[qfd_sync_value]; 
    RT[events = RT_TOP++] = NORM_NO_RESTRICTION; 
    ITERATE_SXI = isi; 

    /* first record the peer identifiers of quantified synchronizations 
     * in the CLOCK1 and CLOCK2 of synchronizers.
     */
    /* Record the qfd sync variable branching effect. */ 
    PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status & ~FLAG_BRANCHING_QFD_SYNC; 
/*
    fprintf(RED_OUT, 
      "\nPrepare_sync_xtion, PSX_NEW_TABLE[%1d].status = %x\n", 
      isi, PSX_NEW_TABLE[isi].status
    ); 
    fflush(RED_OUT); 
*/
 
    /* construct the array of actions from component xtions. */ 
    if (PSX_NEW_TABLE[isi].qfd_sync_count) { 
      for (ai = 0; ai < PSX_NEW_TABLE[isi].qfd_sync_count; ai++) 
        VAR[PSX_NEW_TABLE[isi].qfd_sync[ai].vi].U.DISC.CORRESPONDING_PI
        = PSX_NEW_TABLE[isi].qfd_sync[ai].value; 
      for (ixi = 0; ixi < PSX_NEW_TABLE[isi].party_count; ixi++) { 
        ITERATE_XI = xi = PSX_NEW_TABLE[isi].party[ixi].xtion;
        ITERATE_PI = pi = PSX_NEW_TABLE[isi].party[ixi].proc;

        MASK_MARK = FLAG_GC_STABLE;
        #ifdef RED_DEBUG_PARSE_MODE 
        fprintf(RED_OUT, 
          "\npst, before sync_statement isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
          isi, xi, pi, RT_TOP
        ); 
        #endif 

        PSX_NEW_TABLE[isi].party[ixi].statement 
        = sync_statement(XTION[xi].statement, pi); 
        #ifdef RED_DEBUG_PARSE_MODE 
        print_cpu_time("psx: after sync_statement for sxi=%1d, party=%1d", 
          isi, ixi
        );
        fprintf(RED_OUT, 
          "\npst, after sync_statement isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
          isi, xi, pi, RT_TOP
        ); 
        #endif 
      } 	
    }
    else { 
      for (ixi = 0; ixi < PSX_NEW_TABLE[isi].party_count; ixi++) { 
        xi = PSX_NEW_TABLE[isi].party[ixi].xtion;
        pi = PSX_NEW_TABLE[isi].party[ixi].proc;
        PSX_NEW_TABLE[isi].party[ixi].statement = XTION[xi].statement;     
      } 	      
    } 

    /* Now calculate the redpost and triggering red and distance. */      
    PSX_NEW_TABLE[isi].distance_change = 0; 
    PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status 
    & ~MASK_XTION_SIDE_EFFECTS; 
    for (ixi = 0; ixi < PSX_NEW_TABLE[isi].party_count; ixi++) {
      ITERATE_XI = xi = PSX_NEW_TABLE[isi].party[ixi].xtion;
      ITERATE_PI = pi = PSX_NEW_TABLE[isi].party[ixi].proc;
/*
      fprintf(RED_OUT, "\n---[Adding party %1d:(pi=%1d,xi=%1d)]-----\n", 
      	      ixi, pi, xi
      	      ); 
*/
      PSX_NEW_TABLE[isi].status 
      = PSX_NEW_TABLE[isi].status 
      | (XTION[xi].status & MASK_XTION_SIDE_EFFECTS); 
      if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC)
        PSX_NEW_TABLE[isi].status 
        = PSX_NEW_TABLE[isi].status | FLAG_SYNC_XTION_QUANTIFIED_SYNC; 
      if (   valid_mode_index(XTION[xi].dst_mode_index) 
          && valid_mode_index(XTION[xi].src_mode_index)
          ) 
        PSX_NEW_TABLE[isi].distance_change
        = PSX_NEW_TABLE[isi].distance_change
        + PROCESS[pi].mode_distance_from_initial[XTION[xi].dst_mode_index]
        - PROCESS[pi].mode_distance_from_initial[XTION[xi].src_mode_index];      
      else 
        PSX_NEW_TABLE[isi].distance_change = 0; 
/*      
      fprintf(RED_OUT, "1) conjuncting xtion trigger:\n"); 
      red_print_graph(XTION[xi].red_trigger[pi]); 
      fprintf(RED_OUT, "2) conjuncting acc result:\n"); 
      red_print_graph(RT[sx_trigger]); 
*/
      PSX_NEW_TABLE[isi].party[ixi].trigger_exp 
      = exp_static_evaluation(XTION[xi].parse_xtion->trigger_exp, 
        ITERATE_PI, 
        &(PSX_NEW_TABLE[isi])
      ); 
      PSX_NEW_TABLE[isi].party[ixi].trigger_exp 
      = rec_ineq_analyze(PSX_NEW_TABLE[isi].party[ixi].trigger_exp); 
      PSX_NEW_TABLE[isi].party[ixi].trigger_exp 
      = shorthand_analysis(PSX_NEW_TABLE[isi].party[ixi].trigger_exp); 
/*
      fillin_indirect_reference(ITERATE_PI, 
        PSX_NEW_TABLE[isi].party[ixi].trigger_exp
      ); 
*/
      PSX_NEW_TABLE[isi].party[ixi].red_trigger 
      = red_local(PSX_NEW_TABLE[isi].party[ixi].trigger_exp, ITERATE_PI, 0); 
      RT[sx_trigger] = red_bop(AND, RT[sx_trigger], 
        PSX_NEW_TABLE[isi].party[ixi].red_trigger
      ); 
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time("psx: after conjuncting red_trigger xi=%1d, pi=%1d", 
        xi, pi
      );
      #endif 
/*
      fprintf(RED_OUT, "3) conjuncted new acc result:\n"); 
      red_print_graph(RT[sx_trigger]); 
*/      
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time(
        "psx: after conjuncting red_trigger xi=%1d, pi=%1d for qfd_sync", 
        xi, pi
      );
      fprintf(RED_OUT, 
        "\npst, before eliminate simple qfd sync isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
      #endif 
      
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time(
        "psx: after eliminating simple qfd syncfor sxi=%1d, pi=%1d", 
        isi, ixi
      );
      fprintf(RED_OUT, 
        "\npst, after eliminate simple qfd sync isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
      #endif 
      
      red_mark(PSX_NEW_TABLE[isi].party[ixi].red_trigger, FLAG_GC_STABLE);
    } 
    if (PSX_NEW_TABLE[isi].status & FLAG_XTION_GLOBAL_WRITING) {
      if (PSX_NEW_TABLE[isi].status & FLAG_XTION_SRC_GLOBAL_READING) 
        PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status 
        | FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE; 
      if (PSX_NEW_TABLE[isi].status & FLAG_XTION_DST_GLOBAL_READING) 
        PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status 
        | FLAG_XTION_FWD_ACTION_INV_INTERFERE; 
    }
    if (PSX_NEW_TABLE[isi].status & FLAG_XTION_SRC_PEER_READING) 
      PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status 
      | FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE; 
    if (PSX_NEW_TABLE[isi].status & FLAG_XTION_DST_PEER_READING) 
      PSX_NEW_TABLE[isi].status = PSX_NEW_TABLE[isi].status 
      | FLAG_XTION_FWD_ACTION_INV_INTERFERE; 

    if (flag_bisim_analysis) { 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, 
        "\npst, before MODL SPEC write cons, isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
      #endif 
      
      PSX_NEW_TABLE[isi].red_ec_global_write_consistency 
      = red_MODL_SPEC_write_consistency(isi, SYNC_XTION_GAME); 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, 
        "\npst, after MODL SPEC write cons, isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
/*
      fprintf(RED_OUT, "4) after computing write consistency:\n"); 
      red_print_graph(PSX_NEW_TABLE[isi].red_ec_global_write_consistency); 
*/      
      #endif 
      
      RT[sx_trigger] = red_bop(AND, RT[sx_trigger], 
	PSX_NEW_TABLE[isi].red_ec_global_write_consistency
      ); 
			       
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, 
        "5) RT[sx_trigger=%1d], after enforcing write consistency:\n", 
        sx_trigger
      ); 
      red_print_graph(RT[sx_trigger]); 
      #endif 

      red_mark(PSX_NEW_TABLE[isi].red_ec_global_write_consistency, FLAG_GC_STABLE);
    } 
/*
    fprintf(RED_OUT, "top_level_child_stack=%1d\n", TOP_LEVEL_CHILD_STACK);    
    fprintf(RED_OUT, 
      "\nBefore calculating approximate postcondition for sync xtion %1d.\n", 
      isi
    ); 
    fprintf(RED_OUT, "\nRT[sx_trigger=%1d]:\n", sx_trigger); 
    red_print_graph(RT[sx_trigger]); 
*/
    RT[post = RT_TOP++] = red_type_eliminate(RT[sx_trigger], TYPE_LAZY_EXP); 
    for (ixi = 0; ixi < PSX_NEW_TABLE[isi].party_count; ixi++) {
      ITERATE_XI = xi = PSX_NEW_TABLE[isi].party[ixi].xtion;
      ITERATE_PI = pi = PSX_NEW_TABLE[isi].party[ixi].proc;
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "\n>>>>>>>>>>>>>>>>>>>>>>>>>\n"); 
      fprintf(RED_OUT, 
        "pst, before the red_posting of red statement fwd, isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
      print_xtion(xi, pi); 
      #endif 

      RT[post] = red_statement_fwd(
	post, 
	pi, 
	PSX_NEW_TABLE[isi].party[ixi].statement, 
	FLAG_ROOT_OAPPROX | FLAG_OAPPROX_DISCRETE_LAZY, 
	FLAG_ACTION_LAZY_EVAL  
      ); 
      #ifdef RED_DEBUG_PARSE_MODE 
/*
      print_cpu_time("psx: after red statement fwd sxi=%1d, pi=%1d, xi=%1d", 
        isi, pi, xi
      );
*/
      fprintf(RED_OUT, 
        "\npst, after red statement fwd, isi=%1d, xi=%1d, pi=%1d, RT_TOP=%1d\n", 
        isi, xi, pi, RT_TOP
      ); 
      red_print_graph(RT[post]); 
      #endif 
      
      if (XTION[xi].dst_mode_index != MODE_NO_SPEC) 
        RT[post] = ddd_one_constraint(
          RT[post], variable_index[TYPE_DISCRETE][pi][OFFSET_MODE],
          XTION[xi].dst_mode_index, XTION[xi].dst_mode_index
        );
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time("psx: after conjuncting dst mode index sxi=%1d, pi=%1d, xi=%1d", 
        isi, pi, xi
      );
      red_print_graph(RT[post]); 
      #endif 
         
      RT[events] = red_bop(AND, RT[events], XTION[xi].red_events[pi]); 
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time("psx: after adding red events sxi=%1d, xi=%1d", 
        isi, xi
      );
      #endif 
    }
    
    PSX_NEW_TABLE[isi].red_events = red_no_event_set(RT[events]); 
    PSX_NEW_TABLE[isi].red_trigger 
    = eliminate_simple_qfd_sync(RT[sx_trigger]); 
    PSX_NEW_TABLE[isi].red_pre 
    = PSX_NEW_TABLE[isi].red_trigger; 
    PSX_NEW_TABLE[isi].red_post 
    = eliminate_simple_qfd_sync(RT[post]); 
    
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, 
      "\nPSX_NEW_TABLE[isi=%1d].red_post before redmarking:\n", 
      isi
    ); 
    red_print_graph(PSX_NEW_TABLE[isi].red_trigger); 
    red_print_graph(PSX_NEW_TABLE[isi].red_post); 
    red_print_graph(PSX_NEW_TABLE[isi].red_events); 
    #endif 
    
    RT_TOP = RT_TOP-4; /* qfd_sync_value, events, sx_trigger, post */ 
    red_mark(PSX_NEW_TABLE[isi].red_trigger, FLAG_GC_STABLE);
    red_mark(PSX_NEW_TABLE[isi].red_events, FLAG_GC_STABLE);
    red_mark(PSX_NEW_TABLE[isi].red_post, FLAG_GC_STABLE);
/*
    fprintf(RED_OUT, "\n--------------------------------------\n"); 
    fprintf(RED_OUT, "red_trigger after quantified synchronization for SYNC_XTION[%1d]:\n", isi); 
    red_print_graph(PSX_NEW_TABLE[isi].red_trigger); 
    fprintf(RED_OUT, "red_post after quantified synchronization for SYNC_XTION[%1d]:\n", isi); 
    red_print_graph(PSX_NEW_TABLE[isi].red_post); 
    fflush(RED_OUT); 
*/
  }
/*
  psx_status("after 2nd fillin", PSX_NEW_TABLE, *sxt_count_ptr); 
  fprintf(RED_OUT, "After constructing all reds of sync xtions\n"); 
  report_red_management(); 
*/
  /* calculate the red_trigger and red_post of the sync_xtion[] */ 
  if ((GSTATUS[INDEX_SEARCH] & MASK_SEARCH) == FLAG_FIRST_MODE_DISTANCE) {
    int	isj;

    for (isi = 0; isi < (*sxt_count_ptr)-1; isi++) {
      for (isj = isi+1; isj < *sxt_count_ptr; isj++) {
        if (PSX_NEW_TABLE[isi].distance_change < PSX_NEW_TABLE[isj].distance_change) {
          struct sync_xtion_type	tmp_syncx;

          tmp_syncx = PSX_NEW_TABLE[isi];
          PSX_NEW_TABLE[isi] = PSX_NEW_TABLE[isj];
          PSX_NEW_TABLE[isj] = tmp_syncx;
        }
      }
    }
  }
/*
  psx_status("after distancing", PSX_NEW_TABLE, *sxt_count_ptr); 
  fprintf(RED_OUT, "Before prepare sync distancing\n"); 
  report_red_management(); 
  fprintf(RED_OUT, "\n=============(%1d sync xtions)====================\n", SYNC_XTION_COUNT);
  This section records which event fairness assumptions are related to 
  a sync xtion and record the fairness assumptions' occ vi in occ_vi array. 
*/
  for (isi = 0; isi < *sxt_count_ptr; isi++) {
    int				gi, gvi, pi, xi, si;
    struct index_link_type	*il; 

    PSX_NEW_TABLE[isi].occ_vi_count = 0; 
    filist = NULL; 
    for (gi = 0; gi < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; gi++) {
      gvi = variable_index[TYPE_SYNCHRONIZER][0][gi];
      VAR[gvi].U.SYNC.DIFF = 0;
    }
    for (pi = 0; pi < PSX_NEW_TABLE[isi].party_count; pi++) {
      xi = PSX_NEW_TABLE[isi].party[pi].xtion;
      for (si = 0; si < XTION[xi].sync_count; si++) 
        if (XTION[xi].sync[si].type < 0) {
          gi = XTION[xi].sync[si].sync_index;
          gvi = variable_index[TYPE_SYNCHRONIZER][0][gi];
      	  VAR[gvi].U.SYNC.DIFF++; 
        }
    }
/*
    for (gi = 0; gi < GLOBAL_COUNT[TYPE_DISCRETE]; gi++) { 
      gvi = variable_index[TYPE_DISCRETE][0][gi]; 
      if (!(VAR[gvi].STATUS & FLAG_FAIRNESS_OCCURRENCE)) 
        continue; 
      if (   (!(((struct ps_exp_type *) VAR[gvi].MODE_RATE_SPEC)->status & FLAG_EXP_STATE_INSIDE))
          && rec_set_sxi_event_flag
	     ((struct ps_exp_type *) VAR[gvi].MODE_RATE_SPEC)
	  ) {
        filist = add_index_count(filist, gvi, &(SYNC_XTION[isi].occ_vi_count));   
      }
    }
*/    
    PSX_NEW_TABLE[isi].occ_vi 
    = (int *) malloc(PSX_NEW_TABLE[isi].occ_vi_count * sizeof(int)); 
    for (gi = 0, il = filist; 
	 gi < PSX_NEW_TABLE[isi].occ_vi_count && il; 
	 gi++, il = il->next_index_link
	 ) { 
      PSX_NEW_TABLE[isi].occ_vi[gi] = il->index;  	
    }
    free_index_list(filist); 
/*
    fprintf(RED_OUT, "SX%4d, status:%1d, distance_change:%1d; \n",
	    isi, SYNC_XTION[isi].status, SYNC_XTION[isi].distance_change
	    );
    for (ixi = 0; ixi < SYNC_XTION[isi].party_count; ixi++) {
      fprintf(RED_OUT, "\t");
      print_xtion_line(SYNC_XTION[isi].party[ixi].xtion, SYNC_XTION[isi].party[ixi].proc);
      fprintf(RED_OUT, "\n");
    }
    print_sync_xtion(isi, PSX_NEW_TABLE); 
*/
  }
  free(qfd_sync); 

  free(sync_party_proc); /* The two arrays on the left were allocated at the beginning of */
  free(sync_party_xtion);/* red_sync_xi_restriction() */ 

  #ifdef RED_DEBUG_PARSE_MODE 
  psx_status("after fairness occ", PSX_NEW_TABLE, *sxt_count_ptr); 
  
  fprintf(RED_OUT, "\n***[%1d new sync transtions generated]********************\n", 
    *sxt_count_ptr
  ); 
  print_sync_xtions("After sync xtion preparation", PSX_NEW_TABLE, PSX_NEW_COUNT); 
  fprintf(RED_OUT, "The sync bulk:\n"); 
  red_print_graph(RT[xi_sync_bulk]); 
  fflush(RED_OUT); 
  #endif 
  
  RT_TOP--; /* xi_sync_bulk */ 
  
  return(RT[xi_sync_bulk]); 
}
  /* prepare_sync_xtions() */  





  

  

/**************************************************************************************************
 *  For forward bulk analysis, FILTER_XI_RESTRICTION is with only untimed triggering condition.
 *  For forward sync analysis, FILTER_XI_RESTRICTION is also with without any triggering condition.
 *  For backward analysis, FILTER_XI_RESTRICTION is with all triggering condition.
 *  For backward analysis, FILTER_XI_SYNC_BULK_WITH_POSTCONDITION is without any triggering condition.
 */
 
struct red_type *f78(f) 
  struct red_type *f; 
{
  f = ddd_one_constraint(f, variable_index[TYPE_XTION_INSTANCE][1][0], 7, 8); 
  return(f); 
}
  /* f78() */  
  
  

int	rec_bulk_global_effect(d)
     struct red_type	*d;
{
  int			ci, flag, xi;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(0);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, risx_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					);
  if (rec != nrec) { 
    return(0); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    flag = 0; 
    for (ci = d->u.ddd.child_count-1; ci >= 0 && (!flag); ci--) {
      ic = &(d->u.ddd.arc[ci]);
      flag = flag | rec_bulk_global_effect(ic->child);
      for (xi = ic->lower_bound; xi <= ic->upper_bound; xi++)
        if (xi) 
          flag = flag | (XTION[xi].status & MASK_XTION_SIDE_EFFECTS);
    }
    return(flag); 
    break; 
  case TYPE_POINTER: 
    if (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) { 
      flag = 0; 
      for (ci = d->u.ddd.child_count-1; ci >= 0 && (!flag); ci--) { 
        ic = &(d->u.ddd.arc[ci]);
        flag = flag | rec_bulk_global_effect(ic->child);
      }
      return(flag); 
      break; 
    }
  default:
    fprintf(RED_OUT, "\nUnexpected diagram type %1d\n", 
      VAR[d->var_index].TYPE
    ); 
    bk(0); 
  }
}
  /* rec_bulk_global_effect() */




int	red_bulk_global_effect(d)
     struct red_type	*d;
{
  int	flag;

/*
  print_cpu_time("Before red_keep_pure_sync_bulk()");
  red_print_graph(RT[f]); 
*/  

  init_23tree(&risx_tree); 
  flag = rec_bulk_global_effect(d);
  free_entire_23tree(risx_tree, rec_free); 
  
  /* 
  print_cpu_time("After red_cdd()");
  fprintf(RED_OUT, "Leaving red_keep_pure_sync_bulk()");
  red_print_graph(result); 
  */
  
  return(flag);
}
/* red_bulk_global_effect() */




filter_sync_xi_restriction()
{
  int 				pi, pj, fxi, ixi, xi, isi, si, imi, mi, ci, 
				iai, tmp_depth;
  struct sync_xtion_rec_type	*sx;
  struct red_type		*conj, *sub, *result;
  struct index_link_type	*filist; 

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("entering filter_sync_xi_restriction()");
  print_processes(); 
  #endif 

  RT[XI_SYNC_ALL] = red_sync_xi_restriction(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after red_sync_xi_restriction");
  fprintf(RED_OUT, "RT[XI_SYNC_ALL=%1d], the initial one:\n", XI_SYNC_ALL);
  red_print_graph(RT[XI_SYNC_ALL]);
  #endif 
  
  race_eliminate(XI_SYNC_ALL);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after race_eliminate");
  fprintf(RED_OUT, "\n=================================================\n"); 
  fprintf(RED_OUT, "RT[XI_SYNC_ALL=%1d], after race elimination:\n", XI_SYNC_ALL);
  red_print_graph(RT[XI_SYNC_ALL]);
  fflush(RED_OUT);
  #endif 
  
  RT[XI_SYNC_ALL_WITH_EVENTS] = NORM_NO_RESTRICTION; 
  
  if (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYNC_ADDRESS_RESRICTION)) { 
    RT[XI_SYNC_ALL_WITH_PROC_HOLDERS] = RT[XI_SYNC_ALL]; 
  }
  else { 
    RT[XI_SYNC_ALL_WITH_PROC_HOLDERS] 
    = red_check_sync_proc_holders(RT[XI_SYNC_ALL]); 
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("fxi_res: after red_check_sync_proc_holders");
    fprintf(RED_OUT, "\n=================================================\n"); 
    fprintf(RED_OUT, 
      "RT[XI_SYNC_ALL=%1d], after XI_SYNC_ALL_WITH_PROC_HOLDERS:\n", 
      XI_SYNC_ALL
    );
    red_print_graph(RT[XI_SYNC_ALL]);
    fflush(RED_OUT);
    fprintf(RED_OUT, 
      "RT[XI_SYNC_ALL_WITH_PROC_HOLDERS=%1d], after checking sync proc holders:\n", 
      XI_SYNC_ALL_WITH_PROC_HOLDERS
    );
    red_print_graph(RT[XI_SYNC_ALL_WITH_PROC_HOLDERS]);
    fflush(RED_OUT);
    #endif 

    RT[XI_SYNC_ALL] = red_keep_pure_sync_bulk(
      RT[XI_SYNC_ALL_WITH_PROC_HOLDERS]
    ); 
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("fxi_res: after red_keep_pure_sync_bulk");
    fprintf(RED_OUT, "\n=================================================\n"); 
    fprintf(RED_OUT, 
      "RT[XI_SYNC_ALL=%1d], after red_keep_pure_sync_bulk:\n", 
      XI_SYNC_ALL
    );
    red_print_graph(RT[XI_SYNC_ALL]);
    fprintf(RED_OUT, 
      "RT[XI_SYNC_ALL_WITH_PROC_HOLDERS=%1d], after red_keep_pure_sync_bulk:\n", 
      XI_SYNC_ALL_WITH_PROC_HOLDERS
    );
    red_print_graph(RT[XI_SYNC_ALL_WITH_PROC_HOLDERS]); 
/*
    fprintf(RED_OUT, "Add sync proc holders\n"); 
    report_red_management(); 
*/
    #endif 
  }
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: before prepare_sync_xtions");
//  report_red_management(); 
  #endif   
  
  if (DEPTH_ENUMERATIVE_SYNCHRONIZATION == DEPTH_ENUMERATIVE_DEFAULT) { 
    DEPTH_ENUMERATIVE_SYNCHRONIZATION 
    = calculate_depth_enumerative_synchronization(RT[XI_SYNC_ALL]); 
  } 
  RT[XI_SYNC_BULK] = prepare_sync_xtions(
    XI_SYNC_ALL_WITH_PROC_HOLDERS, 
    &SYNC_XTION, &SYNC_XTION_COUNT, 
    TYPE_FALSE // not for a bisimulation analysis 
  ); 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\nEnumerated sync xtions: %1d\n", 
    SYNC_XTION_COUNT
  ); 
  print_cpu_time("fxi_res: after prepare_sync_xtions");
  #endif   
  
  si = red_bulk_global_effect(RT[XI_SYNC_BULK]); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after red_bulk_global_effect");
  #endif 
  
  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
  = GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
  & ~FLAG_BULK_TRIGGER_ACTION_INTERFERE;
  if (si & FLAG_XTION_GLOBAL_WRITING) {
    if (si & FLAG_XTION_SRC_GLOBAL_READING) 
      GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      = GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      | FLAG_BULK_TRIGGER_ACTION_INTERFERE; 
    if (si & FLAG_XTION_DST_GLOBAL_READING) 
      GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      = GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      | FLAG_BULK_TRIGGER_ACTION_INTERFERE; 
  }
//  if (si & FLAG_XTION_PEER_WRITING) {
    if (si & FLAG_XTION_SRC_PEER_READING) 
      GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      = GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      | FLAG_BULK_TRIGGER_ACTION_INTERFERE; 
    if (si & FLAG_XTION_DST_PEER_READING) 
      GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      = GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      | FLAG_BULK_TRIGGER_ACTION_INTERFERE; 
//  }
/*
  fprintf(RED_OUT, "After prepare sync\n"); 
  report_red_management(); 
  print_cpu_time("After preparing sync xtions");
  fprintf(RED_OUT, "\nRT[XI_SYNC_BULK=%1d]:\n", XI_SYNC_BULK);
  red_print_graph(RT[XI_SYNC_BULK]);
*/

  init_ec_management(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after init_ec_management");
  #endif 
  
  if (RT[XI_SYNC_BULK] != NORM_FALSE) { 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_HUGE_SYNC; 
  } 
  RT[XI_SYNC_BULK_WITH_TRIGGERS] 
  = red_add_trigger_sync_bulk(RT[XI_SYNC_BULK]);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after red_add_trigger_sync_bulk");
  #endif 
  
  RT[XI_SYNC_BULK_WITH_EVENTS] = red_no_event_set(red_add_events(
    RT[XI_SYNC_BULK], MASK_GAME_ROLES
  ) ); 
/*
  fprintf(RED_OUT, "\nRT[XI_SYNC_BULK_WITH_EVENTS=%1d]:\n", 
    XI_SYNC_BULK_WITH_EVENTS
  ); 
  red_print_graph(RT[XI_SYNC_BULK_WITH_EVENTS]); 
  
  fprintf(RED_OUT, "\nRT[XI_SYNC_BULK_WITH_TRIGGERS=%1d]:\n", XI_SYNC_BULK_WITH_TRIGGERS);
  red_print_graph(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
*/  
  RT[XI_SYNC_BULK_WITH_POSTCONDITION] 
  = add_post_condition(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after add_post_condition");
  #endif 
/*
  fprintf(RED_OUT, "after calculating RT[XI_SYNC_BULK_WITH_POSTCONDITION=%1d]\n", 
    XI_SYNC_BULK_WITH_POSTCONDITION
  ); 
*/
  garbage_collect(FLAG_GC_SILENT);


  // Now we construct the xi_sync_all family for serious. 
  // This means that we have to include the sync xtions with all xi=0. 
  RT[XI_SYNC_ALL_WITH_TRIGGERS] 
  = NULL; 

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: after red_add_trigger_sync_bulk");
  #endif 
  
  RT[XI_SYNC_ALL_WITH_EVENT_PROC_HOLDERS] = RT[XI_SYNC_ALL]; 
/*
  fprintf(RED_OUT, 
          "RT[XI_SYNC_ALL_WITH_EVENT_PROC_HOLDERS=%1d]:\n", 
          XI_SYNC_ALL_WITH_EVENT_PROC_HOLDERS
          );
  red_print_graph(RT[XI_SYNC_ALL_WITH_EVENT_PROC_HOLDERS]);

  fprintf(RED_OUT, 
          "\nLeaving sync ALL restriction\nRT[XI_SYNC_ALL=%1d]:\n", 
          XI_SYNC_ALL
          );
  red_print_graph(RT[XI_SYNC_ALL]);

  fprintf(RED_OUT, 
          "RT[XI_SYNC_ALL_WITH_TRIGGERS=%1d]:\n", 
          XI_SYNC_ALL_WITH_TRIGGERS
          );
  red_print_graph(RT[XI_SYNC_ALL_WITH_TRIGGERS]);

  fprintf(RED_OUT, 
          "\nLeaving sync bulk restriction\nRT[XI_SYNC_BULK=%1d]:\n", 
          XI_SYNC_BULK
          );
  red_print_graph(RT[XI_SYNC_BULK]);
  fprintf(RED_OUT, 
          "RT[XI_SYNC_BULK_WITH_TRIGGERS=%1d]:\n", 
          XI_SYNC_BULK_WITH_TRIGGERS
          );
  red_print_graph(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
  fprintf(RED_OUT, 
          "RT[XI_SYNC_BULK_WITH_POSTCONDITION=%1d]:\n", 
          XI_SYNC_BULK_WITH_POSTCONDITION
          );
  red_print_graph(RT[XI_SYNC_BULK_WITH_POSTCONDITION]);
  fprintf(RED_OUT, 
          "\nLeaving sync bulk restriction\nRT[XI_SYNC_BULK=%1d]:\n", 
          XI_SYNC_BULK
          );
  red_print_graph(RT[XI_SYNC_BULK]);
  fprintf(RED_OUT, 
          "RT[XI_SYNC_BULK_WITH_TRIGGERS=%1d]:\n", 
          XI_SYNC_BULK_WITH_TRIGGERS
          );
  red_print_graph(RT[XI_SYNC_BULK_WITH_TRIGGERS]);
  fprintf(RED_OUT, 
          "RT[XI_SYNC_BULK_WITH_POSTCONDITION=%1d]:\n", 
          XI_SYNC_BULK_WITH_POSTCONDITION
          );
  red_print_graph(RT[XI_SYNC_BULK_WITH_POSTCONDITION]);
  fprintf(RED_OUT, "\nTo garbage report for FILTER_SYNC_XI_RESTRICTION\n");
  */
}
/* filter_sync_xi_restriction() */








struct red_type	*red_debug_initial()
{
  int			ci, di;
  struct red_type	*d;

  d = NORM_TRUE;

  for (di = 1; di <= PROCESS_COUNT; di++) {
    d = red_bop(AND, d, ddd_atom(variable_index[TYPE_DISCRETE][di][0], 0, 0));
  }

  return(d);
}
/* red_debug_initial() */


void	set_debug() {
  GSTATUS[INDEX_DEBUG] = GSTATUS[INDEX_DEBUG] & ~FLAG_DEBUG_INITIAL;
}
/* set_debug() */



int 	IB_CMVI, IB_CVI, IB_CI, IB_XI;


int	arc_count;


int	rec_big_timing_constant_in_CRD(d)
     struct red_type	*d;
{
  int				c1, c2, ci, bigc, onec;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE ||d->var_index == TYPE_FALSE)
    return(0);

  ce = cache1_check_result_key(
  	OP_BIG_TIMING_CONSTANT_IN_CRD, d
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  bigc = 0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == IB_CI)
      if (c2)
        return(CLOCK_POS_INFINITY);
      else if (d->u.crd.arc[d->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
        bigc = d->u.crd.arc[d->u.ddd.child_count-2].upper_bound+1;
      else
        bigc = d->u.crd.arc[d->u.ddd.child_count-1].upper_bound+1;
    else if (c2 == IB_CI)
      if (c1)
        return(CLOCK_POS_INFINITY);
      else
        bigc = -1*d->u.crd.arc[0].upper_bound;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      onec = rec_big_timing_constant_in_CRD(d->u.crd.arc[ci].child);
      if (bigc < onec)
        bigc = onec;
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      onec = rec_big_timing_constant_in_CRD(d->u.hrd.arc[ci].child);
      if (bigc < onec)
        bigc = onec;
    }
    break;
  case TYPE_LAZY_EXP: 
    onec = rec_big_timing_constant_in_CRD(d->u.lazy.false_child);
    if (bigc < onec)
      bigc = onec;
    onec = rec_big_timing_constant_in_CRD(d->u.lazy.true_child);
    if (bigc < onec)
      bigc = onec;
    break; 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      onec = rec_big_timing_constant_in_CRD(d->u.fdd.arc[ci].child);
      if (bigc < onec)
        bigc = onec;
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      onec = rec_big_timing_constant_in_CRD(d->u.dfdd.arc[ci].child);
      if (bigc < onec)
        bigc = onec;
    }
    break; 
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      onec = rec_big_timing_constant_in_CRD(d->u.ddd.arc[ci].child);
      if (bigc < onec)
        bigc = onec;
    }
  }
  return((int) (ce->result 
	  = (struct red_type *) bigc
  ) );
  return(bigc);
}
/* rec_big_timing_constant_in_CRD() */



int	big_timing_constant_in_CRD(d)
	struct red_type	*d;
{
  int	bigc;

  bigc = rec_big_timing_constant_in_CRD(d);

  return(bigc);
}
/* big_timing_constant_in_CRD() */




int	big_timing_constant_in_action_clock_assign_constant(pi, act)
     int			pi;
     struct statement_type	*act;
{
  int 			lvi, lci;
  struct ps_exp_type	*lvar;

  lvar = act->u.act.lhs;

/*
  if (lvar->u.atom.indirect_count)
    return(-1);
  else {
*/
    lvi = lvar->u.atom.var_index;
    if (lvar->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
      lvi = variable_index[TYPE_CLOCK][pi][VAR[lvi].OFFSET];
    lci = VAR[lvi].U.CLOCK.CLOCK_INDEX;

    if (lci == IB_CI)
      return(0);
    else
      return(-1);
//  }
}
/* big_timing_constant_in_action_clock_assign_constant() */






int	big_timing_constant_in_action_clock_assign_exp(pi, act)
     int			pi;
     struct statement_type	*act;
{
  int 			lvi, lci, rvi, rci;
  struct ps_exp_type	*lvar, *rvar;

  lvar = act->u.act.term[0].operand;
  rvar = act->u.act.term[1].operand;

/*
  if (rvar->u.atom.indirect_count)
    return(CLOCK_POS_INFINITY);
*/
  rvi = rvar->u.atom.var_index;
  switch (rvar->u.atom.exp_base_proc_index->type) {
  case TYPE_LOCAL_IDENTIFIER: 
    rvi = variable_index[TYPE_CLOCK][pi][VAR[rvi].OFFSET];
  }
  rci = VAR[rvi].U.CLOCK.CLOCK_INDEX;
  if (rci == IB_CI)
    return(CLOCK_POS_INFINITY);

/*
  if (lvar->u.atom.indirect_count)
    return(-1);
*/
  lvi = lvar->u.atom.var_index;
  if (lvar->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
    lvi = variable_index[TYPE_CLOCK][pi][VAR[lvi].OFFSET];
  lci = VAR[lvi].U.CLOCK.CLOCK_INDEX;

  if (lci == IB_CI)
    return(0);
  else
    return(-1);
}
/* big_timing_constant_in_action_clock_assign_exp() */




int	get_statement_big_timing_constant(st, pi)
	struct statement_type	*st; 
	int			pi; 
{ 
  int	curc1, curc2, i; 
  
  if (!st) 
    return(CLOCK_NEG_INFINITY); 
    
  switch (st->op) { 
  case ST_IF: 
    curc1 = big_timing_constant_in_CRD(st->u.branch.red_cond[pi]); 
    curc2 = get_statement_big_timing_constant(st->u.branch.if_statement, pi); 
    if (curc2 > curc1) 
      curc1 = curc2; 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      curc2 = get_statement_big_timing_constant(st->u.branch.else_statement, pi); 
      if (curc2 > curc1) 
        curc1 = curc2; 
    } 
    return(curc1); 
    break; 
  case ST_WHILE: 
    curc1 = big_timing_constant_in_CRD(st->u.loop.red_cond[pi]); 
    curc2 = get_statement_big_timing_constant(st->u.loop.statement, pi); 
    if (curc2 > curc1) 
      curc1 = curc2; 
    return(curc1); 
    break; 
  case ST_SEQ: 
    curc1 = CLOCK_NEG_INFINITY; 
    for (i = st->u.seq.count-1; i>=0; i--) { 
      curc2 = get_statement_big_timing_constant(st->u.seq.statement[i], pi); 
      if (curc2 > curc1) 
        curc1 = curc2; 
    } 
    return(curc1); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
  case ST_CPLUG: 
    return(CLOCK_NEG_INFINITY); 
    break; 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
    curc1 = big_timing_constant_in_action_clock_assign_constant(pi, st);
    return(curc1); 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    curc1 = big_timing_constant_in_action_clock_assign_exp(pi, st);
    return(curc1); 

  default: 
    return(CLOCK_NEG_INFINITY); 
    break; 	
  } 
}
  /* get_statement_big_timing_constant() */
  
  
  

int	count_mode_clock_bound_analysis = 0; 

void	mode_clock_bound_analysis() {
  int 			mi, ci, cvi, pi, mvi, lci, lcvi, imi, mv, chi,
			flag_change, ixi, curc, one_curc, ai;
  struct red_type	*d;

  if (CLOCK_COUNT == 0) 
    return; 
    
  /* claim the memory */
  for (mi = 0; mi < MODE_COUNT; mi++) {
    MODE[mi].bound = (int *) malloc(CLOCK_COUNT*sizeof(int));
    MODE[mi].bound[0] = CLOCK_POS_INFINITY;
  }
  /* initialize the bound for global clocks */
  for (ci = 0; ci < GLOBAL_COUNT[TYPE_CLOCK]; ci++) {
    cvi = variable_index[TYPE_CLOCK][0][ci];
    for (mi = 0; mi < MODE_COUNT; mi++) {
      MODE[mi].bound[VAR[cvi].U.CLOCK.CLOCK_INDEX] = CLOCK_POS_INFINITY;
    }
  }
  /* initialize the bound for local clocks */
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    mvi = variable_index[TYPE_DISCRETE][pi][OFFSET_MODE];
    for (lci=0; lci < LOCAL_COUNT[TYPE_CLOCK]; lci++) {
      lcvi = variable_index[TYPE_CLOCK][pi][lci];
      ci = VAR[lcvi].U.CLOCK.CLOCK_INDEX;
      d = VAR[lcvi].RED_ACTIVE;
      if (d->var_index != mvi) {
	for (mi = 0; mi < MODE_COUNT; mi++)
	  MODE[mi].bound[ci] = 0;
	for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++)
	  MODE[PROCESS[pi].reachable_mode[imi]].bound[ci] = CLOCK_POS_INFINITY;
      }
      else {
	for (mv = VAR[mvi].U.DISC.LB; mv <= VAR[mvi].U.DISC.UB; mv++)
          MODE[mv].bound[ci] = 0;
/*
	for (chi = 0; chi < d->u.ddd.child_count; chi++)
	  for (mi = d->u.ddd.arc[chi].lower_bound; mi <= d->u.ddd.arc[chi].upper_bound; mi++)
	    MODE[mi].bound[ci] = CLOCK_POS_INFINITY;
*/
      }
    }
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (lci = 0; lci < LOCAL_COUNT[TYPE_CLOCK]; lci++) {
      IB_CVI = variable_index[TYPE_CLOCK][pi][lci];
      IB_CI = VAR[IB_CVI].U.CLOCK.CLOCK_INDEX;
      for (flag_change = TYPE_TRUE; flag_change == TYPE_TRUE; ) {
        flag_change = TYPE_FALSE;
	for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
	  mi = PROCESS[pi].reachable_mode[imi];
	  curc = big_timing_constant_in_CRD(MODE[mi].invariance[pi].red);
	  if (curc > MODE[mi].bound[IB_CI]) {
	    MODE[mi].bound[IB_CI] = curc;
	    flag_change = TYPE_TRUE;
	  }
	  for (ixi = 0; ixi < MODE[mi].xtion_count; ixi++) {
	    if (!(IB_XI = MODE[mi].xtion[ixi])) 
	      continue;
	    curc = big_timing_constant_in_CRD(XTION[IB_XI].red_trigger[pi]);
	    if (curc > MODE[mi].bound[IB_CI]) {
	      MODE[mi].bound[IB_CI] = curc;
	      flag_change = TYPE_TRUE;
	    } 
	    curc = get_statement_big_timing_constant(XTION[IB_XI].statement, pi); 
	    if (curc < 0) { 
/*
	      fprintf(RED_OUT, 
	        "\n****(%1d: mode clock bound analysis()****\n", 
	        ++count_mode_clock_bound_analysis 
	      ); 
	      fprintf(RED_OUT, "MODE[mi=%1d:%s].bound[IB_CI=%1d]=%1d\n", 
	        mi, MODE[mi].name, 
	        IB_CI, MODE[mi].bound[IB_CI]
	      ); 
	      if (valid_mode_index(XTION[IB_XI].dst_mode_index)) { 
	      	fprintf(RED_OUT, "XTION[IB_XI=%1d].dst_mode_index=%1d\n", 
	          IB_XI, XTION[IB_XI].dst_mode_index
	        ); 
	        fprintf(RED_OUT, 
	          "MODE[XTION[IB_XI=%1d].dst_mode_index=%1d].bound[IB_CI=%1d]=%1d\n", 
	          IB_XI, XTION[IB_XI].dst_mode_index, 
	          IB_CI, MODE[XTION[IB_XI].dst_mode_index].bound[IB_CI]
	        ); 
	      }
	      fflush(RED_OUT); 
*/	      
	      if (   valid_mode_index(XTION[IB_XI].dst_mode_index) 
	          && MODE[mi].bound[IB_CI] 
	             < MODE[XTION[IB_XI].dst_mode_index].bound[IB_CI] 
	          ) {
                MODE[mi].bound[IB_CI] 
                = MODE[XTION[IB_XI].dst_mode_index].bound[IB_CI];
                flag_change = TYPE_TRUE;
	      }
	      else if (   XTION[IB_XI].dst_mode_index == MODE_DYNAMIC
	               && MODE[mi].bound[IB_CI] < CLOCK_POS_INFINITY
	               ) {
                MODE[mi].bound[IB_CI] = CLOCK_POS_INFINITY;
                flag_change = TYPE_TRUE;
	      }
	    }
	    else if (curc > MODE[mi].bound[IB_CI]) {
	      MODE[mi].bound[IB_CI] = curc;
	      flag_change = TYPE_TRUE;
	    }
	  }
	}
      }
    }
  }
/*
  fprintf(RED_OUT, "MODE clock bound analysis:\n");
  for (mi = 0; mi < MODE_COUNT; mi++) {
    fprintf(RED_OUT, "\nMODE %1d:%s: ", mi, MODE[mi].name);
    for (ci = 0; ci < CLOCK_COUNT; ci++) {
      fprintf(RED_OUT, "%1d[%s:%1d] ", ci, VAR[CLOCK[ci]].NAME, MODE[mi].bound[ci]);
    }
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
  }
*/
}
/* mode_clock_bound_analysis() */



/*
test_hybrid_ineq() {
  struct ps_exp_type 	*ineq;
  struct red_type	*result, *conj;

  ineq = ps_exp_alloc(LESS);
  ineq->u.ineq.term_count = 5;
  ineq->u.ineq.term = (struct parse_term_type *)
	malloc(ineq->u.ineq.term_count * sizeof(struct parse_term_type));
  ineq->u.ineq.term[0].operand = exp_atom(TYPE_CLOCK,-1,"x");
  ineq->u.ineq.term[0].coeff 
  = exp_binary(ARITH_ADD, exp_atom(TYPE_LOCAL_IDENTIFIER, 0, NULL),
	exp_binary(ARITH_ADD , exp_atom(TYPE_CONSTANT, -3,NULL))
  );
  ineq->u.ineq.term[1].operand = exp_atom(TYPE_DENSE,0,"y");
  ineq->u.ineq.term[1].coeff = exp_binary(ARITH_ADD, exp_atom(TYPE_CONSTANT, 3, NULL),
					  exp_binary(ARITH_DIVIDE , exp_atom(TYPE_CONSTANT, -7,NULL))
					  );
  ineq->u.ineq.term[2].operand = exp_atom(TYPE_CLOCK,0,"z");
  ineq->u.ineq.term[2].coeff = exp_binary(ARITH_ADD, exp_atom(TYPE_CONSTANT, 7, NULL),
					  exp_binary(ARITH_DIVIDE , exp_atom(TYPE_CONSTANT, -3,NULL))
					  );
  ineq->u.ineq.term[3].operand = exp_atom(TYPE_DENSE,0,"h");
  ineq->u.ineq.term[3].coeff = exp_binary(ARITH_ADD, exp_atom(TYPE_CONSTANT, 4, NULL),
					  exp_binary(ARITH_ADD , exp_atom(TYPE_CONSTANT, 9,NULL))
					  );
  ineq->u.ineq.term[4].operand = exp_atom(TYPE_DENSE,0,"i");
  ineq->u.ineq.term[4].coeff = exp_binary(ARITH_ADD, exp_atom(TYPE_CONSTANT, 5, NULL),
					  exp_binary(ARITH_DIVIDE , exp_atom(TYPE_CONSTANT, -3,NULL))
					  );
  //ineq->u.ineq.offset.operand =  exp_atom(TYPE_CLOCK,0,"j");
  ineq->u.ineq.offset = exp_binary(ARITH_ADD, exp_atom(TYPE_CONSTANT, 5, NULL),
				   exp_binary(ARITH_DIVIDE , exp_atom(TYPE_CONSTANT, 2 ,NULL))
				   );

  fprintf(RED_OUT, "test parse hybrid inequality:\n");
  print_parse_subformula(ineq, FLAG_GENERAL_PROCESS_IDENTIFIER);
  fprintf(RED_OUT, "\ntest red hybrid at process 1:\n");
  red_print_graph(red_local(ineq, 1, 0));
  fprintf(RED_OUT, "\ntest red hybrid at process 2:\n");
  red_print_graph(red_local(ineq, 2, 0));
  fprintf(RED_OUT, "\ntest red hybrid at process 3:\n");
  red_print_graph(red_local(ineq, 3, 0));

//Edit 12/20



  exit(0);
}
*/
  /* test_hybrid_ineq() */




  
  
void 	debug_process2() { 
  int	i, j, result, subresult, start, stop;
    
  fprintf(RED_OUT, "\n%1d rules:\n", DEBUG_RED_COUNT); 
  DEBUG_RED = (struct red_type **) malloc(DEBUG_RED_COUNT * sizeof(struct red_type *));
  for (i = 0; i < DEBUG_RED_COUNT; i++) {
    struct ps_exp_type	*texp;

    texp = spec_global(PARSE_DEBUG_EXP[i], 0, FLAG_LAZY_EVALUATION, 0);
    fprintf(RED_OUT, "*****************************************\nPARSE_DEBUG_EXP[%1d]:\n", i);
    pcform(PARSE_DEBUG_EXP[i]);

    DEBUG_RED[i] = texp->u.rpred.red;
    free(texp);
    red_mark(DEBUG_RED[i], FLAG_GC_STABLE);
    fprintf(RED_OUT, "\nDEBUG_RED[%1d]:\n", i); 
    red_print_graph(DEBUG_RED[i]); 
  }
  RT[result = RT_TOP++] = NORM_NO_RESTRICTION; 

  for (start = 0, j = 0; j < 4; j++) { 
    if (j == 3) 
      stop = DEBUG_RED_COUNT; 
    else 
      stop = start + DEBUG_RED_COUNT/4; 
    RT[subresult = RT_TOP++] = NORM_NO_RESTRICTION; 
    for (i = start; i < stop; i++) {
      fprintf(RED_OUT, "\n**********************************\nDEBUG_RED[%1d]:\n", i); 
      fflush(RED_OUT); 
      red_print_graph(DEBUG_RED[i]); 
      RT[subresult] = red_bop(INTERSECT, RT[subresult], DEBUG_RED[i]);
      garbage_collect(FLAG_GC_SILENT);
      fprintf(RED_OUT, "\nresult after iteration %1d:\n", i); 
      red_print_graph(RT[subresult]); 
    } 
    start = stop; 
    RT[result] = red_bop(INTERSECT, RT[result], RT[subresult]); 
    RT_TOP--; /* subresult */ 
  }
  fprintf(RED_OUT, "\nresult after the final iteration\n"); 
  red_print_graph(RT[result]);  
  RT_TOP--; /* result */ 
  exit(0); 
	
}
  /* debug_process2() */ 
  
  
    
  
void 	debug_process() { 
  int	i, result;
    
  fprintf(RED_OUT, "\n%1d rules:\n", DEBUG_RED_COUNT); 
  DEBUG_RED = (struct red_type **) malloc(DEBUG_RED_COUNT * sizeof(struct red_type *));
  for (i = 0; i < DEBUG_RED_COUNT; i++) {
    struct ps_exp_type	*texp;

    texp = spec_global(PARSE_DEBUG_EXP[i], 0, FLAG_LAZY_EVALUATION, 0);
    fprintf(RED_OUT, "*****************************************\nPARSE_DEBUG_EXP[%1d]:\n", i);
    pcform(PARSE_DEBUG_EXP[i]);

    DEBUG_RED[i] = texp->u.rpred.red;
    free(texp);
    red_mark(DEBUG_RED[i], FLAG_GC_STABLE);
    fprintf(RED_OUT, "\nDEBUG_RED[%1d]:\n", i); 
    red_print_graph(DEBUG_RED[i]); 
  }
  RT[result = RT_TOP++] = NORM_NO_RESTRICTION; 

  for (i = 0; i < DEBUG_RED_COUNT; i++) {
    fprintf(RED_OUT, "\n**********************************\nDEBUG_RED[%1d]:\n", i); 
    fflush(RED_OUT); 
//    red_print_graph(DEBUG_RED[i]); 
    RT[result] = red_bop(INTERSECT, RT[result], DEBUG_RED[i]);
    garbage_collect(FLAG_GC_SILENT);
//    fprintf(RED_OUT, "\nresult after iteration %1d:\n", i); 
//    red_print_graph(RT[result]); 
  } 
  fprintf(RED_OUT, "\nresult after the final iteration\n"); 
  red_print_graph(RT[result]);  
  RT_TOP--; /* result */ 
  exit(0); 
	
}
  /* debug_process() */ 
  
  
  
  
/*********************************************************************
 *
 * The input processing routine.
 */
parse_mode_xtion_system_spec() { 
  int	i, vi, pi, vin; 

  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_BRANCHING_BISIM_CHECKING: 
  case TASK_BRANCHING_SIM_CHECKING: 
    /* Greatest fixpoint task
     */ 
    SPEC_EXP->type = RED; 
    SPEC_EXP->u.rpred.red = NORM_NO_RESTRICTION; 
    init_inactive_management();
    RT[INDEX_INITIAL] = red_hull_normalize(INDEX_INITIAL); 
    RT[INDEX_INITIAL] = inactive_variable_eliminate(INDEX_INITIAL); 
    red_mark(RT[INDEX_INITIAL], FLAG_GC_STABLE);

    mode_clock_bound_analysis();

    GSTATUS[INDEX_NORM_ZONE] 
    = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
    | FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE; 
/*
    fprintf(RED_OUT, "\nThe mode restriction with invariance:\n"); 
    red_print_graph(RT[DECLARED_GLOBAL_INVARIANCE]); 
*/
    
    break; 
  case TASK_DEADLOCK: 
  case TASK_ZENO: 
/*
    print_cpu_time("before inactive management");
*/
    init_inactive_management();
    RT[INDEX_INITIAL] = red_hull_normalize(INDEX_INITIAL); 
    RT[INDEX_INITIAL] = inactive_variable_eliminate(INDEX_INITIAL); 
    red_mark(RT[INDEX_INITIAL], FLAG_GC_STABLE);
    
    mode_clock_bound_analysis();

    break; 
    
  default: 
    // Changes on 081215: 
    // Shorthand_analysis() was moved from redgram.y, the parser, 
    // to here.  
    // The reason is for better analysis of TCTCTL formulas. 
    // In redgram.y, we may not have the variable table ready and 
    // could not construct CRD+MDD for the analysis of location disjoint 
    // spaces.  
    // Here, the variable table is ready and we can build the CRD+MDD 
    // for easy analysis of location disjoint. 
    // 
    if (PARSE_SPEC == NULL) { 
      fprintf(RED_OUT, "\nError: PARSE_SPEC should at least be of type TRUE\n"); 
      fprintf(RED_OUT, "       at this stage.\n"); 
      fflush(RED_OUT); 
      exit(0); 
    }  
    SPEC_EXP = analyze_tctl(PARSE_SPEC, 0, TYPE_TRUE); 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_GOAL: 
    case TASK_RISK:
    case TASK_SAFETY: 
    case TASK_SIMULATE: 
    case TASK_REDLIB_SESSION: 
      RT[INDEX_GOAL] = SPEC_EXP->u.rpred.red; 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "\nAfter spec_global()\n"); 
      red_print_graph(RT[INDEX_GOAL]); 
      #endif 
      break; 
    default: 
      #ifdef RED_DEBUG_PARSE_MODE 
      fprintf(RED_OUT, "after changing event counts of the tctl spec.\n"); 
      pcform(SPEC_EXP); 
      #endif 
      RT[INDEX_GOAL] = NORM_FALSE; 
      break; 
    }

    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after analyze tctctl of the spec");
    fprintf(RED_OUT, "\nThe negated parse spec after spec global analysis.\n");
    print_parse_subformula_structure(SPEC_EXP, 0);
    #endif 
    
    init_inactive_management();
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after init inactive management");
    #endif 
    
    RT[INDEX_INITIAL] = red_hull_normalize(INDEX_INITIAL); 
    RT[INDEX_INITIAL] = inactive_variable_eliminate(INDEX_INITIAL); 
    red_mark(RT[INDEX_INITIAL], FLAG_GC_STABLE);
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after inactive variable eliminate of the initial condition");
    #endif 

    mode_clock_bound_analysis();
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after mode clock bound analysis");
    fprintf(RED_OUT, "\nThe diagram for the initial condition:\n"); 
    red_print_graph(RT[INDEX_INITIAL]); 
/*
  print_cpu_time("after inactive management");
*/
    #endif 

    if (GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY) {
      for (vi = 4; vi < VARIABLE_COUNT; vi++) {
        if (VAR[vi].PROC_INDEX && (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)) {
	  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
	    vin = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
  	    VAR[vin].STATUS = VAR[vin].STATUS | FLAG_SPEC_REFERENCED;
	  }
        }
      }
    }

    if (SPEC_EXP->type != RED)
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_GOAL) {
        fprintf(RED_OUT, "\nModal formulus is not compatible with GOAL reachability analysis.\n");
        fflush(RED_OUT);
        exit(0);
      }
      else if ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_RISK)  {
        fprintf(RED_OUT, "\nModal formulus is not compatible with RISK reachability analysis.\n");
        fflush(RED_OUT);
        exit(0);
      }
/*
    fprintf(RED_OUT, "\n\nNegated SPEC_EXP:\n");
    print_parse_subformula(SPEC_EXP, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n\n"); 
    if (SPEC_EXP->type == RED) 
      red_print_graph(SPEC_EXP->u.rpred.red); 
    fprintf(RED_OUT, "\n");
    fflush(RED_OUT);
    exit(0);
    */
    sig_process_analyze();
  }

/*

  fprintf(RED_OUT, "\nXTION's processes:\n");
  for (xi = 0; xi < XTION_COUNT; xi++) {
    fprintf(RED_OUT, "X%1d:%1d:", xi, XTION[xi].process_count);
    for (pi = 0; pi < XTION[xi].process_count; pi++) {
      fprintf(RED_OUT, "{%1d}", XTION[xi].process[pi]);
    }
    fprintf(RED_OUT, "\n");
  }
  fprintf(RED_OUT, "\n");
*/
/*
  print_cpu_time("after firable management");
  print_processes();
*/
} 
  /* parse_mode_xtion_system_spec() */ 
  



/************************************************************
* How do we handle the many cases of model and spec input. 
*
* 1. In the packaged usage of red, 
*      flag_task != TASK_REDLIB_SESSION, 
*    we expect model_file_name and spec_file_name both non-null. 
* 2. In the relib usage, 
*      flag_task == TASK_REDLIB_SESSION, 
*    we expect model_file_name to be non-null. 
*    We skip the checking of spec_file_name.  
*/

void 	parse_input_model(char *model_file_name) { 
//  test_float(); 

  if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
      == FLAG_MODEL_PARSING_ONLY
      ) {  
    int	ti; 
    
    GLOBAL_COUNT = ((int *) malloc((TYPE_QSYNC_HOLDER-TYPE_SYNCHRONIZER+1)
      * sizeof(int)
    ) ) - TYPE_SYNCHRONIZER; 
    LOCAL_COUNT = ((int *) malloc((TYPE_QSYNC_HOLDER-TYPE_SYNCHRONIZER+1)
      * sizeof(int)
    ) ) - TYPE_SYNCHRONIZER; 
    for (ti = TYPE_SYNCHRONIZER; ti <= TYPE_QSYNC_HOLDER; ti++) {
      GLOBAL_COUNT[ti] = 0; 
      LOCAL_COUNT[ti] = 0; 
    } 

    declare_global_synchronizer_list = NULL;
    declare_global_dense_list = NULL;
    declare_global_clock_list = NULL;
    declare_global_discrete_list = NULL;
    declare_global_pointer_list = NULL;

    declare_local_synchronizer_list = NULL; 
    declare_local_dense_list = NULL; 
    declare_local_clock_list = NULL; 
    declare_local_discrete_list = NULL; 
    declare_local_pointer_list = NULL; 

    declare_global_rel_count = 0;
    declare_spec_rel_count = 0;

    declare_global_rel_clock_count = 0;
    declare_spec_rel_clock_count = 0;

    declare_global_rel_discrete_count = 0;
    declare_spec_rel_discrete_count = 0;
  }

  redlibin = stdin;
  model_file_name = file_include(model_file_name); 
  model_file_name = macro_eliminate(model_file_name); 
  
  if ((redlibin = fopen(model_file_name, "r")) == NULL) {
    printf("Can not open model template file %s.\n", model_file_name);
    exit(1);
  }
  else {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
      declare_inline_exp_list = NULL;
      declare_inline_exp_count = 0; 
    } 
    init_exp_pre_management(); 
    flag_redlib_input_source = FLAG_INPUT_FILE; 
    redlibrestart(redlibin); 
    redlibparse(); /* calling the parser constructed out of the yacc rules. */ 
    fclose(redlibin); 
  } 
  
  if (TYPE_PARSE_CHOICE != TYPE_PARSE_MODE_XTION_SYSTEM) { 
    fprintf(RED_OUT, "Error: Illegal parsing result \n"); 
    fprintf(RED_OUT, "       when a mode transition is expected.\n"); 
    exit(0);  
  } 
}
  /* parse_input_model() */  






// struct red_type	*dt1, *dt2; 

void	parse_system_description(
  char	*model_file_name,  
  char	*output_file_name, 
  int	process_count, 
  int	flag_task  
) {
  int				i, j, k, argvbnd, xi;
  int				ci, cj, fi, fsi, pi, pin, vi, vin, flag_overflow, VAR_size;
  struct red_type		*disj, *conj;
  struct parse_xtion_type	*px;
  struct parse_assignment_type	*pt, *ptt;

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("entering parse system description\n"); 
  #endif

  if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
    init_23tree_management();
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after init 23tree management\n"); 
    #endif

    init_hash_management(); 
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after init hash management\n"); 
    #endif

    ITERATION_COUNT = -1;

    /* The first pass parsing. */
    VAR = NULL;  /* This is for the safe-gaurding of print_parse_xtion() */
    GSYNC = NULL; 
    
    if (process_count != -1) { 
      GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
      = GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
      | FLAG_TEMPLATE_PROCESS_COUNT_OVERRIDDEN; 
      PROCESS_COUNT = process_count; 
    }
  } 

/*
  if (GSTATUS[INDEX_PARSE] & FLAG_PARSER_FULL_MODEL) 
  else 
*/
  parse_input_model(model_file_name); 
  
  if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
      == FLAG_MODEL_PARSING_ONLY
      ) { 
    return; 
  } 
  
/*  fprintf(RED_OUT, "End 1 of model input for PC=%1d.\n", PROCESS_COUNT); 
  fflush(RED_OUT); 
//  fclose(redlibin); // I think it is closed in redlibwrap(). 
*/
  GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
    		      | (MASK_TASK & TASK_REDLIB_SESSION); 
  PARSE_SPEC = ps_exp_alloc(TYPE_TRUE); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after null spec.\n"); 
  #endif

  check_options();
  
  if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
    variable_fillin();
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after variable fillin.\n"); 
    #endif
  } 
  else { 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      vi = variable_index[TYPE_DISCRETE][pi][OFFSET_MODE]; 
      VAR[vi+1].U.DISC.LB = VAR[vi].U.DISC.LB = 0; 
      VAR[vi+1].U.DISC.UB = VAR[vi].U.DISC.UB = MODE_COUNT-1; 
      
      vi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
      VAR[vi].U.DISC.LB = 0; 
      VAR[vi].U.DISC.UB = declare_xtion_count-1; 
    } 	
  } 

  gsync_fillin(); 

  if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
    init_red_management(); 
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after red management.\n"); 
    #endif
  }
  init_garbage_management();
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after init garbage colleciton.\n"); 
  #endif

  RT[INDEX_INITIAL] = NULL;
  RED_INVARIANCE = NULL;

  init_hybrid_management();

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after initializing hybrid management");
  #endif

  if ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_MODEL_CHECK) {
    if (!(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)) {
      GSTATUS[INDEX_INFERENCE_DIRECTION] = GSTATUS[INDEX_INFERENCE_DIRECTION] | FLAG_BCK_ANALYSIS;
      fprintf(RED_OUT, "\nForward analysis option overridden for model-checking task.\n");
    }
  }

  if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
      && ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_MODEL_CHECK)
      ) {
    fprintf(RED_OUT, "\nCounter example option overridden in model-checking task.\n");
  }

  mode_fillin();
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after mode_fillin");
  #endif

  xtion_fillin(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after xtion_fillin"); 
//  print_gsyncs(); 
  print_xtions(); 
  #endif

  init_counter_example_management();
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("init_counter_example_management");
  #endif

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nThe parse initial before parsing.\n");
  #endif
/*
  print_parse_subformula_structure(PARSE_INITIAL_EXP, 0);
  fflush(RED_OUT);
  test_hybrid_ineq();
*/
  PARSE_INITIAL_EXP = analyze_tctl(
    PARSE_INITIAL_EXP, FLAG_ANALYZE_INITIAL, 0
  ); 
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nyacc global: After analyze_tctl\nInitial:\n");
  pcform(PARSE_INITIAL_EXP); 
//  print_parse_subformula_structure(PARSE_INITIAL_EXP, 0);
  fflush(RED_OUT);
  #endif 
  if (PARSE_INITIAL_EXP->type != RED) {
    fprintf(RED_OUT, "\nError: An initial condition with modal operators. \n");
    exit(0);
  }
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after translating the initial condition to the diagram");
  fprintf(RED_OUT, "\nThe parse initial after parsing.\n");
  pcform(PARSE_INITIAL_EXP);
  #endif

  RT[INDEX_INITIAL] = PARSE_INITIAL_EXP->u.rpred.red;
  if (DEPTH_CALL > 0) 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      RT[INDEX_INITIAL] = ddd_one_constraint(RT[INDEX_INITIAL], 
        variable_index[TYPE_DISCRETE][pi][OFFSET__SP], 0, 0
      ); 
  red_mark(RT[INDEX_INITIAL], FLAG_GC_STABLE);
  garbage_collect(FLAG_GC_SILENT); 

  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nThe initial red:\n");
  red_print_graph(RT[INDEX_INITIAL]);
  fflush(RED_OUT);
  #endif

/*
  print_cpu_time("after processing spec");
  fprintf(RED_OUT, "\nThe parse spec after parsing.\n");
  print_parse_subformula_structure(PARSE_SPEC, 0);

  fprintf(RED_OUT, "\nBefore process_fillin()\n"); 
*/
  PROCESS_fillin(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after process fillin");
  print_modes(); 
  print_xtions(); 
  #endif

  red_invariance();
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after red invariance");
  #endif
/*
  fflush(RED_OUT);
*/
  init_zone_management();
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after init zone management");
  #endif

  init_fxp_management();   
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("XTIONs, after init_fxp_management()");
  print_xtions();
  #endif

  xtion_1st_reduce(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("XTIONs, after the 1st reduction");
  print_xtions();
  #endif

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED) {
    local_clock_bound_analysis();
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("after local clock bound analysis");
    fflush(RED_OUT);
    #endif
  }
  MAX_GSYNC_COUNT = 2*PROCESS_COUNT;
  /*
  fprintf(RED_OUT, "\nbefore filter_sync_xi_restriction, RT_TOP=%1d\n", RT_TOP);
  Why we have to put filter_sync_xi_restriction before the constrution of 
  spec_exp ?  

  fprintf(RED_OUT, "Before filter sync\n"); 
  report_red_management(); 
  */
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("fxi_res: before filter_sync_xi_restriction()");
//  report_red_management(); 
  #endif   
  filter_sync_xi_restriction();
  analyze_clock_lubs(); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("after fxi restriciton");
  fprintf(RED_OUT, "After filter sync\n"); 
  report_red_management(); 
  print_xtions();
  print_sync_xtions("After filter sync", SYNC_XTION, SYNC_XTION_COUNT); 
  #endif

  parse_mode_xtion_system_spec(); 

  PEXP_EREACHABLE = ps_exp_alloc(EXISTS_UNTIL);
  PEXP_EREACHABLE->var_status = 0;
  PEXP_EREACHABLE->exp_status = 0;
  PEXP_EREACHABLE->u.mexp.strong_fairness_count = 0;
  PEXP_EREACHABLE->u.mexp.strong_fairness_list = NULL;
  PEXP_EREACHABLE->u.mexp.weak_fairness_count = 0;
  PEXP_EREACHABLE->u.mexp.weak_fairness_list = NULL;
  PEXP_EREACHABLE->u.mexp.path_child = NULL;
  PEXP_EREACHABLE->u.mexp.dest_child = NULL;
  PEXP_EREACHABLE->u.mexp.time_lb = 0;
  PEXP_EREACHABLE->u.mexp.time_ub = CLOCK_POS_INFINITY;
 
  parse_symmetry();
  
  if (GSTATUS[INDEX_EXIT] & FLAG_EXIT_AFTER_QUOTIENT) 
    exit(0); 
  fprintf(RED_OUT, 
    "\n** Model parsing for file %s completed.\n", model_file_name
  ); 
  /*
  if (PROCESS_COUNT == 10) {
    fprintf(RED_OUT, "\nred_big_frac(3, 5):\n");
    red_print_graph(red_big_frac(3, 5));
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nred_big_frac(1, 3)\n");
    red_print_graph(red_big_frac(1, 3));
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nred_big_frac(3, 3):\n");
    red_print_graph(red_big_frac(3, 3));
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nint_boundary(1, 3)\n");
    red_print_graph(int_boundary(1, 3));
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nint_boundary(3, 6)\n");
    red_print_graph(int_boundary(3, 6));
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nint_boundary(5, 5)\n");
    red_print_graph(int_boundary(5, 5));
    fflush(RED_OUT);

    fflush(RED_OUT);
    exit(10);
  }
  */
}
/* parse_system_description() */








