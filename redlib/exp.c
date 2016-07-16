#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include <limits.h> 


#include "redbasics.h"  
#include "redbasics.e"  
#include "redgram.e"  

#include "vindex.e"  

#include "redbop.h"  
#include "redbop.e"  

#include "zone.h"  
#include "zone.e"  

#include "redparse.h"  
#include "redparse.e" 

#include "tctctl.e" 

#include "access_analysis.e" 

#include "bisim.e" 

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

#define THRESHOLD_LAZY_SIZE	100 

#define FLAG_DELAYED_EVALUATION	1
#define FLAG_LAZY_EVALUATION	0

#define	FLAG_XVI_TIME_ELIMINATE		-1 
#define	FLAG_XVI_QSYNC_ELIMINATE	-2 
#define	FLAG_XVI_CLOCK_LOWER_EXTEND	-3 
#define	FLAG_XVI_CLOCK_UPPER_EXTEND	-4 
#define	FLAG_XVI_LOCAL_ELIMINATE	-5 

#define DISP_PROJECT_VAR_SIM		100000

#define VSIM_TYPE(vi)	(vi%DISP_PROJECT_VAR_SIM) 
#define VSIM_OFFSET(vi)	(vi/DISP_PROJECT_VAR_SIM) 

int	FLAG_POLICY_EVALUATION; 
int	W_PI; 
int	COUNT_DD_BLOWUP = 0; 

struct a23tree_type	*EXP_TREE; 
struct ps_exp_type	*PS_EXP_TRUE, 
			*PS_EXP_FALSE, 
			*PS_EXP_LOCAL_IDENTIFIER = NULL, 
			*PS_EXP_GLOBAL_IDENTIFIER, 
			*PS_EXP_MODE, 
			*PS_EXP__SP, 
			*PS_EXP__SP_PLUS, 
			*PS_EXP__SP_MINUS, 
			*PS_EXP__RETMODE, 
			*PS_EXP_ONE, 
			*PS_EXP_NEG_ONE, 
			*PS_EXP_ZERO; 

struct ps_exp_type	*tmp_exp_comp, *target_exp, *target_exp2; 
struct ps_bunit_type	*tmp_bunit_comp, *tmp_bunit_comp2; 

int
  LAZY_PI; 

struct red_type	
  *RED_LAZY_SPACE; 

struct a23tree_type 
  *delayed_eval_tree; 

struct ps_exp_type	*exp_arith(
  int 			, // op, 
  struct ps_exp_type	*, // *lhs, 
  struct ps_exp_type	*  // *rhs 
); 

struct red_type	
  *lazy_one_constraint(
    struct red_type	*, // *d, 
    int			, // pi, 
    struct ps_exp_type	* // *lazy_exp
  ),  
  *lazy_one_neg_constraint(
    struct red_type	*, // *d, 
    int			, // pi, 
    struct ps_exp_type	* // *lazy_exp
  ); 



int	flt_ceil(float v) { 
  int	i; 

  i = v; 
  if (i < v) 
    return(i+1); 
  else 
    return(i); 
} 
  /* flt_ceil() */ 
  
  
int	flt_floor(float v) { 
  int	i; 
  i = v; 
  if (i > v) 
    return(i-1); 
  else 
    return(i); 
} 
  /* flt_floor() */ 
  

int	dble_ceil(double v) { 
  int	i; 

  i = v; 
  if (i < v) 
    return(i+1); 
  else 
    return(i); 
} 
  /* dble_ceil() */ 


int	dble_floor(double v) { 
  int	i; 
  i = v; 
  if (i > v) 
    return(i-1); 
  else 
    return(i); 
} 
  /* dble_floor() */ 
  

/*****************************************************
 *  The following are some forward references to procedures.  
 */ 
 
struct ps_exp_type	*ps_exp_alloc(
  int	// type 
); 

int	ps_exp_free(
  struct ps_exp_type	* // *psub
); 

struct ps_exp_type	*ps_exp_share(
  struct ps_exp_type	* // *psub
);

struct red_type	*rec_discrete_value( 
  struct ps_exp_type	* // *psub 
); 

struct red_type	*red_discrete_value(
  int			, // pi, 
  struct ps_exp_type	* // *psub
); 

struct ps_exp_type	*rewrite_modal_timing( 
  struct ps_exp_type	* // *psub
); 

struct red_type	*rec_delayed_exp_value(
  struct ps_exp_type	* // *psub 
); 

struct red_type	*red_discrete_ineq(
     struct ps_exp_type	*, // *psub, 
     int		// pi; 
); 


int 
  FLAG_CONTROL_EXP_VALUE,  
  PI_EXP_VALUE; 





int	op_ineq_reverse(op)
{
  switch (op) { 
  case ARITH_EQ : 
  case ARITH_NEQ : 
  case NEQ:
  case EQ: 
    return(op); 

  case ARITH_LEQ :
    return(ARITH_GEQ); 
  case ARITH_LESS :
    return(ARITH_GREATER); 
  case ARITH_GREATER :
    return(ARITH_LESS); 
  case ARITH_GEQ : 
    return(ARITH_LEQ); 

  case LEQ :
    return(GEQ); 
  case LESS :
    return(GREATER); 
  case GREATER :
    return(LESS); 
  case GEQ : 
    return(LEQ); 
  }
}
/* op_ineq_reverse() */ 


int	get_qsync_value_in_sync_xtion(
  int				vi, 
  struct sync_xtion_type	*psx
) { 
  int	ai; 
  
  for (ai = 0; ai < psx->qfd_sync_count; ai++) {
    if (vi == psx->qfd_sync[ai].vi)  
      return(psx->qfd_sync[ai].value); 
  }
  fprintf(RED_OUT, "\nERROR: Illegal quantified sync variable %1d:%s in a sync_xtion:\n", 
    vi, VAR[vi].NAME
  ); 
  bk(0); 
}
  /* get_qsync_value_in_sync_xtion() */ 





#define FLAG_EXP_NO_VALUE	0
#define	FLAG_EXP_SPECIFIC_VALUE	1
#define FLAG_EXP_ANY_VALUE	2 

int 	rec_get_exp_value( 
  struct ps_exp_type 	*exp, 
  int			*flag_ptr 
) {
  int lvalue = 0, rvalue = 0, lflag, rflag, vi;

  switch(exp->type){
  case TYPE_CONSTANT: 
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(exp->u.value); 
  case TYPE_MACRO_CONSTANT: 
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(
      exp->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value
    ); 
  case TYPE_PROCESS_COUNT: 
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(PROCESS_COUNT); 
  case TYPE_MODE_COUNT: 
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(MODE_COUNT); 
  case TYPE_MODE_INDEX: 
    exp->u.mode_index.parse_mode 
    = search_parse_mode(exp->u.mode_index.mode_name); 
    if (exp->u.mode_index.parse_mode == NULL) { 
      fprintf(RED_OUT, "\nError: Undefined mode name %s at line %1d.\n", 
        exp->u.atom.var_name, exp->lineno
      ); 
      bk(0);    
    } 
    return(exp->u.mode_index.value = exp->u.mode_index.parse_mode->index); 
    break; 
  
  case TYPE_REFERENCE: 
    *flag_ptr = FLAG_ANY_VALUE; 
    return(0); 
    break; 
  case TYPE_DEREFERENCE: 
    if (   (   exp->u.exp->type == TYPE_DISCRETE
            || exp->u.exp->type == TYPE_POINTER
            || exp->u.exp->type == TYPE_DENSE
            || exp->u.exp->type == TYPE_CLOCK
            || exp->u.exp->type == TYPE_BDD
            )
//        && (exp->u.exp->u.atom.indirect_count == 0)
        ) { 
      vi = exp->u.exp->u.atom.var_index; 
      if (!(exp->u.exp->u.atom.var->status & FLAG_LOCAL_VARIABLE)) {
      	*flag_ptr = FLAG_SPECIFIC_VALUE; 
      	return(vi); 
      } 
      lvalue = rec_get_exp_value(exp->u.exp->u.atom.exp_base_proc_index, 
        &lflag
      ); 
      if (   lflag == FLAG_SPECIFIC_VALUE
          && lvalue >= 1
          && lvalue <= PROCESS_COUNT
          ) { 
        *flag_ptr = FLAG_SPECIFIC_VALUE; 
      	return(variable_index[VAR[vi].TYPE][lvalue][VAR[vi].OFFSET]); 
      } 
    } 
    *flag_ptr = FLAG_ANY_VALUE; 
    return(0); 
    break; 
  case TYPE_LOCAL_IDENTIFIER: 
    if (PI_EXP_VALUE <= 0) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0);    	
    } 
    else { 
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(PI_EXP_VALUE);
    }
  case TYPE_QFD: 
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(qfd_value(exp->u.atom.var_name)); 
  case TYPE_NULL:
  case TYPE_FALSE:
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(0);
  case TYPE_TRUE:
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(1);
  case TYPE_QSYNC_HOLDER:
    if (PI_EXP_VALUE < 0) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    vi = variable_index[TYPE_QSYNC_HOLDER][PI_EXP_VALUE][exp->u.qsholder.place_index]; 
    
    if (VAR[vi].U.QSHLDR.PI == FLAG_ANY_PROCESS) { 
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    } 
    else {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(VAR[vi].U.QSHLDR.PI); 
    }
    break; 

  case TYPE_POINTER:
  case TYPE_DISCRETE: 
    *flag_ptr = FLAG_ANY_VALUE; 
    return(0); 
    
  case TYPE_CLOCK:
  case TYPE_DENSE:
    fprintf(RED_OUT, "Error: dense variable in address expression is not supported at the moment at line %1d.\n", 
	    lineno
	    ); 
    fflush(RED_OUT); 
    bk(""); 
    exit(0); 
    return(0);
    
  case BIT_NOT: 
    lvalue = rec_get_exp_value(exp->u.exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(~lvalue);

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(bit_op_value(exp->type, lvalue, rvalue));
    }
  case ARITH_ADD: 
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(lvalue + rvalue);
    }
  case ARITH_MINUS:
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(lvalue - rvalue);
    }
  case ARITH_MULTIPLY:
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(lvalue * rvalue);
    }
  case ARITH_DIVIDE:
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else if (rvalue) {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(lvalue / rvalue);
    }
    else {
      fprintf(RED_OUT, "\nParser: Huh ? (parse 1) \n");
      bk(); 
    }
    break; 
  case ARITH_MODULO:
    lvalue = rec_get_exp_value(exp->u.arith.lhs_exp, &lflag);
    if (lflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    rvalue = rec_get_exp_value(exp->u.arith.rhs_exp, &rflag);
    if (rflag == FLAG_ANY_VALUE) {
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    }
    else if (rvalue) {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(lvalue % rvalue);
    }
    else {
      fprintf(RED_OUT, 
        "\nParser: Huh ? (parse 1) \n", exp->type 
      );
      bk(); 
    }
    break; 
  case TYPE_INLINE_CALL: 
    if (exp->u.inline_call.instantiated_exp) 
      return(rec_get_exp_value(exp->u.inline_call.instantiated_exp, flag_ptr)); 
    else 
      return(rec_get_exp_value(
        exp->u.inline_call.inline_declare->u.inline_declare.declare_exp, 
        flag_ptr
      ) ); 

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
/* rec_get_exp_value() */



int	get_exp_value(
  struct ps_exp_type	*psub, 
  int			pi, 
  int			control_flag, 
  int			*result_flag_ptr
) { 
  PI_EXP_VALUE = pi; 
  FLAG_CONTROL_EXP_VALUE = control_flag; 
  return(rec_get_exp_value(psub, result_flag_ptr)); 
}
  /* get_exp_value() */ 
  




int	get_value(psub, pi, flag_ptr) 
  struct ps_exp_type	*psub; 
  int			pi, *flag_ptr; 
{ 
  return(get_exp_value(psub, pi, 0, flag_ptr));  
}
  /* get_value() */ 



int	get_address( 
  struct ps_exp_type	*exp_address,  
  int			pi, 
  int			*flag_ptr
) {
  int	address, flag; 

  if (   (exp_address->exp_status & FLAG_LOCAL_IDENTIFIER) 
      && PROCESS_COUNT >= -1*pi 
      && pi < 0
      ) 
    if (exp_address->type == TYPE_LOCAL_IDENTIFIER) 
      return(-1* pi); 
    else 
      return(FLAG_ANY_PROCESS); 

  address = get_exp_value(exp_address, pi, 0, &flag); 	

  if (flag == FLAG_ANY_VALUE) {
    *flag_ptr = FLAG_ANY_PROCESS; 
    return(0); 
  } 
  else if (address < 1 || address > PROCESS_COUNT) { 
    *flag_ptr = FLAG_ANY_VARIABLE; 
    return(0); 
/* 
    fprintf(RED_OUT, "ERROR: Illegal address valuation %1d from ", address); 
    print_parse_subformula(exp_address, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, " for process %1d at line %1d.\n", pi, lineno); 
    fflush(RED_OUT); 
    bk(""); 
    exit(0); 
*/
  }
  else {
    *flag_ptr = FLAG_SPECIFIC_VALUE; 
    return(address); 
  }
}
  /* get_address() */ 


int	get_vi( 
  struct ps_exp_type	*var,  
  int			pi, 
  int			*flag_ptr
) {
  int	ipi; 

  switch (var->type) { 
  case TYPE_REFERENCE: 
    *flag_ptr = FLAG_ANY_VALUE; 
    return(0); 
  case TYPE_CLOCK: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
  case TYPE_DISCRETE: 
  case TYPE_DENSE: 
/*
    if (var->u.atom.indirect_count > 0) { 
      *flag_ptr = FLAG_ANY_VALUE; 
      return(0); 
    } 
*/
    if (!(VAR[var->u.atom.var_index].STATUS & FLAG_LOCAL_VARIABLE)) {
      *flag_ptr = FLAG_SPECIFIC_VALUE; 
      return(var->u.atom.var_index); 
    }
    ipi = get_value(var->u.atom.exp_base_proc_index, pi, flag_ptr); 
    if (*flag_ptr != FLAG_SPECIFIC_VALUE) { 
      return(0); 
    }
    return(variable_index[var->type]
      [ipi]
      [VAR[var->u.atom.var_index].OFFSET]
    );  
  default: 
    *flag_ptr = FLAG_ANY_VALUE; 
    return(0); 
  } 
}
  /* get_address() */ 




  
  
/* if the return value is > 0, it is a variable index. 
*  if it is in (-VARIABLE_COUNT+1,-1], it is a peer variable index. 
*  if it is in (-VARIABLE_COUNT-LOCAL_VARIABLE_COUNT,-VARIABLE_COUNT], it is the local variable 
*  of such declaration of any processes. 
*  If it is -2*VARIABVLE_COUNT, it is any variable. 
*/

int	get_variable_index(
  struct ps_exp_type	*var, 
  int			wpi
) { 
  int	pi, vi, flag; 
  
  if (wpi < 0) { 
    fprintf(RED_OUT, "\nCaught a negative wpi=%1d\n", wpi); 
    bk(0); 	
  } 
  if (!(var->u.atom.var->status & FLAG_LOCAL_VARIABLE)) {
    vi = variable_index[var->type][0][var->u.atom.var->index]; 
    return(vi); 
  }
/*
  if (var->u.atom.indirect_count) { 
    vi = -VARIABLE_COUNT 
    -1 * variable_index[var->type][1][var->u.atom.var->index];    
  } 
  else { 
*/
    pi = get_address(var->u.atom.exp_base_proc_index, wpi, &flag); 
    if (flag == FLAG_SPECIFIC_VALUE) {
      vi = variable_index[var->type][pi][var->u.atom.var->index];
      if (var->var_status & FLAG_VAR_PRIMED) {
        vi = VAR[vi].PRIMED_VI; 
      }
    }
    else   
      vi = -VARIABLE_COUNT 
      -1 * variable_index[var->type][1][var->u.atom.var->index];
//  } 

  return(vi); 
}
  /* get_variable_index() */ 
  
 


/***********************************************************
 *  Now we have all the procedure definitions in the following. 
 */	

struct dint_type { 
  int	lb, ub; 	
}; 

struct fint_type { 
  float	lb, ub; 
}; 

struct dfint_type { 
  double	lb, ub; 	
}; 


union interval_union_type { 
  struct dint_type	dint; 
  struct fint_type	fint; 
  struct dfint_type	dfint; 	
}; 

struct interval_link_type { 
  union	interval_union_type	u; 
  struct interval_link_type	*next_interval_link; 	
} ; 

struct interval_link_type 	dummy_interval_link; 

struct interval_link_type	*insert_dint_link(
  struct interval_link_type	*list, 
  int				vlb, 
  int				vub, 
  int				lb, 
  int				ub  
//  int				*count_ptr 
) {
  struct interval_link_type	*ii, *ip, *in, *nlist, *ntail; 
  
/* 
  if (*count_ptr < 0) { 
    fprintf(RED_OUT, 
      "\nError: negative list length %1d in insert_interval_link().\n", 
      *count_ptr
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
  else 
*/
  if (lb > ub) { 
    fprintf(RED_OUT, 
      "\nError: inconsistent lb %1d and ub %1d in insert_interval_link().\n", 
      lb, ub
    ); 
    bk(0); 	
  } 
  else if (list == NULL) 
/* 
    if (*count_ptr != 0) { 
      fprintf(RED_OUT, 
        "\nError: positive list length %1d for a NULL list in insert_interval_link().\n", 
        *count_ptr
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else 
*/ {
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.dint.lb = lb; 
      ii->u.dint.ub = ub; 
      ii->next_interval_link = NULL; 
//      *count_ptr = 1; 
      return(ii);     
    }

  dummy_interval_link.next_interval_link = list; 
  dummy_interval_link.u.dint.ub = vlb - 2; 
  ip = &dummy_interval_link; 
  in = list; 
  
  // What is the invariance at the beginning of the loop ? 
  // We assume that at the beginning of each loop, 
  // [lb,ub] is disconnected to ip. 
  // That is, lb > ip->ub + 1. 
  for (; in; ) {
    if (ub < in->u.dint.lb-1) { 
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.dint.lb = lb; 
      ii->u.dint.ub = ub; 
      ip->next_interval_link = ii; 
      ii->next_interval_link = in; 
//      (*count_ptr)++; 
      return(dummy_interval_link.next_interval_link);     
    } 
    else if (lb > in->u.dint.ub + 1) { 
      ip = in; 
      in = in->next_interval_link; 
    } 
    else { 
      if (in->u.dint.lb > lb) 
        in->u.dint.lb = lb; 
      if (in->u.dint.ub >= ub) { 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else if (in->next_interval_link == NULL 
      || in->next_interval_link->u.dint.lb-1 > ub 
      ) { 
      	in->u.dint.ub = ub; 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else { 
      	in->u.dint.ub = in->next_interval_link->u.dint.ub; 
      	ii = in; 
      	in = in->next_interval_link; 
      	ip->next_interval_link = in; 
      	free(ii); 
//      	(*count_ptr)--; 
    } } 
  } 
  ii = (struct interval_link_type *) 
    malloc(sizeof(struct interval_link_type)); 
  ii->u.dint.lb = lb; 
  ii->u.dint.ub = ub; 
  ip->next_interval_link = ii; 
  ii->next_interval_link = NULL; 
//      (*count_ptr)++; 
  return(dummy_interval_link.next_interval_link); 
}
  /* insert_dint_link() */ 
  
  
  
struct interval_link_type	*insert_fint_link(
  struct interval_link_type	*list, 
  float				vlb, 
  float				vub, 
  float				lb, 
  float				ub  
//  int				*count_ptr 
) {
  struct interval_link_type	*ii, *ip, *in, *nlist, *ntail; 
  
/* 
  if (*count_ptr < 0) { 
    fprintf(RED_OUT, 
      "\nError: negative list length %1d in insert_interval_link().\n", 
      *count_ptr
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
  else 
*/
  if (lb > ub) { 
    fprintf(RED_OUT, 
      "\nError: inconsistent lb %f and ub %f in insert_interval_link().\n", 
      lb, ub
    ); 
    bk(0); 	
  } 
  else if (list == NULL) 
/* 
    if (*count_ptr != 0) { 
      fprintf(RED_OUT, 
        "\nError: positive list length %1d for a NULL list in insert_interval_link().\n", 
        *count_ptr
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else 
*/ {
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.fint.lb = lb; 
      ii->u.fint.ub = ub; 
      ii->next_interval_link = NULL; 
//      *count_ptr = 1; 
      return(ii);     
    }

  dummy_interval_link.next_interval_link = list; 
  dummy_interval_link.u.fint.ub = vlb - 2; 
  ip = &dummy_interval_link; 
  in = list; 
  
  // What is the invariance at the beginning of the loop ? 
  // We assume that at the beginning of each loop, 
  // [lb,ub] is disconnected to ip. 
  // That is, lb > ip->ub + 1. 
  for (; in; ) {
    if (ub < feps_minus(in->u.fint.lb)) { 
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.fint.lb = lb; 
      ii->u.fint.ub = ub; 
      ip->next_interval_link = ii; 
      ii->next_interval_link = in; 
//      (*count_ptr)++; 
      return(dummy_interval_link.next_interval_link);     
    } 
    else if (lb > feps_plus(in->u.fint.ub)) { 
      ip = in; 
      in = in->next_interval_link; 
    } 
    else { 
      if (in->u.fint.lb > lb) 
        in->u.fint.lb = lb; 
      if (in->u.fint.ub >= ub) { 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else if (in->next_interval_link == NULL 
      || feps_minus(in->next_interval_link->u.fint.lb) > ub 
      ) { 
      	in->u.fint.ub = ub; 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else { 
      	in->u.fint.ub = in->next_interval_link->u.fint.ub; 
      	ii = in; 
      	in = in->next_interval_link; 
      	ip->next_interval_link = in; 
      	free(ii); 
//      	(*count_ptr)--; 
    } } 
  } 
  ii = (struct interval_link_type *) 
    malloc(sizeof(struct interval_link_type)); 
  ii->u.fint.lb = lb; 
  ii->u.fint.ub = ub; 
  ip->next_interval_link = ii; 
  ii->next_interval_link = NULL; 
//      (*count_ptr)++; 
  return(dummy_interval_link.next_interval_link); 
}
  /* insert_fint_link() */ 
  
  
  
struct interval_link_type	*insert_dfint_link(
  struct interval_link_type	*list, 
  double			vlb, 
  double			vub, 
  double			lb, 
  double			ub  
//  int				*count_ptr 
) {
  struct interval_link_type	*ii, *ip, *in, *nlist, *ntail; 
  
/* 
  if (*count_ptr < 0) { 
    fprintf(RED_OUT, 
      "\nError: negative list length %1d in insert_interval_link().\n", 
      *count_ptr
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
  else 
*/
  if (lb > ub) { 
    fprintf(RED_OUT, 
      "\nError: inconsistent lb %f and ub %f in insert_interval_link().\n", 
      lb, ub
    ); 
    bk(0); 	
  } 
  else if (list == NULL) 
/* 
    if (*count_ptr != 0) { 
      fprintf(RED_OUT, 
        "\nError: positive list length %1d for a NULL list in insert_interval_link().\n", 
        *count_ptr
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else 
*/ {
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.dfint.lb = lb; 
      ii->u.dfint.ub = ub; 
      ii->next_interval_link = NULL; 
//      *count_ptr = 1; 
      return(ii);     
    }

  dummy_interval_link.next_interval_link = list; 
  dummy_interval_link.u.dfint.ub = vlb - 2; 
  ip = &dummy_interval_link; 
  in = list; 
  
  // What is the invariance at the beginning of the loop ? 
  // We assume that at the beginning of each loop, 
  // [lb,ub] is disconnected to ip. 
  // That is, lb > ip->ub + 1. 
  for (; in; ) {
    if (ub < feps_minus(in->u.dfint.lb)) { 
      ii = (struct interval_link_type *) 
        malloc(sizeof(struct interval_link_type)); 
      ii->u.dfint.lb = lb; 
      ii->u.dfint.ub = ub; 
      ip->next_interval_link = ii; 
      ii->next_interval_link = in; 
//      (*count_ptr)++; 
      return(dummy_interval_link.next_interval_link);     
    } 
    else if (lb > feps_plus(in->u.dfint.ub)) { 
      ip = in; 
      in = in->next_interval_link; 
    } 
    else { 
      if (in->u.dfint.lb > lb) 
        in->u.dfint.lb = lb; 
      if (in->u.dfint.ub >= ub) { 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else if (in->next_interval_link == NULL 
      || dfeps_minus(in->next_interval_link->u.dfint.lb) > ub 
      ) { 
      	in->u.dfint.ub = ub; 
      	return (dummy_interval_link.next_interval_link); 
      } 
      else { 
      	in->u.dfint.ub = in->next_interval_link->u.dfint.ub; 
      	ii = in; 
      	in = in->next_interval_link; 
      	ip->next_interval_link = in; 
      	free(ii); 
//      	(*count_ptr)--; 
    } } 
  } 
  ii = (struct interval_link_type *) 
    malloc(sizeof(struct interval_link_type)); 
  ii->u.dfint.lb = lb; 
  ii->u.dfint.ub = ub; 
  ip->next_interval_link = ii; 
  ii->next_interval_link = NULL; 
//      (*count_ptr)++; 
  return(dummy_interval_link.next_interval_link); 
}
  /* insert_dfint_link() */ 
  
  
  
inline void	free_interval_list(
  struct interval_link_type	*list
) { 
  struct interval_link_type	*ii; 
  
  for (; list; ) { 
    ii = list; 
    list = list->next_interval_link; 
    free(ii);   	
  } 
}
  /* free_interval_list() */ 


struct interval_link_type
  ****GLOBAL_INTERVAL_LIST; 

int
  ***GLOBAL_INTERVAL_COUNT; 


void	init_exp_pre_management() { 
  int	pi, i, vi, last_discrete_vi = 0; 

  PS_EXP_TRUE = NULL;  
  PS_EXP_FALSE = NULL; 
  PS_EXP_LOCAL_IDENTIFIER = NULL; 
  PS_EXP_GLOBAL_IDENTIFIER = NULL; 
  PS_EXP_MODE = NULL; 
  PS_EXP__SP = NULL; 
  PS_EXP__SP_PLUS = NULL; 
  PS_EXP__SP_MINUS = NULL; 
  PS_EXP__RETMODE = NULL; 
  PS_EXP_ONE = NULL; 
  PS_EXP_NEG_ONE = NULL; 
  PS_EXP_ZERO = NULL; 

  init_23tree(&EXP_TREE); 
  PS_EXP_TRUE = ps_exp_share(ps_exp_alloc(TYPE_TRUE)); 
  PS_EXP_TRUE->var_status = 0; 
  PS_EXP_TRUE->exp_status = FLAG_CONSTANT | FLAG_TCTCTL_SUBFORM; 

  PS_EXP_FALSE = ps_exp_share(ps_exp_alloc(TYPE_FALSE)); 
  PS_EXP_FALSE->var_status = 0; 
  PS_EXP_FALSE->exp_status = FLAG_CONSTANT | FLAG_TCTCTL_SUBFORM; 

  PS_EXP_LOCAL_IDENTIFIER = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER); 
  PS_EXP_LOCAL_IDENTIFIER->var_status = 0; 
  PS_EXP_LOCAL_IDENTIFIER->exp_status = FLAG_LOCAL_IDENTIFIER; 
  PS_EXP_LOCAL_IDENTIFIER = ps_exp_share(PS_EXP_LOCAL_IDENTIFIER); 

  PS_EXP_ZERO = ps_exp_alloc(TYPE_CONSTANT); 
  PS_EXP_ZERO->var_status = 0; 
  PS_EXP_ZERO->exp_status = FLAG_CONSTANT; 
  PS_EXP_ZERO->u.value = 0; 
  PS_EXP_ZERO = ps_exp_share(PS_EXP_ZERO); 
  
  PS_EXP_GLOBAL_IDENTIFIER = PS_EXP_ZERO; 

  PS_EXP_ONE = ps_exp_alloc(TYPE_CONSTANT); 
  PS_EXP_ONE->var_status = 0; 
  PS_EXP_ONE->exp_status = FLAG_CONSTANT; 
  PS_EXP_ONE->u.value = 1; 
  PS_EXP_ONE = ps_exp_share(PS_EXP_ONE); 
  
  PS_EXP_NEG_ONE = ps_exp_alloc(TYPE_CONSTANT); 
  PS_EXP_NEG_ONE->var_status = 0; 
  PS_EXP_NEG_ONE->exp_status = FLAG_CONSTANT; 
  PS_EXP_NEG_ONE->u.value = -1; 
  PS_EXP_NEG_ONE = ps_exp_share(PS_EXP_NEG_ONE); 
}
  /* init_exp_pre_management() */ 





struct interval_link_type 
  DUMMY_INTERVAL_NODE, // This is the interval of all values between 
                       // lb and ub. 
                       // It is declared as a static so that its 
                       // deallocation causes a failure for debugging.
  *GENERAL_INTERVAL_FULL,  
  *GENERAL_INTERVAL_EMPTY; 

void	init_exp_management() { 
  int	pi, i, vi, last_discrete_vi = 0; 

  GENERAL_INTERVAL_FULL = &DUMMY_INTERVAL_NODE; 
  GENERAL_INTERVAL_EMPTY = &(DUMMY_INTERVAL_NODE)+1; 
  
  GLOBAL_INTERVAL_LIST = ((struct interval_link_type ****) 
    malloc(4*sizeof(struct interval_link_type ***)) 
  ) - TYPE_DISCRETE; 
  last_discrete_vi = 0; 
  GLOBAL_INTERVAL_LIST[TYPE_DISCRETE] = (struct interval_link_type ***) 
    malloc((PROCESS_COUNT+1) * sizeof(struct interval_link_type **)); 
  if (GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE) {
    GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][0] = (struct interval_link_type **) 
      malloc((GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE)
             *sizeof(struct interval_link_type *)
             );
    for (i = 0; i < GLOBAL_COUNT[TYPE_DISCRETE]; i++) {
      GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][0][i] = NULL;
      vi = variable_index[TYPE_DISCRETE][0][i]; 
      VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
      last_discrete_vi = vi; 
    } 
  }
  else
    GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][0] = NULL;

  GLOBAL_INTERVAL_LIST[TYPE_FLOAT] = (struct interval_link_type ***) 
    malloc((PROCESS_COUNT+1) * sizeof(struct interval_link_type **)); 
  if (GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE) {
    GLOBAL_INTERVAL_LIST[TYPE_FLOAT][0] = (struct interval_link_type **) 
      malloc((GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE)
             *sizeof(struct interval_link_type *)
             );
    for (i = 0; i < GLOBAL_COUNT[TYPE_FLOAT]; i++) {
      GLOBAL_INTERVAL_LIST[TYPE_FLOAT][0][i] = NULL;
      vi = variable_index[TYPE_FLOAT][0][i]; 
/*
      VAR[last_discrete_vi].U..NEXT_DISCRETE_VI = vi; 
      last_discrete_vi = vi; 
*/
    } 
  }
  else
    GLOBAL_INTERVAL_LIST[TYPE_FLOAT][0] = NULL;

  GLOBAL_INTERVAL_LIST[TYPE_DOUBLE] = (struct interval_link_type ***) 
    malloc((PROCESS_COUNT+1) * sizeof(struct interval_link_type **)); 
  if (GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE) {
    GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][0] = (struct interval_link_type **) 
      malloc((GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE)
             *sizeof(struct interval_link_type *)
             );
    for (i = 0; i < GLOBAL_COUNT[TYPE_DOUBLE]; i++) {
      GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][0][i] = NULL;
      vi = variable_index[TYPE_DOUBLE][0][i]; 
/*
      VAR[last_discrete_vi].U..NEXT_DISCRETE_VI = vi; 
      last_discrete_vi = vi; 
*/
    } 
  }
  else
    GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][0] = NULL;

  GLOBAL_INTERVAL_LIST[TYPE_POINTER] = (struct interval_link_type ***) 
    malloc((PROCESS_COUNT+1) * sizeof(struct interval_link_type **)); 
  if (GLOBAL_COUNT[TYPE_POINTER]) {
    GLOBAL_INTERVAL_LIST[TYPE_POINTER][0] = (struct interval_link_type **) 
      malloc(GLOBAL_COUNT[TYPE_POINTER]*sizeof(struct interval_link_type *));
    for (i = 0; i < GLOBAL_COUNT[TYPE_POINTER]; i++) {
      GLOBAL_INTERVAL_LIST[TYPE_POINTER][0][i] = NULL; 
      vi = variable_index[TYPE_POINTER][0][i]; 
      VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
      last_discrete_vi = vi; 
    } 
  }
  else
    GLOBAL_INTERVAL_LIST[TYPE_POINTER][0] = NULL;

  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    if (LOCAL_COUNT[TYPE_DISCRETE]) {
      GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][pi] 
      = (struct interval_link_type **) 
        malloc(LOCAL_COUNT[TYPE_DISCRETE]
               *sizeof(struct interval_link_type *)
      );
      for (i = 0; i < LOCAL_COUNT[TYPE_DISCRETE]; i++) {
        GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][pi][i] = NULL; 
        vi = variable_index[TYPE_DISCRETE][pi][i]; 
        if (last_discrete_vi) 
          VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
        else 
          VAR[0].U.DISC.NEXT_DISCRETE_VI = vi; 
        last_discrete_vi = vi; 
      }
    }
    else
      GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][pi] = NULL; 

    if (LOCAL_COUNT[TYPE_FLOAT]) {
      GLOBAL_INTERVAL_LIST[TYPE_FLOAT][pi] 
      = (struct interval_link_type **) 
        malloc(LOCAL_COUNT[TYPE_FLOAT]
               *sizeof(struct interval_link_type *)
      );
      for (i = 0; i < LOCAL_COUNT[TYPE_FLOAT]; i++) {
        GLOBAL_INTERVAL_LIST[TYPE_FLOAT][pi][i] = NULL; 
        vi = variable_index[TYPE_FLOAT][pi][i]; 
/*
        if (last_discrete_vi) 
          VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
        else 
          VAR[0].U.DISC.NEXT_DISCRETE_VI = vi; 
        last_discrete_vi = vi; 
*/
      }
    }
    else
      GLOBAL_INTERVAL_LIST[TYPE_FLOAT][pi] = NULL; 

    if (LOCAL_COUNT[TYPE_DOUBLE]) {
      GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][pi] 
      = (struct interval_link_type **) 
        malloc(LOCAL_COUNT[TYPE_DOUBLE]
               *sizeof(struct interval_link_type *)
      );
      for (i = 0; i < LOCAL_COUNT[TYPE_DOUBLE]; i++) {
        GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][pi][i] = NULL; 
        vi = variable_index[TYPE_DOUBLE][pi][i]; 
/*
        if (last_discrete_vi) 
          VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
        else 
          VAR[0].U.DISC.NEXT_DISCRETE_VI = vi; 
        last_discrete_vi = vi; 
*/
      }
    }
    else
      GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][pi] = NULL; 

    if (LOCAL_COUNT[TYPE_POINTER]) {
      GLOBAL_INTERVAL_LIST[TYPE_POINTER][pi] 
      = (struct interval_link_type **) 
        malloc(LOCAL_COUNT[TYPE_POINTER]
               *sizeof(struct interval_link_type *)
      );
      for (i = 0; i < LOCAL_COUNT[TYPE_POINTER]; i++) {
        GLOBAL_INTERVAL_LIST[TYPE_POINTER][pi][i] = NULL; 
        vi = variable_index[TYPE_POINTER][pi][i]; 
        if (last_discrete_vi) 
          VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = vi; 
        else 
          VAR[0].U.DISC.NEXT_DISCRETE_VI = vi; 
        last_discrete_vi = vi; 
      }
    }
    else
      GLOBAL_INTERVAL_LIST[TYPE_POINTER][pi] = NULL; 
  }

  if (MEMORY_DISCRETE_SIZE > 0) {
    for (i = 0; i < MEMORY_DISCRETE_SIZE; i++) { 
      GLOBAL_INTERVAL_LIST[TYPE_DISCRETE]
      [0]
      [i+GLOBAL_COUNT[TYPE_DISCRETE]] 
      = NULL;
      vi = variable_index[TYPE_DISCRETE][0][i+GLOBAL_COUNT[TYPE_DISCRETE]]; 
/*
      fprintf(RED_OUT, "initialize global_interval_list for %1d:%s\n", 
        vi, VAR[vi].NAME
      ); 
      fprintf(RED_OUT, "i=%1d, GLOBAL_COUNT[TYPE_DISCRETE]=%1d\n", 
        i, GLOBAL_COUNT[TYPE_DISCRETE] 
      ); 
*/
      VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI 
      = variable_index[TYPE_DISCRETE][0][i+GLOBAL_COUNT[TYPE_DISCRETE]]; 
      last_discrete_vi = VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI; 
    } 
  }
  VAR[last_discrete_vi].U.DISC.NEXT_DISCRETE_VI = VARIABLE_COUNT; 

  if (MEMORY_FLOAT_SIZE > 0) {
    for (i = 0; i < MEMORY_FLOAT_SIZE; i++) { 
      GLOBAL_INTERVAL_LIST[TYPE_FLOAT]
      [0]
      [i+GLOBAL_COUNT[TYPE_FLOAT]] 
      = NULL;
    } 
  }
  
  if (MEMORY_DOUBLE_SIZE > 0) {
    for (i = 0; i < MEMORY_DOUBLE_SIZE; i++) { 
      GLOBAL_INTERVAL_LIST[TYPE_DOUBLE]
      [0]
      [i+GLOBAL_COUNT[TYPE_DOUBLE]] 
      = NULL;
    } 
  }
}
  /* init_exp_management() */ 





void	release_all_ps_exp() { 
  free_entire_23tree(EXP_TREE, ps_exp_free); 
} 
  /* release_all_ps_exp() */ 




struct ps_exp_type	*ps_exp_alloc(
  int	type 
) {
  struct ps_exp_type	*psub; 
  
  psub = (struct ps_exp_type *) malloc(sizeof(struct ps_exp_type)); 
  psub->type = type; 
  psub->var_status = 0; 
  psub->exp_status = 0; 
  psub->a23tree = NULL; 
  psub->count = 0; 
  
  switch (type) { 
  case TYPE_NULL:  
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_PROCESS_COUNT: 
    break; 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    psub->u.exp = NULL; 
    break; 
  case TYPE_MODE_INDEX: 
    psub->u.mode_index.mode_name = NULL; 
    psub->u.mode_index.value = 0; 
    break; 
  case TYPE_INTERVAL: 
    psub->u.interval.lbound_exp = NULL; 
    psub->u.interval.rbound_exp = NULL; 
    break; 
  case TYPE_SYNCHRONIZER: 
    psub->var_status = FLAG_SYNCHRONIZER; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_DISCRETE: 
    psub->var_status = FLAG_DISCRETE; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_POINTER: 
    psub->var_status = FLAG_POINTER; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_FLOAT: 
    psub->var_status = FLAG_FLOAT; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_DOUBLE: 
    psub->var_status = FLAG_DOUBLE; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_CLOCK: 
    psub->var_status = FLAG_CLOCK; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_DENSE: 
    psub->var_status = FLAG_DENSE; 
/*
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case TYPE_LOCAL_IDENTIFIER: 
    if (PS_EXP_LOCAL_IDENTIFIER) {
      free(psub); 
      psub = PS_EXP_LOCAL_IDENTIFIER; 
    }
    else 
      psub->exp_status = FLAG_LOCAL_IDENTIFIER; 
    break; 
  case TYPE_QFD: 
    psub->var_status = FLAG_QFD; 
/* 
    psub->u.atom.indirect_count = 0; 
    psub->u.atom.indirect_exp = NULL; 
    psub->u.atom.indirect_vi = NULL; 
*/
    break; 
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
  	
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:
  
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

    psub->u.arith.lhs_exp = NULL; 
    psub->u.arith.rhs_exp = NULL; 
    break; 
    
  case ARITH_CONDITIONAL: 
    psub->u.arith_cond.cond = NULL; 
    psub->u.arith_cond.if_exp = NULL; 
    psub->u.arith_cond.else_exp = NULL; 
    break; 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    psub->u.ineq.term = NULL;
    psub->u.ineq.offset = NULL;
    break; 
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    psub->u.inline_declare.inline_exp_name = NULL; 
    psub->u.inline_declare.status = 0; 
    psub->u.inline_declare.formal_argument_count = 0; 
    psub->u.inline_declare.formal_argument_list = NULL; 
    psub->u.inline_declare.declare_exp = NULL; 
    break; 
    
  case TYPE_INLINE_CALL: 
    psub->u.inline_call.inline_exp_name = NULL;  
    psub->u.inline_call.inline_declare = NULL; 
    psub->u.inline_call.instantiated_exp = NULL; 
    psub->u.inline_call.actual_argument_list = NULL; 
    break; 
    
  case TYPE_INLINE_ARGUMENT: 
    psub->u.argument = NULL; 
    break; 
    
  case AND :
  case OR :
  case NOT :
  case IMPLY :
    psub->u.bexp.blist = NULL;
    break; 
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case EXISTS_ALWAYS: 
  case EXISTS_EVENTUALLY: 
  case FORALL_UNTIL: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
  
  case TYPE_GAME_SIM: 
    psub->u.mexp.dest_child = NULL; 
    psub->u.mexp.path_child = NULL; 
    psub->u.mexp.time_lb == 0; 
    psub->u.mexp.time_ub == 0;
    psub->u.mexp.time_restriction = PS_EXP_TRUE; 
    psub->u.mexp.event_restriction = NULL; 
    psub->u.mexp.strong_fairness_count = 0;
    psub->u.mexp.strong_fairness_list = NULL; 
    psub->u.mexp.weak_fairness_count = 0;
    psub->u.mexp.weak_fairness_list = NULL; 
    psub->u.mexp.red_early_decision_maker = NULL; 
    break; 

  case LINEAR_EVENT: 
    psub->u.eexp.precond_exp = NULL; 
    psub->u.eexp.postcond_exp = NULL; 
    psub->u.eexp.red_precond = NULL; 
    psub->u.eexp.red_postcond = NULL; 
    psub->u.eexp.event_exp = NULL; 
    psub->u.eexp.red_sync_bulk_from_event_exp = NULL;
    psub->u.eexp.red_game_sync_bulk_from_event_exp = NULL;
    break; 
  } 
  return(psub);
}
  /* ps_exp_alloc() */ 



struct ps_exp_type	*CURRENT_PS_EXP; 

void	ps_exp_free_list(l) 
  struct ps_bunit_type	*l; 
{ 
  struct ps_bunit_type	*pbu, *gar;

  for (pbu = l; pbu; ) { 
    gar = pbu; 
    pbu = pbu->bnext; 
/*
    if (gar == tmp_bunit_comp) { 
      fprintf(RED_OUT, "\nCaught freeing tmp_bunit_comp = %x at %x:%1d\n", 
        (unsigned int) gar, (unsigned int) CURRENT_PS_EXP, CURRENT_PS_EXP->type
      ); 
//      pcform(CURRENT_PS_EXP); 
      fflush(RED_OUT); 
    } 
    else if (gar == tmp_bunit_comp2) { 
      fprintf(RED_OUT, "\nCaught freeing tmp_bunit_comp2 = %x at %x:%1d\n", 
        (unsigned int) gar, (unsigned int) CURRENT_PS_EXP, CURRENT_PS_EXP->type
      ); 
//      pcform(CURRENT_PS_EXP); 
      fflush(RED_OUT); 
    } 
*/
    free(gar); 
  }
}
  /* ps_exp_free_list() */ 


void	ps_fairness_free_list(
  struct ps_fairness_link_type	*l 
) { 
  struct ps_fairness_link_type	*fl, *pfl; 
  
  for (fl = l; 
       fl; 
       pfl = fl->next_ps_fairness_link, free(fl), fl = pfl 
       ) ; 
}
  /* ps_fairness_free_list() */ 



#ifdef RED_DEBUG_EXP_MODE
int	count_exp_free = 0; 
#endif 

int	ps_exp_free(
  struct ps_exp_type	*psub
) {
  int				ii;
  struct ps_bunit_type		*pbu, *gar;
  struct ps_fairness_link_type	*fl, *pfl; 
  struct name_link_type		*nl, *pnl; 

  #ifdef RED_DEBUG_EXP_MODE
//  if (tmp_exp_comp == psub) { 
    fprintf(RED_OUT, "\n%1d: free ps exp %x:%1d\n", 
      ++count_exp_free, (unsigned int) psub, psub->type
    ); 
    fflush(RED_OUT); 
//  } 
  #endif 

  #ifdef RED_DEBUG_EXP_MODE
  if (psub == target_exp) { 
    fprintf(RED_OUT, "\nCaught freeing target_exp = %x:%1d\n", 
      (unsigned int) target_exp, target_exp->type 
    ); 
//    pcform(target_exp); 
    fflush(RED_OUT); 
  } 
  else if (psub == target_exp2) { 
    fprintf(RED_OUT, "\nCaught freeing target_exp2 %x:%1d\n", 
      (unsigned int) target_exp2, target_exp2->type
    ); 
//    pcform(target_exp2); 
    fflush(RED_OUT); 
  } 
  #endif 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_PROCESS_COUNT: 
  
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  
  case BIT_NOT: 

  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 

  case RED: 
    free(psub); 
    break; 
    
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
/*
    if (psub->u.atom.indirect_exp) {
      free(psub->u.atom.indirect_exp); 
    } 
    if (psub->u.atom.indirect_vi) 
      free(psub->u.atom.indirect_vi); 
*/
    free(psub); 
    break; 
    
  case TYPE_MODE_INDEX: 
    free(psub->u.mode_index.mode_name); 
    free(psub); 
    break; 
    
  case TYPE_INLINE_ARGUMENT: 
//    free(psub->u.argument); 
    free(psub); 
    break; 
    
  case TYPE_INTERVAL: 
    free(psub); 
    break; 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    free(psub->u.ineq.term);
    free(psub);
    break;

  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:
  
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    free(psub);
    break;

  case ARITH_CONDITIONAL:
    free(psub);
    break;
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
//    free(psub->u.inline_declare.inline_exp_name); 
    for (nl = psub->u.inline_declare.formal_argument_list; 
         nl; 
         pnl = nl->next_name_link, free(nl), nl = pnl
         ) ; 
      /* free(nl->name)*/ ; 
//    free(psub->u.inline_declare.declare_exp); 
    free(psub); 
    break; 
    
  case TYPE_INLINE_CALL: 
//    The following string is shared with the corresponding 
//    TYPE_INLINE_DISCRETE_DECLARE or TYPE_INLINE_BOOLEAN_DECLARE 
//    and is to be released there. 
//    free(psub->u.inline_call.inline_exp_name);  
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         gar = pbu, pbu = pbu->bnext, free(gar)  
         ) ; 
    free(psub); 
    break; 
    
  case AND :
  case OR :
  case NOT :
  case IMPLY :
    CURRENT_PS_EXP = psub; 
    ps_exp_free_list(psub->u.bexp.blist); 
    free(psub); 
    return; 

  case PROJECT:
  case PROJECT_TIME:
  case PROJECT_TYPE:
  case PROJECT_QSYNC: 
  case PROJECT_PEER:
  case PROJECT_LOCAL:
  case PROJECT_VAR_SIM:
  case PROJECT_CLOCK_SIM:
  case PROJECT_CLOCK_LOWER_EXTEND:
  case PROJECT_CLOCK_UPPER_EXTEND:
  case PROJECT_MCHUNK:
  case RESET: 
    free(psub); 
    return; 

  case FORALL: 
  case EXISTS: 
  case TYPE_MULTIPLE_FAIRNESS: 
    free(psub);
    return;
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_UNTIL: 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
  case EXISTS_ALWAYS: 
  case EXISTS_EVENTUALLY: 
  case EXISTS_UNTIL: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 

  case TYPE_GAME_SIM: 
/*
    fprintf(RED_OUT, "\nFreeing a game sim %x: \n", (unsigned int) psub); 
//    pcform(psub); 
*/
    for (fl = psub->u.mexp.strong_fairness_list; 
         fl; 
         pfl = fl->next_ps_fairness_link, free(fl), fl = pfl 
         ) ; 
    for (fl = psub->u.mexp.weak_fairness_list; 
         fl; 
         pfl = fl->next_ps_fairness_link, free(fl), fl = pfl
         ) ; 
    free(psub); 
    break; 
 
  case LINEAR_EVENT: 
    free(psub); 
    break; 
    
  default: 
    fprintf(RED_OUT, "Error: to free unimplemented ps exp type %1d. \n", psub->type);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(13);
  }
}
  /* ps_exp_free() */ 



void	free_ps_exptree_list(l) 
  struct ps_bunit_type	*l; 
{ 
  struct ps_bunit_type	*pbu, *gar;

  for (pbu = l; pbu; gar = pbu, pbu = pbu->bnext, free(gar)) 
    free_ps_exptree(pbu->subexp); 
}
  /* free_ps_exptree_list() */ 



void	free_ps_exp_list(l) 
  struct ps_bunit_type	*l; 
{ 
  struct ps_bunit_type	*pbu, *gar;

  for (pbu = l; pbu; gar = pbu, pbu = pbu->bnext, free(gar)) ; 
}
  /* free_ps_exp_list() */ 





free_ps_exptree(psub)
     struct ps_exp_type	*psub;
{
  int				ii;
  struct ps_bunit_type		*pbu, *gar;
  struct ps_fairness_link_type	*fl, *pfl; 
  struct name_link_type		*nl, *pnl; 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_PROCESS_COUNT: 

  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER:   
  case TYPE_MACRO_CONSTANT: 

  case RED: 
    free(psub); 
    break; 
    
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    free_ps_exptree(psub->u.exp); 
    free(psub); 
    break; 

  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    free_ps_exptree(psub->u.atom.exp_base_proc_index); 
/*
    if (psub->u.atom.indirect_exp) {
      for (ii = 0; ii < psub->u.atom.indirect_count; ii++) 
        free_ps_exptree(psub->u.atom.indirect_exp[ii]); 
      free(psub->u.atom.indirect_exp); 
    } 
    if (psub->u.atom.indirect_vi) 
      free(psub->u.atom.indirect_vi); 
*/
    free(psub); 
    break; 

  case TYPE_MODE_INDEX: 
    free(psub->u.mode_index.mode_name); 
    free(psub); 
    break; 
    
  case TYPE_INLINE_ARGUMENT: 
//    free(psub->u.argument); 
    free(psub); 
    break; 
    
  case TYPE_INTERVAL: 
    free_ps_exptree(psub->u.interval.lbound_exp); 
    free_ps_exptree(psub->u.interval.rbound_exp); 
    free(psub); 
    break; 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    for (ii = 0; ii < psub->u.ineq.term_count; ii++) {
      free_ps_exptree(psub->u.ineq.term[ii].operand);
      free_ps_exptree(psub->u.ineq.term[ii].coeff);
    }
    free(psub->u.ineq.term);
    free(psub->u.ineq.offset);
    free(psub);
    break;

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:
    free_ps_exptree(psub->u.arith.lhs_exp);
    free_ps_exptree(psub->u.arith.rhs_exp);
    free(psub);
    break;
  case ARITH_CONDITIONAL:
    free_ps_exptree(psub->u.arith_cond.cond);
    free_ps_exptree(psub->u.arith_cond.if_exp);
    free_ps_exptree(psub->u.arith_cond.else_exp);
    free(psub);
    break;
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
//    free(psub->u.inline_declare.inline_exp_name); 
    for (nl = psub->u.inline_declare.formal_argument_list; 
         nl; 
         pnl = nl->next_name_link, free(nl), nl = pnl
         ) 
      /* free(nl->name)*/ ; 
    free(psub->u.inline_declare.declare_exp); 
    free(psub); 
    break; 
    
  case TYPE_INLINE_CALL: 
//    The following string is shared with the corresponding 
//    TYPE_INLINE_DISCRETE_DECLARE or TYPE_INLINE_BOOLEAN_DECLARE 
//    and is to be released there. 
//    free(psub->u.inline_call.inline_exp_name);  
    if (psub->u.inline_call.instantiated_exp) 
      free_ps_exptree(psub->u.inline_call.instantiated_exp); 
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         gar = pbu, pbu = pbu->bnext, free(gar)  
         ) 
      free(pbu->subexp); 
    free(psub); 
    break; 
    
  case AND :
  case OR :
    free_ps_exptree_list(psub->u.bexp.blist); 
    free(psub); 
    return; 
  case NOT :
    free_ps_exptree(psub->u.bexp.blist->subexp);
    free(psub->u.bexp.blist);
    free(psub); 
    return;
  case IMPLY :
    free_ps_exptree(psub->u.bexp.blist->subexp);
    free_ps_exptree(psub->u.bexp.blist->bnext->subexp);
    free(psub->u.bexp.blist->bnext); 
    free(psub->u.bexp.blist);
    free(psub); 
    return; 
  case PROJECT:
  case PROJECT_TIME:
  case PROJECT_TYPE:
  case PROJECT_QSYNC: 
  case PROJECT_CLOCK_LOWER_EXTEND:
  case PROJECT_CLOCK_UPPER_EXTEND:
  case PROJECT_PEER:
  case PROJECT_LOCAL: 
  case PROJECT_VAR_SIM:
  case PROJECT_CLOCK_SIM:
  case PROJECT_MCHUNK:
  case RESET: 
    free(psub); 
    return; 

  case FORALL: 
  case EXISTS: 
    free_ps_exptree(psub->u.qexp.child); 
    free_ps_exptree(psub->u.qexp.lb_exp); 
    free_ps_exptree(psub->u.qexp.ub_exp); 
    free(psub);
    return;
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case EXISTS_ALWAYS: 
  case EXISTS_EVENTUALLY: 
  case FORALL_UNTIL: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
    free_ps_exptree(psub->u.mexp.dest_child); 
    free_ps_exptree(psub->u.mexp.path_child); 
    free_ps_exptree(psub->u.mexp.time_restriction); 
    if (psub->u.mexp.event_restriction) 
      free_ps_exptree(psub->u.mexp.event_restriction); 
    for (fl = psub->u.mexp.strong_fairness_list; 
         fl; 
         pfl = fl->next_ps_fairness_link, free(fl), fl = pfl 
         ) 
      free_ps_exptree(fl->fairness); 
    for (fl = psub->u.mexp.weak_fairness_list; 
         fl; 
         fl = fl->next_ps_fairness_link, free(fl), fl = pfl
         ) 
      free_ps_exptree(fl->fairness); 
    free(psub); 
    break; 
  case TYPE_GAME_SIM: 
    for (fl = psub->u.mexp.strong_fairness_list; 
         fl; 
         pfl = fl->next_ps_fairness_link, free(fl), fl = pfl 
         ) 
      free_ps_exptree(fl->fairness); 
    for (fl = psub->u.mexp.weak_fairness_list; 
         fl; 
         fl = fl->next_ps_fairness_link, free(fl), fl = pfl
         ) 
      free_ps_exptree(fl->fairness); 
    break; 
 
  case LINEAR_EVENT: 
    if (psub->u.eexp.event_exp)
      free_ps_exptree(psub->u.eexp.event_exp); 
    free_ps_exptree(psub->u.eexp.precond_exp); 
    free_ps_exptree(psub->u.eexp.postcond_exp); 
    free(psub); 
    break; 
  default: 
    fprintf(RED_OUT, "Error: to free unimplemented ps exp type %1d. \n", psub->type);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(13);
  }
}
  /* free_ps_exptree() */ 





struct ps_exp_type	*ps_exp_copy(); 

struct ps_exp_type	**ps_exp_indirect_exp_copy(
  struct ps_exp_type	**indirect_exp, 
  int			indirect_count 
) { 
  struct ps_exp_type	**nind;
  int			i; 

  nind = (struct ps_exp_type **) 
    malloc(indirect_count * sizeof(struct ps_exp_type *)); 
  for (i = 0; i < indirect_count; i++) 
    nind[i] = indirect_exp[i]; 
  return(nind); 
}
  /* ps_exp_indirect_exp_copy() */ 




struct ps_fairness_link_type	*ps_exp_flist_copy(list) 
  struct ps_fairness_link_type	*list; 
{ 
  struct ps_fairness_link_type	*fl, *nfl, dummy_fl, *fl_tail;
  
  fl_tail = &dummy_fl; 
  for (fl = list; fl; fl = fl->next_ps_fairness_link) { 
    nfl = (struct ps_fairness_link_type *) malloc(sizeof(struct ps_fairness_link_type)); 
    fl_tail->next_ps_fairness_link = nfl; 
    fl_tail = nfl; 
    nfl->fairness = fl->fairness; 
  } 
  fl_tail->next_ps_fairness_link = NULL; 
  return(dummy_fl.next_ps_fairness_link); 
} 
  /* ps_exp_flist_copy() */  




struct ps_bunit_type	*ps_explist_copy(
  struct ps_bunit_type	*list
) {
  struct ps_bunit_type	dummy_bu, *bu_tail, *pbu, *nbu; 
  
  bu_tail = &dummy_bu;  
  for (pbu = list; pbu; pbu = pbu->bnext) { 
    nbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu_tail->bnext = nbu; 
    bu_tail = nbu; 
    bu_tail->subexp = pbu->subexp; 
  }
  bu_tail->bnext = NULL; 
  return(dummy_bu.bnext); 
}
  /* ps_explist_copy() */ 




struct parse_term_type *ps_term_array_copy(
  struct parse_term_type	*t, 
  int				tc
) {
  struct parse_term_type	*nt; 
  int				i; 
  
  nt = (struct parse_term_type *) 
    malloc(tc * sizeof(struct parse_term_type)); 
  for (i = 0; i < tc; i++)  {
    nt[i].coeff = t[i].coeff; 
    nt[i].operand = t[i].operand; 
  } 
  return(nt); 
} 
  /* ps_term_array_copy() */ 



struct ps_exp_type	*ps_exp_copy(psub)
     struct ps_exp_type	*psub; 
{
  int				i;
  struct ps_exp_type		*newsub; 
  struct ps_bunit_type		*pbu, *nbu, dummy_bu, *bu_tail;
  struct name_link_type		*nl, *pnl, dummy_nl, *nl_tail; 

  if (!psub) 
    return(NULL); 
    
  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_QSYNC_HOLDER: 
  case TYPE_QFD:
  case TYPE_NULL:
  case TYPE_PROCESS_COUNT: 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
  
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_INLINE_ARGUMENT: 
  case TYPE_MODE_INDEX: 
  case TYPE_INTERVAL:
    return(psub); 
    
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.atom.exp_base_proc_index = psub->u.atom.exp_base_proc_index; 
/*
    newsub->u.atom.indirect_exp = ps_exp_indirect_exp_copy(
      psub->u.atom.indirect_exp, psub->u.atom.indirect_count
    ); 
    if (psub->u.atom.indirect_vi) {
      newsub->u.atom.indirect_vi = (int *) 
        malloc((PROCESS_COUNT+1) * sizeof(int) 
      ); 
      for (i = 1; i <= PROCESS_COUNT; i++) 
        newsub->u.atom.indirect_vi[i] = psub->u.atom.indirect_vi[i]; 
    } 
*/
    return(newsub); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = psub->u.arith.lhs_exp;  
    newsub->u.arith.rhs_exp = psub->u.arith.rhs_exp;  
    return(newsub); 

  case ARITH_CONDITIONAL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith_cond.cond = psub->u.arith_cond.cond;  
    newsub->u.arith_cond.if_exp = psub->u.arith_cond.if_exp;  
    newsub->u.arith_cond.else_exp = psub->u.arith_cond.else_exp;  
    return(newsub); 

  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.ineq.offset = psub->u.ineq.offset; 
    newsub->u.ineq.term = ps_term_array_copy(
      psub->u.ineq.term, psub->u.ineq.term_count
    );  
    return(newsub);
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.inline_declare.inline_exp_name
    = psub->u.inline_declare.inline_exp_name; 
    dummy_nl.next_name_link = NULL; 
    nl_tail = &dummy_nl; 
    for (nl = psub->u.inline_declare.formal_argument_list; 
         nl; 
         nl = nl->next_name_link
         ) {
      pnl = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
      pnl->name = nl->name; 
      nl_tail->next_name_link = pnl; 
      nl_tail = pnl; 
    }
    nl_tail->next_name_link = NULL; 
    newsub->u.inline_declare.formal_argument_list = dummy_nl.next_name_link; 
    
    newsub->u.inline_declare.declare_exp 
    = psub->u.inline_declare.declare_exp; 
    return(newsub); 
    break; 
    
  case TYPE_INLINE_CALL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.inline_call.inline_exp_name 
    = psub->u.inline_call.inline_exp_name; 
    bu_tail = &dummy_bu; 
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         pbu = pbu->bnext  
         ) {
      nbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
      nbu->subexp = pbu->subexp; 
      bu_tail->bnext = nbu; 
      bu_tail = nbu; 
    } 
    bu_tail->bnext = NULL; 
    newsub->u.inline_call.actual_argument_list = dummy_bu.bnext; 
    if (psub->u.inline_call.instantiated_exp) { 
      newsub->u.inline_call.instantiated_exp 
      = psub->u.inline_call.instantiated_exp; 
    } 
    return(newsub); 
    break; 
    
  case AND :
  case OR :
  case NOT :
  case IMPLY : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.blist = ps_explist_copy(psub->u.bexp.blist); 
    return(newsub);

  case FORALL:
  case EXISTS:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.qexp.lb_exp = psub->u.qexp.lb_exp;
    newsub->u.qexp.ub_exp = psub->u.qexp.ub_exp;
    newsub->u.qexp.child = psub->u.qexp.child;
    return(newsub);

  case RESET:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = psub->u.reset.child; 
    return (newsub); 

  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY: 
  case EXISTS_ALWAYS:
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE:
  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.strong_fairness_list 
    = ps_exp_flist_copy(psub->u.mexp.strong_fairness_list); 
    newsub->u.mexp.weak_fairness_list 
    = ps_exp_flist_copy(psub->u.mexp.weak_fairness_list); 
    newsub->u.mexp.path_child = psub->u.mexp.path_child;
    newsub->u.mexp.event_restriction = psub->u.mexp.event_restriction; 
    newsub->u.mexp.red_xi_restriction = psub->u.mexp.red_xi_restriction; 
    newsub->u.mexp.dest_child = psub->u.mexp.dest_child;
    newsub->u.mexp.time_restriction = psub->u.mexp.time_restriction; 
    return (newsub); 
    
  case LINEAR_EVENT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.eexp.precond_exp = psub->u.eexp.precond_exp;
    newsub->u.eexp.event_exp = psub->u.eexp.event_exp;
    newsub->u.eexp.postcond_exp = psub->u.eexp.postcond_exp;
    newsub->u.eexp.red_sync_bulk_from_event_exp 
    = psub->u.eexp.red_sync_bulk_from_event_exp;
    newsub->u.eexp.red_game_sync_bulk_from_event_exp 
    = psub->u.eexp.red_game_sync_bulk_from_event_exp;
    newsub->u.eexp.red_precond = psub->u.eexp.red_precond;
    newsub->u.eexp.red_postcond = psub->u.eexp.red_postcond;
    return (newsub); 
  
  case TYPE_GAME_SIM: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.strong_fairness_list 
    = ps_exp_flist_copy(psub->u.mexp.strong_fairness_list); 
    newsub->u.mexp.weak_fairness_list 
    = ps_exp_flist_copy(psub->u.mexp.weak_fairness_list); 
    newsub->u.mexp.path_child = NULL; 
    newsub->u.mexp.dest_child = NULL; 
    return (newsub); 

  case RED:
    newsub->u.rpred.red = psub->u.rpred.red;
    newsub->u.rpred.original_red = psub->u.rpred.original_red;
    return (newsub); 
  default: 
    fprintf(RED_OUT, "\nERROR, unexpected exp type %1d in ps_exp_copy().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* ps_exp_copy() */ 



#ifdef RED_DEBUG_EXP_MODE
int	count_ps_exp_comp = 0; 
#endif 

int	ps_exp_comp(e1, e2)
     struct ps_exp_type	*e1, *e2; 
{
  int				i, comp;
  struct ps_bunit_type		*pbu1, *pbu2;
//  struct parse_indirect_type	*pt1, *pt2;
  struct ps_fairness_link_type	*f1, *f2;
  struct name_link_type		*nl1, *nl2; 

#ifdef RED_DEBUG_EXP_MODE
  if (tmp_exp_comp == e1) { 
    fprintf(RED_OUT, "\n**********\ncount ps exp comp = %1d:e1:%x:%1d:\n", 
      ++count_ps_exp_comp, (unsigned int) e1, e1->type 
    ); 
    pcform(e1); 
    fprintf(RED_OUT, "count ps exp comp = %1d:e2:%x:%1d:\n", 
      count_ps_exp_comp, (unsigned int) e2, e2->type 
    ); 
    pcform(e2); 
    fflush(RED_OUT); 
  }
#endif 

  if (!e1) 
    if (!e2) 
      return (0); 
    else 
      return (-1); 
  else if (!e2) 
    return (1); 
  else if (e1->type != e2->type) 
    return (e1->type - e2->type); 

  else switch(e1->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH: 
  case TYPE_PROCESS_COUNT: 
    return(0); 
  
  case TYPE_CONSTANT:
    return (e1->u.value - e2->u.value); 
  
  case TYPE_FLOAT_CONSTANT:
    return (e1->u.float_value - e2->u.float_value); 
  
  case TYPE_MACRO_CONSTANT:
    return (  e1->u.inline_call.inline_declare
              ->u.inline_declare.declare_exp
              ->u.value 
            - e2->u.inline_call.inline_declare
              ->u.inline_declare.declare_exp
              ->u.value
            ); 
  
  case TYPE_MODE_INDEX: 
    return (strcmp(e1->u.mode_index.mode_name, e2->u.mode_index.mode_name));  

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(e1->u.exp - e2->u.exp); 
        
  case TYPE_INLINE_ARGUMENT: 
    return (e1->u.argument - e2->u.argument);  

  case TYPE_QSYNC_HOLDER: 
    if (comp = (e1->u.qsholder.place_index - e2->u.qsholder.place_index)) 
      return(comp); 
    else  
      return(e1->u.qsholder.qsync_var - e2->u.qsholder.qsync_var); 	

  case TYPE_SYNCHRONIZER: 
    if (comp = (e1->u.atom.var - e2->u.atom.var)) 
      return(comp); 
    else  
      return(e1->u.atom.exp_base_proc_index 
      - e2->u.atom.exp_base_proc_index
      ); 	
      
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER: 
    if (comp = (e1->u.atom.var - e2->u.atom.var)) 
      return(comp); 
    else if (comp 
             = (e1->var_status & FLAG_VAR_PRIMED)
             - (e2->var_status & FLAG_VAR_PRIMED)
             )
      return(comp); 
    else if (comp = e1->u.atom.exp_base_proc_index 
             - e2->u.atom.exp_base_proc_index
             )
      return(comp); 
/*
    else if (comp = e1->u.atom.indirect_count - e2->u.atom.indirect_count) 
      return(comp); 
    for (i = 0; i < e1->u.atom.indirect_count; i++) 
      if (comp = e1->u.atom.indirect_exp[i] - e2->u.atom.indirect_exp[i]) 
        return(comp); 
*/
    return(0); 
  
  case TYPE_QFD:
    return(strcmp(e1->u.atom.var_name, e2->u.atom.var_name)); 

  case TYPE_INTERVAL:
    if (comp = e1->u.interval.lbound_exp - e2->u.interval.lbound_exp) 
      return(comp); 
    else if (comp = e1->u.interval.rbound_exp - e2->u.interval.rbound_exp)
      return(comp); 
/*
    else 
      return(e1->u.interval.status - e2->u.interval.status); 
*/
  case BIT_NOT:
    return(e1->u.exp - e2->u.exp); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_MAX:
  case ARITH_MIN:
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    if (comp = ((int) e1->u.arith.lhs_exp) - (int) e2->u.arith.lhs_exp) 
      return(comp); 
    else 
      return(((int) e1->u.arith.rhs_exp) - (int) e2->u.arith.rhs_exp); 

  case ARITH_CONDITIONAL: 
    if (comp = ((int) e1->u.arith_cond.cond) - (int) e2->u.arith_cond.cond) 
      return(comp); 
    else if (comp = ((int) e1->u.arith_cond.if_exp) - (int) e2->u.arith_cond.if_exp) 
      return(comp); 
    else 
      return(((int) e1->u.arith_cond.else_exp) - (int) e2->u.arith_cond.else_exp); 

  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    if (comp = e1->u.ineq.term_count - e2->u.ineq.term_count) 
      return(comp); 
    for (i = 0; i < e1->u.ineq.term_count; i++)  {
      if (comp = e1->u.ineq.term[i].coeff - e2->u.ineq.term[i].coeff) 
        return(comp); 
      else if (comp = e1->u.ineq.term[i].operand - e2->u.ineq.term[i].operand) 
        return(comp); 
    } 
    return(e1->u.ineq.offset - e2->u.ineq.offset); 

  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    if (!(comp = strcmp(
          e1->u.inline_declare.inline_exp_name, 
          e2->u.inline_declare.inline_exp_name
        ) ) ) 
      return(comp); 
    else if (comp = e1->u.inline_declare.formal_argument_count 
                  - e2->u.inline_declare.formal_argument_count 
             ) 
      return(comp); 
    else for (nl1 = e1->u.inline_declare.formal_argument_list, 
              nl2 = e2->u.inline_declare.formal_argument_list;  
              nl1 && nl2; 
              nl1 = nl1->next_name_link, nl2 = nl2->next_name_link 
              ) 
      if (comp = strcmp(nl1->name, nl2->name))  
        return(comp); 

    return(e1->u.inline_declare.declare_exp 
    - e2->u.inline_declare.declare_exp
    ); 
    break; 
    
  case TYPE_INLINE_CALL: 
    if (comp = strcmp( 
          e1->u.inline_declare.inline_exp_name, 
          e2->u.inline_declare.inline_exp_name
        ) ) 
      return(comp); 
    else for (pbu1 = e1->u.inline_call.actual_argument_list, 
              pbu2 = e2->u.inline_call.actual_argument_list;  
              pbu1 && pbu2; 
              pbu1 = pbu1->bnext, pbu2 = pbu2->bnext 
              ) 
      if (comp = pbu1->subexp - pbu2->subexp)  
        return(comp); 

    return(0); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY : 
    if (comp = e1->u.bexp.len - e2->u.bexp.len) 
      return(comp);  
    for (pbu1 = e1->u.bexp.blist, pbu2 = e2->u.bexp.blist; 
	 pbu1; 
	 pbu1 = pbu1->bnext, pbu2 = pbu2->bnext
	 ) { 
      if (comp = pbu1->subexp - pbu2->subexp) 
        return(comp);  
    }
    return(0);

  case ARITH_SUM: 
  case FORALL:
  case EXISTS:
    if (comp = e1->u.qexp.lb_exp - e2->u.qexp.lb_exp) 
      return(comp); 
    else if (comp = e1->u.qexp.ub_exp - e2->u.qexp.ub_exp) 
      return(comp); 
    else if (comp = e1->u.qexp.quantifier_name - e2->u.qexp.quantifier_name) 
      return(comp); 
    else 
      return(e1->u.qexp.child - e2->u.qexp.child);

  case RESET:
    if (comp = strcmp(e1->u.reset.clock_name, e2->u.reset.clock_name)) 
      return(comp); 
    else 
      return(e1->u.reset.child - e2->u.reset.child); 

  case PROJECT:
  case PROJECT_TYPE:
  case PROJECT_PEER:
  case PROJECT_VAR_SIM:
  case PROJECT_CLOCK_SIM:
  case PROJECT_MCHUNK:
    if (comp = e1->u.project.variable_index - e2->u.project.variable_index) 
      return(comp); 
    else 
      return(e1->u.project.child - e2->u.project.child); 

  case PROJECT_TIME:
  case PROJECT_QSYNC: 
  case PROJECT_CLOCK_LOWER_EXTEND:
  case PROJECT_CLOCK_UPPER_EXTEND:
  case PROJECT_LOCAL: 
    return(e1->u.project.child - e2->u.project.child); 

  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY: 
  case EXISTS_ALWAYS:
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE:
  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST:
  
  case TYPE_GAME_SIM: 
    if (comp = e1->u.mexp.path_child - e2->u.mexp.path_child)
      return(comp); 
    else if (comp = e1->u.mexp.dest_child - e2->u.mexp.dest_child) 
      return(comp); 
    else if (comp = e1->u.mexp.time_restriction 
                  - e2->u.mexp.time_restriction
             )
      return(comp); 
    else if (comp = e1->u.mexp.event_restriction 
                  - e2->u.mexp.event_restriction
             )
      return(comp); 
    else if (comp = e1->u.mexp.strong_fairness_count 
                  - e2->u.mexp.strong_fairness_count
             ) 
      return(comp); 
    for (f1 = e1->u.mexp.strong_fairness_list, f2 = e2->u.mexp.strong_fairness_list; 
	 f1; 
	 f1 = f1->next_ps_fairness_link, f2 = f2->next_ps_fairness_link
	 ) { 
      if (comp = f1->fairness - f2->fairness)
      	return(comp);  
    } 
    if (comp = e1->u.mexp.weak_fairness_count - e2->u.mexp.weak_fairness_count)
      return(comp); 
    for (f1 = e1->u.mexp.weak_fairness_list, f2 = e2->u.mexp.weak_fairness_list; 
	 f1; 
	 f1 = f1->next_ps_fairness_link, f2 = f2->next_ps_fairness_link
	 ) { 
      if (comp = f1->fairness - f2->fairness)
      	return(comp);  
    } 
    return(0); 

  case LINEAR_EVENT: 
    if (comp = e1->u.eexp.precond_exp - e2->u.eexp.precond_exp)
      return(comp); 
    if (comp = e1->u.eexp.event_exp - e2->u.eexp.event_exp)
      return(comp); 
    else 
      return (e1->u.eexp.postcond_exp - e2->u.eexp.postcond_exp);
  case RED:
    return(e1->u.rpred.original_red - e2->u.rpred.original_red);
  default: 
    fprintf(RED_OUT, "\nUnexpected expression type %1d in ps_exp_comp()\ne1:", 
      e1->type
    ); 
    pcform(e1); 
    fprintf(RED_OUT, "e2:"); 
    pcform(e2); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* ps_exp_comp() */ 





ps_exp_23tree_set(psub, tree_node)
     struct ps_exp_type		*psub; 
     struct a23tree_type	*tree_node;
{
  psub->a23tree = tree_node; 
}
/* ps_exp_23tree_set() */ 



ps_exp_nop(psub)
     struct ps_exp_type	*psub; 
{

}
/* ps_exp_nop() */ 



ps_exp_count_inc(psub)
  struct ps_exp_type	*psub; 
{
  psub->count++;
}
/* ps_exp_count_inc() */ 





  
char	*ps_exp_type_name(type)
     int	type; 
{
  switch(type) {
  case TYPE_FALSE :
    return("false"); 
  case TYPE_TRUE :
    return("true"); 
  case TYPE_QSYNC_HOLDER: 
    return("QSYNC"); 
  case TYPE_QFD:
    return("QFD"); 
  case TYPE_NULL:
    return("NULL"); 
  case TYPE_LOCAL_IDENTIFIER: 
    return("P"); 
  case TYPE_PEER_IDENTIFIER:
    return("OTHERS"); 
  case TYPE_TRASH: 
    return("DONT_CARE"); 
  case TYPE_CONSTANT:
    return("CONSTANT"); 
  case TYPE_FLOAT_CONSTANT:
    return("FCONSTANT"); 

  case TYPE_PROCESS_COUNT:
    return("#PS"); 

  case TYPE_MODE_INDEX:
    return("INDEX"); 

  case TYPE_REFERENCE: 
    return("REF"); 

  case TYPE_DEREFERENCE: 
    return("DEREF"); 

  case TYPE_SYNCHRONIZER:
    return("SYNC"); 
  case TYPE_DISCRETE:
    return("DISCRETE"); 
  case TYPE_FLOAT:
    return("FLOAT"); 
  case TYPE_DOUBLE:
    return("DOUBLE"); 
  case TYPE_CLOCK:
    return("CLOCK"); 
  case TYPE_DENSE:
    return("DENSE"); 
  case TYPE_POINTER:
    return("POINTER"); 
  case TYPE_BDD: 
    return("BDD"); 

  case TYPE_INTERVAL:
    return("INTERVAL"); 

  case BIT_NOT: 
    return("~"); 
  case BIT_OR: 
    return("|"); 
  case BIT_AND:  
    return("&"); 
  case BIT_SHIFT_RIGHT: 
    return(">>"); 
  case BIT_SHIFT_LEFT: 
    return("<<"); 
    
  case ARITH_ADD: 
    return("+"); 
  case ARITH_MINUS:
    return("-"); 
  case ARITH_MULTIPLY:
    return("*"); 
  case ARITH_DIVIDE:
    return("/"); 
  case ARITH_MODULO: 
    return("%"); 
  case ARITH_MIN: 
    return("MIN"); 
  case ARITH_MAX: 
    return("MAX"); 

  case ARITH_EQ :
  case EQ :
    return("=="); 
  case ARITH_NEQ :
  case NEQ :
    return("!="); 
  case ARITH_LEQ :
  case LEQ :
    return("<="); 
  case ARITH_LESS : 
  case LESS :
    return("<"); 
  case ARITH_GREATER :
  case GREATER :
    return(">"); 
  case ARITH_GEQ :
  case GEQ : 
    return(">="); 

  case ARITH_CONDITIONAL: 
    return("ARITH COND"); 

  case TYPE_INLINE_ARGUMENT: 
    return("INLINE ARGUMENT"); 
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
    return("INLINE BOOLEAN DECLARE"); 
    
  case TYPE_INLINE_DISCRETE_DECLARE: 
    return("INLINE DISCRETE DECLARE"); 
    
  case TYPE_INLINE_CALL: 
    return("INLINE CALL"); 
    
  case AND :
    return("&&"); 
  case OR :
    return("||"); 
  case NOT :
    return("NOT"); 
  case IMPLY : 
    return("IMPLIES"); 

  case FORALL:
    return("FORALL"); 
  case EXISTS:
    return("EXISTS"); 
  case RESET:
    return ("RESET"); 
  case FORALL_ALWAYS: 
    return("FORALL ALWAYS"); 
  case FORALL_EVENTUALLY: 
    return("FORALL EVENTUALLY"); 
  case EXISTS_ALWAYS:
    return("EXISTS ALWAYS"); 
  case EXISTS_EVENTUALLY: 
    return("EXISTS EVENTUALLY"); 
  case EXISTS_CHANGE: 
    return("EXISTS CHANGE"); 
  case FORALL_CHANGE:
    return("FORALL CHANGE"); 
  case EXISTS_UNTIL: 
    return("EXISTS UNTIL"); 
  case FORALL_UNTIL: 
    return("FORALL UNTIL"); 
  case EXISTS_OFTEN: 
    return("EXISTS OFTEN"); 
  case EXISTS_ALMOST: 
    return("EXISTS ALMOST"); 
  case FORALL_OFTEN: 
    return("FORALL OFTEN"); 
  case FORALL_ALMOST:
    return ("FORALL ALMOST"); 
    
  case FORALL_EVENT: 
    return ("FORALL EVENT"); 
  case EXISTS_EVENT: 
    return ("EXISTS EVENT"); 
    
    break; 
  case RED:
    return ("RED"); 
  }
}
  /* ps_exp_type_name() */ 


ps_exp_print(psub, depth)
  struct ps_exp_type	*psub;
  int			depth; 
{
  for (; depth; depth--)
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "%s:%1d:%x\n", 
    ps_exp_type_name(psub->type), psub->count, (unsigned int) psub
  ); 
}
/* ps_exp_print() */


  

  
print_parse_list(list)
     struct parse_variable_type	*list;
{
  struct parse_variable_type	*pv;

  if (!list) 
    return; 
  else if (list == declare_global_discrete_list)
    fprintf(RED_OUT, "\n-----(%d global discrete declarations)-----\n", 
	    GLOBAL_COUNT[TYPE_DISCRETE]
	    );
  else if (list == declare_global_pointer_list)
    fprintf(RED_OUT, "\n-----(%d global pointer declarations)------\n",
	    GLOBAL_COUNT[TYPE_POINTER]
	    ); 
  else if (list == declare_global_clock_list) 
    fprintf(RED_OUT, "\n-----(%d global clock declarations)------\n", 
	    GLOBAL_COUNT[TYPE_CLOCK]
	    ); 
  else if (list == declare_global_synchronizer_list)
    fprintf(RED_OUT, "\n-----(%d global synchronizer declarations)------\n", 
	    GLOBAL_COUNT[TYPE_SYNCHRONIZER]
	    ); 
  else if (list == declare_local_discrete_list) 
    fprintf(RED_OUT, "\n-----(%d local discrete declarations)-----\n",
	    LOCAL_COUNT[TYPE_DISCRETE]
	    ); 
  else if (list == declare_stack_discrete_list) 
    fprintf(RED_OUT, "\n-----(%d stack discrete declarations)-----\n",
	    count_stack_discrete 
	    ); 
  else if (list == declare_local_pointer_list)
    fprintf(RED_OUT, "\n-----(%d local pointer declarations)------\n", 
	    LOCAL_COUNT[TYPE_POINTER]
	    );
  else if (list == declare_local_clock_list) 
    fprintf(RED_OUT, "\n-----(%d local clock declarations)------\n",
	    LOCAL_COUNT[TYPE_CLOCK]
	    ); 
  else if (list == declare_local_synchronizer_list)
    fprintf(RED_OUT, "\n-----(%d local synchronizer declarations)------\n", 
	    GLOBAL_COUNT[TYPE_SYNCHRONIZER]
	    );
  else {
    fprintf(RED_OUT, "\n-----(Unrecoginzed parse variable list)--------\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  for (pv = list; pv; pv = pv->next_parse_variable) {
    fprintf(RED_OUT, "%d : %s, ", pv->index, pv->name); 
    switch (pv->type) { 
    case TYPE_FLOAT: 
      fprintf(RED_OUT, " LB = %.4f; UB = %.4f; Status = %x\n", 
        pv->u.flt.lb, pv->u.flt.ub, pv->status
      ); 
      break; 
    case TYPE_DOUBLE: 
      fprintf(RED_OUT, " LB = %.4f; UB = %.4f; Status = %x\n", 
        pv->u.dble.lb, pv->u.dble.ub, pv->status
      ); 
      break; 
    default: 
      fprintf(RED_OUT, " LB = %1d; UB = %1d; Status = %x\n", 
        pv->u.disc.lb, pv->u.disc.ub, pv->status
      ); 
      break; 
  } }

}
  /* print_parse_list() */



print_sop_fairness_structure(qstring, mstring, psub, depth)
	char			*qstring, *mstring; 
	struct ps_exp_type	*psub; 
	int			depth;
{
  int				i;
  struct ps_fairness_link_type	*fl; 
  
  for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
  fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

  fprintf(RED_OUT, "%s \n", qstring);
  if (psub->u.mexp.strong_fairness_count) {
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "STRONG FAIRNESS: {\n"); 
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      for (i = depth+1; i; i--, fprintf(RED_OUT, "    "));
      print_parse_subformula_structure(fl->fairness, depth+1);
    }
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n"); 
  } 
  if (psub->u.mexp.weak_fairness_count) {
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "WEAK FAIRNESS: {\n"); 
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      for (i = depth+1; i; i--, fprintf(RED_OUT, "    "));
      print_parse_subformula_structure(fl->fairness, depth+1); 
    }
    for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
    fprintf(RED_OUT, "}\n");
  } 

  for (i = depth; i; i--, fprintf(RED_OUT, "    "));
  fprintf(RED_OUT, "%s", mstring); 
}
/* print_sop_fairness_structure() */





print_eop_fairness_structure(qstring, mstring, psub, depth)
	char			*qstring, *mstring; 
	struct ps_exp_type	*psub; 
	int			depth;
{
  int				i;
  struct ps_fairness_link_type	*fl; 
  
  for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
  fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

  fprintf(RED_OUT, "%s \n", qstring);

  for (i = depth; i; i--, fprintf(RED_OUT, "    "));
  fprintf(RED_OUT, "%s", mstring); 
}
/* print_eop_fairness_structure() */




print_time_interval(lb, ub)
	int	lb, ub;
{
  if (lb != 0 || ub != CLOCK_POS_INFINITY) {
    if (lb <= ub) { 
    // Not an NEQ
      if (lb % 2) 
      	fprintf(RED_OUT, "(%1d,", lb/2);
      else
      	fprintf(RED_OUT, "[%1d,", lb/2);
      if (ub == CLOCK_POS_INFINITY) 
        fprintf(RED_OUT, "oo)"); 
      else if (ub % 2) 
        fprintf(RED_OUT, "%1d)", (ub+1)/2);
      else 
        fprintf(RED_OUT, "%1d]", ub/2);
    }
    // an NEQ
    else if (ub == -1) { 
      if (lb % 2)
      	fprintf(RED_OUT, "(%1d,oo)", lb/2); 
      else
      	fprintf(RED_OUT, "[%1d,oo)", lb/2);
    } 
    else if (lb-1==ub+1 && (lb%2)) { 
      fprintf(RED_OUT, "{!=%1d}", lb/2);
    }
    else { 
      ub = ub+1;
      lb = lb-1; 
      if (ub % 2)
      	fprintf(RED_OUT, "~(%1d,", ub/2);
      else 
      	fprintf(RED_OUT, "~[%1d,", ub/2);
      if (lb % 2)
        fprintf(RED_OUT, "%1d)", (lb+1)/2); 
      else
        fprintf(RED_OUT, "%1d]", lb/2); 

    }
  }	
}
/* print_time_interval() */



int	count_print_parse_subformula_structure = 0; 

print_parse_subformula_structure(psub, depth)
     struct ps_exp_type	*psub;
     int		depth;
{
  int				i, vtype, voffset;
  struct ps_bunit_type		*pbu;
  struct ps_fairness_link_type	*fl;

  switch(psub->type) {
  case TYPE_FALSE :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
/*    fprintf(RED_OUT, "TYPE_FALSE\n");
*/
    fprintf(RED_OUT, "%x:TYPE_FALSE\n", (unsigned int) psub);
    return;
  case TYPE_TRUE :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
/*
    fprintf(RED_OUT, "TYPE_TRUE\n");
*/
    fprintf(RED_OUT, "%x:TYPE_TRUE\n", (unsigned int) psub);
    return;
  case TYPE_MACRO_CONSTANT: 
    fprintf(RED_OUT, "%s\n", psub->u.inline_call.inline_exp_name); 
    return; 

  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
/*
    fprintf(RED_OUT, "cppss=%1d;\n", 
      ++count_print_parse_subformula_structure
    ); 
*/
    fprintf(RED_OUT, "%x:vi%d:%s", 
      (unsigned int) psub, psub->u.atom.var_index, psub->u.atom.var_name
    );
    if (   psub->u.atom.exp_base_proc_index
        && psub->u.atom.exp_base_proc_index != PS_EXP_LOCAL_IDENTIFIER
        ) { 
      switch (psub->u.atom.exp_base_proc_index->type) {
      case TYPE_NULL: 
      case 0: 
        fprintf(RED_OUT, "@(0)"); 
	break;
      default: 
/*	  fprintf(RED_OUT, "%s[%x;", psub->u.atom.var_name, 
	    (unsigned int) psub->u.atom.exp_base_proc_index 
	  );
*/
	fprintf(RED_OUT, "@(%x:", (unsigned int) psub->u.atom.exp_base_proc_index);
	print_parse_subformula(psub->u.atom.exp_base_proc_index, 
	  FLAG_GENERAL_PROCESS_IDENTIFIER
	); 
	fprintf(RED_OUT, ")");
	break;
      }
    }
/*
    fprintf(RED_OUT, "%x:@i:%1d;vi:%1d%;bpi:%1d:",
      (unsigned int) psub, psub->u.atom.var->index, psub->u.atom.var_index, psub->u.atom.base_proc_index
    ); 
*/
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      fprintf(RED_OUT, "["); 
      print_parse_subformula(
        psub->u.atom.indirect_exp[i], FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
    }
*/
    break;
  case TYPE_QSYNC_HOLDER: 
    fprintf(RED_OUT, "%x:QSYNC:%1d:%s@%1d:%s", (unsigned int) psub, 
      psub->u.qsholder.place_index, 
      psub->u.qsholder.place_holder_var->name, 
      psub->u.qsholder.qsync_var->index, 
      psub->u.qsholder.qsync_var_name
    ); 
    break; 
  case TYPE_QFD:
    fprintf(RED_OUT, "%x:QFD:%s", (unsigned int) psub, psub->u.atom.var_name);
    break; 
  case TYPE_NULL:
/*
    fprintf(RED_OUT, "NULL");
*/
    fprintf(RED_OUT, "%x:NULL", (unsigned int) psub);
    break;
  case TYPE_LOCAL_IDENTIFIER:
/*
    fprintf(RED_OUT, "P");
*/
    fprintf(RED_OUT, "%x:P", (unsigned int) psub);
    break;
  case TYPE_PEER_IDENTIFIER:
/*
    fprintf(RED_OUT, "~P");
*/ 
    fprintf(RED_OUT, "%x:~P", (unsigned int) psub);
    break;
  case TYPE_TRASH:
/*
    fprintf(RED_OUT, "?");
*/ 
    fprintf(RED_OUT, "%x:?", (unsigned int) psub);
    break;
  case TYPE_CONSTANT:
/*
    fprintf(RED_OUT, "%1d", psub->u.value);
*/
    fprintf(RED_OUT, "%x:%1d", (unsigned int) psub, psub->u.value);
    break;
  case TYPE_FLOAT_CONSTANT:
/*
    fprintf(RED_OUT, "%1d", psub->u.value);
*/
    fprintf(RED_OUT, "%x:%.4f", (unsigned int) psub, psub->u.float_value);
    break;
  case TYPE_MODE_INDEX:
    fprintf(RED_OUT, "%x:mode index:%s", 
      (unsigned int) psub, psub->u.atom.var_name
    );
/* 
    fprintf(RED_OUT, "%x:%1d", (unsigned int) psub, psub->u.value);
*/
    break;

  case TYPE_PROCESS_COUNT:
    fprintf(RED_OUT, "#PS");
    break;

  case TYPE_REFERENCE: 
//    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    if (psub->u.exp->type != ARITH_ADD) { 
      fprintf(RED_OUT, "*(");
      print_parse_subformula_structure(psub->u.exp, depth+1);
      for (i = depth; i; i--, fprintf(RED_OUT, "    "));
      fprintf(RED_OUT, ")");
    }
    else { 
      print_parse_subformula(psub->u.exp->u.arith.lhs_exp, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "["); 
      print_parse_subformula(psub->u.exp->u.arith.rhs_exp, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
    } 
    break;

  case TYPE_DEREFERENCE: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "&(");
    print_parse_subformula_structure(psub->u.exp, depth+1);
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, ")");
    break;

  case TYPE_INTERVAL:
    if (psub->u.interval.status & INTERVAL_LEFT_UNBOUNDED)
      fprintf(RED_OUT, "(-oo,");
    else {
      if (psub->u.interval.status & INTERVAL_LEFT_OPEN)
        fprintf(RED_OUT, "(");
      else
        fprintf(RED_OUT, "[");
      print_parse_subformula(psub->u.interval.lbound_exp, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      );
      fprintf(RED_OUT, ",");
    }
    if (psub->u.interval.status & INTERVAL_RIGHT_UNBOUNDED)
      fprintf(RED_OUT, "oo)");
    else {
      print_parse_subformula(psub->u.interval.rbound_exp, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      );
      if (psub->u.interval.status & INTERVAL_RIGHT_OPEN)
        fprintf(RED_OUT, ")");
      else
        fprintf(RED_OUT, "]");
    }
    break;
  case BIT_NOT: 
    fprintf(RED_OUT, "%x:~(", (unsigned int) psub);
    print_parse_subformula_structure(psub->u.exp, depth);
    fprintf(RED_OUT, ")");
    break;
  
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
/*
    fprintf(RED_OUT, "("); 
*/
    fprintf(RED_OUT, "%x:(", (unsigned int) psub);
    print_parse_subformula_structure(psub->u.arith.lhs_exp, depth);
    print_op(psub->type);
    print_parse_subformula_structure(psub->u.arith.rhs_exp, depth);
    fprintf(RED_OUT, ")");
    break;
    
  case ARITH_MIN: 
/*
    fprintf(RED_OUT, "("); 
*/
    fprintf(RED_OUT, "%x::MIN(", (unsigned int) psub);
    print_parse_subformula_structure(psub->u.arith.lhs_exp, depth);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula_structure(psub->u.arith.rhs_exp, depth);
    fprintf(RED_OUT, ")");
    break;
  case ARITH_MAX: 
/*
    fprintf(RED_OUT, "("); 
*/
    fprintf(RED_OUT, "%x:MAX(", (unsigned int) psub);
    print_parse_subformula_structure(psub->u.arith.lhs_exp, depth);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula_structure(psub->u.arith.rhs_exp, depth);
    fprintf(RED_OUT, ")");
    break;
  case ARITH_EQ :
    if (   psub->u.arith.lhs_exp->type == TYPE_DISCRETE 
        && psub->u.arith.lhs_exp->u.atom.var == var_mode
//        && psub->u.arith.lhs_exp->u.atom.indirect_count == 0 
        && psub->u.arith.rhs_exp->type == TYPE_MODE_INDEX
        ) { 
      fprintf(RED_OUT, "%s[", 
        psub->u.arith.rhs_exp->u.mode_index.mode_name
      ); 
      print_parse_subformula(
        psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
      break; 
    }
    else if (   MODE 
        && psub->u.arith.lhs_exp->type == TYPE_DISCRETE 
        && psub->u.arith.lhs_exp->u.atom.var == var_mode
//        && psub->u.arith.lhs_exp->u.atom.indirect_count == 0 
        && psub->u.arith.rhs_exp->type == TYPE_CONSTANT 
        && psub->u.arith.rhs_exp->u.value >= 0
        && psub->u.arith.rhs_exp->u.value < MODE_COUNT 
        ) { 
      fprintf(RED_OUT, "%s[", 
        MODE[psub->u.arith.rhs_exp->u.value].name
      ); 
      print_parse_subformula(
        psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
      break; 
    }
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));

    fprintf(RED_OUT, "%x:", (unsigned int) psub);

    print_parse_subformula_structure(psub->u.arith.lhs_exp, depth);
    print_op(psub->type);
    print_parse_subformula_structure(psub->u.arith.rhs_exp, depth);
    fprintf(RED_OUT, "\n");
    return;
  case ARITH_CONDITIONAL :
    fprintf(RED_OUT, "\n");
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));

    fprintf(RED_OUT, "%x:(", (unsigned int) psub);

    print_parse_subformula_structure(psub->u.arith_cond.cond, depth);
    fprintf(RED_OUT, ") ? "); 
    print_parse_subformula_structure(psub->u.arith_cond.if_exp, depth+1);
    fprintf(RED_OUT, " : ");
    print_parse_subformula_structure(psub->u.arith_cond.else_exp, depth+1);
    fprintf(RED_OUT, "\n");
    return; 
  case EQ :
    if (   psub->u.ineq.term_count == 1
        && psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT  
        && psub->u.ineq.term[0].coeff->u.value == 1  
        && psub->u.ineq.term[0].operand->type == TYPE_DISCRETE
        && psub->u.ineq.term[0].operand->u.atom.var == var_mode
//        && psub->u.ineq.term[0].operand->u.atom.indirect_count == 0 
        && psub->u.ineq.offset->type == TYPE_MODE_INDEX
        ) { 
      fprintf(RED_OUT, "%s[", 
        psub->u.ineq.offset->u.mode_index.mode_name
      ); 
      print_parse_subformula(
        psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
      break; 
    }
    else if (   MODE 
        && psub->u.ineq.term_count == 1
        && psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT  
        && psub->u.ineq.term[0].coeff->u.value == 1  
        && psub->u.ineq.term[0].operand->type == TYPE_DISCRETE
        && psub->u.ineq.term[0].operand->u.atom.var == var_mode
//        && psub->u.ineq.term[0].operand->u.atom.indirect_count == 0 
        && psub->u.ineq.offset->type == TYPE_CONSTANT 
        && psub->u.ineq.offset->u.value >= 0
        && psub->u.ineq.offset->u.value < MODE_COUNT 
        ) { 
      fprintf(RED_OUT, "%s[", 
        MODE[psub->u.ineq.offset->u.value].name
      ); 
      print_parse_subformula(
        psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fprintf(RED_OUT, "]"); 
      break; 
    }
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));

    fprintf(RED_OUT, "%x:", (unsigned int) psub);

    for (i = 0; i < psub->u.ineq.term_count; i++)  {
      if (psub->u.ineq.term[i].coeff->type == TYPE_CONSTANT) {
        if (psub->u.ineq.term[i].coeff->u.value < 0)
	  if (psub->u.ineq.term[i].coeff->u.value == -1)
	    fprintf(RED_OUT, "-");
	  else
	    fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
	else
	  if (psub->u.ineq.term[i].coeff->u.value == 1) {
	    if (i)
	      fprintf(RED_OUT, "+");
	  }
	  else {
	    if (i)
	      fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
	    else
	      fprintf(RED_OUT, "+%1d ", psub->u.ineq.term[i].coeff->u.value);
	  }
      }
      else {
        if (i) {
          fprintf(RED_OUT, "+(");
	}
	else
          fprintf(RED_OUT, "(");
   	print_parse_subformula_structure(psub->u.ineq.term[i].coeff, 0);
	fprintf(RED_OUT, ")");
      }
      print_parse_subformula_structure(psub->u.ineq.term[i].operand, 0);
    }
    print_op(psub->type);
    print_parse_subformula(psub->u.ineq.offset, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    );
    fprintf(RED_OUT, "\n");
    return;

  case TYPE_INLINE_BOOLEAN_DECLARE: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "inline boolean %s with %1d arguments:", 
      psub->u.inline_declare.inline_exp_name, 
      psub->u.inline_declare.formal_argument_count
    ); 
    if (psub->u.inline_declare.formal_argument_list) { 
      struct name_link_type	*nl; 
      
      fprintf(RED_OUT, "(%s", psub->u.inline_declare.formal_argument_list->name); 
      for (nl = psub->u.inline_declare.formal_argument_list->next_name_link; 
           nl; 
           nl = nl->next_name_link
           ) { 
        fprintf(RED_OUT, ", %s", nl->name); 
      } 
      fprintf(RED_OUT, ") {\n"); 
    } 
    print_parse_subformula_structure(
      psub->u.inline_declare.declare_exp, depth+1
    ); 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n"); 
    return; 
    
  case TYPE_INLINE_DISCRETE_DECLARE: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "inline discrete %s with %1d arguments:", 
      psub->u.inline_declare.inline_exp_name, 
      psub->u.inline_declare.formal_argument_count
    ); 
    if (psub->u.inline_declare.formal_argument_list) { 
      struct name_link_type	*nl; 
      
      fprintf(RED_OUT, "(%s", psub->u.inline_declare.formal_argument_list->name); 
      for (nl = psub->u.inline_declare.formal_argument_list->next_name_link; 
           nl; 
           nl = nl->next_name_link
           ) { 
        fprintf(RED_OUT, ", %s", nl->name); 
      } 
      fprintf(RED_OUT, ") "); 
    } 
    fprintf(RED_OUT, "{\n"); 
    print_parse_subformula_structure(
      psub->u.inline_declare.declare_exp, depth+1
    ); 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n"); 
    return; 
    
  case TYPE_INLINE_CALL: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "inline call %s with %1d arguments:\n", 
      psub->u.inline_call.inline_exp_name, 
      psub->u.inline_call.inline_declare->u.inline_declare.formal_argument_count
    ); 
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         pbu = pbu->bnext
         ) { 
      print_parse_subformula_structure(pbu->subexp, depth+1); 
    } 
    if (psub->u.inline_call.instantiated_exp) { 
      for (i = depth+1; i; i--, fprintf(RED_OUT, "    "));
        fprintf(RED_OUT, "Instantiated expression:\n"); 
      print_parse_subformula_structure(
        psub->u.inline_call.instantiated_exp, 
        depth+2
      ); 
    }
    return; 
    
  case TYPE_INLINE_ARGUMENT: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "inline argument %s\n", psub->u.argument); 
    return(0); 
         
  case AND :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));

    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "{\n");
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      for (i = depth; i; i--, fprintf(RED_OUT, "    "));
      fprintf(RED_OUT, "AND\n");
      print_parse_subformula_structure(pbu->subexp, depth+1);
    }
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n");
    return;
  case OR :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));

    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 


    fprintf(RED_OUT, "{\n");
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      for (i = depth; i; i--, fprintf(RED_OUT, "    "));
      fprintf(RED_OUT, "OR\n");
      print_parse_subformula_structure(pbu->subexp, depth+1);
    }
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n");
    return;
  case NOT :
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 


    fprintf(RED_OUT, "NOT {\n");
    print_parse_subformula_structure(psub->u.bexp.blist->subexp, depth+1);
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n");
    return;
  case IMPLY :
    for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 

    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "{\n");
    print_parse_subformula_structure(psub->u.bexp.blist->subexp, depth+1);
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "IMPLY\n");
    print_parse_subformula_structure(psub->u.bexp.blist->bnext->subexp, depth+1);
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "}\n");
    return;
  case TYPE_MULTIPLE_FAIRNESS: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "|%s:", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.lb_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ",\n"); 
    print_parse_subformula_structure(psub->u.qexp.child, depth+1); 
    return; 
  case ARITH_SUM:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "SUM %s:\n", psub->u.qexp.quantifier_name);
    print_parse_subformula(psub->u.qexp.lb_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ",\n");
    print_parse_subformula_structure(psub->u.qexp.child, depth+1);
    return;
  case FORALL:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "FORALL %s:\n", psub->u.qexp.quantifier_name);
    print_parse_subformula(psub->u.qexp.lb_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ",\n");
    print_parse_subformula_structure(psub->u.qexp.child, depth+1);
    return;
  case EXISTS:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "EXISTS %s:\n", psub->u.qexp.quantifier_name);
    print_parse_subformula(psub->u.qexp.lb_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ",\n");
    print_parse_subformula_structure(psub->u.qexp.child, depth+1);
    return;
  case RESET:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "RESET %s \n", psub->u.reset.clock_name);
    print_parse_subformula_structure(psub->u.reset.child, depth+1); 
    return; 
  case PROJECT:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT %s \n", 
      VAR[psub->u.project.variable_index].NAME
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_MCHUNK:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT M%1d:%1d \n", 
      psub->u.project.variable_index%VARIABLE_COUNT, 
      psub->u.project.variable_index/VARIABLE_COUNT 
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_VAR_SIM:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 
    voffset = psub->u.project.variable_index / DISP_PROJECT_VAR_SIM; 
    vtype = psub->u.project.variable_index % DISP_PROJECT_VAR_SIM; 
    fprintf(RED_OUT, "PROJECT local vars %s of all procs\n", 
      VAR[variable_index[vtype][1][voffset]].NAME
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_CLOCK_SIM:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT local clocks %s of all procs\n", 
      VAR[
        variable_index[TYPE_CLOCK][1][psub->u.project.variable_index]
      ].NAME
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_PEER:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT PEER %1d \n", 
      psub->u.project.variable_index 
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_TIME:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT TIME \n"); 
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_CLOCK_LOWER_EXTEND:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT TIME BCK \n"); 
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_CLOCK_UPPER_EXTEND:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT TIME FWD\n"); 
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_TYPE:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT TYPE %1d \n", 
      psub->u.project.variable_index
    );
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_QSYNC: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT QSYNC \n"); 
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case PROJECT_LOCAL:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "PROJECT LOCAL \n"); 
    print_parse_subformula_structure(psub->u.project.child, depth+1); 
    return; 
  case FORALL_ALWAYS: 
    print_sop_fairness_structure("FORALL", "ALWAYS", psub, depth);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, "\n");
/*
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n"); 
*/
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return; 
  case FORALL_EVENTUALLY: 
    print_sop_fairness_structure("FORALL", "EVENTUALLY", psub, depth);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, "\n"); 
/* 
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n"); 
*/
    print_parse_subformula_structure(psub->u.mexp.dest_child, depth+1);
    return;
  case EXISTS_ALWAYS:
    print_sop_fairness_structure("EXISTS", "ALWAYS", psub, depth);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, "\n");
/* 
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n"); 
*/ 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return; 
  case EXISTS_EVENTUALLY: 
    print_sop_fairness_structure("EXISTS", "EVENTUALLY", psub, depth); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, "\n"); 
/*
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n");
*/ 
    print_parse_subformula_structure(psub->u.mexp.dest_child, depth+1); 
    return;
  case EXISTS_CHANGE: 
    print_sop_fairness_structure("EXISTS", "CHANGE", psub, depth); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, "\n"); 
/* 
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n"); 
*/ 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return;
  case FORALL_CHANGE:
    print_sop_fairness_structure("FORALL", "CHANGE", psub, depth);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, "\n");
/*
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n");
*/ 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return; 
  case EXISTS_UNTIL: 
///*
    for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 
//*/
    fprintf(RED_OUT, "EXISTS \n");
    if (psub->u.mexp.strong_fairness_count) { 
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "STRONG FAIRNESS: {\n");
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) 
        print_parse_subformula_structure(fl->fairness, depth+1);
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "}\n");
    }
    if (psub->u.mexp.weak_fairness_count) { 
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "WEAK FAIRNESS: {\n"); 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) 
        print_parse_subformula_structure(fl->fairness, depth+1);
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "}\n"); 
    } 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "UNTIL"); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, "\n");
/* 
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n"); 
*/ 
    print_parse_subformula_structure(psub->u.mexp.dest_child, depth+1); 
    return; 
  case FORALL_UNTIL: 
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    if (psub->exp_status & FLAG_EXP_MODAL_INSIDE) 
      fprintf(RED_OUT, "M:"); 
    else 
      fprintf(RED_OUT, "-:"); 

    fprintf(RED_OUT, "FORALL\n");
    if (psub->u.mexp.strong_fairness_count) { 
      for (i = depth; i; i--, fprintf(RED_OUT, "    "));
      fprintf(RED_OUT, "STRONG FAIRNESS: {\n");
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link)
        print_parse_subformula_structure(fl->fairness, depth+1); 
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "}\n"); 
    } 
    if (psub->u.mexp.weak_fairness_count) { 
      for (i = depth; i; i--, fprintf(RED_OUT, "    "));
      fprintf(RED_OUT, "WEAK FAIRNESS: {\n");
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) 
        print_parse_subformula_structure(fl->fairness, depth+1); 
      for (i = depth; i; i--, fprintf(RED_OUT, "    ")); 
      fprintf(RED_OUT, "}\n");
    }
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1);
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "UNTIL");
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " EVENT {"); 
      print_parse_subformula_structure(psub->u.mexp.event_restriction, depth+1); 
      fprintf(RED_OUT, "}"); 
    } 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, "\n"); 
/* 
    red_print_graph_depth(psub->u.mexp.red_modal_constraint, depth+1); 
    fprintf(RED_OUT, "\n");
*/ 
    print_parse_subformula_structure(psub->u.mexp.dest_child, depth+1);
    return; 
  case EXISTS_OFTEN: 
    print_sop_fairness_structure("EXISTS", "OFTEN", psub, depth);
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return;
  case EXISTS_ALMOST: 
    print_sop_fairness_structure("EXISTS", "ALMOST", psub, depth); 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return; 
  case FORALL_OFTEN: 
    print_sop_fairness_structure("FORALL", "OFTEN", psub, depth); 
    fprintf(RED_OUT, "\n"); 
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1); 
    return; 
  case FORALL_ALMOST:
    print_sop_fairness_structure("FORALL", "ALMOST", psub, depth);
    print_parse_subformula_structure(psub->u.mexp.path_child, depth+1);
    return;
    
   
  case RED:
    for (i = depth; i; i--, fprintf(RED_OUT, "    "));
    fprintf(RED_OUT, "%x:", (unsigned int) psub);
    red_print_graph_depth(psub->u.rpred.red, depth+1);
    break; 
  }
}
  /* print_parse_subformula_structure() */ 




print_sop_fairness(qstring, mstring, psub) 
	char			*qstring, *mstring;
	struct ps_exp_type	*psub; 
{
  struct ps_fairness_link_type	*fl;
  
  fprintf(RED_OUT, "%s ", qstring); 
  if (psub->u.mexp.strong_fairness_count) {
    fprintf(RED_OUT, "strong {"); 
    for (fl = psub->u.mexp.strong_fairness_list; 
         fl; 
         fl = fl->next_ps_fairness_link
         ) {
      print_parse_subformula(fl->fairness, 0); 
      fprintf(RED_OUT, ";"); 
    }
    fprintf(RED_OUT, "}"); 
  } 
  if (psub->u.mexp.weak_fairness_count) { 
    fprintf(RED_OUT, "weak {"); 
    for (fl = psub->u.mexp.weak_fairness_list; 
         fl; 
         fl = fl->next_ps_fairness_link
         ) {
      print_parse_subformula(fl->fairness, 0); 
      fprintf(RED_OUT, ";"); 
    }
    fprintf(RED_OUT, "}"); 
  } 

  fprintf(RED_OUT, " %s", mstring); 
}
/* print_sop_fairness() */ 






print_eop_fairness(qstring, mstring, psub) 
	char			*qstring, *mstring;
	struct ps_exp_type	*psub; 
{
  struct ps_fairness_link_type	*fl;
  
  fprintf(RED_OUT, "%s ", qstring); 
  fprintf(RED_OUT, " %s", mstring); 
}
/* print_eop_fairness() */ 




char	*flexible_parse_mode_name(int mi) {
  if (mi < 0 || mi >= MODE_COUNT) { 
    fprintf(RED_OUT, "\nError: Illegal mode index %1d\n", mi); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  else if (MODE) { 
    return(MODE[mi].name); 
  } 
  else { 
    struct parse_mode_type	*pm; 
    
    for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
      if (pm->index == mi) 
        return(pm->name); 
    } 
    fprintf(RED_OUT, "\nError: Missing mode index %1d\n", mi); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* flexible_parse_mode_name() */



/* If pi == FLAG_GENERAL_PROCESS_IDENTIFIER, then 
 * every time a local identifier or the local process identifier symbol P
 * is used, we just print P. 
 */
int	count_bug_oo = 0; 

print_parse_subformula(psub, pi)
     struct ps_exp_type	*psub;
     int		pi; 
{
  int				i, vtype, voffset;
  struct ps_bunit_type		*pbu;
  struct ps_fairness_link_type	*fl;

  switch(psub->type) {
  case TYPE_FALSE :
    fprintf(RED_OUT, "false");
    return;
  case TYPE_TRUE :
    fprintf(RED_OUT, "true");
    return;
  case TYPE_MACRO_CONSTANT: 
    fprintf(RED_OUT, "%s", psub->u.inline_call.inline_exp_name); 
    return; 
  case TYPE_REFERENCE: 
    if (psub->u.exp->type != ARITH_ADD) { 
      fprintf(RED_OUT, "*(");
      print_parse_subformula(psub->u.exp, pi);
      fprintf(RED_OUT, ")"); 
    }
    else { 
      print_parse_subformula(psub->u.exp->u.arith.lhs_exp, pi);
      fprintf(RED_OUT, "["); 
      print_parse_subformula(psub->u.exp->u.arith.rhs_exp, pi);
      fprintf(RED_OUT, "]"); 
    } 
    break;

  case TYPE_DEREFERENCE: 
    fprintf(RED_OUT, "&(");
    print_parse_subformula(psub->u.exp, pi);
    fprintf(RED_OUT, ")");
    break;

  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, "%s", psub->u.atom.var_name);
    if (psub->u.atom.exp_base_proc_index != PS_EXP_GLOBAL_IDENTIFIER) { 
      fprintf(RED_OUT, "@("); 
      print_parse_subformula(psub->u.atom.exp_base_proc_index, 0); 
      fprintf(RED_OUT, ")");
    }
    break; 

  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
    fprintf(RED_OUT, "%s", psub->u.atom.var_name);
    if (psub->u.atom.var && (psub->u.atom.var->status & FLAG_VAR_STACK)) { 
      if (   psub->u.atom.exp_base_proc_index
          && psub->u.atom.exp_base_proc_index != PS_EXP__SP
          ) { 
        switch (psub->u.atom.exp_base_proc_index->type) {
        case TYPE_NULL: 
        case 0: 
          fprintf(RED_OUT, "@+(0)"); 
	  break;
        default: 
/*	    fprintf(RED_OUT, "%s[%x;", psub->u.atom.var_name, 
	      (unsigned int) psub->u.atom.exp_base_proc_index 
	    );
*/
          fprintf(RED_OUT, "@+("); 
	  print_parse_subformula(psub->u.atom.exp_base_proc_index, pi); 
	  fprintf(RED_OUT, ")");
	  break;
        }
      }
    }
    else if (   psub->u.atom.var 
             && (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)
             && psub->u.atom.exp_base_proc_index
             && psub->u.atom.exp_base_proc_index != PS_EXP_LOCAL_IDENTIFIER
             ) { 
      switch (psub->u.atom.exp_base_proc_index->type) {
      case TYPE_NULL: 
      case 0: 
        fprintf(RED_OUT, "@(0)"); 
	break;
      default: 
/*	  fprintf(RED_OUT, "%s[%x;", psub->u.atom.var_name, 
	    (unsigned int) psub->u.atom.exp_base_proc_index 
	  );
*/
        fprintf(RED_OUT, "@("); 
	print_parse_subformula(psub->u.atom.exp_base_proc_index, pi); 
	fprintf(RED_OUT, ")");
	break;
      }
    }
/*
    fprintf(RED_OUT, "%x:@i:%1d;vi:%1d%;bpi:%1d:",
      (unsigned int) psub, psub->u.atom.var->index, psub->u.atom.var_index, psub->u.atom.base_proc_index
    ); 
*/
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      fprintf(RED_OUT, "["); 
      print_parse_subformula(
        psub->u.atom.indirect_exp[i], pi
      ); 
      fprintf(RED_OUT, "]"); 
    }
*/
    break;

  case TYPE_QSYNC_HOLDER: 
/*
    fprintf(RED_OUT, "%1d:%s@%1d:%s", 
	    psub->u.qsholder.place_index, 
	    psub->u.qsholder.place_holder_var->name, 
	    psub->u.qsholder.qsync_var->index, 
	    psub->u.qsholder.qsync_var_name
	    ); 
*/
    fprintf(RED_OUT, "%s", psub->u.qsholder.qsync_var_name); 
    break; 
  case TYPE_QFD:
    fprintf(RED_OUT, "%s", psub->u.atom.var_name);
    break; 
  case TYPE_NULL:
    fprintf(RED_OUT, "NULL");
    break;
  case TYPE_LOCAL_IDENTIFIER:
    if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) 
      fprintf(RED_OUT, "P");
    else 
      fprintf(RED_OUT, "%1d", pi); 
    break;
  case TYPE_PEER_IDENTIFIER:
    if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) 
      fprintf(RED_OUT, "~P");
    else 
      fprintf(RED_OUT, "(~%1d)", pi); 
    break;
  case TYPE_TRASH:
    fprintf(RED_OUT, "?");
    break;
  case TYPE_CONSTANT:
    fprintf(RED_OUT, "%1d", psub->u.value);
    break;
  case TYPE_FLOAT_CONSTANT:
    fprintf(RED_OUT, "%.4f", psub->u.float_value);
    break;
  case TYPE_MODE_INDEX:
    fprintf(RED_OUT, "index %s", psub->u.mode_index.mode_name);
    break;
  case TYPE_PROCESS_COUNT:
    fprintf(RED_OUT, "#PS");
    break;
  case TYPE_INTERVAL:
    if (psub->u.interval.status & INTERVAL_LEFT_UNBOUNDED)
      fprintf(RED_OUT, "(-oo,");
    else {
      if (psub->u.interval.status & INTERVAL_LEFT_OPEN)
        fprintf(RED_OUT, "(");
      else
        fprintf(RED_OUT, "[");
      print_parse_subformula(psub->u.interval.lbound_exp, pi);
      fprintf(RED_OUT, ",");
    }
    if (psub->u.interval.status & INTERVAL_RIGHT_UNBOUNDED)
      fprintf(RED_OUT, "oo)");
    else {
      print_parse_subformula(psub->u.interval.rbound_exp, pi);
      if (psub->u.interval.status & INTERVAL_RIGHT_OPEN)
        fprintf(RED_OUT, ")");
      else
        fprintf(RED_OUT, "]");
    }
    break;
  case BIT_NOT: 
    fprintf(RED_OUT, "~(");
    print_parse_subformula(psub->u.exp, pi);
    fprintf(RED_OUT, ")");
    break; 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    fprintf(RED_OUT, "(");
    print_parse_subformula(psub->u.arith.lhs_exp, pi);
    print_op(psub->type);
    print_parse_subformula(psub->u.arith.rhs_exp, pi);
    fprintf(RED_OUT, ")");
    break; 
  case ARITH_MAX: 
    fprintf(RED_OUT, "max(");
    print_parse_subformula(psub->u.arith.lhs_exp, pi);
    fprintf(RED_OUT, ", ");
    print_parse_subformula(psub->u.arith.rhs_exp, pi);
    fprintf(RED_OUT, ")");
    break; 
  case ARITH_MIN: 
    fprintf(RED_OUT, "min(");
    print_parse_subformula(psub->u.arith.lhs_exp, pi);
    fprintf(RED_OUT, ", ");
    print_parse_subformula(psub->u.arith.rhs_exp, pi);
    fprintf(RED_OUT, ")");
    break; 
  case ARITH_CONDITIONAL :
    fprintf(RED_OUT, "(("); 
    print_parse_subformula(psub->u.arith_cond.cond, pi);
    fprintf(RED_OUT, ")?"); 
    print_parse_subformula(psub->u.arith_cond.if_exp, pi);
    fprintf(RED_OUT, ":");
    print_parse_subformula(psub->u.arith_cond.else_exp, pi);
    fprintf(RED_OUT, ")"); 
    return; 
  case ARITH_EQ :
    if (   psub->u.arith.lhs_exp->type == TYPE_DISCRETE 
        && psub->u.arith.lhs_exp->u.atom.var == var_mode
//        && psub->u.arith.lhs_exp->u.atom.indirect_count == 0 
        ) { 
      if (psub->u.arith.rhs_exp->type == TYPE_MODE_INDEX) { 
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            fprintf(RED_OUT, "%s@(P)", 
              psub->u.arith.rhs_exp->u.mode_index.mode_name
            );
          }
          else {
            fprintf(RED_OUT, "%s@(%1d)", 
              psub->u.arith.rhs_exp->u.mode_index.mode_name, pi 
            ); 
          }
        else { 
          fprintf(RED_OUT, "%s@(", 
            psub->u.arith.rhs_exp->u.mode_index.mode_name
          ); 
          print_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pi 
          ); 
          fprintf(RED_OUT, ")"); 
        }
        break; 
      }
      else if (psub->u.arith.rhs_exp->type == TYPE_CONSTANT) { 
      	char	*mname; 
      	
      	mname = flexible_parse_mode_name(psub->u.arith.rhs_exp->u.value); 
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            fprintf(RED_OUT, "%s@(P)", mname);
          }
          else {
            fprintf(RED_OUT, "%s@(%1d)", mname, pi); 
          }
        else { 
          fprintf(RED_OUT, "%s@(", mname); 
          print_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pi 
          ); 
          fprintf(RED_OUT, ")"); 
        }
        break; 
      }
    }
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "%x:", psub->status);
    #endif 
    print_parse_subformula(psub->u.arith.lhs_exp, pi);
    print_op(psub->type);
    print_parse_subformula(psub->u.arith.rhs_exp, pi); 
    return;

  case EQ :
    if (   psub->u.ineq.term_count == 1
        && psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT  
        && psub->u.ineq.term[0].coeff->u.value == 1  
        && psub->u.ineq.term[0].operand->type == TYPE_DISCRETE
        && psub->u.ineq.term[0].operand->u.atom.var == var_mode
//        && psub->u.ineq.term[0].operand->u.atom.indirect_count == 0 
        ) { 
      if (psub->u.ineq.offset->type == TYPE_MODE_INDEX) { 
        if (psub->u.ineq.term[0].operand->u.atom.exp_base_proc_index->type  
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            fprintf(RED_OUT, "%s[P]", 
              psub->u.ineq.offset->u.mode_index.mode_name
            );
          }
          else {
            fprintf(RED_OUT, "%s[%1d]", 
              psub->u.ineq.offset->u.mode_index.mode_name, pi 
            ); 
          }
        else { 
          fprintf(RED_OUT, "%s[", 
            psub->u.ineq.offset->u.mode_index.mode_name
          ); 
          print_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pi 
          ); 
          fprintf(RED_OUT, "]"); 
        }
        break; 
      }
      else if (psub->u.ineq.offset->type == TYPE_CONSTANT) { 
        if (psub->u.ineq.term[0].operand->u.atom.exp_base_proc_index->type  
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (pi == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            fprintf(RED_OUT, "%s[P]", 
              MODE[psub->u.ineq.offset->u.value].name
            );
          }
          else {
            fprintf(RED_OUT, "%s[%1d]", 
              MODE[psub->u.ineq.offset->u.value].name, pi 
            ); 
          }
        else { 
          fprintf(RED_OUT, "%s[", 
            MODE[psub->u.ineq.offset->u.value].name
          ); 
          print_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pi 
          ); 
          fprintf(RED_OUT, "]"); 
        }
        break; 
      }
    }
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
/*
    fprintf(RED_OUT, "%x:", psub->status);
*/
    if (psub->u.ineq.term_count == 0) { 
      fprintf(RED_OUT, "0"); 
    } 
    else for (i = 0; i < psub->u.ineq.term_count; i++)  {
      if (psub->u.ineq.term[i].coeff->type == TYPE_CONSTANT) {
        if (psub->u.ineq.term[i].coeff->u.value < 0)
          if (psub->u.ineq.term[i].coeff->u.value == -1)
          	fprintf(RED_OUT, "-");
          else
            fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
        else
          if (psub->u.ineq.term[i].coeff->u.value == 1) {
            if (i)
              fprintf(RED_OUT, "+");
          }
          else {
            if (i)
              fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
            else
              fprintf(RED_OUT, "+%1d ", psub->u.ineq.term[i].coeff->u.value);
          }
      }
      else {
        if (i) {
          fprintf(RED_OUT, "+(");
        }
        else
          fprintf(RED_OUT, "(");
        print_parse_subformula(psub->u.ineq.term[i].coeff, pi);
        fprintf(RED_OUT, ")");
      }
      print_parse_subformula(psub->u.ineq.term[i].operand, pi);
    }
    print_op(psub->type);
    print_parse_subformula(psub->u.ineq.offset, pi);
    return;
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
    fprintf(RED_OUT, "inline boolean %s", 
      psub->u.inline_declare.inline_exp_name
    ); 
    if (psub->u.inline_declare.formal_argument_list) { 
      struct name_link_type	*nl; 
      
      fprintf(RED_OUT, "(%s", psub->u.inline_declare.formal_argument_list->name); 
      for (nl = psub->u.inline_declare.formal_argument_list->next_name_link; 
           nl; 
           nl = nl->next_name_link
           ) { 
        fprintf(RED_OUT, ", %s", nl->name); 
      } 
      fprintf(RED_OUT, ")"); 
    } 
    fprintf(RED_OUT, " {"); 
    print_parse_subformula(psub->u.inline_declare.declare_exp, pi); 
    fprintf(RED_OUT, "}"); 
    return; 
    
  case TYPE_INLINE_DISCRETE_DECLARE: 
    fprintf(RED_OUT, "inline discrete %s", 
      psub->u.inline_declare.inline_exp_name, 
      psub->u.inline_declare.formal_argument_count
    ); 
    if (psub->u.inline_declare.formal_argument_list) { 
      struct name_link_type	*nl; 
      
      fprintf(RED_OUT, "(%s", psub->u.inline_declare.formal_argument_list->name); 
      for (nl = psub->u.inline_declare.formal_argument_list->next_name_link; 
           nl; 
           nl = nl->next_name_link
           ) { 
        fprintf(RED_OUT, ", %s", nl->name); 
      } 
      fprintf(RED_OUT, ") "); 
    } 
    fprintf(RED_OUT, "{"); 
    print_parse_subformula(psub->u.inline_declare.declare_exp, pi); 
    fprintf(RED_OUT, "}"); 
    return; 
    
  case TYPE_INLINE_CALL: 
    fprintf(RED_OUT, "%s", psub->u.inline_call.inline_exp_name); 
    if (pbu = psub->u.inline_call.actual_argument_list) { 
      fprintf(RED_OUT, "("); 
      print_parse_subformula(pbu->subexp, pi); 
      for (pbu = pbu->bnext; pbu; pbu = pbu->bnext) { 
      	fprintf(RED_OUT, ", "); 
        print_parse_subformula(pbu->subexp, pi); 
      }
      fprintf(RED_OUT, ")"); 
    } 
    return; 
    
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "%s", psub->u.argument); 
    return(0); 
         
  case AND :
    pbu = psub->u.bexp.blist;
    fprintf(RED_OUT, "("); 
    print_parse_subformula(pbu->subexp, pi);
    fprintf(RED_OUT, ")");
    for (pbu = pbu->bnext; pbu; pbu = pbu->bnext) {
      fprintf(RED_OUT, "&&(");
      print_parse_subformula(pbu->subexp, pi);
      fprintf(RED_OUT, ")");
    }
    return;
  case OR :
    pbu = psub->u.bexp.blist;
    fprintf(RED_OUT, "(");
    print_parse_subformula(pbu->subexp, pi);
    fprintf(RED_OUT, ")");
    for (pbu = pbu->bnext; pbu; pbu = pbu->bnext) {
      fprintf(RED_OUT, "||("); 
      print_parse_subformula(pbu->subexp, pi); 
      fprintf(RED_OUT, ")"); 
    }
    return; 
  case NOT :
    fprintf(RED_OUT, "not(");
    print_parse_subformula(psub->u.bexp.blist->subexp, pi); 
    fprintf(RED_OUT, ")"); 
    return;
  case IMPLY :
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.bexp.blist->subexp, pi); 
    fprintf(RED_OUT, ")implies(");
    print_parse_subformula(psub->u.bexp.blist->bnext->subexp, pi); 
    fprintf(RED_OUT, ")");
    return;
  case TYPE_MULTIPLE_FAIRNESS: 
    fprintf(RED_OUT, "|%s:", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.lb_exp, pi);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, pi);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula(psub->u.qexp.child, pi); 
    return; 
  case ARITH_SUM: 
    fprintf(RED_OUT, "SUM %s:", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.lb_exp, pi);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, pi);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula(psub->u.qexp.child, pi); 
    return; 
  case FORALL: 
    fprintf(RED_OUT, "forall %s:", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.lb_exp, pi);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, pi);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula(psub->u.qexp.child, pi); 
    return; 
  case EXISTS: 
    fprintf(RED_OUT, "exists %s:", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.lb_exp, pi);
    fprintf(RED_OUT, ".."); 
    print_parse_subformula(psub->u.qexp.ub_exp, pi);
    fprintf(RED_OUT, ", "); 
    print_parse_subformula(psub->u.qexp.child, pi);
    return;
  case RESET:
    fprintf(RED_OUT, "reset %s (", psub->u.reset.clock_name); 
    print_parse_subformula(psub->u.reset.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case PROJECT:
    fprintf(RED_OUT, "project %s (", 
      VAR[psub->u.project.variable_index].NAME
    );
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case PROJECT_MCHUNK:
    fprintf(RED_OUT, "project M%1d:%1d (", 
      psub->u.project.variable_index%VARIABLE_COUNT, 
      psub->u.project.variable_index/VARIABLE_COUNT       
    );
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case PROJECT_VAR_SIM:
    voffset = psub->u.project.variable_index / DISP_PROJECT_VAR_SIM; 
    vtype = psub->u.project.variable_index % DISP_PROJECT_VAR_SIM; 
    fprintf(RED_OUT, "project local vars %s of all procs\n", 
      VAR[variable_index[vtype][1][voffset]].NAME
    );
    print_parse_subformula(psub->u.project.child, pi); 
    return; 
  case PROJECT_CLOCK_SIM:
    fprintf(RED_OUT, "project local clocks %s of all procs\n", 
      VAR[
        variable_index[TYPE_CLOCK][1][psub->u.project.variable_index]
      ].NAME
    );
    print_parse_subformula(psub->u.project.child, pi); 
    return; 
  case PROJECT_TYPE:
    fprintf(RED_OUT, "project type %1d (", 
      psub->u.project.variable_index
    );
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case PROJECT_PEER:
    fprintf(RED_OUT, "project peer %1d (", 
      psub->u.project.variable_index
    );
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case PROJECT_TIME:
    fprintf(RED_OUT, "project time (");
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 

  case PROJECT_CLOCK_LOWER_EXTEND:
    fprintf(RED_OUT, "project time bck (");
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 

  case PROJECT_CLOCK_UPPER_EXTEND:
    fprintf(RED_OUT, "project time fwd (");
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 

  case PROJECT_QSYNC:
    fprintf(RED_OUT, "project qsync (");
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
 
  case PROJECT_LOCAL:
    fprintf(RED_OUT, "project local (");
    print_parse_subformula(psub->u.project.child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
 
  case FORALL_ALWAYS: 
    print_sop_fairness("forall", "always", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, "event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    print_parse_subformula(psub->u.mexp.path_child, pi); 
    return; 
  case FORALL_EVENTUALLY:
    print_sop_fairness("forall", "eventually", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " ");
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, "event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    print_parse_subformula(psub->u.mexp.dest_child, pi);
    return; 
  case EXISTS_ALWAYS: 
    print_sop_fairness("exists", "always", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, "event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    print_parse_subformula(psub->u.mexp.path_child, pi);
    return; 
  case EXISTS_EVENTUALLY:
    print_sop_fairness("EXISTS", "EVENTUALLY", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, "event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    print_parse_subformula(psub->u.mexp.dest_child, pi); 
    return; 
  case EXISTS_UNTIL: 
    fprintf(RED_OUT, "exists "); 
    if (psub->u.mexp.strong_fairness_count) {
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        print_parse_subformula(fl->fairness, pi);
        fprintf(RED_OUT, ";"); 
      }
      fprintf(RED_OUT, "}"); 
    } 
    if (psub->u.mexp.weak_fairness_count) {
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        print_parse_subformula(fl->fairness, pi); 
        fprintf(RED_OUT, ";");
      }
      fprintf(RED_OUT, "}"); 
    }
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi); 
    fprintf(RED_OUT, ")until"); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.dest_child, pi);
    fprintf(RED_OUT, ")"); 
    return;
  case FORALL_UNTIL: 
    fprintf(RED_OUT, "forall "); 
    if (psub->u.mexp.strong_fairness_count) { 
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        print_parse_subformula(fl->fairness, pi); 
        fprintf(RED_OUT, ";");
      }
      fprintf(RED_OUT, "}"); 
    }
    if (psub->u.mexp.weak_fairness_count) {
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        print_parse_subformula(fl->fairness, pi); 
        fprintf(RED_OUT, ";"); 
      }
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi);
    fprintf(RED_OUT, ")until"); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.dest_child, pi); 
    fprintf(RED_OUT, ")"); 
    return;
  case EXISTS_CHANGE:
    print_sop_fairness("exists", "change", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "(");
    print_parse_subformula(psub->u.mexp.path_child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case FORALL_CHANGE: 
    print_sop_fairness("forall", "change", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi);
    fprintf(RED_OUT, ")"); 
    return; 
  case EXISTS_OFTEN: 
    print_sop_fairness("exists", "often", psub); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi);
    fprintf(RED_OUT, ")"); 
    return;
  case EXISTS_ALMOST: 
    print_sop_fairness("exists", "almost", psub); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case FORALL_OFTEN:
    print_sop_fairness("forall", "often ", psub); 
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi);
    fprintf(RED_OUT, ")"); 
    return; 
  case FORALL_ALMOST: 
    print_sop_fairness("forall", "almost", psub);
    if (psub->u.mexp.event_restriction) { 
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.mexp.event_restriction, pi); 
      fprintf(RED_OUT, "}"); 
    } 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.mexp.path_child, pi); 
    fprintf(RED_OUT, ")"); 
    return; 
  case LINEAR_EVENT: 
    fprintf(RED_OUT, "linear "); 
    print_parse_subformula(psub->u.eexp.precond_exp, pi); 
    if (psub->u.eexp.event_exp) {
      fprintf(RED_OUT, " event {"); 
      print_parse_subformula(psub->u.eexp.event_exp, pi); 
      fprintf(RED_OUT, "} "); 
      print_parse_subformula(psub->u.eexp.postcond_exp, pi); 
    }
    return; 
  case TYPE_GAME_SIM: 
    print_sop_fairness("GAME SIMULATE ", "", psub);
    fprintf(RED_OUT, "\n"); 
    return;
  case RED: 
    red_print_line(psub->u.rpred.red);
    break; 
  }
}
  /* print_parse_subformula() */ 




pcform(psub)
	struct ps_exp_type	*psub; 
{ 
  print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
} 
  /* pcform() */ 


void	print_ps_exp_list(struct ps_bunit_type *list) { 
  fprintf(RED_OUT, "\nA ps_exp_type list:\n"); 
  for (; list; list = list->bnext) 
    pcform(list->subexp); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
}
  /* print_ps_exp_list() */  



/*************************************************
 *  The following pointer is for a stack that stores the 
 *  enumeration values of quantified variables. 
 */
struct ps_bunit_type	*STACK_QUANTIFIED_VALUE_TOP = NULL; 


void	push_quantified_value_stack(
  struct ps_exp_type	*p 
) { 
  struct ps_bunit_type	*s; 
  
  s = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
  s->subexp = p; 
  s->bnext = STACK_QUANTIFIED_VALUE_TOP; 
  STACK_QUANTIFIED_VALUE_TOP = s; 
}
  /* push_quantified_value_stack() */ 
  
  

void	pop_quantified_value_stack(
  struct ps_exp_type	*p 
) { 
  struct ps_bunit_type	*s; 
  
  if (p != STACK_QUANTIFIED_VALUE_TOP->subexp) {
    fprintf(RED_OUT, "\nERROR: Inconsistent quantified value stack top.\n"); 
    fflush(RED_OUT); 
    bk(0); 	
  }
  s = STACK_QUANTIFIED_VALUE_TOP->bnext; 
  free(STACK_QUANTIFIED_VALUE_TOP); 
  STACK_QUANTIFIED_VALUE_TOP = s; 
}
  /* pop_quantified_value_stack() */ 
  
  

int	qfd_variable_index(var, qname) 
     struct parse_variable_type	*var; 
     char			*qname;
{
  struct ps_bunit_type	*scope;

  for (scope = STACK_QUANTIFIED_VALUE_TOP; 
       scope; 
       scope = scope->bnext
       )
    if (!strcmp(scope->subexp->u.qexp.quantifier_name, qname))
      break;

  if (scope) {
    return(variable_index[var->type]
      [scope->subexp->u.qexp.value]
      [var->index]
    );
  }
  else {
    fprintf(RED_OUT, "\nBug: how comes that an unquantified variable %s can happen here.\n", qname);
    fflush(RED_OUT); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0);

  }
}
/* qfd_variable_index() */





int	qfd_value(char *qname) {
  struct ps_bunit_type	*scope;

  for (scope = STACK_QUANTIFIED_VALUE_TOP; 
       scope; 
       scope = scope->bnext
       )
    if (!strcmp(scope->subexp->u.qexp.quantifier_name, qname))
      break;

  if (scope) {
    return(scope->subexp->u.qexp.value);
  }
  else {
    fprintf(RED_OUT, "\nBug: how comes that an unquantified variable %s can happen here.\n", qname);
    fflush(RED_OUT); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0);

  }
}
/* qfd_value() */




#ifdef RED_DEBUG_EXP_MODE
int	count_exp_share = 0; 
#endif 


struct ps_exp_type	*ps_exp_share(
  struct ps_exp_type	*psub
) { 
  struct ps_exp_type	*result; 
  struct ps_bunit_type	*pbu; 
  int			flag; 
  
  #ifdef RED_DEBUG_EXP_MODE
//  if (psub == tmp_exp_comp) { 
    fprintf(RED_OUT, "\n==(%1d)==sharing %x=============\n", 
      ++count_exp_share, (unsigned int) psub
    ); 
    pcform(psub); 
    fflush(RED_OUT); 	
//  } 
  #endif 

  flag = psub->exp_status & FLAG_TCTCTL_SUBFORM; 
  result = (struct ps_exp_type *) 
    add_23tree(psub, EXP_TREE, ps_exp_comp, ps_exp_free,
      ps_exp_nop, ps_exp_23tree_set, ps_exp_print
    ); 
  result->exp_status = result->exp_status | flag; 

  #ifdef RED_DEBUG_EXP_MODE
  if (result == psub) 
    fprintf(RED_OUT, "New shared psub %x:%1d\n", (unsigned int) psub, psub->type); 
  else 
    fprintf(RED_OUT, "Old shared psub %x:%1d\n", (unsigned int) result, result->type); 
  #endif 
  #ifdef RED_DEBUG_EXP_MODE
  switch (result->type) {
  case AND: 
  case OR: 
  case IMPLY: 
  case NOT: 

    for (pbu = result->u.bexp.blist; pbu; pbu = pbu->bnext) 
      if (pbu == tmp_bunit_comp) { 
        fprintf(RED_OUT, 
          "\nSHARE: Caught sharing tmp_bunit_comp = %x at %x:%1d\n", 
          (unsigned int) pbu, (unsigned int) result, result->type
        ); 
        pcform(result); 
        fflush(RED_OUT); 
        target_exp = result; 
      } 
      else if (pbu == tmp_bunit_comp2) { 
        fprintf(RED_OUT, 
          "\nSHARE: Caught sharing tmp_bunit_comp2 = %x at %x:%1d\n", 
          (unsigned int) pbu, (unsigned int) result, result->type
        ); 
        pcform(result); 
        fflush(RED_OUT); 
        target_exp2 = result; 
      } 
    break; 
  } 
  #endif 

  return(result); 
}
  /* ps_exp_share() */ 


 
 
int	PI_GET_LAZY; 

int	rec_get_lazy_proc(
  struct ps_exp_type	*exp
) { 
  int 			pi1, pi2, ti, llb, lub, ulb, uub;
  float			flb, fub; 
  struct ps_bunit_type	*b; 

  switch (exp->type) {
  case TYPE_CONSTANT:
  case TYPE_MACRO_CONSTANT:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_INLINE_ARGUMENT: 
  case TYPE_QSYNC_HOLDER: 
    return(0); 
  case TYPE_INTERVAL: 
    pi1 = rec_get_lazy_proc(exp->u.interval.lbound_exp);
    pi2 = rec_get_lazy_proc(exp->u.interval.rbound_exp); 
    if (pi1 > pi2) { 
      return(pi1); 
    } 
    else 
      return(pi2); 

  case TYPE_REFERENCE: 
    return(0); 
    break; 
  case TYPE_DEREFERENCE: 
    if (get_integer_range(exp->u.exp->u.atom.exp_base_proc_index, 
          PI_GET_LAZY, &pi1, &pi2, &flb, &fub  
        ) != FLAG_SPECIFIC_VALUE) { 
      fprintf(RED_OUT, "\nERROR: Illegal process index value.\n"); 
      pcform(exp->u.exp->u.atom.exp_base_proc_index); 
      bk(0); 
    } 
    if (pi1 < pi2) 
      pi1 = pi2; 
    pi2 = rec_get_lazy_proc(exp->u.exp->u.atom.exp_base_proc_index);
    if (pi1 < pi2) 
      pi1 = pi2; 
    if (pi1 <= 0 || pi1 > PROCESS_COUNT) 
      pi1 = PROCESS_COUNT; 
    return(pi1); 
    break; 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
  case TYPE_POINTER: 
    if (get_integer_range(exp->u.atom.exp_base_proc_index, 
          PI_GET_LAZY, &pi1, &pi2, &flb, &fub 
        ) != FLAG_SPECIFIC_VALUE) { 
      return(PROCESS_COUNT);
//      fprintf(RED_OUT, "\nWARNING: Illegal process index value:  \n"); 
//      pcform(exp); 
//      bk(0); 
    } 
    if (pi1 < pi2) 
      pi1 = pi2; 
/*
    pi2 = rec_get_lazy_proc(exp->u.atom.exp_base_proc_index);
    if (pi1 < pi2) 
      pi1 = pi2; 
*/
    if (pi1 <= 0 || pi1 > PROCESS_COUNT) 
      pi1 = PROCESS_COUNT; 
    return(pi1); 

  case BIT_NOT: 
    if (get_integer_range(exp->u.exp, PI_GET_LAZY, &pi1, &pi2, &flb, &fub)
        != FLAG_SPECIFIC_VALUE
        ) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal Boolean operations on ambiguous or floatings.\n"
      ); 
      bk(0);  
    } 
    if (pi1 < pi2) 
      pi1 = pi2; 
    pi2 = rec_get_lazy_proc(exp->u.atom.exp_base_proc_index);
    if (pi1 < pi2) 
      pi1 = pi2; 
    if (pi1 <= 0 || pi1 > PROCESS_COUNT) 
      pi1 = PROCESS_COUNT; 
    return(pi1); 
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_EQ: 
  case ARITH_NEQ: 
  case ARITH_LESS: 
  case ARITH_LEQ: 
  case ARITH_GEQ: 
  case ARITH_GREATER: 
    pi1 = rec_get_lazy_proc(exp->u.arith.lhs_exp);
    pi2 = rec_get_lazy_proc(exp->u.arith.rhs_exp); 
    if (pi1 > pi2) { 
      return(pi1); 
    } 
    else 
      return(pi2); 

  case ARITH_CONDITIONAL: 
    pi1 = rec_get_lazy_proc(exp->u.arith_cond.if_exp);
    pi2 = rec_get_lazy_proc(exp->u.arith_cond.else_exp);
    if (pi1 < pi2) 
      pi1 = pi2; 
    pi2 = rec_get_lazy_proc(exp->u.arith_cond.cond); 
    if (pi1 > pi2) { 
      return(pi1); 
    } 
    else 
      return(pi2); 
    break; 
  case EQ: 
  case NEQ: 
  case LEQ: 
  case LESS: 
  case GEQ: 
  case GREATER: 
    pi1 = 0; 
    for (ti = 0; ti < exp->u.ineq.term_count; ti++) { 
      pi2 = rec_get_lazy_proc(exp->u.ineq.term[ti].coeff); 
      if (pi2 > pi1) 
        pi1 = pi2;  
      pi2 = rec_get_lazy_proc(exp->u.ineq.term[ti].operand); 
      if (pi2 > pi1) 
        pi1 = pi2;  
    } 
    pi2 = rec_get_lazy_proc(exp->u.ineq.offset);
    if (pi1 > pi2) 
      return(pi1); 
    else 
      return(pi2); 
    break; 
  
  case TYPE_INLINE_CALL: 
    return(rec_get_lazy_proc(exp->u.inline_call.instantiated_exp));
  
  case IMPLY:     
  case NOT: 
  case AND: 
  case OR: 
    pi1 = 0; 
    for (b = exp->u.bexp.blist; b; b = b->bnext) { 
      pi2 = rec_get_lazy_proc(b->subexp); 
      if (pi1 < pi2) 
        pi1 = pi2; 
    } 
    return(pi1); 

  case FORALL: 
  case EXISTS: {
    float	flb, fub; 

    if (get_integer_range(
          exp->u.qexp.lb_exp, PI_GET_LAZY, &llb, &lub, &flb, &fub
        ) != FLAG_SPECIFIC_VALUE) { 
      fprintf(RED_OUT, "\nERROR: Illegal types of range indices. \n"); 
      bk(0); 
    }
    if (get_integer_range(
          exp->u.qexp.ub_exp, PI_GET_LAZY, &ulb, &uub, &flb, &fub
        ) != FLAG_SPECIFIC_VALUE) { 
      fprintf(RED_OUT, "\nERROR: Illegal types of range indices. \n"); 
      bk(0); 
    }
    pi1 = rec_get_lazy_proc(exp->u.qexp.lb_exp); 
    pi2 = rec_get_lazy_proc(exp->u.qexp.ub_exp); 
    if (pi1 < pi2) 
      pi1 = pi2; 
    push_quantified_value_stack(exp); 
    for (exp->u.qexp.value = llb; 
         exp->u.qexp.value <= uub; 
         exp->u.qexp.value++
         ) { 
      pi2 = rec_get_lazy_proc(exp->u.qexp.child); 
      if (pi1 < pi2) 
        pi1 = pi2; 
    } 
    pop_quantified_value_stack(exp); 
    return(pi1); 
    break; 
  }
  default:
    fprintf(RED_OUT, 
      "\nError: Illegal expression type %1d in rec_get_lazy_proc()!\n", 
      exp->type
    );
    bk(); 
  }
} 
  /* rec_get_lazy_proc() */ 



int	get_lazy_proc(
  struct ps_exp_type	*exp, 
  int			pi
) { 
  PI_GET_LAZY = pi; 
  return(rec_get_lazy_proc(exp)); 
} 
  /* get_lazy_proc() */ 






struct red_type	*lazy_subtree(
  struct red_type	*false_child, 
  struct red_type	*true_child, 
  int			pi, 
  struct ps_exp_type	*lazy_exp
) {
  int			vid;  
  struct red_type	*d; 
  
  vid = variable_index[TYPE_LAZY_EXP][pi][0]; 
  if (   (   false_child != NORM_FALSE 
          && false_child != NORM_NO_RESTRICTION 
          && (   (vid > false_child->var_index)
              || (   (vid == false_child->var_index) 
                  && (ps_exp_comp(lazy_exp, false_child->u.lazy.exp) >= 0)
          )   )   ) 
      || (   true_child != NORM_FALSE 
          && true_child != NORM_NO_RESTRICTION 
          && (   (vid > true_child->var_index)
              || (   (vid == true_child->var_index) 
                  && (ps_exp_comp(lazy_exp, true_child->u.lazy.exp) >= 0)
      )   )   )   ) {  
    fprintf(RED_OUT, "\nERROR: Variable out of order in lazy_subtree()\n"); 
    fprintf(RED_OUT, "\n**************************************************\n"); 
    pcform(lazy_exp); 
//    fprintf(RED_OUT, "\n----------------------------\nfalse_child:\n"); 
//    red_print_graph(false_child); 
//    fprintf(RED_OUT, "\n----------------------------\ntrue_child:\n"); 
//    red_print_graph(true_child); 
    fflush(RED_OUT); 
    bk(0); 
  }
  else if (true_child == false_child) 
    return(true_child); 
  else if (lazy_exp == PS_EXP_FALSE) 
    return(false_child); 
  else if (lazy_exp == PS_EXP_TRUE)
    return(true_child); 
  d = red_alloc(vid); 
  d->u.lazy.exp = lazy_exp; 
  d->u.lazy.false_child = false_child; 
  d->u.lazy.true_child = true_child; 

  return(red_share(d)); 
}
/* lazy_subtree() */ 




struct red_type	*lazy_2_cases(
  struct red_type	*false_child, 
  struct red_type	*true_child, 
  int			pi, 
  struct ps_exp_type	*lazy_exp
) {
  int			vid;  
  struct red_type	*fcase, *tcase; 
  
  if (false_child == true_child) 
    return(false_child); 
  
  vid = variable_index[TYPE_LAZY_EXP][pi][0]; 
  if (   (   false_child == NORM_FALSE 
          || false_child == NORM_NO_RESTRICTION 
          || vid < false_child->var_index 
          )
      && (   true_child == NORM_FALSE 
          || true_child == NORM_NO_RESTRICTION 
          || vid < true_child->var_index 
      )   ) { 
    return(lazy_subtree(false_child, true_child, pi, lazy_exp)); 
  }
    
  if (   (vid > false_child->var_index)
      || (   (vid == false_child->var_index) 
          && (ps_exp_comp(lazy_exp, false_child->u.lazy.exp) >= 0)
      )   ) { 
    fcase = lazy_one_neg_constraint(false_child, pi, lazy_exp); 
  } 
  else 
    fcase = NULL; 
  if (   (vid > true_child->var_index)
      || (   (vid == true_child->var_index) 
          && (ps_exp_comp(lazy_exp, true_child->u.lazy.exp) >= 0)
      )   ) {
    tcase = lazy_one_constraint(true_child, pi, lazy_exp); 
  }
  else 
    tcase = NULL; 
      
  if (fcase || tcase) { 
    if (!fcase) { 
      fcase = lazy_subtree(false_child, NORM_FALSE, pi, lazy_exp); 
    } 
    if (!tcase) { 
      tcase = lazy_subtree(NORM_FALSE, true_child, pi, lazy_exp); 
    } 
    return(red_bop(OR, fcase, tcase)); 
  } 
  else 
    return(lazy_subtree(false_child, true_child, pi, lazy_exp)); 
}
/* lazy_2_cases() */ 




struct ps_exp_type	*LAZY_CONSTRAINT_EXP; 
int			LAZY_CONSTRAINT_PI, LAZY_CONSTRAINT_VI, 
			FLAG_LAZY_POS; 
struct red_type		*LAZY_CONSTRAINT_ATOM; 

int	count_lazy_one_constraint = 0; 

struct red_type	*rec_lazy_one_constraint(d)
     struct red_type	*d;
{
  int				ci, ub, lb, comp;
  struct red_type		*new_child, *result;
  struct cache2_hash_entry_type	*ce; 
/*
  fprintf(RED_OUT, "\nLAZY ONE CONSTRAINT %1d, polarity %1d, pi=%1d, vi=%1d:\n", 
    ++count_lazy_one_constraint, 
    FLAG_LAZY_POS, 
    LAZY_CONSTRAINT_PI,  
    LAZY_CONSTRAINT_VI
  ); 
  pcform(LAZY_CONSTRAINT_EXP); 
  red_print_graph(d); 
  fflush(RED_OUT); 
*/
  if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(AND, d, LAZY_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 
  else if (
     d == NORM_NO_RESTRICTION 
  || d->var_index > LAZY_CONSTRAINT_VI
  || (   d->var_index == LAZY_CONSTRAINT_VI
      && (comp = ps_exp_comp(d->u.lazy.exp, LAZY_CONSTRAINT_EXP)) > 0
  )   )
    if (FLAG_LAZY_POS) 
      return(lazy_subtree(NORM_FALSE, d, LAZY_CONSTRAINT_PI, 
        LAZY_CONSTRAINT_EXP 
      ) );
    else 
      return(lazy_subtree(d, NORM_FALSE, LAZY_CONSTRAINT_PI, 
        LAZY_CONSTRAINT_EXP 
      ) );
  else if (d->var_index == LAZY_CONSTRAINT_VI && comp == 0) { 
    if (FLAG_LAZY_POS) 
      return(lazy_subtree(
        NORM_FALSE, 
        d->u.lazy.true_child, 
        LAZY_CONSTRAINT_PI, 
        LAZY_CONSTRAINT_EXP 
      ) );
    else 
      return(lazy_subtree(
        d->u.lazy.false_child, 
        NORM_FALSE, 
        LAZY_CONSTRAINT_PI, 
        LAZY_CONSTRAINT_EXP 
      ) );
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    new_child = bdd_new(d->var_index, 
      rec_lazy_one_constraint(d->u.bdd.zero_child), 
      rec_lazy_one_constraint(d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_lazy_one_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    new_child = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_lazy_one_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
    }
    new_child = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;
  case TYPE_LAZY_EXP: 
    new_child = lazy_subtree( 
      rec_lazy_one_constraint(d->u.lazy.false_child), 
      rec_lazy_one_constraint(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp  
    ); 
    break; 
    
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_lazy_one_constraint(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child,
        d->u.fdd.arc[ci].lower_bound,
        d->u.fdd.arc[ci].upper_bound
      );
    }
    new_child = fdd_new(d->var_index);
    break; 
    
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_lazy_one_constraint(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child,
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound
      );
    }
    new_child = dfdd_new(d->var_index);
    break; 
    
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_lazy_one_constraint(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child,
        d->u.ddd.arc[ci].lower_bound,
        d->u.ddd.arc[ci].upper_bound
      );
    }
    new_child = ddd_new(d->var_index);
  }
  return(ce->result = new_child);
}
  /* rec_lazy_one_constraint() */


struct red_type	*lazy_one_constraint(
     struct red_type	*d, 
     int		pi, 
     struct ps_exp_type	*lazy_exp
) {
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  LAZY_CONSTRAINT_PI = pi; 
  LAZY_CONSTRAINT_VI = variable_index[TYPE_LAZY_EXP][pi][0];
  FLAG_LAZY_POS = TYPE_TRUE; 
  LAZY_CONSTRAINT_EXP = lazy_exp; 
  LAZY_CONSTRAINT_ATOM = lazy_subtree(NORM_FALSE, NORM_NO_RESTRICTION, 
    pi, lazy_exp 
  ); 
  result = rec_lazy_one_constraint(d);
  return(result);
}
/* lazy_one_constraint() */



 


struct red_type	*lazy_one_neg_constraint(
     struct red_type	*d, 
     int		pi, 
     struct ps_exp_type	*lazy_exp
) {
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  LAZY_CONSTRAINT_PI = pi; 
  LAZY_CONSTRAINT_VI = variable_index[TYPE_LAZY_EXP][pi][0];
  FLAG_LAZY_POS = TYPE_FALSE; 
  LAZY_CONSTRAINT_EXP = lazy_exp; 
  LAZY_CONSTRAINT_ATOM = lazy_subtree(NORM_NO_RESTRICTION, NORM_FALSE, 
    pi, lazy_exp 
  ); 
  result = rec_lazy_one_constraint(d);
  return(result);
}
/* lazy_one_neg_constraint() */



 
struct ps_exp_type	*exp_var_fillin(
  struct ps_exp_type	*psub, 
  int			type, 
  int			vflags, 
  int			eflags, 
  int			vi,  
  char			*name 
) { 
  psub->type = type; 
  psub->var_status = vflags; 
  psub->exp_status = eflags; 
  if (vi >= 0) { 
    psub->u.atom.var_name = name;
    psub->u.atom.var_index = vi; 
    psub->u.atom.var = var_search(name); 
    psub->exp_status = psub->exp_status 
    | (VAR[vi].STATUS & MASK_VARIABLE_FLAGS); 
    psub->u.atom.var->status; 
    if (VAR[vi].STATUS & FLAG_LOCAL_VARIABLE) 
      psub->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER;  
    else 
      psub->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
  }
  else { 
    psub->u.atom.var_name = name;
    psub->u.atom.var = var_search(name); 
    psub->exp_status = psub->exp_status | psub->u.atom.var->status; 
    if (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE) { 
      psub->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER;  
      if (variable_index) 
        psub->u.atom.var_index 
        = variable_index[psub->u.atom.var->type][1][psub->u.atom.var->index]; 
    }
    else {
      psub->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
      if (variable_index) 
        psub->u.atom.var_index 
        = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index];
  } } 
/*
  psub->u.atom.indirect_count = 0; 
  psub->u.atom.indirect_exp = NULL; 
  psub->u.atom.indirect_vi = NULL; 
*/
  return(ps_exp_share(psub)); 
}
  /* exp_var_fillin() */  



struct ps_exp_type	*exp_atom(
  int	type, 
  int	value, // when this is a variable, -1: means no VI is given.
               // if value >= 0, it means a real VI.  
  char	*name
) {
  struct ps_exp_type *psub;

  switch (type) {
  case TYPE_NULL: 
    psub = ps_exp_alloc(type);
    psub->var_status = 0; 
    psub->exp_status = FLAG_CONSTANT; 
    return(ps_exp_share(psub)); 
  case TYPE_LOCAL_IDENTIFIER: 
    return(PS_EXP_LOCAL_IDENTIFIER); 
  case TYPE_CONSTANT:
    psub = ps_exp_alloc(type);
    psub->u.value = value; 
    return(ps_exp_share(psub)); 
  case TYPE_BDD: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_BDD, 0, value, name));
  case TYPE_SYNCHRONIZER: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_SYNCHRONIZER, 0, value, name));
  case TYPE_CLOCK: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_CLOCK, 0, value, name));
  case TYPE_DENSE: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_DENSE, 0, value, name));
  case TYPE_FLOAT: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_FLOAT, 0, value, name));
  case TYPE_DOUBLE: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_DOUBLE, 0, value, name));
  case TYPE_DISCRETE: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_DISCRETE, 0, value, name));
  case TYPE_POINTER: 
    psub = ps_exp_alloc(type);
    return(exp_var_fillin(psub, type, FLAG_POINTER, 0, value, name));
  }
}
  /* exp_atom() */ 
  

struct ps_exp_type	*exp_ref(
  struct ps_exp_type	*e
) { 
  struct ps_exp_type	*r; 
  
  r = ps_exp_alloc(TYPE_REFERENCE); 
  r->var_status = e->var_status; 
  r->exp_status = e->exp_status; 
  r->u.exp = e; 
  return(ps_exp_share(r)); 
} 
  /* exp_ref() */ 



struct ps_exp_type	*exp_deref(
  struct ps_exp_type	*e
) { 
  struct ps_exp_type	*r; 
  
  r = ps_exp_alloc(TYPE_DEREFERENCE); 
  r->var_status = e->var_status; 
  r->exp_status = e->exp_status; 
  r->u.exp = e; 
  return(ps_exp_share(r)); 
} 
  /* exp_deref() */ 




int	PI_INSTANTIATE; 

struct ps_exp_type	*rec_ps_exp_instantiate(); 

struct ps_fairness_link_type	*ps_exp_seq_instantiate(list) 
	struct ps_fairness_link_type	*list; 
{ 
  struct ps_fairness_link_type	*fl, *nfl, dummy_fl, *fl_tail;

  fl_tail = &dummy_fl; 
  for (fl = list; fl; fl = fl->next_ps_fairness_link) { 
    nfl = (struct ps_fairness_link_type *) malloc(sizeof(struct ps_fairness_link_type)); 
    fl_tail->next_ps_fairness_link = nfl; 
    fl_tail = nfl; 
    nfl->fairness = rec_ps_exp_instantiate(fl->fairness); 
  } 
  fl_tail->next_ps_fairness_link = NULL; 
  return(dummy_fl.next_ps_fairness_link); 
}
  /* ps_exp_seq_instantiate() */  

   
  
  
  
void	insert_sorted_blist_dummy_head(
  int			type, 
  struct ps_exp_type	*subexp, 
  struct ps_bunit_type	*dummy_head, 
  int			*bcount_ptr 
) { 
  struct ps_bunit_type	*pbu, *nbu, *bu; 
  
  switch (type) {
  case AND: 
    if (subexp == PS_EXP_TRUE) 
      return; 
    break; 
    
  case OR: 
    if (subexp == PS_EXP_FALSE) 
      return; 
    break; 	
  } 
  for (pbu = dummy_head, nbu = pbu->bnext; 
       nbu && nbu->subexp < subexp; 
       pbu = nbu, nbu = nbu->bnext
       ) ; 
       
  if (nbu == NULL || nbu->subexp > subexp) { 
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = subexp; 
    bu->bnext = nbu; 
    pbu->bnext = bu; 
    (*bcount_ptr)++; 	
  } 
} 
  /* insert_sorted_blist_dummy_head() */ 


  
struct ps_fairness_link_type	*insert_sorted_flist(
  struct ps_exp_type		*fairness, 
  int				status,  
  struct ps_fairness_link_type	*list, 
  int				*fcount_ptr  
) { 
  struct ps_fairness_link_type	*pfl, *nfl, *fl, dummy_fl; 
  
  dummy_fl.next_ps_fairness_link = list; 
  for (pfl = &dummy_fl, nfl = pfl->next_ps_fairness_link; 
       nfl && nfl->fairness < fairness; 
       pfl = nfl, nfl = nfl->next_ps_fairness_link
       ) ; 

  if (nfl == NULL || nfl->fairness > fairness) { 
    fl = (struct ps_fairness_link_type *) 
      malloc(sizeof(struct ps_fairness_link_type)); 
    fl->fairness = fairness; 
    fl->red_fairness = NULL; 
    fl->status = status; 
    fl->next_ps_fairness_link = nfl; 
    pfl->next_ps_fairness_link = fl; 
    (*fcount_ptr)++; 
  } 
  return(dummy_fl.next_ps_fairness_link); 
} 
  /* insert_sorted_flist() */ 
   
  
  



  
struct ps_exp_type	*rec_ps_exp_instantiate(psub)
     struct ps_exp_type	*psub; 
{
  int				i;
  struct ps_exp_type		*newsub, *texp; 
  struct ps_bunit_type		*pbu, *nbu, dummy_bu, *bu_tail;
//  struct parse_indirect_type	*pt;

  if (!psub) 
    return(NULL); 
    
  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_QSYNC_HOLDER: 
  case TYPE_QFD:
  case TYPE_NULL:
  case TYPE_PROCESS_COUNT: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_CONSTANT:
  case TYPE_MODE_INDEX: 
    return(psub); 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_ps_exp_instantiate(psub->u.exp); 
    return(ps_exp_share(newsub)); 
  
  case TYPE_LOCAL_IDENTIFIER:
    return(exp_atom(TYPE_CONSTANT, PI_INSTANTIATE, NULL)); 
    
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.atom.exp_base_proc_index = rec_ps_exp_instantiate(psub->u.atom.exp_base_proc_index); 
/*
    newsub->u.atom.indirect_exp = ps_exp_indirect_exp_copy(
      psub->u.atom.indirect_exp, psub->u.atom.indirect_count 
    ); 
    if (psub->u.atom.indirect_vi) {
      newsub->u.atom.indirect_vi = (int *) 
        malloc((PROCESS_COUNT+1) * sizeof(int) 
      ); 
      for (i = 1; i <= PROCESS_COUNT; i++) 
        newsub->u.atom.indirect_vi[i] = psub->u.atom.indirect_vi[i]; 
    } 
*/
    return(ps_exp_share(newsub)); 

  case TYPE_INTERVAL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.interval.lbound_exp = rec_ps_exp_instantiate(psub->u.interval.lbound_exp);  
    newsub->u.interval.rbound_exp = rec_ps_exp_instantiate(psub->u.interval.rbound_exp);  
    return(ps_exp_share(newsub)); 

  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_ps_exp_instantiate(psub->u.exp);  
    return(ps_exp_share(newsub)); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = bit_op_value(psub->type, 
        newsub->u.arith.lhs_exp->u.value, 
        newsub->u.arith.rhs_exp->u.value
      ); 
    }
    if (   (psub->type == BIT_OR || psub->type == BIT_AND)
        && newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp
        ) {
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 
  case ARITH_ADD:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = newsub->u.arith.lhs_exp->u.value + newsub->u.arith.rhs_exp->u.value; 
    }
    else if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 
  case ARITH_MINUS:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = newsub->u.arith.lhs_exp->u.value - newsub->u.arith.rhs_exp->u.value; 
    }
    return(ps_exp_share(newsub)); 
  case ARITH_MULTIPLY:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = newsub->u.arith.lhs_exp->u.value * newsub->u.arith.rhs_exp->u.value; 
    }
    else if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 
  case ARITH_DIVIDE:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (newsub->u.arith.rhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->u.value == 0
        ) { 
      fprintf(RED_OUT, "ERROR: ZERO divisor while instantiating formula for process %1d:\n", 
	      PI_INSTANTIATE
	      ); 
      print_parse_subformula(psub, 
        FLAG_GENERAL_PROCESS_IDENTIFIER
      ); 
      fflush(RED_OUT); 
      bk(0); 
    }
    else if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
             && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
             ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = newsub->u.arith.lhs_exp->u.value / newsub->u.arith.rhs_exp->u.value; 
    }
    return(ps_exp_share(newsub)); 
  case ARITH_MODULO: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (newsub->u.arith.rhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->u.value == 0
        ) { 
      fprintf(RED_OUT, "ERROR: ZERO divisor while instantiating formula for process %1d:\n", 
	      PI_INSTANTIATE
	      ); 
      print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fflush(RED_OUT); 
      bk(0); 
    }
    else if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
             && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
             ) { 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = newsub->u.arith.lhs_exp->u.value % newsub->u.arith.rhs_exp->u.value; 
    }
    return(ps_exp_share(newsub)); 
  case ARITH_EQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          == newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 

  case ARITH_NEQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          != newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 

  case ARITH_LEQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          <= newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      newsub->type = ARITH_GEQ; 
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 

  case ARITH_LESS :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          < newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      newsub->type = ARITH_GREATER; 
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 

  case ARITH_GREATER :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          > newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      newsub->type = ARITH_LESS; 
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 
  case ARITH_GEQ : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = rec_ps_exp_instantiate(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp = rec_ps_exp_instantiate(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT 
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (newsub->u.arith.lhs_exp->u.value 
          >= newsub->u.arith.rhs_exp->u.value
          ) {
      	free(newsub); 
        newsub = PS_EXP_TRUE; 
      }
      else {
      	free(newsub); 
        newsub = PS_EXP_FALSE; 
      }
      return(newsub); 
    }
    if (newsub->u.arith.lhs_exp > newsub->u.arith.rhs_exp) {
      newsub->type = ARITH_LEQ; 
      texp = newsub->u.arith.lhs_exp; 
      newsub->u.arith.lhs_exp = newsub->u.arith.rhs_exp;
      newsub->u.arith.rhs_exp = texp;
    }   
    return(ps_exp_share(newsub)); 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.ineq.offset = rec_ps_exp_instantiate(psub->u.ineq.offset); 
    newsub->u.ineq.term = (struct parse_term_type *) 
			  malloc(psub->u.ineq.term_count * sizeof(struct parse_term_type)); 
    for (i = 0; i < psub->u.ineq.term_count; i++)  {
      newsub->u.ineq.term[i].coeff = rec_ps_exp_instantiate(psub->u.ineq.term[i].coeff); 
      newsub->u.ineq.term[i].operand = rec_ps_exp_instantiate(psub->u.ineq.term[i].operand); 
    } 
    return(ps_exp_share(newsub));

  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith_cond.cond 
    = rec_ps_exp_instantiate(psub->u.arith_cond.cond); 
    newsub->u.arith_cond.if_exp 
    = rec_ps_exp_instantiate(psub->u.arith_cond.if_exp); 
    newsub->u.arith_cond.else_exp 
    = rec_ps_exp_instantiate(psub->u.arith_cond.else_exp); 
    return(ps_exp_share(newsub)); 

  case TYPE_INLINE_ARGUMENT: 
    return(psub); 
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    fprintf(RED_OUT, "This should not happen here.\n"); 
    fflush(RED_OUT); 
    bk(0); 
    
  case TYPE_INLINE_CALL: 
    return(rec_ps_exp_instantiate(psub->u.inline_call.instantiated_exp)); 

  case AND :
  case OR :
  case NOT :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL;  
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      insert_sorted_blist_dummy_head(
        psub->type, 
        rec_ps_exp_instantiate(pbu->subexp), 
        &dummy_bu, &(newsub->u.bexp.len)
      ); 
    }
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub));

  case IMPLY : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    bu_tail = &dummy_bu;  
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      nbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
      bu_tail->bnext = nbu; 
      bu_tail = nbu; 
      bu_tail->subexp = rec_ps_exp_instantiate(pbu->subexp); 
    }
    bu_tail->bnext = NULL; 
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub));

  case FORALL:
  case EXISTS:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.qexp.lb_exp = rec_ps_exp_instantiate(psub->u.qexp.lb_exp);
    newsub->u.qexp.ub_exp = rec_ps_exp_instantiate(psub->u.qexp.ub_exp);
    newsub->u.qexp.child = rec_ps_exp_instantiate(psub->u.qexp.child);
    return (ps_exp_share(newsub));

  case RESET:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = rec_ps_exp_instantiate(psub->u.reset.child); 
    return (ps_exp_share(newsub)); 

  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY: 
  case EXISTS_ALWAYS:
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE:
  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.strong_fairness_list 
    = ps_exp_seq_instantiate(psub->u.mexp.strong_fairness_list, newsub); 
    newsub->u.mexp.weak_fairness_list 
    = ps_exp_seq_instantiate(psub->u.mexp.weak_fairness_list, newsub); 

    newsub->u.mexp.path_child 
    = rec_ps_exp_instantiate(psub->u.mexp.path_child);

    newsub->u.mexp.dest_child 
    = rec_ps_exp_instantiate(psub->u.mexp.dest_child);
    
    newsub->u.mexp.time_restriction  
    = rec_ps_exp_instantiate(psub->u.mexp.time_restriction);
    
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction  
      = rec_ps_exp_instantiate(psub->u.mexp.event_restriction);
    
    return (ps_exp_share(newsub)); 
    
  case RED:
    return(psub);
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: unexpted exp type %1d in ps_exp_instantiate().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* rec_ps_exp_instantiate() */ 



struct ps_exp_type	*ps_exp_instantiate(psub, pi)
     struct ps_exp_type	*psub; 
     int		pi; 
{ 
  PI_INSTANTIATE = pi; 
  return(rec_ps_exp_instantiate(psub)); 	
}
  /* ps_exp_instantiate() */ 
  
  


  


struct ps_exp_type	*exp_boolean( 
  int			type,  
  struct ps_exp_type	*e1, 
  struct ps_exp_type	*e2   
) {
  struct ps_bunit_type	*p, dummy_bu; 
  struct ps_exp_type	*result; 
  
  if (type != AND && type != OR) {
    fprintf(RED_OUT, "Error: We cannot use Boolean operations other than AND and OR to exp_boolean().\n"); 
    bk(0); 	
  }
  if (e1->type == type) {
    result = ps_exp_copy(e1); 	
  } 
  else if (e2->type == type) { 
    result = ps_exp_copy(e2); 
    e2 = e1; 	
  } 
  else { 
    result = ps_exp_alloc(type); 
    result->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    insert_sorted_blist_dummy_head(
      type, 
      e1, 
      &dummy_bu, &(result->u.bexp.len)
    ); 
    insert_sorted_blist_dummy_head( 
      type, 
      e2, 
      &dummy_bu, &(result->u.bexp.len)
    ); 
    result->u.bexp.blist = dummy_bu.bnext; 
    result->var_status = e1->var_status | e2->var_status; 
    result->exp_status = e1->exp_status | e2->exp_status; 
/*
    e1->parent = r; 
    e2->parent = r; 
*/
    return(ps_exp_share(result)); 
  } 

  if (e2->type == type) {
    dummy_bu.bnext = result->u.bexp.blist; 
    for (p = e2->u.bexp.blist; p; p = p->bnext) {
      insert_sorted_blist_dummy_head(
        type, 
        p->subexp, 
        &dummy_bu, &(result->u.bexp.len)
      ); 
    }
    result->u.bexp.blist = dummy_bu.bnext; 
  } 
  else { 
    dummy_bu.bnext = result->u.bexp.blist; 
    insert_sorted_blist_dummy_head(
      type, 
      e2, 
      &dummy_bu, &(result->u.bexp.len)
    ); 
    result->u.bexp.blist = dummy_bu.bnext; 
  }
  return(ps_exp_share(result)); 
}
  /* exp_boolean() */  
  
  

struct ps_exp_type	*exp_arith(
  int 			op, 
  struct ps_exp_type	*lhs, 
  struct ps_exp_type	*rhs 
) {
  struct ps_exp_type *newsub; 

  if (lhs->type == TYPE_CONSTANT && rhs->type == TYPE_CONSTANT) { 
    switch (op) { 
    case BIT_OR: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value | rhs->u.value, NULL)); 
    case BIT_AND: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value & rhs->u.value, NULL)); 
    case BIT_SHIFT_RIGHT: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value >> rhs->u.value, NULL)); 
    case BIT_SHIFT_LEFT: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value << rhs->u.value, NULL)); 
    case ARITH_ADD: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value + rhs->u.value, NULL)); 
    case ARITH_MINUS: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value - rhs->u.value, NULL)); 
    case ARITH_MULTIPLY: 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value * rhs->u.value, NULL)); 
    case ARITH_DIVIDE: 
      if (rhs->u.value == 0) {
      	fprintf(RED_OUT, "\nError: divided by zero! \n"); 
      	exit(0); 
      } 
      else if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
               == FLAG_SYSTEM_HYBRID
               ) 
        break; 
      else 
        return(exp_atom(TYPE_CONSTANT, lhs->u.value / rhs->u.value, NULL)); 
    case ARITH_MODULO: 
      if (rhs->u.value == 0) {
      	fprintf(RED_OUT, "\nError: divided by zero! \n"); 
      	exit(0); 
      } 
      return(exp_atom(TYPE_CONSTANT, lhs->u.value % rhs->u.value, NULL)); 
    case ARITH_EQ: 
      if (lhs->u.value == rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 

    case ARITH_NEQ: 
      if (lhs->u.value != rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 

    case ARITH_LESS: 
      if (lhs->u.value < rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 

    case ARITH_LEQ: 
      if (lhs->u.value <= rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 

    case ARITH_GREATER: 
      if (lhs->u.value > rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 

    case ARITH_GEQ: 
      if (lhs->u.value >= rhs->u.value) 
        return(PS_EXP_TRUE); 
      else 
        return(PS_EXP_FALSE); 
    } 	
  } 
  newsub = ps_exp_alloc(op); 
  newsub->u.arith.lhs_exp = lhs; 
  newsub->u.arith.rhs_exp = rhs; 
  newsub->var_status = lhs->var_status | rhs->var_status; 
  newsub->exp_status = lhs->exp_status | rhs->exp_status; 
  return(ps_exp_share(newsub)); 
}
  /* exp_arith() */  




struct ps_exp_type	*ps_arith_normal(
  struct ps_exp_type	*a, 
  int			*flag_child_swapping_ptr 
) { 
  struct ps_exp_type	*lhs, *rhs; 
  int			type; 

  switch (type = a->type) { 
  case EQ: 
  case NEQ: 
  case LEQ: 
  case LESS: 
    *flag_child_swapping_ptr = TYPE_FALSE; 
    return(a); 
  
  case GREATER: 
    lhs = ps_exp_alloc(LEQ);
    *lhs = *a; 
    lhs->type = LEQ; 
    lhs->u.ineq.term = ps_term_array_copy(
      a->u.ineq.term, a->u.ineq.term_count
    );  
    *flag_child_swapping_ptr = TYPE_TRUE; 
    return(ps_exp_share(lhs)); 
  
  case GEQ: 
    lhs = ps_exp_alloc(LESS);
    *lhs = *a; 
    lhs->type = LESS; 
    lhs->u.ineq.term = ps_term_array_copy(
      a->u.ineq.term, a->u.ineq.term_count
    );  
    *flag_child_swapping_ptr = TYPE_TRUE; 
    return(ps_exp_share(lhs)); 
  
  case ARITH_EQ: 
  case ARITH_NEQ: 
    lhs = a->u.arith.lhs_exp; 
    rhs = a->u.arith.rhs_exp; 
    *flag_child_swapping_ptr = TYPE_FALSE; 
    if (ps_exp_comp(lhs, rhs) > 0) 
      return(exp_arith(type, rhs, lhs)); 
    else 
      return(a); 
  case ARITH_GREATER: 
    lhs = a->u.arith.lhs_exp; 
    rhs = a->u.arith.rhs_exp; 
    if (ps_exp_comp(lhs, rhs) > 0) {
      *flag_child_swapping_ptr = TYPE_FALSE; 
      return(exp_arith(ARITH_LESS, rhs, lhs)); 
    }
    else {
      *flag_child_swapping_ptr = TYPE_TRUE; 
      return(exp_arith(ARITH_LEQ, lhs, rhs));  
    }
  case ARITH_GEQ: 
    lhs = a->u.arith.lhs_exp; 
    rhs = a->u.arith.rhs_exp; 
    if (ps_exp_comp(lhs, rhs) > 0) {
      *flag_child_swapping_ptr = TYPE_FALSE; 
      return(exp_arith(ARITH_LEQ, rhs, lhs)); 
    }
    else {
      *flag_child_swapping_ptr = TYPE_TRUE; 
      return(exp_arith(ARITH_LESS, lhs, rhs)); 
    }
  case ARITH_LEQ: 
    lhs = a->u.arith.lhs_exp; 
    rhs = a->u.arith.rhs_exp; 
    if (ps_exp_comp(lhs, rhs) > 0) { 
      *flag_child_swapping_ptr = TYPE_TRUE; 
      return(exp_arith(ARITH_LESS, rhs, lhs)); 
    }
    else {
      *flag_child_swapping_ptr = TYPE_FALSE; 
      return(a); 
    }
  case ARITH_LESS: 
    lhs = a->u.arith.lhs_exp; 
    rhs = a->u.arith.rhs_exp; 
    if (ps_exp_comp(lhs, rhs) > 0) { 
      *flag_child_swapping_ptr = TYPE_TRUE; 
      return(exp_arith(ARITH_LEQ, rhs, lhs)); 
    } 
    else {
      *flag_child_swapping_ptr = TYPE_FALSE; 
      return(a); 
    }
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal inequality type %1d in lazy_atom().\n", 
      type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* ps_arith_normal() */  


int	count_lazy_atom = 0; 
struct red_type	*lazy_atom(
  int			pi, 
  struct ps_exp_type	*lazy_exp
) { 
  int			comp, flag_child_swapping; 
  struct ps_exp_type	*normal_lazy_exp; 
  
/*
  fprintf(RED_OUT, "\n======================\nlazy atom %1d(1): exp=%x\n", 
    ++count_lazy_atom, lazy_exp
  ); 
  pcform(lazy_exp); 
*/  
  normal_lazy_exp = ps_exp_instantiate(lazy_exp, pi); 
/*
  fprintf(RED_OUT, "lazy atom %1d(2): exp=%x\n", 
    count_lazy_atom, normal_lazy_exp
  ); 
  pcform(normal_lazy_exp); 
*/   
  normal_lazy_exp = ps_arith_normal(normal_lazy_exp, &flag_child_swapping); 
/*
  fprintf(RED_OUT, "lazy atom %1d(3): exp=%x\n", 
    count_lazy_atom, normal_lazy_exp
  ); 
  pcform(normal_lazy_exp); 
*/
  if (flag_child_swapping) 
    return(lazy_subtree(NORM_NO_RESTRICTION, NORM_FALSE, 
      get_lazy_proc(normal_lazy_exp, pi),  
      normal_lazy_exp
    ) ); 
  else 
    return(lazy_subtree(NORM_FALSE, NORM_NO_RESTRICTION, 
      get_lazy_proc(normal_lazy_exp, pi),  
      normal_lazy_exp
    ) ); 
}
  /* lazy_atom() */ 



/************************************
 *  The following procedures are for ps_exp_project(). 
 */ 
int	VI_IN_EXP_POSSIBLY, FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 

int	rec_check_vi_in_exp_possibly(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_vi_in_red_possibly(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NULL); 
  else if (d->var_index == VI_IN_EXP_POSSIBLY)  
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_VI_IN_EXP_POSSIBLY, 
    d, (struct red_type *) VI_IN_EXP_POSSIBLY
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NULL; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   d->var_index == VI_IN_EXP_POSSIBLY
        || rec_check_vi_in_red_possibly(d->u.bdd.zero_child)
        || rec_check_vi_in_red_possibly(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NULL; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   CLOCK[c1] == VI_IN_EXP_POSSIBLY 
        || CLOCK[c2] == VI_IN_EXP_POSSIBLY
        ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NULL; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_vi_in_red_possibly(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (VI_IN_EXP_POSSIBLY == d->u.hrd.hrd_exp->hrd_term[ci].var_index) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NULL; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_vi_in_red_possibly(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_vi_in_red_possibly");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_vi_in_exp_possibly(d->u.lazy.exp) 
        || rec_check_vi_in_red_possibly(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_vi_in_red_possibly(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NULL; 
    break; 

  case TYPE_FLOAT: 
    if (d->var_index == VI_IN_EXP_POSSIBLY) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NULL; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_vi_in_red_possibly(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  case TYPE_DOUBLE: 
    if (d->var_index == VI_IN_EXP_POSSIBLY) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NULL; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_vi_in_red_possibly(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  default: 
    if (d->var_index == VI_IN_EXP_POSSIBLY) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NULL; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_vi_in_red_possibly(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_vi_in_red_possibly() */  


int	check_vi_in_red_possibly(
  struct red_type	*d, 
  int			vi
) { 
  VI_IN_EXP_POSSIBLY = vi; 
  FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_TRUE; 
  return((int) rec_check_vi_in_red_possibly(d)); 
} 
  /* check_vi_in_exp_possibly() */ 




int	rec_check_vi_in_exp_possibly(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case BIT_NOT: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_exp_possibly(psub->u.exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (   psub->type == VAR[VI_IN_EXP_POSSIBLY].TYPE 
        && VAR[psub->u.atom.var_index].OFFSET 
           == VAR[VI_IN_EXP_POSSIBLY].OFFSET 
        ) { 
      if (   psub->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
          || (   psub->u.atom.exp_base_proc_index->type == TYPE_CONSTANT
              && VAR[VI_IN_EXP_POSSIBLY].PROC_INDEX 
                 == psub->u.atom.exp_base_proc_index->u.value
          )   ) {
        return(TYPE_TRUE); 
    } }
          
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_vi_in_exp_possibly(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_exp_possibly(psub->u.interval.lbound_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_in_exp_possibly(psub->u.interval.rbound_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_exp_possibly(psub->u.arith.lhs_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_in_exp_possibly(psub->u.arith.rhs_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_exp_possibly(psub->u.arith_cond.cond)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_in_exp_possibly(psub->u.arith_cond.if_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_in_exp_possibly(psub->u.arith_cond.else_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_vi_in_exp_possibly(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_exp_possibly(psub->u.ineq.offset)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_vi_in_exp_possibly(psub->u.ineq.term[i].coeff)) {
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_vi_in_exp_possibly(psub->u.ineq.term[i].operand)) {
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_vi_in_exp_possibly(pbu->subexp)) { 
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_vi_in_exp_possibly(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_in_red_possibly(psub->u.rpred.red) 
        == NORM_NO_RESTRICTION
        ) { 
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
    if (psub->u.project.variable_index == VI_IN_EXP_POSSIBLY) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_MCHUNK:  
    if (   psub->u.project.variable_index%VARIABLE_COUNT 
           <= VI_IN_EXP_POSSIBLY
        && psub->u.project.variable_index/VARIABLE_COUNT 
           >= VI_IN_EXP_POSSIBLY
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_VAR_SIM: 
    if (   VSIM_TYPE(psub->u.project.vsim_type_offset)  
           == VAR[VI_IN_EXP_POSSIBLY].TYPE
        && VAR[VI_IN_EXP_POSSIBLY].PROC_INDEX
        && VSIM_OFFSET(psub->u.project.vsim_type_offset)  
           == VAR[VI_IN_EXP_POSSIBLY].OFFSET 
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 
    break; 

  case PROJECT_CLOCK_SIM: 
    if (   TYPE_CLOCK == VAR[VI_IN_EXP_POSSIBLY].TYPE
        && VAR[VI_IN_EXP_POSSIBLY].PROC_INDEX
        && psub->u.project.clock_offset == VAR[VI_IN_EXP_POSSIBLY].OFFSET 
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 
    break; 

  case PROJECT_TIME:  
    if (
       VAR[VI_IN_EXP_POSSIBLY].TYPE == TYPE_CLOCK 
    || VAR[VI_IN_EXP_POSSIBLY].TYPE == TYPE_DENSE
    ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_QSYNC:  
    if (
       VAR[VI_IN_EXP_POSSIBLY].TYPE == TYPE_POINTER 
    && (VAR[VI_IN_EXP_POSSIBLY].STATUS & FLAG_QUANTIFIED_SYNC) 
    ) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_TYPE:  
    if (VAR[VI_IN_EXP_POSSIBLY].TYPE == psub->u.project.var_type) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_PEER:  
    if (VAR[VI_IN_EXP_POSSIBLY].PROC_INDEX != psub->u.project.var_proc) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    if (VAR[VI_IN_EXP_POSSIBLY].PROC_INDEX) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

    break;  

  default: 
    fprintf(RED_OUT, 
      "\nError 1: Unrecognized condition operator %1d.\n", 
      psub->type
    ); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_vi_in_exp_possibly() */  


int	check_vi_in_exp_possibly(
  struct ps_exp_type	*child, 
  int			vi
) { 
  VI_IN_EXP_POSSIBLY = vi; 
  FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_TRUE; 
  return ((int) rec_check_vi_in_exp_possibly(child));  
} 
  /* check_vi_in_exp_possibly() */ 





int	MADDR_LB_IN_EXP, MADDR_UB_IN_EXP; 

struct red_type	*rec_check_mchunk_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (d->var_index == VI_IN_EXP_POSSIBLY)  
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_MCHUNK_IN_EXP, d, 
    (struct red_type *) 
      (MADDR_LB_IN_EXP + VARIABLE_COUNT * MADDR_UB_IN_EXP)
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_mchunk_in_red(d->u.bdd.zero_child)
        || rec_check_mchunk_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_mchunk_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_mchunk_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_mchunk_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_mchunk_in_exp(d->u.lazy.exp) 
        || rec_check_mchunk_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_mchunk_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    if (   d->var_index >= MADDR_LB_IN_EXP
        && d->var_index <= MADDR_UB_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_mchunk_in_red(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  case TYPE_DOUBLE: 
    if (   d->var_index >= MADDR_LB_IN_EXP
        && d->var_index <= MADDR_UB_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_mchunk_in_red(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  default: 
    if (   d->var_index >= MADDR_LB_IN_EXP
        && d->var_index <= MADDR_UB_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_mchunk_in_red(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_mchunk_in_red() */  





int	rec_check_mchunk_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
  case TYPE_BDD: 
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_exp(psub->u.exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_DISCRETE:
/*
    if (psub->u.atom.indirect_count > 0) 
      return(TYPE_TRUE); 
    else 
*/
    if (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
      result = rec_check_mchunk_in_exp(
        psub->u.atom.exp_base_proc_index
      ); 
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(result); 
    }
    else if (   psub->u.atom.var_index >= MADDR_LB_IN_EXP
             && psub->u.atom.var_index <= MADDR_UB_IN_EXP
             ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_mchunk_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_mchunk_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_exp(psub->u.arith_cond.cond)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_mchunk_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_mchunk_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_mchunk_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_exp(psub->u.ineq.offset)) {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_mchunk_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_mchunk_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_mchunk_in_exp(pbu->subexp)) { 
        FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_mchunk_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL; 
    FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_mchunk_in_red(psub->u.rpred.red) 
        == NORM_NO_RESTRICTION
        ) { 
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

  case PROJECT_MCHUNK:  
    if (   psub->u.project.variable_index%VARIABLE_COUNT 
           <= MADDR_LB_IN_EXP
        && psub->u.project.variable_index/VARIABLE_COUNT 
           >= MADDR_LB_IN_EXP
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_in_exp_possibly(psub->u.project.child)); 

  case PROJECT_VAR_SIM: 
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_CLOCK_SIM: 
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_TIME:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

  case PROJECT_QSYNC:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

  case PROJECT_TYPE:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(rec_check_mchunk_in_exp(psub->u.project.child)); 

    break;  

  default: 
    fprintf(RED_OUT, 
      "\nError 1: Unrecognized condition operator %1d.\n", 
      psub->type
    ); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_mchunk_in_exp() */  


int	check_mchunk_in_exp(
  struct ps_exp_type	*child, 
  int			maddr_lb, 
  int			maddr_ub 
) { 
  MADDR_LB_IN_EXP = maddr_lb; 
  MADDR_UB_IN_EXP = maddr_ub; 
  FLAG_VI_IN_EXP_POSSIBLY_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_mchunk_in_exp(child)); 
} 
  /* check_mchunk_in_exp() */ 







/**************************************************************
 *
 *  procedures for check_local_in_exp(). 
 */

int	VTYPE_SIM_IN_EXP, VOFFSET_SIM_IN_EXP, FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 

int	rec_check_vi_sim_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_vi_sim_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NULL);
  else if (   VAR[d->var_index].PROC_INDEX 
           && VAR[d->var_index].TYPE == VTYPE_SIM_IN_EXP
           && VAR[d->var_index].TYPE == VOFFSET_SIM_IN_EXP 
           ) 
    result = NORM_NO_RESTRICTION; 

  ce = cache2_check_result_key(OP_VI_SIM_IN_EXP, 
    d, 
    (struct red_type *) 
    (VTYPE_SIM_IN_EXP + (VOFFSET_SIM_IN_EXP * DISP_PROJECT_VAR_SIM))
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NULL; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_vi_sim_in_red(d->u.bdd.zero_child)
        || rec_check_vi_sim_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NULL; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   VTYPE_SIM_IN_EXP == TYPE_CLOCK
        && (   (   VAR[CLOCK[c1]].PROC_INDEX
                && VAR[CLOCK[c1]].OFFSET == VOFFSET_SIM_IN_EXP
                ) 
            || (   VAR[CLOCK[c2]].PROC_INDEX
                && VAR[CLOCK[c2]].OFFSET == VOFFSET_SIM_IN_EXP
        )   )   ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NULL; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_vi_sim_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          && VTYPE_SIM_IN_EXP 
             == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE
          && VOFFSET_SIM_IN_EXP 
             == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].OFFSET
          ) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NULL; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_vi_sim_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_vi_sim_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_vi_sim_in_exp(d->u.lazy.exp) 
        || rec_check_vi_sim_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_vi_sim_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NULL; 
    break; 

  case TYPE_FLOAT: 
    result = NULL; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (rec_check_vi_sim_in_red(d->u.fdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  case TYPE_DOUBLE: 
    result = NULL; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (rec_check_vi_sim_in_red(d->u.dfdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  default: 
    result = NULL; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      if (rec_check_vi_sim_in_red(d->u.ddd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_vi_sim_in_red() */  



int	check_vi_sim_in_red(
  struct red_type	*d, 
  int			vtype, 
  int			voffset 
) { 
  VTYPE_SIM_IN_EXP = vtype; 
  VOFFSET_SIM_IN_EXP = voffset; 
  FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return((int) rec_check_vi_sim_in_red(d)); 
} 
  /* check_vi_sim_in_red() */ 






int	rec_check_vi_sim_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (   psub->type == VTYPE_SIM_IN_EXP 
        && VAR[psub->u.atom.var_index].OFFSET == VOFFSET_SIM_IN_EXP
        ) { 
      if (   psub->u.atom.exp_base_proc_index != PS_EXP_GLOBAL_IDENTIFIER
          && (   psub->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
              || psub->u.atom.exp_base_proc_index->u.value != 0
          )   ) {
        return(TYPE_TRUE); 
    } }
          
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_vi_sim_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_sim_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_sim_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_exp(psub->u.arith_cond.cond)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_sim_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_vi_sim_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_vi_sim_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_exp(psub->u.ineq.offset)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_vi_sim_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_vi_sim_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_vi_sim_in_exp(pbu->subexp)) { 
        FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_vi_sim_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_vi_sim_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION
        ) { 
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
    return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_MCHUNK:  
    return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_VAR_SIM: 
    if (   VSIM_TYPE(psub->u.project.vsim_type_offset) == VTYPE_SIM_IN_EXP
        && VSIM_OFFSET(psub->u.project.vsim_type_offset) == VOFFSET_SIM_IN_EXP 
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_sim_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_CLOCK_SIM: 
    if (   TYPE_CLOCK == VTYPE_SIM_IN_EXP
        && psub->u.project.clock_offset == VOFFSET_SIM_IN_EXP  
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_sim_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_TIME:  
    if (VTYPE_SIM_IN_EXP == TYPE_CLOCK || VTYPE_SIM_IN_EXP == TYPE_DENSE) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_QSYNC:  
    return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_TYPE:  
    if (VTYPE_SIM_IN_EXP == psub->u.project.var_type) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_vi_sim_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_vi_sim_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(TYPE_FALSE); 

    break;  

  default: 
    fprintf(RED_OUT, 
      "\nError 1: Unrecognized condition operator %1d.\n", 
      psub->type
    ); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_vi_sim_in_exp() */  






int	check_vi_sim_in_exp(
  struct ps_exp_type	*child, 
  int			vtype, 
  int			voffset 
) { 
  VTYPE_SIM_IN_EXP = vtype; 
  VOFFSET_SIM_IN_EXP = voffset; 
  FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_vi_sim_in_exp(child)); 
} 
  /* check_vi_sim_in_exp() */ 







/**************************************************************
 *
 *  procedures for check_local_in_exp(). 
 */

int	COFFSET_SIM_IN_EXP, FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 

int	rec_check_clock_sim_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_clock_sim_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE);
  else if (   VAR[d->var_index].PROC_INDEX 
           && VAR[d->var_index].TYPE == TYPE_CLOCK
           && VAR[d->var_index].TYPE == COFFSET_SIM_IN_EXP 
           ) 
    result = NORM_NO_RESTRICTION; 

  ce = cache2_check_result_key(OP_CLOCK_SIM_IN_EXP, 
    d, (struct red_type *) COFFSET_SIM_IN_EXP
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_clock_sim_in_red(d->u.bdd.zero_child)
        || rec_check_clock_sim_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (   VAR[CLOCK[c1]].PROC_INDEX
            && VAR[CLOCK[c1]].OFFSET == COFFSET_SIM_IN_EXP
            ) 
        || (   VAR[CLOCK[c2]].PROC_INDEX
                && VAR[CLOCK[c2]].OFFSET == COFFSET_SIM_IN_EXP
        )   ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_clock_sim_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          && TYPE_CLOCK 
             == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE
          && COFFSET_SIM_IN_EXP 
             == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].OFFSET
          ) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_clock_sim_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_vi_sim_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_clock_sim_in_exp(d->u.lazy.exp) 
        || rec_check_clock_sim_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_clock_sim_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (rec_check_clock_sim_in_red(d->u.fdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (rec_check_clock_sim_in_red(d->u.dfdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      if (rec_check_clock_sim_in_red(d->u.ddd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_clock_sim_in_red() */  





int	rec_check_clock_sim_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_clock_sim_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_sim_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_sim_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_exp(psub->u.arith_cond.cond)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_sim_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_sim_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_clock_sim_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_exp(psub->u.ineq.offset)) {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_clock_sim_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_clock_sim_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_clock_sim_in_exp(pbu->subexp)) { 
        FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_clock_sim_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_sim_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION
        ) { 
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
    return(rec_check_clock_sim_in_exp(psub->u.project.child)); 

  case PROJECT_MCHUNK:  
    return(rec_check_clock_sim_in_exp(psub->u.project.child)); 

  case PROJECT_VAR_SIM: 
    if (   VSIM_TYPE(psub->u.project.vsim_type_offset) == TYPE_CLOCK
        && VSIM_OFFSET(psub->u.project.vsim_type_offset) == COFFSET_SIM_IN_EXP 
        ) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_clock_sim_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_CLOCK_SIM: 
    if (psub->u.project.clock_offset == COFFSET_SIM_IN_EXP) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_clock_sim_in_exp(psub->u.project.child)); 
    break; 

  case PROJECT_TIME:  
    return(TYPE_FALSE); 

  case PROJECT_QSYNC:  
    return(rec_check_clock_sim_in_exp(psub->u.project.child)); 

  case PROJECT_TYPE:  
    if (TYPE_CLOCK == psub->u.project.var_type) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_clock_sim_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_clock_sim_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_clock_sim_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(TYPE_FALSE); 

    break;  

  default: 
    fprintf(RED_OUT, 
      "\nError 1: Unrecognized condition operator %1d.\n", 
      psub->type
    ); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_clock_sim_in_exp() */  






int	check_clock_sim_in_exp(
  struct ps_exp_type	*child, 
  int			clock_offset 
) { 
  COFFSET_SIM_IN_EXP = clock_offset; 
  FLAG_CLOCK_SIM_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_clock_sim_in_exp(child)); 
} 
  /* check_clock_sim_in_exp() */ 






/**************************************************************
 *
 *  procedures for check_local_in_exp(). 
 */

int	FLAG_TIME_IN_EXP_TOP_LEVEL; 

int	rec_check_time_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_time_in_red(d)
     struct red_type	*d;
{
  int				ci;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (   VAR[d->var_index].TYPE == TYPE_CLOCK
           || VAR[d->var_index].TYPE == TYPE_DENSE 
           || VAR[d->var_index].TYPE == TYPE_CRD
           || VAR[d->var_index].TYPE == TYPE_HRD 
           ) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_TIME_IN_EXP, d, NULL); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_time_in_red(d->u.bdd.zero_child)
        || rec_check_time_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
  case TYPE_HRD:
    result = NORM_NO_RESTRICTION; 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_time_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_time_in_exp(d->u.lazy.exp) 
        || rec_check_time_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_time_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (rec_check_time_in_red(d->u.fdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (rec_check_time_in_red(d->u.dfdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      if (rec_check_time_in_red(d->u.ddd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_time_in_red() */  



int	rec_check_time_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_CLOCK:
  case TYPE_DENSE:
    return(TYPE_TRUE); 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_QSYNC_HOLDER: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_time_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_time_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_time_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_exp(psub->u.arith_cond.cond)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_time_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_time_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_time_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_exp(psub->u.ineq.offset)) {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_time_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_time_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_time_in_exp(pbu->subexp)) { 
        FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_time_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_TIME_IN_EXP_TOP_LEVEL; 
    FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_time_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_TIME_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_QSYNC:  
  case PROJECT_TYPE:  
  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
  case PROJECT_PEER:  
  case PROJECT_LOCAL: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_time_in_exp(psub->u.project.child)); 

  case PROJECT_TIME:  
    return(TYPE_FALSE); 

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_time_in_exp() */  




int	check_time_in_exp(
  struct ps_exp_type	*child
) {
  FLAG_TIME_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_time_in_exp(child)); 
} 
  /* check_time_in_exp() */ 






/*******************************************************************
 *
 */
int	TYPE_IN_EXP, FLAG_TYPE_IN_EXP_TOP_LEVEL; 

int	rec_check_type_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_type_in_red(d)
     struct red_type	*d;
{
  int				ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE);
  else if (VAR[d->var_index].TYPE == TYPE_IN_EXP) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_TYPE_IN_EXP, 
    d, (struct red_type *) TYPE_IN_EXP
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  if (VAR[d->var_index].TYPE == TYPE_IN_EXP) 
    result = NORM_NO_RESTRICTION; 
  else { 
    result = NORM_FALSE;  
    switch (VAR[d->var_index].TYPE) {
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      if (   rec_check_type_in_red(d->u.bdd.zero_child)
          || rec_check_type_in_red(d->u.bdd.one_child)
          ) 
        result = NORM_NO_RESTRICTION; 
      else  
        result = NORM_FALSE; 
      break; 
    case TYPE_CRD: 
      if (TYPE_IN_EXP == TYPE_CLOCK) 
        result = NORM_NO_RESTRICTION; 
      else {
        result = NORM_FALSE; 
        for (ci = 0; ci < d->u.crd.child_count; ci++) 
          if (rec_check_type_in_red(d->u.crd.arc[ci].child) 
              == NORM_NO_RESTRICTION
              ) {
      	    result = NORM_NO_RESTRICTION; 
      	    break; 
          } 
      }
      break;
    case TYPE_HRD:
      len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
      for (ci = 0; ci < len; ci++) {
        if (TYPE_IN_EXP 
            == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE
            ) 
          break;
      } 
      if (ci < len) { 
        result = NORM_NO_RESTRICTION; 
      } 
      else { 
        result = NORM_FALSE; 
        for (ci = 0; ci < d->u.hrd.child_count; ci++) 
          if (rec_check_type_in_red(d->u.hrd.arc[ci].child) 
              == NORM_NO_RESTRICTION
              ) {
      	    result = NORM_NO_RESTRICTION; 
      	    break; 
      }   }
      break;
    case TYPE_HDD:
      fprintf(RED_OUT,"ERROR in rec_check_type_in_red");
      exit(0);
      break;

    case TYPE_LAZY_EXP: 
      if (   rec_check_type_in_exp(d->u.lazy.exp) 
          || rec_check_type_in_red(d->u.lazy.false_child)
             == NORM_NO_RESTRICTION  
          || rec_check_type_in_red(d->u.lazy.true_child)
             == NORM_NO_RESTRICTION 
          ) {
        result = NORM_NO_RESTRICTION;  
      }
      else 
        result = NORM_FALSE; 
      break; 

    case TYPE_FLOAT: 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_type_in_red(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
      break; 

    case TYPE_DOUBLE: 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_type_in_red(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
      break; 

    default: 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_type_in_red(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }
  return(ce->result = result);
}
  /* rec_check_type_in_red() */  





int	rec_check_type_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (psub->type == VAR[TYPE_IN_EXP].TYPE) { 
      return(TYPE_TRUE); 
    }
          
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_type_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_type_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_type_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_exp(psub->u.arith_cond.cond)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_type_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_type_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_type_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_exp(psub->u.ineq.offset)) {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_type_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_type_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_type_in_exp(pbu->subexp)) { 
        FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_type_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_TYPE_IN_EXP_TOP_LEVEL; 
    FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_type_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_TYPE_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_type_in_exp(psub->u.project.child)); 

  case PROJECT_TIME:  
    if (TYPE_IN_EXP == TYPE_CLOCK || TYPE_IN_EXP == TYPE_DENSE) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_type_in_exp(psub->u.project.child)); 

  case PROJECT_QSYNC:  
    if (TYPE_IN_EXP == TYPE_POINTER) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_type_in_exp(psub->u.project.child)); 

  case PROJECT_TYPE:  
    if (TYPE_IN_EXP == psub->u.project.var_type) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_type_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_type_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_type_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(rec_check_type_in_exp(psub->u.project.child)); 

    break;  

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_type_in_exp() */  



int	check_type_in_exp(
  struct ps_exp_type	*child, 
  int			type
) { 
  TYPE_IN_EXP = type; 
  FLAG_TYPE_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_type_in_exp(child)); 
} 
  /* check_type_in_exp() */ 



/**************************************************************
 *
 *  procedures for check_qsync_in_exp(). 
 */
int	QSYNC_IN_EXP, FLAG_QSYNC_IN_EXP_TOP_LEVEL; 

int	rec_check_qsync_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_qsync_in_red(d)
     struct red_type	*d;
{
  int				ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE);
  else if (   VAR[d->var_index].TYPE == TYPE_POINTER
           && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
           ) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_QSYNC_IN_EXP, d, NULL); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_qsync_in_red(d->u.bdd.zero_child)
        || rec_check_qsync_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_qsync_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (
         VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE == TYPE_POINTER
      && (  VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].STATUS 
          & FLAG_QUANTIFIED_SYNC 
          )
      ) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_qsync_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_qsync_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_qsync_in_exp(d->u.lazy.exp) 
        || rec_check_qsync_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_qsync_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (rec_check_qsync_in_red(d->u.fdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (rec_check_qsync_in_red(d->u.dfdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      if (rec_check_qsync_in_red(d->u.ddd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_qsync_in_red() */  





int	rec_check_qsync_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_POINTER:
    if (psub->var_status & FLAG_QUANTIFIED_SYNC) 
      return(TYPE_TRUE); 
  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_qsync_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_qsync_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_qsync_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_exp(psub->u.arith_cond.cond)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_qsync_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_qsync_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_qsync_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_exp(psub->u.ineq.offset)) {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_qsync_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_qsync_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_qsync_in_exp(pbu->subexp)) { 
        FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_qsync_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_QSYNC_IN_EXP_TOP_LEVEL; 
    FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_qsync_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_QSYNC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_qsync_in_exp(psub->u.project.child)); 

  case PROJECT_TIME:  
    return(rec_check_qsync_in_exp(psub->u.project.child)); 

  case PROJECT_QSYNC:  
    return(TYPE_FALSE); 

  case PROJECT_TYPE:  
    if (psub->u.project.var_type == TYPE_POINTER) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_qsync_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_qsync_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_qsync_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(rec_check_qsync_in_exp(psub->u.project.child)); 

    break;  

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_qsync_in_exp() */  



int	check_qsync_in_exp(
  struct ps_exp_type	*child
) { 
  FLAG_QSYNC_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_qsync_in_exp(child)); 
} 
  /* check_qsync_in_exp() */  



/**************************************************************
 *
 *  procedures for check_clock_in_exp(). 
 */
int	CLOCK_IN_EXP, FLAG_CLOCK_IN_EXP_TOP_LEVEL; 

int	rec_check_clock_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_clock_in_red(d)
     struct red_type	*d;
{
  int				ci, len; 
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (   VAR[d->var_index].TYPE == TYPE_CLOCK
           && VAR[d->var_index].TYPE == TYPE_CRD
           ) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_CLOCK_IN_EXP, d, NULL); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   rec_check_clock_in_red(d->u.bdd.zero_child)
        || rec_check_clock_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    result = NORM_NO_RESTRICTION; 
    break;

  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE == TYPE_CLOCK) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_clock_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_clock_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_clock_in_exp(d->u.lazy.exp) 
        || rec_check_clock_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_clock_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (rec_check_clock_in_red(d->u.fdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (rec_check_clock_in_red(d->u.dfdd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
    break; 

  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      if (rec_check_clock_in_red(d->u.ddd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
        result = NORM_NO_RESTRICTION; 
        break; 
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_clock_in_red() */  





int	rec_check_clock_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_CLOCK:
    return(TYPE_TRUE); 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_clock_in_exp(
      psub->u.atom.exp_base_proc_index
    ); 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_exp(psub->u.arith_cond.cond)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_clock_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_clock_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_exp(psub->u.ineq.offset)) {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_clock_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_clock_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_clock_in_exp(pbu->subexp)) { 
        FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_clock_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_CLOCK_IN_EXP_TOP_LEVEL; 
    FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_clock_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_CLOCK_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_clock_in_exp(psub->u.project.child)); 

  case PROJECT_TIME:  
    return(TYPE_FALSE); 

  case PROJECT_QSYNC:  
    return(rec_check_clock_in_exp(psub->u.project.child)); 

  case PROJECT_TYPE: 
    if (TYPE_CLOCK == psub->u.project.var_type) { 
      return(TYPE_FALSE); 
    } 
    else 
      return(rec_check_clock_in_exp(psub->u.project.child)); 

  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
    return(rec_check_clock_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    return(rec_check_clock_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(rec_check_clock_in_exp(psub->u.project.child)); 

    break;  

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_clock_in_exp() */  




int	check_clock_in_exp(
  struct ps_exp_type	*child
) { 
  FLAG_CLOCK_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_clock_in_exp(child)); 
} 
  /* check_clock_in_exp() */ 








/**************************************************************
 *
 *  procedures for check_peer_in_exp(). 
 */
int	PEER_IN_EXP, FLAG_PEER_IN_EXP_TOP_LEVEL; 

int	rec_check_peer_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_peer_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (   VAR[d->var_index].PROC_INDEX 
           && VAR[d->var_index].PROC_INDEX != PEER_IN_EXP 
           ) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_PEER_IN_EXP, 
    d, (struct red_type *) PEER_IN_EXP
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   (   VAR[d->var_index].PROC_INDEX 
            && VAR[d->var_index].PROC_INDEX != PEER_IN_EXP
            ) 
        || rec_check_peer_in_red(d->u.bdd.zero_child)
        || rec_check_peer_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (   VAR[CLOCK[c1]].PROC_INDEX 
            && VAR[CLOCK[c1]].PROC_INDEX != PEER_IN_EXP 
            )
        || (   VAR[CLOCK[c2]].PROC_INDEX 
            && VAR[CLOCK[c2]].PROC_INDEX != PEER_IN_EXP 
            ) 
        ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_peer_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          && PEER_IN_EXP 
             != VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          ) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_peer_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_peer_in_exp");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_peer_in_exp(d->u.lazy.exp) 
        || rec_check_peer_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_peer_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    if (   VAR[d->var_index].PROC_INDEX
        && VAR[d->var_index].PROC_INDEX != PEER_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_peer_in_red(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  case TYPE_DOUBLE: 
    if (   VAR[d->var_index].PROC_INDEX
        && VAR[d->var_index].PROC_INDEX != PEER_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_peer_in_red(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  default: 
    if (   VAR[d->var_index].PROC_INDEX
        && VAR[d->var_index].PROC_INDEX != PEER_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_peer_in_red(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_peer_in_red() */  




int	rec_check_peer_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (   psub->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
        || psub->u.atom.exp_base_proc_index->u.value != PEER_IN_EXP
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_peer_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_peer_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_exp(psub->u.arith_cond.cond)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_peer_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_peer_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_peer_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_exp(psub->u.ineq.offset)) {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_peer_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_peer_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_peer_in_exp(pbu->subexp)) { 
        FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_peer_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_PEER_IN_EXP_TOP_LEVEL; 
    FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_peer_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_PEER_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_TIME:  
  case PROJECT_QSYNC:  
  case PROJECT_TYPE:  
  case PROJECT_LOCAL: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_peer_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    if (PEER_IN_EXP == psub->u.project.var_proc) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_peer_in_exp(psub->u.project.child)); 
    break; 

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_peer_in_exp() */  




int	check_peer_in_exp(
  struct ps_exp_type	*child, 
  int			pi
) { 
  PEER_IN_EXP = pi; 
  FLAG_PEER_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_peer_in_exp(child)); 
} 
  /* check_peer_in_exp() */ 





/**************************************************************
 *
 *  procedures for check_proc_and_global_in_exp(). 
 */
int	PROC_IN_EXP, FLAG_PROC_IN_EXP_TOP_LEVEL; 

int	rec_check_proc_and_global_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_proc_and_global_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (   (!VAR[d->var_index].PROC_INDEX) 
           || VAR[d->var_index].PROC_INDEX == PROC_IN_EXP 
           ) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_PROC_AND_GLOBAL_IN_EXP, 
    d, (struct red_type *) PROC_IN_EXP
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   (!VAR[d->var_index].PROC_INDEX) 
        || VAR[d->var_index].PROC_INDEX == PROC_IN_EXP
        || rec_check_proc_and_global_in_red(d->u.bdd.zero_child)
        || rec_check_proc_and_global_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (!VAR[CLOCK[c1]].PROC_INDEX) 
        || VAR[CLOCK[c1]].PROC_INDEX == PROC_IN_EXP 
        || (!VAR[CLOCK[c2]].PROC_INDEX) 
        || VAR[CLOCK[c2]].PROC_INDEX == PROC_IN_EXP 
        ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_proc_and_global_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (   (!VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX) 
          || PROC_IN_EXP 
             == VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          ) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_proc_and_global_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_proc_and_global_in_exp");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_proc_and_global_in_exp(d->u.lazy.exp) 
        || rec_check_proc_and_global_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_proc_and_global_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    if (   (!VAR[d->var_index].PROC_INDEX)
        || VAR[d->var_index].PROC_INDEX == PROC_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_proc_and_global_in_red(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  case TYPE_DOUBLE: 
    if (   (!VAR[d->var_index].PROC_INDEX)
        || VAR[d->var_index].PROC_INDEX == PROC_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_proc_and_global_in_red(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  default: 
    if (   (!VAR[d->var_index].PROC_INDEX)
        || VAR[d->var_index].PROC_INDEX == PROC_IN_EXP
        ) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_proc_and_global_in_red(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_proc_and_global_in_red() */  




int	rec_check_proc_and_global_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (   psub->u.atom.exp_base_proc_index->type == TYPE_CONSTANT
        && psub->u.atom.exp_base_proc_index->u.value != PROC_IN_EXP
        ) 
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_proc_and_global_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_proc_and_global_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_exp(psub->u.arith_cond.cond)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_proc_and_global_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_proc_and_global_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_proc_and_global_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_exp(psub->u.ineq.offset)) {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_proc_and_global_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_proc_and_global_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_proc_and_global_in_exp(pbu->subexp)) { 
        FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_proc_and_global_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_PROC_IN_EXP_TOP_LEVEL; 
    FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_proc_and_global_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_PROC_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_TIME:  
  case PROJECT_QSYNC:  
  case PROJECT_TYPE:  
  case PROJECT_LOCAL: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_proc_and_global_in_exp(psub->u.project.child)); 

  case PROJECT_PEER:  
    if (PROC_IN_EXP == psub->u.project.var_proc) { 
      return(TYPE_FALSE); 
    }
    else 
      return(rec_check_proc_and_global_in_exp(psub->u.project.child)); 
    break; 

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_proc_and_global_in_exp() */  




int	check_proc_and_global_in_exp(
  struct ps_exp_type	*child, 
  int			pi
) { 
  PROC_IN_EXP = pi; 
  FLAG_PROC_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_proc_and_global_in_exp(child)); 
} 
  /* check_proc_and_global_in_exp() */ 






/**************************************************************
 *
 *  procedures for check_local_in_exp(). 
 */
int	LOCAL_IN_EXP, FLAG_LOCAL_IN_EXP_TOP_LEVEL; 

int	rec_check_local_in_exp(
  struct ps_exp_type	*  
); 


struct red_type	*rec_check_local_in_red(d)
     struct red_type	*d;
{
  int				c1, c2, ci, len;
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(NORM_FALSE); 
  else if (VAR[d->var_index].PROC_INDEX) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_LOCAL_IN_EXP, d, NULL); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   VAR[d->var_index].PROC_INDEX
        || rec_check_local_in_red(d->u.bdd.zero_child)
        || rec_check_local_in_red(d->u.bdd.one_child)
        ) 
      result = NORM_NO_RESTRICTION; 
    else  
      result = NORM_FALSE; 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   VAR[CLOCK[c1]].PROC_INDEX 
        || VAR[CLOCK[c2]].PROC_INDEX
        ) {  
      result = NORM_NO_RESTRICTION; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_check_local_in_red(d->u.crd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      if (VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX) 
        break;
    } 
    if (ci < len) { 
      result = NORM_NO_RESTRICTION; 
      break; 
    } 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) 
      if (rec_check_local_in_red(d->u.hrd.arc[ci].child) 
          == NORM_NO_RESTRICTION
          ) {
      	result = NORM_NO_RESTRICTION; 
      	break; 
      } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_check_local_in_red");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    if (   rec_check_local_in_exp(d->u.lazy.exp) 
        || rec_check_local_in_red(d->u.lazy.false_child)
           == NORM_NO_RESTRICTION  
        || rec_check_local_in_red(d->u.lazy.true_child)
           == NORM_NO_RESTRICTION 
        ) {
      result = NORM_NO_RESTRICTION;  
    }
    else 
      result = NORM_FALSE; 
    break; 

  case TYPE_FLOAT: 
    if (VAR[d->var_index].PROC_INDEX) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        if (rec_check_local_in_red(d->u.fdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  case TYPE_DOUBLE: 
    if (VAR[d->var_index].PROC_INDEX) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        if (rec_check_local_in_red(d->u.dfdd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
    break; 

  default: 
    if (VAR[d->var_index].PROC_INDEX) 
      result = NORM_NO_RESTRICTION; 
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        if (rec_check_local_in_red(d->u.ddd.arc[ci].child) 
            == NORM_NO_RESTRICTION
            ) {
          result = NORM_NO_RESTRICTION; 
          break; 
        }
      }
    }
  }

  return(ce->result = result);
}
  /* rec_check_local_in_red() */  





int	rec_check_local_in_exp(
  struct ps_exp_type	*psub  
) {
  int			i, result, orig_flag;
  struct ps_bunit_type	*pbu;

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_CONSTANT:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_TRASH:
    return (TYPE_FALSE);

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    orig_flag = FLAG_VI_SIM_IN_EXP_TOP_LEVEL; 
    FLAG_VI_SIM_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_exp(psub->u.exp)) {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_VI_SIM_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_BDD: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_QSYNC_HOLDER: 
    if (VAR[psub->u.atom.var_index].PROC_INDEX) { 
      return(TYPE_TRUE); 
    }
    else 
      return(TYPE_FALSE); 
    break; 

  case TYPE_INTERVAL: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_exp(psub->u.interval.lbound_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_local_in_exp(psub->u.interval.rbound_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    }
    break; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_exp(psub->u.arith.lhs_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_local_in_exp(psub->u.arith.rhs_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case ARITH_CONDITIONAL: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_exp(psub->u.arith_cond.cond)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_local_in_exp(psub->u.arith_cond.if_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    else if (rec_check_local_in_exp(psub->u.arith_cond.else_exp)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 
  case TYPE_INLINE_CALL: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    result = rec_check_local_in_exp(
      psub->u.inline_call.instantiated_exp
    ); 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
    return(result); 

  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_exp(psub->u.ineq.offset)) {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    }
    for (i = 1; i < psub->u.ineq.term_count; i++) {
      if (rec_check_local_in_exp(psub->u.ineq.term[i].coeff)) {
        FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
      }
      else if (rec_check_local_in_exp(psub->u.ineq.term[i].operand)) {
        FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } } 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY :
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (rec_check_local_in_exp(pbu->subexp)) { 
        FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
        return(TYPE_TRUE); 
    } }
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
    return(TYPE_FALSE); 

  case FORALL: 
  case EXISTS :
    fprintf(RED_OUT, 
      "\nERROR: We did not expect to see quantified expressions \n"
    ); 
    fprintf(RED_OUT, 
      "       in rec_check_local_in_exp(). \n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break;

  case RED: 
    orig_flag = FLAG_LOCAL_IN_EXP_TOP_LEVEL; 
    FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_FALSE; 
    if (rec_check_local_in_red(psub->u.rpred.red) == NORM_NO_RESTRICTION) { 
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_TRUE); 
    } 
    else {
      FLAG_LOCAL_IN_EXP_TOP_LEVEL = orig_flag; 
      return(TYPE_FALSE); 
    } 
    break; 

  case PROJECT:  
  case PROJECT_MCHUNK: 
  case PROJECT_TIME:  
  case PROJECT_QSYNC:  
  case PROJECT_TYPE:  
  case PROJECT_CLOCK_LOWER_EXTEND:  
  case PROJECT_CLOCK_UPPER_EXTEND:  
  case PROJECT_PEER:  
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
    return(rec_check_local_in_exp(psub->u.project.child)); 
  
  case PROJECT_LOCAL: 
    return(TYPE_FALSE); 

    break;  

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_check_local_in_exp() */  






int	check_local_in_exp(
  struct ps_exp_type	*child
) { 
  FLAG_LOCAL_IN_EXP_TOP_LEVEL = TYPE_TRUE; 
  return(rec_check_local_in_exp(child)); 
} 
  /* check_local_in_exp() */ 




 

struct ps_exp_type	*ps_exp_project(
  int			type, 
  struct ps_exp_type	*child, 
  int			vi  
){
  struct ps_exp_type *psub; 

  switch (type) { 
  case PROJECT: 
    if (!check_vi_in_exp_possibly(child, vi)) { 
      return(child); 
    } 
    break; 
  case PROJECT_VAR_SIM: 
    if (!check_vi_sim_in_exp(child, VSIM_TYPE(vi), VSIM_OFFSET(vi))) { 
      return(child); 
    } 
    break; 
  case PROJECT_CLOCK_SIM: 
    if (!check_clock_sim_in_exp(child, vi)) { 
      return(child); 
    } 
    break; 
  case PROJECT_TIME: 
    if (!check_time_in_exp(child)) {
      return(child); 
    } 
    break; 
  case PROJECT_TYPE: 
    if (!check_type_in_exp(child, vi)) { 
      return(child); 
    } 
    break; 
  case PROJECT_QSYNC:
    if (!check_qsync_in_exp(child)) { 
      return(child); 
    } 
    break; 
  case PROJECT_CLOCK_LOWER_EXTEND: 
  case PROJECT_CLOCK_UPPER_EXTEND: 
    if (!check_clock_in_exp(child)) { 
      return(child); 
    } 
    break; 
  case PROJECT_PEER: 
    if (!check_peer_in_exp(child, vi)) { 
      return(child); 
    } 
    break; 
  case PROJECT_LOCAL: 
    if (!check_local_in_exp(child)) { 
      return(child); 
    } 
    break; 
  case PROJECT_MCHUNK: 
    if (!check_mchunk_in_exp(child, vi%VARIABLE_COUNT, vi/VARIABLE_COUNT)) { 
      return(child); 
    } 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal project type %1d in ps_exp_project().\n", 
      type 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  psub = ps_exp_alloc(type); 
  psub->exp_status = child->exp_status; 
  psub->u.project.child = child; 
  psub->u.project.variable_index = vi; 
  return(ps_exp_share(psub)); 
}
  /* ps_exp_project() */



      



struct ps_exp_type	*exp_qexp(
  int			path,  
  char			*qname, 
  struct ps_exp_type	*lb_exp, 
  struct ps_exp_type	*ub_exp, 
  struct ps_exp_type	*qchild 
) {
  struct ps_exp_type	*q; 
  
  q = ps_exp_alloc(path); 
  q->exp_status = FLAG_PATH_INSIDE | qchild->exp_status; 
  q->u.qexp.lb_exp = lb_exp; 
  q->u.qexp.ub_exp = ub_exp; 
  q->u.qexp.child = qchild; 
  q->u.qexp.quantifier_name = qname; 
  q->u.qexp.value = 0; 
  
  return(ps_exp_share(q)); 
}
  /* exp_qexp() */ 
  





/*************************************************************************************************8
 *
 */


struct ps_exp_type	*add_neg(psub)
     struct ps_exp_type	*psub;
{
  struct ps_exp_type	*parentsub; 

  if (psub->type == RED)
    if (   psub->u.rpred.red == NORM_FALSE 
        || psub == PS_EXP_FALSE
        ) {
      return(PS_EXP_TRUE); 
    }
    else if (   psub->u.rpred.red == NORM_NO_RESTRICTION 
             || psub == PS_EXP_TRUE
             ) { 
      return(PS_EXP_FALSE); 
    } 
    else { 
      parentsub = ps_exp_alloc(RED); 
      parentsub->u.rpred.red 
      = parentsub->u.rpred.original_red
      = red_complement(psub->u.rpred.red); 
      parentsub->exp_status = (parentsub->exp_status & ~FLAG_TCTCTL_SUBFORM) 
      | check_time_convexity(
          red_bop(AND, RT[DECLARED_GLOBAL_INVARIANCE], 
            parentsub->u.rpred.red
        ) ); 
      return(ps_exp_share(parentsub)); 
    } 

  parentsub = ps_exp_alloc(NOT); 
  parentsub->var_status = psub->var_status; 
  parentsub->exp_status = psub->exp_status; 
  
  parentsub->u.bexp.len = 1; 
  parentsub->u.bexp.blist = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
  parentsub->u.bexp.blist->subexp = psub; 
  parentsub->u.bexp.blist->bnext = NULL; 

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "leaving addneg:\n"); 
  fflush(RED_OUT); 
  pcform(parentsub); 
  #endif 
  
  return(ps_exp_share(parentsub)); 
}
/* add_neg() */





struct ps_exp_type	*exp_modal_interval(lb, ub) 
	int	lb, ub; 
{ 
  struct ps_exp_type	*psub, *child, *gchild; 
  struct ps_bunit_type	*pbu, *nbu; 
  
  if (ub == CLOCK_POS_INFINITY) { 
    child = ps_exp_alloc(ARITH_GEQ); 
    if (lb % 2) 
      child->type = ARITH_GREATER; 
    else 
      child->type = ARITH_GEQ; 
    child->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 
    
    child->u.arith.lhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_name = var_modal_clock->name; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    if (lb % 2)
      gchild->u.value = (lb / 2)-1 ; 
    else 
      gchild->u.value = lb/2; 
    
    return(ps_exp_share(rec_ineq_analyze(child))); 
  } 
  else if (lb > ub) { 
  // This is an NEQ. 
    psub = ps_exp_alloc(OR); 
    psub->u.bexp.len = 2; 
    psub->u.bexp.blist = pbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    pbu->bnext = nbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    nbu->bnext = NULL; 

    /* for the upperbound */ 
    pbu->subexp 
    = child 
    = ps_exp_alloc(ARITH_LEQ); 
    if (ub % 2) 
      child->type = ARITH_LESS; 
    else 
      child->type = ARITH_LEQ; 
    child->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 

    child->u.arith.lhs_exp = gchild = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
    gchild->u.atom.var_name = var_modal_clock->name; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    
    if (ub % 2) 
      gchild->u.value = (ub / 2)+1 ;
    else 
      gchild->u.value = ub/2; 
    
    /* for the lowerbound */ 
    nbu->subexp 
    = child 
    = ps_exp_alloc(ARITH_GEQ); 
    if (lb % 2) 
      child->type = ARITH_GREATER; 
    else 
      child->type = ARITH_GEQ; 
    child->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 

    child->u.arith.lhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
    gchild->u.atom.var_name = var_modal_clock->name; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    if (lb % 2) 
      gchild->u.value = (lb / 2)-1 ; 
    else 
      gchild->u.value = lb/2; 
    
    return(ps_exp_share(rec_ineq_analyze(psub))); 
  } 
  // The following are not NEQ. 
  else if (lb == 0) { 
    child = ps_exp_alloc(ARITH_LEQ); 
    if (ub % 2) 
      child->type = ARITH_LESS; 
    else 
      child->type = ARITH_LEQ;
    child->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 

    child->u.arith.lhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
    gchild->u.atom.var_name = var_modal_clock->name; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    
    if (ub % 2) 
      gchild->u.value = (ub / 2)+1 ; 
    else 
      gchild->u.value = ub/2; 
    return(ps_exp_share(rec_ineq_analyze(child))); 	
  } 
  else { 
    psub = ps_exp_alloc(AND); 
    psub->u.bexp.len = 2; 
    psub->u.bexp.blist = pbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    pbu->bnext = nbu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    nbu->bnext = NULL; 

    /* for the upperbound */ 
    pbu->subexp = child = ps_exp_alloc(ARITH_LEQ); 
    if (ub % 2) 
      child->type = ARITH_LESS; 
    else 
      child->type = ARITH_LEQ; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 

    child->u.arith.lhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
    gchild->u.atom.var_name = var_modal_clock->name; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    if (ub % 2) 
      gchild->u.value = (ub / 2)+1 ; 
    else 
      gchild->u.value = ub/2; 
    
    /* for the lowerbound */ 
    nbu->subexp = child = ps_exp_alloc(ARITH_GEQ); 
    if (lb % 2) 
      child->type = ARITH_GREATER; 
    else 
      child->type = ARITH_GEQ; 
    child->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT; 
    child->var_status = FLAG_CLOCK; 
    child->exp_status = 0; 

    child->u.arith.lhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CLOCK); 
    gchild->var_status = FLAG_CLOCK; 
    gchild->exp_status = 0; 
    gchild->u.atom.var = var_modal_clock; 
    gchild->u.atom.var_index = CLOCK[MODAL_CLOCK]; 
    gchild->u.atom.var_name = var_modal_clock->name; 
//    gchild->u.atom.indirect_count = 0; 
    gchild->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER;  
    
    child->u.arith.rhs_exp 
    = gchild 
    = ps_exp_alloc(TYPE_CONSTANT); 
    if (lb % 2) 
      gchild->u.value = (lb / 2)-1 ; 
    else
      gchild->u.value = lb/2; 
    
    return(ps_exp_share(rec_ineq_analyze(psub))); 
  } 
} 
  /* exp_modal_interval() */ 





struct ps_exp_type	*add_modal_reset(psub) 
	struct ps_exp_type	*psub; 
{ 
  struct ps_exp_type	*newsub; 
  
  newsub = ps_exp_alloc(RESET); 
  newsub->var_status 
  = FLAG_CLOCK | (psub->var_status & FLAG_EXP_STATE_INSIDE);   
  newsub->exp_status = FLAG_EXP_MODAL_INSIDE | FLAG_RESET_INSIDE; 
  newsub->u.reset.var = var_modal_clock; 
  newsub->u.reset.clock_name = var_modal_clock->name; 
  newsub->u.reset.clock_index = MODAL_CLOCK; 
  newsub->u.reset.child = psub; 
  
  return(ps_exp_share(newsub)); 
} 
/* add_modal_reset() */ 



/*****************************************************************
 *  This procedure is highly destructive.  
 *  It directly changes the structure of psub. 
 */

int	rwmt_count = 0; 

#define	FLAG_REWRITE_TIMING	1
#define	FLAG_NO_REWRITE_TIMING	0

void	rewrite_modal_timing_mexp(
  struct ps_exp_type	*newsub, 
  struct ps_exp_type	*psub, 
  int			flag_rewrite_timing 
) { 
  struct ps_fairness_link_type	*fl; 

  newsub->u.mexp.strong_fairness_list = NULL; 
  newsub->u.mexp.strong_fairness_count = 0; 
  for (fl = psub->u.mexp.strong_fairness_list; 
    fl; 
    fl = fl->next_ps_fairness_link
  ) {
    newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
      rewrite_modal_timing(fl->fairness), 
      fl->status, 
      newsub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count) 
    ); 
  } 

  newsub->u.mexp.weak_fairness_list = NULL; 
  newsub->u.mexp.weak_fairness_count = 0; 
  for (fl = psub->u.mexp.weak_fairness_list; 
    fl; 
    fl = fl->next_ps_fairness_link
  ) {
    newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
      rewrite_modal_timing(fl->fairness), 
      fl->status, 
      newsub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count) 
    ); 
  } 

  if (psub->type != TYPE_GAME_SIM && flag_rewrite_timing) { 
    if (   newsub->u.mexp.time_lb == 0 
        && newsub->u.mexp.time_ub == CLOCK_POS_INFINITY/*oo*/
        ) { 
      newsub->u.mexp.time_restriction = PS_EXP_TRUE; 
    }
    else { 
      newsub->u.mexp.time_restriction = exp_modal_interval(
        psub->u.mexp.time_lb, psub->u.mexp.time_ub
      ); 
    }
  } 
}
  /* rewrite_modal_timing_mexp() */ 





struct ps_exp_type	*rewrite_modal_timing( 
  struct ps_exp_type	*psub
) {
  int				lvi, rvi, lci, i; 
  struct ps_bunit_type		*pbu, *nbu, dummy_bu, *tail_bu; 
  struct ps_exp_type		*newchild, *newsub; 

  switch(psub->type) {
  case TYPE_FALSE : 
  case TYPE_TRUE : 
  case TYPE_CONSTANT:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_NULL: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_CLOCK: 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
  case ARITH_CONDITIONAL: 
  case TYPE_INTERVAL: 
  case TYPE_INLINE_CALL: 
  case RED: 
    return(psub);
    break; 
  case AND :
  case OR :
  case NOT : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      insert_sorted_blist_dummy_head(
        psub->type, 
        rewrite_modal_timing(pbu->subexp), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    } 
    newsub->u.bexp.blist = dummy_bu.bnext; 
/*
    fprintf(RED_OUT, "Modal rewriting AND-OR: EXP_MODAL_INSIDE, %1x", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    for (jj = newsub->u.bexp.len, pbu = psub->u.bexp.blist; 
	 jj; 
	 jj--, pbu = pbu->bnext
	 ) {
      fprintf(RED_OUT, ", %1x", pbu->subexp->status & FLAG_EXP_MODAL_INSIDE); 
    }
    fprintf(RED_OUT, "\n"); 
    print_parse_subformula_structure(newsub, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
*/
    return(ps_exp_share(newsub)); 

  case IMPLY : 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nRewriting modal timing for IMPLY:\n"); 
    pcform(psub); 
    #endif 
    
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = OR; 
    newsub->u.bexp.blist = (struct ps_bunit_type *) 
      malloc(sizeof(struct ps_bunit_type)); 
    newsub->u.bexp.blist->bnext = (struct ps_bunit_type *) 
      malloc(sizeof(struct ps_bunit_type)); 
    newsub->u.bexp.blist->bnext->bnext = NULL; 
    
    newsub->u.bexp.blist->subexp 
    = add_neg(rewrite_modal_timing(psub->u.bexp.blist->subexp)); 
    newsub->u.bexp.blist->bnext->subexp 
    = rewrite_modal_timing(psub->u.bexp.blist->bnext->subexp); 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nThe outcome is:\n"); 
    pcform(psub); 
    #endif 

    return(ps_exp_share(newsub)); 
    break; 

  case FORALL: 
  case EXISTS: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.qexp.child = rewrite_modal_timing(psub->u.qexp.child); 
    newsub->u.qexp.lb_exp = rewrite_modal_timing(psub->u.qexp.lb_exp); 
    newsub->u.qexp.ub_exp = rewrite_modal_timing(psub->u.qexp.ub_exp); 
/*
    fprintf(RED_OUT, "Modal rewriting QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
*/
    return(ps_exp_share(newsub)); 
    break; 
  case RESET: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.clock_index 
    = variable_index[TYPE_CLOCK][0][psub->u.reset.var->index]; 
    newsub->u.reset.clock_index 
    = VAR[psub->u.reset.clock_index].U.CLOCK.CLOCK_INDEX; 
    newsub->u.reset.child = rewrite_modal_timing(psub->u.reset.child); 
/*
    fprintf(RED_OUT, "Modal rewriting RESET: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
*/
    return(ps_exp_share(newsub)); 
    break; 
  case EXISTS_ALWAYS: 
  case FORALL_ALWAYS: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.path_child = rewrite_modal_timing(psub->u.mexp.path_child); 
    rewrite_modal_timing_mexp(newsub, psub, FLAG_REWRITE_TIMING); 
    return(ps_exp_share(newsub)); 
    break; 
 
  case TYPE_GAME_SIM: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.path_child = NULL; 
    newsub->u.mexp.dest_child = NULL; 
    rewrite_modal_timing_mexp(newsub, psub, FLAG_REWRITE_TIMING); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_UNTIL: 
  case FORALL_EVENTUALLY : 
  case EXISTS_EVENTUALLY: 
  case FORALL_UNTIL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.path_child = rewrite_modal_timing(psub->u.mexp.path_child); 
    newsub->u.mexp.dest_child = rewrite_modal_timing(psub->u.mexp.dest_child); 
    rewrite_modal_timing_mexp(newsub, psub, FLAG_REWRITE_TIMING); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST: 
  // There should be no modal timing constraint.  
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.path_child = rewrite_modal_timing(psub->u.mexp.path_child); 
    newsub->u.mexp.dest_child = rewrite_modal_timing(psub->u.mexp.dest_child); 
    if (psub->u.mexp.event_restriction) 
      newsub->u.mexp.event_restriction 
      = rewrite_modal_timing(psub->u.mexp.event_restriction); 
    rewrite_modal_timing_mexp(newsub, psub, FLAG_NO_REWRITE_TIMING); 
    return(ps_exp_share(newsub)); 
    break; 
  case LINEAR_EVENT: 
  // There should be no modal timing constraint.  
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.eexp.precond_exp 
    = rewrite_modal_timing(psub->u.eexp.precond_exp); 
    if (psub->u.eexp.event_exp) 
      newsub->u.eexp.event_exp 
      = rewrite_modal_timing(psub->u.eexp.event_exp); 
    newsub->u.eexp.postcond_exp 
    = rewrite_modal_timing(psub->u.eexp.postcond_exp); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_CHANGE: 
  case FORALL_CHANGE: 
    fprintf(RED_OUT, "\nWarning: This modal operator should have been rewritten in shorthand_analysis().\n"); 
    fflush(RED_OUT); 
    bk(0); 
//    exit(0); 
    break; 
  default: 
    fprintf(RED_OUT, "\nError 4: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
}
/* rewrite_modal_timing() */ 




  
  
  
  
/*****************************************************************
 *  This procedure is highly destructive.  
 *  It directly changes the structure of psub. 
 */
int	push_neg_count = 0; 

struct ps_exp_type	*push_neg(psub, pos_flag) 
     struct ps_exp_type	*psub; 
     int		pos_flag; 
{
  int				lvi, rvi, lci, i; 
  struct ps_bunit_type		*pbu, dummy_bu; 
  struct ps_exp_type		*newsub; 
  struct red_type		*childred; 
  struct ps_fairness_link_type	*fl; 

  /* 
  newsub->status = psub->status;
  */
  switch(psub->type) {
  case TYPE_FALSE : 
    if (pos_flag) 
      return(psub);  
    else 
      return(PS_EXP_TRUE); 

  case TYPE_TRUE : 
    if (pos_flag)
      return(psub); 
    else
      return(PS_EXP_FALSE); 

  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD :
    if (pos_flag)
      return(psub);
    else
      return(add_neg(psub));
  case EQ :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(NEQ);
      *newsub = *psub; 
      newsub->type = NEQ; 
      return(ps_exp_share(newsub)); 
    } 

    return(psub);
    break;
  case NEQ :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(EQ);
      *newsub = *psub; 
      newsub->type = EQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case LEQ :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(GREATER);
      *newsub = *psub; 
      newsub->type = GREATER; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case LESS :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(GEQ);
      *newsub = *psub; 
      newsub->type = GEQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case GREATER :
    if (!pos_flag) {
      newsub = ps_exp_alloc(LEQ);
      *newsub = *psub; 
      newsub->type = LEQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case GEQ :
    if (!pos_flag) {
      newsub = ps_exp_alloc(LESS);
      *newsub = *psub; 
      newsub->type = LESS; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case ARITH_EQ :
    if (!pos_flag) {
      newsub = ps_exp_alloc(ARITH_NEQ);
      *newsub = *psub; 
      newsub->type = ARITH_NEQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case ARITH_NEQ :
    if (!pos_flag) {
      newsub = ps_exp_alloc(ARITH_EQ);
      *newsub = *psub; 
      newsub->type = ARITH_EQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case ARITH_LEQ :
    if (!pos_flag) {
      newsub = ps_exp_alloc(ARITH_GREATER);
      *newsub = *psub; 
      newsub->type = ARITH_GREATER; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break; 
  case ARITH_LESS :
    if (!pos_flag) {
      newsub = ps_exp_alloc(ARITH_GEQ);
      *newsub = *psub; 
      newsub->type = ARITH_GEQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case ARITH_GREATER :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(ARITH_LEQ);
      *newsub = *psub; 
      newsub->type = ARITH_LEQ; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break;
  case ARITH_GEQ :
    if (!pos_flag) { 
      newsub = ps_exp_alloc(ARITH_LESS);
      *newsub = *psub; 
      newsub->type = ARITH_LESS; 
      return(ps_exp_share(newsub)); 
    }
    return(psub);
    break; 

  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(ARITH_CONDITIONAL);
    *newsub = *psub; 
    newsub->u.arith_cond.if_exp = push_neg(psub->u.arith_cond.if_exp, pos_flag); 
    newsub->u.arith_cond.else_exp = push_neg(psub->u.arith_cond.else_exp, pos_flag); 
    return(ps_exp_share(newsub)); 
    break; 

  case TYPE_INLINE_CALL: 
    if (pos_flag) 
      return(psub); 
    else 
      return(add_neg(psub)); 
    
  case AND :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = OR;
    else
      newsub->type = AND;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      insert_sorted_blist_dummy_head(
        newsub->type, 
        push_neg(pbu->subexp, pos_flag), 
        &dummy_bu, &(newsub->u.bexp.len)
      ); 
    }
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 
    break; 
  case OR :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag) 
      newsub->type = AND;
    else
      newsub->type = OR;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      insert_sorted_blist_dummy_head(
        newsub->type, 
        push_neg(pbu->subexp, pos_flag), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 
    break; 
  case NOT : 
    newsub = push_neg(psub->u.bexp.blist->subexp, !pos_flag); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
    return(newsub); 
    
  case IMPLY :
    fprintf(RED_OUT, "Bug: IMPLY has already been eliminated in shorthand_analysis().\n"); 
    exit(0);

  case FORALL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = EXISTS;
    newsub->u.qexp.child = push_neg(psub->u.qexp.child, pos_flag); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = FORALL;
    newsub->u.qexp.child = push_neg(psub->u.qexp.child, pos_flag); 
    return(ps_exp_share(newsub)); 
    break; 

  case RESET:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = push_neg(psub->u.reset.child, pos_flag);
    return(ps_exp_share(newsub));
    break;
/*
    psub->u.reset.child = push_neg(psub->u.reset.child, TYPE_TRUE);
    psub->u.qexp.child->parent = psub;
    if (!pos_flag)
      psub = add_neg(psub);
    return(psub);
    break;
*/
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_UNTIL: 
  case FORALL_CHANGE: 
  case EXISTS_CHANGE:
  case FORALL_ALMOST: 
  case FORALL_OFTEN:
  case FORALL_EVENT:
  case EXISTS_EVENTUALLY: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
    fprintf(RED_OUT, "\nBug: Universal path modal operators should already have been eliminated.\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  case EXISTS_ALWAYS: 

  case EXISTS_UNTIL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.dest_child = push_neg(psub->u.mexp.dest_child, TYPE_TRUE); 
    newsub->u.mexp.path_child = push_neg(psub->u.mexp.path_child, TYPE_TRUE); 
    newsub->u.mexp.time_restriction 
    = push_neg(psub->u.mexp.time_restriction, TYPE_TRUE); 
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction 
      = push_neg(psub->u.mexp.event_restriction, TYPE_TRUE); 

    newsub->u.mexp.strong_fairness_list = NULL; 
    newsub->u.mexp.strong_fairness_count = 0; 
    for (fl = psub->u.mexp.strong_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
        push_neg(fl->fairness, TYPE_TRUE), 
        fl->status, 
        newsub->u.mexp.strong_fairness_list, 
        &(newsub->u.mexp.strong_fairness_count) 
      ); 
    } 

    newsub->u.mexp.weak_fairness_list = NULL; 
    newsub->u.mexp.weak_fairness_count = 0; 
    for (fl = psub->u.mexp.weak_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
        push_neg(fl->fairness, TYPE_TRUE), 
        fl->status, 
        newsub->u.mexp.weak_fairness_list, 
        &(newsub->u.mexp.weak_fairness_count) 
      ); 
    } 

    newsub = ps_exp_share(newsub); 
    if (!pos_flag)
      newsub = add_neg(newsub);
    return(newsub);
    break; 

  case TYPE_GAME_SIM: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.dest_child = NULL; 
    newsub->u.mexp.path_child = NULL; 
    newsub->u.mexp.time_restriction = NULL; 

    newsub->u.mexp.strong_fairness_list = NULL; 
    newsub->u.mexp.strong_fairness_count = 0; 
    for (fl = psub->u.mexp.strong_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
        push_neg(fl->fairness, TYPE_TRUE), 
        fl->status, 
        newsub->u.mexp.strong_fairness_list, 
        &(newsub->u.mexp.strong_fairness_count) 
      ); 
    } 

    newsub->u.mexp.weak_fairness_list = NULL; 
    newsub->u.mexp.weak_fairness_count = 0; 
    for (fl = psub->u.mexp.weak_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
        push_neg(fl->fairness, TYPE_TRUE), 
        fl->status, 
        newsub->u.mexp.weak_fairness_list, 
        &(newsub->u.mexp.weak_fairness_count) 
      ); 
    } 

    newsub = ps_exp_share(newsub); 
    if (!pos_flag)
      newsub = add_neg(newsub);
    return(newsub);
    break; 

  case LINEAR_EVENT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (psub->u.eexp.event_exp)
      newsub->u.eexp.event_exp 
      = push_neg(psub->u.eexp.event_exp, TYPE_TRUE); 
    newsub->u.eexp.precond_exp 
    = push_neg(psub->u.eexp.precond_exp, TYPE_TRUE); 
    newsub->u.eexp.postcond_exp 
    = push_neg(psub->u.eexp.postcond_exp, TYPE_TRUE); 
    newsub = ps_exp_share(newsub); 
    if (!pos_flag)
      newsub = add_neg(newsub);
    return(newsub);
    break; 
  case RED: 
    if (pos_flag) 
      return(psub); 
    else { 
      newsub = ps_exp_alloc(psub->type); 
      *newsub = *psub; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_complement(psub->u.rpred.red); 
      return(ps_exp_share(newsub)); 
    }
    break; 
  case PROJECT: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
  case PROJECT_TYPE: 
  case PROJECT_PEER: 
  case PROJECT_TIME: 
  case PROJECT_QSYNC: 
  case PROJECT_LOCAL: 
  case PROJECT_CLOCK_LOWER_EXTEND: 
  case PROJECT_CLOCK_UPPER_EXTEND: 
    if (pos_flag) 
      return(psub); 
    else 
      return(add_neg(psub)); 
 default: 
    fprintf(RED_OUT, "\nError 5: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
} 
/* push_neg() */




struct ps_exp_type	*lazy_push_neg(psub, pos_flag) 
     struct ps_exp_type	*psub; 
     int		pos_flag; 
{
  int				lvi, rvi, lci, i; 
  struct ps_bunit_type		*pbu, dummy_bu; 
  struct ps_exp_type		*newsub; 
  struct red_type		*childred; 

  /* 
  newsub->status = psub->status;
  */
  switch(psub->type) {
  case TYPE_FALSE : 
    if (pos_flag) 
      return(psub);  
    else 
      return(PS_EXP_TRUE); 

  case TYPE_TRUE : 
    if (pos_flag)
      return(psub); 
    else
      return(PS_EXP_FALSE); 

  case TYPE_BDD :
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :

  case TYPE_INLINE_CALL: 

  case EXISTS_ALWAYS: 
  case EXISTS_UNTIL: 
  case EXISTS_EVENT: 
  
  case PROJECT: 
  case PROJECT_VAR_SIM: 
  case PROJECT_CLOCK_SIM: 
  case PROJECT_TYPE: 
  case PROJECT_PEER: 
  case PROJECT_TIME: 
  case PROJECT_QSYNC: 
  case PROJECT_LOCAL: 
  case PROJECT_CLOCK_LOWER_EXTEND: 
  case PROJECT_CLOCK_UPPER_EXTEND: 
    if (pos_flag)
      return(psub);
    else
      return(add_neg(psub));
  case ARITH_CONDITIONAL: 
    fprintf(RED_OUT, "\nError: Illegal ARITH CONDITIONAL in lazy_push_neg().\n"); 
    fflush(RED_OUT); 
    bk(0); 
    break; 
    
  case AND :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = OR;
    else
      newsub->type = AND;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      insert_sorted_blist_dummy_head(
        newsub->type, 
        lazy_push_neg(pbu->subexp, pos_flag), 
        &dummy_bu, &(newsub->u.bexp.len)
      ); 
    }
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 
    break; 
  case OR :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag) 
      newsub->type = AND;
    else
      newsub->type = OR;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      insert_sorted_blist_dummy_head(
        newsub->type, 
        lazy_push_neg(pbu->subexp, pos_flag), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 
    break; 
  case NOT : 
    newsub = lazy_push_neg(psub->u.bexp.blist->subexp, !pos_flag); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
    return(newsub); 
    
  case IMPLY :
    fprintf(RED_OUT, "Bug: IMPLY has already been eliminated in shorthand_analysis().\n"); 
    exit(0);

  case FORALL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = EXISTS;
    newsub->u.qexp.child = lazy_push_neg(psub->u.qexp.child, pos_flag); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (!pos_flag)
      newsub->type = FORALL;
    newsub->u.qexp.child = lazy_push_neg(psub->u.qexp.child, pos_flag); 
    return(ps_exp_share(newsub)); 
    break; 

  case RESET:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = lazy_push_neg(psub->u.reset.child, pos_flag);
    return(ps_exp_share(newsub));
    break;
/*
    psub->u.reset.child = lazy_push_neg(psub->u.reset.child, TYPE_TRUE);
    psub->u.qexp.child->parent = psub;
    if (!pos_flag)
      psub = add_neg(psub);
    return(psub);
    break;
*/
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_UNTIL: 
  case FORALL_CHANGE: 
  case EXISTS_CHANGE:
  case FORALL_ALMOST: 
  case FORALL_OFTEN:
  case FORALL_EVENT:
  case EXISTS_EVENTUALLY: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
    fprintf(RED_OUT, "\nBug: Universal path modal operators should already have been eliminated.\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 


  case RED: 
    if (pos_flag) 
      return(psub); 
    else { 
      newsub = ps_exp_alloc(psub->type); 
      *newsub = *psub; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_complement(psub->u.rpred.red); 
      return(ps_exp_share(newsub)); 
    }
    break; 
  default: 
    fprintf(RED_OUT, "\nError 5: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
} 
/* lazy_push_neg() */



    
struct red_type	*red_lazy_project(
  struct red_type	*false_child, 
  struct red_type	*true_child, 
  struct red_type	*root, 
  int			op_project, 
  int			arg_project   
){
  struct ps_exp_type 	*psub; 
  struct red_type	*result; 

  switch (op_project) { 
  case PROJECT: 
    if (!check_vi_in_exp_possibly(root->u.lazy.exp, arg_project)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_VAR_SIM: 
    if (!check_vi_sim_in_exp(root->u.lazy.exp, 
           VSIM_TYPE(arg_project), VSIM_OFFSET(arg_project)
        )) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_CLOCK_SIM: 
    if (!check_clock_sim_in_exp(root->u.lazy.exp, arg_project)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_TIME: 
    if (!check_time_in_exp(root->u.lazy.exp)) {
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_TYPE: 
    if (!check_type_in_exp(root->u.lazy.exp, arg_project)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_QSYNC:
    if (!check_qsync_in_exp(root->u.lazy.exp)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_CLOCK_LOWER_EXTEND: 
  case PROJECT_CLOCK_UPPER_EXTEND: 
    if (!check_clock_in_exp(root->u.lazy.exp)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_PEER: 
    if (!check_peer_in_exp(root->u.lazy.exp, arg_project)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  case PROJECT_LOCAL: 
    if (!check_local_in_exp(root->u.lazy.exp)) { 
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  
  case PROJECT_MCHUNK: 
    if (!check_mchunk_in_exp(root->u.lazy.exp, 
           arg_project%VARIABLE_COUNT, arg_project/VARIABLE_COUNT
        ) ) {
      return(lazy_2_cases(false_child, true_child, 
        VAR[root->var_index].PROC_INDEX, root->u.lazy.exp
      ) ); 
    } 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal project type %1d in ps_exp_project().\n", 
      op_project 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  result = red_bop(OR, 
    lazy_2_cases(
      NORM_FALSE, 
      false_child, 
      VAR[root->var_index].PROC_INDEX, 
      ps_exp_project( 
        op_project, lazy_push_neg(root->u.lazy.exp, TYPE_FALSE), arg_project
    ) ), 
    lazy_2_cases(
      NORM_FALSE, 
      true_child, 
      VAR[root->var_index].PROC_INDEX, 
      ps_exp_project( 
        op_project, root->u.lazy.exp, arg_project
  ) ) ); 
  return(result); 
}
  /* red_lazy_project() */














/***********************************************************************
 *
 */
struct a23tree_type	*tree_mark_working; 

void	clear_working(int mask) {
  int	vi; 
  
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    VAR[vi].STATUS = VAR[vi].STATUS & ~mask; 	
  } 	
}
  /* clear_working() */ 



int 
  MASK_MARK_WORKING, 
  VI_MAX_MARK,  
  VI_MIN_MARK; 
; 
void	rec_mark_working(struct ps_exp_type *);

inline void	range_mark_working(
  int	vi, 
  int	vj, 
  int	mask 
) {
  int	i; 
  
  for (i = vi; i<= vj; i++) { 
    if (!(VAR[i].STATUS 
          & (  FLAG_VAR_PRIMED 
             | FLAG_VAR_AUX_BOTTOM_ORDERING
             | FLAG_SYNC_PLACE
        ) )  )
      VAR[i].STATUS = VAR[i].STATUS | mask; 
  } 
  if (vi < VI_MIN_MARK) 
    VI_MIN_MARK = vi; 
  if (vj > VI_MAX_MARK) 
    VI_MAX_MARK = vj; 
}
  /* range_mark_working() */ 


void	peer_mark_working(
  int	vi, 
  int	mask 
) {
  int	pi, depth, vip; 
  
  for (pi = 1; pi<= PROCESS_COUNT; pi++) { 
    if (VAR[vi].STATUS & FLAG_VAR_STACK) {
      for (depth = 0; depth < DEPTH_CALL; depth++) { 
        vip = variable_index[VAR[vi].TYPE]
          [pi]
          [VAR[vi].OFFSET+depth*HEIGHT_STACK_FRAME]; 
        VAR[vip].STATUS = VAR[vip].STATUS | mask; 
      }
    }
    else {
      vip = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET]; 
      VAR[vip].STATUS = VAR[vip].STATUS | mask; 
    }
  } 
}
  /* peer_mark_working() */ 


void	rec_mark_working_in_red(d)
     struct red_type	*d; 
{
  int				vi, ci; 
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct rec_type		*nrec, *rec;
        
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return; 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, tree_mark_working, 
    rec_comp, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    range_mark_working(d->var_index, d->var_index, MASK_MARK_WORKING);
    rec_mark_working_in_red(d->u.bdd.zero_child);
    rec_mark_working_in_red(d->u.bdd.one_child);
    break; 
  case TYPE_CRD:
    ci = VAR[d->var_index].U.CRD.CLOCK1; 
    if (ci) { 
      range_mark_working(CLOCK[ci], CLOCK[ci], MASK_MARK_WORKING);
    }
    ci = VAR[d->var_index].U.CRD.CLOCK2; 
    if (ci) { 
      range_mark_working(CLOCK[ci], CLOCK[ci], MASK_MARK_WORKING);
    }
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
      rec_mark_working_in_red(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++) {
      vi = d->u.hrd.hrd_exp->hrd_term[ci].var_index;
      range_mark_working(vi, vi, MASK_MARK_WORKING);
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
      rec_mark_working_in_red(d->u.hrd.arc[ci].child);
    break; 
  case TYPE_LAZY_EXP: 
    rec_mark_working(d->u.lazy.exp); 
    rec_mark_working_in_red(d->u.lazy.false_child);
    rec_mark_working_in_red(d->u.lazy.true_child);
    break; 
  case TYPE_FLOAT:
    range_mark_working(d->var_index, d->var_index, MASK_MARK_WORKING);
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--)
      rec_mark_working_in_red(d->u.fdd.arc[ci].child);
    break; 
  case TYPE_DOUBLE:
    range_mark_working(d->var_index, d->var_index, MASK_MARK_WORKING);
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--)
      rec_mark_working_in_red(d->u.dfdd.arc[ci].child);
    break; 
  default:
    range_mark_working(d->var_index, d->var_index, MASK_MARK_WORKING);
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--)
      rec_mark_working_in_red(d->u.ddd.arc[ci].child);
  }
}
/* rec_mark_working_in_red() */





void	mark_working_in_red(
  struct red_type	*d, 
  int			mask 
) {
  MASK_MARK_WORKING = mask; 
  init_23tree(&tree_mark_working); 
  rec_mark_working_in_red(d); 
  free_entire_23tree(tree_mark_working, rec_free); 
} 
  /* mark_working_in_red() */ 




void	rec_mark_working(psub)
     struct ps_exp_type	*psub;
{
  int				lb, ub, i;
  struct ps_bunit_type		*pbu;
  struct ps_fairness_link_type	*fl;
/*
  fprintf(RED_OUT, "entering rec_mark_working() for type %1d\n", psub->type); 
  pcform(psub); 
*/
  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_CONSTANT: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_SYNCHRONIZER: 
    return; 
  
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    range_mark_working(GLOBAL_SYSTEM_OVERHEAD_COUNT, VARIABLE_COUNT-1, MASK_MARK_WORKING); 
    return; 
  case TYPE_DISCRETE: 
  case TYPE_CLOCK: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
/*
    if (psub->u.atom.indirect_count > 0) { 
    // Then we need to use the content of A[i]=*(A+i) 
    // to decide the LHS address. 
    // This could be very expensive to decide before hand anything. 
      range_mark_working(GLOBAL_SYSTEM_OVERHEAD_COUNT, VARIABLE_COUNT-1, MASK_MARK_WORKING); 
      return; 
    } 
*/
    if (  psub->u.atom.exp_base_proc_index->var_status 
        & FLAG_EXP_STATE_INSIDE
        ) { 
      rec_mark_working(psub->u.atom.exp_base_proc_index); 
      peer_mark_working(psub->u.atom.var_index, FLAG_WORKING_IN_LAZY_EXP); 
      return; 
    } 
    if (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE) { 
      float flb, fub; 
      
      if (get_integer_range(
            psub->u.atom.exp_base_proc_index, 0, &lb, &ub, &flb, &fub
          ) != FLAG_SPECIFIC_VALUE) {
        lb = 1; 
        ub = PROCESS_COUNT; 
        fprintf(RED_OUT, 
          "\nWARNING: The following variable contains dynamic process id\n"
        );  
        fprintf(RED_OUT, 
          "         and is prepared for process 1 to %1d.\n", PROCESS_COUNT 
        ); 
        pcform(psub); 
        fflush(RED_OUT); 
/*
        fprintf(RED_OUT, 
          "\nERROR: Illegal process indices in base proc index in rec_mark_working().\n"
        ); 
        pcform(psub); 
        fflush(RED_OUT); 
        bk(0); 
*/
      }
      if (lb != ub || lb <= 0 || ub > PROCESS_COUNT) {
      	ub = psub->u.atom.var_index;
        for (lb = 1; lb <= PROCESS_COUNT; lb++) { 
          i = variable_index[VAR[ub].TYPE][lb][VAR[ub].OFFSET]; 
          range_mark_working(i, i, MASK_MARK_WORKING); 
        } 
      }
      else {
        ub = psub->u.atom.var_index;
        i = variable_index[VAR[ub].TYPE][lb][VAR[ub].OFFSET]; 
        range_mark_working(i, i, MASK_MARK_WORKING); 
      }
    }
    else {
      i = psub->u.atom.var_index; 
      range_mark_working(i, i, MASK_MARK_WORKING); 
    }       
    return; 

  case IMPLY :
  case FORALL : 
  case EXISTS : 
    fprintf(RED_OUT, "\nBug: This types should already have been eliminated.\n"); 
    bk(); 
    
  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    rec_mark_working(psub->u.ineq.offset); 
    for (i = 0; i < psub->u.ineq.term_count; i++) {
      rec_mark_working(psub->u.ineq.term[i].coeff); 
      rec_mark_working(psub->u.ineq.term[i].operand); 
    }
    break; 
    return; 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case ARITH_MODULO: 
  case ARITH_EQ : 
  case ARITH_NEQ : 
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    rec_mark_working(psub->u.arith.lhs_exp);
    rec_mark_working(psub->u.arith.rhs_exp);
    return; 
    
  case ARITH_CONDITIONAL: 
    rec_mark_working(psub->u.arith_cond.cond);
    rec_mark_working(psub->u.arith_cond.if_exp);
    rec_mark_working(psub->u.arith_cond.else_exp);
    break; 
    
  case TYPE_INLINE_CALL: 
    rec_mark_working(psub->u.inline_call.instantiated_exp);
    break; 
    
  case AND :
  case OR :
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      rec_mark_working(pbu->subexp); 
    }
    break; 
  case NOT : 
    rec_mark_working(psub->u.bexp.blist->subexp); 
    break; 
  case RESET: 
    rec_mark_working(psub->u.reset.child);
    break; 
    
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_UNTIL: 
  case EXISTS_EVENTUALLY: 
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST: 
  case FORALL_EVENT: 
    fprintf(RED_OUT, "\nBug: Universal path modal operators should already have been eliminated.\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    break; 

  case EXISTS_ALWAYS: 
  case EXISTS_UNTIL: 
    rec_mark_working(psub->u.mexp.dest_child); 
    rec_mark_working(psub->u.mexp.path_child); 
    rec_mark_working(psub->u.mexp.time_restriction); 
    if (psub->u.mexp.event_restriction)
      rec_mark_working(psub->u.mexp.event_restriction); 
    rec_mark_working_in_red(psub->u.mexp.red_xi_restriction); 
    if (psub->u.mexp.strong_fairness_count) 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_mark_working(fl->fairness); 
        if (fl->red_fairness) 
          rec_mark_working_in_red(fl->red_fairness);
      }
    if (psub->u.mexp.weak_fairness_count) 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_mark_working(fl->fairness); 
        if (fl->red_fairness) 
          rec_mark_working_in_red(fl->red_fairness); 
      }
    break; 

  case TYPE_GAME_SIM: 
    if (psub->u.mexp.strong_fairness_count) 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_mark_working(fl->fairness); 
        if (fl->red_fairness) 
          rec_mark_working_in_red(fl->red_fairness);
      }
    if (psub->u.mexp.weak_fairness_count) 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_mark_working(fl->fairness); 
        if (fl->red_fairness) 
          rec_mark_working_in_red(fl->red_fairness); 
      }
    break; 

  case LINEAR_EVENT: 
    rec_mark_working(psub->u.eexp.precond_exp); 
    rec_mark_working(psub->u.eexp.postcond_exp); 
    if (psub->u.eexp.event_exp) {
      rec_mark_working(psub->u.eexp.event_exp); 
      rec_mark_working_in_red(psub->u.eexp.red_sync_bulk_from_event_exp); 
      rec_mark_working_in_red(psub->u.eexp.red_game_sync_bulk_from_event_exp); 
    } 
    rec_mark_working_in_red(psub->u.eexp.red_precond); 
    rec_mark_working_in_red(psub->u.eexp.red_postcond); 
    break; 
  case RED: 
    rec_mark_working_in_red(psub->u.rpred.red); 
    if (psub->u.rpred.red != psub->u.rpred.original_red) {
      rec_mark_working_in_red(psub->u.rpred.original_red); 
    }     
    break; 


  default:
    fprintf(RED_OUT, 
      "\nError 7: unrecognized condition operator %1d in red_mark_working().\n", 
      psub->type
    );
    pcform(psub); 
    fflush(RED_OUT); 
    bk(); 
  }
}
/* rec_mark_working() */ 




void	mark_working(psub, mask) 
  struct ps_exp_type	*psub; 
  int			mask; 
{
  MASK_MARK_WORKING = mask; 
  init_23tree(&tree_mark_working); 
  rec_mark_working(psub); 
  free_entire_23tree(tree_mark_working, rec_free); 
}
  /* mark_working() */ 



inline void	mark_spec_referenced(struct ps_exp_type *psub) { 
  mark_working(psub, FLAG_SPEC_REFERENCED); 
}
  /* mark_spec_referenced() */ 






/*****************************************************************************
 *
 */
struct ps_exp_type	*EXP_PSUB;


struct a23tree_type	*parse_rec_tree;
int			VALUE_INDIRECT, PI_INDIRECT;



struct red_type	*red_interval_value(dx, dy, flag_delayed_evaluation)
  struct red_type	*dx, *dy;
  int			flag_delayed_evaluation; 
{
  struct red_type	*result, *conj;
  int			cix, ciy;

  result = NORM_FALSE;
  for (cix = 0; cix < dx->u.ddd.child_count; cix++)
    for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
      conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
      if (conj != NORM_FALSE) {
	conj = red_bop(AND, conj,
		       ddd_atom(VI_VALUE,
				dx->u.ddd.arc[cix].lower_bound,
				dy->u.ddd.arc[ciy].upper_bound
				)
		       );
	result = red_bop(OR, result, conj);
      }
    }
  return(result);
}
  /* red_interval_value() */



struct red_type	*red_interval_value_top_level(dx, dy, lb, ub, flag_delayed_evaluation)
	struct red_type	*dx, *dy;
	int		lb, ub, flag_delayed_evaluation; 
{
  struct red_type	*result, *conj;
  int			cix, ciy, wlb, wub;

  result = NORM_FALSE;
  for (cix = 0; cix < dx->u.ddd.child_count; cix++)
    for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) { 
      wlb = int_max(lb, dx->u.ddd.arc[cix].lower_bound); 
      wub = int_min(ub, dy->u.ddd.arc[ciy].upper_bound); 
      if (wlb > wub) 
        continue; 
      conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
      if (conj != NORM_FALSE) {
	conj = ddd_one_constraint(conj, VI_VALUE, wlb, wub);
	result = red_bop(OR, result, conj);
      }
    }
  return(result);
}
  /* red_interval_value_top_level() */


/* This can only be called in delayed evaluation. 
 */ 
struct red_type	*red_add_value(
  int			cx, 
  struct red_type	*dx, 
  int			cy, 
  struct red_type	*dy
) {
  struct red_type	*result, *conj;
  int			cix, ciy;

  if (dx == NORM_FALSE || dy == NORM_FALSE) { 
    return(NORM_FALSE); 	
  } 
  result = NORM_FALSE;
  if (dx->var_index == DOUBLE_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE,
              cx*dx->u.dfdd.arc[cix].lower_bound
              +cy*dy->u.dfdd.arc[ciy].lower_bound,
	      cx*dx->u.dfdd.arc[cix].upper_bound
	      +cy*dy->u.dfdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, 
            dy->u.fdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE,
              cx*dx->u.dfdd.arc[cix].lower_bound
              +cy*dy->u.fdd.arc[ciy].lower_bound,
	      cx*dx->u.dfdd.arc[cix].upper_bound
	      +cy*dy->u.fdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE)  { 
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, 
            dy->u.ddd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE,
              cx*dx->u.dfdd.arc[cix].lower_bound
              +cy*dy->u.ddd.arc[ciy].lower_bound,
	      cx*dx->u.dfdd.arc[cix].upper_bound
	      +cy*dy->u.ddd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == FLOAT_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE,
              cx*dx->u.fdd.arc[cix].lower_bound
              +cy*dy->u.dfdd.arc[ciy].lower_bound,
	      cx*dx->u.fdd.arc[cix].upper_bound
	      +cy*dy->u.dfdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, 
            dy->u.fdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = fdd_one_constraint(conj, FLOAT_VALUE,
              cx*dx->u.fdd.arc[cix].lower_bound
              +cy*dy->u.fdd.arc[ciy].lower_bound,
	      cx*dx->u.fdd.arc[cix].upper_bound
	      +cy*dy->u.fdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE)  { 
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, 
            dy->u.ddd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = fdd_one_constraint(conj, FLOAT_VALUE,
              cx*dx->u.fdd.arc[cix].lower_bound
              +cy*dy->u.ddd.arc[ciy].lower_bound,
	      cx*dx->u.fdd.arc[cix].upper_bound
	      +cy*dy->u.ddd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == VI_VALUE)  { 
    if (dy->var_index == DOUBLE_VALUE) { 
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE,
              cx*dx->u.ddd.arc[cix].lower_bound
              +cy*dy->u.dfdd.arc[ciy].lower_bound,
	      cx*dx->u.ddd.arc[cix].upper_bound
	      +cy*dy->u.dfdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, 
            dy->u.fdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = fdd_one_constraint(conj, FLOAT_VALUE,
              cx*dx->u.ddd.arc[cix].lower_bound
              +cy*dy->u.fdd.arc[ciy].lower_bound,
	      cx*dx->u.ddd.arc[cix].upper_bound
	      +cy*dy->u.fdd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE)  { 
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, 
            dy->u.ddd.arc[ciy].child
          );
          if (conj != NORM_FALSE) {
	    conj = ddd_one_constraint(conj, VI_VALUE,
              cx*dx->u.ddd.arc[cix].lower_bound
              +cy*dy->u.ddd.arc[ciy].lower_bound,
	      cx*dx->u.ddd.arc[cix].upper_bound
	      +cy*dy->u.ddd.arc[ciy].upper_bound
	    );
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } }  
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal 1st root variable %1d:%s in red_add_value().\n", 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    bk(0); 
  } 
  return(result);
}
  /* red_add_value() */



struct red_type	*red_add_value_top_level(
  int			cx, 
  struct red_type	*dx, 
  int			cy, 
  struct red_type	*dy, 
  int			lb, 
  int			ub
) {
  struct red_type	*result, *conj;
  int			cix, ciy;

  if (dx == NORM_FALSE || dy == NORM_FALSE) { 
    return(NORM_FALSE); 	
  } 
  result = NORM_FALSE;
  if (dx->var_index == DOUBLE_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double	wlb, wub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          wlb = dble_max(lb, cx*dx->u.dfdd.arc[cix].lower_bound
          +cy*dy->u.dfdd.arc[ciy].lower_bound); 
          wub = dble_min(ub, cx*dx->u.dfdd.arc[cix].upper_bound
          +cy*dy->u.dfdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) { 
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      double	wlb, wub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          wlb = dble_max(lb, cx*dx->u.dfdd.arc[cix].lower_bound
          +cy*dy->u.fdd.arc[ciy].lower_bound); 
          wub = dble_min(ub, cx*dx->u.dfdd.arc[cix].upper_bound
          +cy*dy->u.fdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      double	wlb, wub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          wlb = dble_max(lb, cx*dx->u.dfdd.arc[cix].lower_bound
          +cy*dy->u.ddd.arc[ciy].lower_bound); 
          wub = dble_min(ub, cx*dx->u.dfdd.arc[cix].upper_bound
          +cy*dy->u.ddd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value_top_level().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == FLOAT_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double	wlb, wub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          wlb = dble_max(lb, cx*dx->u.fdd.arc[cix].lower_bound
          +cy*dy->u.dfdd.arc[ciy].lower_bound); 
          wub = dble_min(ub, cx*dx->u.fdd.arc[cix].upper_bound
          +cy*dy->u.dfdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) { 
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float	wlb, wub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          wlb = flt_max(lb, cx*dx->u.fdd.arc[cix].lower_bound
          +cy*dy->u.fdd.arc[ciy].lower_bound); 
          wub = flt_min(ub, cx*dx->u.fdd.arc[cix].upper_bound
          +cy*dy->u.fdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = fdd_one_constraint(conj, FLOAT_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      float	wlb, wub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          wlb = flt_max(lb, cx*dx->u.fdd.arc[cix].lower_bound
          +cy*dy->u.ddd.arc[ciy].lower_bound); 
          wub = flt_min(ub, cx*dx->u.fdd.arc[cix].upper_bound
          +cy*dy->u.ddd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = fdd_one_constraint(conj, FLOAT_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value_top_level().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == VI_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double	wlb, wub; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          wlb = dble_max(lb, cx*dx->u.ddd.arc[cix].lower_bound
          +cy*dy->u.dfdd.arc[ciy].lower_bound); 
          wub = dble_min(ub, cx*dx->u.ddd.arc[cix].upper_bound
          +cy*dy->u.dfdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, 
            dy->u.dfdd.arc[ciy].child
          );
          if (conj != NORM_FALSE) { 
	    conj = dfdd_one_constraint(conj, DOUBLE_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float	wlb, wub; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          wlb = flt_max(lb, cx*dx->u.ddd.arc[cix].lower_bound
          +cy*dy->u.ddd.arc[ciy].lower_bound); 
          wub = flt_min(ub, cx*dx->u.ddd.arc[cix].upper_bound
          +cy*dy->u.fdd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = fdd_one_constraint(conj, FLOAT_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      int	wlb, wub; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          wlb = flt_max(lb, cx*dx->u.ddd.arc[cix].lower_bound
          +cy*dy->u.ddd.arc[ciy].lower_bound); 
          wub = flt_min(ub, cx*dx->u.ddd.arc[cix].upper_bound
          +cy*dy->u.ddd.arc[ciy].upper_bound); 
          if (wlb > wub) 
            continue; 
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) { 
	    conj = ddd_one_constraint(conj, VI_VALUE, wlb, wub); 
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_add_value_top_level().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal 1st root variable %1d:%s in red_add_value_top_level().\n", 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    bk(0); 
  } 
  return(result);
}
  /* red_add_value_top_level() */



struct red_type	*red_multiply_value(
  struct red_type	*dx, 
  struct red_type	*dy 
) {
  struct red_type	*result, *conj; 
  int			cix, ciy;

  if (dx == NORM_FALSE || dy == NORM_FALSE) { 
    return(NORM_FALSE); 	
  } 
  result = NORM_FALSE;
  if (dx->var_index == DOUBLE_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.ddd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    * dy->u.ddd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.ddd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    * dy->u.ddd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub)
	    ); 
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == FLOAT_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.ddd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    * dy->u.ddd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.ddd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    * dy->u.ddd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == VI_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.ddd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.ddd.arc[cix].lower_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.ddd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.ddd.arc[cix].upper_bound 
	    * dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.ddd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.ddd.arc[cix].lower_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.ddd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.ddd.arc[cix].upper_bound 
	    * dy->u.fdd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      int		v, vx, vy; 
      struct red_type	*filter; 
      
      for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
        for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
	    filter = NORM_FALSE;
	    for (vx = dx->u.ddd.arc[cix].lower_bound; 
	         vx <= dx->u.ddd.arc[cix].upper_bound; 
	         vx++
	         ) {
	      for (vy = dy->u.ddd.arc[ciy].lower_bound; 
	           vy <= dy->u.ddd.arc[ciy].upper_bound; 
	           vy++
	           ) {
	        v = vx * vy;
	        filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v, v));
	      }
	    }
	    conj = red_bop(AND, conj, filter);
	    result = red_bop(OR, result, conj);
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal 1st root variable %1d:%s in red_multiply_value().\n", 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    bk(0); 
  }
  return(result);
}
  /* red_multiply_value() */



inline struct red_type	*red_check_value_range(
  int 	v, 
  int 	lb, 
  int 	ub
) { 
  if (v >= lb && v <= ub) { 
    return(ddd_atom(VI_VALUE, v, v)); 
  } 
  else 
    return(TYPE_FALSE); 
}
  /* red_check_value_range() */ 
  
  
  
  
struct red_type	*red_multiply_value_top_level(
  struct red_type	*dx, 
  struct red_type	*dy, 
  int			lb, 
  int			ub 
) {
  struct red_type	*result, *conj, *filter;
  int			cix, ciy, v, vy, vx;

  if (dx == NORM_FALSE || dy == NORM_FALSE) { 
    return(NORM_FALSE); 	
  } 
  result = NORM_FALSE;
  for (cix = 0; cix < dx->u.ddd.child_count; cix++)
    for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
      conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
      if (conj != NORM_FALSE) {
	filter = NORM_FALSE;
	for (vx = dx->u.ddd.arc[cix].lower_bound; vx <= dx->u.ddd.arc[cix].upper_bound; vx++) {
	  for (vy = dy->u.ddd.arc[ciy].lower_bound; vy <= dy->u.ddd.arc[ciy].upper_bound; vy++) {
	    v = vx * vy;
	    filter = red_bop(OR, filter, 
	      red_check_value_range(v, lb, ub)
	    );
	  }
	}
	conj = red_bop(AND, conj, filter);
	result = red_bop(OR, result, conj);
      }
    }
  return(result);
}
  /* red_multiply_value_top_level() */







struct red_type	*red_divide_value(
  struct red_type	*dx, 
  struct red_type	*dy 
) {
  struct red_type	*result, *conj; 
  int			cix, ciy;

  if (dx == NORM_FALSE || dy == NORM_FALSE) { 
    return(NORM_FALSE); 	
  } 
  result = NORM_FALSE;
  if (dx->var_index == DOUBLE_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 

      for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
        if (   dy->u.dfdd.arc[ciy].lower_bound <= 0
            && dy->u.dfdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
        if (   dy->u.fdd.arc[ciy].lower_bound <= 0
            && dy->u.fdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
        if (   dy->u.ddd.arc[ciy].lower_bound <= 0
            && dy->u.ddd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.dfdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.dfdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.ddd.arc[ciy].lower_bound; 
            lxuy = dx->u.dfdd.arc[cix].lower_bound 
	    / dy->u.ddd.arc[ciy].upper_bound; 
            uxly = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.ddd.arc[ciy].lower_bound; 
            uxuy = dx->u.dfdd.arc[cix].upper_bound 
	    / dy->u.ddd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub)
	    ); 
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == FLOAT_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
        if (   dy->u.dfdd.arc[ciy].lower_bound <= 0
            && dy->u.dfdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
        if (   dy->u.fdd.arc[ciy].lower_bound <= 0
            && dy->u.fdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
        if (   dy->u.ddd.arc[ciy].lower_bound <= 0
            && dy->u.ddd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.fdd.child_count; cix++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.ddd.arc[ciy].lower_bound; 
            lxuy = dx->u.fdd.arc[cix].lower_bound 
	    / dy->u.ddd.arc[ciy].upper_bound; 
            uxly = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.ddd.arc[ciy].lower_bound; 
            uxuy = dx->u.fdd.arc[cix].upper_bound 
	    / dy->u.ddd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else if (dx->var_index == VI_VALUE) { 
    if (dy->var_index == DOUBLE_VALUE) { 
      double lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.dfdd.child_count; ciy++) {
        if (   dy->u.dfdd.arc[ciy].lower_bound <= 0
            && dy->u.dfdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.ddd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            lxuy = dx->u.ddd.arc[cix].lower_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
            uxly = dx->u.ddd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].lower_bound; 
            uxuy = dx->u.ddd.arc[cix].upper_bound 
	    / dy->u.dfdd.arc[ciy].upper_bound; 
	    lb = dble_min(dble_min(lxly, lxuy), dble_min(uxly, uxuy)); 
	    ub = dble_max(dble_max(lxly, lxuy), dble_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      dfdd_one_constraint(conj, DOUBLE_VALUE, lb, ub) 
	    ); 
    } } } }
    else if (dy->var_index == FLOAT_VALUE) { 
      float lxly, lxuy, uxly, uxuy, lb, ub; 
      
      for (ciy = 0; ciy < dy->u.fdd.child_count; ciy++) {
        if (   dy->u.fdd.arc[ciy].lower_bound <= 0
            && dy->u.fdd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
          conj = red_bop(AND, dx->u.ddd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (conj != NORM_FALSE) {
            lxly = dx->u.ddd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            lxuy = dx->u.ddd.arc[cix].lower_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
            uxly = dx->u.ddd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].lower_bound; 
            uxuy = dx->u.ddd.arc[cix].upper_bound 
	    / dy->u.fdd.arc[ciy].upper_bound; 
	    lb = flt_min(flt_min(lxly, lxuy), flt_min(uxly, uxuy)); 
	    ub = flt_max(flt_max(lxly, lxuy), flt_max(uxly, uxuy)); 
	    result = red_bop(OR, result, 
	      fdd_one_constraint(conj, FLOAT_VALUE, lb, ub)
	    ); 
    } } } }
    else if (dy->var_index == VI_VALUE) { 
      int		v, vx, vy; 
      struct red_type	*filter; 
      
      for (ciy = 0; ciy < dy->u.ddd.child_count; ciy++) {
        if (   dy->u.ddd.arc[ciy].lower_bound <= 0
            && dy->u.ddd.arc[ciy].upper_bound >= 0
            ) {
          fprintf(RED_OUT, 
            "\nERROR: division by zero in expression:\n"
          ); 
          red_print_graph(dy); 
          bk(0); 
        }
        for (cix = 0; cix < dx->u.ddd.child_count; cix++) {
          conj = red_bop(AND, dx->u.fdd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (conj != NORM_FALSE) {
	    filter = NORM_FALSE;
	    for (vx = dx->u.ddd.arc[cix].lower_bound; 
	         vx <= dx->u.ddd.arc[cix].upper_bound; 
	         vx++
	         ) 
	      for (vy = dy->u.ddd.arc[ciy].lower_bound; 
	           vy <= dy->u.ddd.arc[ciy].upper_bound; 
	           vy++
	           ) 
	        if (vy) {
		  v = vx / vy; 
		  filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v, v));
	        }
	    conj = red_bop(AND, conj, filter); 
	    result = red_bop(OR, result, conj); 
    } } } }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal 2nd root variable %1d:%s in red_multiply_value().\n", 
        dy->var_index, VAR[dy->var_index].NAME
      ); 
      bk(0); 
  } } 
  else { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal 1st root variable %1d:%s in red_multiply_value().\n", 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    bk(0); 
  }
  return(result);
}
  /* red_divide_value() */








int	count_oi = 0; 
struct red_type	*red_operand_indirection( 
  struct ps_exp_type	*var,  
  int			wpi 
) { 
  int			vi, flag; 
  struct red_type	*result; 

  if (var->type == TYPE_REFERENCE) { 
    vi = get_value(var, wpi, &flag); 
    if (flag != FLAG_SPECIFIC_VALUE) { 
      return(ddd_atom(RHS_PI, 0, VARIABLE_COUNT-1)); 
    } 
    else 
      return(ddd_atom(RHS_PI, vi, vi)); 
  } 
  else if (   var->type == TYPE_CLOCK 
           || var->type == TYPE_DENSE 
           || var->type == TYPE_DISCRETE 
           || var->type == TYPE_FLOAT 
           || var->type == TYPE_DOUBLE 
           || var->type == TYPE_POINTER
           || var->type == TYPE_BDD
           ) { 
/*
    if (var->u.atom.indirect_vi != NULL) { 
      return(ddd_atom(RHS_PI, 
        var->u.atom.indirect_vi[wpi], var->u.atom.indirect_vi[wpi]
      ) ); 
    }
*/
    vi = get_value(var->u.atom.exp_base_proc_index, wpi, &flag); 
    if (flag == FLAG_SPECIFIC_VALUE) { 
      return(ddd_atom(RHS_PI, 
        variable_index[var->type][vi][VAR[var->u.atom.var_index].OFFSET], 
        variable_index[var->type][vi][VAR[var->u.atom.var_index].OFFSET]
      ) ); 
    }
    else if (var->u.atom.exp_base_proc_index == PS_EXP__SP) {
      int	dpi, spvi; 
      
      spvi = variable_index[TYPE_DISCRETE][wpi][OFFSET__SP]; 
      result = NORM_FALSE; 
      for (dpi = 0; dpi < PROCESS[wpi].depth_call; dpi++) { 
      	vi = var->u.atom.var_index + dpi * HEIGHT_STACK_FRAME; 
      	result = red_bop(OR, result, 
      	  ddd_one_constraint(ddd_atom(RHS_PI, vi, vi), spvi, dpi, dpi)
      	); 
      } 
      return(result); 
    } 
    else if (var->u.atom.exp_base_proc_index == PS_EXP__SP_PLUS) { 
      int	dpi, spvi; 
      
      spvi = variable_index[TYPE_DISCRETE][wpi][OFFSET__SP]; 
      result = NORM_FALSE; 
      for (dpi = 0; dpi < PROCESS[wpi].depth_call-1; dpi++) { 
      	vi = var->u.atom.var_index + (dpi+1) * HEIGHT_STACK_FRAME; 
      	result = red_bop(OR, result, 
      	  ddd_one_constraint(ddd_atom(RHS_PI, vi, vi), spvi, dpi, dpi)
      	); 
      } 
      return(result); 
    } 
    else if (var->u.atom.exp_base_proc_index == PS_EXP__SP_MINUS) { 
      int	dpi, spvi; 
      
      spvi = variable_index[TYPE_DISCRETE][wpi][OFFSET__SP]; 
      result = NORM_FALSE; 
      for (dpi = 1; dpi < PROCESS[wpi].depth_call; dpi++) { 
      	vi = var->u.atom.var_index + (dpi-1) * HEIGHT_STACK_FRAME; 
      	result = red_bop(OR, result, 
      	  ddd_one_constraint(ddd_atom(RHS_PI, vi, vi), spvi, dpi, dpi)
      	); 
      } 
      return(result); 
    } 
    else { 
      int	pi; 

      result = NORM_FALSE; 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        vi = variable_index[var->type][pi][VAR[var->u.atom.var_index].OFFSET]; 
        result = red_bop(OR, result, 
          ddd_one_constraint(
            red_discrete_ineq(
              exp_arith(ARITH_EQ, 
                var->u.atom.exp_base_proc_index, 
                exp_atom(TYPE_CONSTANT, pi, NULL)
              ), 
              wpi
            ), 
            RHS_PI, vi, vi
        ) ); 
      } 
      return(result); 
    } 
  }
  else { 
    fprintf(RED_OUT, 
      "\nERROR, Illegal process index %1d in red_operand_indirection.\n", 
      wpi
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* red_operand_indirection() */ 




inline char	*name_var(int vi) { 
  if (vi == VARIABLE_COUNT) 
    return("***"); 
  else if (vi < 0) 
    return("---"); 
  else 
    return(VAR[vi].NAME); 
} 
  /* name_var() */ 






struct a23tree_type 
  *tree_collect_value_intervals; 


void	clear_value_intervals() { 
  int				pi, i; 
  
  if (GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE; i++) {
      free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][0][i]);  
      GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][0][i] = NULL;
  } } 
  if (GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE; i++) {
      free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_FLOAT][0][i]);  
      GLOBAL_INTERVAL_LIST[TYPE_FLOAT][0][i] = NULL;
  } } 
  if (GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE; i++) {
      free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][0][i]);  
      GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][0][i] = NULL;
  } } 
  if (GLOBAL_COUNT[TYPE_POINTER]) {
    for (i = 0; i < GLOBAL_COUNT[TYPE_POINTER]; i++) {
      free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_POINTER][0][i]); 
      GLOBAL_INTERVAL_LIST[TYPE_POINTER][0][i] = NULL; 
  } }
  if (LOCAL_COUNT[TYPE_DISCRETE]) 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (i = 0; i < LOCAL_COUNT[TYPE_DISCRETE]; i++) {
        free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][pi][i]); 
        GLOBAL_INTERVAL_LIST[TYPE_DISCRETE][pi][i] = NULL; 
    } }
  if (LOCAL_COUNT[TYPE_FLOAT]) 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (i = 0; i < LOCAL_COUNT[TYPE_FLOAT]; i++) {
        free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_FLOAT][pi][i]); 
        GLOBAL_INTERVAL_LIST[TYPE_FLOAT][pi][i] = NULL; 
    } }
  if (LOCAL_COUNT[TYPE_DOUBLE]) 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (i = 0; i < LOCAL_COUNT[TYPE_DOUBLE]; i++) {
        free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][pi][i]); 
        GLOBAL_INTERVAL_LIST[TYPE_DOUBLE][pi][i] = NULL; 
    } }

  if (LOCAL_COUNT[TYPE_POINTER]) 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (i = 0; i < LOCAL_COUNT[TYPE_POINTER]; i++) {
        free_interval_list(GLOBAL_INTERVAL_LIST[TYPE_POINTER][pi][i]); 
        GLOBAL_INTERVAL_LIST[TYPE_POINTER][pi][i] = NULL; 
    } }
}
  /* clear_value_intervals() */ 



inline void	var_collect_full_intervals(int i) { 
  switch (VAR[i].TYPE) { 
  case TYPE_DISCRETE: 
  case TYPE_POINTER:
    if (   (VAR[i].STATUS & FLAG_WORKING_IN_LAZY_EXP)
        && !(VAR[i].STATUS & FLAG_VAR_AUX_BOTTOM_ORDERING)
        )  
      GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET] 
      = insert_dint_link(
        GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET], 
        VAR[i].U.DISC.LB, VAR[i].U.DISC.UB, 
        VAR[i].U.DISC.LB, VAR[i].U.DISC.UB 
      );
    break; 
       
  case TYPE_FLOAT:
    if (   (VAR[i].STATUS & FLAG_WORKING_IN_LAZY_EXP)
        && !(VAR[i].STATUS & FLAG_VAR_AUX_BOTTOM_ORDERING)
        ) { 
/*      fprintf(RED_OUT, "\nrange collect all: vi=%1d:%s\n", 
        i, VAR[i].NAME
      ); 
      fprintf(RED_OUT, "  lb:%e, ub:%e\n", 
        VAR[i].U.FLT.LB, VAR[i].U.FLT.UB 
      ); 
      fprintf(RED_OUT, "  global interval list: %x\n", 
        GLOBAL_INTERVAL_LIST[VAR[i].TYPE]
        [VAR[i].PROC_INDEX]
        [VAR[i].OFFSET] 
      ); 
*/
      GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET] 
      = insert_fint_link(
        GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET], 
        VAR[i].U.FLT.LB, VAR[i].U.FLT.UB, 
        VAR[i].U.FLT.LB, VAR[i].U.FLT.UB 
      );
    }
    break; 
       
  case TYPE_DOUBLE:
    if (   (VAR[i].STATUS & FLAG_WORKING_IN_LAZY_EXP)
        && !(VAR[i].STATUS & FLAG_VAR_AUX_BOTTOM_ORDERING)
        )  {
/*
      fprintf(RED_OUT, "\nrange collect all: vi=%1d:%s\n", 
        i, VAR[i].NAME
      ); 
      fprintf(RED_OUT, "  lb:%e, ub:%e\n", 
        VAR[i].U.DBLE.LB, VAR[i].U.DBLE.UB 
      ); 
      fprintf(RED_OUT, "  global interval list: %x\n", 
        GLOBAL_INTERVAL_LIST[VAR[i].TYPE]
        [VAR[i].PROC_INDEX]
        [VAR[i].OFFSET] 
      ); 
*/
      GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET] 
      = insert_dfint_link(
        GLOBAL_INTERVAL_LIST[VAR[i].TYPE][VAR[i].PROC_INDEX][VAR[i].OFFSET], 
        VAR[i].U.DBLE.LB, VAR[i].U.DBLE.UB, 
        VAR[i].U.DBLE.LB, VAR[i].U.DBLE.UB 
      );
    }
    break; 
       
  } 
}
  /* var_collect_full_intervals() */ 





void	range_collect_full_intervals(
  int	vi, 
  int	vj
) {
  int	i; 
  
  for (i = vi; i< vj; i++) { 
    var_collect_full_intervals(i); 
  }
/*  
  if (vi > MEMORY_START_VI) { 
    for (i = MEMORY_START_VI; i < vi; i++) {
      var_collect_full_intervals(i); 
    }
  } 
  if (vj < VARIABLE_COUNT) { 
    if (vj < MEMORY_START_VI) { 
      for (i = MEMORY_START_VI; i < VARIABLE_COUNT; i++) {
        var_collect_full_intervals(i); 
    } }
    else {
      for (i = vj+1; i < VARIABLE_COUNT; i++) {
        var_collect_full_intervals(i); 
    } }
  } 
*/
}
  /* range_collect_full_intervals() */ 




inline int	min_full_range(
  int	vi_sgstart, 	// the local segment start
  int	vi_sgstop, 	// the local segment stop
  int	old_min_start, 	// the previous min start
  int	min_start	// the new min start from a child. 
) { 
  if (old_min_start <= min_start) 
    return(old_min_start); 
  else if (min_start > vi_sgstop+1) 
    return(min_start);  
  else 
    return(vi_sgstart); 
}
  /* min_full_range() */ 




int	count_rcolvi = 0; 

// The return value is the minimum index of variables that 
// have been fully marked. 
int	rec_collect_value_intervals(struct red_type *d) {
  int				vi, mci, ci, local_min_stop; 
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct rec_type		*nrec, *rec;

  if (   d == NORM_FALSE 
      || d == NORM_NO_RESTRICTION 
//       || d->var_index > VI_MAX_MARK 
      ) 
    return (VARIABLE_COUNT); 

  rec = rec_new(d, NULL); 
  nrec = (struct rec_type *) add_23tree(
    rec, tree_collect_value_intervals, 
    rec_comp, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return ((int) rec->result); 
  }

/*
  fprintf(RED_OUT, 
    "\nrec_collect_value_intervals()\n"
  ); 
  fprintf(RED_OUT, "from vi=%1d:%s, last_discrete_vi=%1d:%s\n-------\n", 
    vi, name_var(vi), last_discrete_vi, VAR[last_discrete_vi].NAME
  ); 
  fflush(RED_OUT); 
*/
  vi = d->var_index;
  switch (VAR[vi].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   d->u.bdd.zero_child == NORM_NO_RESTRICTION 
        || d->u.bdd.one_child == NORM_NO_RESTRICTION
        ) {
      range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
      mci = vi+1; 
    }
    else {
      local_min_stop = int_max(d->u.bdd.zero_child->var_index, 
        d->u.bdd.one_child->var_index
      ); 
      range_collect_full_intervals(vi+1, local_min_stop); 
      mci = min_full_range(vi+1, local_min_stop, VARIABLE_COUNT, 
        rec_collect_value_intervals(d->u.bdd.zero_child)
      );
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.bdd.one_child)
      );
    }
    break; 
  case TYPE_CRD:
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      if (d->u.crd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.crd.arc[ci].child->var_index) {
      	local_min_stop = d->u.crd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.crd.arc[ci].child)
      );
    break;
  case TYPE_HRD:
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) { 
      if (d->u.hrd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.hrd.arc[ci].child->var_index) {
      	local_min_stop = d->u.hrd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.hrd.arc[ci].child)
      );
    break;

  case TYPE_FLOAT: 
    if (VAR[vi].STATUS & FLAG_WORKING_IN_LAZY_EXP) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      	GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET] 
        = insert_fint_link(
            GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET], 
            VAR[vi].U.FLT.LB, VAR[vi].U.FLT.UB, 
            d->u.fdd.arc[ci].lower_bound, 
            d->u.fdd.arc[ci].upper_bound // , 
          ); 
    } }
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) { 
      if (d->u.fdd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.fdd.arc[ci].child->var_index) {
      	local_min_stop = d->u.fdd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.fdd.arc[ci].child)
      );
    }
    break; 

  case TYPE_DOUBLE: 
    if (VAR[vi].STATUS & FLAG_WORKING_IN_LAZY_EXP) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      	GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET] 
        = insert_dfint_link(
            GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET], 
            VAR[vi].U.DBLE.LB, VAR[vi].U.DBLE.UB, 
            d->u.dfdd.arc[ci].lower_bound, 
            d->u.dfdd.arc[ci].upper_bound // , 
          ); 
    } }
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) { 
      if (d->u.dfdd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.dfdd.arc[ci].child->var_index) {
      	local_min_stop = d->u.dfdd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.dfdd.arc[ci].child)
      );
    }
    break; 

  case TYPE_DISCRETE:
  case TYPE_POINTER:
  
    if (VAR[vi].STATUS & FLAG_WORKING_IN_LAZY_EXP) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      	GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET] 
        = insert_dint_link(
            GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET], 
            VAR[vi].U.DISC.LB, VAR[vi].U.DISC.UB, 
            d->u.ddd.arc[ci].lower_bound, 
            d->u.ddd.arc[ci].upper_bound // , 
          ); 
    } }
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      if (d->u.ddd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.ddd.arc[ci].child->var_index) {
      	local_min_stop = d->u.ddd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.ddd.arc[ci].child)
      );
    }
    break; 
    
  case TYPE_LAZY_EXP: 
    if (   d->u.lazy.false_child == NORM_NO_RESTRICTION
        || d->u.lazy.true_child == NORM_NO_RESTRICTION
        ) {
      range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
      rec->result = (struct red_type *) vi+1; 
      return (vi+1); 
    } 
    local_min_stop = int_max( 
      d->u.lazy.false_child->var_index, 
      d->u.lazy.true_child->var_index 
    ); 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = min_full_range(vi+1, local_min_stop, VARIABLE_COUNT, 
      rec_collect_value_intervals(d->u.lazy.false_child)
    );  
    mci = min_full_range(vi+1, local_min_stop, mci, 
      rec_collect_value_intervals(d->u.lazy.true_child)
    ); 
    break; 
  default: 
    local_min_stop = d->var_index; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      if (d->u.ddd.arc[ci].child == NORM_NO_RESTRICTION) {
        range_collect_full_intervals(vi+1, VARIABLE_COUNT); 
        rec->result = (struct red_type *) vi+1; 
        return (vi+1); 
      } 
      else if (local_min_stop < d->u.ddd.arc[ci].child->var_index) {
      	local_min_stop = d->u.ddd.arc[ci].child->var_index; 
      } 
    } 
    range_collect_full_intervals(vi+1, local_min_stop); 
    mci = VARIABLE_COUNT; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      mci = min_full_range(vi+1, local_min_stop, mci, 
        rec_collect_value_intervals(d->u.ddd.arc[ci].child)
      );
  } }
  rec->result = (struct red_type *) mci; 
  return (mci); 
}
/* rec_collect_value_intervals() */







// int	depth_colvi = 0; 

void	clear_flag_working_in_lazy_exp() { 
  int	i, pi, vi; 
  
  VI_MAX_MARK = 0; 
  VI_MIN_MARK = VARIABLE_COUNT; 
  
  for (i = 0; i < GLOBAL_COUNT[TYPE_DISCRETE]+MEMORY_DISCRETE_SIZE; i++) { 
    vi = variable_index[TYPE_DISCRETE][0][i]; 
    VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    for (i = 0; i < LOCAL_COUNT[TYPE_DISCRETE]; i++) { 
      vi = variable_index[TYPE_DISCRETE][pi][i]; 
      VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
    } 
  for (i = 0; i < GLOBAL_COUNT[TYPE_FLOAT]+MEMORY_FLOAT_SIZE; i++) { 
    vi = variable_index[TYPE_FLOAT][0][i]; 
    VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    for (i = 0; i < LOCAL_COUNT[TYPE_FLOAT]; i++) { 
      vi = variable_index[TYPE_FLOAT][pi][i]; 
      VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
    } 
  for (i = 0; i < GLOBAL_COUNT[TYPE_DOUBLE]+MEMORY_DOUBLE_SIZE; i++) { 
    vi = variable_index[TYPE_DOUBLE][0][i]; 
    VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    for (i = 0; i < LOCAL_COUNT[TYPE_DOUBLE]; i++) { 
      vi = variable_index[TYPE_DOUBLE][pi][i]; 
      VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
    } 
  for (i = 0; i < GLOBAL_COUNT[TYPE_POINTER]; i++) { 
    vi = variable_index[TYPE_POINTER][0][i]; 
    VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    for (i = 0; i < LOCAL_COUNT[TYPE_POINTER]; i++) { 
      vi = variable_index[TYPE_POINTER][pi][i]; 
      VAR[vi].STATUS = VAR[vi].STATUS & ~FLAG_WORKING_IN_LAZY_EXP; 	
    } 
}
  /* clear_flag_working_in_lazy_exp() */ 




void	collect_value_intervals(
  int			pi, 
  struct ps_exp_type	*lhs, 
  struct ps_exp_type	*exp, 
  struct red_type	*red_lazy_space
) {
  int	vi, flag, vi_min, vi_max, lpi, lvi; 
  
/*
  if (depth_colvi > 0) { 
    fprintf(RED_OUT, "\nCaught dirty value intervals.\n"); 
    fflush(RED_OUT); 	
  } 
  fprintf(RED_OUT, "\ncollect value intervals %1d:\n", ++depth_colvi); 
  fflush(RED_OUT); 
*/  

  clear_flag_working_in_lazy_exp(); 

  LAZY_PI = pi; 
  if (exp) 
    mark_working(exp, FLAG_WORKING_IN_LAZY_EXP); 
  if (lhs) { 
    switch (lhs->type) { 
    case TYPE_REFERENCE: 
      if (lhs->u.exp->var_status & FLAG_EXP_STATE_INSIDE) {
        range_mark_working(GLOBAL_SYSTEM_OVERHEAD_COUNT, 
          VARIABLE_COUNT-1, FLAG_WORKING_IN_LAZY_EXP
        ); 
      }
      else {
        vi = get_value(lhs->u.exp, pi, &flag); 
        if (flag == FLAG_SPECIFIC_VALUE) { 
          range_mark_working(vi, vi, FLAG_WORKING_IN_LAZY_EXP); 
        }
        else { 
      	  fprintf(RED_OUT, "\nERROR: There is something wrong.\n"); 
      	  bk(0); 
        } 
      }
      break; 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_FLOAT: 
    case TYPE_DOUBLE: 
    case TYPE_CLOCK: 
    case TYPE_DENSE: 
      // The cases for full range. 
      // 1. A[i][j] --> *(A+i)+j is the LHS address.  
      //    This implies that we need the contents of A[i] which could be 
      //    anything to decide the LHS address. 
      // 2. A[x] --> A+x is the LHS address which could be anything from x. 
      // 3. A@(x)[i] 
/*
      if (lhs->u.atom.indirect_count > 1) { 
      // Then we need to use the content of A[i]=*(A+i) 
      // to decide the LHS address. 
      // This could be very expensive to decide before hand anything. 
        range_mark_working(GLOBAL_SYSTEM_OVERHEAD_COUNT, 
          VARIABLE_COUNT-1, FLAG_WORKING_IN_LAZY_EXP
        ); 
        break; 
      } 
      else if (lhs->u.atom.indirect_count == 1) {
        if (lhs->u.atom.indirect_exp[0]->var_status & FLAG_EXP_STATE_INSIDE) {
          range_mark_working(GLOBAL_SYSTEM_OVERHEAD_COUNT, 
            VARIABLE_COUNT-1, FLAG_WORKING_IN_LAZY_EXP
          ); 
          break; 
        }
        vi = lhs->u.atom.var_index; 
      	if (!(VAR[vi].PROC_INDEX)) {
          range_mark_working(vi, vi, FLAG_WORKING_IN_LAZY_EXP); 
      	}
      	else if (lhs->u.atom.exp_base_proc_index->var_status 
                 & FLAG_EXP_STATE_INSIDE 
                 ){  
          for (lpi = 1; lpi <= PROCESS_COUNT; lpi++) {
            lvi = variable_index[VAR[vi].TYPE][lpi][VAR[vi].OFFSET]; 
            range_mark_working(lvi, lvi, FLAG_WORKING_IN_LAZY_EXP); 
          }
          mark_working(lhs->u.atom.exp_base_proc_index, 
            FLAG_WORKING_IN_LAZY_EXP
          ); 
        } 
        else { 
          lpi = get_value(lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          lvi = variable_index[VAR[vi].TYPE][lpi][VAR[vi].OFFSET]; 
          range_mark_working(lvi, lvi, FLAG_WORKING_IN_LAZY_EXP); 
        } 
        break; 
      }
      else 
*/
      if (  lhs->u.atom.exp_base_proc_index->var_status 
               & FLAG_EXP_STATE_INSIDE 
               ) { 
        mark_working(lhs->u.atom.exp_base_proc_index, 
          FLAG_WORKING_IN_LAZY_EXP
        ); 
        break; 
      } 
      break; 
    default: 
      fprintf(RED_OUT, "\nERROR: unexpected LHS type in collect_lhs_value_intervals().\n"); 
      pcform(lhs); 
      bk(0); 
    }
  } 
  if (VI_MIN_MARK > VI_MAX_MARK) {
    RED_LAZY_SPACE = NULL; 
    return; 
  }
  RED_LAZY_SPACE = red_lazy_space; 
  init_23tree(&tree_collect_value_intervals); 
  range_collect_full_intervals(GLOBAL_SYSTEM_OVERHEAD_COUNT, 
    red_lazy_space->var_index
  );  
  rec_collect_value_intervals(red_lazy_space); 
  free_entire_23tree(tree_collect_value_intervals, rec_free);
  init_23tree(&delayed_eval_tree); 
}
  /* collect_value_intervals() */ 






void	collect_value_intervals_in_red(
  int			pi, 
  struct red_type	*red_lazy_predicate, 
  struct red_type	*red_lazy_space 
) {
  int	vi_min, vi_max; 
  
/*
  if (depth_colvi > 0) { 
    fprintf(RED_OUT, "\nCaught dirty value intervals.\n"); 
    fflush(RED_OUT); 	
  } 
  fprintf(RED_OUT, "\ncollect value intervals %1d:\n", ++depth_colvi); 
  fflush(RED_OUT); 
*/  

  clear_flag_working_in_lazy_exp(); 

  LAZY_PI = pi; 
  mark_working_in_red(red_lazy_predicate, FLAG_WORKING_IN_LAZY_EXP); 
  if (VI_MIN_MARK > VI_MAX_MARK) {
    RED_LAZY_SPACE = NULL; 
    return; 
  }
  RED_LAZY_SPACE = red_lazy_space; 
  init_23tree(&tree_collect_value_intervals); 
  range_collect_full_intervals(10, red_lazy_space->var_index);  
  rec_collect_value_intervals(red_lazy_space); 
  free_entire_23tree(tree_collect_value_intervals, rec_free);
  init_23tree(&delayed_eval_tree); 
}
  /* collect_value_intervals_in_red() */ 



void	decollect_value_intervals() { 
/*
  fprintf(RED_OUT, "\nfree value intervals %1d:\n", --depth_colvi); 
  fflush(RED_OUT); 
*/
  if (RED_LAZY_SPACE) { 
    free_entire_23tree(delayed_eval_tree, rec_free); 
    clear_value_intervals(); 
    clear_flag_working_in_lazy_exp(); 
  }
}
  /* decollect_value_intervals() */ 




/**************************************************************
 *  Note that psub must be a parameter since 
 *  each pointer may involves its own rec_indirecrt_reference operation. 
 */
struct a23tree_type	*delayed_indirect_ref_tree; 

struct red_type	*rec_delayed_indirect_reference(
  struct ps_exp_type	*var, 
  int			vi, 
  int			indirect_index
) {
  int				ci, vv, ov, size_th = 0;
  struct interval_link_type	*ip; 
  struct rec_type		*rec, *nrec; 
  struct red_type		*conj, *result, *ind; 

  if (   vi < 0 
      || vi >= VARIABLE_COUNT 
/*
      || (   indirect_index < var->u.atom.indirect_count
          && VAR[vi].TYPE != TYPE_DISCRETE
          )
      || (   indirect_index == var->u.atom.indirect_count
          && VAR[vi].TYPE != TYPE_DISCRETE
          && VAR[vi].TYPE != TYPE_FLOAT
          && VAR[vi].TYPE != TYPE_DOUBLE
          )
*/
      ) 
    return(NORM_FALSE); 
  else /* if (indirect_index == var->u.atom.indirect_count) */ { 
    return(ddd_atom(RHS_PI, vi, vi)); 
  } 

/*
  ind = rec_delayed_exp_value(
    var->u.atom.indirect_exp[indirect_index] 
  ); 
  if (ind == NULL) 
    return (NULL); 

  result = NORM_FALSE; 
  ip = GLOBAL_INTERVAL_LIST
    [VAR[vi].TYPE]
    [VAR[vi].PROC_INDEX]
    [VAR[vi].OFFSET]; 
  for (; ip; ip = ip->next_interval_link) { 
    for (vv = ip->u.dint.lb; vv <= ip->u.dint.ub; vv++) { 
      size_th = size_th + ip->u.dint.ub - ip->u.dint.lb + 1; 
      if (size_th > THRESHOLD_LAZY_SIZE) 
        return(NULL); 
      for (ci = 0; ci < ind->u.ddd.child_count; ci++) { 
        for (ov = ind->u.ddd.arc[ci].lower_bound; 
             ov <= ind->u.ddd.arc[ci].upper_bound; 
             ov++
             ) { 
          size_th = size_th 
          + ind->u.ddd.arc[ci].upper_bound 
          - ind->u.ddd.arc[ci].lower_bound + 1; 
          conj = rec_delayed_indirect_reference(
            var, vv+ov, indirect_index+1
          ); 
          if (conj == NORM_FALSE)
            continue; 
          conj = red_bop(AND, conj, ind->u.ddd.arc[ci].child); 
          conj = ddd_one_constraint(conj, vi, vv, vv); 
          result = red_bop(OR, result, conj); 
        }
      } 
    }
  }
  return(result);
*/
}
/* rec_delayed_indirect_reference() */



struct red_type	*red_delayed_indirect_reference(
  struct ps_exp_type	*var, 
  int			vi 
) {
  struct red_type	*result; 
  
//  init_23tree(&delayed_indirect_ref_tree); 
  result = rec_delayed_indirect_reference(var, vi, 0); 
//  free_entire_23tree(delayed_indirect_ref_tree, rec_free); 
  return(result); 
} 
  /* red_delayed_indirect_reference() */ 



int	count_doind = 0; 


struct red_type	*rec_delayed_operand_indirection( 
  struct ps_exp_type	*var  
) { 
  int				pi, ci, vi, vx, v, local_count_doind; 
  struct red_type		*result, *red_addr, *conj; 
  struct interval_link_type	*ip; 

  /* It is assumed that W_PI = wpi. */ 
  switch (var->type) { 
  case TYPE_REFERENCE: 
  
// At this moment, I am not sure whether the following line should 
// be rec_delayed_operand_indirection() or rec_delayed_exp_value(). 
// The question is that whether we need different treatment for LHS and RHS 
// of an assignment ? 
// QQQQQQQQQQQQQQQQq  
    result = rec_delayed_exp_value(var->u.exp); 
    return(result); 
/*
    result = NORM_FALSE; 
    for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
      for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
           vi <= red_addr->u.ddd.arc[ci].upper_bound; 
	   vi++
	   ) { 
	vx = vi_in_primed_context(var, vi); 
	ip = GLOBAL_INTERVAL_LIST[VAR[vx].TYPE]
	  [VAR[vx].PROC_INDEX]
	  [VAR[vx].OFFSET]; 
	for (; ip; ip = ip->next_interval_link) { 
          for (v = ip->lb; v <= ip->ub; v++) { 
	    conj = ddd_one_constraint(
	      red_addr->u.ddd.arc[ci].child, RHS_PI, v, v
	    ); 
	    conj = ddd_one_constraint(conj, vx, v, v); 
	    result = red_bop(OR, result, conj); 
	} }
      } 
    } 
    return(result); 
*/
    break; 

  case TYPE_DEREFERENCE: 
    red_addr = rec_delayed_operand_indirection(var->u.exp); 
    if (red_addr == NULL) 
      return(NULL); 
    result = NORM_FALSE; 
    for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
      for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
           vi <= red_addr->u.ddd.arc[ci].upper_bound; 
	   vi++
	   ) { 
        conj = ddd_one_constraint(red_addr->u.ddd.arc[ci].child, 
          RHS_PI, vi, vi
        ); 
        result = red_bop(OR, result, conj); 
      }
    }
    break; 

  case TYPE_POINTER: 
  case TYPE_CLOCK: 
  case TYPE_DENSE: 
    if (var->u.atom.var->status & FLAG_LOCAL_VARIABLE) { 
      red_addr = rec_delayed_exp_value(var->u.atom.exp_base_proc_index); 
      if (red_addr == NULL) 
        return(NULL); 
      result = NORM_FALSE; 
      for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
        for (pi = red_addr->u.ddd.arc[ci].lower_bound; 
             pi <= red_addr->u.ddd.arc[ci].upper_bound; 
	     pi++
	     ) { 
	  vi = var->u.atom.var_index; 
          vi = variable_index[var->type][pi][VAR[vi].OFFSET]; 
          conj = ddd_one_constraint( 
            red_addr->u.ddd.arc[ci].child, RHS_PI, vi, vi 
          ); 
          result = red_bop(OR, result, conj); 
        }
      }
    } 
    else { 
      result = ddd_atom(VI_VALUE, 
        var->u.atom.var_index, var->u.atom.var_index
      ); 
    }   
    break; 
  case TYPE_DISCRETE: 
    PI_INDIRECT = LAZY_PI; 
    if (var->u.atom.var->status & FLAG_VAR_STACK) { 
      red_addr = rec_delayed_exp_value(var->u.atom.exp_base_proc_index); 
      if (red_addr == NULL) 
        return(NULL); 
      result = NORM_FALSE; 
      for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
        for (pi = red_addr->u.ddd.arc[ci].lower_bound; 
             pi <= red_addr->u.ddd.arc[ci].upper_bound; 
	     pi++
	     ) { 
	  if (pi<0 || pi >= DEPTH_CALL) 
	    continue; 

	  vi = var->u.atom.var_index; 
          vi = variable_index[var->type]
            [LAZY_PI]
            [VAR[vi].OFFSET+pi*HEIGHT_STACK_FRAME]; 
          conj = red_bop(AND, red_addr->u.ddd.arc[ci].child, 
            red_delayed_indirect_reference(var, vi) 
          ); 
          result = red_bop(OR, result, conj); 
        }
      }
    } 
    else if (var->u.atom.var->status & FLAG_LOCAL_VARIABLE) { 
      red_addr = rec_delayed_exp_value(var->u.atom.exp_base_proc_index); 
      if (red_addr == NULL) 
        return(NULL); 
      result = NORM_FALSE; 
      for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
        for (pi = red_addr->u.ddd.arc[ci].lower_bound; 
             pi <= red_addr->u.ddd.arc[ci].upper_bound; 
	     pi++
	     ) { 
	  if (pi<=0 || pi > PROCESS_COUNT) 
	    continue; 

	  vi = var->u.atom.var_index; 
          vi = variable_index[var->type][pi][VAR[vi].OFFSET]; 
          conj = red_bop(AND, red_addr->u.ddd.arc[ci].child, 
            red_delayed_indirect_reference(var, vi) 
          ); 
          result = red_bop(OR, result, conj); 
        }
      }
    } 
    else { 
      vi = var->u.atom.var_index; 
      result = red_delayed_indirect_reference(var, vi); 
    } 
  } 
  return(result); 
}
  /* rec_delayed_operand_indirection() */ 




struct red_type	*red_delayed_operand_indirection( 
  struct ps_exp_type	*var,  
  int			wpi, 
  struct red_type	*red_lazy_space  
) { 
  int			orig_evaluation; 
  struct red_type	*result; 

  /* It is assumed that W_PI = wpi. */ 
  orig_evaluation = FLAG_POLICY_EVALUATION; 
  FLAG_POLICY_EVALUATION = FLAG_DELAYED_EVALUATION; 
  LAZY_PI = wpi; 
  collect_value_intervals(wpi, var, NULL, red_lazy_space); 
  result = rec_delayed_operand_indirection(var); 
  decollect_value_intervals(); 
  FLAG_POLICY_EVALUATION = orig_evaluation;
  return(result); 
}
  /* red_delayed_operand_indirection() */ 




#ifdef RED_DEBUG_EXP_MODE
int	count_discrete_value = 0; 
#endif 

struct red_type	*rec_local(struct ps_exp_type *psub, int depth); 

struct red_type	*rec_discrete_value( 
  struct ps_exp_type	*psub 
) { 
  int				vi, v, cix, ciy, ci, ppi, vx, vy, value, 
				flag_simple, pi;
  struct ps_bunit_type		*pbu;
//  struct parse_indirect_type	*pt;
  struct red_type		*result, *childx, *childy, *conj, 
				*conjx, *conjy, *filter, *red_addr;
  struct ps_exp_type		*var;

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\ncount_discrete_value = %1d, psub=%x\n", 
    ++count_discrete_value, (unsigned int) psub
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  switch (psub->type) {
  case TYPE_FALSE :
  case TYPE_NULL:
    return(ddd_atom(VI_VALUE, 0, 0));
  case TYPE_TRUE :
    return(ddd_atom(VI_VALUE, 1, 1));
  case TYPE_LOCAL_IDENTIFIER: 
    if (W_PI > 0) 
      return(ddd_atom(VI_VALUE, W_PI, W_PI)); 
    else if (W_PI == 0 /* PROC_GLOBAL */) { 
      fprintf(RED_OUT, "Error: A local identifier in a global environment ?\n"); 
      bk(0); 
    } 
    else if (W_PI == FLAG_ANY_PROCESS || W_PI == FLAG_ANY_VALUE)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT));
    else if (W_PI == INDEX_LOCAL_IDENTIFIER) { 
      fprintf(RED_OUT, "Error: A local identifier in a local-identifier setting ?\n"); 
      bk(0); 
    } 
    else if (W_PI == FLAG_ANY_VARIABLE) { 
      return(ddd_atom(VI_VALUE, 0, VARIABLE_COUNT-1)); 
    } 
    else if (W_PI < 0 && W_PI >= -1*PROCESS_COUNT) { 
    	if (W_PI == -1 * PROCESS_COUNT) { 
    		return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1)); 
    	} 
    	else if (W_PI == -1) {
    		return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT)); 
    	}
    	else 
        return(red_bop(OR,
                       ddd_atom(VI_VALUE, 1, -W_PI-1),
                       ddd_atom(VI_VALUE, -W_PI+1, PROCESS_COUNT)
                       )
               );
    }
    else {
    	fprintf(RED_OUT, "Undefined process identifier values.\n"); 
    	fflush(RED_OUT); 
    	bk(0); 
    }
  case TYPE_PEER_IDENTIFIER:
    if (PROCESS_COUNT <= 1)
      return(NORM_FALSE);
    else if (W_PI < 0) 
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT)); 
    else if (W_PI == 1)
      return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT));
    else if (W_PI == PROCESS_COUNT)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1));
    else
      return(red_bop(OR,
		     ddd_atom(VI_VALUE, 1, W_PI-1),
		     ddd_atom(VI_VALUE, W_PI+1, PROCESS_COUNT)
		     )
	     );
  case TYPE_TRASH:
    return(NORM_NO_RESTRICTION);
  case TYPE_CONSTANT:
    return(ddd_atom(VI_VALUE, psub->u.value, psub->u.value)); 
  case TYPE_FLOAT_CONSTANT:
    return(fdd_atom(FLOAT_VALUE, psub->u.float_value, psub->u.float_value)); 
  case TYPE_MACRO_CONSTANT:
    return(ddd_atom(VI_VALUE, 
      psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value, 
      psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value
    ) ); 
  case TYPE_PROCESS_COUNT: 
    return(ddd_atom(VI_VALUE, PROCESS_COUNT, PROCESS_COUNT));
  case TYPE_MODE_INDEX: 
    return(ddd_atom(VI_VALUE, psub->u.mode_index.value, psub->u.mode_index.value));
  
  case TYPE_INTERVAL: 
    childx = rec_discrete_value(psub->u.interval.lbound_exp);
    childy = rec_discrete_value(psub->u.interval.rbound_exp);
    return(red_interval_value(childx, childy));

  case TYPE_QFD:
    v = qfd_value(psub->u.atom.var_name);
    return(ddd_atom(VI_VALUE, v, v));
  
  case TYPE_REFERENCE: 
    red_addr = rec_discrete_value(psub->u.exp); 
    if (   red_addr == NULL 
        || red_addr == NORM_FALSE 
        || red_addr == NORM_NO_RESTRICTION
        ) 
      return(red_addr); 
    result = NORM_FALSE; 
    for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
      for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
           vi <= red_addr->u.ddd.arc[ci].upper_bound; 
           vi++
           ) { 
        if (VAR[vi].TYPE != TYPE_DISCRETE) 
          continue; 
        for (v = VAR[vi].U.DISC.LB; v <= VAR[vi].U.DISC.UB; v++) { 
          conj = ddd_one_constraint(red_addr->u.ddd.arc[ci].child, 
            vi, v, v
          ); 
          conj = ddd_one_constraint(conj, VI_VALUE, v, v); 
          result = red_bop(OR, result, conj); 
        } 	
      } 
    } 
    return(result); 
    break;     
  case TYPE_DEREFERENCE: 
    red_addr = red_operand_indirection(psub->u.exp, W_PI); 
    if (   red_addr == NULL 
        || red_addr == NORM_FALSE 
        || red_addr == NORM_NO_RESTRICTION
        ) 
      return(red_addr); 

    result = NORM_FALSE; 
    for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
      result = red_bop(OR, result, 
        ddd_one_constraint(red_addr->u.ddd.arc[ci].child, 
          VI_VALUE, red_addr->u.ddd.arc[ci].lower_bound, 
          red_addr->u.ddd.arc[ci].upper_bound
      ) ); 
    } 
    return(result); 
    break; 

  case TYPE_POINTER:
    vi = psub->u.atom.var_index; 
    vi = variable_index[TYPE_POINTER][W_PI][VAR[vi].OFFSET]; 
    if (   VAR[vi].PROC_INDEX 
        && (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      result = NORM_FALSE; 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	result = red_bop(OR, result, 
      	  ddd_lone_subtree(ddd_atom(vi, pi, pi), 
      	    VI_VALUE, pi, pi
      	) ); 
      } 
      return(result); 
    }
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, 
      "\nWarning: We are not able to enumerate all values of %s\n", 
      psub->u.atom.var->name 
    ); 
    fprintf(RED_OUT, 
      "         which is a floating point number in red_discrete_value().\n"
    ); 
    return(NORM_NO_RESTRICTION); 
  case TYPE_DISCRETE:
    red_addr = red_operand_indirection(psub, W_PI); 
    if (red_addr == NULL) 
      return(NULL); 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "red_addr with psub->u.atom.var_index:%1d\n", psub->u.atom.var_index); 
    red_print_graph(red_addr); 
    #endif 
    
    result = NORM_FALSE; 
    #ifdef RED_DEBUG_EXP_MODE
    pcform(psub); 
    #endif 
    
    switch (FLAG_POLICY_EVALUATION) { 
    case FLAG_LAZY_EVALUATION: 
      for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
        for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	     vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	     vi++
	     ) { 
          #ifdef RED_DEBUG_EXP_MODE
	  fprintf(RED_OUT, 
	    "count_discrete_value=%1d, in rec_discrete_value for vi=%1d\n", 
	    count_discrete_value, 
	    vi
	  ); 
	  fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	  fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
	  #endif 
	
	  for (v = VAR[vi].U.DISC.LB; v <= VAR[vi].U.DISC.UB; v++) { 
	    childx = ddd_one_constraint(
	      red_addr->u.ddd.arc[cix].child, VI_VALUE, v, v
	    ); 
	    childx = ddd_one_constraint(childx, vi, v, v); 
	    result = red_bop(OR, result, childx); 
	  }
	} 
      } 
      break; 
    case FLAG_DELAYED_EVALUATION: 
      for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
        for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
             vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	     vi++
	     ) { 
          #ifdef RED_DEBUG_EXP_MODE
	  fprintf(RED_OUT, 
	    "count_discrete_value=%1d, in rec_discrete_value for vi=%1d\n", 
	    count_discrete_value, 
	    vi
	  ); 
	  fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	  fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
	  #endif 
	
	  for (v = VAR[vi].U.DISC.LB; v <= VAR[vi].U.DISC.UB; v++) { 
	    childx = ddd_one_constraint(
	      red_addr->u.ddd.arc[cix].child, VI_VALUE, v, v
	    ); 
	    childx = ddd_one_constraint(childx, vi, v, v); 
	    result = red_bop(OR, result, childx); 
	  }
	} 
      } 
      break; 
    } 
    if (red_path_threshold(result, 100))   
      return(NULL); 
    else 
      return(result); 

  case TYPE_CLOCK:
    result = NORM_FALSE; 
    red_addr = red_operand_indirection(psub, W_PI); 
    if (red_addr == NULL) 
      return(NULL); 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      conj = red_addr->u.ddd.arc[cix].child;
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
	ci = VAR[vi].U.CLOCK.CLOCK_INDEX;  
	for (v = 0; v < CLOCK_POS_INFINITY; v = v+2) { 
	  childx = crd_one_constraint(conj, ZONE[ci][0], v+1); 
	  childx = crd_one_constraint(childx, ZONE[0][ci], -1 * v); 
	  childx = ddd_one_constraint(childx, VI_VALUE, v/2, v/2); 
	  result = red_bop(OR, result, childx); 
	} 
      }
    }
    if (red_path_threshold(result, 100))   
      return(NULL); 
    else 
      return(result); 
/*
    fprintf(RED_OUT, 
      "\nError: unexpected dense variable %s in red_discrete_value().\n", 
      psub->u.atom.var_name
    ); 
    fflush(RED_OUT); 
    exit(0); 
*/
    break;
  case TYPE_DENSE:
    fprintf(RED_OUT, "\nBug: how come there is a dense variable in a discrete expression!\n");
    fflush(RED_OUT);
    exit(0);
    break; 
  case TYPE_QSYNC_HOLDER: 
    vi = variable_index[TYPE_POINTER][W_PI][psub->u.qsholder.qsync_var->index]; 
    result = NORM_FALSE;
    for (v = 1; v <= PROCESS_COUNT; v++)
      result = red_bop(OR, result, ddd_one_constraint(ddd_atom(VI_VALUE, v, v), vi, v, v)); 
    return(result); 
    break; 
  case BIT_NOT: 
    
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    if (   psub->u.arith.lhs_exp->type == TYPE_FLOAT
        || psub->u.arith.lhs_exp->type == TYPE_DOUBLE
        || psub->u.arith.rhs_exp->type == TYPE_FLOAT
        || psub->u.arith.rhs_exp->type == TYPE_DOUBLE
        ) { 
      fprintf(RED_OUT, 
        "\nERROR: Apparently someone tries to do Boolean operation %s\n", 
        ps_exp_type_name(psub->type)
      ); 
      fprintf(RED_OUT, 
        "       on floating point expression(s) in red_discrete_value().\n"
      ); 
      bk(0); 
    } 
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
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
    childx = rec_discrete_value(psub->u.arith.lhs_exp); 
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp); 
    if (!childy) 
      return(NULL); 
    result = red_add_value(1, childx, 1, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MINUS:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
    if (!childy) 
      return(NULL); 
    result = red_add_value(1, childx, -1, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 

  case ARITH_MULTIPLY:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
    if (!childy) 
      return(NULL); 
    result = red_multiply_value(childx, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_DIVIDE:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp); 
    if (!childy) 
      return(NULL); 
    result = red_divide_value(childx, childy); 
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MODULO: 
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp); 
    if (!childy) 
      return(NULL); 
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
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result);     
    break; 
  case ARITH_CONDITIONAL: 
    conj = rec_local(psub->u.arith_cond.cond, 0); 
    if (!conj) 
      return(NULL); 
    childx = rec_discrete_value(psub->u.arith_cond.if_exp); 
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith_cond.else_exp); 
    if (!childy) 
      return(NULL); 
    result = red_bop(OR, 
      red_bop(AND, conj, childx), 
      red_bop(AND, red_complement(conj), childy)
    ); 
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
    break; 
  case TYPE_INLINE_CALL: 
    return(rec_discrete_value(psub->u.inline_call.instantiated_exp)); 
  case TYPE_BDD:
    fprintf(RED_OUT, 
      "\nError: unexpected bdd variable %s in an arithmetic expression.\n", 
      psub->u.atom.var_name 
    );   
    fflush(RED_OUT); 
    exit(0); 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "\nError: unexpected synchronizer variable %s in arithmetic an expression.\n", 
      psub->u.atom.var_name 
    );   
    fflush(RED_OUT); 
    exit(0); 
  }
}
/* rec_discrete_value() */ 




struct red_type	*red_discrete_value(
  int			pi, 
  struct ps_exp_type	*psub
) {
  struct ps_exp_type	*tmp; 
  
  W_PI = pi; 
  if (psub->var_status & FLAG_EXP_STATE_INSIDE) {
    tmp = exp_arith(ARITH_EQ, 
      exp_atom(TYPE_DISCRETE, VI_VALUE, VAR[VI_VALUE].NAME), psub
    ); 
    return(lazy_atom(W_PI, tmp)); 
  }
  return(rec_discrete_value(psub)); 
}
/* red_discrete_value() */




struct red_type	*red_discrete_value_top_level(
  int			wpi, 
  struct ps_exp_type	*psub, 
  int			lb, 
  int			ub 
) {
  int				vi, v, cix, ciy, ci, ppi, vx, vy, value, 
				wlb, wub, 
				flag_simple, pi;
  struct ps_bunit_type		*pbu;
//  struct parse_indirect_type	*pt;
  struct red_type		*result, *childx, *childy, *conj, *conj2, 
				*conjx, *conjy, *filter, *red_addr;
  struct ps_exp_type		*var;

  W_PI = wpi; 

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\ncount_discrete_value = %1d\n", ++count_discrete_value); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  switch (psub->type) {
  case TYPE_FALSE :
  case TYPE_NULL:
    return (red_check_value_range(0, lb, ub)); 
  case TYPE_TRUE :
    return (red_check_value_range(1, lb, ub)); 
  case TYPE_LOCAL_IDENTIFIER: 
    if (W_PI > 0) 
      return (red_check_value_range(W_PI, lb, ub)); 
    else if (W_PI == 0 /* PROC_GLOBAL */) { 
      fprintf(RED_OUT, "Error: A local identifier in a global environment ?\n"); 
      bk(0); 
    } 
    else if (W_PI == FLAG_ANY_PROCESS || W_PI == FLAG_ANY_VALUE)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT));
    else if (W_PI == INDEX_LOCAL_IDENTIFIER) { 
      fprintf(RED_OUT, "Error: A local identifier in a local-identifier setting ?\n"); 
      bk(0); 
    } 
    else if (W_PI == FLAG_ANY_VARIABLE) { 
      return(ddd_atom(VI_VALUE, 0, VARIABLE_COUNT-1)); 
    } 
    else if (W_PI < 0 && W_PI >= -1*PROCESS_COUNT) { 
      if (W_PI == -1 * PROCESS_COUNT) { 
    	return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1)); 
      } 
      else if (W_PI == -1) {
    	return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT)); 
      }
      else 
        return(red_bop(OR,
                       ddd_atom(VI_VALUE, 1, -W_PI-1),
                       ddd_atom(VI_VALUE, -W_PI+1, PROCESS_COUNT)
                       )
               );
    }
    else {
    	fprintf(RED_OUT, "Undefined process identifier values.\n"); 
    	fflush(RED_OUT); 
    	bk(0); 
    }
  case TYPE_PEER_IDENTIFIER:
    if (PROCESS_COUNT <= 1)
      return(NORM_FALSE);
    else if (W_PI < 0) 
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT)); 
    else if (W_PI == 1)
      return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT));
    else if (W_PI == PROCESS_COUNT)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1));
    else
      return(red_bop(OR,
		     ddd_atom(VI_VALUE, 1, W_PI-1),
		     ddd_atom(VI_VALUE, W_PI+1, PROCESS_COUNT)
		     )
	     );
  case TYPE_TRASH:
    return(NORM_NO_RESTRICTION);
  case TYPE_CONSTANT:
    return (red_check_value_range(psub->u.value, lb, ub)); 
  case TYPE_PROCESS_COUNT: 
    return (red_check_value_range(PROCESS_COUNT, lb, ub)); 
  case TYPE_MODE_INDEX: 
    return (red_check_value_range(psub->u.mode_index.value, lb, ub)); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    return(rec_discrete_value(psub)); 
 
  case TYPE_INTERVAL: 
    childx = rec_discrete_value(psub->u.interval.lbound_exp);
    if (!childx) 
      return(NULL); 
    childy = rec_discrete_value(psub->u.interval.rbound_exp); 
    if (!childy) 
      return(NULL); 
    return(red_interval_value_top_level(childx, childy, lb, ub));

  case TYPE_QFD:
    v = qfd_value(psub->u.atom.var_name);
    return(red_check_value_range(v, lb, ub));
  case TYPE_DISCRETE:
  case TYPE_POINTER:
    red_addr = red_operand_indirection(psub, W_PI); 
    if (!red_addr) 
      return(NULL); 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "red_addr with psub->u.atom.var_index:%1d\n", psub->u.atom.var_index); 
    red_print_graph(red_addr); 
    #endif 
    
    result = NORM_FALSE; 
    #ifdef RED_DEBUG_EXP_MODE
//    for (; count_discrete_value == -1 /*1323*/; ) ;  
    pcform(psub); 
    #endif 
    
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, 
	  "count_discrete_value=%1d, in rec_discrete_value for vi=%1d\n", 
	  count_discrete_value, 
	  vi
	); 
	fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
	#endif 

	wlb = int_max(lb, VAR[vi].U.DISC.LB); 
	wub = int_min(ub, VAR[vi].U.DISC.UB); 
	for (v = wlb; v <= wub; v++) { 
	  childx = ddd_one_constraint(red_addr->u.ddd.arc[cix].child, 
	    VI_VALUE, v, v
	  ); 
	  childx = ddd_one_constraint(childx, vi, v, v); 
	  result = red_bop(OR, result, childx); 
	} 
      } 
    } 
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 

  case TYPE_CLOCK:
    result = NORM_FALSE; 
    red_addr = red_operand_indirection(psub, W_PI); 
    if (!red_addr) 
      return(NULL); 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      conj = red_addr->u.ddd.arc[cix].child;
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
	ci = VAR[vi].U.CLOCK.CLOCK_INDEX;  
	wlb = int_max(0, 2*lb); 
	wub = int_min(CLOCK_POS_INFINITY, 2*ub+1); 
	for (v = wlb; v < wub; v = v+2) { 
	  childx = crd_one_constraint(conj, ZONE[ci][0], v+1); 
	  childx = crd_one_constraint(childx, ZONE[0][ci], -1 * v); 
	  childx = ddd_one_constraint(childx, VI_VALUE, v/2, v/2); 
	  result = red_bop(OR, result, childx); 
	} 
      }
    }
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
/*
    fprintf(RED_OUT, 
      "\nError: unexpected dense variable %s in red_discrete_value().\n", 
      psub->u.atom.var_name
    ); 
    fflush(RED_OUT); 
    exit(0); 
*/
    break;
  case TYPE_DENSE:
    fprintf(RED_OUT, "\nBug: how come there is a dense variable in a discrete expression!\n");
    fflush(RED_OUT);
    exit(0);
    break; 
  case TYPE_QSYNC_HOLDER: 
    vi = variable_index[TYPE_POINTER][W_PI][psub->u.qsholder.qsync_var->index]; 
    result = NORM_FALSE;
    for (v = 1; v <= PROCESS_COUNT; v++) {
      conj = red_check_value_range(v, lb, ub); 
      if (conj != NORM_FALSE) 
        result = red_bop(OR, result, ddd_one_constraint(conj, vi, v, v)); 
    }
    return(result); 
    break; 
  case BIT_NOT: 
    childx = rec_discrete_value(psub->u.exp); 
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
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
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
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_add_value_top_level(1, childx, 1, childy, lb, ub);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MINUS:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_add_value_top_level(1, childx, -1, childy, lb, ub);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MULTIPLY:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_multiply_value_top_level(childx, childy, lb, ub);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_DIVIDE:
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp); 
    if (!childy)
      return(NULL); 
    result = NORM_FALSE;
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) 
      for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) {
	conj = red_bop(AND, childx->u.ddd.arc[cix].child, childy->u.ddd.arc[ciy].child); 
	if (conj != NORM_FALSE) {
	  filter = NORM_FALSE; 
	  for (vx = childx->u.ddd.arc[cix].lower_bound; vx <= childx->u.ddd.arc[cix].upper_bound; vx++) 
	    for (vy = childy->u.ddd.arc[ciy].lower_bound; vy <= childy->u.ddd.arc[ciy].upper_bound; vy++) 
	      if (vy) {
		conj2 = red_check_value_range(vx / vy, lb, ub); 
		if (conj2 != NORM_FALSE) 
		  filter = red_bop(OR, filter, conj2);
	      }
	  conj = red_bop(AND, conj, filter); 
	  result = red_bop(OR, result, conj); 
	}
      }
    return(result); 
  case ARITH_MODULO: 
    childx = rec_discrete_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_discrete_value(psub->u.arith.rhs_exp); 
    if (!childy)
      return(NULL); 
    result = NORM_FALSE;
    for (cix = 0; cix < childx->u.ddd.child_count; cix++) 
      for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) {
	conj = red_bop(AND, childx->u.ddd.arc[cix].child, childy->u.ddd.arc[ciy].child); 
	if (conj != NORM_FALSE) {
	  filter = NORM_FALSE; 
	  for (vx = childx->u.ddd.arc[cix].lower_bound; vx <= childx->u.ddd.arc[cix].upper_bound; vx++) 
	    for (vy = childy->u.ddd.arc[ciy].lower_bound; vy <= childy->u.ddd.arc[ciy].upper_bound; vy++) 
	      if (vy) {
		conj2 = red_check_value_range(vx % vy, lb, ub); 
		if (conj2 != NORM_FALSE) 
		  filter = red_bop(OR, filter, conj2);
	      }
	  conj = red_bop(AND, conj, filter); 
	  result = red_bop(OR, result, conj); 
	}
      }
    return(result);     
    break; 
  case ARITH_CONDITIONAL: 
    conj = rec_local(psub->u.arith_cond.cond, 0); 
    if (!conj)
      return(NULL); 
    childx = red_discrete_value_top_level(
      wpi, psub->u.arith_cond.if_exp, lb, ub 
    ); 
    if (!childx)
      return(NULL); 
    childy = red_discrete_value_top_level(
      wpi, psub->u.arith_cond.else_exp, lb, ub
    ); 
    if (!childy)
      return(NULL); 
    return(red_bop(OR, 
      red_bop(AND, conj, childx), 
      red_bop(AND, red_complement(conj), childy)
    ) ); 
    break; 
  case TYPE_INLINE_CALL: 
    return(rec_discrete_value(psub->u.inline_call.instantiated_exp)); 
  case TYPE_BDD:
    fprintf(RED_OUT, 
      "\nError: unexpected bdd variable %s in an arithmetic expression.\n", 
      psub->u.atom.var_name 
    );   
    fflush(RED_OUT); 
    exit(0); 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "\nError: unexpected synchronizer variable %s in arithmetic an expression.\n", 
      psub->u.atom.var_name 
    );   
    fflush(RED_OUT); 
    exit(0); 
  }
}
/* red_discrete_value_top_level() */ 






struct red_type	*red_value_ineq(op, lred, rred, flag_delayed_evaluation)
     int		op; 
     struct red_type	*lred, *rred;
     int		flag_delayed_evaluation; 
{
  int			cix, ciy, ystart; 
  struct red_type	*conj, *result, **acc, *ytotal;

  switch(op) {
  case EQ: 
  case ARITH_EQ :
    result = NORM_FALSE;
    for (ystart = 0, cix = 0; cix < lred->u.ddd.child_count; cix++) { 
      for (ciy = ystart; ciy < rred->u.ddd.child_count; ciy++) { 
      	if (rred->u.ddd.arc[ciy].upper_bound >= lred->u.ddd.arc[cix].lower_bound) {
	  ystart = ciy; 
	  break; 
	} 
      }
      for (; 
	      ciy < rred->u.ddd.child_count 
	   && rred->u.ddd.arc[ciy].lower_bound <= lred->u.ddd.arc[cix].upper_bound; 
	   ciy++
	   ) { 
	conj = red_bop(AND, lred->u.ddd.arc[cix].child, rred->u.ddd.arc[ciy].child); 
	result = red_bop(OR, result, conj); 
      }
    }
    return(result); 
    break; 

  case NEQ: 
  case ARITH_NEQ: 
    acc = (struct red_type **) malloc(rred->u.ddd.child_count * sizeof(struct red_type *)); 
    acc[rred->u.ddd.child_count-1] = NORM_FALSE; 
    ytotal = rred->u.ddd.arc[rred->u.ddd.child_count-1].child; 
    for (ciy = rred->u.ddd.child_count-2; ciy >= 0; ciy--) { 
      acc[ciy] = red_bop(OR, acc[ciy+1], rred->u.ddd.arc[ciy+1].child); 
      ytotal = red_bop(OR, ytotal, rred->u.ddd.arc[ciy].child); 
    } 
    result = NORM_FALSE; 
    conj = NORM_FALSE; 
    for (ystart = 0, cix = 0; cix < lred->u.ddd.child_count; cix++) { 
      if (lred->u.ddd.arc[cix].lower_bound < lred->u.ddd.arc[cix].upper_bound) {
        result = red_bop(OR, result, red_bop(AND, ytotal, lred->u.ddd.arc[cix].child)); 
        continue; 
      } 
      for (ciy = ystart; ciy < rred->u.ddd.child_count; ciy++) { 
      	if (lred->u.ddd.arc[cix].lower_bound <= rred->u.ddd.arc[ciy].upper_bound) {
	  ystart = ciy; 
	  break; 
	} 
	else 
	  conj = red_bop(OR, conj, rred->u.ddd.arc[ciy].child); 
      } 
      if (ciy >= rred->u.ddd.child_count) { 
      	ystart = ciy; 
        result = red_bop(OR, result, red_bop(AND, ytotal, lred->u.ddd.arc[cix].child)); 
        continue;       	
      } 
      else if (   rred->u.ddd.arc[ciy].lower_bound < rred->u.ddd.arc[ciy].upper_bound
	       || rred->u.ddd.arc[ciy].lower_bound != lred->u.ddd.arc[cix].lower_bound
	       ) { 
        result = red_bop(OR, result, red_bop(AND, ytotal, lred->u.ddd.arc[cix].child)); 
        continue;       	
      } 
      else { 
      	if (ciy < rred->u.ddd.child_count - 1) 
      	  result = red_bop(OR, result, red_bop(AND, acc[ciy], lred->u.ddd.arc[cix].child)); 
      	result = red_bop(OR, result, red_bop(AND, conj, lred->u.ddd.arc[cix].child)); 
      } 
    }
    free(acc); 
    return(result);     
    break; 

  case LEQ: 
  case ARITH_LEQ:
    acc = (struct red_type **) malloc(lred->u.ddd.child_count * sizeof(struct red_type *)); 
    acc[0] = lred->u.ddd.arc[0].child; 
    for (cix = 1; cix < lred->u.ddd.child_count; cix++) { 
      acc[cix] = red_bop(OR, acc[cix-1], lred->u.ddd.arc[cix].child); 
    } 
    result = NORM_FALSE;
    conj = NORM_FALSE; 
    for (cix = lred->u.ddd.child_count-1, ciy = rred->u.ddd.child_count-1; cix >= 0; cix--) { 
      for (; 
	   ciy >=0 && lred->u.ddd.arc[cix].lower_bound <= rred->u.ddd.arc[ciy].upper_bound; 
	   ciy--
	   ) 
      	conj = red_bop(OR, conj, rred->u.ddd.arc[ciy].child);  
      acc[cix] = red_bop(AND, acc[cix], conj); 
      result = red_bop(OR, result, acc[cix]); 
    }
    free(acc); 
    return(result); 
    break; 

  case LESS: 
  case ARITH_LESS: 
    acc = (struct red_type **) malloc(lred->u.ddd.child_count * sizeof(struct red_type *)); 
    acc[0] = lred->u.ddd.arc[0].child; 
    for (cix = 1; cix < lred->u.ddd.child_count; cix++) { 
      acc[cix] = red_bop(OR, acc[cix-1], lred->u.ddd.arc[cix].child); 
    } 
    result = NORM_FALSE;
    conj = NORM_FALSE; 
    for (cix = lred->u.ddd.child_count-1, ciy = rred->u.ddd.child_count-1; cix >= 0; cix--) { 
      for (; 
	   ciy >=0 && lred->u.ddd.arc[cix].lower_bound < rred->u.ddd.arc[ciy].upper_bound; 
	   ciy--
	   ) 
      	conj = red_bop(OR, conj, rred->u.ddd.arc[ciy].child);  
      acc[cix] = red_bop(AND, acc[cix], conj); 
      result = red_bop(OR, result, acc[cix]); 
    }
    free(acc); 
    return(result); 
    break; 

  case GREATER: 
  case ARITH_GREATER: 
    acc = (struct red_type **) malloc(rred->u.ddd.child_count * sizeof(struct red_type *)); 
    acc[0] = rred->u.ddd.arc[0].child; 
    for (ciy = 1; ciy < rred->u.ddd.child_count; cix++) { 
      acc[ciy] = red_bop(OR, acc[ciy-1], rred->u.ddd.arc[ciy].child); 
    } 
    result = NORM_FALSE;
    conj = NORM_FALSE; 
    for (cix = lred->u.ddd.child_count-1, ciy = rred->u.ddd.child_count-1; ciy >= 0; ciy--) { 
      for (; 
	   cix >=0 && rred->u.ddd.arc[ciy].lower_bound < lred->u.ddd.arc[cix].upper_bound; 
	   cix--
	   ) 
      	conj = red_bop(OR, conj, lred->u.ddd.arc[cix].child);  
      acc[ciy] = red_bop(AND, acc[ciy], conj); 
      result = red_bop(OR, result, acc[ciy]); 
    }
    free(acc); 
    return(result); 
    break; 

  case GEQ: 
  case ARITH_GEQ: 
    acc = (struct red_type **) malloc(rred->u.ddd.child_count * sizeof(struct red_type *)); 
    acc[0] = rred->u.ddd.arc[0].child; 
    for (ciy = 1; ciy < rred->u.ddd.child_count; cix++) { 
      acc[ciy] = red_bop(OR, acc[ciy-1], rred->u.ddd.arc[ciy].child); 
    } 
    result = NORM_FALSE;
    conj = NORM_FALSE; 
    for (cix = lred->u.ddd.child_count-1, ciy = rred->u.ddd.child_count-1; ciy >= 0; ciy--) { 
      for (; 
	   cix >=0 && rred->u.ddd.arc[ciy].lower_bound <= lred->u.ddd.arc[cix].upper_bound; 
	   cix--
	   ) 
      	conj = red_bop(OR, conj, lred->u.ddd.arc[cix].child);  
      acc[ciy] = red_bop(AND, acc[ciy], conj); 
      result = red_bop(OR, result, acc[ciy]); 
    }
    free(acc); 
    return(result); 
    break; 

  }

}
/* red_value_ineq() */ 







inline struct red_type	*rec_clock_ineq_bottom_analysis(
  op,  
  c1, 
  c2, 
  offset_lb, offset_ub
) {
  struct red_type	*result; 
  
  switch(op) { 
  case EQ : 
    result = crd_atom(ZONE[c1][c2], 2*offset_ub); 
    result = crd_one_constraint(result, ZONE[c2][c1], -2*offset_lb); 
    return(result); 
    
  case NEQ:
    result = crd_atom(ZONE[c1][c2], 2*offset_lb - 1); 
    result = red_bop(OR, result, 
      crd_atom(ZONE[c2][c1], -2*offset_ub - 1)
    ); 
    return(result); 
   
  case LEQ:
    return(crd_atom(ZONE[c1][c2], 2*offset_ub)); 
    
  case LESS: 
    return(crd_atom(ZONE[c1][c2], 2*offset_ub-1)); 
    
  case GREATER: 
    return(crd_atom(ZONE[c2][c1], -2*offset_lb-1)); 
   
  case GEQ: 
    return(crd_atom(ZONE[c2][c1], -2*offset_lb));     
  }

}
  /* rec_clock_ineq_bottom_analysis() */ 





inline struct red_type	*rec_clock_ineq_offset_analysis( 
  int			op, 
  int			pi, 
  int			c1, 
  int			c2, 
  int			offset_lb, 
  int			offset_ub, 
  struct red_type	*red_offset
) {
  struct red_type	*result, *conj; 
  int			ci; 
  
  if (red_offset == NULL) 
    return(rec_clock_ineq_bottom_analysis(
      op,  
      c1, 
      c2, 
      offset_lb, offset_ub
    ) ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_offset->u.ddd.child_count; ci++) { 
    conj = red_bop(AND, red_offset->u.ddd.arc[ci].child, 
      rec_clock_ineq_bottom_analysis( 
        op, c1, c2, 
        red_offset->u.ddd.arc[ci].lower_bound, 
        red_offset->u.ddd.arc[ci].upper_bound
    ) ); 
    result = red_bop(OR, result, conj); 
  } 
  return(result); 
}
  /* rec_clock_ineq_offset_analysis() */ 
  
  
  
inline struct red_type	*rec_clock_ineq_neg_analysis( 
  int			op, 
  int			pi, 
  int			c1, 
  struct ps_exp_type	*cv2, 
  int			c2, 
  struct red_type	*ropd, 
  int			offset_lb, 
  int			offset_ub, 
  struct red_type	*red_offset
) {
  struct red_type	*result, *conj; 
  int			ci, rvi; 
  
  if (cv2 == NULL) 
    return(rec_clock_ineq_offset_analysis(
      op, pi, 
      c1, 
      c2, 
      offset_lb, offset_ub, red_offset
    ) ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < ropd->u.ddd.child_count; ci++) { 
    conj = NORM_FALSE; 
    for (rvi = ropd->u.ddd.arc[ci].lower_bound; 
         rvi <= ropd->u.ddd.arc[ci].upper_bound; 
         rvi++
         ) { 
      c2 = clock_index_from_exp(cv2, VAR[rvi].PROC_INDEX);       
      conj = red_bop(OR, conj,
        rec_clock_ineq_offset_analysis( 
          op, pi, c1, c2, 
          offset_lb, offset_ub, red_offset
      ) ); 
    } 
    conj = red_bop(AND, conj, ropd->u.ddd.arc[ci].child); 
    result = red_bop(OR, result, conj); 
  } 
  return(result); 
}
  /* rec_clock_ineq_neg_analysis() */ 
  
  
  
inline struct red_type	*rec_clock_ineq_pos_analysis( 
  int			op, 
  int			pi, 
  struct ps_exp_type	*cv1, 
  int			c1, 
  struct red_type	*lopd, 
  struct ps_exp_type	*cv2, 
  int			c2, 
  struct red_type	*ropd, 
  int			offset_lb, 
  int			offset_ub, 
  struct red_type	*red_offset
) {
  struct red_type	*result, *conj; 
  int			ci, lvi; 
  
  if (cv1 == NULL) 
    return(rec_clock_ineq_neg_analysis(
      op, pi, 
      c1, 
      cv2, c2, ropd, 
      offset_lb, offset_ub, red_offset
    ) ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
    conj = NORM_FALSE; 
    for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
         lvi <= lopd->u.ddd.arc[ci].upper_bound; 
         lvi++
         ) { 
      c1 = clock_index_from_exp(cv1, VAR[lvi].PROC_INDEX);       
      conj = red_bop(OR, conj,
        rec_clock_ineq_neg_analysis( 
          op, pi, c1, cv2, c2, ropd, 
          offset_lb, offset_ub, red_offset
      ) ); 
    } 
    conj = red_bop(AND, conj, lopd->u.ddd.arc[ci].child); 
    result = red_bop(OR, result, conj); 
  } 
  return(result); 
}
  /* rec_clock_ineq_pos_analysis() */ 






struct red_type 	*rec_clock_ineq(psub)
     struct ps_exp_type	*psub;
{
  int			pi, offset_lb, offset_ub, 
			lppi, rppi, c1, c2;
  struct red_type	*result, *lopd, *ropd, *red_offset; 

  CLOCK_POS = CLOCK_NEG = NULL;
  if (psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT)
    switch (psub->u.ineq.term[0].coeff->u.value) {
    case 1:
      CLOCK_POS = psub->u.ineq.term[0].operand;
      break;
    case -1:
      CLOCK_NEG = psub->u.ineq.term[0].operand;
      break;
    default:
      fprintf(RED_OUT, "\nError: Something wrong with no .\n");
      fflush(RED_OUT);
      exit(0);
    }
  else {
    fprintf(RED_OUT, "\nError: Something wrong.\n");
    fflush(RED_OUT);
    exit(0);
  }
  if (   psub->u.ineq.term_count == 2 
      && psub->u.ineq.term[1].coeff->type == TYPE_CONSTANT 
      )
    switch (psub->u.ineq.term[1].coeff->u.value) {
    case 1:
      if (CLOCK_POS) {
        fprintf(RED_OUT, "\nHow come there is still a conflict on CLOCK_POS ?\n");
        fflush(RED_OUT);
        exit(0);
      }
      CLOCK_POS = psub->u.ineq.term[1].operand;
      break;
    case -1:
      if (CLOCK_NEG) {
        fprintf(RED_OUT, "\nHow come there is still a conflict on CLOCK_NEG ?\n");
        fflush(RED_OUT);
        exit(0);
      }
      CLOCK_NEG = psub->u.ineq.term[1].operand;
      break;
    default:
      fprintf(RED_OUT, "\nError: Something wrong with no .\n");
      fflush(RED_OUT);
      exit(0);
    }


  if (!CLOCK_POS) { 
    c1 = 0; 
  } 
  else if (CLOCK_POS->u.atom.exp_base_proc_index->type == TYPE_CONSTANT) { 
    pi = CLOCK_POS->u.atom.exp_base_proc_index->u.value; 
/*
    c1 = CLOCK_POS->u.atom.var_index; 
*/

    #ifdef RED_DEBUG_EXP_MODE
    pcform(psub); 
    pcform(CLOCK_POS); 
    pcform(CLOCK_POS->u.atom.exp_base_proc_index); 
    phex(CLOCK_POS->u.atom.exp_base_proc_index->status); 
    fprintf(RED_OUT, "offset = %1d\n", VAR[c1].OFFSET); 
    fprintf(RED_OUT, "\nin clock_ineq: pi = %1d\n", pi); 
    fprintf(RED_OUT, "\nin clock_ineq: c1 = %1d\n", c1); 
    #endif 
    
/*
    c1 = variable_index[TYPE_CLOCK][pi][VAR[c1].OFFSET]; 
    c1 = VAR[c1].SPEC_INDEX; 
*/
    c1 = clock_index_from_exp(CLOCK_POS, pi);
    CLOCK_POS = NULL; 
  } 
  else if (CLOCK_POS->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER) { 
/*
    c1 = CLOCK_POS->u.atom.var_index; 
    c1 = variable_index[TYPE_CLOCK][W_PI][VAR[c1].OFFSET]; 
    c1 = VAR[c1].SPEC_INDEX; 
*/
    c1 = clock_index_from_exp(CLOCK_POS, W_PI);
    CLOCK_POS = NULL; 
  } 
  else 
    lopd = red_operand_indirection(CLOCK_POS, W_PI); 

  if (!CLOCK_NEG) { 
    c2 = 0; 
  } 
  else if (CLOCK_NEG->u.atom.exp_base_proc_index->type == TYPE_CONSTANT) { 
    pi = CLOCK_NEG->u.atom.exp_base_proc_index->u.value; 
/*
    c2 = CLOCK_NEG->u.atom.var_index; 
    c2 = variable_index[TYPE_CLOCK][pi][VAR[c2].OFFSET]; 
    c2 = VAR[c2].SPEC_INDEX; 
*/
    c2 = clock_index_from_exp(CLOCK_NEG, pi);
    CLOCK_NEG = NULL; 
  } 
  else if (CLOCK_NEG->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER) { 
/*
    c2 = CLOCK_NEG->u.atom.var_index; 
    c2 = variable_index[TYPE_CLOCK][W_PI][VAR[c2].OFFSET]; 
    c2 = VAR[c2].SPEC_INDEX; 
*/
    c2 = clock_index_from_exp(CLOCK_NEG, W_PI);
    CLOCK_NEG = NULL; 
  } 
  else 
    ropd = red_operand_indirection(CLOCK_NEG, W_PI); 

  if (psub->u.ineq.offset->type == TYPE_CONSTANT) { 
    offset_lb = offset_ub = psub->u.ineq.offset->u.value; 
    red_offset = NULL; 
  } 
  else if (!(psub->u.ineq.offset->var_status 
             & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
           ) ) {
    float flb, fub; 
    
    if (get_integer_range(
          psub->u.ineq.offset, W_PI, &offset_lb, &offset_ub, &flb, &fub
        ) != FLAG_SPECIFIC_VALUE) {
/*
      fprintf(RED_OUT, 
        "\nWARNING: unspecific process indices in ineq offset in rec_clock_ineq().\n" 
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
*/
      return(lazy_atom(W_PI, psub)); 
      bk(0); 
    }
    red_offset = NULL; 
  } 
  else 
    red_offset = rec_discrete_value(psub->u.ineq.offset);

  return(rec_clock_ineq_pos_analysis(
    psub->type, W_PI, 
    CLOCK_POS, c1, lopd, 
    CLOCK_NEG, c2, ropd, 
    offset_lb, offset_ub, red_offset
  ) ); 
}
/* rec_clock_ineq() */



struct red_type	*red_clock_ineq(
  struct ps_exp_type	*psub, 
  int			pi 
) {
  W_PI = pi;
  return(rec_clock_ineq(psub));
}
/* red_clock_ineq() */








struct red_type	*red_discrete_dividend_precondition(dx, dy, flag_delayed_evaluation)
     struct red_type	*dx, *dy; 
     int		flag_delayed_evaluation; 
{
  int				vi, v, cix, ciy, ppi, vx, vy, value, flag_simple;
  struct ps_bunit_type		*pbu; 
//  struct parse_indirect_type	*pt; 
  struct red_type		*result, *childx, *childy, *conj, *filter;
  struct ps_exp_type		*var; 

  result = NORM_FALSE; 
  for (cix = 0; cix < childx->u.ddd.child_count; cix++)
    for (ciy = 0; ciy < childy->u.ddd.child_count; ciy++) {
      conj = red_bop(AND, childx->u.ddd.arc[cix].child, childy->u.ddd.arc[ciy].child); 
      if (conj != NORM_FALSE) {
	filter = NORM_FALSE; 
	for (vx = childx->u.ddd.arc[cix].lower_bound; vx <= childx->u.ddd.arc[cix].upper_bound; vx++) 
	  for (vy = childy->u.ddd.arc[ciy].lower_bound; vy <= childy->u.ddd.arc[ciy].upper_bound; vy++) {
	    v = vx * vy; 
	    if (vx > 0 && vy > 0) {
	      filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v, v+vy-1)); 
	    }
	    else { 
	      if (vy < 0) 
		filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v+vy+1, v)); 
	      else 
		filter = red_bop(OR, filter, ddd_atom(VI_VALUE, v-vy+1, v)); 
	    } 
	  }
	conj = red_bop(AND, conj, filter); 
	result = red_bop(OR, result, conj);
      }
    }
  return(result); 
}
/* red_discrete_dividend_precondition() */







struct red_type	*red_value_divide(dx, dy, flag_delayed_evaluation)
     struct red_type	*dx, *dy; 
     int		flag_delayed_evaluation; 
{
  int				vi, v, cix, ciy, ppi, vx, vy, value, flag_simple; 
  struct ps_bunit_type		*pbu; 
//  struct parse_indirect_type	*pt; 
  struct red_type		*result, *childx, *childy, *conj, *filter; 
  struct ps_exp_type		*var; 

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
}
/* red_value_divide() */ 





struct red_type	*red_value_modulo(dx, dy, flag_delayed_evaluation)
     struct red_type	*dx, *dy; 
     int		flag_delayed_evaluation; 
{
  int				vi, v, cix, ciy, ppi, vx, vy, value, flag_simple; 
  struct ps_bunit_type		*pbu; 
//  struct parse_indirect_type	*pt; 
  struct red_type		*result, *childx, *childy, *conj, *filter; 
  struct ps_exp_type		*var; 

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
}
/* red_value_modulo() */ 



/* d is an RED with root type VI_OP and 2nd-tier type VI_VALUE. 
 * After the root tier, the value of op will be changed 
 * to the corresponding arc value of the root.  
 * The procedure is to return RED for VARX_VI op VI_VALUE.  
 */ 
int	VARX_VI, VARX_OP;


struct red_type	*rec_ineq_instance(d, op, lb, ub)
     struct red_type	*d; 
     int		op, lb, ub; 
{
  struct red_type	*result, *conj;
  int			ci; 

  if (d == NORM_FALSE) 
    return(d); 
  else if (d->var_index == VI_VALUE) { 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      conj = rec_ineq_instance(d->u.ddd.arc[ci].child, op, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound); 
      result = red_bop(OR, result, conj); 
    }
    return(result); 
  }
  else if (d->var_index == VI_OP) { 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      for (op = d->u.ddd.arc[ci].lower_bound; op <= d->u.ddd.arc[ci].upper_bound; op++) {
	conj = rec_ineq_instance(d->u.ddd.arc[ci].child, op, lb, ub); 
	result = red_bop(OR, result, conj); 
      }
    }
    return(result); 
  }
  else { 
    switch (op) { 
    case ARITH_EQ: 
      if (lb < VAR[VARX_VI].U.DISC.LB) 
	lb = VAR[VARX_VI].U.DISC.LB; 
      if (ub > VAR[VARX_VI].U.DISC.UB) 
	ub = VAR[VARX_VI].U.DISC.UB; 
      if (lb  <= ub) {
	return(ddd_one_constraint(d, VARX_VI, lb, ub)); 
      }
      else 
	return(NORM_FALSE); 
    case ARITH_NEQ: 
      if (lb != ub || lb < VAR[VARX_VI].U.DISC.LB || lb > VAR[VARX_VI].U.DISC.UB) 
	return(d); 
      else {
	if (lb == VAR[VARX_VI].U.DISC.LB) 
	  result = ddd_atom(VARX_VI, VAR[VARX_VI].U.DISC.LB+1, 
	    VAR[VARX_VI].U.DISC.UB
	  ); 
	else if (lb == VAR[VARX_VI].U.DISC.UB) 
	  result = ddd_atom(VARX_VI, VAR[VARX_VI].U.DISC.LB, 
	    VAR[VARX_VI].U.DISC.UB-1
	  ); 
	else 
	  result = red_bop(OR, 
			   ddd_atom(VARX_VI, VAR[VARX_VI].U.DISC.LB, lb-1), 
			   ddd_atom(VARX_VI, lb+1, VAR[VARX_VI].U.DISC.UB)
			   ); 
	return(red_bop(AND, result, d)); 
      }
    case ARITH_LEQ: 
      if (ub >= VAR[VARX_VI].U.DISC.UB) 
	return(d); 
      else if (ub >= VAR[VARX_VI].U.DISC.LB) {
	return(ddd_one_constraint(d, VARX_VI, VAR[VARX_VI].U.DISC.LB, ub)); 
      }
      else 
	return(NORM_FALSE); 
    case ARITH_GEQ: 
      if (lb <= VAR[VARX_VI].U.DISC.LB)
	return(d); 
      else if (lb <= VAR[VARX_VI].U.DISC.UB) {
	return(ddd_one_constraint(d, VARX_VI, lb, VAR[VARX_VI].U.DISC.UB));
      }
      else 
	return(NORM_FALSE); 
    case ARITH_LESS: 
      if (ub > VAR[VARX_VI].U.DISC.UB) 
	return(d); 
      else if (ub > VAR[VARX_VI].U.DISC.LB) {
	return(ddd_one_constraint(d, VARX_VI, VAR[VARX_VI].U.DISC.LB, ub-1)); 
      }
      else 
	return(NORM_FALSE); 
    case ARITH_GREATER: 
      if (lb < VAR[VARX_VI].U.DISC.LB) 
	return(d); 
      else if (lb < VAR[VARX_VI].U.DISC.UB) {
	return(ddd_one_constraint(d, VARX_VI, lb+1, VAR[VARX_VI].U.DISC.UB)); 
      }
      else 
	return(NORM_FALSE); 
    default: 
      fprintf(RED_OUT, "\nError: Wrong ineq_instance input op\n"); 
      bk("!!"); 
    }
  } 
}
/* rec_ineq_instance() */ 





struct red_type	*red_ineq_instance(d, vi) 
     struct red_type	*d;
     int		vi; 
{
  VARX_VI = vi; 
  return(rec_ineq_instance(d, 0, NEG_INFINITY, POS_INFINITY)); 
}
/* red_ineq_instance() */ 








 
struct red_type	*red_reverse_op(d) 
     struct red_type	*d; 
{
  struct red_type	*result, *conj; 
  int			ci, op; 

  if (d->var_index == VI_OP) { 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      for (op = d->u.ddd.arc[ci].lower_bound; op <= d->u.ddd.arc[ci].upper_bound; op++) {
	switch (op) { 
	case EQ: 
	case NEQ:
	  conj = ddd_atom(VI_OP, op, op); 
	  break; 
	case LEQ: 
	  conj = ddd_atom(VI_OP, GEQ, GEQ);
	  break; 
	case GEQ: 
	  conj = ddd_atom(VI_OP, LEQ, LEQ); 
	  break; 
	case LESS: 
	  conj = ddd_atom(VI_OP, GREATER, GREATER); 
	  break; 
	case GREATER: 
	  conj = ddd_atom(VI_OP, LESS, LESS); 
	  break; 
	}
	conj = red_bop(AND, d->u.ddd.arc[ci].child, conj); 
	result = red_bop(OR, result, conj); 
      }
    }
    return(result); 
  }
  else 
    return(d); 
}
/* red_reverse_op() */ 



int	VARX_INEQ_VI, VARX_INEQ_OP, VARX_INEQ_VALUE; 

struct red_type	*rec_ineq_left(d)
     struct red_type	*d;
{
  int			ci, op; 
  struct red_type	*result; 

  if (d->var_index == VI_OP) { 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      for (op = d->u.ddd.arc[ci].lower_bound; op <= d->u.ddd.arc[ci].upper_bound; op++) {
	VARX_INEQ_OP = op; 
	result = red_bop(OR, result, rec_ineq_left(d->u.ddd.arc[ci].child)); 
      }
    }
    return(result); 
  } 
  else if (d->var_index = VI_VALUE) { 
    switch (VARX_INEQ_OP) { 
    case EQ: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound <= VARX_INEQ_VALUE && VARX_INEQ_VALUE <= d->u.ddd.arc[ci].upper_bound) 
	  return(d->u.ddd.arc[ci].child); 
      } 
      return(NORM_FALSE); 
    case NEQ: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (   d->u.ddd.arc[ci].lower_bound < d->u.ddd.arc[ci].upper_bound
	    || d->u.ddd.arc[ci].lower_bound != VARX_INEQ_VALUE
	    ) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case LEQ:
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound <= VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child);
      } 
      return(result); 
    case GEQ: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].upper_bound >= VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case LESS: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound < VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case GREATER: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].upper_bound > VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result);
    }
  }
  else 
    return(d); 
}
/* rec_ineq_left() */ 



struct red_type	*red_ineq_left(d, vi, value, flag_delayed_evaluation) 
     struct red_type	*d; 
     int		vi, value, flag_delayed_evaluation; 
{
  VARX_INEQ_VI = vi; 
  VARX_INEQ_VALUE = value; 
  return(rec_ineq_left(d)); 
}
/* red_ineq_left() */ 





struct red_type	*rec_ineq_right(d)
     struct red_type	*d; 
{
  int			ci, op; 
  struct red_type	*result; 

  if (d->var_index == VI_OP) { 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      for (op = d->u.ddd.arc[ci].lower_bound; op <= d->u.ddd.arc[ci].upper_bound; op++) {
	VARX_INEQ_OP = op; 
	result = red_bop(OR, result, rec_ineq_right(d->u.ddd.arc[ci].child)); 
      }
    }
    return(result); 
  } 
  else if (d->var_index = VI_VALUE) { 
    switch (VARX_INEQ_OP) {
    case EQ: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound <= VARX_INEQ_VALUE && VARX_INEQ_VALUE <= d->u.ddd.arc[ci].upper_bound) 
	  return(d->u.ddd.arc[ci].child); 
      } 
      return(NORM_FALSE); 
    case NEQ: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (   d->u.ddd.arc[ci].lower_bound < d->u.ddd.arc[ci].upper_bound
	    || d->u.ddd.arc[ci].lower_bound != VARX_INEQ_VALUE
	    ) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case LEQ: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].upper_bound >= VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case GEQ:
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound <= VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      }
      return(result);
    case LESS: 
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	if (d->u.ddd.arc[ci].upper_bound > VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    case GREATER: 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
	if (d->u.ddd.arc[ci].lower_bound < VARX_INEQ_VALUE) 
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
      } 
      return(result); 
    }
  }
  else 
    return(d); 
}
/* rec_ineq_right() */ 



struct red_type	*red_ineq_right(d, vi, value, flag_delayed_evaluation) 
     struct red_type	*d; 
     int		vi, value, flag_delayed_evaluation;
{
  VARX_INEQ_VI = vi; 
  VARX_INEQ_VALUE = value; 
  return(rec_ineq_right(d)); 
}
/* red_ineq_right() */




struct red_type	*red_discrete_ineq_arith(
  int			op, 
  struct red_type	*lhs, 
  struct red_type	*rhs
) {
  struct red_type	*result, *tmp, *conj; 
  int			ci, cj; 
  
  switch (op) { 
  case ARITH_EQ: 
    if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
      return(NORM_FALSE); 
    if (lhs->var_index == FLOAT_VALUE) { 
      if (rhs->var_index == FLOAT_VALUE) { 
        result = red_bop(AND, lhs, rhs); 
        result = red_variable_eliminate(result, FLOAT_VALUE); 
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) {
      	    if (dble_max(lhs->u.fdd.arc[ci].lower_bound, 
      	                 rhs->u.dfdd.arc[cj].lower_bound
      	                 )
      	        <= dble_min(lhs->u.fdd.arc[ci].upper_bound, 
      	                    rhs->u.dfdd.arc[cj].upper_bound
      	        )           ) { 
      	      conj = red_bop(AND, lhs->u.fdd.arc[ci].child, 
      	        rhs->u.dfdd.arc[cj].child
      	      ); 
      	      result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.ddd.child_count; cj++) {
      	    if (flt_max(lhs->u.fdd.arc[ci].lower_bound, 
      	                rhs->u.ddd.arc[cj].lower_bound
      	                ) 
      	        <= flt_min(lhs->u.fdd.arc[ci].upper_bound, 
      	                   rhs->u.ddd.arc[cj].upper_bound
      	        )          ) { 
      	      conj = red_bop(AND, lhs->u.fdd.arc[ci].child, 
      	        rhs->u.ddd.arc[cj].child
      	      ); 
              result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else if (lhs->var_index == DOUBLE_VALUE) { 
      if (rhs->var_index == DOUBLE_VALUE) { 
        result = red_bop(AND, lhs, rhs); 
        result = red_variable_eliminate(result, DOUBLE_VALUE); 
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.fdd.child_count; cj++) {
      	    if (dble_max(lhs->u.dfdd.arc[ci].lower_bound, 
      	                 rhs->u.fdd.arc[cj].lower_bound
      	                 ) 
      	        <= dble_min(lhs->u.dfdd.arc[ci].upper_bound, 
      	                    rhs->u.fdd.arc[cj].upper_bound
      	        )           ) { 
      	      conj = red_bop(AND, lhs->u.dfdd.arc[ci].child, 
      	        rhs->u.fdd.arc[cj].child
      	      ); 
       	      result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.ddd.child_count; cj++) {
      	    if (dble_max(lhs->u.dfdd.arc[ci].lower_bound, 
      	                 rhs->u.ddd.arc[cj].lower_bound
      	                 ) 
      	        <= dble_min(lhs->u.dfdd.arc[ci].upper_bound, 
      	                    rhs->u.ddd.arc[cj].upper_bound
      	        )           ) { 
      	      conj = red_bop(AND, lhs->u.dfdd.arc[ci].child, 
      	        rhs->u.ddd.arc[cj].child
      	      ); 
      	      result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      } 
      else { 
      	bk(0); 
      } 
    } 
    else if (lhs->var_index == VI_VALUE) { 
      if (rhs->var_index == VI_VALUE) { 
        result = red_bop(AND, lhs, rhs); 
        result = red_variable_eliminate(result, VI_VALUE); 
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) {
      	    if (dble_max(lhs->u.ddd.arc[ci].lower_bound, 
      	                 rhs->u.dfdd.arc[cj].lower_bound
      	                 )
      	        <= dble_min(lhs->u.ddd.arc[ci].upper_bound, 
      	                    rhs->u.dfdd.arc[cj].upper_bound
      	        )           ) { 
              conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	        rhs->u.dfdd.arc[cj].child
      	      ); 
              result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
      	result = NORM_FALSE; 
      	for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  for (cj = 0; cj < rhs->u.fdd.child_count; cj++) {
      	    if (flt_max(lhs->u.ddd.arc[ci].lower_bound, 
      	                rhs->u.fdd.arc[cj].lower_bound
      	                ) 
      	        <= flt_min(lhs->u.ddd.arc[ci].upper_bound, 
      	                   rhs->u.fdd.arc[cj].upper_bound
      	        )          ) { 
      	      conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	        rhs->u.fdd.arc[cj].child
      	      ); 
      	      result = red_bop(OR, conj, result); 
      	} } }
      	return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else { 
      bk(0); 
    } 
    break; 
  case ARITH_NEQ: 
    if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
      return(NORM_NO_RESTRICTION); 
    if (lhs->var_index == FLOAT_VALUE) { 
      if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(   (lhs->u.fdd.arc[ci].upper_bound == rhs->u.fdd.arc[cj].upper_bound)
      	          && (lhs->u.fdd.arc[ci].lower_bound == rhs->u.fdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.fdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(   (lhs->u.fdd.arc[ci].upper_bound == rhs->u.dfdd.arc[cj].upper_bound)
      	          && (lhs->u.fdd.arc[ci].lower_bound == rhs->u.dfdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.fdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(   (lhs->u.fdd.arc[ci].upper_bound == rhs->u.ddd.arc[cj].upper_bound)
      	          && (lhs->u.fdd.arc[ci].lower_bound == rhs->u.ddd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.fdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else if (lhs->var_index == DOUBLE_VALUE) { 
      if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(   (lhs->u.dfdd.arc[ci].upper_bound == rhs->u.dfdd.arc[cj].upper_bound)
      	          && (lhs->u.dfdd.arc[ci].lower_bound == rhs->u.dfdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.dfdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(   (lhs->u.dfdd.arc[ci].upper_bound == rhs->u.fdd.arc[cj].upper_bound)
      	          && (lhs->u.dfdd.arc[ci].lower_bound == rhs->u.fdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.dfdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(   (lhs->u.dfdd.arc[ci].upper_bound == rhs->u.ddd.arc[cj].upper_bound)
      	          && (lhs->u.dfdd.arc[ci].lower_bound == rhs->u.ddd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.dfdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    } 
    else if (lhs->var_index == VI_VALUE) { 
      if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(   (lhs->u.ddd.arc[ci].upper_bound == rhs->u.ddd.arc[cj].upper_bound)
      	          && (lhs->u.ddd.arc[ci].lower_bound == rhs->u.ddd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.ddd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(   (lhs->u.ddd.arc[ci].upper_bound == rhs->u.dfdd.arc[cj].upper_bound)
      	          && (lhs->u.ddd.arc[ci].lower_bound == rhs->u.dfdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.ddd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(   (lhs->u.ddd.arc[ci].upper_bound == rhs->u.fdd.arc[cj].upper_bound)
      	          && (lhs->u.ddd.arc[ci].lower_bound == rhs->u.fdd.arc[cj].lower_bound)
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	          lhs->u.ddd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else { 
      bk(0); 
    } 
    break; 

  case ARITH_GREATER: 
    tmp = lhs; 
    lhs = rhs; 
    rhs = tmp; 
  case ARITH_LESS: 
    if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
      return(NORM_FALSE); 
    if (lhs->var_index == FLOAT_VALUE) { 
      if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          >= rhs->u.fdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          >= rhs->u.dfdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          >= rhs->u.ddd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else if (lhs->var_index == DOUBLE_VALUE) { 
      if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          >= rhs->u.dfdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          >= rhs->u.fdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          >= rhs->u.ddd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    } 
    else if (lhs->var_index == VI_VALUE) { 
      if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          >= rhs->u.ddd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          >= rhs->u.dfdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          >= rhs->u.fdd.arc[cj].upper_bound
      	          ) 
      	        ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else { 
      bk(0); 
    } 
    break; 

  case ARITH_GEQ: 
    tmp = lhs; 
    lhs = rhs; 
    rhs = tmp; 
  case ARITH_LEQ: 
    if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
      return(NORM_FALSE); 
    if (lhs->var_index == FLOAT_VALUE) { 
      if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          > rhs->u.fdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          > rhs->u.dfdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.fdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.fdd.arc[ci].lower_bound 
      	          > rhs->u.ddd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.fdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else if (lhs->var_index == DOUBLE_VALUE) { 
      if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          > rhs->u.dfdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          > rhs->u.fdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.dfdd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.dfdd.arc[ci].lower_bound 
      	          > rhs->u.ddd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.dfdd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    } 
    else if (lhs->var_index == VI_VALUE) { 
      if (rhs->var_index == VI_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          > rhs->u.ddd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.ddd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == DOUBLE_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          > rhs->u.dfdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.dfdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      }
      else if (rhs->var_index == FLOAT_VALUE) { 
        result = NORM_FALSE; 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
          for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
      	    if (!(lhs->u.ddd.arc[ci].lower_bound 
      	          > rhs->u.fdd.arc[cj].upper_bound
      	        ) ) 
      	      result = red_bop(OR, result, red_bop(AND, 
      	        lhs->u.ddd.arc[ci].child, rhs->u.fdd.arc[cj].child
      	      ) ); 
          } 
        }  
        return(result); 
      } 
      else { 
      	bk(0); 
      } 
    }
    else { 
      bk(0); 
    } 
    break; 

  } 
}
  /* red_discrete_ineq_arith() */ 





int	count_disc_ineq = 0; 

struct red_type	*red_discrete_ineq_discrete(
  struct ps_exp_type	*psub, 
  struct red_type	*lhs, 
  struct red_type	*rhs
) { 
  int			ci, cj, vi;
  struct red_type	*result, *tmp, *conj;

  if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (lhs == NORM_NO_RESTRICTION) 
    return (NORM_NO_RESTRICTION); 
  else if (rhs == NORM_NO_RESTRICTION) {
    result = NORM_FALSE; 
    for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      result = red_bop(OR, result, lhs->u.ddd.arc[ci].child);  
    } 
    return(result); 
  } 
  switch (psub->type) { 
  case ARITH_EQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                dble_ceil(rhs->u.dfdd.arc[cj].lower_bound), 
                dble_floor(rhs->u.dfdd.arc[cj].upper_bound)
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                flt_ceil(rhs->u.fdd.arc[cj].lower_bound), 
                flt_floor(rhs->u.fdd.arc[cj].upper_bound)
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound, 
                rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
    break; 
  case ARITH_NEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DISC.LB < rhs->u.dfdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                  dble_floor(dfeps_minus(rhs->u.dfdd.arc[cj].lower_bound)) 
              ) ); 
            }
            if (VAR[vi].U.DISC.UB > rhs->u.dfdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi,  
                  dble_ceil(dfeps_plus(rhs->u.dfdd.arc[cj].upper_bound)), 
                  VAR[vi].U.DISC.UB 
              ) ); 
            }
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DISC.LB < rhs->u.fdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                  flt_floor(feps_minus(rhs->u.fdd.arc[cj].lower_bound)) 
              ) ); 
            }
            if (VAR[vi].U.DISC.UB > rhs->u.fdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi,  
                  flt_ceil(feps_plus(rhs->u.fdd.arc[cj].upper_bound)), 
                  VAR[vi].U.DISC.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else  { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DISC.LB < rhs->u.ddd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                  rhs->u.ddd.arc[cj].lower_bound-1 
              ) ); 
            }
            if (VAR[vi].U.DISC.UB > rhs->u.ddd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                ddd_one_constraint(conj, vi,  
                  rhs->u.ddd.arc[cj].upper_bound+1, VAR[vi].U.DISC.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
  case ARITH_LESS: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].upper_bound == VAR[vi].U.DISC.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                dble_floor(dfeps_minus(rhs->u.dfdd.arc[cj].upper_bound))
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].upper_bound == VAR[vi].U.DISC.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                flt_floor(feps_minus(rhs->u.fdd.arc[cj].upper_bound))
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].upper_bound == VAR[vi].U.DISC.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                rhs->u.ddd.arc[cj].upper_bound-1
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_LEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                dble_floor(rhs->u.dfdd.arc[cj].upper_bound)
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                flt_floor(rhs->u.fdd.arc[cj].upper_bound) 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, VAR[vi].U.DISC.LB, 
                rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_GREATER: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].lower_bound == VAR[vi].U.DISC.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                dble_ceil(dfeps_plus(rhs->u.dfdd.arc[cj].lower_bound)), 
                VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].lower_bound == VAR[vi].U.DISC.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                flt_ceil(feps_plus(rhs->u.fdd.arc[cj].lower_bound)), 
                VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].lower_bound == VAR[vi].U.DISC.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound+1, VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 

  case ARITH_GEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                dble_ceil(rhs->u.dfdd.arc[cj].lower_bound), VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                flt_ceil(rhs->u.fdd.arc[cj].lower_bound), VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
/*
          fprintf(RED_OUT, "\ncount_disc_ineq=%1d\n", 
            ++count_disc_ineq
          ); 
          fflush(RED_OUT); 
*/
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              ddd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound, VAR[vi].U.DISC.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR, unexpected inequality type %1d in rec_discrete_ineq().\n", 
      psub->type
    ); 
    bk(0); 
  } 
}
/* red_discrete_ineq_discrete() */ 





struct red_type	*red_discrete_ineq_float(
  struct ps_exp_type	*psub, 
  struct red_type	*lhs, 
  struct red_type	*rhs
) { 
  int			ci, cj, vi;
  struct red_type	*result, *tmp, *conj;

  if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (lhs == NORM_NO_RESTRICTION) 
    return (NORM_NO_RESTRICTION); 
  else if (rhs == NORM_NO_RESTRICTION) {
    result = NORM_FALSE; 
    for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      result = red_bop(OR, result, lhs->u.ddd.arc[ci].child);  
    } 
    return(result); 
  } 
  switch (psub->type) { 
  case ARITH_EQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                rhs->u.dfdd.arc[cj].lower_bound, 
                rhs->u.dfdd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                rhs->u.fdd.arc[cj].lower_bound, 
                rhs->u.fdd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                (float) rhs->u.ddd.arc[cj].lower_bound, 
                (float) rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
    break; 
  case ARITH_NEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.FLT.LB < rhs->u.dfdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                  feps_minus(rhs->u.dfdd.arc[cj].lower_bound)
              ) ); 
            }
            if (VAR[vi].U.FLT.UB > rhs->u.dfdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi,  
                  feps_minus(rhs->u.dfdd.arc[cj].upper_bound), 
                  VAR[vi].U.FLT.UB 
              ) ); 
            }
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.FLT.LB < rhs->u.fdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                  feps_minus(rhs->u.fdd.arc[cj].lower_bound)  
              ) ); 
            }
            if (VAR[vi].U.FLT.UB > rhs->u.fdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi,  
                  feps_plus(rhs->u.fdd.arc[cj].upper_bound), 
                  VAR[vi].U.FLT.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else  { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.FLT.LB < rhs->u.ddd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                  feps_minus(rhs->u.ddd.arc[cj].lower_bound) 
              ) ); 
            }
            if (VAR[vi].U.FLT.UB > rhs->u.ddd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi,  
                  feps_plus(rhs->u.ddd.arc[cj].upper_bound), VAR[vi].U.FLT.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
  case ARITH_LESS: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].upper_bound == VAR[vi].U.FLT.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                dfeps_minus(rhs->u.dfdd.arc[cj].upper_bound) 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child 
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].upper_bound == VAR[vi].U.FLT.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                feps_minus(rhs->u.fdd.arc[cj].upper_bound)
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].upper_bound == VAR[vi].U.FLT.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                feps_minus(rhs->u.ddd.arc[cj].upper_bound)
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_LEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child 
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                rhs->u.dfdd.arc[cj].upper_bound
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                rhs->u.fdd.arc[cj].upper_bound 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, VAR[vi].U.FLT.LB, 
                rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_GREATER: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].lower_bound == VAR[vi].U.FLT.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                feps_plus(rhs->u.dfdd.arc[cj].lower_bound), // we use FLT_MIN 
                // since the result has to be in float.
                VAR[vi].U.FLT.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].lower_bound == VAR[vi].U.FLT.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                feps_plus(rhs->u.fdd.arc[cj].lower_bound), 
                VAR[vi].U.FLT.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].lower_bound == VAR[vi].U.FLT.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                feps_plus(rhs->u.ddd.arc[cj].lower_bound), VAR[vi].U.FLT.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 

  case ARITH_GEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                rhs->u.dfdd.arc[cj].lower_bound, VAR[vi].U.FLT.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                rhs->u.fdd.arc[cj].lower_bound, VAR[vi].U.FLT.UB
            ) ); 
          } 
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              fdd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound, VAR[vi].U.FLT.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR, unexpected inequality type %1d in rec_discrete_ineq().\n", 
      psub->type
    ); 
    bk(0); 
  } 
}
/* red_discrete_ineq_float() */ 





struct red_type	*red_discrete_ineq_double(
  struct ps_exp_type	*psub, 
  struct red_type	*lhs, 
  struct red_type	*rhs
) { 
  int			ci, cj, vi;
  struct red_type	*result, *tmp, *conj;

  if (lhs == NORM_FALSE || rhs == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (lhs == NORM_NO_RESTRICTION) 
    return (NORM_NO_RESTRICTION); 
  else if (rhs == NORM_NO_RESTRICTION) {
    result = NORM_FALSE; 
    for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      result = red_bop(OR, result, lhs->u.ddd.arc[ci].child);  
    } 
    return(result); 
  } 
  switch (psub->type) { 
  case ARITH_EQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.dfdd.arc[cj].lower_bound, 
                rhs->u.dfdd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.fdd.arc[cj].lower_bound, 
                rhs->u.fdd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound, 
                rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
    break; 
  case ARITH_NEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DBLE.LB < rhs->u.dfdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                  dfeps_minus(rhs->u.dfdd.arc[cj].lower_bound) 
              ) ); 
            }
            if (VAR[vi].U.DBLE.UB > rhs->u.dfdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                dfdd_one_constraint(conj, vi,  
                  dfeps_plus(rhs->u.dfdd.arc[cj].upper_bound), 
                  VAR[vi].U.DBLE.UB 
              ) ); 
            }
          }
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DBLE.LB < rhs->u.fdd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                  dfeps_minus(rhs->u.fdd.arc[cj].lower_bound)   
              ) ); 
            }
            if (VAR[vi].U.DBLE.UB > rhs->u.fdd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                dfdd_one_constraint(conj, vi,  
                  dfeps_plus(rhs->u.fdd.arc[cj].upper_bound), 
                  VAR[vi].U.DBLE.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    else  { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            if (VAR[vi].U.DBLE.LB < rhs->u.ddd.arc[cj].lower_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                  dfeps_minus(rhs->u.ddd.arc[cj].lower_bound) 
              ) ); 
            }
            if (VAR[vi].U.DBLE.UB > rhs->u.ddd.arc[cj].upper_bound) {  
              result = red_bop(OR, result, 
                fdd_one_constraint(conj, vi,  
                  dfeps_plus(rhs->u.ddd.arc[cj].upper_bound), 
                  VAR[vi].U.DBLE.UB 
              ) ); 
            }
          } 
        }
        if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
          return(lazy_atom(W_PI, psub)); 
    } }
    return(result); 
  
  case ARITH_LESS: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].upper_bound == VAR[vi].U.DBLE.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                dfeps_minus(rhs->u.dfdd.arc[cj].upper_bound) 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child 
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].upper_bound == VAR[vi].U.DBLE.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                dfeps_minus(rhs->u.fdd.arc[cj].upper_bound) 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].upper_bound == VAR[vi].U.DBLE.LB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                dfeps_minus(rhs->u.ddd.arc[cj].upper_bound)
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_LEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child 
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                rhs->u.dfdd.arc[cj].upper_bound
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                rhs->u.fdd.arc[cj].upper_bound 
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, VAR[vi].U.DBLE.LB, 
                rhs->u.ddd.arc[cj].upper_bound
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
  
  case ARITH_GREATER: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.dfdd.arc[cj].lower_bound == VAR[vi].U.DBLE.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                dfeps_plus(rhs->u.dfdd.arc[cj].lower_bound), // we use FLT_MIN 
                // since the result has to be in float.
                VAR[vi].U.DBLE.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.fdd.arc[cj].lower_bound == VAR[vi].U.DBLE.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                dfeps_plus(rhs->u.fdd.arc[cj].lower_bound), 
                VAR[vi].U.DBLE.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
      	    if (rhs->u.ddd.arc[cj].lower_bound == VAR[vi].U.DBLE.UB) 
      	      continue; 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                dfeps_plus(rhs->u.ddd.arc[cj].lower_bound), 
                VAR[vi].U.DBLE.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 

  case ARITH_GEQ: 
    result = NORM_FALSE; 
    if (rhs->var_index == DOUBLE_VALUE) { 
      for (cj = 0; cj < rhs->u.dfdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.dfdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.dfdd.arc[cj].lower_bound, VAR[vi].U.DBLE.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else if (rhs->var_index == FLOAT_VALUE) { 
      for (cj = 0; cj < rhs->u.fdd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.fdd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.fdd.arc[cj].lower_bound, VAR[vi].U.DBLE.UB
            ) ); 
          } 
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    else { 
      for (cj = 0; cj < rhs->u.ddd.child_count; cj++) { 
        for (ci = 0; ci < lhs->u.ddd.child_count; ci++) { 
      	  conj = red_bop(AND, lhs->u.ddd.arc[ci].child, 
      	    rhs->u.ddd.arc[cj].child
      	  ); 
      	  if (conj == NORM_FALSE) 
      	    continue; 
          for (vi = lhs->u.ddd.arc[ci].lower_bound; 
               vi <= lhs->u.ddd.arc[ci].upper_bound; 
               vi++
               ) { 
            result = red_bop(OR, result, 
              dfdd_one_constraint(conj, vi, 
                rhs->u.ddd.arc[cj].lower_bound, VAR[vi].U.DBLE.UB
            ) ); 
          }
          if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
            return(lazy_atom(W_PI, psub)); 
    } } }
    return(result); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR, unexpected inequality type %1d in rec_discrete_ineq().\n", 
      psub->type
    ); 
    bk(0); 
  } 
}
/* red_discrete_ineq_double() */ 




int	count_red_disc_ineq = 0; 

struct red_type	*red_discrete_ineq(psub, pi)
     struct ps_exp_type	*psub;
     int		pi; 
{
  int			ci, cj, vi;
  struct ps_exp_type	*lhs_exp, *rhs_exp; 
  struct red_type	*result, *lhs, *rhs, *tmp, *conj;

  /* find the first variable and use its range to start computing the value of the expression. */
/*
  fprintf(RED_OUT, "\ndisc ineq %1d\n", ++count_disc_ineq); 
  if (count_disc_ineq == -1) {
    pcform(psub); 
  }
  fflush(RED_OUT); 
*/

  W_PI = pi; 
/*
  fprintf(RED_OUT, "\ncount disc ineq %1d, lhs: ", ++count_disc_ineq); 
  pcform(psub); 
*/
  if (   (psub->u.arith.lhs_exp->var_status 
          & (FLAG_DISCRETE | FLAG_POINTER | FLAG_FLOAT | FLAG_DOUBLE)
          )
      || psub->u.arith.lhs_exp->type == TYPE_POINTER 
      ) {
    lhs_exp = psub->u.arith.lhs_exp; 
    rhs_exp = psub->u.arith.rhs_exp; 
  }
  else {
    lhs_exp = psub->u.arith.rhs_exp; 
    rhs_exp = psub->u.arith.lhs_exp; 
  } 
  if (   lhs_exp->type == TYPE_POINTER 
      && (lhs_exp->u.atom.var->status & FLAG_QUANTIFIED_SYNC) 
      && (lhs_exp->u.atom.var->status & FLAG_LOCAL_VARIABLE) 
      ) { 
    result = NORM_FALSE; 
    vi = lhs_exp->u.atom.var_index; 
    vi = variable_index[TYPE_POINTER][pi][VAR[vi].OFFSET]; 
    for (ci = 1; ci <= PROCESS_COUNT; ci++) { 
      result = red_bop(OR, result, 
        ddd_lone_subtree(ddd_atom(vi, ci, ci), 
          VI_VALUE, 
          ci, ci 
      ) ); 
    } 
    result = red_discrete_ineq_arith(psub->type, 
      result, rec_discrete_value(rhs_exp)
    ); 
    return(result); 
  }
         
  lhs = red_operand_indirection(lhs_exp, W_PI); 
  if (!lhs) { 
    return(lazy_atom(W_PI, psub)); 
  } 
/*
  red_print_graph(lhs); 
*/
  rhs = rec_discrete_value(rhs_exp); 
/*
  fprintf(RED_OUT, "\nrhs in red_discrete_ineq().\n"); 
  red_print_graph(rhs); 
*/
  if (!rhs) { 
    result = lazy_atom(W_PI, psub); 
  } 
  else if ((lhs_exp->var_status | rhs_exp->var_status) & FLAG_DOUBLE) { 
    result = red_discrete_ineq_double(psub, lhs, rhs); 
  }
  else if ((lhs_exp->var_status | rhs_exp->var_status) & FLAG_FLOAT) { 
    result = red_discrete_ineq_float(psub, lhs, rhs); 
  } 
  else { 
    result = red_discrete_ineq_discrete(psub, lhs, rhs); 
  } 
/*  
  fprintf(RED_OUT, "%1d, red ineq disc: ", ++count_red_disc_ineq); 
  print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
  fprintf(RED_OUT, " -->\n"); 
  red_print_graph(result); 
*/
  return(result); 
}
  /* red_discrete_ineq() */  





struct red_type	*red_ineq_vi_value(op, lhs, rhs) 
	int		op; 
	struct red_type	*lhs, *rhs; 
{ 
  struct red_type	*conj, *result, *child; 
  int			ci, v; 
  
  if (lhs->var_index != VI_VALUE || rhs->var_index != VI_VALUE) { 
    if (lhs->var_index == VI_VALUE) {
      lhs = red_variable_eliminate(lhs, VI_VALUE); 
    }
    if (rhs->var_index == VI_VALUE) {
      rhs = red_variable_eliminate(rhs, VI_VALUE); 
    }
    return(red_bop(AND, lhs, rhs)); 
  } 
  
  result = NORM_FALSE; 
  for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
    child = rhs->u.ddd.arc[ci].child; 
    for (v = rhs->u.ddd.arc[ci].lower_bound; v <= rhs->u.ddd.arc[ci].upper_bound; v++) {
      switch (op) { 
      case EQ: 
        conj = ddd_one_constraint(lhs, VI_VALUE, v, v); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      case NEQ: 
        conj = red_bop(OR, 
	  ddd_one_constraint(lhs, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, v-1), 
	  ddd_one_constraint(lhs, VI_VALUE, v+1, VAR[VI_VALUE].U.DISC.UB) 
	); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      case LEQ: 
        conj = ddd_one_constraint(lhs, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, v); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      case LESS: 
        conj = ddd_one_constraint(lhs, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, v-1); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      case GEQ: 
        conj = ddd_one_constraint(lhs, VI_VALUE, v, VAR[VI_VALUE].U.DISC.UB); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      case GREATER: 	
        conj = ddd_one_constraint(lhs, VI_VALUE, v+1, VAR[VI_VALUE].U.DISC.UB); 
        conj = red_variable_eliminate(conj, VI_VALUE); 
        conj = red_bop(AND, child, conj); 
        result = red_bop(OR, result, conj); 
        break; 
      }
    }	
  } 
  return(result); 
} 
  /* red_ineq_vi_value() */ 
  


/* The following procedure tries to derive the 
 * range restriction on a variable x 
 * from a constraint like c x ~ d
 * with given ranges of c and d. 
 */
void	get_ineq_range(
  int	*type_ptr, 
  int	vi, 
  int	*coeff_ptr, 
  int	*offset_lb_ptr, 
  int	*offset_ub_ptr, 
  int	*lb_ptr, 
  int	*ub_ptr
) {
  if (*coeff_ptr == 0) {
    if (*offset_lb_ptr > 0 || *offset_ub_ptr < 0) {
      *lb_ptr = VAR[vi].U.DISC.UB; 
      *ub_ptr = VAR[vi].U.DISC.LB; 
    } 
    else { 
      *lb_ptr = VAR[vi].U.DISC.LB; 
      *ub_ptr = VAR[vi].U.DISC.UB; 
    } 
    return; 
  } 
  
  *lb_ptr = VAR[vi].U.DISC.LB; 
  *ub_ptr = VAR[vi].U.DISC.UB; 
  if (*coeff_ptr < 0) { 
    *coeff_ptr = -1*(*coeff_ptr); 
    *offset_lb_ptr = -1 *(*offset_ub_ptr); 
    *offset_ub_ptr = -1 *(*offset_lb_ptr); 
    switch (*type_ptr) {
    case NEQ:
    case EQ: 
      break; 
    case GREATER: 
      *type_ptr = LESS; 
      break; 
    case GEQ: 
      *type_ptr = LEQ; 
      break; 
    case LESS: 
      *type_ptr = GREATER; 
      break; 
    case LEQ: 
      *type_ptr = GEQ; 
      break; 
  } }
  if ((*offset_lb_ptr) % (*coeff_ptr)) { 
    *lb_ptr = int_max(*lb_ptr, (*offset_lb_ptr / *coeff_ptr)+1); 
    if (*type_ptr == GREATER) 
      *type_ptr = GEQ; 
  } 
  else 
    *lb_ptr = int_max(*lb_ptr, *offset_lb_ptr / *coeff_ptr); 	

  if (*offset_ub_ptr % *coeff_ptr) { 
    *ub_ptr = int_min(*ub_ptr, (*offset_ub_ptr / *coeff_ptr)-1); 
    if (*type_ptr == LESS) 
      *type_ptr = LEQ; 
  } 
  else 
    *ub_ptr = int_min(*ub_ptr, *offset_ub_ptr / *coeff_ptr); 	
}
  /* get_ineq_range() */ 





struct red_type	*red_discrete_ineq_vi_range(
  int			type, 
  struct ps_exp_type	*var, 
  struct red_type	*red_addr, 
  int			coeff, 
  struct red_type	*offset_child, 
  int			offset_lb, 
  int			offset_ub
) { 
  int 			cix, vi, vx, lb, ub; 
  struct red_type	*childx, *result; 
  
  result = NORM_FALSE; 
  #ifdef RED_DEBUG_EXP_MODE
//    for (; count_discrete_value == -1 /*1323*/; ) ;  
  pcform(var); 
  #endif 
  
  get_ineq_range(
    &type, var->u.atom.var_index, 
    &coeff, &offset_lb, &offset_ub, 
    &lb, &ub
  ); 
  for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
    for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
         vi <= red_addr->u.ddd.arc[cix].upper_bound; 
         vi++
         ) { 
      #ifdef RED_DEBUG_EXP_MODE
      fprintf(RED_OUT, 
	"count_discrete_value=%1d, in rec_discrete_value for vi=%1d\n", 
	count_discrete_value, 
	vi
      ); 
      fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
      fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
      #endif 
	
      switch (type) { 
      case EQ: 
        childx = ddd_one_constraint(offset_child, vi, lb, ub); 
        break; 
      case NEQ: 
        childx = NORM_FALSE; 
        if (lb > VAR[vi].U.DISC.LB) { 
          childx = red_bop(OR, childx, 
            ddd_one_constraint(offset_child, vi, VAR[vi].U.DISC.LB, lb-1)
          ); 
        }
        if (ub < VAR[vi].U.DISC.UB) {
          childx = red_bop(OR, childx, 
            ddd_one_constraint(offset_child, vi, ub+1, VAR[vi].U.DISC.UB)
          ); 
        } 
        break; 
      case GREATER: 
        childx = ddd_one_constraint(offset_child, vi, lb+1, VAR[vi].U.DISC.UB); 
        break; 
      case GEQ: 
        childx = ddd_one_constraint(offset_child, vi, lb, VAR[vi].U.DISC.UB); 
        break; 
      case LEQ: 
        childx = ddd_one_constraint(offset_child, vi, VAR[vi].U.DISC.LB, ub); 
        break; 
      case LESS: 
        childx = ddd_one_constraint(offset_child, vi, VAR[vi].U.DISC.LB, ub-1); 
        break; 
      }
      result = red_bop(OR, result, childx); 
    } 
  } 
  return(result); 	
} 
  /* red_discrete_ineq_vi_range() */ 
  



struct red_type	*rec_discrete_ineq_linear(psub) 
	struct ps_exp_type	*psub;
{
  struct red_type	*result, *conj, *red_offset, *red_addr;
  int			offset_num, offset_den, ti;

  switch (psub->u.ineq.term_count) {
  case 0:
    red_offset = rec_discrete_value(psub->u.ineq.offset); 
    switch (psub->type) {
    case EQ: 
      result = ddd_one_constraint(red_offset, VI_VALUE, 0, 0); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    case NEQ:
      conj = ddd_one_constraint(red_offset, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, -1); 
      result = ddd_one_constraint(red_offset, VI_VALUE, 1, VAR[VI_VALUE].U.DISC.UB); 
      result = red_bop(OR, conj, result); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    case LEQ:
      result = ddd_one_constraint(red_offset, VI_VALUE, 0, VAR[VI_VALUE].U.DISC.UB); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    case LESS:
      result = ddd_one_constraint(red_offset, VI_VALUE, 1, VAR[VI_VALUE].U.DISC.UB); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    case GEQ:
      result = ddd_one_constraint(red_offset, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, 0); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    case GREATER:
      result = ddd_one_constraint(red_offset, VI_VALUE, VAR[VI_VALUE].U.DISC.LB, -1); 
      result = red_variable_eliminate(result, VI_VALUE); 
      return(result); 
    }
  case 1: 
    if (psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT) { 
      int		ci; 
      struct red_type	*child; 

      red_offset = rec_discrete_value(psub->u.ineq.offset); 
      red_addr = red_operand_indirection(
        psub->u.ineq.term[0].operand, W_PI
      ); 
      result = NORM_FALSE; 
      for (ci = 0; ci < red_offset->u.ddd.child_count; ci++) { 
      	child = red_offset->u.ddd.arc[ci].child; 
      	child = red_discrete_ineq_vi_range(
      	  psub->type, psub->u.ineq.term[0].operand, 
      	  red_addr, 
      	  psub->u.ineq.term[0].coeff->u.value, 
      	  child, 
      	  red_offset->u.ddd.arc[ci].lower_bound, 
      	  red_offset->u.ddd.arc[ci].upper_bound
      	); 
      	result = red_bop(OR, result, child); 
      } 
      return(result); 
      break; 
    } 

  default: 
    switch (FLAG_POLICY_EVALUATION) { 
    case FLAG_LAZY_EVALUATION: 
      return(lazy_atom(W_PI, psub)); 

    case FLAG_DELAYED_EVALUATION: 
      result = red_multiply_value(
        rec_discrete_value(psub->u.ineq.term[0].coeff),
	rec_discrete_value(psub->u.ineq.term[0].operand)
      );
      for (ti = 1; ti < psub->u.ineq.term_count; ti++) {
        result = red_add_value(1, result, 1, 
          red_multiply_value(
            rec_discrete_value(psub->u.ineq.term[ti].coeff),
	    rec_discrete_value(psub->u.ineq.term[ti].operand) 
          )
	);
      }
      return(red_ineq_vi_value(
        psub->type, result, red_offset, FLAG_POLICY_EVALUATION
      ) ); 
  } } 
}
  /* rec_discrete_ineq_linear() */



struct red_type	*red_discrete_ineq_linear( 
  struct ps_exp_type	*psub, 
  int			pi, 
  int			flag_delayed_evaluation  
) {
  W_PI = pi;
  FLAG_POLICY_EVALUATION = flag_delayed_evaluation; 
  return(rec_discrete_ineq_linear(psub));
}
  /* red_discrete_ineq_linear() */


int	PI_ADJUST_SPECIFIC; 
  

struct ps_exp_type	*rec_adjust_specific_pi( 
     struct ps_exp_type	*psub 
) {
  int				vi, flag, xsi;
//  struct parse_indirect_type	*pt;
  struct ps_exp_type		*newsub, *child; 

  switch (psub->type) {
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_CONSTANT:
  case TYPE_NULL:
  case TYPE_QFD:
  case TYPE_QSYNC_HOLDER:
  case TYPE_INTERVAL:
  case TYPE_MODE_INDEX: 
    return(psub); 
    break;

  case TYPE_LOCAL_IDENTIFIER:
    return(exp_atom(TYPE_CONSTANT, PI_ADJUST_SPECIFIC, NULL)); 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_adjust_specific_pi(psub->u.exp);
    return(ps_exp_share(newsub)); 

  case TYPE_DISCRETE: 
  case TYPE_POINTER:
  case TYPE_DENSE: 
  case TYPE_CLOCK: 
    switch (psub->u.atom.exp_base_proc_index->type) { 
    case TYPE_CONSTANT: 
      return(psub); 
      break; 
    default: 
      newsub = ps_exp_alloc(psub->type); 
      *newsub = *psub; 
      newsub->u.atom.exp_base_proc_index 
      = rec_adjust_specific_pi(psub->u.atom.exp_base_proc_index); 
/*
      if (   newsub->u.atom.exp_base_proc_index->type == TYPE_CONSTANT
          && psub->u.atom.indirect_count
          ) { 
        int	vi; 
        
      	vi = psub->u.atom.indirect_vi
      	  [newsub->u.atom.exp_base_proc_index->u.value]; 
      	for (xsi = 0; xsi <= PROCESS_COUNT; xsi++) 
      	  psub->u.atom.indirect_vi[xsi] = vi; 
      } 
*/
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
  case ARITH_EQ: 
  case ARITH_NEQ: 
  case ARITH_LEQ: 
  case ARITH_LESS: 
  case ARITH_GEQ: 
  case ARITH_GREATER: 

    return(exp_arith(psub->type, 
      rec_adjust_specific_pi(psub->u.arith.lhs_exp),  
      rec_adjust_specific_pi(psub->u.arith.rhs_exp)
    ) ); 
    break; 

  case ARITH_CONDITIONAL: {
    struct ps_exp_type	*cond; 
    
    cond = rec_adjust_specific_pi(psub->u.arith_cond.cond); 
    if (cond == PS_EXP_TRUE) { 
      return(rec_adjust_specific_pi(psub->u.arith_cond.if_exp));
    }
    else if (cond == PS_EXP_FALSE) { 
      return(rec_adjust_specific_pi(psub->u.arith_cond.else_exp));
    } 
    newsub = ps_exp_copy(psub); 
    newsub->u.arith_cond.cond = cond; 
    newsub->u.arith_cond.if_exp 
    = rec_adjust_specific_pi(psub->u.arith_cond.if_exp); 
    newsub->u.arith_cond.else_exp 
    = rec_adjust_specific_pi(psub->u.arith_cond.else_exp); 
    return(ps_exp_share(newsub)); 
  }
  case TYPE_INLINE_BOOLEAN_DECLARE:     
  case TYPE_INLINE_DISCRETE_DECLARE: 
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "\nError: This should not be here!\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case TYPE_INLINE_CALL: 
    return(rec_adjust_specific_pi(psub->u.inline_call.instantiated_exp)); 

  case AND : {
    struct ps_bunit_type	*pbu, dummy_bu; 
    
    newsub = ps_exp_copy(psub); 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      child = rec_adjust_specific_pi(pbu->subexp); 
      if (child == PS_EXP_FALSE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
      	free(newsub); 
      	return(PS_EXP_FALSE); 
      } 
      insert_sorted_blist_dummy_head(
        newsub->type, 
        child, 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_TRUE); 
    case 1: 
      child = newsub->u.bexp.blist->subexp; 
      free(newsub->u.bexp.blist); 
      free(newsub); 
      return(child); 
    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub));
    }
  }
  case OR : {
    struct ps_bunit_type	*pbu, dummy_bu; 
    
    newsub = ps_exp_copy(psub); 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      child = rec_adjust_specific_pi(pbu->subexp); 
      if (child == PS_EXP_TRUE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
      	free(newsub); 
      	return(PS_EXP_TRUE); 
      } 
      insert_sorted_blist_dummy_head(
        newsub->type, 
        child, 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_FALSE); 
    case 1: 
      child = newsub->u.bexp.blist->subexp; 
      free(newsub->u.bexp.blist); 
      free(newsub); 
      return(child); 
    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub));
    }
  } 
  case NOT :
    return(add_neg(rec_adjust_specific_pi(psub->u.bexp.blist->subexp))); 

  case IMPLY: {
    struct ps_bunit_type	dummy_bu; 
    
    newsub = ps_exp_copy(psub); 
    newsub->type = OR; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    child = add_neg(rec_adjust_specific_pi(psub->u.bexp.blist->subexp)); 
    if (child == PS_EXP_TRUE) {
      free(newsub); 
      return(PS_EXP_TRUE); 
    } 
    insert_sorted_blist_dummy_head(
      newsub->type, 
      child, 
      &dummy_bu, &(newsub->u.bexp.len) 
    ); 

    child = rec_adjust_specific_pi(psub->u.bexp.blist->bnext->subexp); 
    if (child == PS_EXP_TRUE) {
      free(newsub); 
      return(PS_EXP_TRUE); 
    } 
    insert_sorted_blist_dummy_head(
      newsub->type, 
      child, 
      &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_FALSE); 
    case 1: 
      child = newsub->u.bexp.blist->subexp; 
      free(newsub->u.bexp.blist); 
      free(newsub); 
      return(child); 
    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub));
    }
  } 
  case FORALL: {
    struct ps_bunit_type	dummy_bu; 
    int				lb, ub, flag; 
    
    newsub = ps_exp_copy(psub); 
    newsub->type = AND; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    lb = get_value(psub->u.qexp.lb_exp, PI_ADJUST_SPECIFIC, &flag); 
    ub = get_value(psub->u.qexp.ub_exp, PI_ADJUST_SPECIFIC, &flag); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      child = rec_adjust_specific_pi(psub->u.qexp.child);   
      if (child == PS_EXP_FALSE) { 
        pop_quantified_value_stack(psub); 
      	ps_exp_free_list(dummy_bu.bnext); 
      	free(newsub); 
      	return(PS_EXP_FALSE); 
      } 
      insert_sorted_blist_dummy_head(
        newsub->type, 
        child, 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    pop_quantified_value_stack(psub); 
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_TRUE); 
    case 1: 
      child = newsub->u.bexp.blist->subexp; 
      free(newsub->u.bexp.blist); 
      free(newsub); 
      return(child); 
    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub));
    }
  }
  case EXISTS : {
    struct ps_bunit_type	dummy_bu; 
    int				lb, ub, flag; 
    
    newsub = ps_exp_copy(psub); 
    newsub->type = OR; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    lb = get_value(psub->u.qexp.lb_exp, PI_ADJUST_SPECIFIC, &flag); 
    ub = get_value(psub->u.qexp.ub_exp, PI_ADJUST_SPECIFIC, &flag); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      child = rec_adjust_specific_pi(psub->u.qexp.child);   
      if (child == PS_EXP_TRUE) { 
        pop_quantified_value_stack(psub); 
      	ps_exp_free_list(dummy_bu.bnext); 
      	free(newsub); 
      	return(PS_EXP_TRUE); 
      } 
      insert_sorted_blist_dummy_head(
        newsub->type, 
        child, 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    pop_quantified_value_stack(psub); 
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_FALSE); 
    case 1: 
      child = newsub->u.bexp.blist->subexp; 
      free(newsub->u.bexp.blist); 
      free(newsub); 
      return(child); 
    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub));
    }
  }

  case RED: 
    return(psub); 

  default:
    fprintf(RED_OUT, "\nHuh ? (in rec_catch concurrent accesses)\n");
    bk(); 
  }
}
  /* rec_adjust_specific_pi() */




struct ps_exp_type	*adjust_specific_pi(
  struct ps_exp_type	*psub, 
  int			pi
) {
  PI_ADJUST_SPECIFIC = pi; 
  
  return(rec_adjust_specific_pi(psub)); 	
}
  /* adjust_specific_pi() */ 




  
// #ifdef RED_DEBUG_EXP_MODE
int	count_red_local = 0; 
// #endif 

struct red_type	*rec_local(psub, depth) 
     int		depth;
     struct ps_exp_type	*psub;
{
  int				i, jj, ci, v1i, c1i, v2i, c2i, 
				rvalue, v, lb, ub, zi;
  struct parse_variable_type	*v1, *v2;
  struct ps_bunit_type		*pbu;
  struct red_type		*result, *lconj, *lchild, *child, *rhs;

  switch(psub->type) {
  case TYPE_FALSE :
    return (NORM_FALSE);
  case TYPE_TRUE :
    return (NORM_TRUE);
  case TYPE_BDD: 
    lconj = red_operand_indirection(psub, W_PI); 
    v1i = psub->u.atom.var_index;
    result = NORM_FALSE;
    for (c1i = 0; c1i < lconj->u.ddd.child_count; c1i++) {
      lchild = lconj->u.ddd.arc[c1i].child; 
      for (v2i = lconj->u.ddd.arc[c1i].lower_bound; 
	   v2i <= lconj->u.ddd.arc[c1i].upper_bound; 
	   v2i++
	   ) { 
//        v2i = variable_index[VAR[v1i].TYPE][i][VAR[v1i].OFFSET];
	child = bdd_new(v2i, NORM_FALSE, NORM_NO_RESTRICTION);  
	child = red_bop(AND, lchild, child); 
	result = red_bop(OR, result, child); 
      }
    }
    return(result); 
    
    break; 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, 
      "\nError: unexpected synchronizer %s in a local predicate.\n", 
      psub->u.atom.var_name
    ); 
    fflush(RED_OUT); 
    exit(0); 
    
    break; 
  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    if (W_PI < 0 && (psub->exp_status & FLAG_LOCAL_IDENTIFIER)) {
      return(NORM_NO_RESTRICTION); 
    } 
    else if (   psub->u.ineq.type == FLAG_EXP_DISCRETE_CONSTANT
	     || psub->u.ineq.type == FLAG_EXP_DISCRETE_LINEAR
	     || !(psub->var_status & FLAG_EXP_STATE_INSIDE) 
	     ) {
      return(rec_discrete_ineq_linear(psub));
    }
    else if (GSTATUS[INDEX_SYSTEM_TYPE] & FLAG_SYSTEM_HYBRID) {
      return(red_hybrid_ineq(psub, W_PI));
    }
    else {
      return(rec_clock_ineq(psub));
    }
    break; 
  case ARITH_EQ :
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nred_local = %1d\n", ++count_red_local); 
    pcform(psub); 
    fflush(RED_OUT); 
    #endif 
    
    if (W_PI < 0 && (psub->exp_status & FLAG_LOCAL_IDENTIFIER)) { 
      return(NORM_NO_RESTRICTION); 
    } 
/*
    fprintf(RED_OUT, "\nred_local = %1d, psub->u.arith.type=%1d\n", 
      ++count_red_local, psub->u.arith.type 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/
    switch(psub->u.arith.status & MASK_EXP_TYPE) { 
    case FLAG_EXP_CLOCK_MIXED: 
      if (psub->u.arith.lhs_exp->type == TYPE_CLOCK) { 
      	c1i = psub->u.arith.lhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[c1i][0]; 
      } 
      else { 
      	c1i = psub->u.arith.lhs_exp->u.arith.rhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[0][c1i]; 
      } 
      rhs = rec_discrete_value(psub->u.arith.rhs_exp); 
      result = NORM_FALSE; 
      if (psub->type == ARITH_LESS) 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound - 1
      	    )
      	  ); 
      	}
      else 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound 
      	    )
      	  ); 
      	}
      return(result); 
      break; 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
      if (psub->type == ARITH_GREATER || psub->type == ARITH_GEQ) { 
      	fprintf(RED_OUT, "\nError: We do not expect this!\n"); 
      	fflush(RED_OUT); 
      	bk(0); 
      } 
      else { 
      	c1i = psub->u.arith.lhs_exp->u.arith.lhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
      	c2i = psub->u.arith.lhs_exp->u.arith.rhs_exp->u.atom.var_index; 
      	c2i = variable_index[TYPE_CLOCK][W_PI][VAR[c2i].OFFSET]; 
      	c2i = VAR[c2i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[c1i][c2i]; 
      } 
      rhs = rec_discrete_value(psub->u.arith.rhs_exp); 
      result = NORM_FALSE; 
      if (psub->type == ARITH_LESS) 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound - 1
      	    )
      	  ); 
      	}
      else 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound 
      	    )
      	  ); 
      	}
      return(result); 
      break; 
    case FLAG_EXP_DISCRETE_CONSTANT: 
      return(red_discrete_ineq(psub, W_PI)); 
    default: 
      if (!(psub->var_status & FLAG_EXP_STATE_INSIDE)) {
        return(red_discrete_ineq_arith(psub->type, 
          rec_discrete_value(psub->u.arith.lhs_exp), 
          rec_discrete_value(psub->u.arith.rhs_exp)
        ) ); 
      } 
      return(lazy_atom(W_PI, psub)); 
    }
    break; 
  case ARITH_CONDITIONAL: 
    lconj = rec_local(psub->u.arith_cond.cond, depth+1); 
    lchild = rec_local(psub->u.arith_cond.if_exp, depth+1); 
    child = rec_local(psub->u.arith_cond.else_exp, depth+1); 
    return(red_bop(OR, 
      red_bop(AND, lconj, lchild), 
      red_bop(AND, red_complement(lconj), child)
    ) ); 
  case TYPE_INLINE_BOOLEAN_DECLARE:     
  case TYPE_INLINE_DISCRETE_DECLARE: 
  case TYPE_INLINE_ARGUMENT: 
    fprintf(RED_OUT, "\nError: This should not be here!\n"); 
    fflush(RED_OUT); 
    bk(0); 

  case TYPE_INLINE_CALL: 
    return(rec_local(psub->u.inline_call.instantiated_exp, depth+1)); 

  case AND :
    result = NORM_TRUE;
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      result = red_bop(AND, result, rec_local(pbu->subexp, depth+1));
    }
    return(result);
  case OR :
    result = NORM_FALSE;
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      result = red_bop(OR, result, rec_local(pbu->subexp, depth+1)); 
    }
    return(result);
  case NOT :
    result = red_complement(rec_local(psub->u.bexp.blist->subexp, depth+1)); 
    return(result); 
  case IMPLY :
    result = red_complement(rec_local(psub->u.bexp.blist->subexp, depth+1)); 
    result = red_bop(OR, result, 
		     rec_local(psub->u.bexp.blist->bnext->subexp, depth+1)
		     ); 
    return(result);
  case FORALL: 
    result = NORM_TRUE; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &jj); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &jj); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      child = rec_local(psub->u.qexp.child, depth+1);   
      if (child == NORM_FALSE) {
        pop_quantified_value_stack(psub); 
        return(NORM_FALSE); 
      }
      else 
        result = red_bop(AND, child, result); 
    }
    pop_quantified_value_stack(psub); 

    return(result);
    break;
  case EXISTS :
    result = NORM_FALSE; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &jj); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &jj); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      child = rec_local(psub->u.qexp.child, depth+1);   
      if (child == NORM_TRUE) {
        pop_quantified_value_stack(psub); 
        return(NORM_TRUE); 
      }
      else 
        result = red_bop(OR, child, result); 
    }
    pop_quantified_value_stack(psub); 
    return(result);
    break;

  case RED: 
    if (psub == PS_EXP_TRUE) 
      return(NORM_NO_RESTRICTION); 
    else if (psub == PS_EXP_FALSE) 
      return(NORM_FALSE); 

  default: 
    fprintf(RED_OUT, "\nError 1: Unrecognized condition operator %1d.\n", psub->type); 
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 

  }
}
  /* rec_local() */ 




/* When -#PS <= pi <= 1, pi means a process identifier of the peer process to process |pi|. 
 * pi == -P, means we want to collect the local condition of all the peers of process P.  
 */ 
struct red_type	*red_local(
  struct ps_exp_type		*psub, 
  int				pi, 
  int				depth
) {
  struct ps_exp_type	*tmp_sub;
  struct red_type	*result;

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\n====[red_local for pi=%1d]====================================\n", pi);
  pcform(psub);
  fprintf(RED_OUT, "\n");
  #endif 

  W_PI = pi;
  result = rec_local(psub, depth);

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "instantiated red for pi=%1d\n", pi);
  red_print_graph(result);
  fflush(RED_OUT);
  #endif 

  return(result);
}
/* red_local() */






struct red_type	*rec_global(psub, depth)
     int		depth; 
     struct ps_exp_type	*psub; 
{
  int				i, v1i, ci, zi, c1i, v2i, c2i, rvalue; 
  struct parse_variable_type	*v1, *v2; 
  struct ps_bunit_type		*pbu; 
  struct red_type		*result, *lconj, *rhs, *lchild, *child; 

  switch(psub->type) {
  case TYPE_FALSE :
    return (NORM_FALSE); 
  case TYPE_TRUE :
    return (NORM_TRUE); 
  case TYPE_BDD: 
    lconj = red_operand_indirection(psub, W_PI); 
//    v1i = psub->u.atom.var_index;
    result = NORM_FALSE;
    for (c1i = 0; c1i < lconj->u.ddd.child_count; c1i++) {
      lchild = lconj->u.ddd.arc[c1i].child; 
      for (v2i = lconj->u.ddd.arc[c1i].lower_bound; 
	   v2i <= lconj->u.ddd.arc[c1i].upper_bound; 
	   v2i++
	   ) { 
//        v2i = variable_index[VAR[v1i].TYPE][i][VAR[v1i].OFFSET]; 
        if (psub->var_status & FLAG_VAR_PRIMED) 
          v2i = VAR[v2i].PRIMED_VI; 
	child = bdd_new(v2i, NORM_FALSE, NORM_NO_RESTRICTION);  
	child = red_bop(AND, child, lchild); 
	result = red_bop(OR, result, child); 
      }
    }
    return(result); 
    
    break; 
  case TYPE_SYNCHRONIZER: 
    v1i = psub->u.atom.var_index; 
    if (psub->u.atom.exp_base_proc_index == PS_EXP_GLOBAL_IDENTIFIER) { 
      result = NORM_FALSE; 
      for (i = 1; i <= PROCESS_COUNT; i++) { 
      	v2i = variable_index[TYPE_SYNCHRONIZER][i][VAR[v1i].OFFSET]; 
      	result = red_bop(OR, result, 
      	  bdd_new(v2i, NORM_FALSE, NORM_NO_RESTRICTION)
      	); 
      } 
      return(result); 
    } 
    else { 
      i = get_value(psub->u.atom.exp_base_proc_index, 0, &v2i); 
      if (v2i != FLAG_SPECIFIC_VALUE) { 
      	fprintf(RED_OUT, "\nERROR: illegal event enforcer "); 
      	pcform(psub->u.atom.exp_base_proc_index); 
      	fflush(RED_OUT); 
      	exit(0); 
      } 
      v2i = variable_index[TYPE_SYNCHRONIZER][i][VAR[v1i].OFFSET]; 
      return(bdd_new(v2i, NORM_FALSE, NORM_NO_RESTRICTION));  
    }
    break; 
  case EQ :
  case NEQ:
  case LEQ:
  case LESS:
  case GREATER:
  case GEQ: 
    if (W_PI < 0 && (psub->exp_status & FLAG_LOCAL_IDENTIFIER)) {
      return(NORM_NO_RESTRICTION); 
    } 
    else if (   psub->u.ineq.type == FLAG_EXP_DISCRETE_CONSTANT
	     || psub->u.ineq.type == FLAG_EXP_DISCRETE_LINEAR
	     || !(psub->var_status & FLAG_EXP_STATE_INSIDE) 
	     ) {
      return(rec_discrete_ineq_linear(psub));
    }
    else if (GSTATUS[INDEX_SYSTEM_TYPE] & FLAG_SYSTEM_HYBRID) {
      return(red_hybrid_ineq(psub, W_PI));
    }
    else {
      return(rec_clock_ineq(psub));
    }
    break; 
  case ARITH_EQ :
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ: 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "\nred_local = %1d\n", ++count_red_local); 
    pcform(psub); 
    fflush(RED_OUT); 
    #endif 
    
    if (W_PI < 0 && (psub->exp_status & FLAG_LOCAL_IDENTIFIER)) { 
      return(NORM_NO_RESTRICTION); 
    } 
/*
    fprintf(RED_OUT, "\nred_local = %1d, psub->u.arith.type=%1d\n", 
      ++count_red_local, psub->u.arith.type 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/
    switch(psub->u.arith.status & MASK_EXP_TYPE) { 
    case FLAG_EXP_CLOCK_MIXED: 
      /* if (psub->type == ARITH_GREATER || psub->type == ARITH_GEQ) { 
      	fprintf(RED_OUT, "\nError: We do not expect this!\n"); 
      	fflush(RED_OUT); 
      	bk(0); 
      } 
      else */
      if (psub->u.arith.lhs_exp->type == TYPE_CLOCK) { 
      	c1i = psub->u.arith.lhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[c1i][0]; 
      } 
      else { 
      	c1i = psub->u.arith.lhs_exp->u.arith.rhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[0][c1i]; 
      } 
      rhs = rec_discrete_value(psub->u.arith.rhs_exp); 
      result = NORM_FALSE; 
      if (psub->type == ARITH_LESS) 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound - 1
      	    )
      	  ); 
      	}
      else 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound 
      	    )
      	  ); 
      	}
      return(result); 
      break; 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
      if (psub->type == ARITH_GREATER || psub->type == ARITH_GEQ) { 
      	fprintf(RED_OUT, "\nError: We do not expect this!\n"); 
      	fflush(RED_OUT); 
      	bk(0); 
      } 
      else { 
      	c1i = psub->u.arith.lhs_exp->u.arith.lhs_exp->u.atom.var_index; 
      	c1i = variable_index[TYPE_CLOCK][W_PI][VAR[c1i].OFFSET]; 
      	c1i = VAR[c1i].U.CLOCK.CLOCK_INDEX; 
      	c2i = psub->u.arith.lhs_exp->u.arith.rhs_exp->u.atom.var_index; 
      	c2i = variable_index[TYPE_CLOCK][W_PI][VAR[c2i].OFFSET]; 
      	c2i = VAR[c2i].U.CLOCK.CLOCK_INDEX; 
        zi = ZONE[c1i][c2i]; 
      } 
      rhs = rec_discrete_value(psub->u.arith.rhs_exp); 
      result = NORM_FALSE; 
      if (psub->type == ARITH_LESS) 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound - 1
      	    )
      	  ); 
      	}
      else 
        for (ci = 0; ci < rhs->u.ddd.child_count; ci++) { 
          result = red_bop(OR, result, 
      	    crd_one_constraint(
      	      rhs->u.ddd.arc[ci].child, 
      	      zi, 2 * rhs->u.ddd.arc[ci].upper_bound 
      	    )
      	  ); 
      	}
      return(result); 
      break; 
    default: 
      return(red_discrete_ineq(psub, 0)); 
    }
    break; 
  
  case ARITH_CONDITIONAL: 
    lconj = rec_global(psub->u.arith_cond.cond, depth+1); 
    lchild = rec_discrete_value(psub->u.arith_cond.if_exp); 
    child = rec_discrete_value(psub->u.arith_cond.else_exp); 
    return(red_bop(OR, 
      red_bop(AND, lconj, lchild), 
      red_bop(AND, red_complement(lconj), child)
    ) ); 
    break; 
  case TYPE_INLINE_CALL: 
    return(rec_global(psub->u.inline_call.instantiated_exp, depth+1)); 
  case RED: 
    return(psub->u.rpred.red); 
  default:
    fprintf(RED_OUT, "\nError 2: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n");
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
/* rec_global() */



struct red_type	*red_global(
  struct ps_exp_type	*psub, 
  int			flag_delayed_evaluation, 
  int			depth 
) {
  struct ps_exp_type	*tmp_sub;
  struct red_type	*result;

  W_PI = PROC_GLOBAL;
  FLAG_POLICY_EVALUATION = flag_delayed_evaluation;  
  result = rec_global(psub, depth); 

  return(result); 
}
/* red_global() */ 








/**************************************************************
 *
 *  The following procedures are for delayed evaluation. 
 */ 

  
  
  



int	bit_op_value(
  int	op, 
  int	x, 
  int	y
) {
  switch (op) { 
  case BIT_OR: 
    return(x | y); 
  case BIT_AND:  
    return(x & y); 
  case BIT_SHIFT_RIGHT: 
    return(x >> y); 
  case BIT_SHIFT_LEFT: 
    return(x << y); 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal bitwise logic operation %1d.\n", 
      op
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* bit_op_value() */ 





int	VI_EVV, DLB_EVV, DUB_EVV; 
float	FLB_EVV, FUB_EVV; 
double	DFLB_EVV, DFUB_EVV; 

struct red_type	*rec_extract_variable_values(d)
     struct red_type	*d;
{
  int					ci, v;
  struct red_type			*result, *child;
  struct cache10_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(d);

  ce = cache10_check_result_key(OP_EXTRACT_VARIABLE_VALUES, d, 
    (struct hrd_exp_type *) VI_EVV, 
    DLB_EVV, 
    DUB_EVV, 
    *((int *) &FLB_EVV), 
    *((int *) &FUB_EVV), 
    ((int *) &DFLB_EVV)[0], 
    ((int *) &DFLB_EVV)[1], 
    ((int *) &DFUB_EVV)[0], 
    ((int *) &DFUB_EVV)[1]  
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  else if (d == NORM_NO_RESTRICTION) 
    switch (VAR[VI_EVV].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
      result = NORM_FALSE; 
      for (v = DLB_EVV; v <= DUB_EVV; v++) { 
      	result = red_bop(OR, result, 
      	  ddd_lone_subtree(ddd_atom(VI_EVV, v, v), VI_VALUE, v, v) 
      	); 
      }
      return(result); 
      break; 
    case TYPE_FLOAT: 
      return(ce->result = fdd_lone_subtree(
          fdd_atom(VI_EVV, FLB_EVV, FUB_EVV), 
          FLOAT_VALUE, FLB_EVV, FUB_EVV
      ) ); 
      break; 
    case TYPE_DOUBLE: 
      return(ce->result = dfdd_lone_subtree(
          dfdd_atom(VI_EVV, DFLB_EVV, DFUB_EVV), 
          DOUBLE_VALUE, DFLB_EVV, DFUB_EVV
      ) ); 
      break; 
    default: 
      bk(0);  
    }
  else if (d->var_index > VI_EVV) { 
    switch (VAR[VI_EVV].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
      return(ce->result = ddd_lone_subtree(
          ddd_lone_subtree(d, VI_EVV, DLB_EVV, DUB_EVV), 
          VI_VALUE, DLB_EVV, DUB_EVV
      ) ); 
      break; 
    case TYPE_FLOAT: 
      return(ce->result = fdd_lone_subtree(
          fdd_lone_subtree(d, VI_EVV, FLB_EVV, FUB_EVV), 
          FLOAT_VALUE, FLB_EVV, FUB_EVV
      ) ); 
      break; 
    case TYPE_DOUBLE: 
      return(ce->result = dfdd_lone_subtree(
          dfdd_lone_subtree(d, VI_EVV, DFLB_EVV, DFUB_EVV), 
          DOUBLE_VALUE, DFLB_EVV, DFUB_EVV
      ) ); 
      break; 
    default: 
      bk(0);  
    }
  } 
  
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      child = rec_extract_variable_values(d->u.crd.arc[ci].child);
      child = crd_one_constraint(child, d->var_index,
	d->u.crd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      child = rec_extract_variable_values(d->u.hrd.arc[ci].child);
      child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
	d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    if (d->var_index == VI_EVV) { 
      float	lb, ub; 
      
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      	lb = flt_max(FLB_EVV, d->u.fdd.arc[ci].lower_bound); 
      	ub = flt_min(FUB_EVV, d->u.fdd.arc[ci].upper_bound);
      	if (lb > ub) 
      	  continue; 
        child = fdd_one_constraint(
          d->u.fdd.arc[ci].child, d->var_index, lb, ub
        ); 
        child = fdd_lone_subtree(
          child, FLOAT_VALUE, lb, ub
        ); 
        result = red_bop(OR, result, child);
    } }
    else {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_extract_variable_values(d->u.fdd.arc[ci].child);
        child = fdd_one_constraint(child, d->var_index, 
          d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
    } }
    break;
  case TYPE_DOUBLE:
    if (d->var_index == VI_EVV) { 
      double	lb, ub; 
      
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      	lb = dble_max(DFLB_EVV, d->u.dfdd.arc[ci].lower_bound); 
      	ub = dble_min(DFUB_EVV, d->u.dfdd.arc[ci].upper_bound);
      	if (lb > ub) 
      	  continue; 
        child = dfdd_one_constraint(
          d->u.dfdd.arc[ci].child, d->var_index, lb, ub
        ); 
        child = dfdd_lone_subtree(
          child, DOUBLE_VALUE, lb, ub
        ); 
        result = red_bop(OR, result, child);
    } }
    else {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_extract_variable_values(d->u.dfdd.arc[ci].child);
        child = dfdd_one_constraint(child, d->var_index, 
          d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
    } }
    break;
  default:
    if (d->var_index == VI_EVV) { 
      int	lb, ub; 
      
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      	lb = dble_max(DLB_EVV, d->u.ddd.arc[ci].lower_bound); 
      	ub = dble_min(DUB_EVV, d->u.ddd.arc[ci].upper_bound);
      	if (lb > ub) 
      	  continue; 
        child = ddd_one_constraint(
          d->u.ddd.arc[ci].child, d->var_index, lb, ub
        ); 
        child = ddd_lone_subtree(
          child, VI_VALUE, lb, ub
        ); 
        result = red_bop(OR, result, child);
    } }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_extract_variable_values(d->u.ddd.arc[ci].child);
        child = ddd_one_constraint(child, 
          d->var_index, d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child);
    } }
  }

  return(ce->result = result); 
}
  /* rec_extract_variable_values() */



struct red_type	*red_extract_variable_values(
  struct red_type	*d, 
  int			vi, 
  int			dlb, 
  int			dub,  
  float			flb, 
  float 		fub, 
  double		dflb, 
  double		dfub
) {
  VI_EVV = vi; 
  DLB_EVV = dlb; 
  DUB_EVV = dub; 
  FLB_EVV = flb; 
  FUB_EVV = fub; 
  DFLB_EVV = dflb; 
  DFUB_EVV = dfub; 
  
  return(rec_extract_variable_values(d)); 
}
  /* red_extract_variable_values() */ 




int	count_dev = 0, countrec_delayed_exp_value = 0; 

struct red_type	*rec_delayed_exp_value(
  struct ps_exp_type	*psub 
) { 
  int				vi, v, cix, ciy, ppi, vx, vy, value, 
				lb, ub, pi, local_count_dev, size_th = 0;
  struct ps_bunit_type		*pbu;
//  struct parse_indirect_type	*pt;
  struct red_type		*result, *childx, *childy, 
				*conj, *conjx, *conjy, *filter, *red_addr;
  struct ps_exp_type		*var;
  struct interval_link_type	*ip; 

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\ncountrec_delayed_exp_value = %1d\n", ++countrec_delayed_exp_value); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  switch (psub->type) {
  case TYPE_FALSE :
  case TYPE_NULL:
    return(ddd_atom(VI_VALUE, 0, 0));
  case TYPE_TRUE :
    return(ddd_atom(VI_VALUE, 1, 1));
  case TYPE_LOCAL_IDENTIFIER: 
    if (LAZY_PI > 0) 
      return(ddd_atom(VI_VALUE, LAZY_PI, LAZY_PI)); 
    else if (LAZY_PI == 0 /* PROC_GLOBAL */) { 
      fprintf(RED_OUT, "Error: A local identifier in a global environment ?\n"); 
      bk(0); 
    } 
    else if (LAZY_PI == FLAG_ANY_PROCESS || LAZY_PI == FLAG_ANY_VALUE)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT));
    else if (LAZY_PI == INDEX_LOCAL_IDENTIFIER) { 
      fprintf(RED_OUT, "Error: A local identifier in a local-identifier setting ?\n"); 
      bk(0); 
    } 
    else if (LAZY_PI == FLAG_ANY_VARIABLE) { 
      return(ddd_atom(VI_VALUE, 0, VARIABLE_COUNT-1)); 
    } 
    else if (LAZY_PI < 0 && LAZY_PI >= -1*PROCESS_COUNT) { 
    	if (LAZY_PI == -1 * PROCESS_COUNT) { 
    		return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1)); 
    	} 
    	else if (LAZY_PI == -1) {
    		return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT)); 
    	}
    	else 
        return(red_bop(OR,
                       ddd_atom(VI_VALUE, 1, -LAZY_PI-1),
                       ddd_atom(VI_VALUE, -LAZY_PI+1, PROCESS_COUNT)
                       )
               );
    }
    else {
    	fprintf(RED_OUT, "Undefined process identifier values.\n"); 
    	fflush(RED_OUT); 
    	bk(0); 
    }
  case TYPE_PEER_IDENTIFIER:
    if (PROCESS_COUNT <= 1)
      return(NORM_FALSE);
    else if (LAZY_PI < 0) 
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT)); 
    else if (LAZY_PI == 1)
      return(ddd_atom(VI_VALUE, 2, PROCESS_COUNT));
    else if (LAZY_PI == PROCESS_COUNT)
      return(ddd_atom(VI_VALUE, 1, PROCESS_COUNT-1));
    else
      return(red_bop(OR,
		     ddd_atom(VI_VALUE, 1, LAZY_PI-1),
		     ddd_atom(VI_VALUE, LAZY_PI+1, PROCESS_COUNT)
		     )
	     );
  case TYPE_TRASH:
    return(NORM_NO_RESTRICTION);
  case TYPE_CONSTANT:
    return(ddd_atom(VI_VALUE, psub->u.value, psub->u.value)); 
  case TYPE_MACRO_CONSTANT:
    return(ddd_atom(VI_VALUE, 
      psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value, 
      psub->u.inline_call.inline_declare
      ->u.inline_declare.declare_exp
      ->u.value
    ) ); 
  case TYPE_PROCESS_COUNT: 
    return(ddd_atom(VI_VALUE, PROCESS_COUNT, PROCESS_COUNT));
  case TYPE_MODE_COUNT: 
    return(ddd_atom(VI_VALUE, MODE_COUNT, MODE_COUNT));
  case TYPE_XTION_COUNT: 
    return(ddd_atom(VI_VALUE, XTION_COUNT, XTION_COUNT));
  case TYPE_MODE_INDEX: 
    return(ddd_atom(VI_VALUE, psub->u.mode_index.value, psub->u.mode_index.value));
  
  case TYPE_INTERVAL: 
    childx = rec_delayed_exp_value(psub->u.interval.lbound_exp);
    childy = rec_delayed_exp_value(psub->u.interval.rbound_exp);
    return(red_interval_value(childx, childy));

  case TYPE_REFERENCE: 
    red_addr = rec_delayed_exp_value(psub->u.exp); 
    if (red_addr == NORM_FALSE || red_addr == NORM_NO_RESTRICTION) 
      return(red_addr); 
    result = NORM_FALSE; 
    vy = 0; 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
           vi <= red_addr->u.ddd.arc[cix].upper_bound; 
           vi++
           ) { 
        if (VAR[vi].TYPE != TYPE_DISCRETE) 
          continue; 
	ip = GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET]; 
	for (; ip; ip = ip->next_interval_link) { 
	  if (   (ip->u.dint.ub > 1 && ip->u.dint.lb < -1) 
	      || (vy = vy + ip->u.dint.ub - ip->u.dint.lb+1) > 3
	      ) { 
            fprintf(RED_OUT, "\nERROR, uninitialized indirect address exp: "); 
            print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
            fprintf(RED_OUT, "\n"); 
            return(NORM_FALSE); 
	  } 
	  size_th = size_th + ip->u.dint.ub - ip->u.dint.lb + 1; 
	  if (size_th > THRESHOLD_LAZY_SIZE) 
	    return(NULL); 
	  conj = red_extract_variable_values(
	    red_addr->u.ddd.arc[cix].child, vi, 
	    ip->u.dint.lb, ip->u.dint.ub,  
	    -1*FLT_MAX, FLT_MAX, 
	    -1*DBL_MAX, DBL_MAX 
	  ); 
	  result = red_bop(OR, result, conj); 
    } } } 
    return(result); 
    break; 
  case TYPE_DEREFERENCE: 
    red_addr = rec_delayed_operand_indirection(psub->u.exp); 
    if (   (!red_addr) 
        || red_addr == NORM_FALSE 
        || red_addr == NORM_NO_RESTRICTION
        ) 
      return(red_addr); 

    result = NORM_FALSE; 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      result = red_bop(OR, result, 
        ddd_one_constraint(red_addr->u.ddd.arc[cix].child, 
          VI_VALUE, red_addr->u.ddd.arc[cix].lower_bound, 
          red_addr->u.ddd.arc[cix].upper_bound
      ) ); 
    } 
    return(result); 
    break; 

  case TYPE_QFD:
    v = qfd_value(psub->u.atom.var_name);
    return(ddd_atom(VI_VALUE, v, v));

  case TYPE_POINTER:
    
  case TYPE_DISCRETE:
/*
    local_count_dev = ++count_dev; 
    fprintf(RED_OUT, "\ndelayed eval %1d: ", local_count_dev); 
    pcform(psub); 
    fflush(RED_OUT); 
    if (local_count_dev == 25) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
      fflush(RED_OUT); 
    } 
*/
/*
    ++countrec_delayed_exp_value; 
    if (countrec_delayed_exp_value == 210) { 
      fprintf(RED_OUT, "\ncountrec_delayed_exp_value = %1d for discrete\n", 
        countrec_delayed_exp_value
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
    }
*/
    red_addr = rec_delayed_operand_indirection(psub); 
    if (!red_addr) {
      fprintf(RED_OUT, 
        "\nERROR: Caught an out-dated NULL red_addr in rec_delayed_exp_value().\n"
      ); 
      fflush(RED_OUT); 
//      bk(0); 
    }
    else if (red_addr == NORM_FALSE)
      return(NORM_FALSE); 
    #ifdef RED_DEBUG_EXP_MODE
    if (countrec_delayed_exp_value == 210) { 
      fprintf(RED_OUT, "red_addr with psub->u.atom.var_index:%1d\n", psub->u.atom.var_index); 
      red_print_graph(red_addr); 
    }
    #endif 
    
    result = NORM_FALSE; 
    #ifdef RED_DEBUG_EXP_MODE
    pcform(psub); 
    #endif 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, 
	  "countrec_delayed_exp_value=%1d, in rec_delayed_exp_value for vi=%1d\n", 
	  countrec_delayed_exp_value, 
	  vi
	); 
	fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
	#endif 
	
	ip = GLOBAL_INTERVAL_LIST[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET]; 
        switch (VAR[vi].TYPE) { 
        case TYPE_POINTER: 
	  if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) { 
	    for (; ip; ip = ip->next_interval_link) { 
	      size_th = size_th + ip->u.dint.ub - ip->u.dint.lb + 1; 
	      if (size_th > THRESHOLD_LAZY_SIZE) 
	        return(NULL); 
	      childx = red_extract_variable_values(
	        red_addr->u.ddd.arc[cix].child, vi, 
	        ip->u.dint.lb, ip->u.dint.ub,  
	        -1*FLT_MAX, FLT_MAX, 
	        -1*DBL_MAX, DBL_MAX 
	      ); 
	      result = red_bop(OR, result, childx); 
            } 
            break; 
          } 
        case TYPE_DISCRETE: 
          vy = 0; // This variable is used to accumulate the number of values to 
                  // vi.  If the number is greater than 3, we think it is too 
                  // much and signal an uninitialized variable warning. 
	  for (; ip; ip = ip->next_interval_link) { 
	    size_th = size_th + ip->u.dint.ub - ip->u.dint.lb + 1; 
	    if (size_th > THRESHOLD_LAZY_SIZE) 
	      return(NULL); 
	    if (   (ip->u.dint.ub > 1 && ip->u.dint.lb < -1) 
  	        || (vy = vy + ip->u.dint.ub - ip->u.dint.lb+1) > 3
	        ) { 
              if (++COUNT_DD_BLOWUP <= 10) { 
              	fprintf(RED_OUT, 
              	  "\nWARNING, values of variable: %s could blow up the decision diagram.\n", 
                  VAR[vi].NAME
                ); 
              }
              else if (COUNT_DD_BLOWUP == 11) { 
              	fprintf(RED_OUT, 
              	  "\nWARNING, values of more than 10 variables could blow up the decision diagram\n" 
                ); 
              } 
//              return(NORM_FALSE); 
	    } 
	    childx = red_extract_variable_values(
	      red_addr->u.ddd.arc[cix].child, vi, 
	      ip->u.dint.lb, ip->u.dint.ub,  
	      -1*FLT_MAX, FLT_MAX, 
	      -1*DBL_MAX, DBL_MAX 
	    ); 
	    result = red_bop(OR, result, childx); 
          } 
          break; 
        case TYPE_FLOAT: 
	  for (; ip; ip = ip->next_interval_link) { 
	    childx = red_extract_variable_values(
	      red_addr->u.ddd.arc[cix].child, vi, 
	      INT_MIN, INT_MAX, 
	      ip->u.fint.lb, ip->u.fint.ub,  
	      -1*DBL_MAX, DBL_MAX 
	    ); 
	    result = red_bop(OR, result, childx); 
          }
          break; 
        case TYPE_DOUBLE: 
	  for (; ip; ip = ip->next_interval_link) { 
	    childx = red_extract_variable_values(
	      red_addr->u.ddd.arc[cix].child, vi, 
	      INT_MIN, INT_MAX, 
	      -1*FLT_MAX, FLT_MAX, 
	      ip->u.dfint.lb, ip->u.dfint.ub 
	    ); 
	    result = red_bop(OR, result, childx); 
	  }
          break; 
        default: 
          bk(0); 
    } } }
    return(result); 

  case TYPE_FLOAT:
/*
    local_count_dev = ++count_dev; 
    fprintf(RED_OUT, "\ndelayed eval %1d: ", local_count_dev); 
    pcform(psub); 
    fflush(RED_OUT); 
    if (local_count_dev == 25) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
      fflush(RED_OUT); 
    } 
*/
    red_addr = rec_delayed_operand_indirection(psub); 
    if (!red_addr) 
      return(NULL); 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "red_addr with psub->u.atom.var_index:%1d\n", psub->u.atom.var_index); 
    red_print_graph(red_addr); 
    #endif 
    
    result = NORM_FALSE; 
    #ifdef RED_DEBUG_EXP_MODE
    pcform(psub); 
    #endif 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, 
	  "countrec_delayed_exp_value=%1d, in rec_delayed_exp_value for vi=%1d\n", 
	  countrec_delayed_exp_value, 
	  vi
	); 
	fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
        #endif 
	
	ip = GLOBAL_INTERVAL_LIST[VAR[vi].TYPE]
	     [VAR[vi].PROC_INDEX]
	     [VAR[vi].OFFSET]; 
	for (; ip; ip = ip->next_interval_link) { 
	  childx = red_extract_variable_values(
	    red_addr->u.ddd.arc[cix].child, vi, 
	    INT_MIN, INT_MAX, 
	    ip->u.fint.lb, ip->u.fint.ub,  
	    -1*DBL_MAX, DBL_MAX 
	  ); 
	  result = red_bop(OR, result, childx); 
    } } } 
    return(result); 

  case TYPE_DOUBLE:
/*
    local_count_dev = ++count_dev; 
    fprintf(RED_OUT, "\ndelayed eval %1d: ", local_count_dev); 
    pcform(psub); 
    fflush(RED_OUT); 
    if (local_count_dev == 25) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
      fflush(RED_OUT); 
    } 
*/
    red_addr = rec_delayed_operand_indirection(psub); 
    if (!red_addr) 
      return(NULL); 
    #ifdef RED_DEBUG_EXP_MODE
    fprintf(RED_OUT, "red_addr with psub->u.atom.var_index:%1d\n", psub->u.atom.var_index); 
    red_print_graph(red_addr); 
    #endif 
    
    result = NORM_FALSE; 
    #ifdef RED_DEBUG_EXP_MODE
    pcform(psub); 
    #endif 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, 
	  "countrec_delayed_exp_value=%1d, in rec_delayed_exp_value for vi=%1d\n", 
	  countrec_delayed_exp_value, 
	  vi
	); 
	fprintf(RED_OUT, "VAR[vi].NAME=%s\n", VAR[vi].NAME); 
	fprintf(RED_OUT, "VAR[vi].PROC=%1d\n", VAR[vi].PROC_INDEX); 
	#endif 
	
	ip = GLOBAL_INTERVAL_LIST[VAR[vi].TYPE]
	     [VAR[vi].PROC_INDEX]
	     [VAR[vi].OFFSET]; 
	for (; ip; ip = ip->next_interval_link) { 
	  childx = red_extract_variable_values(
	    red_addr->u.ddd.arc[cix].child, vi, 
	    INT_MIN, INT_MAX, 
	    -1*FLT_MAX, FLT_MAX, 
	    ip->u.dfint.lb, ip->u.dfint.ub 
	  ); 
	  result = red_bop(OR, result, childx); 
    } } } 
    return(result); 

  case TYPE_CLOCK:
    result = NORM_FALSE; 
    red_addr = rec_delayed_operand_indirection(psub); 
    if (!red_addr) 
      return(NULL); 
    for (cix = 0; cix < red_addr->u.ddd.child_count; cix++) { 
      conj = red_addr->u.ddd.arc[cix].child;
      for (vi = red_addr->u.ddd.arc[cix].lower_bound; 
	   vi <= red_addr->u.ddd.arc[cix].upper_bound; 
	   vi++
	   ) { 
	ciy = VAR[vi].U.CLOCK.CLOCK_INDEX;  
	for (v = 0; v < CLOCK_POS_INFINITY; v = v+2) { 
	  childx = crd_one_constraint(conj, ZONE[ciy][0], v+1); 
	  childx = crd_one_constraint(childx, ZONE[0][ciy], -1 * v); 
	  childx = ddd_one_constraint(childx, VI_VALUE, v/2, v/2); 
	  result = red_bop(OR, result, childx); 
	} 
      }
    }
    return(result); 
/*
    fprintf(RED_OUT, 
      "\nError: unexpected dense variable %s in red_lazy_discrete_value().\n", 
      psub->u.atom.var_name
    ); 
    fflush(RED_OUT); 
    exit(0); 
*/
    break;
  case TYPE_DENSE:
    fprintf(RED_OUT, "\nBug: how come there is a dense variable in a discrete expression!\n");
    fflush(RED_OUT);
    exit(0);
    break; 
  case TYPE_QSYNC_HOLDER: 
    vi = variable_index[TYPE_POINTER][LAZY_PI][psub->u.qsholder.qsync_var->index]; 
    result = NORM_FALSE;
    for (v = 1; v <= PROCESS_COUNT; v++)
      result = red_bop(OR, result, ddd_one_constraint(ddd_atom(VI_VALUE, v, v), vi, v, v)); 
    return(result); 
    break; 
  case BIT_NOT: 
    childx = rec_delayed_exp_value(psub->u.exp); 
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
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp);
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
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_add_value(1, childx, 1, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MINUS:
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_add_value(1, childx, -1, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MULTIPLY:
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp);
    if (!childy)
      return(NULL); 
    result = red_multiply_value(childx, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_DIVIDE:
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp); 
    if (!childy)
      return(NULL); 
    result = red_divide_value(childx, childy);
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
  case ARITH_MODULO: 
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp);
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp); 
    if (!childy)
      return(NULL); 
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
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
    break; 
  case ARITH_CONDITIONAL: 
    conj = rec_delayed_exp_value(psub->u.arith_cond.cond); 
    if (!conj)
      return(NULL); 
    childx = rec_delayed_exp_value(psub->u.arith_cond.if_exp); 
    if (!childx)
      return(NULL); 
    childy = rec_delayed_exp_value(psub->u.arith_cond.else_exp); 
    if (!childy)
      return(NULL); 
    result = red_bop(OR, 
      red_bop(AND, conj, childx), 
      red_bop(AND, childy, 
        red_bop(AND, RED_LAZY_SPACE, red_complement(conj))
    ) ); 
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(NULL); 
    return(result); 
    break; 
  case TYPE_INLINE_CALL: 
    return(rec_delayed_exp_value(psub->u.inline_call.instantiated_exp)); 
  case TYPE_BDD:
    fprintf(RED_OUT, 
      "\nError: unexpected bdd variable %s in an arithmetic expression.\n", 
      psub->u.atom.var_name 
    );   
    fflush(RED_OUT); 
    exit(0); 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "\nError: unexpected synchronizer variable %s in arithmetic an expression.\n", 
      psub->u.atom.var_name 
    ); 
    fflush(RED_OUT); 
    exit(0); 
  case ARITH_EQ: 
  case ARITH_NEQ: 
  case ARITH_GREATER: 
  case ARITH_GEQ: 
  case ARITH_LEQ: 
  case ARITH_LESS: 
    childx = rec_delayed_exp_value(psub->u.arith.lhs_exp); 
    if (!childx) 
      return(lazy_atom(LAZY_PI, psub)); 
    childy = rec_delayed_exp_value(psub->u.arith.rhs_exp); 
    if (!childy) 
      return(lazy_atom(LAZY_PI, psub)); 
    result = red_discrete_ineq_arith(psub->type, childx, childy); 
    if (red_path_threshold(result, THRESHOLD_LAZY_SIZE)) 
      return(lazy_atom(LAZY_PI, psub)); 
    else 
      return(result); 

  case AND :
    result = NORM_TRUE;
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      result = red_bop(AND, result, rec_delayed_exp_value(pbu->subexp));
    }
    return(result);
  case OR :
    result = NORM_FALSE;
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      result = red_bop(OR, result, rec_delayed_exp_value(pbu->subexp)); 
    }
    return(result);
  case NOT :
    result = red_complement(
      rec_delayed_exp_value(psub->u.bexp.blist->subexp)
    ); 
    return(result); 
  case IMPLY :
    result = red_complement(
      rec_delayed_exp_value(psub->u.bexp.blist->subexp)
    ); 
    result = red_bop(OR, result, 
      rec_delayed_exp_value(psub->u.bexp.blist->bnext->subexp)
    ); 
    return(result);
  case FORALL: 
    result = NORM_TRUE; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &v); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &v); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      childx = rec_delayed_exp_value(psub->u.qexp.child);   
      if (childx == NORM_FALSE) {
        pop_quantified_value_stack(psub); 
        return(NORM_FALSE); 
      }
      else 
        result = red_bop(AND, childx, result); 
    }
    pop_quantified_value_stack(psub); 

    return(result);
    break;
  case EXISTS :
    result = NORM_FALSE; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &v); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &v); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) {
      childx = rec_delayed_exp_value(psub->u.qexp.child);   
      if (childx == NORM_TRUE) {
        pop_quantified_value_stack(psub); 
        return(NORM_TRUE); 
      }
      else 
        result = red_bop(OR, childx, result); 
    }
    pop_quantified_value_stack(psub); 
    return(result);
    break;
  case PROJECT: 
    return(red_variable_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      psub->u.project.variable_index
    ) );
  case PROJECT_MCHUNK: 
    return(red_multi_variables_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      psub->u.project.variable_index % VARIABLE_COUNT, 
      psub->u.project.variable_index / VARIABLE_COUNT 
    ) );
  case PROJECT_VAR_SIM: 
    return(red_variable_sim_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      variable_index
      [VSIM_TYPE(psub->u.project.vsim_type_offset)]
      [1]
      [VSIM_OFFSET(psub->u.project.vsim_type_offset)] 
    ) );
  case PROJECT_CLOCK_SIM: 
    return(red_time_clock_sim_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      VAR[variable_index
        [TYPE_CLOCK][1][psub->u.project.clock_offset]
      ].U.CLOCK.CLOCK_INDEX
    ) );
  case PROJECT_TYPE: 
    return(red_type_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      psub->u.project.var_type
    ) );
  case PROJECT_PEER: 
    return(red_peer_eliminate(
      rec_delayed_exp_value(psub->u.project.child), 
      psub->u.project.var_proc
    ) );
  case PROJECT_TIME: 
    return(red_time_eliminate(
      rec_delayed_exp_value(psub->u.project.child) 
     ) );
  case PROJECT_QSYNC: 
    return(red_qsync_eliminate(
      rec_delayed_exp_value(psub->u.project.child) 
    ) );
  case PROJECT_LOCAL: 
    return(red_local_eliminate(
      rec_delayed_exp_value(psub->u.project.child) 
    ) );
  case PROJECT_CLOCK_LOWER_EXTEND: 
    return(red_clock_lower_extend(
      rec_delayed_exp_value(psub->u.project.child) 
    ) );
  case PROJECT_CLOCK_UPPER_EXTEND: 
    return(red_clock_upper_extend(
      rec_delayed_exp_value(psub->u.project.child) 
    ) );
  default: 
    fprintf(RED_OUT, 
      "\nERROR: an unexpected exp type %1d in rec_delayed_exp_value().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
/* rec_delayed_exp_value() */ 


int	count_dev_coll = 0; 

struct red_type	*red_delayed_exp_value(
  struct ps_exp_type	*psub, 
  int			pi, 
  struct red_type	*red_lazy_space
) { 
  struct red_type	*result; 

  if (red_lazy_space == NORM_FALSE) 
    return(NORM_FALSE); 
  
  LAZY_PI = pi; 
  RED_LAZY_SPACE = red_lazy_space; 
  
/*
  fprintf(RED_OUT, "\ndev_coll %1d\n", ++count_dev_coll); 
  fflush(RED_OUT); 
*/
  collect_value_intervals(pi, NULL, psub, red_lazy_space); 
  result = rec_delayed_exp_value(psub); 
  decollect_value_intervals(); 

  return(result); 
}
  /* red_delayed_exp_value() */ 






struct red_type	*rec_delayed_eval(d)
     struct red_type	*d;
{
  int			ci, olb, oub, orig_lazy_pi;
  struct red_type	*child, *result;
  struct hrd_exp_type	*he;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  struct rec_type	*rec, *nrec; 

  if (!(d->status & FLAG_RED_LAZY))
    return(d); 

  rec = rec_new(d, (struct red_type *) W_PI); 
  nrec = (struct rec_type *) add_23tree(
    rec, delayed_eval_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  }

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_delayed_eval(d->u.bdd.zero_child), 
      rec_delayed_eval(d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_delayed_eval(bc->child);
      child = crd_one_constraint(child, d->var_index, bc->upper_bound); 
      result = red_bop(OR, result, child);
    } 
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_delayed_eval(hc->child);
      child = hrd_one_constraint(child, 
        d->u.hrd.hrd_exp, 
        d->u.hrd.arc[ci].ub_numerator, 
        d->u.hrd.arc[ci].ub_denominator
      ); 
      result = red_bop(OR, result, child); 
    } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    orig_lazy_pi = LAZY_PI; 
    LAZY_PI = VAR[d->var_index].PROC_INDEX; 
    child = rec_delayed_exp_value(d->u.lazy.exp); 
    LAZY_PI = orig_lazy_pi; 
    result = red_bop(OR, 
      red_bop(AND, red_complement(child), 
        rec_delayed_eval(d->u.lazy.false_child)
      ), 
      red_bop(AND, child, 
        rec_delayed_eval(d->u.lazy.true_child)
    ) ); 
    break; 

  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_delayed_eval(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 

  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_delayed_eval(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 

  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      child = rec_delayed_eval(ic->child);
      child = ddd_one_constraint(
        child, d->var_index, ic->lower_bound, ic->upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }

  return(nrec->result = result);
}
  /* rec_delayed_eval() */  







struct red_type	*red_delayed_eval(
  struct red_type	*red_lazy_predicate, 
  int			pi, 
  struct red_type	*red_lazy_space 
) {
  struct red_type	*result; 
  
  if (!(red_lazy_predicate->status & FLAG_RED_LAZY)) 
    result = red_lazy_predicate; 
  else if (red_lazy_space == NORM_FALSE) {
    return(NORM_FALSE); 	
  } 
  else { 
    LAZY_PI = pi; 
    RED_LAZY_SPACE = red_lazy_space; 

/*
    fprintf(RED_OUT, "\ndev_coll %1d\n", ++count_dev_coll); 
    fflush(RED_OUT); 
*/
    collect_value_intervals_in_red(pi, red_lazy_predicate, red_lazy_space); 
    result = rec_delayed_eval(red_lazy_predicate); 
    decollect_value_intervals(); 
  }
  if (red_lazy_space->status & FLAG_RED_LAZY) 
    return(result); 
  else 
    return(red_bop(AND, red_lazy_space, result)); 
}
/* red_delayed_eval() */



struct red_type	*red_xi_pi_constraint_from_events(
  struct ps_exp_type 	*psub, 
  int 			pi
) { 
  int			ixi, xi, vxi, si;
  struct red_type	*result;

  result = NORM_FALSE; 
  vxi = variable_index[TYPE_XTION_INSTANCE][pi][0]; 
  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
    xi = PROCESS[pi].firable_xtion[ixi]; 
    for (si = 0; si < XTION[xi].sync_count; si++) { 
      switch (XTION[xi].sync[si].type) { 
      case -1: // xmit
        if (   (psub->exp_status & FLAG_EVENT_XMIT)
            && (psub->u.atom.var->index == XTION[xi].sync[si].sync_index)
            ) { 
          result = red_bop(OR, result, ddd_atom(vxi, xi, xi)); 
        } 
        break; 
      case 1: // recv
        if (   (psub->exp_status & FLAG_EVENT_RECV)
            && (psub->u.atom.var->index == XTION[xi].sync[si].sync_index)
            ) { 
          result = red_bop(OR, result, ddd_atom(vxi, xi, xi)); 
        } 
        break; 
      default: 
        fprintf(RED_OUT, "\nERROR!\n"); 
        exit(0); 
      } 
    } 
  } 
  return(result); 
} 
  /* red_xi_pi_constraint_from_events() */ 





struct red_type	*red_xi_constraint_from_events(
     struct ps_exp_type	*psub 
) {
  int			pi;
  struct ps_bunit_type	*pbu;
  struct red_type	*result;

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\n----------------------------------------------\n"); 
  fprintf(RED_OUT, "\ncount spec global %1d:\n", 
    local_count_spec_global = ++count_spec_global
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  switch(psub->type) {
  case TYPE_FALSE :
    return(NORM_FALSE); 
  case TYPE_TRUE :
    return(NORM_NO_RESTRICTION); 
  case TYPE_SYNCHRONIZER: 
    if (psub->u.atom.exp_base_proc_index == PS_EXP_GLOBAL_IDENTIFIER) { 
      result = NORM_FALSE; 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      	result = red_bop(OR, result, 
      	  red_xi_pi_constraint_from_events(psub, pi)
      	); 
      }
      return(result); 
    }
    else if (   psub->u.atom.exp_base_proc_index->type == TYPE_CONSTANT
             && psub->u.atom.exp_base_proc_index->u.value >= 1
             && psub->u.atom.exp_base_proc_index->u.value <= PROCESS_COUNT
             ) { 
      return(red_xi_pi_constraint_from_events(psub, 
        psub->u.atom.exp_base_proc_index->u.value
      ) ); 
    } 
    else { 
      fprintf(RED_OUT, "\nERROR in event spec: "); 
      pcform(psub); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    break; 

  case AND :
    result = NORM_NO_RESTRICTION; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      #ifdef RED_DEBUG_EXP_MODE
      fprintf(RED_OUT, "\nBEFORE local_count_spec_global=%1d:%1d\n", 
        local_count_spec_global, newsub->u.bexp.len 
      ); 
      #endif 

      result = red_bop(AND, result, 
        red_xi_constraint_from_events(pbu->subexp)
      ); 

      if (result == NORM_FALSE) { 
	return(NORM_FALSE);
    } }

    return(result);
    break; 

  case OR :
    result = NORM_FALSE; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      #ifdef RED_DEBUG_EXP_MODE
      fprintf(RED_OUT, "\nBEFORE local_count_spec_global=%1d:%1d\n", 
        local_count_spec_global, newsub->u.bexp.len 
      ); 
      #endif 

      result = red_bop(OR, result, 
        red_xi_constraint_from_events(pbu->subexp)
      ); 

      if (result == NORM_NO_RESTRICTION) { 
	return(NORM_NO_RESTRICTION);
    } }

    return(result);
    break; 

  case NOT :
    return(red_complement(
      red_xi_constraint_from_events(psub->u.bexp.blist->subexp)
    ) ); 

  case IMPLY :
    return(red_bop(OR, 
      red_complement(red_xi_constraint_from_events(
        psub->u.bexp.blist->subexp
      ) ), 
      red_xi_constraint_from_events(psub->u.bexp.blist->bnext->subexp)
    ) );

  case TYPE_BDD: 
  case EQ :
  case NEQ :
  case LESS :
  case LEQ :
  case GEQ :
  case GREATER :

  case ARITH_EQ :
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ:

  case ARITH_CONDITIONAL: 
  case FORALL :

  case EXISTS : 

  case RESET: 

  case EXISTS_EVENTUALLY: 
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case EXISTS_ALWAYS:

  case FORALL_UNTIL: 
  case EXISTS_UNTIL: 
  case TYPE_GAME_SIM: 
  case LINEAR_EVENT: 
  case RED: 
  default:
    fprintf(RED_OUT, "\nExp error 6.3: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
}
/* red_xi_constraint_from_events() */ 




struct ps_exp_type	*rec_spec_global(
     struct ps_exp_type	*, 
     int		 
); 


struct ps_fairness_link_type	*rec_spec_global_seq( 
  struct ps_fairness_link_type	*ps_list,  
  int				*count_fl_ptr, 
  int				depth
) { 
  struct ps_fairness_link_type	*fl, *list; 
  struct ps_exp_type		*latom; 

  list = NULL; 
  *count_fl_ptr = 0; 
  for (fl = ps_list; fl; fl = fl->next_ps_fairness_link) {
    list = insert_sorted_flist(
      rec_spec_global(fl->fairness, depth+1), 
      fl->status, 
      list, 
      count_fl_ptr 
    ); 
  } 
  return(list); 
}
/* rec_spec_global_seq() */




// #ifdef RED_DEBUG_EXP_MODE
int	count_spec_global = 0; 
// #endif 

struct ps_exp_type	*rec_spec_global(
     struct ps_exp_type	*psub, 
     int		depth 
) {
  int			local_count_spec_global, i, jj, v, lb, ub;
  struct ps_bunit_type	*pbu, *nbu, dummy_bu;
  struct ps_exp_type	*newsub, *childsub, *childsubf, *childfair, 
			*latom, *ratom, *if_exp, *else_exp;
  struct red_type	*childred, *fairred;

  #ifdef RED_DEBUG_EXP_MODE
  fprintf(RED_OUT, "\n----------------------------------------------\n"); 
  fprintf(RED_OUT, "\ncount spec global %1d:\n", 
    local_count_spec_global = ++count_spec_global
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  newsub = ps_exp_alloc(RED); // Could change to others
  switch(psub->type) {
  case TYPE_FALSE :
    newsub->u.rpred.red = newsub->u.rpred.original_red = NORM_FALSE; 
    return(newsub); 
  case TYPE_TRUE :
    newsub->u.rpred.red = newsub->u.rpred.original_red = NORM_NO_RESTRICTION; 
    return(newsub); 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    newsub->type = RED; 
    newsub->u.rpred.red 
    = newsub->u.rpred.original_red 
    = red_global(psub, FLAG_POLICY_EVALUATION, 0); 
    return(newsub); 
    
  case EQ :
  case NEQ :
  case LESS :
  case LEQ :
  case GEQ :
  case GREATER :
    switch (psub->u.ineq.type & MASK_EXP_TYPE) { 
    case FLAG_EXP_DISCRETE_CONSTANT: 
    case FLAG_EXP_DISCRETE_LINEAR: 
      if (!(psub->var_status & FLAG_EXP_STATE_INSIDE)) { 
        fprintf(RED_OUT, "\n******************************************\n"); 
        fprintf(RED_OUT, "I am not sure if this is going to happen!\n"); 
        fprintf(RED_OUT, "Anyway I make a big noise to let you know that it happened.\n"); 
        fprintf(RED_OUT, "Supposedly, it does not have to happen, right ?\n"); 
        EXP_PSUB = psub;
        newsub->type = RED;
        newsub->u.rpred.red 
        = newsub->u.rpred.original_red 
        = rec_discrete_ineq_linear(psub); 
        return(newsub); 
      }

    case FLAG_EXP_DISCRETE_POLYNOMIAL: 
      fprintf(RED_OUT, 
        "\nError: This should have been preserved as types ARITH_EQ, ARITH_NEQ,\n"
      ); 
      fprintf(RED_OUT, 
        "       ARITH_LEQ, ARITH_GEQ, ARITH_GREATER, ARITH_LESS.\n"
      ); 
      fflush(RED_OUT); 
      bk(0); 
      
      fprintf(RED_OUT, "\nLazy evaluation of BDD diagrams.\n"); 
      break; 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    case FLAG_EXP_DENSE_MIXED: 
    case FLAG_EXP_DENSE_POLYNOMIAL: 
      *newsub = *psub; 
      return(newsub); 
    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_DENSE_CONSTANT: 
    case FLAG_EXP_DENSE_LINEAR: 
      if (GSTATUS[INDEX_SYSTEM_TYPE] & FLAG_SYSTEM_HYBRID) {
        newsub->u.rpred.red 
        = newsub->u.rpred.original_red = red_hybrid_ineq(psub, W_PI); 
      }
      else {
        newsub->type = RED; 
        newsub->u.rpred.red 
        = newsub->u.rpred.original_red 
        = rec_clock_ineq(psub);
      } 
      return(newsub); 
    }
    break; 
  case ARITH_EQ :
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GREATER:
  case ARITH_GEQ:
    if (!(psub->var_status & FLAG_EXP_STATE_INSIDE)) {
      newsub->type = RED; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_discrete_ineq_arith(psub->type, 
        rec_discrete_value(psub->u.arith.lhs_exp), 
        rec_discrete_value(psub->u.arith.rhs_exp)
      ); 
      return(ps_exp_share(newsub)); 
    }
    else switch (psub->u.arith.status & MASK_EXP_TYPE) { 
    case FLAG_EXP_DISCRETE_CONSTANT: 
      EXP_PSUB = psub;
      newsub->type = RED;
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_discrete_ineq(psub, 0);
      return(ps_exp_share(newsub)); 
      break; 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL: 
    case FLAG_EXP_DENSE_POLYNOMIAL: 
      EXP_PSUB = psub;
      newsub->type = RED;
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_delayed_exp_value(psub, 0, RT[DECLARED_GLOBAL_INVARIANCE]);
      return(ps_exp_share(newsub)); 
      break; 

    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    case FLAG_EXP_DENSE_CONSTANT: 
    case FLAG_EXP_DENSE_LINEAR: 
    case FLAG_EXP_DENSE_MIXED: 
      fprintf(RED_OUT, 
        "\nError: This should have been converted to types EQ, NEQ,\n"
      ); 
      fprintf(RED_OUT, 
        "       LEQ, GEQ, GREATER, LESS.\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
      
    } 
    break; 

  case ARITH_CONDITIONAL: 
    childsub = rec_spec_global(
      psub->u.arith_cond.cond, depth+1
    ); 
    if_exp = rec_spec_global(
      psub->u.arith_cond.if_exp, depth+1
    ); 
    else_exp = rec_spec_global(
      psub->u.arith_cond.else_exp, depth+1
    ); 
    
    if (   childsub->type == RED 
        && if_exp->type == RED
        && else_exp->type == RED
        ) { 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_bop(OR, 
          red_bop(AND, childsub->u.rpred.red, if_exp->u.rpred.red), 
          red_bop(AND, red_complement(childsub->u.rpred.red), 
            else_exp->u.rpred.red
        ) ); 
    } 
    else { 
      *newsub = *psub; 
      newsub->u.arith_cond.cond = childsub; 
      newsub->u.arith_cond.if_exp = if_exp; 
      newsub->u.arith_cond.else_exp = else_exp; 
    }
    return(ps_exp_share(newsub)); 
    break; 
  case AND :
    *newsub = *psub; 
    childred = NORM_TRUE;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      #ifdef RED_DEBUG_EXP_MODE
      fprintf(RED_OUT, "\nBEFORE local_count_spec_global=%1d:%1d\n", 
        local_count_spec_global, newsub->u.bexp.len 
      ); 
      #endif 

      childsub = rec_spec_global(pbu->subexp, depth+1); 

      #ifdef RED_DEBUG_EXP_MODE
      fprintf(RED_OUT, "\n AFTER local_count_spec_global=%1d:%1d\n", 
        local_count_spec_global, newsub->u.bexp.len 
      ); 
      fprintf(RED_OUT, "childsub=%x\n", (unsigned int) childsub); 
      pcform(childsub); 
/*
      fprintf(RED_OUT, "PS_EXP_FALSE=%x\n", (unsigned int) PS_EXP_FALSE); 
      pcform(PS_EXP_FALSE); 
*/
      fflush(RED_OUT); 
      #endif 
      
      if (childsub == PS_EXP_FALSE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
	free(newsub);
	return(PS_EXP_FALSE);
      }
      else if (childsub->type == RED) { 
	childred = red_bop(AND, childsub->u.rpred.red, childred);
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, "***************************\ncount spec global = %1d, after conjuncting diagrams, %x!\n", ++count_spec_global, (unsigned int) childred); 
	red_print_graph(childred); 
        #endif 
	continue;
      }
      else {
        insert_sorted_blist_dummy_head(
          AND, 
          childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
    } }

    if (newsub->u.bexp.len) {
      if (childred != NORM_NO_RESTRICTION) { 
        childsub = ps_exp_alloc(RED); 
        childsub->u.rpred.red = childsub->u.rpred.original_red = childred; 
        childsub = ps_exp_share(childsub); 
        insert_sorted_blist_dummy_head(
          AND, 
          childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        return(ps_exp_share(newsub)); 
      } 
      else if (newsub->u.bexp.len == 1) {
      	childsub = newsub->u.bexp.blist->subexp;
      	free(newsub->u.bexp.blist); 
      	free(newsub); 
      	return(childsub); 
      } 
      else {
        newsub->u.bexp.blist = dummy_bu.bnext; 
	return(ps_exp_share(newsub)); 
    } }
    else {
      newsub->type = RED; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = childred;
      return(ps_exp_share(newsub));
    }
    break; 

  case OR :
    *newsub = *psub; 
    childred = NORM_FALSE;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      childsub = rec_spec_global(pbu->subexp, depth+1); 
      if (childsub == PS_EXP_TRUE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
	free(newsub);
	return(PS_EXP_TRUE);
      }
      else if (childsub->type == RED) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, "***************************\ncount spec global = %1d, %x!\n", ++count_spec_global, (unsigned int) childred); 
	red_print_graph(childsub->u.rpred.red); 
	red_print_graph(childred); 
	#endif 
	  
	childred = red_bop(OR, childsub->u.rpred.red, childred);
	continue;
      }
      else  {
        insert_sorted_blist_dummy_head(
          OR, childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
    } }

    if (newsub->u.bexp.len) {
      if (childred != NORM_FALSE) { 
        childsub = ps_exp_alloc(RED); 
        childsub->u.rpred.red = childsub->u.rpred.original_red = childred; 
        childsub = ps_exp_share(childsub); 
        insert_sorted_blist_dummy_head(
          OR, 
          childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        return(ps_exp_share(newsub)); 
      } 
      else if (newsub->u.bexp.len == 1) {
      	childsub = newsub->u.bexp.blist->subexp;
      	free(newsub->u.bexp.blist); 
      	free(newsub); 
      	return(childsub); 
      } 
      else {
        newsub->u.bexp.blist = dummy_bu.bnext; 
	return(ps_exp_share(newsub)); 
    } }
    else {
      newsub->type = RED; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = childred;
      return(ps_exp_share(newsub));
    }
    break; 

  case NOT :
    childsub = rec_spec_global(psub->u.bexp.blist->subexp, depth+1); 
    if (childsub->type == RED) {
      newsub = ps_exp_alloc(RED); 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_complement(childsub->u.rpred.red); 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(add_neg(childsub));

  case IMPLY :
    childsub = rec_spec_global(psub->u.bexp.blist->subexp, depth+1); 
    childsubf = rec_spec_global(psub->u.bexp.blist->bnext->subexp, depth+1);
    if (childsub->type == RED) { 
      childred = red_complement(childsub->u.rpred.red);  
      if (childsubf->type == RED) { 
      	childred = red_bop(OR, childred, childsubf->u.rpred.red); 
        childsub = ps_exp_alloc(RED); 
        childsub->exp_status = (childsub->exp_status & ~FLAG_TCTCTL_SUBFORM) 
        | check_time_convexity(childsub->u.rpred.red); 
        childsub->u.rpred.red 
        = childsub->u.rpred.original_red
        = childred; 
        return(ps_exp_share(childsub));  
      } 
    }
    else 
      childsub = add_neg(childsub); 

    if (childsub == childsubf) {
      free(newsub); 
      return(childsub); 
    }
    *newsub = *psub; 
    newsub->type = OR; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL;     
    insert_sorted_blist_dummy_head(
      OR, 
      childsub, &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    insert_sorted_blist_dummy_head(
      OR, 
      childsubf, &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 

  case FORALL :
    *newsub = *psub; 
    newsub->type = AND; 
    childred = NORM_TRUE;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &jj); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &jj); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) { 
      childsub = rec_spec_global(pbu->subexp, depth+1); 
      if (childsub == PS_EXP_FALSE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
	free(newsub);
        pop_quantified_value_stack(psub); 
	return(PS_EXP_FALSE);
      }
      else if (childsub->type == RED) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, "***************************\ncount spec global = %1d, %x!\n", ++count_spec_global, (unsigned int) childred); 
	red_print_graph(nbu->subexp->u.rpred.red); 
	red_print_graph(childred); 
	#endif 
	  
	childred = red_bop(AND, childsub->u.rpred.red, childred);
	continue;
      }
      else  {
        insert_sorted_blist_dummy_head(
          AND, childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
    } }
    pop_quantified_value_stack(psub); 

    if (newsub->u.bexp.len) {
      if (childred != NORM_NO_RESTRICTION) { 
        childsub = ps_exp_alloc(RED); 
        childsub->u.rpred.red = childsub->u.rpred.original_red = childred; 
        childsub = ps_exp_share(childsub); 
        insert_sorted_blist_dummy_head(
          AND, childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        return(ps_exp_share(newsub)); 
      } 
      else if (newsub->u.bexp.len == 1) {
      	childsub = newsub->u.bexp.blist->subexp;
      	free(newsub->u.bexp.blist); 
      	free(newsub); 
      	return(childsub); 
      } 
      else {
        newsub->u.bexp.blist = dummy_bu.bnext; 
	return(ps_exp_share(newsub)); 
    } }
    else {
      newsub->type = RED; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = childred;
      return(ps_exp_share(newsub));
    }
    break; 

  case EXISTS : 
    *newsub = *psub; 
    newsub->type = OR; 
    childred = NORM_FALSE;
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    lb = get_value(psub->u.qexp.lb_exp, -1, &jj); 
    ub = get_value(psub->u.qexp.ub_exp, -1, &jj); 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = lb; 
         psub->u.qexp.value <= ub; 
         psub->u.qexp.value++
         ) { 
      childsub = rec_spec_global(pbu->subexp, depth+1); 
      if (childsub == PS_EXP_TRUE) { 
      	ps_exp_free_list(dummy_bu.bnext); 
	free(newsub);
        pop_quantified_value_stack(psub); 
	return(PS_EXP_TRUE);
      }
      else if (childsub->type == RED) { 
        #ifdef RED_DEBUG_EXP_MODE
	fprintf(RED_OUT, "***************************\ncount spec global = %1d, %x!\n", ++count_spec_global, (unsigned int) childred); 
	red_print_graph(nbu->subexp->u.rpred.red); 
	red_print_graph(childred); 
	#endif 
	  
	childred = red_bop(OR, childsub->u.rpred.red, childred);
	continue;
      }
      else {
        insert_sorted_blist_dummy_head(
          OR, childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
    } }
    pop_quantified_value_stack(psub); 

    if (newsub->u.bexp.len) {
      if (childred != NORM_FALSE) { 
        childsub = ps_exp_alloc(RED); 
        childsub->u.rpred.red = childsub->u.rpred.original_red = childred; 
        childsub = ps_exp_share(childsub); 
        insert_sorted_blist_dummy_head(
          OR, childsub, 
          &dummy_bu, &(newsub->u.bexp.len) 
        ); 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        return(ps_exp_share(newsub)); 
      } 
      else if (newsub->u.bexp.len == 1) {
      	childsub = newsub->u.bexp.blist->subexp;
      	free(newsub->u.bexp.blist); 
      	free(newsub); 
      	return(childsub); 
      } 
      else {
        newsub->u.bexp.blist = dummy_bu.bnext; 
	return(ps_exp_share(newsub)); 
    } }
    else {
      newsub->type = RED; 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = childred;
      return(ps_exp_share(newsub));
    }
    break; 

  case RESET: 
    *newsub = *psub; 
    newsub->u.reset.child = rec_spec_global(psub->u.reset.child, depth+1); 
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_EVENTUALLY: 
/*
    fprintf(RED_OUT, "\nBug: Exists_eventually modal operators should already have been eliminated.\n"); 
    bk(0);
    break; 
*/
  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY : 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case EXISTS_ALWAYS:

  case FORALL_UNTIL: 
  case EXISTS_UNTIL: 
    *newsub = *psub; 
      
    childsub = rec_spec_global(psub->u.mexp.dest_child, depth+1); 
    childsubf = rec_spec_global(psub->u.mexp.path_child, depth+1); 
    newsub->u.mexp.time_lb = psub->u.mexp.time_lb; 
    newsub->u.mexp.time_ub = psub->u.mexp.time_ub; 

    newsub->u.mexp.dest_child = childsub; 
    newsub->u.mexp.path_child = childsubf;     
    newsub->u.mexp.event_restriction = psub->u.mexp.event_restriction; 
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.red_xi_restriction 
      = psub->u.mexp.red_xi_restriction // this is to protect from exp sharing. 
      = red_xi_constraint_from_events(newsub->u.mexp.event_restriction); 
    else 
      newsub->u.mexp.red_xi_restriction 
      = psub->u.mexp.red_xi_restriction // this is to protect from exp sharing. 
      = NORM_NO_RESTRICTION; 

    newsub->u.mexp.time_restriction 
    = rec_spec_global(psub->u.mexp.time_restriction, depth+1);  
    newsub->u.mexp.red_time_restriction 
    = newsub->u.mexp.time_restriction->u.rpred.red; 
    
    newsub->u.mexp.strong_fairness_list = rec_spec_global_seq(
      psub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count), 
      depth
    ); 
    newsub->u.mexp.weak_fairness_list = rec_spec_global_seq(
      psub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count), 
      depth
    ); 
    return(ps_exp_share(newsub)); 
    break; 

  case TYPE_GAME_SIM: 
    *newsub = *psub; 
      
    newsub->u.mexp.time_lb = psub->u.mexp.time_lb; 
    newsub->u.mexp.time_ub = psub->u.mexp.time_ub; 

    newsub->u.mexp.dest_child = NULL; 
    newsub->u.mexp.path_child = NULL;     
    newsub->u.mexp.time_restriction = NULL; 
    
    newsub->u.mexp.red_time_restriction = NULL; 
    newsub->u.mexp.strong_fairness_list = rec_spec_global_seq(
      psub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count), 
      depth
    ); 
    newsub->u.mexp.weak_fairness_list = rec_spec_global_seq(
      psub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count), 
      depth
    ); 
    return(ps_exp_share(newsub)); 
    break; 

  case LINEAR_EVENT: 
    *newsub = *psub; 
    newsub->u.eexp.precond_exp  
    = rec_spec_global(psub->u.eexp.precond_exp, depth+1); 
    newsub->u.eexp.postcond_exp  
    = rec_spec_global(psub->u.eexp.postcond_exp, depth+1); 
    newsub = ps_exp_share(newsub); 

    if (psub->u.eexp.event_exp) { 
      psub->u.eexp.red_game_sync_bulk_from_event_exp 
      = psub->u.eexp.red_sync_bulk_from_event_exp 
      = newsub->u.eexp.red_game_sync_bulk_from_event_exp 
      = newsub->u.eexp.red_sync_bulk_from_event_exp 
      = red_xi_constraint_from_events(psub->u.eexp.event_exp); 
    } 
    if (newsub->u.eexp.precond_exp->type == RED) 
      newsub->u.eexp.red_precond = newsub->u.eexp.precond_exp->u.rpred.red;
    else 
      newsub->u.eexp.red_precond = NULL;  
    if (newsub->u.eexp.postcond_exp->type == RED) 
      newsub->u.eexp.red_postcond = newsub->u.eexp.postcond_exp->u.rpred.red;
    else 
      newsub->u.eexp.red_postcond = NULL;  
    #ifdef RED_DEBUG_EXP_MODE 
    fprintf(RED_OUT, "After spec_global either EX EVENT OR LINEAR EVENT:\n"); 
    pcform(newsub); 
    fprintf(RED_OUT, "\nWith red events:\n"); 
    red_print_graph(newsub->u.eexp.red_events); 
    #endif 
    
    return(newsub); 
    break; 
  
  case RED: 
    return(psub); 

  default:
    fprintf(RED_OUT, "\nExp error 6.1: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
}
/* rec_spec_global() */ 



struct ps_exp_type	*spec_global(
  struct ps_exp_type	*psub, 
  int			pi, 
  int			flag_delayed_evaluation, 
  int			depth  
) {
  W_PI = pi; 
  FLAG_POLICY_EVALUATION = flag_delayed_evaluation;  

  psub = rec_spec_global(psub, depth); 
  return(psub);  
}
  /* spec_global() */ 
  
  










