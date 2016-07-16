/**************************************************************
 *
 *  What should we do about red_effect ? 
 *  What should we do about actions with possibly LHS recursion ? 
 *   1. The discretes have been taken care of with the current implementation. 
 *      There is no need to disrupt it. 
 *      Besides, the proposal of using lazy expression together with 
 *      LHS_VI (actually LHS_PI) to store lhs variable index is actually 
 *      no simpler than the current implementation. 
 *   2. The clocks. 
 *      Well, it has been working correctly for assignments 
 *      of the form: x=y+c; whether y is x or not. 
 */
#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h> 
*/
#include "redbasics.h"
#include "redbasics.e" 

#include "vindex.e"

#include "redbop.h"
#include "redbop.e"

#include "zone.h"
#include "zone.e"

#include "redparse.h" 
#include "redparse.e" 

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "hybrid.e" 

#include "redcplugins.e" 


#define	FLAG_ACTION_ABSTRACT	TYPE_TRUE
#define FLAG_ACTION_EXACT	TYPE_FALSE 

#define	FLAG_ACTION_DEC		TYPE_TRUE 
#define FLAG_ACTION_INC		TYPE_FALSE 

struct statement_type	ACTION_BUFFER, 
			*ACTION_SAVE_RETMODE, 
			*ACTION_RESUME_RETMODE; 

int			count_act_debug1 = 0; 

int			VI_ACT, LB_ACT, UB_ACT, RCOEFF_ACT, ROFFSET_ACT, 
			AW; 
int			FLAG_STATEMENT_POLARITY, 
			FLAG_STATEMENT_PI; 

struct a23tree_type	*action_tree;


/*****************************************************************
 * Common basic routines 
 */ 
int	check_dynamic_complex_exp(e)
     struct ps_exp_type	*e; 
{
  int				i, comp;
  struct ps_bunit_type		*pbu1, *pbu2;
//  struct parse_indirect_type	*pt1, *pt2;
  struct ps_fairness_link_type	*f1, *f2;
  struct name_link_type		*nl1, *nl2; 

  if (!e) 
    return(TYPE_FALSE); 
  else switch(e->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_MACRO_CONSTANT:
  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
    return (TYPE_FALSE);  
    
  case TYPE_INLINE_ARGUMENT: 
    return (TYPE_TRUE);  

  case TYPE_QSYNC_HOLDER: 
    return (TYPE_FALSE); 	

  case TYPE_SYNCHRONIZER: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
    return(TYPE_FALSE); 
      
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER: 
    if (/*
           e->u.atom.indirect_count 
        || */
           (  e->u.atom.exp_base_proc_index->var_status 
            & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
            )
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  
  case TYPE_INTERVAL:
    if (  (  e->u.interval.lbound_exp->var_status 
           | e->u.interval.rbound_exp->var_status
           )
        & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE);  

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
    if (   (  e->u.arith.lhs_exp->var_status 
            & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
            )
        || (  e->u.arith.rhs_exp->var_status 
            & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
        )   ) {
      return(TYPE_TRUE);   	
    } 
    else 
      return(
        check_dynamic_complex_exp(e->u.arith.lhs_exp)
      | check_dynamic_complex_exp(e->u.arith.rhs_exp)
      ); 

  case ARITH_CONDITIONAL: 
    return(
      check_dynamic_complex_exp(e->u.arith_cond.cond)
    | check_dynamic_complex_exp(e->u.arith_cond.if_exp)
    | check_dynamic_complex_exp(e->u.arith_cond.else_exp)
    ); 

  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    if (e->u.ineq.term_count > 1) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 

  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    fprintf(RED_OUT, "ERROR\n"); 
    exit(0); 
    break; 
    
  case TYPE_INLINE_CALL: 
    return(check_dynamic_complex_exp(e->u.inline_call.instantiated_exp)); 
    break; 

  case RED:
    return(TYPE_TRUE);

  case AND :
  case OR :
  case NOT :
  case IMPLY : 

  case FORALL:
  case EXISTS:

  case RESET:

  case PROJECT:
  case PROJECT_TYPE:
  case PROJECT_PEER:
  case PROJECT_VAR_SIM:
  case PROJECT_CLOCK_SIM:

  case PROJECT_TIME:
  case PROJECT_QSYNC: 
  case PROJECT_CLOCK_LOWER_EXTEND:
  case PROJECT_CLOCK_UPPER_EXTEND:
  case PROJECT_LOCAL: 

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

  case LINEAR_EVENT: 
  case FORALL_EVENT: 
  case EXISTS_EVENT:

  default: 
    fprintf(RED_OUT, "\nUnexpected expression type %1d in check_dynamic_complex_exp()\ne:", 
      e->type
    ); 
    pcform(e); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* check_dynamic_complex_exp() */ 




struct red_type	*rec_effect_simple(d) 
     struct red_type	*d; 
{
  int				b, lb, ub, ci; 
  struct red_type		*new_child, *result; 
  struct crd_child_type		*bc; 
  struct ddd_child_type		*ic; 
  struct cache7_hash_entry_type	*ce; 
    
  if (d == NORM_FALSE) 
    return(d); 

  ce = cache7_check_result_key(
    OP_EFFECT_SIMPLE, d, 
    (struct hrd_exp_type *) VI_ACT, 
    RCOEFF_ACT, 
    ROFFSET_ACT, 
    NULL, 
    LB_ACT, 
    UB_ACT
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  if (d->var_index == VI_ACT) { 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(d->u.ddd.arc[ci]); 

      lb = RCOEFF_ACT * ic->lower_bound + ROFFSET_ACT;
      ub = RCOEFF_ACT * ic->upper_bound + ROFFSET_ACT;
      if (lb > ub) {
	b = lb; lb = ub; ub = b;
      }
      if (lb > VAR[VI_ACT].U.DISC.UB || ub < VAR[VI_ACT].U.DISC.LB)
        continue;

      if (lb < VAR[VI_ACT].U.DISC.LB)
	lb = VAR[VI_ACT].U.DISC.LB;
  
      if (ub > VAR[VI_ACT].U.DISC.UB) 
	ub = VAR[VI_ACT].U.DISC.UB; 

      new_child = ddd_one_constraint(ic->child, VI_ACT, lb, ub); 
      result = red_bop(OR, result, new_child); 
    }
  } 
  else if (d->var_index > VI_ACT || d == NORM_NO_RESTRICTION) 
    result = ddd_one_constraint(d, VI_ACT, LB_ACT, UB_ACT); 
  else { 
    switch (VAR[d->var_index].TYPE) {
    case TYPE_CRD: 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	bc = &(d->u.crd.arc[ci]); 
	new_child = rec_effect_simple(bc->child); 
	result = red_bop(OR, result, crd_one_constraint(new_child, d->var_index, bc->upper_bound)); 
      }
      break;

    case TYPE_FLOAT: 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	new_child = rec_effect_simple(d->u.fdd.arc[ci].child); 
	result = red_bop(OR, result,
	  fdd_one_constraint(new_child, d->var_index, 
	    d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	) ); 
      }
      break; 
    case TYPE_DOUBLE: 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	new_child = rec_effect_simple(d->u.dfdd.arc[ci].child); 
	result = red_bop(OR, result,
	  dfdd_one_constraint(new_child, d->var_index, 
	    d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	) ); 
      }
      break; 
    default: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]); 
	new_child = rec_effect_simple(ic->child); 
	result = red_bop(OR, result,
			 ddd_one_constraint
			 (new_child, d->var_index, ic->lower_bound, ic->upper_bound)
			 ); 
      }
      break; 
    }
  }
  return(ce->result = result); 
}
  /* rec_effect_simple() */ 



struct red_type	*red_effect_simple(d, lvi, rvi, rcoeff, roffset) 
     struct red_type	*d; 
     int		lvi, rvi, rcoeff, roffset; 
{
  int			lb, ub, v; 
  struct red_type	*result;

  if (lvi == rvi) { 
    VI_ACT = lvi;
    RCOEFF_ACT = rcoeff; 
    ROFFSET_ACT = roffset; 
    LB_ACT = rcoeff*VAR[rvi].U.DISC.LB + roffset;
    UB_ACT = rcoeff*VAR[rvi].U.DISC.UB + roffset; 
    if (LB_ACT > UB_ACT) { 
      v = LB_ACT; LB_ACT = UB_ACT; UB_ACT = v; 
    }
    if (LB_ACT < VAR[lvi].U.DISC.LB)
      LB_ACT = VAR[lvi].U.DISC.LB; 
    
    if (UB_ACT > VAR[lvi].U.DISC.UB) 
      UB_ACT = VAR[lvi].U.DISC.UB; 
    
    result = rec_effect_simple(d); 
  }
  else { 
    lb = VAR[lvi].U.DISC.LB - roffset; 
    if (lb % rcoeff) 
      lb = lb /rcoeff - 1; 
    else 
      lb = lb/rcoeff; 
    
    ub = VAR[lvi].U.DISC.UB - roffset; 
    if (ub % rcoeff) 
      ub = ub / rcoeff + 1; 
    else 
      ub = ub /rcoeff;

    if (lb > ub) {
      v = lb; lb = ub; ub = v; 
    } 

    if (lb < VAR[rvi].U.DISC.LB) 
      lb = VAR[rvi].U.DISC.LB; 
    
    if (ub > VAR[rvi].U.DISC.UB) 
      ub = VAR[rvi].U.DISC.UB;

    result = NORM_FALSE;   
    for (v = lb; v <= ub; v++) {
      result = red_bop(OR, result, ddd_one_constraint(
        ddd_atom(lvi, rcoeff*v+roffset, rcoeff*v+roffset), 
        rvi, v, v
      ) ); 
    }
    result = red_bop(AND, d, result); 
  }
  return(result); 
}
/* red_effect_simple() */ 




int	MIC_LCI, MIC_RCI, MIC_OFFSET_LB, MIC_OFFSET_UB; 




#define PI_OPPONENT	-1





/********************************************
*  It is assume that the root variable is VALUE. 
*  The routine gets rid of variable VALUE and 
*  copies its value to lvi. 
*/
struct red_type	*red_effect(d, lvi)
     struct red_type	*d; 
     int		lvi; 
{
  struct red_type	*result, *conj;
  int			ci, lb, ub;

  result = NORM_FALSE; 
  d = red_variable_eliminate(d, lvi); 
  for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
    conj = d->u.ddd.arc[ci].child; 
    if (d->u.ddd.arc[ci].lower_bound < VAR[lvi].U.DISC.LB) 
      lb = VAR[lvi].U.DISC.LB; 
    else 
      lb = d->u.ddd.arc[ci].lower_bound; 
    if (d->u.ddd.arc[ci].upper_bound > VAR[lvi].U.DISC.UB) 
      ub = VAR[lvi].U.DISC.UB; 
    else 
      ub = d->u.ddd.arc[ci].upper_bound; 

    if (lb <= ub)
      result = red_bop(OR, result, ddd_one_constraint(conj, lvi, lb, ub)); 
  }
  return(result); 
}
/* red_effect() */ 






int	_SP_VI; 

struct red_type	*rec_clear_procedure_stack_frame(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, j;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_VARIABLE_ELIMINATE, d, 
    (struct red_type *) (_SP_VI + VARIABLE_COUNT * VARIABLE_COUNT) 
  ); 
  if (ce->result) { 
    if (   ce->result->var_index >= VARIABLE_COUNT 
        || ce->result->var_index < 0
        ) {
      fprintf(RED_OUT, "A bad cached variable index %1d\n", 
              ce->result->var_index
              ); 
      bk(0); 
    }
    return(ce->result); 
  } 

  if (d->var_index > _SP_VI) { 
    result = red_multi_variables_eliminate(d, 
      variable_index[TYPE_DISCRETE]
        [VAR[_SP_VI].PROC_INDEX]
        [STACK_START_OFFSET+HEIGHT_STACK_FRAME], 
      variable_index[TYPE_DISCRETE]
        [VAR[_SP_VI].PROC_INDEX]
        [STACK_START_OFFSET+DEPTH_CALL*HEIGHT_STACK_FRAME-2]
    ); 
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_clear_procedure_stack_frame(d->u.bdd.zero_child), 
      rec_clear_procedure_stack_frame(d->u.bdd.one_child)
    );
    break; 

  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      conj = rec_clear_procedure_stack_frame(bc->child);
      bchild_stack_push(conj, bc->upper_bound);
    }
    result = crd_new(d->var_index);
    break;
  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      conj = rec_clear_procedure_stack_frame(hc->child);  
      hchild_stack_push(conj, hc->ub_numerator, hc->ub_denominator);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, 
      "\nWe do not expect lazy node in rec_clear_procedure_stack_frame()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_clear_procedure_stack_frame(d->u.fdd.arc[ci].child); 
      fchild_stack_push(conj, 
      	d->u.fdd.arc[ci].lower_bound,
      	d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_clear_procedure_stack_frame(d->u.dfdd.arc[ci].child); 
      dfchild_stack_push(conj, 
      	d->u.dfdd.arc[ci].lower_bound,
      	d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 

  default:
    if (d->var_index == _SP_VI) { 
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      	for (j = d->u.ddd.arc[ci].lower_bound; 
      	     j <= d->u.ddd.arc[ci].upper_bound; 
      	     j++
      	     ) {
          conj = red_multi_variables_eliminate(d->u.ddd.arc[ci].child, 
            variable_index[TYPE_DISCRETE]
              [VAR[_SP_VI].PROC_INDEX]
              [STACK_START_OFFSET+j*HEIGHT_STACK_FRAME], 
            variable_index[TYPE_DISCRETE]
              [VAR[_SP_VI].PROC_INDEX]
              [STACK_START_OFFSET+DEPTH_CALL*HEIGHT_STACK_FRAME-1]
          ); 
	  ichild_stack_push(conj, j, j); 
      } }
      result = ddd_new(d->var_index);
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]);
	conj = rec_clear_procedure_stack_frame(ic->child); 
	ichild_stack_push(conj,
      	  ic->lower_bound,
      	  ic->upper_bound
      	);
      }
      result = ddd_new(d->var_index);
    }
    break;
  }
/*
  fprintf(RED_OUT, "var_elm(%1d, %x), new result=%x\n", XVI_INC, d, result); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
/* rec_clear_procedure_stack_frame() */



struct red_type	*red_clear_procedure_stack_frame(d, sp_vi)
     struct red_type	*d;
     int		sp_vi;
{
  struct red_type	*result;

  _SP_VI = sp_vi; 

  result = rec_clear_procedure_stack_frame(d);

  return(result);
}
/* red_clear_procedure_stack_frame() */





struct red_type	*red_discrete_assign_bck(d, vi, lb, ub)
	struct red_type	*d; 
	int		vi, lb, ub; 
{ 
  d = ddd_one_constraint(d, vi, lb, ub); 
  d = red_variable_eliminate(d, vi); 
  return(d); 
} 
  /* red_discrete_assign_bck() */ 
  
  



/**************************************************************
 *  
 *  The following procedures are for the setup of action parameter values. 
 */

void	get_action_clock_offset_range(act, pi, lbptr, ubptr) 
	struct statement_type	*act; 
	int			pi, *lbptr, *ubptr; 
{ 
  switch (act->st_status & MASK_ACTION_OFFSET_TYPE) { 
  case FLAG_ACTION_OFFSET_CONSTANT: 
    *lbptr = (int) act->u.act.offset_numerator; 
    *ubptr = 2 * (*lbptr); 
    *lbptr = -2 * (*lbptr); 
    break; 
  case FLAG_ACTION_OFFSET_PROCESS_CONSTANT: 
    *lbptr = act->u.act.offset_numerator[pi] / act->u.act.offset_denominator[pi]; 
    *ubptr = 2 * (*lbptr); 
    *lbptr = -2 * (*lbptr); 
    break; 
  case FLAG_ACTION_OFFSET_INTERVAL_CONSTANT: 
    *lbptr = ((int) act->u.act.offset_numerator) 
           / ((int) act->u.act.offset_denominator); 
    if (act->u.act.offset->u.interval.status & INTERVAL_LEFT_UNBOUNDED) { 
      *lbptr = CLOCK_NEG_INFINITY; 
    }
    else if (act->u.act.offset->u.interval.status & INTERVAL_LEFT_OPEN) { 
      *lbptr = -2 * (*lbptr) - 1; 
    } 
    else {
      *lbptr = -2 * (*lbptr); 
    }
    *ubptr = ((int) act->u.act.single_coeff_numerator) 
           / ((int) act->u.act.single_coeff_denominator); 
    if (act->u.act.offset->u.interval.status & INTERVAL_RIGHT_UNBOUNDED) { 
      *ubptr = CLOCK_POS_INFINITY; 
    }
    else if (act->u.act.offset->u.interval.status & INTERVAL_RIGHT_OPEN) { 
      *ubptr = 2 * (*ubptr) - 1; 
    } 
    else {
      *ubptr = 2 * (*ubptr); 
    }
    break;  
  }
}
  /* get_action_clock_offset_range() */ 
  
  



void	discrete_lhs_rhs_setup(
  struct red_type	*red_lazy_space, 
  struct statement_type	*act, 
  int			pi, 

  int			*lvi_ptr, // if RT[lopd] is returned NULL, 
  int                   lopdi,    // *lpi_ptr is the static lhs process index. 

  int			*offset_lb_ptr, // if RT[offset] is returned NULL,
  int			*offset_ub_ptr, // *offset_lb_ptr and *offset_ub_ptr
  float			*offset_flb_ptr, // if RT[offset] is returned NULL,
  float			*offset_fub_ptr, // *offset_lb_ptr and *offset_ub_ptr
  int			offseti        // are the static range of offset.
) {
  int			flag_interval_list_ready; 
  struct ps_exp_type	*lhs; 

  flag_interval_list_ready = TYPE_FALSE; 
  lhs = act->u.act.lhs;
  if (lhs == NULL) { 
    RT[lopdi] = NULL; 
    *lvi_ptr = -1; 
  }
  else if (lhs->type == TYPE_REFERENCE) { 
// We need to add in a new flag for indirection inside to 
// to detect the special case here.  
/* 
    if (   (lhs->u.exp->status & 
            (FLAG_DISCRETE | FLAG_POINTER | FLAG_DENSE | FALG_CLOCK)
            )
        || lhs->u.exp->type == TYPE_REFERENCE 
        ) {
*/
      if (!flag_interval_list_ready) { 
        flag_interval_list_ready = TYPE_TRUE; 
        collect_value_intervals(pi, act->u.act.lhs, 
          act->u.act.rhs_exp, red_lazy_space
        ); 
      } 
      RT[lopdi] = rec_delayed_operand_indirection(act->u.act.lhs); 
/*
    }
    else { 
      if (
    } 
*/
  } 
  else if (   (lhs->u.atom.exp_base_proc_index->type == TYPE_CONSTANT) 
//           && lhs->u.atom.indirect_count == 0 
           ) { 
    RT[lopdi] = NULL; 
    *lvi_ptr = lhs->u.atom.exp_base_proc_index->u.value;
    *lvi_ptr = variable_index[lhs->type][*lvi_ptr]
      [VAR[lhs->u.atom.var_index].OFFSET]; 
  } 
  else if (   (!(  lhs->u.atom.exp_base_proc_index->var_status  
                 & (FLAG_POINTER | FLAG_DISCRETE | FLAG_SYNCHRONIZER | FLAG_QUANTIFIED_SYNC)
               ) ) 
//           && lhs->u.atom.indirect_count == 0 
           ) { 
    int	flag; 
    
    RT[lopdi] = NULL; 
    *lvi_ptr = get_value(
      lhs->u.atom.exp_base_proc_index, pi, &flag
    ); 
    *lvi_ptr = variable_index[lhs->type][*lvi_ptr]
      [VAR[lhs->u.atom.var_index].OFFSET]; 
  } 
  else if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
           == FLAG_ACTION_LAZY_EVAL
           ) {
    RT[lopdi] = red_operand_indirection(
      act->u.act.lhs, pi
    ); 
    RT[lopdi] = red_bop(AND, RT[lopdi], red_lazy_space); 
  } 
  else { 
    if (!flag_interval_list_ready) { 
      flag_interval_list_ready = TYPE_TRUE; 
      collect_value_intervals(pi, act->u.act.lhs, 
        act->u.act.rhs_exp, red_lazy_space
      ); 
    } 
    RT[lopdi] = rec_delayed_operand_indirection(act->u.act.lhs); 
  }
  
  if (act->u.act.rhs_exp->type == TYPE_CONSTANT) { 
    *offset_lb_ptr = *offset_ub_ptr = act->u.act.rhs_exp->u.value; 
    *offset_flb_ptr = 0.0; 
    *offset_fub_ptr = -1.0; 
    RT[offseti] = NULL; 
  } 
  else if (act->u.act.rhs_exp->type == TYPE_FLOAT_CONSTANT) { 
    *offset_lb_ptr = 0; 
    *offset_ub_ptr = -1; 
    *offset_flb_ptr = *offset_fub_ptr = act->u.act.rhs_exp->u.float_value;; 
    RT[offseti] = NULL; 
  } 
  else if (   act->u.act.rhs_exp->type == TYPE_INTERVAL
           && act->u.act.rhs_exp->u.interval.lbound_exp->type == TYPE_CONSTANT 
           && act->u.act.rhs_exp->u.interval.rbound_exp->type == TYPE_CONSTANT 
           ) { 
    *offset_lb_ptr = act->u.act.rhs_exp->u.interval.lbound_exp->u.value;
    *offset_ub_ptr = act->u.act.rhs_exp->u.interval.rbound_exp->u.value;
    *offset_flb_ptr = 0.0; 
    *offset_fub_ptr = -1.0; 
    RT[offseti] = NULL; 
  } 
  else if (!(  act->u.act.rhs_exp->var_status  
             & (FLAG_POINTER | FLAG_DISCRETE | FLAG_SYNCHRONIZER | FLAG_QUANTIFIED_SYNC)
           ) ) {
    float	flb, fub; 
    
    switch (get_integer_range(act->u.act.rhs_exp, 
              pi, offset_lb_ptr, offset_ub_ptr, offset_flb_ptr, offset_fub_ptr
            ) ) { 
    case FLAG_SPECIFIC_VALUE: 
      *offset_flb_ptr = 0.0; 
      *offset_fub_ptr = -1.0; 
      break; 
    case FLAG_SPECIFIC_FLOAT_VALUE: 
      *offset_lb_ptr = 0; 
      *offset_ub_ptr = -1; 
      break; 
    case FLAG_UNSPECIFIC_VALUE: 
    default: 
      fprintf(RED_OUT, "\nERROR: ambiguous value.\n"); 
      bk(0); 
      break; 
    } 
    RT[offseti] = NULL; 
  }
  else {
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[offseti] = red_discrete_value(pi, act->u.act.rhs_exp); 
      RT[offseti] = red_bop(AND, RT[offseti], red_lazy_space); 
    }
    else {
      if (!flag_interval_list_ready) { 
        flag_interval_list_ready = TYPE_TRUE;       
        collect_value_intervals(pi, act->u.act.lhs, 
          act->u.act.rhs_exp, red_lazy_space
        ); 
      } 
      RT[offseti] = rec_delayed_exp_value(act->u.act.rhs_exp); 
    }
  }
  if (flag_interval_list_ready) { 
    decollect_value_intervals(); 
  } 
}  
  /* discrete_lhs_rhs_setup() */ 






// int count_clock_assign_setup = 0; 

  
void	clock_assign_setup(
  struct red_type	*red_lazy_space, 
  struct statement_type	*act, 
  int			pi, 

  struct ps_exp_type	**lvar_ptr, 
  int			*lpi_ptr, // if RT[lopd] is returned NULL, 
  int                   lopdi,     // *lpi_ptr is the static lhs process index. 

  struct ps_exp_type	**rvar_ptr, // if *rvar_ptr is NULL, 
                                    // then there is no RHS variable.
  int			*rpi_ptr, // if RT[ropd] is returned NULL,
  int			ropdi,     // *rpi_ptr is the static rhs process index. 

  int			*offset_lb_ptr, // if RT[offset] is returned NULL,
  int			*offset_ub_ptr, // *offset_lb_ptr and *offset_ub_ptr
  int			offseti          // are the static range of offset.
) {
  int	flag_interval_list_ready; 

/*
  fprintf(RED_OUT, "\nclock assign setup %1d\n", ++count_clock_assign_setup); 
  fflush(RED_OUT); 
  if (count_clock_assign_setup == 13) { 
    fprintf(RED_OUT, "caught!\n"); 
    fflush(RED_OUT); 	
  } 
*/
  flag_interval_list_ready = TYPE_FALSE; 
  *lvar_ptr = act->u.act.term[0].operand;
  if (   ((*lvar_ptr)->u.atom.exp_base_proc_index->type == TYPE_CONSTANT) 
//      && (*lvar_ptr)->u.atom.indirect_count == 0 
      ) {
    RT[lopdi] = NULL; 
    *lpi_ptr = (*lvar_ptr)->u.atom.exp_base_proc_index->u.value;
  } 
  else if (   (*lvar_ptr)->u.atom.exp_base_proc_index->type 
              == TYPE_LOCAL_IDENTIFIER
//           && (*lvar_ptr)->u.atom.indirect_count == 0 
           ) {
    RT[lopdi] = NULL; 
    *lpi_ptr = pi;
  } 
  else if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
           == FLAG_ACTION_LAZY_EVAL
           ) {
    RT[lopdi] = red_operand_indirection(
      act->u.act.term[0].operand, pi 
    );
  }
  else { 
    if (!flag_interval_list_ready) { 
      flag_interval_list_ready = TYPE_TRUE; 
      collect_value_intervals(pi, act->u.act.term[0].operand, 
        act->u.act.term[1].operand, red_lazy_space
      ); 
    } 
    RT[lopdi] = rec_delayed_operand_indirection(
      act->u.act.term[0].operand  
    );
  } 
 
  if (act->u.act.term_count == 1) { 
    *rvar_ptr = NULL; 
    RT[ropdi] = NULL; 	
  } 
  else { 
    *rvar_ptr = act->u.act.term[1].operand;
    if (   ((*rvar_ptr)->u.atom.exp_base_proc_index->type == TYPE_CONSTANT) 
//        && (*rvar_ptr)->u.atom.indirect_count == 0 
        ) {
      RT[ropdi] = NULL;
      *rpi_ptr = (*rvar_ptr)->u.atom.exp_base_proc_index->u.value;
    } 
    else if (   (*rvar_ptr)->u.atom.exp_base_proc_index->type 
                 == TYPE_LOCAL_IDENTIFIER 
//             && (*rvar_ptr)->u.atom.indirect_count == 0 
             ) {
      RT[ropdi] = NULL;
      *rpi_ptr = pi;
    } 
    else if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
             == FLAG_ACTION_LAZY_EVAL
             ) {
      RT[ropdi] = red_operand_indirection(
        act->u.act.term[1].operand, pi 
      ); 
    }
    else {
      if (!flag_interval_list_ready) { 
        flag_interval_list_ready = TYPE_TRUE; 
        collect_value_intervals(pi, act->u.act.term[0].operand, 
          act->u.act.term[1].operand, red_lazy_space
        ); 
      } 
      RT[ropdi] = rec_delayed_operand_indirection(
        act->u.act.term[1].operand 
      ); 
    }
  }

  if (act->u.act.offset->type == TYPE_CONSTANT) { 
    *offset_lb_ptr = *offset_ub_ptr = 2*act->u.act.offset->u.value; 
    RT[offseti] = NULL; 
  } 
  else if (   act->u.act.offset->type == TYPE_INTERVAL
           && (  act->u.act.offset->u.interval.lbound_exp->exp_status 
               & FLAG_CONSTANT
               )
           && (  act->u.act.offset->u.interval.rbound_exp->exp_status 
               & FLAG_CONSTANT
               )
           )  { 
    get_action_clock_offset_range(act, pi, offset_lb_ptr, offset_ub_ptr); 
    RT[offseti] = NULL; 
  }  	
  else {
    if (!flag_interval_list_ready) { 
      flag_interval_list_ready = TYPE_TRUE; 
      collect_value_intervals(pi, act->u.act.term[0].operand, 
        act->u.act.term[1].operand, red_lazy_space
      ); 
    } 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[offseti] = red_discrete_value(pi, act->u.act.offset); 
    }
    else 
      RT[offseti] = rec_delayed_exp_value(act->u.act.offset); 
  }
  if (flag_interval_list_ready) { 
    decollect_value_intervals(); 
  } 
}  
  /* clock_assign_setup() */ 






/*****************************************************************
 * Actions for forward executions
 */



inline struct red_type	*red_discrete_assign_bottom_analysis_fwd( 
  struct red_type	*d, 
  int			lvi, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float			ofub 
) { 
  d = red_variable_eliminate(d, lvi); 
  switch (VAR[lvi].TYPE) { 
  case TYPE_FLOAT: 
    if (olb > oub) { 
      if (oflb < VAR[lvi].U.FLT.LB || ofub > VAR[lvi].U.FLT.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%.4f,%.4f] to %s.\n", 
          oflb, ofub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(fdd_one_constraint(d, lvi, oflb, ofub)); 
    } 
    else if (oflb > ofub) {  
      if (olb < VAR[lvi].U.FLT.LB || oub > VAR[lvi].U.FLT.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%1d,%1d] to %s.\n", 
          olb, oub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(fdd_one_constraint(d, lvi, (float) olb, (float) oub)); 
    } 
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Conflict of offset values in both float and int types.\n"
      ); 
      bk(0); 
    } 
    break; 	
  case TYPE_DOUBLE: 
    if (olb > oub) { 
      if (oflb < VAR[lvi].U.DBLE.LB || ofub > VAR[lvi].U.DBLE.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%.4f,%.4f] to %s.\n", 
          oflb, ofub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(dfdd_one_constraint(d, lvi, (double) oflb, (double) ofub)); 
    } 
    else if (oflb > ofub) {  
      if (olb < VAR[lvi].U.DBLE.LB || oub > VAR[lvi].U.DBLE.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%1d,%1d] to %s.\n", 
          olb, oub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(dfdd_one_constraint(d, lvi, (double) olb, (double) oub)); 
    } 
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Conflict of offset values in both double and int types.\n"
      ); 
      bk(0); 
    } 
    break; 	
  case TYPE_DISCRETE: 
    if (olb > oub) { 
      if (oflb < VAR[lvi].U.DISC.LB || ofub > VAR[lvi].U.DISC.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%.4f,%.4f] to %s.\n", 
          oflb, ofub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(ddd_one_constraint(d, lvi, flt_ceil(oflb), flt_floor(ofub))); 
    } 
    else if (oflb > ofub) {  
      if (olb < VAR[lvi].U.DISC.LB || oub > VAR[lvi].U.DISC.UB) {
        fprintf(RED_OUT, 
          "WARNING: assignment trucation of [%1d,%1d] to %s.\n", 
          olb, oub, VAR[lvi].NAME
        ); 
        fflush(RED_OUT); 
        return(NORM_FALSE); 
      }
      return(ddd_one_constraint(d, lvi, olb, oub)); 
    } 
    else { 
      fprintf(RED_OUT, 
        "\nERROR: Conflict of offset values in both discrete and int types.\n"
      ); 
      bk(0); 
    } 
    break; 	
  }
}
  /* red_discrete_assign_bottom_analysis_fwd() */ 
  


 
int	count_discrete_assign_offset = 0; 
  
inline struct red_type	*red_discrete_assign_offset_analysis_fwd(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float			ofub, 
  struct red_type	*offset
) { 
  int	result, ci, conj; 
  
/*
  fprintf(RED_OUT, "\nd a o a fw %d\n", ++count_discrete_assign_offset); 
  if (count_discrete_assign_offset == 75) { 
    fprintf(RED_OUT, "Caught\n"); 	
  } 
  fflush(RED_OUT); 
*/  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_discrete_assign_bottom_analysis_fwd(
      d, lvi, olb, oub, oflb, ofub 
    ); 
  } 
  else if (offset->var_index == FLOAT_VALUE) { 
    for (ci = 0; ci < offset->u.fdd.child_count; ci++) { 
      RT[conj = RT_TOP++] = red_bop(AND, d, offset->u.fdd.arc[ci].child); 
      RT[conj] = red_discrete_assign_bottom_analysis_fwd(
        RT[conj], 
        lvi, 
        0, -1, 
        offset->u.fdd.arc[ci].lower_bound, 
        offset->u.fdd.arc[ci].upper_bound  
      ); 
      RT[result] = red_bop(OR, RT[result], RT[conj]); 
      RT_TOP--; // conj 
  } }
  else { 
    for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
      RT[conj = RT_TOP++] = red_bop(AND, d, offset->u.ddd.arc[ci].child); 
      RT[conj] = red_discrete_assign_bottom_analysis_fwd(
        RT[conj], 
        lvi, 
        offset->u.ddd.arc[ci].lower_bound, 
        offset->u.ddd.arc[ci].upper_bound, 
        0.0, -1 
      ); 
      RT[result] = red_bop(OR, RT[result], RT[conj]); 
      RT_TOP--; // conj 
  } }
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_discrete_assign_offset_analysis_fwd() */ 
  



inline struct red_type	*red_discrete_assign_lhs_analysis_fwd(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  struct red_type	*lopd, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float			ofub, 
  struct red_type	*offset
) { 
  int	result, ci, lconj, value; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    if (   offset == NULL
        || !(act->st_status & FLAG_ACTION_LHS_RECURSION)
        ) {
      RT[result] = red_discrete_assign_offset_analysis_fwd(
        d, act, pi, lvi, olb, oub, oflb, ofub, offset   
      ); 
    }
    else switch (VAR[lvi].TYPE) { 
    case TYPE_FLOAT: 
      RT[value = RT_TOP++] 
      = red_discrete_assign_offset_analysis_fwd(d, act, pi, FLOAT_VALUE, 
          olb, oub, oflb, ofub, offset  
        ); 
      for (ci = 0; ci < RT[value]->u.fdd.child_count; ci++) { 
        RT[result] = red_bop(OR, RT[result], 
          red_assign_float_interval(
            RT[value]->u.fdd.arc[ci].child,  
            lvi, 
            RT[value]->u.fdd.arc[ci].lower_bound, 
            RT[value]->u.fdd.arc[ci].upper_bound  
        ) ) ; 
      }
      RT_TOP--; // value
      break; 
    case TYPE_DOUBLE: 
      RT[value = RT_TOP++] 
      = red_discrete_assign_offset_analysis_fwd(d, act, pi, DOUBLE_VALUE,  
          olb, oub, oflb, ofub, offset  
        ); 
      for (ci = 0; ci < RT[value]->u.ddd.child_count; ci++) { 
        RT[result] = red_bop(OR, RT[result], 
          red_assign_double_interval(
            RT[value]->u.dfdd.arc[ci].child,  
            lvi, 
            RT[value]->u.dfdd.arc[ci].lower_bound, 
            RT[value]->u.dfdd.arc[ci].upper_bound   
        ) ) ; 
      }
      RT_TOP--; // value
      break; 
    case TYPE_DISCRETE: 
      RT[value = RT_TOP++] 
      = red_discrete_assign_offset_analysis_fwd(d, act, pi, VI_VALUE, 
          olb, oub, oflb, ofub, offset  
        ); 
      for (ci = 0; ci < RT[value]->u.dfdd.child_count; ci++) { 
        RT[result] = red_bop(OR, RT[result], 
          red_assign_interval(
            RT[value]->u.ddd.arc[ci].child, lvi, 
            RT[value]->u.ddd.arc[ci].lower_bound, 
            RT[value]->u.ddd.arc[ci].upper_bound 
        ) ); 
      }
      RT_TOP--; // value
      break; 
    }
  } 
  else if (   offset == NULL
           || !(act->st_status & FLAG_ACTION_LHS_RECURSION)
           ) { 
    for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
      RT[lconj = RT_TOP++] = red_bop(AND, lopd->u.ddd.arc[ci].child, d); 
      for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
	   lvi <= lopd->u.ddd.arc[ci].upper_bound; 
	   lvi++
	   ) {
        if (lvi == FLAG_NO_USE) 
          continue; 
      
        RT[result] = red_bop(OR, RT[result], 
          red_discrete_assign_offset_analysis_fwd( 
            RT[lconj], act, pi, lvi, 
            olb, oub, oflb, ofub, offset 
        ) ); 
    } }
    RT_TOP--; // lconj 
  }
  else {
    int	if_value, idf_value, cj; 

    for (ci = 0; ci < lopd->u.ddd.child_count; ci++) {       
      RT[value = RT_TOP++] = NULL; 
      RT[if_value = RT_TOP++] = NULL; 
      RT[idf_value = RT_TOP++] = NULL; 
      RT[lconj = RT_TOP++] = red_bop(AND, lopd->u.ddd.arc[ci].child, d); 
      for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
	   lvi <= lopd->u.ddd.arc[ci].upper_bound; 
	   lvi++
	   ) {
        if (lvi == FLAG_NO_USE) 
          continue; 
      
        switch (VAR[lvi].TYPE) { 
        case TYPE_FLOAT: 
          if (!RT[if_value]) 
            RT[if_value] = red_discrete_assign_offset_analysis_fwd( 
              RT[lconj], act, pi, FLOAT_VALUE, 
              olb, oub, oflb, ofub, offset 
            ); 
          for (cj = 0; cj < RT[if_value]->u.dfdd.child_count; cj++) { 
            RT[result] = red_bop(OR, RT[result], 
              red_assign_float_interval(
                RT[if_value]->u.fdd.arc[cj].child,  
                lvi, 
                RT[if_value]->u.fdd.arc[cj].lower_bound, 
                RT[if_value]->u.fdd.arc[cj].upper_bound  
            ) ); 
          }
          break; 
        case TYPE_DOUBLE: 
          if (!RT[idf_value]) 
            RT[idf_value] = red_discrete_assign_offset_analysis_fwd( 
              RT[lconj], act, pi, DOUBLE_VALUE, 
              olb, oub, oflb, ofub, offset 
            ); 
          for (cj = 0; cj < RT[idf_value]->u.dfdd.child_count; cj++) { 
            RT[result] = red_bop(OR, RT[result], 
              red_assign_double_interval(
                RT[idf_value]->u.dfdd.arc[cj].child,  
                lvi, 
                RT[idf_value]->u.dfdd.arc[cj].lower_bound, 
                RT[idf_value]->u.dfdd.arc[cj].upper_bound  
            ) ); 
          }
          break; 
        case TYPE_DISCRETE: 
          if (!RT[value]) 
            RT[value] = red_discrete_assign_offset_analysis_fwd( 
              RT[lconj], act, pi, VI_VALUE, 
              olb, oub, oflb, ofub, offset 
            ); 
          for (cj = 0; cj < RT[value]->u.ddd.child_count; cj++) { 
            RT[result] = red_bop(OR, RT[result], 
              red_assign_interval(
                RT[value]->u.ddd.arc[cj].child,  
                lvi, 
                RT[value]->u.ddd.arc[cj].lower_bound, 
                RT[value]->u.ddd.arc[cj].upper_bound  
            ) ); 
          }
          break; 
        }
      }
      RT_TOP = RT_TOP-4; // lconj, idf_value, if_value, value 
  } }
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_discrete_assign_lhs_analysis_fwd() */



#if RED_DEBUG_ACTION_MODE
int	count_da_fwd = 0; 
#endif 

struct red_type	*red_action_discrete_assign_fwd(
  int			W, 
  struct statement_type	*act, 
  int			pi 
) {
  int 			lvi, lopdi, 
  			offset_lb, offset_ub,  
  			offseti, flag; 
  float			offset_flb, offset_fub; 
  struct red_type	*result; 

  #if RED_DEBUG_ACTION_MODE
  fprintf(RED_OUT, "\ncount_da_fwd = %1d: ", ++count_da_fwd); 
  pcform(act->u.act.lhs); 
  fprintf(RED_OUT, "op=%1d, "); 
  pcform(act->u.act.rhs_exp); 
  fflush(RED_OUT); 
  #endif 
  
  if (   act->u.act.lhs->type != TYPE_REFERENCE
      && (GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
         == FLAG_ACTION_LAZY_EVAL
      && (   (  act->u.act.lhs->u.atom.exp_base_proc_index->var_status 
              & FLAG_EXP_STATE_INSIDE
              )
//          || act->u.act.lhs->u.atom.indirect_count
          || check_dynamic_complex_exp(act->u.act.rhs_exp)
      )   ){
    if (   (  act->u.act.lhs->u.atom.exp_base_proc_index->var_status 
            & FLAG_EXP_STATE_INSIDE
            )
//        || act->u.act.lhs->u.atom.indirect_count
        ) {
      result = red_variable_sim_eliminate(RT[W], 
        act->u.act.lhs->u.atom.var_index
      ); 
    }
    else { 
      lopdi = get_value(
        act->u.act.lhs->u.atom.exp_base_proc_index, pi, &flag
      ); 
      lvi = act->u.act.lhs->u.atom.var_index; 
      lvi = variable_index[VAR[lvi].TYPE][lopdi][VAR[lvi].OFFSET]; 
      result = red_variable_eliminate(RT[W], lvi); 
    }
    return(result); 
  }

  lopdi = RT_TOP++; 
  offseti = RT_TOP++; 
  discrete_lhs_rhs_setup(RT[W], act, pi, 
    &lvi, lopdi, 
    &offset_lb, &offset_ub, &offset_flb, &offset_fub, offseti 
  ); 
  #if RED_DEBUG_ACTION_MODE
  if (!RT[offseti])  
    fprintf(RED_OUT, "offset_ub = %1d\n", offset_ub); 
  #endif 
  result = red_discrete_assign_lhs_analysis_fwd(RT[W], act, pi, 
    lvi, RT[lopdi], 
    offset_lb, offset_ub, offset_flb, offset_fub, RT[offseti]  
  ); 
  RT_TOP = RT_TOP-2; // lopdi, offseti 
  
  return(result); 

}
/* red_action_discrete_assign_fwd() */ 





/*****************************************************************
 *
 */ 


inline struct red_type	*red_clear_process_offset_analysis_fwd(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			olb, 
  int			oub, 
  struct red_type	*offset
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_proc_eliminate(
      d, olb, oub 
    ); 
  } 
  else for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
    RT[conj = RT_TOP++] = red_bop(AND, d, offset->u.ddd.arc[ci].child); 
    RT[conj] = red_proc_eliminate(
      RT[conj], 
      offset->u.ddd.arc[ci].lower_bound, 
      offset->u.ddd.arc[ci].upper_bound  
    ); 
    RT[result] = red_bop(OR, RT[result], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_clear_process_offset_analysis_fwd(() */ 





struct red_type	*red_action_clear_process_fwd(
  int			W, 
  struct statement_type	*act, 
  int			pi 
) {
  int 			lvi, lopdi, offset_lb, offset_ub, offseti; 
  float			offset_flb, offset_fub; 
  struct red_type	*result; 

  #if RED_DEBUG_ACTION_MODE
  fprintf(RED_OUT, "\ncount_da_fwd = %1d: ", ++count_da_fwd); 
  pcform(act->u.act.lhs); 
  fprintf(RED_OUT, "op=%1d, "); 
  pcform(act->u.act.rhs_exp); 
  fflush(RED_OUT); 
  #endif 
  
  lopdi = RT_TOP++; 
  offseti = RT_TOP++; 
  discrete_lhs_rhs_setup(RT[W], act, pi, 
    &lvi, lopdi, 
    &offset_lb, &offset_ub, &offset_flb, &offset_fub, offseti 
  ); 
  #if RED_DEBUG_ACTION_MODE
  if (!RT[offseti])  
    fprintf(RED_OUT, "offset_ub = %1d\n", offset_ub); 
  #endif 
  
  result = red_clear_process_offset_analysis_fwd(RT[W], act, pi, 
    offset_lb, offset_ub, RT[offseti]  
  ); 
  RT_TOP = RT_TOP-2; // lopdi, offseti 
  
  return(result); 

}
/* red_action_clear_process_fwd() */ 





/************************************************
 *  The forward increment and decrement. 
 */


inline struct red_type	*red_discrete_inc_bottom_analysis_fwd( 
  struct red_type	*d, 
  int			lvi, 
  int			olb, 
  int			oub, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  if (flag_dec) 
//    if (flag_abstract) 
      return(red_inc_off(d, lvi, -1 * oub, -1 * olb)); 
//    else 
//      return(red_inc(d, lvi, -1 * oub, -1 * olb)); 
  else 
//    if (flag_abstract) 
      return(red_inc_off(d, lvi, olb, oub));  
//    else 
//      return(red_inc(d, lvi, olb, oub)); 
}
  /* red_discrete_inc_bottom_analysis_fwd() */ 
  
  
  
inline struct red_type	*red_discrete_inc_offset_analysis_fwd(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  int			olb, 
  int			oub, 
  struct red_type	*offset, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_discrete_inc_bottom_analysis_fwd(
      d, lvi, olb, oub, flag_dec, flag_abstract
    ); 
  } 
  else for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
    RT[conj = RT_TOP++] = red_bop(AND, d, offset->u.ddd.arc[ci].child); 
    RT[conj] = red_discrete_inc_bottom_analysis_fwd(
      RT[conj], 
      lvi, 
      offset->u.ddd.arc[ci].lower_bound, 
      offset->u.ddd.arc[ci].upper_bound, 
      flag_dec, flag_abstract
    ); 
    RT[result] = red_bop(OR, RT[result], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_discrete_inc_offset_analysis_fwd() */ 
  



inline struct red_type	*red_discrete_inc_lhs_analysis_fwd(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  struct red_type	*lopd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  int	result, ci, lconj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    RT[result] = red_discrete_inc_offset_analysis_fwd(
      d, act, pi, lvi, olb, oub, offset, flag_dec, flag_abstract  
    ); 
  } 
  else for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
    RT[lconj = RT_TOP++] = red_bop(AND, lopd->u.ddd.arc[ci].child, d); 
    for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
	 lvi <= lopd->u.ddd.arc[ci].upper_bound; 
	 lvi++
	 ) {
      if (lvi == FLAG_NO_USE) 
        continue; 
      
      RT[result] = red_bop(OR, RT[result], 
        red_discrete_inc_offset_analysis_fwd( 
          RT[lconj], act, pi, lvi, olb, oub, offset, flag_dec, flag_abstract 
      ) ); 
    }
    RT_TOP--; // lconj 
  }
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_discrete_inc_lhs_analysis_fwd() */



// int count_inc_fwd = 0; 

struct red_type	*red_action_discrete_inc_fwd(
  int			W, 
  struct statement_type	*act, 
  int			pi, 
  int			flag_dec, 
  int			flag_abstract
) {
  int 			lvi, lopdi, offset_lb, offset_ub, offseti; 
  float			offset_flb, offset_fub; 
  struct red_type	*result;

/*
  fprintf(RED_OUT, "\ninc_fwd %1d\n", ++count_inc_fwd); 
  fflush(RED_OUT); 
  if (count_inc_fwd == -1) { 
    fprintf(RED_OUT, "Caught!\n  "); 
    print_parse_statement_line(act); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 	
  } 
*/
  lopdi = RT_TOP++; 
  offseti = RT_TOP++; 
  discrete_lhs_rhs_setup(RT[W], 
    act, pi, 
    &lvi, lopdi, 
    &offset_lb, &offset_ub, &offset_flb, &offset_fub, offseti
  ); 
  result = red_discrete_inc_lhs_analysis_fwd(RT[W], act, pi, 
    lvi, RT[lopdi], 
    offset_lb, offset_ub, RT[offseti], 
    flag_dec, flag_abstract 
  ); 
  RT_TOP = RT_TOP-2; // lopdi, offseti 
  
  return(result); 

}
/* red_action_discrete_inc_fwd() */ 







/**************************************************************************
*  Forward no abstraction
*/ 




struct red_type	*rec_time_clock_magnitude_inc(d) 
     struct red_type	*d; 
{
  int				b, ci;
  struct red_type		*new_child, *result; 
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic; 
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return(d); 

  ce = cache4_check_result_key(
    OP_TIME_CLOCK_MAGNITUDE_INC, d, 
    (struct hrd_exp_type *) MIC_LCI,  
    MIC_RCI,  
    MIC_OFFSET_LB * CLOCK_POS_INFINITY + MIC_OFFSET_UB 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    if (d->var_index == ZONE[0][MIC_RCI]) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	bc = &(d->u.crd.arc[ci]); 
	b = zone_ub_add(bc->upper_bound, -1*MIC_OFFSET_LB); 
	if (b > 0)
	  b = 0; 
	new_child = bc->child; 
	new_child = crd_one_constraint(new_child, ZONE[0][MIC_LCI], b); 
	if (bc->upper_bound > 0) 
	  b = 0; 
	else 
	  b = bc->upper_bound;
	new_child = crd_one_constraint(new_child, d->var_index, b); 
	
	result = red_bop(OR, result, new_child);
      }
    } 
    else if (d->var_index == ZONE[MIC_RCI][0]) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	bc = &(d->u.crd.arc[ci]); 
	b = zone_ub_add(bc->upper_bound, MIC_OFFSET_UB); 
	if (b < 0)
	  return(result);
	
	new_child = bc->child; 
	if (b < CLOCK_POS_INFINITY) 
	  new_child = crd_one_constraint(new_child, ZONE[MIC_LCI][0], b); 
	
	if (bc->upper_bound < CLOCK_POS_INFINITY) 
	  new_child = crd_one_constraint(new_child, d->var_index, bc->upper_bound); 
	
	result = red_bop(OR, result, new_child); 
      }
    } 
    else { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	bc = &(d->u.crd.arc[ci]); 
	new_child = rec_time_clock_magnitude_inc(bc->child); 
	result = red_bop(OR, result, 
			      crd_one_constraint
			      (new_child, d->var_index, bc->upper_bound) 
			      ); 
      }
    }
    break; 

  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) { 
      new_child = rec_time_clock_magnitude_inc(d->u.fdd.arc[ci].child); 
      result = red_bop(OR, result, fdd_one_constraint(
        new_child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ) );
    }
    break; 

  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) { 
      new_child = rec_time_clock_magnitude_inc(d->u.dfdd.arc[ci].child); 
      result = red_bop(OR, result, dfdd_one_constraint(
        new_child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ) );
    }
    break; 

  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(d->u.ddd.arc[ci]); 
      new_child = rec_time_clock_magnitude_inc(ic->child); 
      result = red_bop(OR, result, 
			    ddd_one_constraint
			    (new_child, d->var_index, ic->lower_bound, ic->upper_bound)
			    );
    }
  }
  return(ce->result = result); 
}
/* rec_time_clock_magnitude_inc() */ 




struct red_type	*red_time_clock_magnitude_inc(d, lci, rci, lb, ub)
     struct red_type	*d; 
     int		lci, rci, lb, ub; 
{
  d = red_time_clock_eliminate(d, lci); 

  MIC_LCI = lci; 
  MIC_RCI = rci; 
  MIC_OFFSET_LB = lb; 
  MIC_OFFSET_UB = ub; 
  d = rec_time_clock_magnitude_inc(d);

  return(d); 
}
/* red_time_clock_magnitude_inc() */ 





inline struct red_type	*red_clock_assign_offset_analysis_fwd( 
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lci, 
  int			rci, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    if (rci == 0) { 
      RT[result] = crd_one_constraint(d, ZONE[lci][0], oub);
      RT[result] = crd_one_constraint(RT[result], ZONE[0][lci], -1*olb); 
    } 
    else if (lci == rci) { 
      if (olb != 0 || oub != 0) { 
        RT[result] = red_time_clock_inc(d, lci, olb, oub); 
      } 
      else 
        RT[result] = d;
      } 
    else if (flag_abstract) { 
      RT[result] = red_time_clock_magnitude_inc(d, lci, rci, olb, oub); 
      RT[result] = crd_one_constraint(RT[result], ZONE[0][lci], 0); 
    } 
    else { 
      RT[result] = crd_one_constraint(d, ZONE[lci][rci], oub);
      RT[result] = crd_one_constraint(RT[result], ZONE[rci][lci], -1*olb);
    }
  }
  else for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
    olb = 2*offset->u.ddd.arc[ci].lower_bound; 
    oub = 2*offset->u.ddd.arc[ci].upper_bound; 
    RT[conj = RT_TOP++] = red_bop(AND, d, offset->u.ddd.arc[ci].child); 
    if (rci == 0) { 
      RT[conj] = crd_one_constraint(RT[conj], ZONE[lci][0], oub);
      RT[conj] = crd_one_constraint(RT[conj], ZONE[0][lci], -1*olb); 
    } 
    else if (lci == rci) { 
      if (olb != 0 || oub != 0) { 
        RT[conj] = red_time_clock_inc(d, lci, olb, oub); 
      } 
      else 
        RT[conj] = d;
      } 
    else if (flag_abstract) { 
      RT[conj] = red_time_clock_magnitude_inc(RT[conj], lci, rci, olb, oub); 
      RT[conj] = crd_one_constraint(RT[conj], ZONE[0][lci], 0); 
    } 
    else { 
      RT[conj] = crd_one_constraint(RT[conj], ZONE[lci][rci], oub);
      RT[conj] = crd_one_constraint(RT[conj], ZONE[rci][lci], -1*olb);
    }
    RT[result] = red_bop(OR, RT[result], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_offset_analysis_fwd() */ 
  
  
  
  
 
inline struct red_type	*red_clock_assign_rhs_analysis_fwd( 
  struct red_type	*d, 
  struct red_type	*d_no_lhs, 
  struct statement_type	*act, 
  int			pi, 
  int			lci, 
  struct ps_exp_type	*rvar, 
  int			rpi, 
  struct red_type	*ropd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, rvi, rci, ci, lconj, rconj, rppi; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (rvar == NULL) { 
    RT[result] = red_clock_assign_offset_analysis_fwd( 
      d_no_lhs, act, pi, lci, 0, olb, oub, offset, flag_abstract
    ); 
  } 
  else if (ropd == NULL) { 
    rvi = rvar->u.atom.var_index;
    rvi = variable_index[TYPE_CLOCK][rpi][VAR[rvi].OFFSET];        
    rci = VAR[rvi].U.CLOCK.CLOCK_INDEX; 
    if (lci == rci) 
      RT[result] = red_clock_assign_offset_analysis_fwd(
        d, act, pi, 
        lci,  
        rci, 
        olb, oub, offset, 
        flag_abstract
      ); 
    else 
      RT[result] = red_clock_assign_offset_analysis_fwd(
        d_no_lhs, act, pi, 
        lci,  
        rci, 
        olb, oub, offset, 
        flag_abstract
      ); 
  }
  else for (ci = 0; ci < ropd->u.ddd.child_count; ci++) { 
    RT[rconj = RT_TOP++] 
    = red_bop(AND, d_no_lhs, ropd->u.ddd.arc[ci].child); 
    for (rppi = ropd->u.ddd.arc[ci].lower_bound; 
	 rppi <= ropd->u.ddd.arc[ci].upper_bound; 
	 rppi++
	 ) {
      rvi = rvar->u.atom.var_index;
      rvi = variable_index[TYPE_CLOCK][rppi][VAR[rvi].OFFSET];
      rci = VAR[rvi].U.CLOCK.CLOCK_INDEX; 
      if (lci == rci) { 
      	int	k; 

      	RT[k = RT_TOP++] 
      	= red_bop(AND, d, ropd->u.ddd.arc[ci].child); 

        RT[result] = red_bop(OR, RT[result], 
          red_clock_assign_offset_analysis_fwd(
            RT[k], act, pi, 
            lci, 
            rci, 
            olb, oub, offset, 
            flag_abstract
        ) ); 
        RT_TOP--; // k 
      } 
      else { 
        RT[result] = red_bop(OR, RT[result], 
          red_clock_assign_offset_analysis_fwd( 
            RT[rconj], act, pi, 
            lci, 
            rci, 
            olb, oub, offset, 
            flag_abstract
        ) ); 
      } 
    } 
    RT_TOP--; // rconj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_rhs_analysis_fwd() */ 
  
  
  


int	easy_equal_lci_rci(
  int			lci, 
  struct red_type	*ropd, 
  struct ps_exp_type	*rvar, 
  int			rpi
) { 
  int	rvi, rci; 
  
  if (ropd || !rvar) 
    return(TYPE_FALSE); 

  rvi = rvar->u.atom.var_index;
  rvi = variable_index[TYPE_CLOCK][rpi][VAR[rvi].OFFSET];        
  rci = VAR[rvi].U.CLOCK.CLOCK_INDEX;
  
  return(lci == rci); 
} 
  /* easy_equal_lci_rci() */  
  
  
  

inline struct red_type	*red_clock_assign_lhs_analysis_fwd( 
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  struct ps_exp_type	*lvar, 
  int			lpi, 
  struct red_type	*lopd, 
  struct ps_exp_type	*rvar, 
  int			rpi, 
  struct red_type	*ropd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, lvi, lci, ci, lconj, rconj, lppi; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    lvi = lvar->u.atom.var_index;
    lvi = variable_index[TYPE_CLOCK][lpi][VAR[lvi].OFFSET];        
    lci = VAR[lvi].U.CLOCK.CLOCK_INDEX;
 
    RT[result] = d; 
    if (!easy_equal_lci_rci(lci, ropd, rvar, rpi)) { 
      if (   !flag_abstract
          && FLAG_STATEMENT_POLARITY <= 0 // either no abstraction or under-approx. 
	  )
        RT[result] = RED_BYPASS_FWD(result, lci); 
      RT[result] = red_time_clock_eliminate(RT[result], lci);
    }
    RT[result] = red_clock_assign_rhs_analysis_fwd(
      d, RT[result], act, pi, 
      lci,  
      rvar, rpi, ropd, 
      olb, oub, offset, 
      flag_abstract
    ); 
  }
  else for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
    RT[lconj = RT_TOP++] = red_bop(AND, d, lopd->u.ddd.arc[ci].child); 
    for (lppi = lopd->u.ddd.arc[ci].lower_bound; 
	 lppi <= lopd->u.ddd.arc[ci].upper_bound; 
	 lppi++
	 ) {
      lvi = lvar->u.atom.var_index;
      lvi = variable_index[TYPE_CLOCK][lppi][VAR[lvi].OFFSET];

      lci = VAR[lvi].U.CLOCK.CLOCK_INDEX; 
      RT[rconj = RT_TOP++] = RT[lconj]; 
      if (!easy_equal_lci_rci(lci, ropd, rvar, rpi)) { 
        if (   !flag_abstract
            && FLAG_STATEMENT_POLARITY <= 0 // either no abstraction or under-approx. 
            )
          RT[rconj] = RED_BYPASS_FWD(lconj, lci); 
        RT[rconj] = red_time_clock_eliminate(RT[rconj], lci);
      }
      RT[rconj] = red_clock_assign_rhs_analysis_fwd(
        d, RT[rconj], act, pi, 
        lci,  
        rvar, rpi, ropd, 
        olb, oub, offset, 
        flag_abstract
      ); 
      RT[result] = red_bop(OR, RT[result], RT[rconj]); 
      RT_TOP--; // rconj 
    } 
    RT_TOP--; // lconj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_lhs_analysis_fwd() */ 
  
  
  
  
   
struct red_type	*red_action_clock_assign_fwd(W, act, pi, flag_abs)
     int			W, pi, flag_abs;
     struct statement_type	*act;
{
  int			lpi, rpi, olb, oub, lopdi, ropdi, offseti;
  struct ps_exp_type	*lvar, *rvar; 

  lopdi = RT_TOP++; 
  ropdi = RT_TOP++;  // for lopd and ropd 
  offseti = RT_TOP++; 
  clock_assign_setup(RT[W], 
    act, pi, 
    &lvar, &lpi, lopdi, 
    &rvar, &rpi, ropdi, 
    &olb, &oub, offseti
  ); 
  RT[W] = red_clock_assign_lhs_analysis_fwd( 
    RT[W], act, pi, 
    lvar, lpi, RT[lopdi], 
    rvar, rpi, RT[ropdi], 
    olb, oub, RT[offseti],  
    flag_abs  
  ); 
  RT_TOP = RT_TOP-3; // lopdi, ropdi, offseti 
  return(RT[W]); 
}
/* red_action_clock_assign_fwd() */ 



struct red_type	*red_action_discrete_assign_constant_fwd(
  int			W,
  struct statement_type	*st, 
  int			pi  
) {
  if (   check_oapprox_lazy_exp()
      && st->u.act.lhs->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
      && st->u.act.lhs->u.atom.exp_base_proc_index 
         != PS_EXP_LOCAL_IDENTIFIER
      && st->u.act.lhs->u.atom.exp_base_proc_index 
         != PS_EXP_GLOBAL_IDENTIFIER
      ) 
    return(red_variable_sim_eliminate(
      RT[W], st->u.act.lhs->u.atom.var_index
    ) ); 
  else 
    return(red_action_discrete_assign_fwd(W, st, pi));
}
  /* red_action_discrete_assign_constant_fwd() */ 




struct red_type	*red_action_discrete_assign_polynomial_fwd( 
  int			W,
  struct statement_type	*st, 
  int			pi  
) { 
  return(red_action_discrete_assign_fwd(
    W, st, FLAG_STATEMENT_PI 
  ) );
}
  /* red_action_discrete_assign_polynomial_fwd() */ 





struct red_type	*red_action_discrete_cplug_fwd(
  int			W,
  struct statement_type	*st, 
  int			pi  
) {
  int	result; 
  
  if (st->u.cplug.lhs) { 
    result = cplugin_proc(st->u.cplug.cmod_index, st->u.cplug.cproc_index); 
    if (   st->u.cplug.lhs->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
        && st->u.cplug.lhs->u.atom.exp_base_proc_index 
           != PS_EXP_LOCAL_IDENTIFIER
        && st->u.cplug.lhs->u.atom.exp_base_proc_index 
           != PS_EXP_GLOBAL_IDENTIFIER
        ) 
      return(red_variable_sim_eliminate(
        RT[W], st->u.cplug.lhs->u.atom.var_index
      ) ); 
    else { 
      ACTION_BUFFER.op = ASSIGN_DISCRETE_POLYNOMIAL; 
      ACTION_BUFFER.u.act.lhs = st->u.cplug.lhs; 
      ACTION_BUFFER.u.act.rhs_exp = exp_atom(TYPE_CONSTANT, result, NULL); 
      return(red_action_discrete_assign_polynomial_fwd(
        W, &ACTION_BUFFER, pi 
      ) );
  } }
  else {
    CPLUG_IN_W = W; 
    CPLUG_IN_PI = pi; 
    cplugin_proc(st->u.cplug.cmod_index, st->u.cplug.cproc_index); 
    return(RT[W]); 
  }
}
  /* red_action_discrete_cplug_fwd() */ 



struct red_type	*rec_statement_untimed_fwd(W, st)
     int			W;
     struct statement_type	*st;
{
  int			red_if, red_else, reachable, 
			cur, i, lvi, flag, pi; 
  
  if (!st) 
    return(RT[W]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[W]);  
  case ST_IF: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_if = RT_TOP++] = red_bop(AND, RT[W], 
        st->u.branch.red_cond[FLAG_STATEMENT_PI]
      ); 
      RT[W] = red_bop(AND, RT[W], 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[red_if = RT_TOP++] = red_delayed_eval( 
        st->u.branch.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W]
      ); 
      RT[W] = red_delayed_eval( 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    RT[red_if] = rec_statement_untimed_fwd(red_if, st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[W] = rec_statement_untimed_fwd(W, st->u.branch.else_statement); 
    } 
    RT[W] = red_bop(OR, RT[red_if], RT[W]); 
    RT_TOP--; 
    return(RT[W]); 
    break; 
  case ST_WHILE: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[reachable = RT_TOP++] = red_bop(AND, RT[W], 
        st->u.loop.red_cond[FLAG_STATEMENT_PI]
      ); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[W] = red_bop(AND, RT[W], st->u.loop.red_uncond[FLAG_STATEMENT_PI]);
    }
    else { 
      RT[reachable = RT_TOP++] = red_delayed_eval( 
        st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W]
      ); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[W] = red_delayed_eval(
        st->u.loop.red_uncond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W]
      );
    }  
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_untimed_fwd(cur, st->u.loop.statement); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[W] = red_bop(OR, RT[W], red_bop(AND, 
          RT[cur], st->u.loop.red_uncond[FLAG_STATEMENT_PI]
          )
        ); 
        RT[cur] = red_bop(AND, RT[cur], 
          st->u.loop.red_cond[FLAG_STATEMENT_PI]
        ); 
      }
      else { 
        RT[W] = red_bop(OR, RT[W], red_delayed_eval( 
          st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, RT[cur] 
        ) ); 
        RT[cur] = red_delayed_eval( 
          st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[cur]
        ); 
      } 
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[reachable]); 
      RT[reachable] = red_bop(OR, RT[reachable], RT[cur]); 
    } 
    RT_TOP = RT_TOP-2; /* reachable, cur */ 
    return(RT[W]);   
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      RT[W] = rec_statement_untimed_fwd(W, st->u.seq.statement[i]); 
    } 
    return(RT[W]); 
    break; 
  case ST_CALL: 
    RT[W] = red_assign_interval(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET_MODE], 
      st->u.call.call_mode_index, st->u.call.call_mode_index
    ); 
    RT[W] = red_inc_off(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      1, 1 
    ); 
    ACTION_SAVE_RETMODE->u.act.rhs_exp 
    = ACTION_SAVE_RETMODE->u.act.offset 
    = exp_atom(TYPE_CONSTANT, st->u.call.ret_mode_index, NULL);  
    return(red_action_discrete_assign_polynomial_fwd(
      W, ACTION_SAVE_RETMODE, FLAG_STATEMENT_PI 
    ) );
    break; 
  case ST_RETURN: 
    RT[W] = red_action_discrete_assign_polynomial_fwd(
      W, ACTION_RESUME_RETMODE, FLAG_STATEMENT_PI 
    ); 
    RT[W] = red_clear_procedure_stack_frame(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP]
    ); 
    RT[W] = red_inc_off(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      -1, -1 
    ); 
    return(RT[W]); 
    break; 
  case ST_CPLUG: 
    return(red_action_discrete_cplug_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ST_GUARD: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[W] = red_bop(AND, RT[W], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[W] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    return(RT[W]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[W] = red_variable_eliminate(RT[W], lvi);
      return(RT[W]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[W] = red_variable_eliminate(RT[W], lvi);
        return(RT[W]); 
      } 
      else { 
      	RT[cur = RT_TOP++] = NORM_FALSE; 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[cur] = red_bop(OR, RT[cur], red_variable_eliminate(RT[W], lvi));  
        } 
        RT_TOP--; // cur 
        return(RT[cur]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      if (st->u.act.lhs->type == TYPE_REFERENCE) 
      // We assume that the reference cannot modify the program counter. 
        return(RT[W]); 

      lvi = st->u.act.lhs->u.atom.var_index; 
      if (VAR[lvi].PROC_INDEX == 0) { 
      	if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	  return(RT[W]); 
      } 
      else { 
      	pi = get_address(st->u.act.lhs->u.atom.exp_base_proc_index, 
          FLAG_STATEMENT_PI, &flag
        ); 
        if (flag == FLAG_SPECIFIC_VALUE) { 
      	  lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	  if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	    return(RT[W]);  
        } 
        else { 
      	  RT[cur = RT_TOP++] = NORM_FALSE; 
      	  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	    lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	    RT[cur] = red_bop(OR, RT[cur], 
      	      red_variable_eliminate(RT[W], lvi)
      	    );  
      	  } 
      	  RT_TOP--; // cur 
      	  return(RT[cur]); 
        }
      }
    }
    return(red_action_discrete_assign_constant_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      if (st->u.act.lhs->type == TYPE_REFERENCE) 
      // We assume that the reference cannot modify the program counter. 
        return(RT[W]); 

      lvi = st->u.act.lhs->u.atom.var_index; 
      if (VAR[lvi].PROC_INDEX == 0) { 
      	if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	  return(RT[W]);        	
      } 
      else { 
        pi = get_address(st->u.act.lhs->u.atom.exp_base_proc_index, 
          FLAG_STATEMENT_PI, &flag
        ); 
        if (flag == FLAG_SPECIFIC_VALUE) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	    return(RT[W]);  
        } 
        else { 
      	  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	    lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	    if (VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING) 
      	      RT[W] = red_variable_eliminate(RT[W], lvi);  
      	  } 
      	  return(RT[W]); 
      	}
      }
    }
    return(red_action_discrete_assign_polynomial_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      return(RT[W]); 
    }     
    else 
      return(red_action_clock_assign_fwd(
        W, st, FLAG_STATEMENT_PI, FLAG_ACTION_ABSTRACT
      ) );
  case ASSIGN_HYBRID_EXP:
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      return(RT[W]); 
    }     
    else if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      return(red_action_hybrid(W, &(st->u.act), FLAG_STATEMENT_PI));
    }
    else {
      lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
      RT[W] = hybrid_bypass_DOWNWARD(W, lvi);
      RT[W] = red_variable_eliminate(RT[W], lvi);
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) 
        RT[W] = red_bop(AND, 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          RT[W] 
        );
      else 
        RT[W] = red_delayed_eval( 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, 
          RT[W] 
        );
      return(RT[W]);
    }
    break;
  case INCREMENT_BY_CONSTANT:
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      if (st->u.act.lhs->type == TYPE_REFERENCE) 
      // We assume that the reference cannot modify the program counter. 
        return(RT[W]); 

      lvi = st->u.act.lhs->u.atom.var_index; 
      if (VAR[lvi].PROC_INDEX == 0) { 
      	if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	  return(RT[W]);        	
      } 
      else { 
        pi = get_address(st->u.act.lhs->u.atom.exp_base_proc_index, 
          FLAG_STATEMENT_PI, &flag
        ); 
        if (flag == FLAG_SPECIFIC_VALUE) { 
      	  lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	  if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	    return(RT[W]);  
        } 
        else { 
      	  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	    lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	    if (VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING) 
      	      RT[W] = red_variable_eliminate(RT[W], lvi);  
      	  } 
      	  return(RT[W]); 
      	}
      }
    }
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_ABSTRACT
    ) );
  case DECREMENT_BY_CONSTANT:
    if (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
        & FLAG_ACTION_ADDRESS_AFFECTING_ONLY
        ) {
      if (st->u.act.lhs->type == TYPE_REFERENCE) 
      // We assume that the reference cannot modify the program counter. 
        return(RT[W]); 

      lvi = st->u.act.lhs->u.atom.var_index; 
      if (VAR[lvi].PROC_INDEX == 0) { 
      	if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	  return(RT[W]);  	
      } 
      else { 
        pi = get_address(st->u.act.lhs->u.atom.exp_base_proc_index, 
          FLAG_STATEMENT_PI, &flag
        ); 
        if (flag == FLAG_SPECIFIC_VALUE) { 
      	  lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	  if (!(VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING))
      	    return(RT[W]);  
        } 
        else { 
      	  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      	    lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
      	    if (VAR[lvi].STATUS & FLAG_ADDRESS_AFFECTING) 
      	      RT[W] = red_variable_eliminate(RT[W], lvi);  
      	  } 
      	  return(RT[W]); 
      	}
      }
    }
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_ABSTRACT
    ) );
  } 
}
  /* rec_statement_untimed_fwd() */ 
  
  
  
struct red_type	*red_statement_untimed_fwd(
  int			src, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_lazy_eval
) {
  int			original_action_stage, 
			original_address_affecting; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  original_address_affecting = GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING]; 
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  
  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
  = (  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] 
     & ~FLAG_ACTION_ADDRESS_AFFECTING_ONLY
     ) 
  | (flag_lazy_eval & FLAG_ACTION_ADDRESS_AFFECTING_ONLY);
  FLAG_STATEMENT_PI = pi; 

  result = rec_statement_untimed_fwd(src, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  GSTATUS[INDEX_ACTION_ADDRESS_AFFECTING] = original_address_affecting; 
  return(result); 
}
  /* red_statement_untimed_fwd() */ 
  
  



struct red_type	*rec_statement_abstract_fwd(W, st)
     int			W;
     struct statement_type	*st;
{
  int	red_if, red_else, cur, reachable, i, lvi, pi, flag; 
  
  if (!st) 
    return(RT[W]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[W]);  
  case ST_IF: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_if = RT_TOP++] = red_bop(AND, RT[W], 
        st->u.branch.red_cond[FLAG_STATEMENT_PI]
      ); 
      RT[W] = red_bop(AND, RT[W], 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI]
      ); 
    }
    else {
      RT[red_if = RT_TOP++] = red_delayed_eval( 
        st->u.branch.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W]
      ); 
      RT[W] = red_delayed_eval( 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W]
      ); 
    }
    RT[red_if] = rec_statement_abstract_fwd(red_if, st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[W] = rec_statement_abstract_fwd(W, st->u.branch.else_statement); 
    } 
    RT[W] = red_bop(OR, RT[red_if], RT[W]); 
    RT_TOP--; 
    return(RT[W]); 
    break; 
  case ST_WHILE: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[reachable = RT_TOP++] = red_bop(AND, 
        RT[W], st->u.loop.red_cond[FLAG_STATEMENT_PI]
      ); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[W] = red_bop(AND, RT[W], st->u.loop.red_uncond[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[reachable = RT_TOP++] = red_delayed_eval( 
        st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W] 
      ); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[W] = red_delayed_eval(
        st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    }
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_abstract_fwd(cur, st->u.loop.statement); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[W] = red_bop(OR, RT[W], red_bop(AND, RT[cur], st->u.loop.red_uncond[FLAG_STATEMENT_PI])); 
        RT[cur] = red_bop(AND, RT[cur], st->u.loop.red_cond[FLAG_STATEMENT_PI]); 
      }
      else { 
        RT[W] = red_bop(OR, RT[W], red_delayed_eval(
          st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, RT[cur]
        ) ); 
        RT[cur] = red_delayed_eval(
          st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[cur]
        ); 
      } 
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[reachable]); 
      RT[reachable] = red_bop(OR, RT[reachable], RT[cur]); 
    } 
    RT_TOP = RT_TOP-2; /* reachable, cur */ 
    return(RT[W]);   
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      RT[W] = rec_statement_abstract_fwd(W, st->u.seq.statement[i]); 
    } 
    return(RT[W]); 
    break; 
  case ST_CALL: 
    RT[W] = red_assign_interval(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET_MODE], 
      st->u.call.call_mode_index, st->u.call.call_mode_index
    ); 
    RT[W] = red_inc_off(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      1, 1 
    ); 
    ACTION_SAVE_RETMODE->u.act.rhs_exp 
    = ACTION_SAVE_RETMODE->u.act.offset 
    = exp_atom(TYPE_CONSTANT, st->u.call.ret_mode_index, NULL);  
    return(red_action_discrete_assign_polynomial_fwd(
      W, ACTION_SAVE_RETMODE, FLAG_STATEMENT_PI 
    ) );
    break; 
  case ST_RETURN: 
    RT[W] = red_action_discrete_assign_polynomial_fwd(
      W, ACTION_RESUME_RETMODE, FLAG_STATEMENT_PI 
    ); 
    RT[W] = red_clear_procedure_stack_frame(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP]
    ); 
    RT[W] = red_inc_off(RT[W], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      -1, -1 
    ); 
    return(RT[W]); 
    break; 
  case ST_CPLUG: 
    return(red_action_discrete_cplug_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ST_GUARD: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[W] = red_bop(AND, RT[W], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[W] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    return(RT[W]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[W] = red_variable_eliminate(RT[W], lvi);
      return(RT[W]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[W] = red_variable_eliminate(RT[W], lvi);
        return(RT[W]); 
      } 
      else { 
      	RT[cur = RT_TOP++] = NORM_FALSE; 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[cur] = red_bop(OR, RT[cur], red_variable_eliminate(RT[W], lvi));  
        } 
        RT_TOP--; // cur 
        return(RT[cur]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    return(red_action_discrete_assign_constant_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    return(red_action_discrete_assign_polynomial_fwd(
      W, st, FLAG_STATEMENT_PI 
    ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    return(red_action_clock_assign_fwd(
      W, st, FLAG_STATEMENT_PI, FLAG_ACTION_ABSTRACT
    ) );

  case ASSIGN_HYBRID_EXP:
    if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      return(red_action_hybrid(W, &(st->u.act), FLAG_STATEMENT_PI));
    }
    else {
      lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
      RT[W] = hybrid_bypass_DOWNWARD(W, lvi);
      RT[W] = red_variable_eliminate(RT[W], lvi);
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[W] = red_bop(AND, 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          RT[W]
        ); 
      }
      else 
        RT[W] = red_delayed_eval( 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, 
          RT[W]
        );
      return(RT[W]);
    }
    break;

  case INCREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_ABSTRACT
    ) );
  case DECREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_ABSTRACT
    ) );
  case ASSIGN_TRASH: 
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
    return(RT[W] = red_variable_eliminate(RT[W], lvi)); 
  default: 
    fprintf(RED_OUT, "Error: unrecognized statemement operator %1d.\n", 
      st->op
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* rec_statement_abstract_fwd() */ 
  
  
  
struct red_type	*red_statement_abstract_fwd(
  int			src, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_lazy_eval
) {
  int			original_action_stage; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  FLAG_STATEMENT_PI = pi; 
  
  result = rec_statement_abstract_fwd(src, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  return(result); 
}
  /* red_statement_abstract_fwd() */ 
  
  


  
  


/* The procedure computes the postcondition from diagram RT[src] 
 * through compound statement st. 
 * It is not to be called directly by the users. 
 * The users have to call it through red_statement_fwd(). 
 * It runs with environment parameters FLAG_STATEMENT_POLARITY and 
 * FLAG_STATEMENT_PI set by red_statement_fwd(). 
 * It destructs the contents in RT[src].  
 */
struct red_type	*rec_statement_fwd(
	int			src, 
	struct statement_type	*st 
	)
{
  int	red_if, red_else, cur, reachable, i, lvi, rvi, pi, flag; 
  
  if (!st) 
    return(RT[src]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[src]); 
  case ST_IF: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_if = RT_TOP++] = red_bop(AND, RT[src], st->u.branch.red_cond[FLAG_STATEMENT_PI]); 
      RT[src] = red_bop(AND, RT[src], st->u.branch.red_uncond[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[red_if = RT_TOP++] = red_delayed_eval(
        st->u.branch.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[src]
      ); 
      RT[src] = red_delayed_eval( 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[src]
      ); 
    } 
    RT[red_if] = rec_statement_fwd(red_if, st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[src] = rec_statement_fwd(src, st->u.branch.else_statement); 
    } 
    RT[src] = red_bop(OR, RT[red_if], RT[src]); 
    RT_TOP--; 
    return(RT[src]); 
    break; 
  case ST_WHILE: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[reachable = RT_TOP++] = red_bop(AND, RT[src], st->u.loop.red_cond[FLAG_STATEMENT_PI]); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[src] = red_bop(AND, RT[src], 
        st->u.loop.red_uncond[FLAG_STATEMENT_PI]
      ); 
    }
    else {
      RT[reachable = RT_TOP++] = red_delayed_eval(
        st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[src]
      ); 
      RT[cur = RT_TOP++] = RT[reachable]; 
      RT[src] = red_delayed_eval( 
        st->u.loop.red_uncond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[src]
      ); 
    }
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_fwd(cur, st->u.loop.statement); 
      RT[src] = red_bop(OR, RT[src], red_bop(AND, RT[cur], st->u.loop.red_uncond[FLAG_STATEMENT_PI])); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[src] = red_bop(OR, RT[src], 
          red_bop(AND, RT[cur], st->u.loop.red_uncond[FLAG_STATEMENT_PI])
        ); 
        RT[cur] = red_bop(AND, RT[cur], 
          st->u.loop.red_cond[FLAG_STATEMENT_PI]
        ); 
      }
      else {
        RT[src] = red_bop(OR, RT[src], 
          red_delayed_eval(
            st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
            FLAG_STATEMENT_PI, RT[cur] 
          )
        ); 
        RT[cur] = red_delayed_eval( 
          st->u.loop.red_cond[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, RT[cur] 
        ); 
      }
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[reachable]); 
      RT[reachable] = red_bop(OR, RT[reachable], RT[cur]); 
    } 
    RT_TOP = RT_TOP-2; /* reachable, cur */ 
    return(RT[src]);   
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      RT[src] = rec_statement_fwd(src, st->u.seq.statement[i]); 
    } 
    return(RT[src]); 
    break; 

  case ST_CALL: 
    RT[src] = red_assign_interval(RT[src], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET_MODE], 
      st->u.call.call_mode_index, st->u.call.call_mode_index
    ); 
    RT[src] = red_inc_off(RT[src], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      1, 1 
    ); 
    ACTION_SAVE_RETMODE->u.act.rhs_exp 
    = ACTION_SAVE_RETMODE->u.act.offset 
    = exp_atom(TYPE_CONSTANT, st->u.call.ret_mode_index, NULL);  
    return(red_action_discrete_assign_polynomial_fwd(
      src, ACTION_SAVE_RETMODE, FLAG_STATEMENT_PI 
    ) );
    break; 
  case ST_RETURN: 
    RT[src] = red_action_discrete_assign_polynomial_fwd(
      src, ACTION_RESUME_RETMODE, FLAG_STATEMENT_PI 
    ); 
    RT[src] = red_clear_procedure_stack_frame(RT[src], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP]
    ); 
    RT[src] = red_inc_off(RT[src], 
      variable_index[TYPE_DISCRETE][FLAG_STATEMENT_PI][OFFSET__SP], 
      -1, -1 
    ); 
    return(RT[src]); 
    break; 
  case ST_CPLUG: 
    return(red_action_discrete_cplug_fwd(
      src, st, FLAG_STATEMENT_PI 
    ) );
  case ST_GUARD: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[src] = red_bop(AND, RT[src], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[src] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[src]
      ); 
    } 
    return(RT[src]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[src] = red_variable_eliminate(RT[src], lvi);
      return(RT[src]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[src] = red_variable_eliminate(RT[src], lvi);
        return(RT[src]); 
      } 
      else { 
      	RT[cur = RT_TOP++] = NORM_FALSE; 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[cur] = red_bop(OR, RT[cur], red_variable_eliminate(RT[src], lvi));  
        } 
        RT_TOP--; // cur 
        return(RT[cur]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    if (   (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) 
           == FLAG_ROOT_OAPPROX
        && (GSTATUS[INDEX_APPROX] & FLAG_OAPPROX_DISCRETE_LAZY) 
        && (   st->u.act.lhs->type == TYPE_REFERENCE
//            || st->u.act.lhs->u.atom.indirect_count > 0
            || (st->u.act.lhs->u.atom.exp_base_proc_index->var_status 
                & FLAG_EXP_STATE_INSIDE
            )   )
        ) { 
      return(NORM_NO_RESTRICTION);   	
    } 
    else 
      return(red_action_discrete_assign_constant_fwd(
        src, st, FLAG_STATEMENT_PI 
      ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    if (   (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) 
           == FLAG_ROOT_OAPPROX
        && (GSTATUS[INDEX_APPROX] & FLAG_OAPPROX_DISCRETE_LAZY) 
        ) { 
      return(NORM_NO_RESTRICTION);   	
    } 
    else 
      return(red_action_discrete_assign_polynomial_fwd(
        src, st, FLAG_STATEMENT_PI 
      ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    return(red_action_clock_assign_fwd(
      src, st, FLAG_STATEMENT_PI, FLAG_ACTION_EXACT
    ) );

  case ASSIGN_HYBRID_EXP: 
    // At this moment, we do no abstraction for LHA.  
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
    if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) 
        RT[src] = red_bop(AND, 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          RT[src] 
        );
      else 
        RT[src] = red_delayed_eval(
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, 
          RT[src] 
        );
      RT[src] = hybrid_bypass_DOWNWARD(src, lvi); 
      RT[src] = red_variable_eliminate(RT[src], lvi); 
      RT[src] = red_switch_vi(RT[src], lvi, CLOCK[DELTAP]); 
    }
    else {
      RT[src] = hybrid_bypass_DOWNWARD(src, lvi);
      RT[src] = red_variable_eliminate(RT[src], lvi);
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) 
        RT[src] = red_bop(AND, 
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          RT[src] 
        );
      else 
        RT[src] = red_delayed_eval(
          st->u.act.red_effect[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, 
          RT[src] 
        );
    }
    return(RT[src]); 
    break;
  case INCREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(src, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_EXACT
    ) );
  case DECREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(src, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_EXACT
    ) );
  case ASSIGN_TRASH: 
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
    return(RT[src] = red_variable_eliminate(RT[src], lvi)); 
  } 
}
  /* rec_statement_fwd() */ 
  
  
  



struct red_type	*red_statement_fwd(
  int			src, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_polarity, 
  int			flag_lazy_eval 
) {
  int			original_action_stage, original_approx; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  original_approx = GSTATUS[INDEX_APPROX]; 
  GSTATUS[INDEX_APPROX] 
  = FLAG_STATEMENT_POLARITY = flag_polarity; 
  FLAG_STATEMENT_PI = pi; 
  
  result = rec_statement_fwd(src, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  GSTATUS[INDEX_APPROX] = original_approx; 
  return(result); 
}
  /* red_statement_fwd() */ 
  
  
  
  

inline struct red_type *red_general_statement_fwd(
  int 			si, 
  int 			pi, 
  struct statement_type *st, 
  int			fa, 
  int			flag_lazy_eval
) { 
  int			original_action_stage; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  switch (fa) { 
  case FLAG_NO_ACTION_APPROX:  
    result = red_statement_fwd(si, pi, st, fa, flag_lazy_eval); 
    break; 
  case FLAG_ACTION_APPROX_NOXTIVE: 
    result = red_statement_abstract_fwd(si, pi, st, flag_lazy_eval); 
    break; 
  case FLAG_ACTION_APPROX_UNTIMED: 
    result = red_statement_untimed_fwd(si, pi, st, flag_lazy_eval); 
    break; 
  default: 
    result = RT[si]; 
    break; 
  } 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  return(result); 
}
  /* red_general_statement_fwd() */ 





/*****************************************************************
 * Actions for backward executions 
 */ 


int	LVI_CHANGE; 

struct red_type	*rec_change_lhs_to_vivalue(d)
     struct red_type	*d;
{
  int				ci, len, i, c1, c2;
  struct red_type		*child, *result, *gchild;
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_CHANGE_LHS_TO_VIVALUE, 
    d, (struct red_type *) LVI_CHANGE
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  if (   d->var_index > LVI_CHANGE
      && VAR[LVI_CHANGE].TYPE != TYPE_CLOCK
      && VAR[LVI_CHANGE].TYPE != TYPE_DENSE
      ) 
    result = d; 
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (d->var_index == LVI_CHANGE) 
      result = red_bop(OR, 
        ddd_one_constraint(d->u.bdd.zero_child, VI_VALUE, 0, 0), 
        ddd_one_constraint(d->u.bdd.one_child, VI_VALUE, 1, 1) 
      );
    else 
      result = bdd_new(d->var_index, 
        rec_change_lhs_to_vivalue(d->u.bdd.zero_child), 
        rec_change_lhs_to_vivalue(d->u.bdd.one_child)
      );
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (CLOCK[c1] == LVI_CHANGE || CLOCK[c2] == LVI_CHANGE) { 
      fprintf(RED_OUT, "\nThere is something wrong.\n"); 
      exit(0); 
    }
    else for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_change_lhs_to_vivalue(bc->child);
      result = red_bop(OR, result, 
        crd_one_constraint(child, d->var_index, 
          d->u.crd.arc[ci].upper_bound
      ) );
    }
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (i = 0; i < len; i++) {
      if (LVI_CHANGE == d->u.hrd.hrd_exp->hrd_term[i].var_index) {
        fprintf(RED_OUT, "\nThere is something wrong!\n"); 
        exit(0); 
        break;
      }
    } 
    if (i < len) { 
      ci = d->u.hrd.child_count-1; 
      if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
          && d->u.hrd.arc[ci].ub_denominator == 1
          ) { 
       	result = rec_change_lhs_to_vivalue(d->u.hrd.arc[ci].child); 
      } 
    }
    else for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_change_lhs_to_vivalue(hc->child);
      result = red_bop(OR, result, 
        hrd_one_constraint(child, d->u.hrd.hrd_exp, 
          d->u.hrd.arc[ci].ub_numerator, 
          d->u.hrd.arc[ci].ub_denominator
      ) );
    }
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_FLOAT: 
    if (d->var_index == LVI_CHANGE) 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = fdd_one_constraint(
          d->u.fdd.arc[ci].child, FLOAT_VALUE, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = rec_change_lhs_to_vivalue(d->u.fdd.arc[ci].child);
        child = fdd_one_constraint(
          child, d->var_index, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
      }
    break;

  case TYPE_DOUBLE: 
    if (d->var_index == LVI_CHANGE) 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = dfdd_one_constraint(
          d->u.dfdd.arc[ci].child, DOUBLE_VALUE, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = rec_change_lhs_to_vivalue(d->u.dfdd.arc[ci].child);
        child = dfdd_one_constraint(
          child, d->var_index, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, child);
      }
    break;

  default: 
    if (d->var_index == LVI_CHANGE) 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]); 
        child = ddd_one_constraint(
          ic->child, VI_VALUE, ic->lower_bound, ic->upper_bound
        );
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]); 
        child = rec_change_lhs_to_vivalue(ic->child);
        child = ddd_one_constraint(
          child, d->var_index, ic->lower_bound, ic->upper_bound
        );
        result = red_bop(OR, result, child);
      }
  }

  return(ce->result = result);
}
  /* rec_change_lhs_to_vivalue() */  





struct red_type	*red_change_lhs_to_vivalue(
  struct red_type	*d, 
  int			lvi
) { 
  struct red_type	*result; 
  
  LVI_CHANGE = lvi; 
  result = rec_change_lhs_to_vivalue(d); 
  
  return(result); 	
}
  /* red_change_lhs_to_vivalue() */ 
  
  
  
inline struct red_type	*red_discrete_assign_bottom_analysis_bck( 
  struct red_type	*d, 
  int			lvi, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float			ofub 
) { 
  if (olb > oub) { 
    switch (VAR[lvi].TYPE) {
    case TYPE_FLOAT: 
      d = fdd_one_constraint(d, lvi, oflb, ofub); 
      break; 
    case TYPE_DOUBLE: 
      d = dfdd_one_constraint(d, lvi, (double) oflb, (double) ofub); 
      break; 
    default: 
      d = ddd_one_constraint(d, lvi, (int) oflb, (int) ofub); 
      break; 
    }
  }
  else { 
    switch (VAR[lvi].TYPE) {
    case TYPE_FLOAT: 
      d = fdd_one_constraint(d, lvi, (float) olb, (float) oub); 
      break; 
    case TYPE_DOUBLE: 
      d = dfdd_one_constraint(d, lvi, (double) olb, (double) oub); 
      break; 
    default: 
      d = ddd_one_constraint(d, lvi, olb, oub); 
      break; 
    }
  } 
  d = red_variable_eliminate(d, lvi); 
  return(d); 
}
  /* red_discrete_assign_bottom_analysis_bck() */ 
  


 
  


  
inline struct red_type	*red_discrete_assign_offset_analysis_bck(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float 		ofub, 
  struct red_type	*offset
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_discrete_assign_bottom_analysis_bck(
      d, lvi, olb, oub, oflb, ofub  
    ); 
  } 
  else {
    RT[result] = red_variable_eliminate(
      red_bop(AND, offset, red_change_lhs_to_vivalue(d, lvi)), 
      VI_VALUE
    );
  } 
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_discrete_assign_offset_analysis_bck() */ 
  







inline struct red_type	*red_discrete_assign_lhs_analysis_bck(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 

  int			lvi, 
  struct red_type	*lopd, 
  int			olb, 
  int			oub, 
  float			oflb, 
  float			ofub, 
  struct red_type	*offset
) { 
  int	result, ci, lconj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    RT[result] = red_discrete_assign_offset_analysis_bck(
      d, act, pi, lvi, olb, oub, oflb, ofub, offset   
    ); 
  } 
  else for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
    RT[lconj = RT_TOP++] = red_bop(AND, lopd->u.ddd.arc[ci].child, d); 
    for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
	 lvi <= lopd->u.ddd.arc[ci].upper_bound; 
	 lvi++
	 ) {
      if (lvi == FLAG_NO_USE) 
        continue; 
      
      RT[result] = red_bop(OR, RT[result], 
        red_discrete_assign_offset_analysis_bck( 
          RT[lconj], act, pi, lvi, olb, oub, oflb, ofub, offset 
      ) ); 
    }
    RT_TOP--; // lconj 
  }
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_discrete_assign_lhs_analysis_bck() */



int	count_ada_bck = 0; 

struct red_type	*red_action_discrete_assign_bck(
  int			W, 
  struct statement_type	*act, 
  int			pi 
) {
  int 			lvi, lopdi, offset_lb, offset_ub, offseti; 
  float			offset_flb, offset_fub; 
  struct red_type	*result;

  lopdi = RT_TOP++; 
  offseti = RT_TOP++; 
/*
  fprintf(RED_OUT, "\nada_bck = %1d\n", ++count_ada_bck); 
  fflush(RED_OUT); 
*/  
  discrete_lhs_rhs_setup(RT[W], 
    act, pi, 
    &lvi, lopdi, 
    &offset_lb, &offset_ub, &offset_flb, &offset_fub, offseti
  ); 
  result = red_discrete_assign_lhs_analysis_bck(RT[W], act, pi, 
    lvi, RT[lopdi], 
    offset_lb, offset_ub, offset_flb, offset_fub, RT[offseti]  
  ); 
  RT_TOP = RT_TOP-2; // lopdi, offseti 
  
  return(result); 

}
/* red_action_discrete_assign_bck() */ 








/****************************************************
 *  Backward increment and decrement to discretes. 
 */
 


inline struct red_type	*red_discrete_inc_bottom_analysis_bck( 
  struct red_type	*d, 
  int			lvi, 
  int			olb, 
  int			oub, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  if (flag_dec) 
/* We feel that it does not make sense to check for the overflow in backward
 * analysis. 
    if (flag_abstract) 
*/
      return(red_inc_off(d, lvi, oub, olb)); 
/*
    else 
      return(red_inc(d, lvi, oub, olb)); 
*/
  else 
/* We feel that it does not make sense to check for the overflow in backward
 * analysis. 
    if (flag_abstract) 
*/
      return(red_inc_off(d, lvi, -1 * olb, -1 * oub));  
/*
    else 
      return(red_inc(d, lvi, -1 * olb, -1 * oub)); 
*/
}
  /* red_discrete_inc_bottom_analysis_bck() */ 
  
  
  
inline struct red_type	*red_discrete_inc_offset_analysis_bck(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  int			olb, 
  int			oub, 
  struct red_type	*offset, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_discrete_inc_bottom_analysis_bck(
      d, lvi, olb, oub, flag_dec, flag_abstract
    ); 
  } 
  else for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
    RT[conj = RT_TOP++] = red_discrete_inc_bottom_analysis_bck(
      d, 
      lvi, 
      offset->u.ddd.arc[ci].lower_bound, 
      offset->u.ddd.arc[ci].upper_bound, 
      flag_dec, flag_abstract
    ); 
    RT[conj] = red_bop(AND, RT[conj], offset->u.ddd.arc[ci].child); 
    RT[result] = red_bop(OR, RT[result], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_discrete_inc_offset_analysis_bck() */ 
  



inline struct red_type	*red_discrete_inc_lhs_analysis_bck(
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lvi, 
  struct red_type	*lopd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset, 
  int			flag_dec, 
  int			flag_abstract 
) { 
  int	result, ci, lconj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    RT[result] = red_discrete_inc_offset_analysis_bck(
      d, act, pi, lvi, olb, oub, offset, flag_dec, flag_abstract  
    ); 
  } 
  else for (ci = 0; ci < lopd->u.ddd.child_count; ci++) { 
    RT[lconj = RT_TOP++] = NORM_FALSE; 
    for (lvi = lopd->u.ddd.arc[ci].lower_bound; 
	 lvi <= lopd->u.ddd.arc[ci].upper_bound; 
	 lvi++
	 ) {
      if (lvi == FLAG_NO_USE) 
        continue; 
      
      RT[lconj] = red_bop(OR, RT[lconj], 
        red_discrete_inc_offset_analysis_bck( 
          d, act, pi, lvi, olb, oub, offset, flag_dec, flag_abstract 
      ) ); 
    }
    RT[lconj] = red_bop(AND, lopd->u.ddd.arc[ci].child, RT[lconj]); 
    RT[result] = red_bop(OR, RT[result], RT[lconj]); 
    RT_TOP--; // lconj 
  }
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_discrete_inc_lhs_analysis_bck() */




struct red_type	*red_action_discrete_inc_bck(
  int			W, 
  struct statement_type	*act, 
  int			pi, 
  int			flag_dec, 
  int			flag_abstract
) {
  int 			lvi, lopdi, offset_lb, offset_ub, offseti;  
  float			offset_flb, offset_fub; 
  struct red_type	*result; 

  lopdi = RT_TOP++; 
  offseti = RT_TOP++; 
  discrete_lhs_rhs_setup(RT[W], 
    act, pi, 
    &lvi, lopdi, 
    &offset_lb, &offset_ub, &offset_flb, &offset_fub, offseti
  ); 
  result = red_discrete_inc_lhs_analysis_bck(RT[W], act, pi, 
    lvi, RT[lopdi], 
    offset_lb, offset_ub, RT[offseti], 
    flag_dec, flag_abstract 
  ); 
  RT_TOP = RT_TOP-2; // lopdi, offseti 
  
  return(result); 

}
/* red_action_discrete_inc_bck() */ 





/**********************************************
 *  Backward assignment to clocks. 
 */


struct red_type	*rec_clock_assign_bck(d) 
     struct red_type	*d; 
{
  int				b, ci, c1, c2;
  struct red_type		*new_child, *result;
  struct crd_child_type		*bc; 
  struct ddd_child_type		*ic; 
  struct cache4_hash_entry_type	*ce; 
    
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return(d); 

  ce = cache4_check_result_key(
    OP_CLOCK_ASSIGN_BCK, d, 
    (struct hrd_exp_type *) MIC_LCI, 
    MIC_RCI, 
    MIC_OFFSET_LB * CLOCK_POS_INFINITY + MIC_OFFSET_UB  
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_2_constraints(
      rec_clock_assign_bck(d->u.bdd.zero_child), 
      rec_clock_assign_bck(d->u.bdd.one_child), 
      d->var_index 
    );
    break; 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == MIC_LCI) { 
      if (c2 == MIC_RCI) { 
      /* if it is the difference between the source and destination, 
         then delete it. 
       */ 
        for (ci = d->u.crd.child_count-1; 
             ci >= 0 && MIC_OFFSET_UB <= d->u.crd.arc[ci].upper_bound;
             ci--
             ) {
          new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child);
	  result = red_bop(OR, result, new_child); 
	}
      } 
      else if (!c2) { 
      	for (ci = d->u.crd.child_count-1; 
      	        ci >= 0 
      	     && (b = zone_ub_subtract(
      	           d->u.crd.arc[ci].upper_bound, MIC_OFFSET_LB
      	         ) ) >= 0;
      	     ci--
      	     ) {
      	  new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child); 
      	  result = red_bop(OR, result, 
      	  		   crd_one_constraint(new_child, ZONE[MIC_RCI][0], b)
      	  		   ); 
      	}
      }
      else { 
      	for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	  b = zone_ub_subtract(d->u.crd.arc[ci].upper_bound, MIC_OFFSET_LB); 
	  new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child); 
      	  result = red_bop(OR, result, 
      	  		   crd_one_constraint(new_child, ZONE[MIC_RCI][c2], b)
      	  		   ); 
      	}
      } 
    } 
    else if (c2 == MIC_LCI) { 
      if (c1 == MIC_RCI) { 
        for (ci = d->u.crd.child_count-1; 
             ci >= 0 && (MIC_OFFSET_UB + d->u.crd.arc[ci].upper_bound) >= 0;
             ci--
             ) { 
	  new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child);
	  result = red_bop(OR, result, new_child); 
	}
      } 
      else if (!c1) { 
      	for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, MIC_OFFSET_UB); 
	  if (b > 0)
	    b = 0;
 	  new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child); 
      	  result = red_bop(OR, result, 
      	  		   crd_one_constraint(new_child, ZONE[0][MIC_RCI], b)
      	  		   ); 
      	}
      }
      else { 
      	for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, MIC_OFFSET_UB); 
	  new_child = rec_clock_assign_bck(d->u.crd.arc[ci].child); 
	  result = red_bop(OR, result, 
      	  		   crd_one_constraint(new_child, ZONE[c1][MIC_RCI], b)
      	  		   ); 
      	}
      } 
    } 
    else { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	bc = &(d->u.crd.arc[ci]); 
	new_child = rec_clock_assign_bck(bc->child); 
	result = red_bop(OR, result,
			 crd_one_constraint(new_child, d->var_index, bc->upper_bound)
			 ); 
      }
    }
    break; 

  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(d->u.ddd.arc[ci]); 
      new_child = rec_clock_assign_bck(ic->child);
      result = red_bop(OR, result,
		       ddd_one_constraint(new_child, d->var_index, 
		       			       ic->lower_bound, ic->upper_bound
		       			       )
		       ); 
    }
  }
  return(ce->result = result); 
}
/* rec_clock_assign_bck() */ 






struct red_type	*red_clock_assign_bck(d, lci, rci, offset_lb, offset_ub)
     struct red_type	*d; 
     int		lci, rci, offset_lb, offset_ub; 
{
  struct red_type	*result; 
  int			ub, v;

  MIC_LCI = lci; 
  MIC_RCI = rci;
  MIC_OFFSET_LB = offset_lb; 
  MIC_OFFSET_UB = offset_ub; 

  result = rec_clock_assign_bck(d); 

  d = crd_one_constraint(result, ZONE[0][lci], 0); 

  return(d);
}
/* red_clock_assign_bck() */



inline struct red_type 	*red_clock_assign_bottom_analysis_bck( 
  struct red_type	*d, 
  int			lci, 
  int			rci, 
  int			olb, 
  int			oub, 
  int			flag_abstract
) { 
  int	result; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lci == rci) { 
    if (olb != 0 || oub != 0) { 
      RT[result] = red_time_clock_inc(d, lci, -1*oub, -1*olb); 
    } 
    else 
      RT[result] = d;
  } 
  else if (flag_abstract || FLAG_STATEMENT_POLARITY > 0) { 
    if (rci == 0) { 
      RT[result] = crd_one_constraint(d, ZONE[lci][0], oub);
      RT[result] = crd_one_constraint(RT[result], ZONE[0][lci], -1*olb); 
      RT[result] = red_time_clock_eliminate(RT[result], lci); 
    } 
    else { 
      RT[result] = red_time_clock_magnitude_inc(d, lci, rci, -1*oub, -1*olb); 
      RT[result] = red_time_clock_eliminate(RT[result], lci); 
      RT[result] = crd_one_constraint(RT[result], ZONE[0][lci], 0); 
    } 
  }
  else { 
    RT[result] = red_clock_assign_bck(d, lci, rci, olb, oub); 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_clock_assign_bottom_analysis_bck() */  





inline struct red_type	*red_clock_assign_offset_analysis_bck( 
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lci, 
  int			rci, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, ci, conj; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (offset == NULL) { 
    RT[result] = red_clock_assign_bottom_analysis_bck( 
      d, lci, rci, olb, oub, flag_abstract
    ); 
  }
  else for (ci = 0; ci < offset->u.ddd.child_count; ci++) { 
    conj = RT_TOP++; 
    olb = 2*offset->u.ddd.arc[ci].lower_bound; 
    oub = 2*offset->u.ddd.arc[ci].upper_bound; 
    RT[conj] = red_clock_assign_bottom_analysis_bck( 
      d, lci, rci, olb, oub, flag_abstract
    ); 
    RT[conj] = red_bop(AND, RT[conj], offset->u.ddd.arc[ci].child); 
    RT[result] = red_bop(OR, RT[result], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_offset_analysis_bck() */ 
  
  
  
  
 
inline struct red_type	*red_clock_assign_rhs_analysis_bck( 
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  int			lci, 
  struct ps_exp_type	*rvar, 
  int			rpi, 
  struct red_type	*ropd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, rvi, rci, ci, rconj, rppi; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (rvar == NULL) { 
    RT[result] = red_clock_assign_offset_analysis_bck( 
      d, act, pi, lci, 0, olb, oub, offset, flag_abstract
    ); 
  } 
  else if (ropd == NULL) { 
    rvi = rvar->u.atom.var_index;
    rvi = variable_index[TYPE_CLOCK][rpi][VAR[rvi].OFFSET];        
    rci = VAR[rvi].U.CLOCK.CLOCK_INDEX; 
    RT[result] = red_clock_assign_offset_analysis_bck(
      d, act, pi, 
      lci,  
      rci, 
      olb, oub, offset, 
      flag_abstract
    ); 
  }
  else for (ci = 0; ci < ropd->u.ddd.child_count; ci++) { 
    for (rppi = ropd->u.ddd.arc[ci].lower_bound; 
	 rppi <= ropd->u.ddd.arc[ci].upper_bound; 
	 rppi++
	 ) {
      rvi = rvar->u.atom.var_index;
      rvi = variable_index[TYPE_CLOCK][rppi][VAR[rvi].OFFSET];
      rci = VAR[rvi].U.CLOCK.CLOCK_INDEX; 
      RT[rconj = RT_TOP++] = red_clock_assign_offset_analysis_bck(
        d, act, pi, 
        lci, 
        rci, 
        olb, oub, offset, 
        flag_abstract
      ); 
      RT[rconj] = red_bop(AND, RT[rconj], ropd->u.ddd.arc[ci].child); 
      RT[result] = red_bop(OR, RT[result], RT[rconj]); 
      RT_TOP--; // rconj 
    } 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_rhs_analysis_bck() */ 
  
  
  



inline struct red_type	*red_clock_assign_lhs_analysis_bck( 
  struct red_type	*d, 
  struct statement_type	*act, 
  int			pi, 
  struct ps_exp_type	*lvar, 
  int			lpi, 
  struct red_type	*lopd, 
  struct ps_exp_type	*rvar, 
  int			rpi, 
  struct red_type	*ropd, 
  int			olb, 
  int			oub, 
  struct red_type	*offset,  
  int			flag_abstract   
) { 
  int	result, lvi, lci, ci, lconj, lppi; 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (lopd == NULL) { 
    lvi = lvar->u.atom.var_index;
    lvi = variable_index[TYPE_CLOCK][lpi][VAR[lvi].OFFSET];        
    lci = VAR[lvi].U.CLOCK.CLOCK_INDEX;
    RT[result] = red_clock_assign_rhs_analysis_bck(
      d, act, pi, 
      lci,  
      rvar, rpi, ropd, 
      olb, oub, offset, 
      flag_abstract
    ); 
  }
  else for (ci = 0; ci < lopd->u.ddd.child_count; ci++) {
    for (lppi = lopd->u.ddd.arc[ci].lower_bound; 
	 lppi <= lopd->u.ddd.arc[ci].upper_bound; 
	 lppi++
	 ) {
      lvi = lvar->u.atom.var_index; 
      lvi = variable_index[TYPE_CLOCK][lppi][VAR[lvi].OFFSET];
      lci = VAR[lvi].U.CLOCK.CLOCK_INDEX; 
      
      RT[lconj = RT_TOP++] = red_clock_assign_rhs_analysis_bck(
        d, act, pi, 
        lci, 
        rvar, rpi, ropd, 
        olb, oub, offset, 
        flag_abstract
      ); 
      RT[lconj] = red_bop(AND, RT[lconj], lopd->u.ddd.arc[ci].child); 
      RT[result] = red_bop(OR, RT[result], RT[lconj]); 
      RT_TOP--; // rconj 
    } 
  } 
  RT_TOP--; // result 
  return(RT[result]); 
} 
  /* red_clock_assign_lhs_analysis_bck() */ 
  
  
  
  
   
struct red_type	*red_action_clock_assign_bck(W, act, pi, flag_abs)
     int			W, pi, flag_abs;
     struct statement_type	*act;
{
  int			lpi, rpi, olb, oub, lopdi, ropdi, offseti;
  struct ps_exp_type	*lvar, *rvar; 

  lopdi = RT_TOP++; 
  ropdi = RT_TOP++;  // for lopd and ropd 
  offseti = RT_TOP++; 
  clock_assign_setup(RT[W], 
    act, pi, 
    &lvar, &lpi, lopdi, 
    &rvar, &rpi, ropdi, 
    &olb, &oub, offseti
  ); 
  RT[W] = red_clock_assign_lhs_analysis_bck( 
    RT[W], act, pi, 
    lvar, lpi, RT[lopdi], 
    rvar, rpi, RT[ropdi], 
    olb, oub, RT[offseti],  
    flag_abs  
  ); 
  RT_TOP = RT_TOP-3; // lopdi, ropdi, offseti 
  return(RT[W]); 
}
/* red_action_clock_assign_bck() */ 





struct red_type	*red_action_discrete_assign_constant_bck(
  int			W,
  struct statement_type	*st, 
  int			pi  
) {
  if (   check_oapprox_lazy_exp()
      && st->u.act.lhs->u.atom.exp_base_proc_index->type != TYPE_CONSTANT
      && st->u.act.lhs->u.atom.exp_base_proc_index 
         != PS_EXP_LOCAL_IDENTIFIER
      && st->u.act.lhs->u.atom.exp_base_proc_index  
         != PS_EXP_GLOBAL_IDENTIFIER
      ) 
    return(red_variable_sim_eliminate(
      RT[W], st->u.act.lhs->u.atom.var_index
    ) ); 
  else 
    return(red_action_discrete_assign_bck(W, st, pi));
}
  /* red_action_discrete_assign_constant_bck() */ 




struct red_type	*red_action_discrete_assign_polynomial_bck( 
  int			W,
  struct statement_type	*st, 
  int			pi  
) { 
  if (check_oapprox_lazy_exp()) {
    struct ps_exp_type	*lhs; 
    int			vi, vtype, voffset; 
      
    lhs = st->u.act.lhs; 
    vi = lhs->u.atom.var_index; 
    vtype = VAR[vi].TYPE; 
    voffset = VAR[vi].OFFSET; 
    switch (st->u.act.lhs->u.atom.exp_base_proc_index->type) {
    case TYPE_NULL: 
      return(red_variable_eliminate(RT[W], vi)); 
    case TYPE_CONSTANT: 
      return(red_variable_eliminate(RT[W], 
        variable_index
          [vtype]
          [lhs->u.atom.exp_base_proc_index->u.value]
          [voffset]
      ) ); 
    case TYPE_LOCAL_IDENTIFIER: 
      return(red_variable_eliminate(RT[W], 
        variable_index[vtype][FLAG_STATEMENT_PI][voffset]
      ) ); 
    default: 
      return(red_variable_sim_eliminate(RT[W], vi)); 
    }
  }
  else 
    return(red_action_discrete_assign_bck(
      W, st, FLAG_STATEMENT_PI 
    ) );
}
  /* red_action_discrete_assign_polynomial_bck() */ 









struct red_type	*rec_statement_untimed_bck(W, st)
     int			W;
     struct statement_type	*st;
{
  int	red_if, red_else, cur, reachable, i, ipi, lvi, ci, pi, flag;

  if (!st) 
    return(RT[W]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[W]);  
  case ST_IF: 
    RT[red_if = RT_TOP++] 
    = rec_statement_untimed_bck(W, st->u.branch.if_statement); 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) 
      RT[red_if] = red_bop(AND, RT[W], 
        st->u.branch.red_cond[FLAG_STATEMENT_PI]
      ); 
    else 
      RT[red_if] = red_delayed_eval( 
        st->u.branch.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W] 
      ); 
    
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[W] = rec_statement_untimed_bck(W, st->u.branch.else_statement); 
    } 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) 
      RT[W] = red_bop(AND, RT[W], st->u.branch.red_uncond[FLAG_STATEMENT_PI]); 
    else 
      RT[W] = red_delayed_eval(st->u.branch.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    RT[W] = red_bop(OR, RT[red_if], RT[W]); 
    RT_TOP--; /* RT_TOP++ */ 
    return(RT[W]); 
    break; 
  case ST_WHILE: 
    /* The precondition consists of (1) the case for the infinite loop and 
     * (2) the case for the finite-loop.  
     * The case for the infinite-loop is a greatest fixpoint.  
     * The case for the finite-loop is a least fixpoint. 
     */
    /* First calculate the finite-loop case. */ 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) 
      RT[cur = RT_TOP++] 
      = RT[W] 
      = red_bop(AND, RT[W], st->u.loop.red_uncond[FLAG_STATEMENT_PI]); 
    else 
      RT[cur = RT_TOP++] 
      = RT[W] 
      = red_delayed_eval(st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W] 
      ); 
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_untimed_bck(cur, st->u.loop.statement); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) 
        RT[cur] = red_bop(AND, RT[cur], 
          st->u.loop.red_cond[FLAG_STATEMENT_PI]
        ); 
      else 
        RT[cur] = red_delayed_eval( 
          st->u.loop.red_cond[FLAG_STATEMENT_PI],FLAG_STATEMENT_PI, RT[cur]
        ); 
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[W]); 
      RT[W] = red_bop(OR, RT[W], RT[cur]); 
    } 
    
    /* Now we calculate the infinite-loop case.  
     * It is better if this can be done once. 
     */ 
    if (st->u.loop.red_gfp[FLAG_STATEMENT_PI]) { 
      RT[W] = red_bop(OR, RT[W], st->u.loop.red_gfp[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[cur] = st->u.loop.red_cond[FLAG_STATEMENT_PI]; 
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (; RT[cur] != RT[reachable]; ) { 
        RT[reachable] = RT[cur]; 
        RT[cur] = rec_statement_untimed_bck(cur, st->u.loop.statement); 
        RT[cur] = red_bop(AND, RT[cur], RT[reachable]); 
      } 
      RT[W] = red_bop(OR, RT[W], RT[reachable]); 
      st->u.loop.red_gfp[FLAG_STATEMENT_PI] = RT[reachable]; 
      red_mark(st->u.loop.red_gfp[FLAG_STATEMENT_PI], FLAG_GC_WHILE_GFP); 
      RT_TOP--; /* reachable */ 
    }
    RT_TOP--; /* cur */ 
    return(RT[W]);   
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count - 1; i >= 0; i--) { 
      RT[W] = rec_statement_untimed_bck(W, st->u.seq.statement[i]); 
    } 
    return(RT[W]); 
    break; 
  case ST_CALL: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure calls.\n"
    ); 
    bk(0); 
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure returns.\n"
    ); 
    bk(0); 
    break; 
  case ST_CPLUG: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of C-plugins.\n"
    ); 
    bk(0); 
    break; 
  case ST_GUARD: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[W] = red_bop(AND, RT[W], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[W] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    return(RT[W]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[W] = red_variable_eliminate(RT[W], lvi);
      return(RT[W]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[W] = red_variable_eliminate(RT[W], lvi);
        return(RT[W]); 
      } 
      else { 
      	RT[cur = RT_TOP++] = NORM_FALSE; 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[cur] = red_bop(OR, RT[cur], red_variable_eliminate(RT[W], lvi));  
        } 
        RT_TOP--; // cur 
        return(RT[cur]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    return(red_action_discrete_assign_constant_bck(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    return(red_action_discrete_assign_polynomial_bck(
      W, st, FLAG_STATEMENT_PI 
    ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    return(red_action_clock_assign_bck(
        W, st, FLAG_STATEMENT_PI, FLAG_ACTION_ABSTRACT 
    ) );
  case ASSIGN_HYBRID_EXP:
    if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      return(red_action_hybrid(W, &(st->u.act), FLAG_STATEMENT_PI));
    }
    else {
      int  addr; 
    	
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) 
        RT[addr = RT_TOP++] = red_operand_indirection(
          st->u.act.lhs, FLAG_STATEMENT_PI
        ); 
      else 
        RT[addr = RT_TOP++] = red_delayed_operand_indirection(
          st->u.act.lhs, FLAG_STATEMENT_PI, RT[W]  
        ); 
        
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (ci = 0; ci < RT[addr]->u.ddd.child_count; ci++) {
        for (lvi = RT[addr]->u.ddd.arc[ci].lower_bound; 
             lvi <= RT[addr]->u.ddd.arc[ci].upper_bound; 
             lvi++
             ) { 
          if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
              == FLAG_ACTION_LAZY_EVAL
              ) 
            RT[cur = RT_TOP++] = red_bop(AND,  
              st->u.act.red_effect[FLAG_STATEMENT_PI], RT[W] 
            ); 
          else 
            RT[cur = RT_TOP++] = red_delayed_eval( 
              st->u.act.red_effect[FLAG_STATEMENT_PI], 
              FLAG_STATEMENT_PI, RT[W]
            );
          RT[cur] = hybrid_bypass_DOWNWARD(cur, lvi);
          RT[cur] = red_variable_eliminate(RT[cur], lvi);
          RT[reachable] = red_bop(OR, RT[cur], RT[reachable]); 
          RT_TOP--; 
        }
      }
      RT_TOP--; /* reachable */ 
      RT_TOP--; /* addr */ 
      return(RT[W] = RT[reachable]);
    }
    break;
  case INCREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_ABSTRACT
    ) );
  case DECREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_ABSTRACT
    ) );
  } 
}
  /* rec_statement_untimed_bck() */ 
  
  
struct red_type	*red_statement_untimed_bck(
  int			dst, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_lazy_eval
) { 
  int			original_action_stage; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  FLAG_STATEMENT_PI = pi; 
  
  result = rec_statement_untimed_bck(dst, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  return(result); 
} 
  /* red_statement_untimed_bck() */ 
  
  




struct red_type	*rec_statement_abstract_bck(W, st)
     int			W;
     struct statement_type	*st;
{
  int	red_if, red_else, cur, reachable, i, lvi, ipi, ci, pi, flag;

  if (!st) 
    return(RT[W]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[W]);  
  case ST_IF: 
    RT[red_if = RT_TOP++] 
    = rec_statement_abstract_bck(W, st->u.branch.if_statement); 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_if] = red_bop(AND, RT[W], 
        st->u.branch.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[red_if] = red_delayed_eval( 
        st->u.branch.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[W] 
      ); 
    }
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[W] = rec_statement_abstract_bck(W, st->u.branch.else_statement); 
    } 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[W] = red_bop(AND, RT[W], 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[W] = red_delayed_eval( 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    RT[W] = red_bop(OR, RT[red_if], RT[W]); 
    RT_TOP--; /* RT_TOP++ */ 
    return(RT[W]); 
    break; 
  case ST_WHILE: 
    /* The precondition consists of (1) the case for the infinite loop and 
     * (2) the case for the finite-loop.  
     * The case for the infinite-loop is a greatest fixpoint.  
     * The case for the finite-loop is a least fixpoint. 
     */
    /* First calculate the finite-loop case. */ 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[cur = RT_TOP++] 
      = RT[W] 
      = red_bop(AND, RT[W], st->u.loop.red_uncond[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[cur = RT_TOP++] 
      = RT[W] 
      = red_delayed_eval(st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]       
      ); 
    }
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_abstract_bck(cur, st->u.loop.statement); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[cur] = red_bop(AND, RT[cur], 
          st->u.loop.red_cond[FLAG_STATEMENT_PI]
        ); 
      } 
      else {
        RT[cur] = red_delayed_eval( 
          st->u.loop.red_cond[FLAG_STATEMENT_PI], 
          FLAG_STATEMENT_PI, RT[cur] 
        ); 
      } 
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[W]); 
      RT[W] = red_bop(OR, RT[W], RT[cur]); 
    } 
    
    /* Now we calculate the infinite-loop case.  
     * It is better if this can be done once. 
     */ 
    if (st->u.loop.red_gfp[FLAG_STATEMENT_PI]) { 
      RT[W] = red_bop(OR, RT[W], st->u.loop.red_gfp[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[cur] = st->u.loop.red_cond[FLAG_STATEMENT_PI]; 
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (; RT[cur] != RT[reachable]; ) { 
        RT[reachable] = RT[cur]; 
        RT[cur] = rec_statement_abstract_bck(cur, st->u.loop.statement); 
        RT[cur] = red_bop(AND, RT[cur], RT[reachable]); 
      } 
      RT[W] = red_bop(OR, RT[W], RT[reachable]); 
      st->u.loop.red_gfp[FLAG_STATEMENT_PI] = RT[reachable]; 
      red_mark(st->u.loop.red_gfp[FLAG_STATEMENT_PI], FLAG_GC_WHILE_GFP); 
      RT_TOP--; /* reachable */ 
    }
    RT_TOP--; /* cur */ 
    return(RT[W]);   
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count - 1; i >= 0; i--) { 
      RT[W] = rec_statement_abstract_bck(W, st->u.seq.statement[i]); 
    } 
    return(RT[W]); 
    break; 
  case ST_CALL: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure calls.\n"
    ); 
    bk(0); 
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure returns.\n"
    ); 
    bk(0); 
    break; 
  case ST_CPLUG: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of C-plugins.\n"
    ); 
    bk(0); 
    break; 
  case ST_GUARD: 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[W] = red_bop(AND, RT[W], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[W] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[W]
      ); 
    } 
    return(RT[W]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[W] = red_variable_eliminate(RT[W], lvi);
      return(RT[W]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[W] = red_variable_eliminate(RT[W], lvi);
        return(RT[W]); 
      } 
      else { 
      	RT[cur = RT_TOP++] = NORM_FALSE; 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[cur] = red_bop(OR, RT[cur], red_variable_eliminate(RT[W], lvi));  
        } 
        RT_TOP--; // cur 
        return(RT[cur]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    return(red_action_discrete_assign_constant_bck(
      W, st, FLAG_STATEMENT_PI 
    ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    return(red_action_discrete_assign_polynomial_bck(
      W, st, FLAG_STATEMENT_PI 
    ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        ) {
      fprintf(RED_OUT, "\nred_effect on lvi = %1d:%s:\n", 
        lvi, VAR[lvi].NAME
      ); 
    } 
    if (st->u.act.red_effect[FLAG_STATEMENT_PI]) {
      red_print_graph(st->u.act.red_effect[FLAG_STATEMENT_PI]); 
    } 
    return(red_action_clock_assign_bck(
        W, st, FLAG_STATEMENT_PI, FLAG_ACTION_ABSTRACT 
    ) );
  case ASSIGN_HYBRID_EXP:
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        ) {
      fprintf(RED_OUT, "\nred_effect on lvi = %1d:%s:\n", 
        lvi, VAR[lvi].NAME
      ); 
    } 
    if (st->u.act.red_effect[FLAG_STATEMENT_PI]) {
      red_print_graph(st->u.act.red_effect[FLAG_STATEMENT_PI]); 
    } 
    if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      return(red_action_hybrid(W, &(st->u.act), FLAG_STATEMENT_PI));
    }
    else {
      int  addr; 

      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[addr = RT_TOP++] = red_operand_indirection(
          st->u.act.lhs, FLAG_STATEMENT_PI
        ); 
      }
      else 
        RT[addr = RT_TOP++] = red_delayed_operand_indirection(
          st->u.act.lhs, FLAG_STATEMENT_PI, RT[W]  
        ); 
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (ci = 0; ci < RT[addr]->u.ddd.child_count; ci++) {
        for (lvi = RT[addr]->u.ddd.arc[ci].lower_bound; 
             lvi <= RT[addr]->u.ddd.arc[ci].upper_bound; 
             lvi++
             ) { 
          if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
              == FLAG_ACTION_LAZY_EVAL
              ) {
            RT[cur = RT_TOP++] = red_bop(AND, 
              st->u.act.red_effect[FLAG_STATEMENT_PI], RT[W] 
            ); 
          }
          else { 
            RT[cur = RT_TOP++] = red_delayed_eval( 
              st->u.act.red_effect[FLAG_STATEMENT_PI], 
              FLAG_STATEMENT_PI, RT[W] 
            ); 
          }
          RT[cur] = hybrid_bypass_DOWNWARD(cur, lvi);
          RT[cur] = red_variable_eliminate(RT[cur], lvi);
          RT[reachable] = red_bop(OR, RT[cur], RT[reachable]); 
          RT_TOP--; 
        }
      }
      RT_TOP--; /* reachable */ 
      RT_TOP--; /* addr */ 
      return(RT[W] = RT[reachable]);
    }
    break;
  case INCREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_ABSTRACT
    ) );
  case DECREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_fwd(W, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_ABSTRACT
    ) );
  } 
}
  /* rec_statement_abstract_bck() */ 
  
  
struct red_type	*red_statement_abstract_bck(
  int			dst, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_lazy_eval
) { 
  int			original_action_stage; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  FLAG_STATEMENT_PI = pi; 
  
  result = rec_statement_abstract_bck(dst, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  return(result); 
} 
  /* red_statement_abstract_bck() */ 
  
  
  
int count_statement_bck = 0; 


struct red_type	*rec_statement_bck(
  int			dst, 
  struct statement_type	*st 
) {
  int			red_if, red_else, cur, 
			reachable, i, lvi, ipi, ci, result, pi, flag;
  struct red_type	*red_addr; 

  if (!st) 
    return(RT[dst]); 
  
  switch (st->op) { 
  case UNCHANGED: 
    return(RT[dst]);  
  case ST_IF: 
    RT[cur = RT_TOP++] = RT[dst]; 
    RT[red_if = RT_TOP++] = rec_statement_bck(dst, st->u.branch.if_statement); 
    #if RED_DEBUG_ACTION_MODE
    fprintf(RED_OUT, 
      "\nP%1d,X%1d: After rec_statement_bck for if-statement\n", 
      ITERATE_PI, ITERATE_XI
    ); 
    red_print_graph(RT[red_if]); 
    #endif 

    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_if] = red_bop(AND, RT[red_if], 
        st->u.branch.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[red_if] = red_delayed_eval( 
        st->u.branch.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[red_if] 
      ); 
    } 
    #if RED_DEBUG_ACTION_MODE
    fprintf(RED_OUT, 
      "\nP%1d,X%1d: After rec_statement_bck for if-condition\n", 
      ITERATE_PI, ITERATE_XI
    ); 
    red_print_graph(st->u.branch.red_cond[FLAG_STATEMENT_PI]); 
    fprintf(RED_OUT, 
      "\nP%1d,X%1d: After rec_statement_bck for if-conj\n", 
      ITERATE_PI, ITERATE_XI
    ); 
    red_print_graph(RT[red_if]); 
    #endif 
    
    RT[red_else = RT_TOP++] = RT[dst]; 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      RT[red_else] = rec_statement_bck(red_else, st->u.branch.else_statement); 
      #if RED_DEBUG_ACTION_MODE
      fprintf(RED_OUT, 
        "\nP%1d,X%1d: After rec_statement_bck for else-statement\n", 
        ITERATE_PI, ITERATE_XI
      ); 
      red_print_graph(RT[red_else]); 
      #endif 
    } 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[red_else] = red_bop(AND, RT[red_else], 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[red_else] = red_delayed_eval( 
        st->u.branch.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[red_else]
      ); 
    } 
    #if RED_DEBUG_ACTION_MODE
    fprintf(RED_OUT, 
      "\nP%1d,X%1d: After rec_statement_bck for else-conj\n", 
      ITERATE_PI, ITERATE_XI
    ); 
    red_print_graph(RT[red_else]); 
    #endif 
    
    RT[red_if] = red_bop(OR, RT[red_if], RT[red_else]);     

    #if RED_DEBUG_ACTION_MODE
    fprintf(RED_OUT, 
      "P%1d,X%1d: in red_if() bck for pi=%1d\n", 
      ITERATE_PI, ITERATE_XI, FLAG_STATEMENT_PI
    ); 
    print_statement_line(st, FLAG_STATEMENT_PI); 
    fprintf(RED_OUT, "\n"); 
    red_print_graph(RT[cur]); 
    
    fprintf(RED_OUT, "P%1d,X%1d: after red_if() bck\n", 
      ITERATE_PI, ITERATE_XI
    ); 
    red_print_graph(RT[red_if]); 
    #endif 
    RT_TOP--; /* red_else */ 
    RT_TOP--; /* red_if */ 
    RT_TOP--; /* cur */ 
    
    return(RT[red_if]); 
    break; 
  case ST_WHILE: 
    /* The precondition consists of (1) the case for the infinite loop and 
     * (2) the case for the finite-loop.  
     * The case for the infinite-loop is a greatest fixpoint.  
     * The case for the finite-loop is a least fixpoint. 
     */
    /* First calculate the finite-loop case. */ 
    RT[result = RT_TOP++] = RT[dst]; 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[cur = RT_TOP++] 
      = RT[result] 
      = red_bop(AND, RT[result], st->u.loop.red_uncond[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[cur = RT_TOP++] 
      = RT[result] 
      = red_delayed_eval(st->u.loop.red_uncond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[result] 
      ); 
    } 
    for (; RT[cur] != NORM_FALSE; ) { 
      RT[cur] = rec_statement_bck(cur, st->u.loop.statement); 
      if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
          == FLAG_ACTION_LAZY_EVAL
          ) {
        RT[cur] = red_bop(AND, RT[cur], 
          st->u.loop.red_cond[FLAG_STATEMENT_PI]
        ); 
      }
      else { 
        RT[cur] = red_delayed_eval( 
          st->u.loop.red_cond[FLAG_STATEMENT_PI], FLAG_STATEMENT_PI, RT[cur]
        ); 
      }
      RT[cur] = red_bop(EXCLUDE, RT[cur], RT[result]); 
      RT[result] = red_bop(OR, RT[result], RT[cur]); 
    } 
    
    /* Now we calculate the infinite-loop case.  
     * It is better if this can be done once. 
     */ 
    if (st->u.loop.red_gfp[FLAG_STATEMENT_PI]) { 
      RT[result] = red_bop(OR, RT[result], st->u.loop.red_gfp[FLAG_STATEMENT_PI]); 
    }
    else { 
      RT[cur] = st->u.loop.red_cond[FLAG_STATEMENT_PI]; 
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (; RT[cur] != RT[reachable]; ) { 
        RT[reachable] = RT[cur]; 
        RT[cur] = rec_statement_bck(cur, st->u.loop.statement); 
        RT[cur] = red_bop(AND, RT[cur], RT[reachable]); 
      } 
      RT[result] = red_bop(OR, RT[result], RT[reachable]); 
      st->u.loop.red_gfp[FLAG_STATEMENT_PI] = RT[reachable]; 
      red_mark(st->u.loop.red_gfp[FLAG_STATEMENT_PI], FLAG_GC_WHILE_GFP); 
      RT_TOP--; /* reachable */ 
    }
    RT_TOP = RT_TOP-2; /* cur, result */  
    return(RT[result]);   
    break; 
  case ST_SEQ: 
    RT[result = RT_TOP++] = RT[dst]; 
    for (i = st->u.seq.count-1; i>=0; i--) { 
      RT[result] = rec_statement_bck(result, st->u.seq.statement[i]); 
    } 
    RT_TOP--; // result 
    return(RT[result]); 
    break; 
  case ST_CALL: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure calls.\n"
    ); 
    bk(0); 
    break; 
  case ST_RETURN: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of procedure returns.\n"
    ); 
    bk(0); 
    break; 
  case ST_CPLUG: 
    fprintf(RED_OUT, 
      "\nSorry that we do not support backward analysis of C-plugins.\n"
    ); 
    bk(0); 
    break; 
  case ST_GUARD: 
    RT[result = RT_TOP++] = NORM_FALSE; 
    if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
        == FLAG_ACTION_LAZY_EVAL
        ) {
      RT[result] = red_bop(AND, RT[dst], 
        st->u.guard.red_cond[FLAG_STATEMENT_PI]
      ); 
    }
    else { 
      RT[result] = red_delayed_eval( 
        st->u.guard.red_cond[FLAG_STATEMENT_PI], 
        FLAG_STATEMENT_PI, RT[dst]
      ); 
    } 
    RT_TOP--; // result 
    return(RT[result]); 
    break; 
  case ST_ERASE:
    lvi = st->u.erase.var->u.atom.var_index; 
    RT[result = RT_TOP++] = NORM_FALSE; 
    if (VAR[lvi].PROC_INDEX == 0) { 
      RT[result] = red_variable_eliminate(RT[dst], lvi);
      RT_TOP--; // result 
      return(RT[result]); 
    } 
    else { 
      pi = get_address(st->u.erase.var->u.atom.exp_base_proc_index, 
        FLAG_STATEMENT_PI, &flag
      ); 
      if (flag == FLAG_SPECIFIC_VALUE) { 
        lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
        RT[result] = red_variable_eliminate(RT[dst], lvi);
        RT_TOP--; // result 
        return(RT[result]); 
      } 
      else { 
        for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
          lvi = variable_index[VAR[lvi].TYPE][pi][VAR[lvi].OFFSET]; 
          RT[result] = red_bop(OR, RT[result], red_variable_eliminate(RT[dst], lvi));  
        } 
        RT_TOP--; // result 
        return(RT[result]); 
      }
    }
    break; 

  case ASSIGN_DISCRETE_CONSTANT:
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
/*
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        ) {
      fprintf(RED_OUT, "\nDISCRETE effect %x on lvi = %1d:%s:\n", 
        st->u.act.red_effect, lvi, VAR[lvi].NAME
      ); 
    } 
    if (st->u.act.red_effect) {
      red_print_graph(st->u.act.red_effect[FLAG_STATEMENT_PI]); 
    } 
*/ 
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        && st->u.act.red_effect
        ) { 
      RT[result = RT_TOP++] = red_bop(AND, RT[dst], 
        st->u.act.red_effect[FLAG_STATEMENT_PI]
      ); 
      RT[result] = red_variable_eliminate(RT[result], lvi); 
      RT_TOP--; // result 
      return(RT[result]); 
    } 

    return(red_action_discrete_assign_constant_bck(
      dst, st, FLAG_STATEMENT_PI 
    ) );
  case ASSIGN_DISCRETE_POLYNOMIAL:
    return(red_action_discrete_assign_polynomial_bck(
      dst, st, FLAG_STATEMENT_PI 
    ) );
    break; 

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_DIFFERENCE: 
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
/*
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        ) { 
      fprintf(RED_OUT, "\nCLOCK effect %x on lvi %1d:%s\n", 
        st->u.act.red_effect, lvi, VAR[lvi].NAME 
      ); 
    } 
    if (st->u.act.red_effect) { 
      red_print_graph(st->u.act.red_effect[FLAG_STATEMENT_PI]); 
    } 
*/
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        && st->u.act.red_effect
        ) { 
      RT[result = RT_TOP++] = red_bop(AND, RT[dst], 
        st->u.act.red_effect[FLAG_STATEMENT_PI]
      ); 
//      RT[result] = red_bypass_DOWNWARD(result, VAR[lvi].U.CLOCK.CLOCK_INDEX); 
      RT[result] = red_time_clock_eliminate(
        RT[result], VAR[lvi].U.CLOCK.CLOCK_INDEX
      ); 
      RT_TOP--; // result 
      return(RT[result]); 
    } 

  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    return(red_action_clock_assign_bck(
        dst, st, FLAG_STATEMENT_PI, FLAG_ACTION_EXACT 
    ) );
  case ASSIGN_HYBRID_EXP:
    lvi = get_variable_index(st->u.act.lhs, FLAG_STATEMENT_PI); 
/*
    if (   lvi > 0 
        && lvi < VARIABLE_COUNT 
        ) { 
      fprintf(RED_OUT, "\nDENSE effect %x on lvi %1d:%s\n", 
        st->u.act.red_effect, lvi, VAR[lvi].NAME 
      ); 
    } 
    if (st->u.act.red_effect) { 
      red_print_graph(st->u.act.red_effect[FLAG_STATEMENT_PI]); 
    } 
*/
    if (lvi > 0 && lvi < VARIABLE_COUNT && st->u.act.red_effect) {
      if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      	RT[result = RT_TOP++] = red_switch_vi(
      	  st->u.act.red_effect[FLAG_STATEMENT_PI], 
      	  lvi, CLOCK[DELTAP]
      	); 
      }
      else 
        RT[result = RT_TOP++] = st->u.act.red_effect[FLAG_STATEMENT_PI]; 
      RT[result] = red_bop(AND, RT[dst], RT[result]); 
      RT[result] = hybrid_bypass_DOWNWARD(result, lvi); 
      RT[result] = red_variable_eliminate(RT[result], lvi); 
      if (st->st_status & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)) {
      	RT[result] = red_switch_vi(
      	  RT[result], lvi, CLOCK[DELTAP]
      	); 
      }
      RT_TOP--; // result 
      return(RT[result]); 
    } 

    if (  st->st_status 
        & (FLAG_ACTION_INDIRECTION | FLAG_ACTION_LHS_RECURSION)
        ) {
      return(red_action_hybrid(dst, &(st->u.act), FLAG_STATEMENT_PI));
    }
    else {
      int  addr; 

      RT[addr = RT_TOP++] = red_operand_indirection(
        st->u.act.lhs, FLAG_STATEMENT_PI 
      ); 
      RT[reachable = RT_TOP++] = NORM_FALSE; 
      for (ci = 0; ci < RT[addr]->u.ddd.child_count; ci++) {
        for (lvi = RT[addr]->u.ddd.arc[ci].lower_bound; 
             lvi <= RT[addr]->u.ddd.arc[ci].upper_bound; 
             lvi++
             ) { 
          if ((GSTATUS[INDEX_ACTION_STAGE_EVAL] & MASK_ACTION_STAGE_EVAL)
              == FLAG_ACTION_LAZY_EVAL
          ) { 
            RT[cur = RT_TOP++] = red_bop(AND, 
              st->u.act.red_effect[FLAG_STATEMENT_PI], 
              RT[dst]
            );
          }
          else { 
            RT[cur = RT_TOP++] = red_delayed_eval( 
              st->u.act.red_effect[FLAG_STATEMENT_PI], 
              FLAG_STATEMENT_PI, RT[dst]
            );
          } 
          RT[cur] = hybrid_bypass_DOWNWARD(cur, lvi);
          RT[cur] = red_variable_eliminate(RT[cur], lvi);
          RT[reachable] = red_bop(OR, RT[cur], RT[reachable]); 
          RT_TOP--; // cur 
        }
      }
      RT_TOP--; /* reachable */ 
      RT_TOP--; /* addr */ 
      return(RT[reachable]);
    }
    break;
  case INCREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_bck(dst, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_INC, FLAG_ACTION_EXACT
    ) );
  case DECREMENT_BY_CONSTANT:
    return(red_action_discrete_inc_bck(dst, st, FLAG_STATEMENT_PI, 
      FLAG_ACTION_DEC, FLAG_ACTION_EXACT
    ) );
  } 
}
  /* rec_statement_bck() */ 
  


struct red_type	*red_statement_bck(
  int			dst, 
  int			pi, 
  struct statement_type	*st, 
  int			flag_polarity, 
  int			flag_lazy_eval 
) { 
  int			original_action_stage, original_approx; 
  struct red_type	*result; 
  
/*
  print_cpu_time("Entering st bck"); 
  print_statement_line(st, pi); 
  fprintf(RED_OUT, "\n"); 
*/
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  original_approx = GSTATUS[INDEX_APPROX]; 
  GSTATUS[INDEX_APPROX] 
  = FLAG_STATEMENT_POLARITY = flag_polarity; 
  FLAG_STATEMENT_PI = pi; 
  
  result = rec_statement_bck(dst, st); 
  	
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  GSTATUS[INDEX_APPROX] = original_approx; 
/*
  print_cpu_time("Leaving st bck"); 
*/
  return(result); 
} 
  /* red_statement_bck() */ 
  
  



inline struct red_type *red_general_statement_bck(
  int 			si, 
  int 			pi, 
  struct statement_type *st, 
  int			fa, 
  int			flag_lazy_eval
) { 
  int			original_action_stage; 
  struct red_type	*result; 
  
  original_action_stage = GSTATUS[INDEX_ACTION_STAGE_EVAL]; 
  
  GSTATUS[INDEX_ACTION_STAGE_EVAL] 
  = (GSTATUS[INDEX_ACTION_STAGE_EVAL] & ~MASK_ACTION_STAGE_EVAL) 
  | (flag_lazy_eval & MASK_ACTION_STAGE_EVAL);  

  switch (fa) { 
  case FLAG_NO_ACTION_APPROX:  
    result = red_statement_bck(si, pi, st, fa, flag_lazy_eval); 
    break; 
  case FLAG_ACTION_APPROX_NOXTIVE: 
    result = red_statement_abstract_bck(si, pi, st, flag_lazy_eval); 
    break; 
  case FLAG_ACTION_APPROX_UNTIMED: 
    result = red_statement_untimed_bck(si, pi, st, flag_lazy_eval); 
    break; 
  default: 
    break; 
  } 
  GSTATUS[INDEX_ACTION_STAGE_EVAL] = original_action_stage; 
  return(result); 
}
  /* red_general_statement_bck() */ 



struct red_type	*red_dstatement_bck(d, pi, st) 
	struct red_type		*d; 
	int			pi; 
	struct statement_type	*st;
{
  int	W; 
  
  RT[W = RT_TOP++] = d; 
  d = red_statement_bck(
    W, pi, st, 
    (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY), 
    FLAG_ACTION_LAZY_EVAL 
  ); 
  RT_TOP--; 
  return(d); 	
}
  /* red_dstatement_bck() */  
  
  
  
  

struct red_type	*red_daction_bck(d, pi, act)
     struct red_type		*d; 
     int			pi;
     struct statement_type	*act;
{
  int	w; 
  
  RT[w = RT_TOP	++] = d; 
  d = red_statement_bck(w, pi, act, 
    (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY), 
    FLAG_ACTION_LAZY_EVAL 
  ); 
  RT_TOP--; 
  
  return(d); 
}
  /* red_daction_bck() */ 
  
  
  

