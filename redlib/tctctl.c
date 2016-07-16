/********************************************************   
    According to the paper, we can check for the time-convexity 
    of HA&&phi and HA&&~phi.  
    But here it is difficult to check the nontrivial time-convexity 
    of HA&&~phi.  
    Thus we opted for a simpler checking for 
    the no-upperbound, no-lowerbound of \phi.  
*/

#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>


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

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "treeman.h" 
#include "treeman.e" 
  
  



/* Shorthand_analysis is destructive. 
 * It changes the structure directly of the argument. 
 */  
int	shana_count = 0; 

  
/* 
 * This procedure does a preliminary time-convex & TCTCTL analysis for 
 * the efficient and adaptive time progress evaluation. 
 * Note that at this moment, we have the following assumptions 
 * for the correct analysis of this procedure. 
 * 1. It must be called after static_evaluation(). 
 *    This means that if some expressions are trivially constant, 
 *    then we might have a chance to tell 
 *    if some of its super-formulas is time-convex.  
 * 2. It must be called after ineq_analyze().   
 *    So all inequalities of arithmetic types must only contain discrete 
 *    variables.  
 * 3. It must be called before shorthand_analysis().  
 *    If it is called after, then all original formula structure may  
 *    have been destroyed. 
 *    Note it is still possible to deduce the structures of the original 
 *    formula with overhead in analysis.  
 *    However, for simplicity of implementation, we decided to 
 *    do TCTCTL analysis before shorthand_analysis(). 
 * 4. Now we have decided to do check_tctctl() after the variable 
 *    table has been constructed.  
 *    In this way, we can use CRD+MDD to check the location disjointness.  
 * 
 * The result of the procedure is a set of flags. 
 * 
 *    FLAG_TCTCTL_SUBFORM	
 *    FLAG_NOT_TCTCTL_SUBFORM 
 *
 *    FLAG_TCTCTL_ANALYSIS_CLOCK_UB
 *    FLAG_TCTCTL_ANALYSIS_CLOCK_LB
 *    FLAG_TCTCTL_ANALYSIS_LB_UB_LOCATION_DISJOINT 
 *
lemma: if only lb, then a disjunction is time-convex. 
lemma: if only ub, then a disjunction is time-convex. 
lemma: if lb and ub are location-disjoint, then a disjunction is time-convex.
lemma: if all time-convex, then a conjunction is time-convex. 
lemma: if only lb, a negation is time-convex. 
lemma: if only ub, a negation is time-convex. 
lemma: if lb and ub are location-disjoint, then a negation is time-convex. 
 */ 
 


int	check_location_disjoint(
  struct red_type	*dx, 
  struct red_type	*dy
) { 
  dx = red_type_eliminate(
    red_bop(AND, dx, RT[DECLARED_GLOBAL_INVARIANCE]), 
    TYPE_CLOCK
  );  
  dy = red_type_eliminate(
    red_bop(AND, dy, RT[DECLARED_GLOBAL_INVARIANCE]), 
    TYPE_CLOCK
  ); 
  if (red_bop(AND, dx, dy) == NORM_FALSE) 
    return(TYPE_TRUE); 
  else 
    return(TYPE_FALSE); 
}
  /* check_location_disjoint() */ 
  
   

void	check_tctctl(
  struct ps_exp_type	*psub
) {
  int				i, lb, ub, llb, lub, ulb, uub, 
				clock_bound_status, child_status; 
  struct ps_bunit_type		*pbu;
  struct ps_exp_type		*wexp, *dest_child, *path_child; 
  struct ps_fairness_link_type	*fl; 
  struct index_link_type	*sibling_mode_index_list; 
  struct red_type		*lb_red, *ub_red, *lb_ub_red; 

  switch(psub->type) {
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_QFD: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_NULL: 
  case TYPE_MODE_INDEX: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_CLOCK: 
  case TYPE_DENSE: 
  case TYPE_DISCRETE: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER: 
  case TYPE_INTERVAL: 
  
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case ARITH_MODULO: 
  case ARITH_MIN: 
  case ARITH_MAX: 

  case TYPE_FALSE : 
  case TYPE_TRUE :
  case TYPE_BDD: 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
  case EQ :
  case NEQ : 
  case ARITH_EQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
  case ARITH_NEQ :
    fprintf(RED_OUT, "\nError: an unexpected arithmetic term encountered \n"); 
    fprintf(RED_OUT, "       in check_tctctl().\n"); 
    pcform(psub); 
    fflush(RED_OUT); 
    exit(0); 
    break; 

  case RED: 
    psub->exp_status = (psub->exp_status & ~FLAG_TCTCTL_SUBFORM) 
    | check_time_convexity(
        red_bop(AND, RT[DECLARED_GLOBAL_INVARIANCE], 
          psub->u.rpred.red
      ) ); 
    break; 
  
  case TYPE_INLINE_CALL: 
    check_tctctl(psub->u.inline_call.instantiated_exp); 
    psub->exp_status = (psub->exp_status & ~FLAG_TCTCTL_SUBFORM) 
    | (psub->u.inline_call.instantiated_exp->exp_status & FLAG_TCTCTL_SUBFORM); 
    break; 
    
  case ARITH_CONDITIONAL: 
    // after static_evalation, if we get to this case, 
    // then it pretty much means that the truth value of the condition 
    // and the identity of the two cases cannot be determined trivially. 
    // In such a situation, we will at the moment declare the formula 
    // as not FLAG_TCTCTL_SUBFORM since the complement of 
    // a time-convex condition is time-concave.  
    check_tctctl(psub->u.arith_cond.cond); 
    check_tctctl(psub->u.arith_cond.if_exp); 
    check_tctctl(psub->u.arith_cond.else_exp); 

    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 

    // First check the degenerate case that .cond is false. 
    if (   (psub->u.arith_cond.cond->type == RED) 
        && red_bop(AND, RT[DECLARED_GLOBAL_INVARIANCE], 
             psub->u.arith_cond.cond->u.rpred.red
           ) == NORM_FALSE
        ) { 
      psub->exp_status = psub->exp_status  
      | (psub->u.arith_cond.else_exp->exp_status & FLAG_TCTCTL_SUBFORM); 
    } 
    // Second, check the degenerate case that ~(.cond) is false. 
    else if (   (psub->u.arith_cond.cond->type == RED) 
             && red_bop(AND, RT[DECLARED_GLOBAL_INVARIANCE], 
                  red_complement(psub->u.arith_cond.cond->u.rpred.red)
                ) == NORM_FALSE
             ) { 
      psub->exp_status = psub->exp_status  
      | (psub->u.arith_cond.if_exp->exp_status & FLAG_TCTCTL_SUBFORM); 
    } 
    return; 

  case AND :
    psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      check_tctctl(pbu->subexp);
      if (~(pbu->subexp->exp_status & FLAG_TCTCTL_SUBFORM)) 
        psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    }
/*
    fprintf(RED_OUT, "Shorthand analyzing AND-OR: EXP_MODAL_INSIDE, %1x\n", 
	    psub->status & FLAG_TCTCTL_ANALYSIS_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(psub, 0); 
*/ 
    return; 

  case OR : 
  case IMPLY : 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      check_tctctl(pbu->subexp);
    }
    return; 

  case NOT : 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    check_tctctl(psub->u.bexp.blist->subexp);
    return; 
    
  case FORALL: 
    fprintf(RED_OUT, "\nError: unexpted FORALL in check_tctctl().\n"); 
    fprintf(RED_OUT, "       Since now we have moved spec_global to \n"); 
    fprintf(RED_OUT, "       before shorthand_analysis(), this must be bug.\n"); 
    exit(0); 
    break; 
  case EXISTS: 
    fprintf(RED_OUT, "\nError: unexpted FORALL in check_tctctl().\n"); 
    fprintf(RED_OUT, "       Since now we have moved spec_global to \n"); 
    fprintf(RED_OUT, "       before shorthand_analysis(), this must be bug.\n"); 
    exit(0); 
    break; 

  case RESET: 
    check_tctctl(psub->u.reset.child); 
    if (clock_bound_status & FLAG_TCTCTL_SUBFORM) 
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 
    else 
      psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    return; 
    break; 
    
  case FORALL_ALWAYS: 
    // <c,oo)\subseteq R^~- engenders time convexity. 
    // 
    check_tctctl(psub->u.mexp.path_child); 
    if (   psub->u.mexp.strong_fairness_list == NULL 
        && psub->u.mexp.weak_fairness_list == NULL 
        && psub->u.mexp.time_ub == CLOCK_POS_INFINITY 
        ) 
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 
    else 
      psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;  
    return; 
    break; 

  case FORALL_EVENTUALLY : 
    check_tctctl(psub->u.mexp.dest_child); 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    if (   psub->u.mexp.strong_fairness_list != NULL 
        || psub->u.mexp.weak_fairness_list != NULL 
        ) 
      return; 
    else if (// Now we check the first lemma in this case. 
       psub->u.mexp.time_lb == 0
    && (psub->u.mexp.dest_child->exp_status & FLAG_TCTCTL_SUBFORM) 
    && (GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
    && psub->u.mexp.dest_child->type == RED 
    && check_location_disjoint(
         psub->u.mexp.dest_child->u.rpred.red, 
         red_complement(psub->u.mexp.dest_child->u.rpred.red)
    )  )  
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 

    #if RED_DEBUG_PARSE_MODE
    fprintf(RED_OUT, "shorthand analysis forall eventually:\nbefore addneg:\n"); 
    pcform(newsub); 
    fprintf(RED_OUT, "\ncheck_tctctl()->status = %x\n", psub->status); 
    pcform(psub); 
    fprintf(RED_OUT, "\n"); 
    #endif 
    
    return; 
    break; 
  case EXISTS_ALWAYS: 
    check_tctctl(psub->u.mexp.path_child); 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    if (   psub->u.mexp.strong_fairness_list != NULL 
        || psub->u.mexp.weak_fairness_list != NULL 
        ) 
      return; 
    if (   (psub->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM)
        && psub->u.mexp.time_lb == 0
        ) 
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 

    #if RED_DEBUG_PARSE_MODE
    fprintf(RED_OUT, "\ncheck_tctctl()->status = %x\n", psub->status); 
    pcform(psub); 
    fprintf(RED_OUT, "\n"); 
    #endif 

    return; 
    break; 

  case EXISTS_EVENTUALLY: 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;  
    check_tctctl(psub->u.mexp.dest_child); 
    if (   psub->u.mexp.strong_fairness_list != NULL 
        || psub->u.mexp.weak_fairness_list != NULL 
        ) 
      return;  
    if (
           psub->u.mexp.time_ub == CLOCK_POS_INFINITY 
        && (GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
        && (psub->u.mexp.dest_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        && psub->u.mexp.dest_child->type == RED 
        && check_location_disjoint(
             psub->u.mexp.dest_child->u.rpred.red, 
             red_complement(psub->u.mexp.dest_child->u.rpred.red)
        )  )  
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 

    return; 
    break; 

  case FORALL_UNTIL: 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;  
    check_tctctl(psub->u.mexp.dest_child); 
    check_tctctl(psub->u.mexp.path_child); 
    if (   psub->u.mexp.strong_fairness_list != NULL 
        || psub->u.mexp.weak_fairness_list != NULL 
        )
      return; 
    if (   psub->u.mexp.time_lb == 0
        && (psub->u.mexp.dest_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        && (psub->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        && psub->u.mexp.dest_child->type == RED 
        && psub->u.mexp.path_child->type == RED 
        && check_location_disjoint(
             psub->u.mexp.dest_child->u.rpred.red, 
             psub->u.mexp.path_child->u.rpred.red
        )  )  
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 

    return; 
    break; 
  case EXISTS_UNTIL: 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;  
    check_tctctl(psub->u.mexp.path_child); 
    check_tctctl(psub->u.mexp.dest_child); 
    if (   psub->u.mexp.strong_fairness_list != NULL 
        || psub->u.mexp.weak_fairness_list != NULL 
        )
      return; 
    if (   psub->u.mexp.time_ub == CLOCK_POS_INFINITY 
        && (psub->u.mexp.dest_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        && (psub->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        && psub->u.mexp.dest_child->type == RED 
        && psub->u.mexp.path_child->type == RED 
        && check_location_disjoint(
             psub->u.mexp.dest_child->u.rpred.red, 
             psub->u.mexp.path_child->u.rpred.red
        )  )  
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 
    else if (
           psub->u.mexp.time_lb > 0
        && psub->u.mexp.time_ub >= psub->u.mexp.time_lb   
        && (psub->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM) 
        )  
      psub->exp_status = psub->exp_status | FLAG_TCTCTL_SUBFORM; 

    return; 
    break; 
    
  case EXISTS_ALMOST: 
  case EXISTS_OFTEN: 
  case FORALL_ALMOST: 
  case FORALL_OFTEN: 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    return; 
    break; 

  case EXISTS_EVENT: 
  case FORALL_EVENT: 
  case LINEAR_EVENT: 
    psub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;  
    return; 
    break; 

  default: 
    fprintf(RED_OUT, "\nError 3.1: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
}
/* check_tctctl() */ 



 





struct ps_exp_type	*shorthand_analysis(
  struct ps_exp_type *
);

struct ps_fairness_link_type	*shorthand_fairness_list_copy_analysis( 
  struct ps_fairness_link_type	*ps_list, 
  int				*fcount_ptr  
) { 
  struct ps_fairness_link_type	*fl, *rlist; 

  rlist = NULL; 
  *fcount_ptr = 0; 
  for (fl = ps_list; fl; fl = fl->next_ps_fairness_link) {
    rlist = insert_sorted_flist(
      shorthand_analysis(fl->fairness), 
      fl->status,  
      rlist, 
      fcount_ptr 
    ); 
  } 
  return (rlist); 
}
/* shorthand_fairness_list_copy_analysis() */  



void	shorthand_fairness_analysis(
  struct ps_exp_type	*newsub, 
  struct ps_exp_type	*psub
) {
  newsub->u.mexp.strong_fairness_count = 0; 
  newsub->u.mexp.strong_fairness_list 
  = shorthand_fairness_list_copy_analysis(
    psub->u.mexp.strong_fairness_list, 
    &(newsub->u.mexp.strong_fairness_count)
  ); 
  newsub->u.mexp.weak_fairness_count = 0; 
  newsub->u.mexp.weak_fairness_list 
  = shorthand_fairness_list_copy_analysis(
    psub->u.mexp.weak_fairness_list, 
    &(newsub->u.mexp.weak_fairness_count)
  ); 
}
  /* shorthand_fairness_analysis() */

/* Shorthand_analysis is destructive. 
 * It changes the structure directly of the argument. 
 */  
    
  

/* This procedure will make a copy of the original formula. 
 * The original formula is saved in attribute original_form. 
 * Then it translates the copy with some shorthand rewriting rules. 
 * 
 */ 
struct ps_exp_type	*shorthand_analysis(psub) 
     struct ps_exp_type	*psub;
{
  int				lvi, rvi, lci, i, jj, clock_bound_status; 
  struct ps_bunit_type		*pbu, *nbu, dummy_bu, *tbu;
  struct ps_exp_type		*newsub, *childsub, *childsubf, 
				*grandchildsub, *wexp, 
				*dest_child, *path_child; 
  struct ps_fairness_link_type	*fl, fl_dummy, *fl_tail, *nfl; 
  struct index_link_type	*sibling_mode_index_list; 
  struct red_type		*childred; 

  switch(psub->type) {
  case TYPE_FALSE : 
  case TYPE_TRUE :
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_QFD: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_NULL: 
  case TYPE_MODE_INDEX: 
  case TYPE_SYNCHRONIZER: 
    return(psub); 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = shorthand_analysis(psub->u.exp); 
    return(ps_exp_share(newsub)); 
    break; 

  case TYPE_CLOCK: 
  case TYPE_DENSE: 
  case TYPE_DISCRETE: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER: 
  case TYPE_BDD: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.atom.exp_base_proc_index 
    = shorthand_analysis(psub->u.atom.exp_base_proc_index); 
/*
    if (psub->u.atom.indirect_count) { 
      newsub->u.atom.indirect_exp = (struct ps_exp_type **) 
        malloc(psub->u.atom.indirect_count * sizeof(struct ps_exp_type *)); 
      for (i = 0; i < psub->u.atom.indirect_count; i++)
        newsub->u.atom.indirect_exp[i] 
        = shorthand_analysis(psub->u.atom.indirect_exp[i]); 
    } 
    if (psub->u.atom.indirect_vi) {
      newsub->u.atom.indirect_vi = (int *) 
        malloc((PROCESS_COUNT+1) * sizeof(int) 
      ); 
      for (i = 1; i <= PROCESS_COUNT; i++) 
        newsub->u.atom.indirect_vi[i] = psub->u.atom.indirect_vi[i]; 
    } 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case TYPE_INTERVAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub;
    newsub->u.interval.lbound_exp = shorthand_analysis(psub->u.interval.lbound_exp); 
    newsub->u.interval.rbound_exp = shorthand_analysis(psub->u.interval.rbound_exp); 
    return(ps_exp_share(newsub)); 

  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.ineq.term = (struct parse_term_type *) 
      malloc(newsub->u.ineq.term_count * sizeof(struct parse_term_type)); 
    for (i = 0; i < newsub->u.ineq.term_count; i++) { 
      newsub->u.ineq.term[i].coeff 
      = shorthand_analysis(psub->u.ineq.term[i].coeff); 
      newsub->u.ineq.term[i].operand 
      = shorthand_analysis(psub->u.ineq.term[i].operand); 
    } 
    newsub->u.ineq.offset = shorthand_analysis(psub->u.ineq.offset); 
    return(ps_exp_share(newsub)); 
    break; 

  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case ARITH_MODULO: 
  case ARITH_MIN: 
  case ARITH_MAX: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub;
    newsub->u.arith.lhs_exp = shorthand_analysis(psub->u.arith.lhs_exp); 
    newsub->u.arith.rhs_exp = shorthand_analysis(psub->u.arith.rhs_exp); 
    return(ps_exp_share(newsub)); 

  case TYPE_INLINE_CALL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub;
    newsub->u.inline_call.instantiated_exp 
    = shorthand_analysis(psub->u.inline_call.instantiated_exp); 
    return(ps_exp_share(newsub)); 
    
  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub;
    newsub->u.arith_cond.cond 
    = shorthand_analysis(psub->u.arith_cond.cond); 
    newsub->u.arith_cond.if_exp 
    = shorthand_analysis(psub->u.arith_cond.if_exp); 
    newsub->u.arith_cond.else_exp 
    = shorthand_analysis(psub->u.arith_cond.else_exp); 
    return(ps_exp_share(newsub)); 

  case FORALL: 
  case EXISTS: 

    // after static_evalation, if we get to this case, 
    // then it pretty much means that the truth value of the condition 
    // and the identity of the two cases cannot be determined trivially. 
    // In such a situation, we will at the moment declare the formula 
    // as not FLAG_TCTCTL_SUBFORM since the complement of 
    // a time-convex condition is time-concave.  
/*
*/
    fprintf(RED_OUT, 
      "\nError: We don't expect to see type %1d in shorthand_analysis().\n", 
      psub->type 
    ); 
    fflush(RED_OUT); 
    bk(0); 

  case RED: 
/*
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
*/
    return(psub); 
    break; 
    
  case AND :
  case OR : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      insert_sorted_blist_dummy_head(newsub->type, 
        shorthand_analysis(pbu->subexp), &dummy_bu, 
        &(newsub->u.bexp.len)
      );
    } 
    if (newsub->u.bexp.len == 1) { 
      free(dummy_bu.bnext); 
      free(newsub); 
      return(newsub->u.bexp.blist->subexp); 
    } 
    else {
      newsub->u.bexp.blist = dummy_bu.bnext; 
/*
    newsub->original_form = psub; 
*/
/*
    fprintf(RED_OUT, "Shorthand analyzing AND-OR: EXP_MODAL_INSIDE, %1x\n", 
	    psub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(psub, 0); 
*/ 
      return(ps_exp_share(newsub)); 
    }
  case NOT : 
    childsub = shorthand_analysis(psub->u.bexp.blist->subexp); 
    switch (childsub->type) {
    case NOT: 
      return(childsub->u.bexp.blist->subexp); 

    case RED: 
      newsub = ps_exp_alloc(RED); 
      newsub->u.rpred.red 
      = newsub->u.rpred.original_red 
      = red_complement(childsub->u.rpred.red); 
      newsub->exp_status = (newsub->exp_status & ~FLAG_TCTCTL_SUBFORM) 
      | check_time_convexity(
          red_bop(AND, RT[DECLARED_GLOBAL_INVARIANCE], 
            newsub->u.rpred.red
        ) ); 
      fprintf(RED_OUT, "\n>>shorthand_analysis()->exp_status=%x\n", newsub->exp_status); 
      pcform(newsub); 
      newsub = ps_exp_share(newsub); 
      fprintf(RED_OUT, "\n<<shorthand_analysis()->exp_status=%x\n", newsub->exp_status); 
      pcform(newsub); 
      fprintf(RED_OUT, "\n"); 
      
      return(newsub); 

    default: 
      newsub = add_neg(shorthand_analysis(psub->u.bexp.blist->subexp)); 
/*
    fprintf(RED_OUT, 
      "Shorthand analyzing AND-OR: EXP_MODAL_INSIDE, %1x\n", 
      psub->status & FLAG_EXP_MODAL_INSIDE
    ); 
    print_parse_subformula_structure(psub, 0); 
*/ 
      return(ps_exp_share(newsub)); 
    }
    break; 

  case IMPLY : 
    childsub = shorthand_analysis(psub->u.bexp.blist->subexp); 
    childsubf = shorthand_analysis(psub->u.bexp.blist->bnext->subexp);
    if (childsub->type == RED) { 
      childred = red_complement(childsub->u.rpred.red);  
      if (childsubf->type == RED) { 
      	childred = red_bop(OR, childred, childsubf->u.rpred.red); 
        childsub = ps_exp_alloc(RED); 
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
    insert_sorted_blist_dummy_head(OR, 
      childsub, &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    insert_sorted_blist_dummy_head(OR, 
      childsubf, &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 

  case RESET: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = shorthand_analysis(psub->u.reset.child); 
/*
    fprintf(RED_OUT, "Shorthand analyzing RESET: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 0); 
*/
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 
    
  case FORALL_ALWAYS: 
    newsub = ps_exp_alloc(EXISTS_UNTIL); 
    *newsub = *psub; 
    newsub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    newsub->type = EXISTS_UNTIL; // This is necessary since it was 
                                 // overwritten by the last statement. 
    newsub->u.mexp.dest_child 
    = add_neg(shorthand_analysis(psub->u.mexp.path_child)); 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction 
    );  
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  

    shorthand_fairness_analysis(newsub, psub); 

    newsub = add_neg(newsub); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 

/*
    newsub->original_form = psub; 
*/
    return (ps_exp_share(newsub)); 
    break; 
  case FORALL_EVENTUALLY : 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub; 
    newsub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    newsub->type = EXISTS_ALWAYS; // This is necessary since it was 
                                 // overwritten by the last statement. 
    newsub->u.mexp.path_child 
    = add_neg(shorthand_analysis(psub->u.mexp.dest_child)); 

    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction 
    );  
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  

    shorthand_fairness_analysis(newsub, psub); 

    #if RED_DEBUG_PARSE_MODE
    fprintf(RED_OUT, "shorthand analysis forall eventually:\nbefore addneg:\n"); 
    pcform(newsub); 
    #endif 
    
    newsub = add_neg(newsub); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_ALWAYS: 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub; 
    newsub->u.mexp.path_child 
    = shorthand_analysis(psub->u.mexp.path_child); 

    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction 
    );  
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  

    shorthand_fairness_analysis(newsub, psub); 

/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_EVENTUALLY: 
    newsub = ps_exp_alloc(EXISTS_UNTIL); 
    *newsub = *psub; 
    newsub->type = EXISTS_UNTIL; // This is necessary since it was 
                                 // overwritten by the last statement. 
    newsub->u.mexp.dest_child = shorthand_analysis(psub->u.mexp.dest_child); 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction 
    );  
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  

    shorthand_fairness_analysis(newsub, psub); 

/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case FORALL_UNTIL: 
    grandchildsub = ps_exp_alloc(AND); 
    grandchildsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    insert_sorted_blist_dummy_head(AND, 
      add_neg(shorthand_analysis(psub->u.mexp.dest_child)), 
      &dummy_bu, &(grandchildsub->u.bexp.len) 
    ); 
    insert_sorted_blist_dummy_head(AND, 
      shorthand_analysis(psub->u.mexp.path_child), 
      &dummy_bu, &(grandchildsub->u.bexp.len) 
    ); 
    if (grandchildsub->u.bexp.len == 1) { 
      free(grandchildsub); 
      grandchildsub = dummy_bu.bnext->subexp; 
      free(dummy_bu.bnext); 
    } 
    else {
      grandchildsub->u.bexp.blist = dummy_bu.bnext; 
      grandchildsub = ps_exp_share(grandchildsub); 
    }

    /* nbu is linked to (exists fairness A (not C) until ((not B) and (not C)))
    */ 
    childsubf = ps_exp_alloc(EXISTS_UNTIL); 
    childsubf->u.mexp.time_lb = psub->u.mexp.time_lb; 
    childsubf->u.mexp.time_ub = psub->u.mexp.time_ub; 
    childsubf->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction
    ); 
    if (psub->u.mexp.event_restriction)
      childsubf->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  
    else 
      childsubf->u.mexp.event_restriction = NULL; 
    childsubf->u.mexp.path_child = add_neg(shorthand_analysis(psub->u.mexp.dest_child)); 
    childsubf->var_status = psub->var_status; 
    childsubf->exp_status = psub->exp_status; 

    shorthand_fairness_analysis(childsubf, psub); 

    childsubf = ps_exp_share(childsubf); 

    /* grandchildsub will be for ((not B) and (not C)) 
    */ 
    childsubf->u.mexp.dest_child = grandchildsub; 
    childsubf = ps_exp_share(childsubf); 
    
    /* pbu is linked to (exists fairness A always not C) 
    */ 
    childsub = ps_exp_alloc(EXISTS_ALWAYS); 
    childsub->u.mexp.time_lb = psub->u.mexp.time_lb; 
    childsub->u.mexp.time_ub = psub->u.mexp.time_ub;
    childsub->u.mexp.time_restriction 
    = shorthand_analysis(psub->u.mexp.time_restriction); 
    if (psub->u.mexp.event_restriction)
      childsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  
    else 
      childsub->u.mexp.event_restriction = NULL; 
      
    childsub->u.mexp.path_child = add_neg(
      dest_child = shorthand_analysis(psub->u.mexp.dest_child)
    ); 
    childsub->u.mexp.dest_child = PS_EXP_FALSE; 
    childsub->var_status = psub->var_status; 
    childsub->exp_status = psub->exp_status; 

    shorthand_fairness_analysis(childsub, psub); 
    childsub = ps_exp_share(childsub); 

    newsub = ps_exp_alloc(OR); 
    newsub->var_status = psub->var_status;
    newsub->exp_status = psub->exp_status;
 
    /*
    forall fairness A through {E} B until at {F} C 
      to be translated to  
      	not (   (exists fairness A through {E} always at {F} not C)
      	     or (exists fairness A through {E} (not C) until ((not B) and (not C)))
      	     ) 
    */ 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    insert_sorted_blist_dummy_head(OR, 
      childsub, 
      &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    insert_sorted_blist_dummy_head(OR, 
      childsubf, 
      &dummy_bu, &(newsub->u.bexp.len) 
    ); 
    if (newsub->u.bexp.len == 1) { 
      free(newsub); 
      newsub = dummy_bu.bnext->subexp; 
      free(dummy_bu.bnext); 
    } 
    else {
      newsub->u.bexp.blist = dummy_bu.bnext; 
      newsub = ps_exp_share(newsub); 
    }
    return(newsub); 
    break; 

  case EXISTS_UNTIL: 
    newsub = ps_exp_alloc(EXISTS_UNTIL); 
    *newsub = *psub; 
    newsub->u.mexp.path_child = shorthand_analysis(psub->u.mexp.path_child); 
    newsub->u.mexp.dest_child = shorthand_analysis(psub->u.mexp.dest_child); 
    newsub->u.mexp.time_restriction = shorthand_analysis(
      psub->u.mexp.time_restriction 
    );  
    if (psub->u.mexp.event_restriction)
      newsub->u.mexp.event_restriction = shorthand_analysis(
        psub->u.mexp.event_restriction 
      );  
    shorthand_fairness_analysis(newsub, psub); 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 
    
  case EXISTS_ALMOST: 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub; 
    newsub->type = EXISTS_ALWAYS; // This is necessary since it was 
                                 // overwritten by the last statement. 
    childsub = shorthand_analysis(psub->u.mexp.path_child);  

    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = PS_EXP_TRUE; 
    newsub->u.mexp.event_restriction = NULL;  

    shorthand_fairness_analysis(newsub, psub); 
    newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
      childsub, 
      (childsub->var_status & FLAG_EXP_STATE_INSIDE) | FLAG_FAIRNESS_WEAK, 
      newsub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count) 
    );  

    newsub->var_status = newsub->var_status 
    | (childsub->var_status & FLAG_EXP_STATE_INSIDE); 
    newsub->exp_status = newsub->exp_status | FLAG_FAIRNESS_WEAK; 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case EXISTS_OFTEN: 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub; 
    newsub->type = EXISTS_ALWAYS; // This is necessary since it was 
                                 // overwritten by the last statement. 
    childsub = shorthand_analysis(psub->u.mexp.path_child); 
    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = PS_EXP_TRUE; 
    newsub->u.mexp.event_restriction = NULL;  

    shorthand_fairness_analysis(newsub, psub); 
    newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
      childsub, 
      (childsub->var_status & FLAG_EXP_STATE_INSIDE) | FLAG_FAIRNESS_STRONG, 
      newsub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count) 
    );  

    newsub->var_status = newsub->var_status 
    | (childsub->var_status & FLAG_EXP_STATE_INSIDE);  
    newsub->exp_status = newsub->exp_status | FLAG_FAIRNESS_STRONG; 
/*
    newsub->original_form = psub; 
*/ 
    return(ps_exp_share(newsub)); 
    break; 

  case FORALL_ALMOST: 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub; 
    newsub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    newsub->type = EXISTS_ALWAYS;  // This is necessary since it was 
                                 // overwritten by the last statement. 
    childsub = shorthand_analysis(psub->u.mexp.path_child); 
    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = PS_EXP_TRUE; 
    newsub->u.mexp.event_restriction = NULL;  

    shorthand_fairness_analysis(newsub, psub); 
    newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
      add_neg(childsub), 
      (childsub->var_status & FLAG_EXP_STATE_INSIDE) | FLAG_FAIRNESS_STRONG, 
      newsub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count) 
    );  

    newsub->var_status = psub->var_status 
    | (childsub->var_status & FLAG_EXP_STATE_INSIDE); 
    newsub->exp_status = psub->exp_status | FLAG_FAIRNESS_STRONG; 
    newsub = add_neg(newsub); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  case FORALL_OFTEN: 
    newsub = ps_exp_alloc(EXISTS_ALWAYS); 
    *newsub = *psub;
    newsub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM; 
    newsub->type = EXISTS_ALWAYS; // This is necessary since it was 
                                 // overwritten by the last statement. 
    childsub = shorthand_analysis(psub->u.mexp.path_child);  
    newsub->u.mexp.dest_child = PS_EXP_FALSE; 
    newsub->u.mexp.path_child = PS_EXP_TRUE; 
    newsub->u.mexp.time_restriction = PS_EXP_TRUE; 
    newsub->u.mexp.event_restriction = NULL;  

    shorthand_fairness_analysis(newsub, psub); 
    newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
      add_neg(childsub), 
      (childsub->var_status & FLAG_EXP_STATE_INSIDE) | FLAG_FAIRNESS_WEAK, 
      newsub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count) 
    );  

    newsub->var_status = psub->var_status 
    | (childsub->exp_status & FLAG_EXP_STATE_INSIDE);  
    newsub->exp_status = psub->exp_status | FLAG_FAIRNESS_WEAK; 
    newsub = add_neg(newsub); 
    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  
  case LINEAR_EVENT: 
    newsub = ps_exp_alloc(LINEAR_EVENT); 
    *newsub = *psub; 
    newsub->exp_status = psub->exp_status & ~FLAG_TCTCTL_SUBFORM;
    newsub->type = LINEAR_EVENT; // This is necessary since it was 
                                 // overwritten by the last statement. 
    if (psub->u.eexp.event_exp)
      newsub->u.eexp.event_exp = shorthand_analysis(psub->u.eexp.event_exp); 
    newsub->u.eexp.precond_exp
    = shorthand_analysis(psub->u.eexp.precond_exp); 
    newsub->u.eexp.postcond_exp
    = shorthand_analysis(psub->u.eexp.postcond_exp); 

    newsub->var_status = psub->var_status; 
    newsub->exp_status = psub->exp_status; 
/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 
    
  case TYPE_GAME_SIM: 
    newsub = ps_exp_alloc(TYPE_GAME_SIM); 
    *newsub = *psub; 
    newsub->type = TYPE_GAME_SIM; // This is necessary since it was 
                                 // overwritten by the last statement. 
    newsub->u.mexp.dest_child = NULL; 
    newsub->u.mexp.path_child = NULL; 
    newsub->u.mexp.time_restriction = NULL;  

    shorthand_fairness_analysis(newsub, psub); 

/*
    newsub->original_form = psub; 
*/
    return(ps_exp_share(newsub)); 
    break; 

  default: 
    fprintf(RED_OUT, "\nError 3.2: Unrecognized condition operator %1d.\n", psub->type);
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
}
/* shorthand_analysis() */ 











void	print_tctctl_flag(psub) 
     struct ps_exp_type	*psub;
{
  int				lvi, rvi, lci, i, jj; 
  struct ps_bunit_type		*pbu, *nbu; 
  struct ps_exp_type		*newchild; 
  struct ps_fairness_link_type	*fl, fl_dummy, *fl_tail, *nfl; 

  fprintf(RED_OUT, "\n==<print_tctctl_flag(): %x>===========\n", 
    psub->exp_status & FLAG_TCTCTL_SUBFORM 
  ); 
  pcform(psub); 
  
  switch(psub->type) {
  case TYPE_FALSE : 
  case TYPE_TRUE :
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_NULL: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_CLOCK: 
  case TYPE_DISCRETE: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
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
    break; 
    
  case ARITH_CONDITIONAL: 
    print_tctctl_flag(psub->u.arith_cond.cond);
    print_tctctl_flag(psub->u.arith_cond.if_exp);
    print_tctctl_flag(psub->u.arith_cond.else_exp);
    break; 
    
  case TYPE_INLINE_CALL: 
    print_tctctl_flag(
      psub->u.inline_call.instantiated_exp
    );
    break; 
    
  case RED: 
    break; 
    
  case AND :
  case OR :
  case IMPLY :
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      print_tctctl_flag(pbu->subexp); 
    }
    return; 
    break; 
  case NOT : 
    print_tctctl_flag(psub->u.bexp.blist->subexp); 
    return;
  case FORALL: 
  case EXISTS: 
    print_tctctl_flag(psub->u.qexp.child); 
    return; 
    break; 

  case RESET: 
    print_tctctl_flag(psub->u.reset.child); 
    return; 
    break; 
  case EXISTS_ALWAYS: 
  case FORALL_ALWAYS: 
  case EXISTS_ALMOST: 
  case FORALL_ALMOST: 

  case FORALL_EVENTUALLY : 
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE: 
  case EXISTS_OFTEN: 
  case FORALL_OFTEN:

  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
    print_tctctl_flag(psub->u.mexp.path_child);       
    print_tctctl_flag(psub->u.mexp.dest_child);       
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      print_tctctl_flag(fl->fairness); 
    }     
    return; 
    break; 

  case EXISTS_EVENT: 
  case FORALL_EVENT: 
  case LINEAR_EVENT: 
    print_tctctl_flag(psub->u.eexp.precond_exp);       
    print_tctctl_flag(psub->u.eexp.postcond_exp);       
    break; 
    
/*
    fprintf(RED_OUT, "\nWarning: This modal operator should have been rewritten in shorthand_analysis().\n"); 
    fflush(RED_OUT); 
    bk(0); 
//    exit(0); 
    break; 
*/
  default: 
    fprintf(RED_OUT, "\nError 4: Unrecognized condition operator %1d.\n", psub->type);
    pcform(psub);
    fprintf(RED_OUT, "\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
}
/* print_tctctl_flag() */ 





#ifdef RED_DEBUG_PARSE_MODE 
int	count_vif = 0; 
#endif 

var_index_fillin(psub)
     struct ps_exp_type	*psub; 
{
  int				i, jj; 
  struct ps_bunit_type		*pbu; 
  struct ps_fairness_link_type	*fl;
  struct parse_indirect_type	*pt;

/*
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\ncount_vif = %1d\n", ++count_vif); 
  pcform(psub); 
  fflush(RED_OUT); 
  for (; count_vif == -1; ) ; 
  #endif 
*/  
  if (!psub) 
    return; 

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_NULL:
  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_INLINE_ARGUMENT: 
    return;

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    var_index_fillin(psub->u.exp); 
    return; 

  case TYPE_SYNCHRONIZER:
    var_index_fillin(psub->u.atom.exp_base_proc_index);
//    psub->u.atom.indirect_count = 0;
    psub->u.atom.var_index
    = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index];
    return;

  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      var_index_fillin(psub->u.atom.indirect_exp[i]); 
    } 
*/
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_BDD: 
/*
    if (psub->u.atom.indirect_vi == NULL) { 
      psub->u.atom.indirect_vi = (int *) 
        malloc((PROCESS_COUNT+1) * sizeof(int)); 
    }
*/
    if (psub->u.atom.var_name) {
      var_index_fillin(psub->u.atom.exp_base_proc_index);
      switch (psub->u.atom.exp_base_proc_index->type) { 
      case TYPE_CONSTANT:
        psub->u.atom.var_index
        = variable_index[psub->u.atom.var->type][psub->u.atom.exp_base_proc_index->u.value][psub->u.atom.var->index];
        break; 
      case TYPE_NULL: 
	psub->u.atom.var_index
	= variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index];
        break; 
      default: 
/*
        fprintf(RED_OUT, 
          "\npsub in var_index_fillin for psub->u.atom.var %1d:%s\n", 
          psub->u.atom.var->index, psub->u.atom.var->name 
        ); 
        pcform(psub); 
*/
	psub->u.atom.var_index
	= variable_index[psub->u.atom.var->type][1][psub->u.atom.var->index];
      }
    }
    else
      psub->u.atom.var_index
	= variable_index[psub->u.atom.var->type][1][psub->u.atom.var->index];
    if (psub->var_status & FLAG_VAR_PRIMED) 
      psub->u.atom.var_index = VAR[psub->u.atom.var_index].PRIMED_VI; 
    return;
  case TYPE_INTERVAL:
    if (psub->u.interval.lbound_exp) 
      var_index_fillin(psub->u.interval.lbound_exp);  
    if (psub->u.interval.rbound_exp) 
      var_index_fillin(psub->u.interval.rbound_exp);  
    break; 
    
  case BIT_NOT: 
    var_index_fillin(psub->u.exp);
    return; 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD :
  case ARITH_MINUS :
  case ARITH_MULTIPLY :
  case ARITH_DIVIDE :
  case ARITH_MODULO: 
  case ARITH_MAX :
  case ARITH_MIN : 
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    var_index_fillin(psub->u.arith.lhs_exp);
    var_index_fillin(psub->u.arith.rhs_exp);
    return; 
  case ARITH_CONDITIONAL: 
    var_index_fillin(psub->u.arith_cond.cond);
    var_index_fillin(psub->u.arith_cond.if_exp);
    var_index_fillin(psub->u.arith_cond.else_exp);
    return; 
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    for (jj = 0; jj < psub->u.ineq.term_count; jj++)
      var_index_fillin(psub->u.ineq.term[jj].operand);
    var_index_fillin(psub->u.ineq.offset);
    return; 
  case TYPE_INLINE_BOOLEAN_DECLARE: 
    var_index_fillin(psub->u.inline_declare.declare_exp); 
    return; 
    
  case TYPE_INLINE_DISCRETE_DECLARE: 
    var_index_fillin(psub->u.inline_declare.declare_exp); 
    return; 
    
  case TYPE_INLINE_CALL: 
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         pbu = pbu->bnext
         ) { 
      var_index_fillin(pbu->subexp); 
    } 
    var_index_fillin(psub->u.inline_call.instantiated_exp); 
    return; 
    
  case AND :
  case OR :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist; 
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      var_index_fillin(pbu->subexp); 
    }
    return;
  case NOT :
    var_index_fillin(psub->u.bexp.blist->subexp); 
    return; 
  case IMPLY :
    var_index_fillin(psub->u.bexp.blist->subexp);
    var_index_fillin(psub->u.bexp.blist->bnext->subexp); 
    return;
  case FORALL : 
  case EXISTS :
    var_index_fillin(psub->u.qexp.lb_exp);
    var_index_fillin(psub->u.qexp.ub_exp);
    var_index_fillin(psub->u.qexp.child);
    return; 
  case RESET:
    psub->u.reset.clock_index = variable_index[psub->u.reset.var->type][0][psub->u.reset.var->index]; 
    psub->u.reset.clock_index = psub->u.reset.var->index; 
/*
    fprintf(RED_OUT, "Test: reset clock %s with clock id %1d.\n", psub->u.reset.clock_name, psub->u.reset.clock_index);
*/
    var_index_fillin(psub->u.reset.child); 
    return; 
  case FORALL_ALWAYS :
  case EXISTS_ALWAYS : 
  case FORALL_EVENTUALLY : 
  case EXISTS_EVENTUALLY :
  case EXISTS_CHANGE : 
  case FORALL_CHANGE :   
  case EXISTS_OFTEN : 
  case FORALL_OFTEN :   
  case EXISTS_ALMOST : 
  case FORALL_ALMOST :
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness); 
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness); 
    var_index_fillin(psub->u.mexp.time_restriction); 
    if (psub->u.mexp.event_restriction)
      var_index_fillin(psub->u.mexp.event_restriction); 
    var_index_fillin(psub->u.mexp.path_child); 
    return; 
  case FORALL_UNTIL : 
  case EXISTS_UNTIL :
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness);
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness);
    if (psub->u.mexp.event_restriction)
      var_index_fillin(psub->u.mexp.time_restriction); 
    var_index_fillin(psub->u.mexp.event_restriction); 
    var_index_fillin(psub->u.mexp.path_child);
    var_index_fillin(psub->u.mexp.dest_child); 
    return; 
  case TYPE_GAME_SIM: 
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness);
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) 
      var_index_fillin(fl->fairness);
    return; 
  
  case LINEAR_EVENT : 
    if (psub->u.eexp.event_exp)
      var_index_fillin(psub->u.eexp.event_exp); 
    var_index_fillin(psub->u.eexp.precond_exp); 
    var_index_fillin(psub->u.eexp.postcond_exp); 
    return; 
    
  case RED: 
    if (psub == PS_EXP_TRUE || psub == PS_EXP_FALSE) { 
      return; 
    } 
    
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal exp type %1d in var_index_fillin().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* var_index_fillin() */ 


#define	FLAG_ANALYZE_INITIAL	1 

struct ps_exp_type	*analyze_tctl(
  struct ps_exp_type	*psub, 
  int			flag_analyze_tctl, 
  int			flag_root_tctl  
) { 
  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\n=============================================\n"); 
  print_cpu_time("\nANA TCTL: Entering for:\n"); 
  pcform(psub); 
  print_tctctl_flag(psub); 
  #endif 
  
  var_index_fillin(psub);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after var_index_fillin\n"); 
  fprintf(RED_OUT, "\nThe negated parse spec after pushing negs.\n");
  pcform(psub);
  print_tctctl_flag(psub); 
  #endif 

  if (!(flag_analyze_tctl & FLAG_ANALYZE_INITIAL)) { 
    psub = rewrite_modal_timing(psub);
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("\nANA TCTL: after rewrite modal timing\n"); 
    fprintf(RED_OUT, "\nThe negated parse spec after rewriting modal timing constraints.\n");
    pcform(psub);
    print_tctctl_flag(psub); 
    #endif 
  }
//  fillin_indirect_reference(PROC_GLOBAL, psub);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after indirect references\n"); 
  fprintf(RED_OUT, "before changing event counts of the tctl spec.\n"); 
  pcform(psub); 
  fprintf(RED_OUT, "\n*** TCTCTL flags ***\n"); 
  print_tctctl_flag(psub); 
  print_cpu_time("\nANA TCTL: after printing tctctl flags\n"); 
  #endif 

  psub = spec_global(psub, PROC_GLOBAL, FLAG_LAZY_EVALUATION, 0); 
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after spec global\n"); 
  pcform(psub); 
  print_tctctl_flag(psub); 
  #endif 
  
  if (   (!(flag_analyze_tctl & FLAG_ANALYZE_INITIAL))
      && (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
         != FLAG_SYSTEM_HYBRID 
      && (GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_MODEL_CHECK 
      && (  GSTATUS[INDEX_TIME_PROGRESS_ANALYSIS] 
          & MASK_TIME_PROGRESS_ANALYSIS
          )   
         > FLAG_TIME_PROGRESS_ANALYSIS_NONE 
      ) {
    check_tctctl(psub); 
    #ifdef RED_DEBUG_PARSE_MODE 
    print_cpu_time("\nANA TCTL: after checking tctctl\n"); 
    pcform(psub); 
    print_tctctl_flag(psub); 
    #endif 
  }
  psub = shorthand_analysis(psub);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after shorthand_analysis\n"); 
  pcform(psub); 
  print_tctctl_flag(psub); 
  #endif 
  
  if (flag_root_tctl) { 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_SAFETY: 
    case TASK_MODEL_CHECK: 
      psub = add_neg(psub);
      #ifdef RED_DEBUG_PARSE_MODE 
      print_cpu_time("\nANA TCTL: after add neg\n"); 
      pcform(psub); 
      print_tctctl_flag(psub); 
      #endif 
      break; 
    } 
  }
  psub = push_neg(psub, TYPE_TRUE);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after pushing neg\n"); 
  pcform(psub); 
  print_tctctl_flag(psub); 
  #endif 

  ps_exp_mark(psub, FLAG_GC_STABLE);
  #ifdef RED_DEBUG_PARSE_MODE 
  print_cpu_time("\nANA TCTL: after red mark spec\n"); 
  print_tctctl_flag(psub); 
  #endif 

  return(psub); 
}
  /* analyze_tctl() */ 



