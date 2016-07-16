#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
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

#include "treeman.h" 
#include "treeman.e" 

#include "hybrid.e"

#include "action.e"

#include "fxp.h"
#include "fxp.e"

#include "bisim.e" 


struct ps_bunit_type	*diff_race_list = NULL; 

void	report_difficult_race(struct ps_exp_type *psub) { 
  struct ps_bunit_type	*bu; 
  
  for (bu = diff_race_list; bu; bu = bu->bnext) { 
    if (bu->subexp == psub) 
      return; 	
  } 
  bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
  bu->subexp = psub; 
  bu->bnext = diff_race_list; 
  diff_race_list = bu; 
  
  fprintf(RED_OUT, 
    "\nWarning: difficulty in offline race analysis due to indirection in:"
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
}
  /* report_difficult_race() */ 





/* Note that process id P in [-#PS, -1] means a process identifier for a peer process to process |P|. */ 

/*************************************
*  returns FALSE if vi is not written to in st by process pi.  
*/
int vi_writing_in_statement(vi, pi, st)
     int      vi, pi;
     struct statement_type  *st;
{
  int i, lhs_vi; 
  
  if (!st) 
    return(TYPE_FALSE); 
    
  switch (st->op) { 
  case ST_IF: 
    if (vi_writing_in_statement(vi, pi, st->u.branch.if_statement)) 
      return(TYPE_TRUE); 
    else if (   (st->st_status & FLAG_STATEMENT_ELSE)
       && vi_writing_in_statement(vi, pi, st->u.branch.else_statement)
       ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    if (vi_writing_in_statement(vi, pi, st->u.loop.statement)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count-1; i>=0; i--) 
      if (vi_writing_in_statement(vi, pi, st->u.seq.statement[i])) 
        return(TYPE_TRUE);  
    return(TYPE_FALSE); 
    break; 
  case ST_CALL: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
            || VAR[vi].OFFSET == var__retmode->index 
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_RETURN: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  default: 
    lhs_vi = st->u.act.lhs->u.atom.var_index;
    if (VAR[lhs_vi].PROC_INDEX) { 
      lhs_vi = variable_index[VAR[lhs_vi].TYPE][pi][VAR[lhs_vi].OFFSET];
      if (   lhs_vi == vi
          && (st->u.act.rhs_exp->type == TYPE_INTERVAL || st->u.act.rhs_exp->type == TYPE_CONSTANT) 
          ) 
      return(TYPE_TRUE);
    }
    return(TYPE_FALSE); 
    break;  
  } 
}
  /* vi_writing_in_statement() */ 



int vi_range_match_in_statement(vi, pi, mi, st) 
  int     vi, pi, mi; 
  struct statement_type *st; 
{ 
  int i, lhs_vi, lbn, lbd, ubn, ubd; 
  
  if (!st) 
    return(TYPE_FALSE); 
    
  switch (st->op) { 
  case ST_IF: 
    if (   (st->st_status & FLAG_STATEMENT_ELSE)
        && vi_range_match_in_statement(vi, pi, mi, st->u.branch.if_statement)
        && vi_range_match_in_statement(vi, pi, mi, st->u.branch.else_statement)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count-1; i>=0; i--) 
      if (vi_range_match_in_statement(vi, pi, mi, st->u.seq.statement[i])) 
        return(TYPE_TRUE);  
    return(TYPE_FALSE); 
    break; 
  case ST_CALL: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
            || VAR[vi].OFFSET == var__retmode->index 
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_RETURN: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  default:       
    lhs_vi = st->u.act.lhs->u.atom.var_index;
    if (VAR[lhs_vi].PROC_INDEX)
      lhs_vi = variable_index[VAR[lhs_vi].TYPE][pi][VAR[lhs_vi].OFFSET];
    if (lhs_vi != vi) {
      return(TYPE_FALSE);
    }
    else if (st->u.act.rhs_exp->type == TYPE_INTERVAL) {
      get_interval_rationals(st->u.act.rhs_exp, pi, &lbn, &lbd, &ubn, &ubd);
      if (   lbn == VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator
          && lbd == VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
          && ubn == VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator
          && ubd == VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator
          ) {
        return(TYPE_TRUE); 
      }
      else
        return(TYPE_FALSE);
    }
    else 
      return(TYPE_FALSE); 
  } 
}
  /* vi_range_match_in_statement() */  


  
  
    
  

struct a23tree_type *peer_tree;
int     XVI_ACTIVE, XCI, XFI, XPI; 


struct red_type *rec_active_variable_global_untimed_extract(d)
     struct red_type  *d; 
{
  int				ci, pc1, pc2; 
  struct red_type 		*result, *conj; 
  struct crd_child_type 	*bc;
  struct ddd_child_type 	*ic;
  struct hrd_child_type 	*hc;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_ACTIVE_VARIABLE_GLOBAL_UNTIMED_EXTRACT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    pc1 = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX;
    pc2 = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX;
    if (pc1 || pc2) {
      for (ci = 0; ci < d->u.crd.child_count; ci++)
        result = red_bop(OR, result, rec_active_variable_global_untimed_extract(d->u.crd.arc[ci].child));
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        bc = &(d->u.crd.arc[ci]);
        conj = crd_lone_subtree(rec_active_variable_global_untimed_extract(bc->child),
         d->var_index, bc->upper_bound
         );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      hc = &(d->u.hrd.arc[ci]);
      conj = hrd_lone_subtree(rec_active_variable_global_untimed_extract(hc->child),
         d->var_index, d->u.hrd.hrd_exp, hc->ub_numerator, hc->ub_denominator
         );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_lone_subtree(
        rec_active_variable_global_untimed_extract(d->u.fdd.arc[ci].child),
        d->var_index, d->u.fdd.arc[ci].lower_bound, 
        d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_lone_subtree(
        rec_active_variable_global_untimed_extract(d->u.dfdd.arc[ci].child),
        d->var_index, d->u.dfdd.arc[ci].lower_bound, 
        d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      ic = &(d->u.ddd.arc[ci]);
      conj = ddd_lone_subtree(rec_active_variable_global_untimed_extract(ic->child),
           d->var_index, ic->lower_bound, ic->upper_bound
           );
      result = red_bop(OR, result, conj);
    }
  }

  return(ce->result = result); 
}
/* rec_active_variable_global_untimed_extract() */



struct red_type *active_variable_global_untimed_extract(d, vi)
     struct red_type  *d;
     int    vi;
{
  struct red_type *result;

  result = rec_active_variable_global_untimed_extract(d);

  return(result);
}
/* active_variable_global_untimed_extract() */






struct red_type *rec_active_clock_support_extract(d)
     struct red_type  *d;
{
  int				ci, pc1, pc2;
  struct red_type 		*result, *conj;
  struct crd_child_type 	*bc;
  struct ddd_child_type 	*ic;
  struct hrd_child_type 	*hc;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_ACTIVE_CLOCK_SUPPORT_EXTRACT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    pc1 = VAR[d->var_index].U.CRD.CLOCK1;
    pc2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (pc1 == XCI || pc2 == XCI) {
      result = red_time_clock_eliminate(d, XCI);
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        bc = &(d->u.crd.arc[ci]);
        if (bc->child != NORM_FALSE && bc->child != NORM_TRUE) {
          conj = crd_lone_subtree(rec_active_clock_support_extract(bc->child),
           d->var_index, bc->upper_bound
           );
          result = red_bop(OR, result, conj);
        }
      }
    }
    break;

  case TYPE_HRD:

    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      hc = &(d->u.hrd.arc[ci]);
      if (hc->child != NORM_FALSE && hc->child != NORM_TRUE) {
        conj = hrd_lone_subtree(rec_active_clock_support_extract(hc->child),
           d->var_index, d->u.hrd.hrd_exp, hc->ub_numerator,
           hc->ub_denominator
           );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_FLOAT:

    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      if (   d->u.fdd.arc[ci].child != NORM_FALSE 
          && d->u.fdd.arc[ci].child != NORM_TRUE
          ) {
        conj = fdd_lone_subtree(
          rec_active_clock_support_extract(d->u.fdd.arc[ci].child),
          d->var_index, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_DOUBLE:

    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      if (   d->u.dfdd.arc[ci].child != NORM_FALSE 
          && d->u.dfdd.arc[ci].child != NORM_TRUE
          ) {
        conj = dfdd_lone_subtree(
          rec_active_clock_support_extract(d->u.dfdd.arc[ci].child),
          d->var_index, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  default:

    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      ic = &(d->u.ddd.arc[ci]);
      if (ic->child != NORM_FALSE && ic->child != NORM_TRUE) {
        conj = ddd_lone_subtree(rec_active_clock_support_extract(ic->child),
             d->var_index, ic->lower_bound, ic->upper_bound
             );
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_active_clock_support_extract() */






struct red_type *rec_active_global_untimed_extract(d)
     struct red_type  *d;
{
  int				ci, pc1, pc2;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_ACTIVE_GLOBAL_UNTIMED_EXTRACT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      result = red_bop(OR, result, rec_active_global_untimed_extract(d->u.crd.arc[ci].child));
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      result = red_bop(OR, result, rec_active_global_untimed_extract(d->u.hrd.arc[ci].child));
    }
    break;

  case TYPE_FLOAT:
    if(VAR[d->var_index].PROC_INDEX) {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        result = red_bop(OR, result, 
          rec_active_global_untimed_extract(d->u.fdd.arc[ci].child)
        );
      }
    }
    else {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = fdd_lone_subtree(
          rec_active_global_untimed_extract(d->u.fdd.arc[ci].child),
          d->var_index, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_DOUBLE:
    if(VAR[d->var_index].PROC_INDEX) {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        result = red_bop(OR, result, 
          rec_active_global_untimed_extract(d->u.dfdd.arc[ci].child)
        );
      }
    }
    else {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = fdd_lone_subtree(
          rec_active_global_untimed_extract(d->u.dfdd.arc[ci].child),
          d->var_index, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  default:
    if(VAR[d->var_index].PROC_INDEX) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        result = red_bop(OR, result, rec_active_global_untimed_extract(d->u.ddd.arc[ci].child));
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        conj = ddd_lone_subtree(rec_active_global_untimed_extract(ic->child),
             d->var_index, ic->lower_bound, ic->upper_bound
             );
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_active_global_untimed_extract() */



struct red_type *active_global_untimed_extract(d)
     struct red_type  *d; 
{
  struct red_type *result; 

  result = rec_active_global_untimed_extract(d);

  return(result);
}
/* active_global_untimed_extract() */ 









/*********************************************************************
 *  The following procedures are used to build variable activeness 
 *  characteristic formulas. 
 */ 

struct a23tree_type	*active_tree; 

struct red_type *rec_active_variable_support_extract(d)
     struct red_type  *d;
{
  int			ci;
  struct red_type 	*result, *conj;
  struct rec_type	*rec, *nrec; 

  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
//      || d->var_index > XVI_ACTIVE
      )
    return(NORM_FALSE);

  rec = rec_new(d, NORM_FALSE);
  nrec = (struct rec_type *) add_23tree(
    rec, active_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) 
    return(nrec->result); 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (CLOCK[VAR[d->var_index].U.CRD.CLOCK1] == XVI_ACTIVE || CLOCK[VAR[d->var_index].U.CRD.CLOCK2] == XVI_ACTIVE) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        conj = red_variable_eliminate(d->u.crd.arc[ci].child, XVI_ACTIVE);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        conj = crd_lone_subtree(rec_active_variable_support_extract(
            d->u.crd.arc[ci].child
          ),
          d->var_index, d->u.crd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (d->u.hrd.hrd_exp->hrd_term[ci].var_index == XVI_ACTIVE)
        break;
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = red_variable_eliminate(d->u.hrd.arc[ci].child, XVI_ACTIVE);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = hrd_lone_subtree(rec_active_variable_support_extract(
            d->u.hrd.arc[ci].child
          ),
          d->var_index, d->u.hrd.hrd_exp,
          d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_LAZY_EXP: 
    if (check_vi_in_exp_possibly(d->u.lazy.exp, XVI_ACTIVE) 
/*     	active_variable_support_extract_in_exp(
          XVI_ACTIVE, VAR[XVI_ACTIVE].PROC_INDEX, d->u.lazy.exp
        ) == TYPE_TRUE
*/	) {
      result = red_bop(OR, 
        red_variable_eliminate(d->u.lazy.false_child, XVI_ACTIVE), 
        red_variable_eliminate(d->u.lazy.true_child, XVI_ACTIVE)  
      ); 
    }
    else 
      result = lazy_2_cases(
        rec_active_variable_support_extract(d->u.lazy.false_child), 
        rec_active_variable_support_extract(d->u.lazy.true_child), 
        VAR[d->var_index].PROC_INDEX,  
        d->u.lazy.exp 
      ); 
    break; 

  case TYPE_FLOAT:
    if (d->var_index == XVI_ACTIVE) {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = red_variable_eliminate(d->u.fdd.arc[ci].child, XVI_ACTIVE);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = fdd_lone_subtree(
          rec_active_variable_support_extract(d->u.fdd.arc[ci].child),
          d->var_index, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj); 
      }
    }
    break; 

  case TYPE_DOUBLE:
    if (d->var_index == XVI_ACTIVE) {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = red_variable_eliminate(d->u.dfdd.arc[ci].child, XVI_ACTIVE);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = dfdd_lone_subtree(
          rec_active_variable_support_extract(d->u.dfdd.arc[ci].child),
          d->var_index, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj); 
      }
    }
    break; 

  default:
    if (d->var_index == XVI_ACTIVE) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = red_variable_eliminate(d->u.ddd.arc[ci].child, XVI_ACTIVE);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_lone_subtree(
          rec_active_variable_support_extract(d->u.ddd.arc[ci].child),
          d->var_index, 
          d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj); 
      }
    }
  }
  return(nrec->result = result); 
}
/* rec_active_variable_support_extract() */





struct red_type *rec_active_untimed_extract(d)
     struct red_type  *d;
{
  int			ci;
  struct red_type 	*result, *conj;
  struct rec_type	*rec, *nrec; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  rec = rec_new(d, NORM_FALSE);
  nrec = (struct rec_type *) add_23tree( 
    rec, active_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) 
    return(nrec->result); 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      result = red_bop(OR, result, rec_active_untimed_extract(d->u.crd.arc[ci].child));
    }
    break;

  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      result = red_bop(OR, result, rec_active_untimed_extract(d->u.hrd.arc[ci].child));
    }
    break;

  case TYPE_LAZY_EXP: 
    result = red_bop(OR, 
      rec_active_untimed_extract(d->u.lazy.false_child), 
      rec_active_untimed_extract(d->u.lazy.true_child)  
    ); 
    break; 
  case TYPE_FLOAT:
    if (   VAR[d->var_index].TYPE == TYPE_POINTER
        && VAR[d->var_index].PROC_INDEX
        && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = rec_active_untimed_extract(
            d->u.fdd.arc[ci].child
          );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = fdd_lone_subtree(rec_active_untimed_extract(
            d->u.fdd.arc[ci].child
          ), 
          d->var_index, d->u.fdd.arc[ci].lower_bound, 
          d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }
    break; 
  case TYPE_DOUBLE:
    if (   VAR[d->var_index].TYPE == TYPE_POINTER
        && VAR[d->var_index].PROC_INDEX
        && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = rec_active_untimed_extract(
            d->u.dfdd.arc[ci].child
          );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = dfdd_lone_subtree(rec_active_untimed_extract(
            d->u.dfdd.arc[ci].child
          ), 
          d->var_index, d->u.dfdd.arc[ci].lower_bound, 
          d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }
    break; 
  default:
    if (   VAR[d->var_index].TYPE == TYPE_POINTER
        && VAR[d->var_index].PROC_INDEX
        && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = rec_active_untimed_extract(
            d->u.ddd.arc[ci].child
          );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_lone_subtree(rec_active_untimed_extract(
            d->u.ddd.arc[ci].child
          ), 
          d->var_index, d->u.ddd.arc[ci].lower_bound, 
          d->u.ddd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }

    break;
  }
  return(nrec->result = result); 
}
/* rec_active_untimed_extract() */




// int	count_avsue = 0; 

struct red_type *red_active_variable_support_untimed_extract(d, vi)
     struct red_type  *d;
     int    vi;
{
  struct red_type *result;

  if (d == NORM_TRUE)
    return(NORM_FALSE);

  XVI_ACTIVE = vi;
/*
  ++count_avsue; 
  if (count_avsue == 713) { 
    fprintf(RED_OUT, "\ncaught count_avsue = %1d at vi=%1d\n", 
      count_avsue, vi
    ); 
    fflush(RED_OUT); 	
  } 
*/
  init_23tree(&active_tree);
  result = rec_active_variable_support_extract(d);
  free_entire_23tree(active_tree, rec_free); 
  
  init_23tree(&active_tree);
  result = rec_active_untimed_extract(result);
  free_entire_23tree(active_tree, rec_free);

  return(result);
}
/* red_active_variable_support_untimed_extract() */





struct red_type *red_active_untimed_extract(d)
     struct red_type  *d;
{
  init_23tree(&active_tree);
  d = rec_active_untimed_extract(d);
  free_entire_23tree(active_tree, rec_free);

  return(d);
}
/* red_active_untimed_extract() */








struct red_type *rec_peer_active_untimed_extract(d)
     struct red_type  *d;
{
  int			ci;
  struct red_type 	*result, *conj;
  struct rec_type	*rec, *nrec; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  rec = rec_new(d, NORM_FALSE);
  nrec = (struct rec_type *) add_23tree( 
    rec, active_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) 
    return(nrec->result); 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      result = red_bop(OR, result, rec_peer_active_untimed_extract(d->u.crd.arc[ci].child));
    }
    break;

  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      result = red_bop(OR, result, rec_peer_active_untimed_extract(d->u.hrd.arc[ci].child));
    }
    break;

  case TYPE_LAZY_EXP: 
    result = red_bop(OR, 
      rec_peer_active_untimed_extract(d->u.lazy.false_child), 
      rec_peer_active_untimed_extract(d->u.lazy.true_child)  
    ); 
    break; 
  case TYPE_FLOAT:
    if (   VAR[d->var_index].PROC_INDEX 
        && (   VAR[d->var_index].PROC_INDEX != VAR[XVI_ACTIVE].PROC_INDEX 
            || (   VAR[d->var_index].TYPE == TYPE_POINTER
                && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        )   )   ) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = rec_peer_active_untimed_extract(
          d->u.fdd.arc[ci].child
        );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        conj = fdd_lone_subtree(rec_peer_active_untimed_extract(
            d->u.fdd.arc[ci].child
          ), 
          d->var_index, d->u.fdd.arc[ci].lower_bound, 
          d->u.fdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }

    break; 
   case TYPE_DOUBLE:
    if (   VAR[d->var_index].PROC_INDEX 
        && (   VAR[d->var_index].PROC_INDEX != VAR[XVI_ACTIVE].PROC_INDEX 
            || (   VAR[d->var_index].TYPE == TYPE_POINTER
                && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        )   )   ) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = rec_peer_active_untimed_extract(
          d->u.dfdd.arc[ci].child
        );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        conj = dfdd_lone_subtree(rec_peer_active_untimed_extract(
            d->u.dfdd.arc[ci].child
          ), 
          d->var_index, d->u.dfdd.arc[ci].lower_bound, 
          d->u.dfdd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }

    break; 
  default:
    if (   VAR[d->var_index].PROC_INDEX 
        && (   VAR[d->var_index].PROC_INDEX != VAR[XVI_ACTIVE].PROC_INDEX 
            || (   VAR[d->var_index].TYPE == TYPE_POINTER
                && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        )   )   ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = rec_peer_active_untimed_extract(
          d->u.ddd.arc[ci].child
        );
        result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_lone_subtree(rec_peer_active_untimed_extract(
            d->u.ddd.arc[ci].child
          ), 
          d->var_index, d->u.ddd.arc[ci].lower_bound, 
          d->u.ddd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
    } }

    break;
  }
  return(nrec->result = result); 
}
/* rec_peer_active_untimed_extract() */




// int	count_avsue = 0; 

struct red_type *red_peer_active_variable_support_untimed_extract(d, vi)
     struct red_type  *d;
     int    vi;
{
  struct red_type *result;

  if (d == NORM_TRUE)
    return(NORM_FALSE);

  XVI_ACTIVE = vi;
/*
  ++count_avsue; 
  if (count_avsue == 713) { 
    fprintf(RED_OUT, "\ncaught count_avsue = %1d at vi=%1d\n", 
      count_avsue, vi
    ); 
    fflush(RED_OUT); 	
  } 
*/
  init_23tree(&active_tree);
  result = rec_active_variable_support_extract(d);
  free_entire_23tree(active_tree, rec_free); 
  
  init_23tree(&active_tree);
  result = rec_peer_active_untimed_extract(result);
  free_entire_23tree(active_tree, rec_free);

  return(result);
}
/* red_peer_active_variable_support_untimed_extract() */





struct red_type *red_peer_active_untimed_extract(d)
     struct red_type  *d;
{
  init_23tree(&active_tree);
  d = rec_peer_active_untimed_extract(d);
  free_entire_23tree(active_tree, rec_free);

  return(d);
}
/* red_peer_active_untimed_extract() */



/* Returns 3 values: 
 * TYPE_TRUE: used. 
 * TYPE_FALSE: not used.  
 * FLAG_ANNIHILATED: assigned to without being referenced in the same atomic action. 
 */ 
#define FLAG_ANNIHILATED  2



int	count_avse_exp = 0; 

int	active_variable_support_extract_in_exp(vi, pi, psub) 
     int    vi, pi;
     struct ps_exp_type *psub; 
{
  int     		dvi, pk, ii, flag; 
  struct ps_bunit_type  *pbu; 

  if (pi < 0) {
    fprintf(RED_OUT, "\nError, a negative process id in xtion_action_variable_support_untimed_extract.\n"); 
    bk(""); 
  } 
  if (!psub)
    return(TYPE_FALSE); 

  switch (psub->type) { 
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_NULL: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_INTERVAL: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
    return(TYPE_FALSE);
  case TYPE_REFERENCE: 
    if (   psub->u.exp->type != TYPE_REFERENCE
        && !(psub->u.exp->var_status & FLAG_EXP_STATE_INSIDE)
        ) {
      dvi = get_value(psub->u.exp, pi, &flag); 
      if (dvi == vi)
        return(TYPE_TRUE);       
      else 
        return(TYPE_FALSE); 
    } 
    else { 
      report_difficult_race(psub); 
      return(TYPE_TRUE); 
    }
    break; 
  
  case TYPE_DEREFERENCE: 
    if (active_variable_support_extract_in_exp(
          vi, pi, psub->u.exp->u.atom.exp_base_proc_index
          ) == TYPE_TRUE
        ) 
      return(TYPE_TRUE); 
/*
    for (ii = 0; ii < psub->u.exp->u.atom.indirect_count; ii++) { 
      if (active_variable_support_extract_in_exp(
            vi, pi, psub->u.exp->u.atom.indirect_exp[ii] 
            ) == TYPE_TRUE
          ) {
        return(TYPE_TRUE); 
    } } 
*/
    return(TYPE_FALSE); 
    break; 

  case TYPE_QFD: 
    fprintf(RED_OUT, "\nHuh ? (inactive 10)\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk("10"); 
    exit(0); 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
/*
    if (psub->u.atom.indirect_count > 0) 
      if (   VAR[vi].TYPE == TYPE_DISCRETE
          || VAR[vi].TYPE == TYPE_POINTER
          ) { 
        return(TYPE_TRUE); 
      }
      else 
        return(TYPE_FALSE); 
    else 
    */
    if (!(psub->var_status & FLAG_LOCAL_VARIABLE)) 
      if (psub->u.atom.var_index == vi) 
        return(TYPE_TRUE); 
      else 
        return(TYPE_FALSE);  
    else if (   psub->type != VAR[vi].TYPE
             || psub->u.atom.var->index != VAR[vi].OFFSET
             )     
      return(TYPE_FALSE); 
    if (active_variable_support_extract_in_exp(
          vi, pi, psub->u.atom.exp_base_proc_index
          ) == TYPE_TRUE
        ) 
      return(TYPE_TRUE); 
    pk = get_address(psub->u.atom.exp_base_proc_index, pi, &flag); 
    if (   flag != FLAG_SPECIFIC_VALUE
        || pk == VAR[vi].PROC_INDEX
        ) { 
    /* This covers the case whether there is an indirection or not. */ 
      return(TYPE_TRUE); 
    } 
    else 
      return(TYPE_FALSE); 
    break; 

  case TYPE_CLOCK:
  case TYPE_DENSE: 
/*
    if (psub->u.atom.indirect_count) { 
      fprintf(RED_OUT, "\nERROR, incompatible pointer type %1d:\n", psub->type); 
      pcform(psub); 
      fflush(RED_OUT); 
      bk(0); 
    } 
*/
    if (!(psub->var_status & FLAG_LOCAL_VARIABLE)) 
      return(TYPE_FALSE);  
    if (active_variable_support_extract_in_exp(
          vi, pi, psub->u.atom.exp_base_proc_index
          ) == TYPE_TRUE
        ) 
      return(TYPE_TRUE); 
    if (   VAR[vi].TYPE != psub->type 
        || VAR[vi].OFFSET != psub->u.atom.var->index
        ) { 
    /* This covers the case whether there is an indirection or not. */ 
      return(TYPE_FALSE); 
    } 
    pk = get_address(psub->u.atom.exp_base_proc_index, pi, &flag); 
    if (flag != FLAG_SPECIFIC_VALUE || VAR[vi].PROC_INDEX == pk) { 
    /* This covers the case whether there is an indirection or not. */ 
      return(TYPE_TRUE); 
    } 
    else {
      return(TYPE_FALSE); 
    } 
    break; 

  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    for (ii = 0; ii < psub->u.ineq.term_count; ii++) { 
      if (active_variable_support_extract_in_exp(
            vi, pi, psub->u.ineq.term[ii].operand
          ) )  
        return(TYPE_TRUE); 
    }
    return(active_variable_support_extract_in_exp(
      vi, pi, psub->u.ineq.offset
    ) ); 
    break; 

  case BIT_NOT: 
    return(active_variable_support_extract_in_exp(vi, pi, psub->u.exp)); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD :
  case ARITH_MINUS :
  case ARITH_MULTIPLY :
  case ARITH_DIVIDE :
  case ARITH_MODULO: 
  case ARITH_LESS :
  case ARITH_LEQ :
  case ARITH_GEQ :
  case ARITH_GREATER :
  case ARITH_EQ :
  case ARITH_NEQ :
    return(  active_variable_support_extract_in_exp(vi, pi, psub->u.arith.lhs_exp)
     | active_variable_support_extract_in_exp(vi, pi, psub->u.arith.rhs_exp)
     ); 
  case ARITH_CONDITIONAL: 
    return(
      active_variable_support_extract_in_exp(
        vi, pi, psub->u.arith_cond.cond
      )
    | active_variable_support_extract_in_exp(
        vi, pi, psub->u.arith_cond.if_exp
      )
    | active_variable_support_extract_in_exp(
        vi, pi, psub->u.arith_cond.else_exp
      )
    ); 
  
  case TYPE_INLINE_CALL: 
    return(
      active_variable_support_extract_in_exp(
        vi, pi, psub->u.inline_call.instantiated_exp
      )
    ); 
  case AND: 
  case OR: 
  case IMPLY: 
  case NOT: 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) 
      if (active_variable_support_extract_in_exp(vi, pi, pbu->subexp)) 
        return(TYPE_TRUE); 
    return(TYPE_FALSE); 
  case FORALL: 
  case EXISTS: 
    if (active_variable_support_extract_in_exp(
          vi, pi, psub->u.qexp.child
        ) ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    
  default:
    fprintf(RED_OUT, "\nHuh psub->type %1d ? (inactive 2) \n", psub->type);
    fflush(RED_OUT); 
    bk(); 
  }
}
/* active_variable_support_extract_in_exp() */



int	active_variable_support_untimed_extract_in_statement( 
  int			vi, 
  int			pi, 
  struct statement_type	*st  
) { 
  int i, lvi, dvi, pk, child_value, flag; 
  
  if (pi < 0) {
    fprintf(RED_OUT, "\nError, a negative process id in xtion_action_variable_support_untimed_extract.\n"); 
    bk(""); 
  } 
  if (!st)
    return(TYPE_FALSE); 
    
  switch (st->op) { 
  case ST_IF: 
    if (active_variable_support_extract_in_exp
        (vi, pi, st->parse_statement->u.branch.cond))
      return(TYPE_TRUE); 
    child_value = active_variable_support_untimed_extract_in_statement
            (vi, pi, st->u.branch.if_statement); 
    if (child_value == TYPE_TRUE)
      return(TYPE_TRUE); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      int else_value; 
      
      else_value = active_variable_support_untimed_extract_in_statement
      (vi, pi, st->u.branch.else_statement); 
      if (else_value == TYPE_TRUE)
        return(TYPE_TRUE); 
      else if (child_value == FLAG_ANNIHILATED && else_value == FLAG_ANNIHILATED) 
        return(FLAG_ANNIHILATED); 
    } 
    return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    if (active_variable_support_extract_in_exp
        (vi, pi, st->parse_statement->u.loop.cond) == TYPE_TRUE
        )
      return(TYPE_TRUE); 
    else if (active_variable_support_untimed_extract_in_statement
             (vi, pi, st->u.loop.statement) == TYPE_TRUE 
             )
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    child_value = TYPE_FALSE; 
    for (i = st->u.seq.count-1; i>=0; i--) { 
      switch (active_variable_support_untimed_extract_in_statement
                (vi, pi, st->u.seq.statement[i])
              ) {
      case TYPE_TRUE: 
        child_value = TYPE_TRUE; 
        break; 
      case TYPE_FALSE: 
        break; 
      case FLAG_ANNIHILATED: 
        child_value = FLAG_ANNIHILATED; 
      } 
    } 
    return(child_value); 
    break; 
  case ST_CALL: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
            || VAR[vi].OFFSET == var__retmode->index 
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_RETURN: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
        )   ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    if (st->u.act.lhs->type == TYPE_REFERENCE) { 
      return(TYPE_TRUE); 
    } 
    else if (active_variable_support_extract_in_exp
             (vi, pi, st->u.act.lhs->u.atom.exp_base_proc_index) 
             == TYPE_TRUE
             ) 
      return(TYPE_TRUE); 
    lvi = get_variable_index(st->u.act.lhs, pi); 
    if (lvi < 0) { 
      if (   VAR[lvi].TYPE == VAR[vi].TYPE 
          && VAR[vi].PROC_INDEX 
          && VAR[lvi].OFFSET == VAR[vi].OFFSET 
          ) { 
        return(TYPE_TRUE); 
      } 
    } 
    else /* if (st->u.act.lhs->u.atom.indirect_count == 0) */ { 
      if (lvi == vi) 
        return(TYPE_TRUE); 
      else 
        return(TYPE_FALSE); 
    } 
/*
    for (i = 0; i < st->u.act.lhs->u.atom.indirect_count; i++) { 
      if (active_variable_support_extract_in_exp(
            vi, pi, st->u.act.lhs->u.atom.indirect_exp[i]
          ) ) {
        return(TYPE_TRUE); 
      } 
    } 
*/
    if (!(  GSTATUS[INDEX_COMPLEX_INDIRECT_SHAPES] 
          & FLAG_COMPLEX_INDIRECT_SHAPES
        ) ) {
      GSTATUS[INDEX_COMPLEX_INDIRECT_SHAPES] 
      = GSTATUS[INDEX_COMPLEX_INDIRECT_SHAPES] 
      | FLAG_COMPLEX_INDIRECT_SHAPES; 
      fprintf(RED_OUT, 
        "\nWarning: difficulty in offline inactiveness analysis \n"
      ); 
      fprintf(RED_OUT, 
        "         due to indirection in: "
      ); 
      pcform(st->u.act.lhs); 
      fprintf(RED_OUT, 
        "         Similar warnings will be omitted.\n"
      ); 
      fflush(RED_OUT); 
    }
    return(TYPE_TRUE); 
    break;
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    if (st->u.act.lhs->type == TYPE_REFERENCE) { 
      switch (st->u.act.lhs->u.exp->type) { 
      case TYPE_REFERENCE: 
        return(TYPE_TRUE); 
      case TYPE_CLOCK: 
      case TYPE_DENSE: 
      case TYPE_DISCRETE: 
      case TYPE_POINTER: 
        if (VAR[vi].PROC_INDEX == 0) 
          if (vi == st->u.act.lhs->u.exp->u.atom.var_index) { 
            return(TYPE_TRUE); 	
          } 
          else 
            return(TYPE_FALSE); 
        else 
          if (   VAR[st->u.act.lhs->u.exp->u.atom.var_index].TYPE 
                 == VAR[vi].TYPE
              && VAR[st->u.act.lhs->u.exp->u.atom.var_index].OFFSET 
                 == VAR[vi].OFFSET
              ) {
            return(TYPE_TRUE); 
          } 
          else 
            return(TYPE_FALSE); 
        break; 
      default: 
        return(TYPE_TRUE); 
    } }
    if (active_variable_support_extract_in_exp(
          vi, pi, st->u.act.lhs->u.atom.exp_base_proc_index
        ) == TYPE_TRUE) 
      return(TYPE_TRUE); 
    lvi = get_variable_index(st->u.act.lhs, pi); 
    child_value = active_variable_support_extract_in_exp(
      vi, pi, st->u.act.rhs_exp
    ); 
    if (   lvi == vi 
        && child_value == TYPE_FALSE
        ) { 
      return(FLAG_ANNIHILATED); 
    } 
    else if (child_value == TYPE_TRUE) 
      return(child_value); 
/*
    if (st->u.act.lhs->u.atom.indirect_count > 0) {
      return(TYPE_TRUE); 
    }
*/
    return(TYPE_FALSE);
  }
} 
  /* active_variable_support_untimed_extract_in_statement() */ 
  
  
  
int	count_xavsue = 0; 

struct red_type *red_xtion_active_variable_support_untimed_extract( 
  int	vi  
) {
  int			pi, imi, mi, ixi, xi;
  struct red_type	*result, *subresult, *conj;

/*
  fprintf(RED_OUT, 
    "%1d, Entering red_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n",
    ++count_xavsue, vi, VAR[vi].NAME  
  ); 
  fflush(RED_OUT); 
*/
  XVI_ACTIVE = vi;
  pi = VAR[vi].PROC_INDEX; 
  if (pi == 0) 
    return(NORM_NO_RESTRICTION); 

  result = NORM_FALSE; 
  for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) { 
    mi = PROCESS[pi].reachable_mode[imi]; 
    result = red_bop(OR, result, 
      red_active_variable_support_untimed_extract(
        MODE[mi].invariance[pi].red, vi
    ) ); 
/*
    fprintf(RED_OUT, 
      "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
      vi, VAR[vi].NAME
    ); 
    fprintf(RED_OUT, "loop for mode %1d:%s inv:\n", 
      mi, MODE[mi].name
    ); 
    red_print_graph(result); 
*/
  }

  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
    xi = PROCESS[pi].firable_xtion[ixi]; 
    mi = XTION[xi].src_mode_index; 
    subresult = XTION[xi].red_trigger[pi];
    if (valid_mode_index(mi)) { 
      subresult = red_bop(AND, subresult, MODE[mi].invariance[pi].red); 
/*
      fprintf(RED_OUT, 
        "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
        vi, VAR[vi].NAME
      ); 
      fprintf(RED_OUT, "conjunct for mode %1d:%s, xi=%1d trigger:\n", 
        mi, MODE[mi].name, xi 
      ); 
      red_print_graph(subresult); 
*/
    }
    if (active_variable_support_untimed_extract_in_statement(
          vi, pi, XTION[xi].statement
        ) == TYPE_TRUE
        ) {
      subresult = red_active_untimed_extract(subresult);
/*
      fprintf(RED_OUT, 
        "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
        vi, VAR[vi].NAME
      ); 
      fprintf(RED_OUT, "untimed extract for mode %1d:%s, xi=%1d trigger:\n", 
        mi, MODE[mi].name, xi 
      ); 
      red_print_graph(subresult); 
*/
      subresult = red_variable_eliminate(subresult, vi); 
/*
      fprintf(RED_OUT, 
        "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
        vi, VAR[vi].NAME
      ); 
      fprintf(RED_OUT, "var elm for mode %1d:%s, xi=%1d trigger:\n", 
        mi, MODE[mi].name, xi 
      ); 
      red_print_graph(subresult); 
*/
    }
    else {
      subresult = red_active_variable_support_untimed_extract(
        subresult, vi
      );
/*
      fprintf(RED_OUT, 
        "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
        vi, VAR[vi].NAME
      ); 
      fprintf(RED_OUT, "act var support untimed elm for mode %1d:%s, xi=%1d trigger:\n", 
        mi, MODE[mi].name, xi 
      ); 
      red_print_graph(subresult); 
*/
    }
    result = red_bop(OR, result, subresult); 
/*
    fprintf(RED_OUT, 
      "\nred_xtion_active_variable_support_untimed_extract(vi=%1d:%s)\n", 
      vi, VAR[vi].NAME
    ); 
    fprintf(RED_OUT, "result OR for mode %1d:%s, xi=%1d result:\n", 
      mi, MODE[mi].name, xi 
    ); 
    red_print_graph(result); 
*/
  }
  /*
  fprintf(RED_OUT, "\n+++++++++++++++++++++++++++++++++++++++++++++++++++\n");
  fprintf(RED_OUT, "Leaving red_xtion_active_variable_support_untimed_extract(vi=%1d:%s, pi=%1d, xi=%1d)\n",
    vi, VAR[vi].NAME, pi, xi
    );
  print_parse_xtion(XTION[xi].parse_xtion, 0);
  fprintf(RED_OUT, "Output is \n");
  red_print_graph(result);
  fflush(RED_OUT);
  */
  return(result);
}
/* red_xtion_active_variable_support_untimed_extract() */



int	count_pxavsu_ex = 0; 

struct red_type *red_peer_xtion_active_variable_support_untimed_extract( 
  int	vi  
) {
  int			imi, mi, pj, ixi, xi;
  struct red_type	*result, *subresult, *conj;

/*
  fprintf(RED_OUT, 
    "%1d, Entering red_xtion_active_variable_support_untimed_extract(vi=%1d:%s, pi=%1d, xi=%1d, st=%x)\n",
    ++count_xavsue, vi, VAR[vi].NAME, pi, xi, XTION[xi].statement 
  ); 
  fflush(RED_OUT); 
*/
  XVI_ACTIVE = vi;
  if (VAR[vi].PROC_INDEX == 0) 
    return(NORM_NO_RESTRICTION); 
  
  result = NORM_FALSE; 
  for (pj = 1; pj <= PROCESS_COUNT; pj++) { 
    if (VAR[vi].PROC_INDEX == pj) 
      continue; 

    for (imi = 0; imi < PROCESS[pj].reachable_mode_count; imi++) { 
      mi = PROCESS[pj].reachable_mode[imi]; 
      result = red_bop(OR, result, 
        red_peer_active_variable_support_untimed_extract(
          MODE[mi].invariance[pj].red, vi
      ) ); 
    }

    for (ixi = 0; ixi < PROCESS[pj].firable_xtion_count; ixi++) { 
      xi = PROCESS[pj].firable_xtion[ixi]; 
      if (active_variable_support_untimed_extract_in_statement(
            vi, pj, XTION[xi].statement
          ) == TYPE_TRUE
          ) {
        init_23tree(&active_tree);
        subresult = rec_peer_active_untimed_extract(XTION[xi].red_trigger[pj]);
        free_entire_23tree(active_tree, rec_free);
        subresult = red_variable_eliminate(subresult, vi); 

        mi = XTION[xi].src_mode_index; 
        if (valid_mode_index(mi)) { 
          init_23tree(&active_tree);
          conj = rec_peer_active_untimed_extract(MODE[mi].invariance[pj].red);
          free_entire_23tree(active_tree, rec_free);
          conj = red_variable_eliminate(conj, vi); 
          subresult = red_bop(AND, subresult, conj); 
        }
        subresult = red_qsync_eliminate(subresult); 
      } 
      else {
      	mi = XTION[xi].src_mode_index; 
/*
        fprintf(RED_OUT, 
          "\npeer active vsu ex %1d, for vi %1d:%s, xi %1d, pj %1d, red_trigger:\n", 
          ++count_pxavsu_ex, vi, VAR[vi].NAME, xi, pj 
        ); 
        red_print_graph(XTION[xi].red_trigger[pj]); 
        if (mi >= 0 && mi < MODE_COUNT) 
          red_print_graph(MODE[mi].invariance[pj].red); 
        fflush(RED_OUT);
*/        
        subresult = red_peer_active_variable_support_untimed_extract(
          XTION[xi].red_trigger[pj], vi
        );
        if (mi >= 0 && mi < MODE_COUNT) 
          subresult = red_bop(AND, subresult, 
            red_peer_active_variable_support_untimed_extract(
              MODE[mi].invariance[pj].red, vi
          ) );
      }
      result = red_bop(OR, result, subresult); 
  } }
  /*
  fprintf(RED_OUT, "\n+++++++++++++++++++++++++++++++++++++++++++++++++++\n");
  fprintf(RED_OUT, "Leaving red_xtion_active_variable_support_untimed_extract(vi=%1d:%s, pi=%1d, xi=%1d)\n",
    vi, VAR[vi].NAME, pi, xi
    );
  print_parse_xtion(XTION[xi].parse_xtion, 0);
  fprintf(RED_OUT, "Output is \n");
  red_print_graph(result);
  fflush(RED_OUT);
  */
  
  return(result);
}
  /* red_peer_xtion_active_variable_support_untimed_extract() */












rec_get_all_universal_references(psub)
     struct ps_exp_type *psub; 
{
  int       dvi, id, pi, rvi; 

  switch (psub->type) {
  case TYPE_REFERENCE: 
    for (rvi = 0; rvi < VARIABLE_COUNT; rvi++) 
      if (VAR[rvi].PROC_INDEX == 0 && VAR[rvi].TYPE == TYPE_DISCRETE) { 
      	VAR[rvi].RED_ACTIVE = NORM_NO_RESTRICTION;
      } 
    break; 
  case TYPE_DEREFERENCE: 
    rec_get_all_universal_references(psub->u.exp);
    break; 
  case TYPE_POINTER: 
  case TYPE_CLOCK: 
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_DENSE:
    if (!(psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)) { 
      VAR[psub->u.atom.var_index].RED_ACTIVE = NORM_NO_RESTRICTION;
    } 
    rec_get_all_universal_references(psub->u.atom.exp_base_proc_index);
/*
    for (id = 0; id < psub->u.atom.indirect_count; id++) {
      rec_get_all_universal_references(psub->u.atom.indirect_exp[id]);
    }   
*/
    break; 
  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    rec_get_all_universal_references(psub->u.arith.lhs_exp);
    rec_get_all_universal_references(psub->u.arith.rhs_exp);
  }
}
/* rec_get_all_universal_references() */






  
/*************************************
 *  The following procedures calculates the precondition from the local process viewpoint. 
 *  STA means Single-Thread Approximation.  
 *  Any peer process id are approximated to no restriction. 
 */

  
  





struct red_type *red_action_discrete_assign_simple_bck_STA(W, pi, act)
     int      W, pi; 
     struct statement_type  *act; 
{
  struct red_type *result; 
  
  result = red_action_discrete_assign_bck(W, act, pi); 
  if (act->st_status & FLAG_ACTION_QUANTIFIED_SYNC) 
    result = red_eliminate_proc_qfd_sync(result, pi); 
/*
  result = red_peer_eliminate(result, pi); 
*/  
  return(result); 
}
/* red_action_discrete_assign_simple_bck_STA() */






struct red_type *red_action_discrete_assign_exp_bck_STA(W, pi, act)
     int      W, pi;
     struct statement_type  *act;
{
  struct red_type *result; 
  
  result = red_action_discrete_assign_bck(W, act, pi); 
  if (act->st_status & FLAG_ACTION_QUANTIFIED_SYNC) 
    result = red_eliminate_proc_qfd_sync(result, pi); 
  result = red_peer_eliminate(result, pi); 
  
  return(result); 
}
/* red_action_discrete_assign_exp_bck_STA() */ 





struct red_type *action_inactive_weakest_precondition(d, vi, pi, st)
  struct red_type 	*d; 
  int     		vi, pi; 
  struct statement_type *st; 
{
  int			lvi, rvalue, flag, lb, ub; 
  float			flb, fub; 
  struct red_type	*conj; 
  
  switch (st->op) {
  case ASSIGN_DISCRETE_CONSTANT: 
    lvi = st->u.act.lhs->u.atom.var_index; 
    switch (get_integer_range(st->u.act.rhs_exp, pi, &lb, &ub, &flb, &fub)) {
    case FLAG_SPECIFIC_VALUE: 
      switch (VAR[lvi].TYPE) { 
      case TYPE_FLOAT: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            fdd_one_constraint(d, lvi, (float) lb, (float) ub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              fdd_one_constraint(d, lvi, (float) lb, (float) ub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                fdd_one_constraint(d, lvi, (float) lb, (float) ub), lvi 
              ); 
          }
        }
        break; 
      case TYPE_DOUBLE: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            dfdd_one_constraint(d, lvi, (double) lb, (double) ub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              dfdd_one_constraint(d, lvi, (double) lb, (double) ub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                dfdd_one_constraint(d, lvi, (double) lb, (double) ub), lvi 
              ); 
          }
        }
        break; 
      default: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            ddd_one_constraint(d, lvi, lb, ub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              ddd_one_constraint(d, lvi, lb, ub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                ddd_one_constraint(d, lvi, lb, ub), lvi 
              ); 
          }
        }
        break; 
      }
      break; 
    case FLAG_SPECIFIC_FLOAT_VALUE: 
      switch (VAR[lvi].TYPE) { 
      case TYPE_FLOAT: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            fdd_one_constraint(d, lvi, flb, fub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              fdd_one_constraint(d, lvi, flb, fub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                fdd_one_constraint(d, lvi, flb, fub), lvi 
              ); 
          }
        }
        break; 
      case TYPE_DOUBLE: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            dfdd_one_constraint(d, lvi, (double) flb, (double) fub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              dfdd_one_constraint(d, lvi, (double) flb, (double) fub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                dfdd_one_constraint(d, lvi, (double) flb, (double) fub), lvi 
              ); 
          }
        }
        break; 
      default: 
        if (VAR[lvi].PROC_INDEX == 0) {
          d = red_variable_eliminate(
            ddd_one_constraint(d, lvi, (int) flb, (int) fub), lvi
          ); 
        }
/*
        else if (st->u.act.lhs->u.atom.indirect_count > 0) {
          lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
          if (lvi != vi) {
            conj = red_variable_eliminate(
              ddd_one_constraint(d, lvi, (int) flb, (int) fub), lvi 
            ); 
            d = red_bop(OR, d, conj); 
          }
        }
*/
        else {
          int	addr;

          addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
            pi, &flag
          ); 
          if (   flag == FLAG_SPECIFIC_VALUE
              && addr > 0 
              && addr <= PROCESS_COUNT
              && addr == VAR[vi].PROC_INDEX
              ) {
            lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
            if (lvi == vi) 
              d = NORM_FALSE; 
            else 
              d = red_variable_eliminate(
                ddd_one_constraint(d, lvi, (int) flb, (int) fub), lvi 
              ); 
          }
        }
        break; 
      }
      break; 
    case FLAG_UNSPECIFIC_VALUE: 
      if (VAR[lvi].PROC_INDEX == 0) {
        d = red_variable_eliminate(d, lvi); 
      }
/*
      else if (st->u.act.lhs->u.atom.indirect_count > 0) {
        lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
        if (lvi != vi) {
          conj = red_variable_eliminate(d, lvi); 
          d = red_bop(OR, d, conj); 
        }
      }
*/
      else {
        int	addr;

        addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
          pi, &flag
        ); 
        if (   flag == FLAG_SPECIFIC_VALUE
            && addr > 0 
            && addr <= PROCESS_COUNT
            && addr == VAR[vi].PROC_INDEX
            ) {
          lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
          if (lvi == vi) 
            d = NORM_FALSE; 
          else 
            d = red_variable_eliminate(d, lvi); 
        }
      }
      break; 
    }
    break;

  case ASSIGN_DISCRETE_POLYNOMIAL: 
    if (st->u.act.lhs->type == TYPE_REFERENCE) { 
      d = NORM_NO_RESTRICTION; 
      break; 
    } 
    lvi = st->u.act.lhs->u.atom.var_index; 
    if (VAR[lvi].PROC_INDEX == 0) {
      d = red_variable_eliminate(d, lvi); 
    }
/*
    else if (st->u.act.lhs->u.atom.indirect_count) {
      lvi = variable_index[VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
      if (lvi != vi) 
        d = red_variable_eliminate(d, lvi); 
    }
*/
    else {
      int	addr;

      addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
        pi, &flag
      ); 
      if (   flag != FLAG_SPECIFIC_VALUE
          || addr <= 0 
          || addr > PROCESS_COUNT          || addr == VAR[vi].PROC_INDEX
          ) { 
        lvi = variable_index
          [VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
        if (lvi != vi) 
          d = red_variable_eliminate(d, lvi); 
      } 
      else if (addr == VAR[vi].PROC_INDEX) { 
        lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
        if (lvi == vi) 
          d = NORM_FALSE; 
        else 
          d = red_variable_eliminate(d, lvi); 
      } 
    }
    break;

  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    lvi = st->u.act.lhs->u.atom.var_index; 
    if (   VAR[lvi].PROC_INDEX > 0
//        && st->u.act.lhs->u.atom.indirect_count == 0
        ) {
      int	addr;

      addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
        pi, &flag
      ); 
      if (   flag == FLAG_SPECIFIC_VALUE
          && addr == VAR[vi].PROC_INDEX
          ) { 
        lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
        if (lvi == vi) 
          d = NORM_FALSE; 
    } }
    break;
  case INCREMENT_BY_CONSTANT:
    lvi = st->u.act.lhs->u.atom.var_index; 
    rvalue = get_value(st->u.act.rhs_exp, pi, &flag); 
    if (VAR[lvi].PROC_INDEX == 0) {
      d = red_inc_off(d, lvi, -1*rvalue, -1*rvalue);
    }
/*
    else if (st->u.act.lhs->u.atom.indirect_count > 0) {
      lvi = variable_index
        [VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
      if (lvi != vi) { 
        d = red_bop(OR, d, 
          red_inc_off(d, lvi, -1*rvalue, -1*rvalue)
        );
      }
    }
*/
    else {
      int	addr;

      addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
        pi, &flag
      ); 
      if (   flag != FLAG_SPECIFIC_VALUE
          || addr <= 0 
          || addr > PROCESS_COUNT          || addr == VAR[vi].PROC_INDEX
          ) { 
        lvi = variable_index
          [VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
        if (lvi != vi) { 
          d = red_bop(OR, d, 
            red_inc_off(d, lvi, -1*rvalue, -1*rvalue)
          );
        }
      } 
      else if (addr == VAR[vi].PROC_INDEX) { 
        lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
        if (lvi == vi) 
          d = NORM_FALSE; 
        else {
          d = red_bop(OR, d, 
            red_inc_off(d, lvi, -1*rvalue, -1*rvalue)
          );
        }
      } 
    }
    break;
  case DECREMENT_BY_CONSTANT:
    lvi = st->u.act.lhs->u.atom.var_index; 
    rvalue = get_value(st->u.act.rhs_exp, pi, &flag); 
    if (VAR[lvi].PROC_INDEX == 0) {
      d = red_inc_off(d, lvi, rvalue, rvalue);
    }
/*
    else if (st->u.act.lhs->u.atom.indirect_count > 0) {
      lvi = variable_index
        [VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
      if (lvi != vi) { 
        d = red_bop(OR, d, 
          red_inc_off(d, lvi, rvalue, rvalue)
        );
      }
    }
*/
    else {
      int	addr;

      addr = get_value(st->u.act.lhs->u.atom.exp_base_proc_index, 
        pi, &flag
      ); 
      if (   flag != FLAG_SPECIFIC_VALUE
          || addr <= 0 
          || addr > PROCESS_COUNT          || addr == VAR[vi].PROC_INDEX
          ) { 
        lvi = variable_index
          [VAR[lvi].TYPE][VAR[vi].PROC_INDEX][VAR[lvi].OFFSET]; 
        if (lvi != vi) { 
          d = red_bop(OR, d, 
            red_inc_off(d, lvi, rvalue, rvalue)
          );
        }
      } 
      else if (addr == VAR[vi].PROC_INDEX) { 
        lvi = variable_index[VAR[lvi].TYPE][addr][VAR[lvi].OFFSET]; 
        if (lvi == vi) 
          d = NORM_FALSE; 
        else {
          d = red_bop(OR, d, 
            red_inc_off(d, lvi, rvalue, rvalue)
          );
        }
      } 
    }
    break;
  }
  return(d);  
}
  /* action_inactive_weakest_precondition() */ 
  
  
  
  
struct red_type *rec_inactive_weakest_precondition(d, vi, pi, st)
     struct red_type    *d; 
     int      vi, pi;
     struct statement_type  *st;
{
  struct red_type *red_if, *red_else, *red_loop, *red_while_prev_reachable; 
  int       i; 
/*  
  fprintf(RED_OUT, "In rec_inactive_weakest_precondition(d, vi=%1d, pi=%1d, st=%x)\n",  
    vi, pi, st
    ); 
  fflush(RED_OUT); 
*/  
  if (!st) 
    return(d); 
    
  switch (st->op) { 
  case ST_IF: 
    red_if = rec_inactive_weakest_precondition(d, vi, pi, st->u.branch.if_statement); 
    red_if = red_bop(AND, d, st->u.branch.red_cond[pi]); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      d = rec_inactive_weakest_precondition(d, vi, pi, st->u.branch.else_statement); 
    } 
    d = red_bop(AND, d, st->u.branch.red_uncond[pi]); 
    d = red_bop(OR, red_if, d); 
    return(d); 
    break; 
  case ST_WHILE: 
    /* The precondition consists of (1) the case for the infinite loop and 
     * (2) the case for the finite-loop.  
     * The case for the infinite-loop is a greatest fixpoint.  
     * The case for the finite-loop is a least fixpoint. 
     */
    /* First calculate the finite-loop case. */ 
    red_loop = red_bop(AND, d, st->u.loop.red_uncond[pi]); 
    d = red_loop; 
    red_while_prev_reachable = NORM_FALSE; 
    for (; d != red_while_prev_reachable; ) { 
      red_while_prev_reachable = d; 
      red_loop = rec_inactive_weakest_precondition(red_loop, vi, pi, st->u.loop.statement); 
      red_loop = red_bop(AND, red_loop, st->u.loop.red_cond[pi]); 
      d = red_bop(OR, d, red_loop); 
    } 
    
    return(d);   
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count-1; i>=0 && d != NORM_FALSE; i--) { 
      d = rec_inactive_weakest_precondition(d, vi, pi, st->u.seq.statement[i]); 
    } 
    return(d); 
    break; 
  case ST_CALL: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
            || VAR[vi].OFFSET == var__retmode->index 
        )   ) 
      return(NORM_NO_RESTRICTION); 
    else 
      return(NORM_FALSE); 
    break; 
  case ST_RETURN: 
    if (   VAR[vi].TYPE == TYPE_DISCRETE
        && VAR[vi].PROC_INDEX
        && (   VAR[vi].OFFSET == var_mode->index
            || VAR[vi].OFFSET == var__sp->index
        )   ) 
      return(NORM_NO_RESTRICTION); 
    else 
      return(NORM_FALSE); 
    break; 
  default: 
    return(action_inactive_weakest_precondition(d, vi, pi, st)); 
    break;  
  } 
}
  /* rec_inactive_weakest_precondition() */ 
  
  
  
struct red_type *inactive_weakest_precondition(d, vi, pi, xi)
     struct red_type  *d;
     int    vi, pi, xi;
{
  int     ai, lvi, rvi, value, id, dvi, flag_read, iter, lvalue, b;
  struct red_type *filter, *cut, *effect, *rconj, *lconj;
/*
  fprintf(RED_OUT, "In untimed_weakest_precondition(d, vi=%1d, pi=%1d, xi=%1d\n", vi, pi, xi); 
  fflush(RED_OUT); 
*/  
  if (active_variable_support_untimed_extract_in_statement
        (vi, pi, XTION[xi].statement) == FLAG_ANNIHILATED
      )
    return(NORM_FALSE); 
    
  RT[iter = RT_TOP++] = rec_inactive_weakest_precondition(d, vi, pi, XTION[xi].statement);
  RT[iter] = red_bop(AND, 
    red_active_untimed_extract(XTION[xi].red_trigger[pi]), 
    red_active_untimed_extract(RT[iter])
  );
  if (xi < XTION_COUNT && valid_mode_index(XTION[xi].src_mode_index))
    RT[iter] = red_bop(AND, 
      red_active_untimed_extract(MODE[XTION[xi].src_mode_index].invariance[pi].red), 
      RT[iter]
    );
  d = RT[iter];
  RT_TOP--; // iter 
  d = red_variable_eliminate(d, vi);

  /*
  fprintf(RED_OUT, "\n========================================================================\n");
  fprintf(RED_OUT, "Leaving untimed_weakest_precondition(RT[RETURN], vi=%1d:%s, pi=%1d, xi=%1d\n",
    vi, VAR[vi].NAME, pi, xi
    );
  print_parse_xtion(XTION[xi].parse_xtion, 0);
  fprintf(RED_OUT, "RT[RETURN] is \n");
  red_print_graph(RT[RETURN]);
  fprintf(RED_OUT, "Output is \n");
  red_print_graph(d);
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT);
  */
  return(d); 
}
/* inactive_weakest_precondition() */



struct red_type *peer_inactive_weakest_precondition(
  struct red_type	*d, 
  int    		vi, 
  int			xi
) {
  int   ipj, pj, iter, result;
/*
  fprintf(RED_OUT, "In untimed_weakest_precondition(d, vi=%1d, pi=%1d, xi=%1d\n", vi, pi, xi); 
  fflush(RED_OUT); 
*/  
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (ipj = 0; ipj < XTION[xi].process_count; ipj++) {
    pj = XTION[xi].process[ipj]; 
    if (VAR[vi].PROC_INDEX == pj) 
      continue; 
	
    if (active_variable_support_untimed_extract_in_statement
          (vi, pj, XTION[xi].statement) == FLAG_ANNIHILATED
        )
      continue; 
  
    RT[iter = RT_TOP++] = rec_inactive_weakest_precondition(
      d, vi, pj, XTION[xi].statement
    );
    RT[iter] = red_peer_active_untimed_extract(RT[iter]);
    RT[iter] = red_bop(AND, RT[iter], 
      red_peer_active_untimed_extract(XTION[xi].red_trigger[pj]) 
    ); 
    if (valid_mode_index(XTION[xi].src_mode_index))
      RT[iter] = red_bop(AND, RT[iter], 
        red_peer_active_untimed_extract( 
          MODE[XTION[xi].src_mode_index].invariance[pj].red, vi 
        )
      );
    RT[result] = red_bop(OR, RT[result], RT[iter]);
    RT_TOP--; /* iter */ 
  }
  /*
  fprintf(RED_OUT, "\n========================================================================\n");
  fprintf(RED_OUT, "Leaving untimed_weakest_precondition(RT[RETURN], vi=%1d:%s, pi=%1d, xi=%1d\n",
    vi, VAR[vi].NAME, pi, xi
    );
  print_parse_xtion(XTION[xi].parse_xtion, 0);
  fprintf(RED_OUT, "RT[RETURN] is \n");
  red_print_graph(RT[RETURN]);
  fprintf(RED_OUT, "Output is \n");
  red_print_graph(d);
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT);
  */
  RT_TOP--; // result 
  return(RT[result]); 
}
/* peer_inactive_weakest_precondition() */



int peers_in_reachable(pi, mi)
  int pi, mi; 
{ 
  int ipi; 
  
  for (ipi = 0; ipi < MODE[mi].process_count; ipi++) 
    if (MODE[mi].process[ipi] != pi) 
      return(TYPE_TRUE); 
  return(TYPE_FALSE);   
}
  /* peers_in_reachable() */ 
  
  


void  set_indirect_active(st) 
  struct statement_type *st; 
{ 
  int i, id, dvi, lvi, pi; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case ST_IF: 
    rec_get_all_universal_references(st->parse_statement->u.branch.cond); 
    set_indirect_active(st->u.branch.if_statement);
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      set_indirect_active(st->u.branch.else_statement); 
    break; 
  case ST_WHILE: 
    rec_get_all_universal_references(st->parse_statement->u.loop.cond); 
    set_indirect_active(st->u.loop.statement);
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count-1; i>=0; i--) 
      set_indirect_active(st->u.seq.statement[i]);  
    break; 
 
  case ST_CALL: 
  case ST_RETURN: 
    break; 

  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
  case INCREMENT_BY_CONSTANT:
  case DECREMENT_BY_CONSTANT:
    rec_get_all_universal_references(st->parse_statement->u.act.lhs);
    if (st->u.act.rhs_exp)
      rec_get_all_universal_references(st->parse_statement->u.act.rhs_exp);
    break; 
  } 
}
  /* set_indirect_active() */ 
  
  


struct red_type *red_inactive_one_weakest_precondition_sync_bulk(
  int 			explore, 
  struct red_type	*red_cur_reachable, 
  struct red_type	*red_reachable, 
  int			vi_active
) {
  int     cur_xi, cur_pi, urgent, flag, fxi, ixi, ai, result, conjm;
  struct red_type *conj;
/*
  print_cpu_time("===================================================================\nEntering sync_bulk_xtion()");
  report_red_management();
  */
  RT[explore] = red_bop(AND, RT[explore], RT[XI_SYNC_BULK_WITH_POSTCONDITION]);
/*
  print_cpu_time("after restricting with xi's");
  report_red_management();
*/
  get_all_firable_xtions(explore, MASK_GAME_ROLES);
  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    for (ixi = 0;
            ixi < PROCESS[ITERATE_PI].firable_xtion_count
         && current_firable_xtion[ITERATE_PI][ixi] != -1;
         ixi++
         ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(RT[explore], fxi, ITERATE_XI, ITERATE_XI);

      if (RT[cur_xi] == NORM_FALSE) {
        RT_TOP--;
        continue;
      }

      if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) )
          && (!(XTION[ITERATE_XI].status & FLAG_XTION_QUANTIFIED_SYNC))
          ) 
        RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi);

      if (ITERATE_XI) {
        RT[cur_xi] = rec_inactive_weakest_precondition
          (RT[cur_xi], vi_active, ITERATE_PI, XTION[ITERATE_XI].statement);

        if (RT[cur_xi] == NORM_FALSE) {
          RT_TOP--;
          continue;
        }
        if (XTION[ITERATE_XI].status & FLAG_XTION_QUANTIFIED_SYNC) 
          RT[cur_xi] = red_eliminate_proc_qfd_sync(RT[cur_xi], ITERATE_PI); 
      }
      if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) ) 
          && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
          ) {
        if (valid_mode_index(XTION[ITERATE_XI].src_mode_index)) { 
          conj = red_bop(AND, XTION[ITERATE_XI].red_trigger[ITERATE_PI],
              MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red
          );

          RT[cur_xi] = red_bop(AND, RT[cur_xi], conj);

          if (RT[cur_xi] == NORM_FALSE) {
            RT_TOP--;
            continue;
          }
        }
      }
      RT[cur_pi] = red_bop(OR, RT[cur_xi], RT[cur_pi]);
/*
      RT[cur_pi] = red_subsume(RT[cur_pi]);
*/
      /*
      fprintf(RED_OUT, "\nITERATION %1d, after final union, ITERATE_XI=%1d, ITERATE_PI=%1d\n",
      ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
      red_print_graph(RT[cur_pi]);
      fflush(RED_OUT);
      probe(PROBE_PRERISK1, "WEAKEST INNER: after final union", RT[cur_pi]);
      red_order_check(RT[cur_pi]);
      */

      RT_TOP--; /* cur_xi */
      garbage_collect(FLAG_GC_SILENT);
    }

    RT[explore] = RT[cur_pi];
    RT_TOP--; /* cur_pi */
    RT[explore] = red_subsume(RT[explore]);
  }

  RT[explore] = red_precondition_postprocessing(
    explore, NULL, 
    DECLARED_GLOBAL_INVARIANCE, 
    red_cur_reachable, 
    red_reachable, 
    NULL, FLAG_SYNC_BULK, 
    TYPE_TRUE // flag_postprocessing 
  );
  /*
  print_cpu_time("Leaving sync_bulk_xtion()");
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */

  garbage_collect(FLAG_GC_SILENT);
  return(RT[explore]);
}
/* red_inactive_one_weakest_precondition_sync_bulk() */




struct red_type *red_inactive_one_weakest_precondition_sync_ITERATIVE(
  int			explore, 
  struct red_type	*red_cur_reachable, 
  struct red_type	*red_reachable, 
  int			vi_active
) {
  int     		sxi, new_dest, urgent, flag, ipi, ai, tmp, 
			local_reachable, result;
  struct red_type 	*conj;

  RT[local_reachable = RT_TOP++] = red_cur_reachable; 
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (ITERATE_SXI = 0; ITERATE_SXI < SYNC_XTION_COUNT; ITERATE_SXI++) {
    RT[sxi = RT_TOP++] = red_bop(AND, RT[explore], SYNC_XTION[ITERATE_SXI].red_post);
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("before backward inferencing", FLAG_PRINT_XTION, RT[sxi]);
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--;
      continue;
    }

    for (ipi = 0; RT[sxi] != NORM_FALSE && ipi < SYNC_XTION[ITERATE_SXI].party_count; ipi++) {
      ITERATE_XI = SYNC_XTION[ITERATE_SXI].party[ipi].xtion;
      ITERATE_PI = SYNC_XTION[ITERATE_SXI].party[ipi].proc;

      RT[sxi] = rec_inactive_weakest_precondition
                (RT[sxi], vi_active, ITERATE_PI, SYNC_XTION[ITERATE_SXI].party[ipi].statement); 
    }
    RT[sxi] = red_bop(AND, RT[sxi], SYNC_XTION[ITERATE_SXI].red_trigger); 
    for (ipi = 0; RT[sxi] != NORM_FALSE && ipi < SYNC_XTION[ITERATE_SXI].party_count; ipi++) {
      ITERATE_XI = SYNC_XTION[ITERATE_SXI].party[ipi].xtion;
      ITERATE_PI = SYNC_XTION[ITERATE_SXI].party[ipi].proc;
      if (valid_mode_index(XTION[ITERATE_XI].src_mode_index))
        RT[sxi] = red_bop(AND, RT[sxi], MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red);
    }
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--; // sxi 
      continue;
    }
    RT[sxi] = red_precondition_postprocessing(
      explore, NULL, 
      DECLARED_GLOBAL_INVARIANCE, 
      RT[local_reachable], 
      red_reachable, 
      &(SYNC_XTION[ITERATE_SXI]), 
      XI_SYNC_BULK_WITH_TRIGGERS, 
      TYPE_TRUE // flag_postprocessing 
    ); 

    RT[result] = red_bop(OR, RT[result], RT[sxi]);
    RT[local_reachable] = red_bop(OR, RT[local_reachable], RT[sxi]);
    RT_TOP--; /* sxi */ 
    garbage_collect(FLAG_GC_SILENT);

    RT[result] = red_subsume(RT[result]);
  }
  RT_TOP = RT_TOP-2; // local_reachable, result 
  return (RT[result]); 
}
/* red_inactive_one_weakest_precondition_sync_ITERATIVE() */






int xxx_count = 0; 

init_inactive_management()
{
  int   		vi, pi, pj, imi, mi, ixi, xi, flag_assign, result, 
			ai, lvi, rvi, dvi, id, iter, active, i;
  struct red_type 	*conj;

  if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_REDLIB_SESSION
      && (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) 
         == FLAG_NO_REDUCTION_INACTIVE
      ) { 
    for (vi = 2; vi < VARIABLE_COUNT; vi++) {
      VAR[vi].RED_ACTIVE = NORM_NO_RESTRICTION;
      VAR[vi].RED_INACTIVE = NORM_FALSE;
    }
    return; 
  }
  
  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    VAR[vi].RED_ACTIVE = NORM_FALSE; 
/*
    fprintf(RED_OUT, "In init_inactive_management(), VAR[vi=%1d].NAME=%s\n", vi, VAR[vi].NAME); 
    fflush(RED_OUT); 
*/
    if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) { 
      VAR[vi].U.DISC.WORKING_QFD_SYNC_VALUE = FLAG_ANY_PROCESS; 
    } 
  }
  
  /* get the universal references of all indirections */
  for (xi = 0; xi < XTION_COUNT; xi++) { 
    set_indirect_active(XTION[xi].statement); 
  }
  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    VAR[vi].RED_ACTIVE = NORM_NO_RESTRICTION;
    VAR[vi].RED_TIMED_ACTIVE = NORM_NO_RESTRICTION;
    VAR[vi].RED_INACTIVE = NORM_FALSE;
    VAR[vi].RED_TIMED_INACTIVE = NORM_FALSE;
  }

  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX; 
    if (   (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)
        || !(pi)
        || (   VAR[vi].TYPE != TYPE_CLOCK
            && VAR[vi].TYPE != TYPE_DENSE
            && VAR[vi].TYPE != TYPE_POINTER
            && (VAR[vi].TYPE != TYPE_DISCRETE || VAR[vi].OFFSET == OFFSET_MODE)
            )
        ) {
      continue;
    }
    else if (variable_index[VAR[vi].TYPE][VAR[vi].PROC_INDEX][VAR[vi].OFFSET] < 0) { 
      /* This variable is not used in its module */ 
      VAR[vi].RED_ACTIVE = NORM_FALSE;
      VAR[vi].RED_INACTIVE = NORM_NO_RESTRICTION;
      continue;      
    } 
    else if (VAR[vi].STATUS & FLAG_VAR_PRIMED) {
      VAR[vi].RED_ACTIVE = VAR[VAR[vi].PRIMED_VI].RED_ACTIVE;
      VAR[vi].RED_INACTIVE = VAR[VAR[vi].PRIMED_VI].RED_INACTIVE;
      continue;
    }
    else switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      if (   VAR[vi].OFFSET == OFFSET_MODE 
          || (VAR[vi].STATUS & FLAG_SYNC_PLACE)
          ) {
        continue; 
      }
      break; 
    case TYPE_POINTER: 
      if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) {
        VAR[vi].U.DISC.WORKING_QFD_SYNC_VALUE = FLAG_ANY_PROCESS; 
        continue; 
      }
      break; 
    } 
    #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
      	fprintf(RED_OUT, "***(inactive analysis for %1d:%s)*******************\n",
          vi, VAR[vi].NAME
        );
//      }
    #endif 

    RT[iter = RT_TOP++] 
    = red_xtion_active_variable_support_untimed_extract(vi); 
/*
    fprintf(RED_OUT, "\ninitial RT[iter]:\n"); 
    red_print_graph(RT[iter]); 
*/
    RT[iter] = red_bop(OR, RT[iter], 
      red_peer_xtion_active_variable_support_untimed_extract(vi)
    ); 
/*
    fprintf(RED_OUT, "\ninitial peering RT[iter]:\n"); 
    red_print_graph(RT[iter]); 
*/
    if (RT[iter] == NORM_FALSE) {
      VAR[vi].RED_ACTIVE = NORM_FALSE;
      VAR[vi].RED_INACTIVE = NORM_NO_RESTRICTION;

      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "\n00000000000000000000000000000000000000\n");
        fprintf(RED_OUT, "Trivial VAR[vi=%1d;%s].RED_ACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_ACTIVE);
        fprintf(RED_OUT, "Trivial VAR[vi=%1d;%s].RED_INACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_INACTIVE);
//      }
      #endif 

      RT_TOP--; /* iter */ 
      continue;
    } 
    else if (RT[iter] == NORM_NO_RESTRICTION) { 
      VAR[vi].RED_ACTIVE = NORM_NO_RESTRICTION;
      VAR[vi].RED_INACTIVE = NORM_FALSE;

      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "\n11111111111111111111111111111111111111\n");
        fprintf(RED_OUT, "Trivial VAR[vi=%1d;%s].RED_ACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_ACTIVE);
        fprintf(RED_OUT, "Trivial VAR[vi=%1d;%s].RED_INACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_INACTIVE);
//      }
      #endif 

      RT_TOP--; /* iter */ 
      continue;
    } 

    for (i = 0, RT[active = RT_TOP++] = NORM_FALSE; 
         RT[iter] != NORM_FALSE; 
         i++
         ) {

      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "\nA new iteration for weakest precondition %1d:\n", i);
        fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
//        print_cpu_time("entering the loop"); 
//      }
      #endif 
      RT[active] = red_bop(OR, RT[active], RT[iter]);
      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "\n==[INACTIVE 6.%1d. vi=%1d:%s, pi=%1d]===============================\nRT[active]:\n", 
          i, vi, VAR[vi].NAME, pi
        ); 
        red_print_graph(RT[active]);
//      }
      #endif 

      RT[result = RT_TOP++] = NORM_FALSE;
      if (   (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_HUGE_SYNC) 
          || !(   (GSTATUS[INDEX_POINTER_ARITH] & FLAG_POINTER_ARITH) 
               && (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC) 
               ) 
          ) {
        for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
          xi = PROCESS[pi].firable_xtion[ixi];
          #if RED_DEBUG_INACTIVE_MODE
//          if (vi == 989) { 
            fprintf(RED_OUT, 
              "\n==[xxx_count %1d, INACTIVE 6.%1d. vi=%1d:%s, pi=%1d, executing xi=%1d]=========\n", 
              xxx_count, i, vi, VAR[vi].NAME, pi, xi
            ); 
            fprintf(RED_OUT, "RT[iter=%1d]=%x:\n", iter, RT[iter]); 
            red_print_graph(RT[iter]);
//          }
          #endif 
	  conj = inactive_weakest_precondition(RT[iter], vi, pi, xi);
          if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC) 
            conj = red_eliminate_proc_qfd_sync(conj, pi); 
          #if RED_DEBUG_INACTIVE_MODE
//          if (xxx_count == 26) { 
//          if (vi == 989) { 
            fprintf(RED_OUT, 
                "\ninactive conj in precond p%1d, x%1d, v%1d:%s:\n", 
              pi, xi, vi, VAR[vi].NAME 
            ); 
            red_print_graph(conj); 
            fflush(RED_OUT); 
//          }
          #endif 
            
          RT[result] = red_bop(OR, conj, RT[result]); 
	}
	for (xi = 0; xi < XTION_COUNT; xi++) { 
	  conj = peer_inactive_weakest_precondition(RT[iter], vi, xi); 

          #if RED_DEBUG_INACTIVE_MODE
//          if (xxx_count == 26) { 
//          if (vi == 989) { 
            fprintf(RED_OUT, 
              "\ninactive peer conj in precond p%1d, x%1d, v%1d:%s:\n", 
              pi, xi, vi, VAR[vi].NAME 
            ); 
            red_print_graph(conj); 
            fflush(RED_OUT); 
//          }
          #endif 
            
	  RT[result] = red_bop(OR, conj, RT[result]); 
        }
      }	          
      else { 
        RT[result] = red_inactive_one_weakest_precondition_sync_ITERATIVE(
          iter, NORM_FALSE, RT[active], vi
        ); 

        #if RED_DEBUG_INACTIVE_MODE
//        if (vi == 989) { 
          fprintf(RED_OUT, "====================\n%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
          red_print_graph(RT[result]); 
//          print_cpu_time("after inactive sync iterative"); 
//        }
        #endif 

        if (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS))
          RT[result] = red_bop(OR, RT[result], 
            red_inactive_one_weakest_precondition_sync_bulk(
              iter, RT[result], RT[active], vi
            )
          ); 

        #if RED_DEBUG_INACTIVE_MODE
//        if (vi == 989) { 
          fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
          red_print_graph(RT[result]); 
//          print_cpu_time("after inactive sync bulk"); 
//        }
        #endif 
        RT[result] = red_active_untimed_extract(RT[result]); 
        RT[result] = red_variable_eliminate(RT[result], vi);
      }
      RT[iter] = RT[result];
      RT_TOP--; /*result */

      #if RED_DEBUG_INACTIVE_MODE
//      if (xxx_count == 26) { 
//      if (vi == 989) { 
        fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
        red_print_graph(RT[iter]); 
//        print_cpu_time("after active global local untimed extract"); 
//      }
      #endif 
        
      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
        red_print_graph(RT[iter]); 
//        print_cpu_time("after pointer and discrete elimination"); 
//      }
      #endif 

      RT[iter] = red_bop(SUBTRACT, RT[iter], RT[active]);

      #if RED_DEBUG_INACTIVE_MODE
//      if (vi == 989) { 
        fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
        red_print_graph(RT[iter]); 
//        print_cpu_time("after iteration active subtraction"); 
//      }
      #endif 

      garbage_collect(FLAG_GC_SILENT);

      #if RED_DEBUG_INACTIVE_MODE
//      if (xxx_count == 26) { 
//      if (vi == 989) { 
        fprintf(RED_OUT, "%1d:%1d:%s\n", i, vi, VAR[vi].NAME); 
        red_print_graph(RT[iter]); 
//        print_cpu_time("after garbage collection"); 
//      }
      #endif 
    }

    VAR[vi].RED_ACTIVE = RT[active];
    RT_TOP--; /* active */ 
    RT_TOP--; /* iter */ 

    red_mark(VAR[vi].RED_ACTIVE, FLAG_GC_STABLE);
    switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
    case FLAG_SYSTEM_HYBRID:
      VAR[vi].RED_INACTIVE = red_complement(VAR[vi].RED_ACTIVE);
      break;
    case FLAG_SYSTEM_TIMED:
    case FLAG_SYSTEM_UNTIMED:
      VAR[vi].RED_INACTIVE = red_complement(VAR[vi].RED_ACTIVE);
      break;
    }

    if (pi)
      VAR[vi].RED_INACTIVE = red_time_eliminate(
        red_bop(AND, VAR[vi].RED_INACTIVE,
        RED_INVARIANCE[pi]
      ) );
    red_mark(VAR[vi].RED_INACTIVE, FLAG_GC_STABLE);
    garbage_collect(FLAG_GC_SILENT);

//    #if RED_DEBUG_INACTIVE_MODE
      fprintf(RED_OUT, "\n*************************************\n");
      fprintf(RED_OUT, "VAR[vi=%1d;%s].RED_ACTIVE:\n", vi, VAR[vi].NAME);
      red_print_graph(VAR[vi].RED_ACTIVE);
      fprintf(RED_OUT, "VAR[vi=%1d;%s].RED_INACTIVE:\n", vi, VAR[vi].NAME);
      red_print_graph(VAR[vi].RED_INACTIVE);
//    #endif 
  }
}
/* init_inactive_management() */



struct red_type *inactive_check1(d)
  struct red_type *d; 
{
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][OFFSET_MODE], 1, 1); 
/*
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][OFFSET_MODE], 4, 4); 
*/
  if (count_ec_elm == STOP_COUNT_EC_ELM) 
    red_print_graph(d); 
  return (d);   
}
  /* inactive_check() */  
  
  
  
struct red_type *inactive_variable_eliminate(IN)
     int  IN;
{
  int     		w, vi, pi, ci, zi, zj, wk;
  struct red_type 	*conj;

  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX;
    if (   (VAR[vi].STATUS & FLAG_VAR_PRIMED)
        || (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)
        || pi == 0
        || !(   VAR[vi].TYPE == TYPE_CLOCK
             || VAR[vi].TYPE == TYPE_DENSE
             || VAR[vi].TYPE == TYPE_POINTER
             || VAR[vi].TYPE == TYPE_DISCRETE
             || VAR[vi].TYPE == TYPE_FLOAT
             || VAR[vi].TYPE == TYPE_DOUBLE
             )
        ) { 
      continue; 
    } 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      if (   VAR[vi].OFFSET == OFFSET_MODE 
          || (VAR[vi].STATUS & FLAG_SYNC_PLACE)
          )
        continue; 
      break; 
    case TYPE_POINTER: 
      if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) 
        continue; 
      break; 
    } 
/*
    fprintf(RED_OUT, "inactive ec elm %1d for vi%1d:%s:\n", count_ec_elm, vi, VAR[vi].NAME); 
    if (count_ec_elm == STOP_COUNT_EC_ELM) { 
      RT[wk = RT_TOP++] = inactive_check1(RT[IN]); 
    }
*/
    RT[w = RT_TOP++] = red_var_presence(RT[IN], vi); 
    RT[w] = red_bop(SUBTRACT, RT[w], VAR[vi].RED_ACTIVE);
    if (RT[w] == NORM_FALSE) {
      RT_TOP--; // w
      continue; 
    } 
  /*
  print_cpu_time("In inactive_variable_eliminate()"); 
  fprintf(RED_OUT, "VAR[%1d]:%s\n", vi, VAR[vi].NAME); 
  fprintf(RED_OUT, "\nDetect an inactive RED fragment for %1d:%s\n", vi, VAR[vi].NAME);
  red_print_graph(RT[w]);
  */

    conj = red_var_absence(RT[IN], vi); 
    RT[IN] = red_bop(OR, conj, 
      red_bop(EXTRACT, RT[IN], VAR[vi].RED_ACTIVE)
    );
    switch (VAR[vi].TYPE) {
    case TYPE_CLOCK:
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
        RT[w] = hybrid_bypass_DOWNWARD(w, vi);
        RT[w] = red_variable_eliminate(RT[w], vi);
      }
      else
        RT[w] = red_time_clock_eliminate(RT[w], VAR[vi].U.CLOCK.CLOCK_INDEX);
    /*
    print_cpu_time("after clock inactive elimination"); 
    probe(PROBE_PRERISK, "after an inactive elimination", RT[w]);
    */
      break;
    case TYPE_DENSE:
      RT[w] = hybrid_bypass_DOWNWARD(w, vi);
      RT[w] = red_variable_eliminate(RT[w], vi);
/*
    print_cpu_time("after dense inactive elimination"); 
*/
      break;
    default:
      RT[w] = red_variable_eliminate(RT[w], vi);
      if (VAR[vi].TYPE == TYPE_POINTER && !(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS))
        RT[w] = red_bop(AND, RT[w], ddd_atom(vi, 0, 0));
/*
    print_cpu_time("after default inactive elimination"); 
*/
    }

  /*
  fprintf(RED_OUT, "\nAfter processing the inactive variable %1d:%s\n", vi, VAR[vi].NAME);
  red_print_graph(RT[w]);
  */

    RT[IN] = red_bop(OR, RT[IN], RT[w]);
    RT_TOP--; /* w */ 
    garbage_collect(FLAG_GC_SILENT);
/*
  print_cpu_time("after garbage collection"); 
*/
/*
      if (count_ec_elm == STOP_COUNT_EC_ELM) { 
        conj = inactive_check1(RT[IN]); 
        if (RT[wk] != conj) { 
          fprintf(RED_OUT, "inactive ec elm %1d for vi%1d:%s, difference detected:\n", count_ec_elm, vi, VAR[vi].NAME); 
          fprintf(RED_OUT, "RT[w] check before:\n"); 
          red_print_graph(RT[wk]); 
          fprintf(RED_OUT, "RT[w] check after:\n"); 
          red_print_graph(conj); 
        } 
        RT_TOP--; // wk 
      }
*/
  }

  return(RT[IN]);
}
/* inactive_variable_eliminate() */




struct red_type *process_inactive_variable_eliminate(IN, pi)
     int  IN, pi;
{
  int			w, vi, ci, zi, zj;
  struct red_type 	*conj;

  for (vi = variable_index[TYPE_DISCRETE][pi][0]; 
       vi < VARIABLE_COUNT && VAR[vi].PROC_INDEX == pi; 
       vi++
       ) {
    if (   (VAR[vi].STATUS & FLAG_VAR_PRIMED)
        || (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)
        || !(   VAR[vi].TYPE == TYPE_CLOCK 
             || VAR[vi].TYPE == TYPE_DENSE 
             || VAR[vi].TYPE == TYPE_POINTER 
             || VAR[vi].TYPE == TYPE_DISCRETE 
             || VAR[vi].TYPE == TYPE_FLOAT
             || VAR[vi].TYPE == TYPE_DOUBLE
             )
        ) {
      continue;   	
    }
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      if (   VAR[vi].OFFSET == OFFSET_MODE 
          || (VAR[vi].STATUS & FLAG_SYNC_PLACE)
          )
      break; 
    case TYPE_POINTER: 
      if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) 
        continue; 
      break; 
    } 

    RT[w = RT_TOP++] = red_var_presence(RT[IN], vi); 
    RT[w] = red_bop(SUBTRACT, RT[w], VAR[vi].RED_ACTIVE);
    if (RT[w] == NORM_FALSE) {
      RT_TOP--; // w 
      continue; 
    }

    /*
      fprintf(RED_OUT, "\nDetect an inactive RED fragment for %1d:%s\n", vi, VAR[vi].NAME);
      red_print_graph(RT[w]);
     */

    conj = red_var_absence(RT[IN], vi); 
    RT[IN] = red_bop(OR, conj, 
      red_bop(EXTRACT, RT[IN], VAR[vi].RED_ACTIVE)
    );
    switch (VAR[vi].TYPE) {
    case TYPE_CLOCK:
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
        RT[w] = hybrid_bypass_DOWNWARD(w, vi);
        RT[w] = red_variable_eliminate(RT[w], vi);
      }
      else
        RT[w] = red_time_clock_eliminate(RT[w], VAR[vi].U.CLOCK.CLOCK_INDEX);
      /*
        probe(PROBE_PRERISK, "after an inactive elimination", RT[w]);
        */
      break;
    case TYPE_DENSE:
      RT[w] = hybrid_bypass_DOWNWARD(w, vi);
      RT[w] = red_variable_eliminate(RT[w], vi);
      break;
    default:
      RT[w] = red_variable_eliminate(RT[w], vi);
      if (VAR[vi].TYPE == TYPE_POINTER && !(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS))
        RT[w] = red_bop(AND, RT[w], ddd_atom(vi, 0, 0));
    }

    /*
    fprintf(RED_OUT, "\nAfter processing the inactive variable %1d:%s\n", vi, VAR[vi].NAME);
    red_print_graph(RT[w]);
    */

    RT[IN] = red_bop(OR, RT[IN], RT[w]);
    RT_TOP--;
    garbage_collect(FLAG_GC_SILENT);
  }

  return(RT[IN]);
}
/* process_inactive_variable_eliminate() */





struct red_type *inactive_variable_eliminate_noxtive(IN)
     int  IN;
{
  int     w, vi, pi, ci, zi, zj;
  struct red_type *conj;

  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX;
    if (   pi == 0 
        || (VAR[vi].STATUS & FLAG_VAR_PRIMED)
        || (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)
        || !(   VAR[vi].TYPE == TYPE_CLOCK
             || VAR[vi].TYPE == TYPE_DENSE
             || VAR[vi].TYPE == TYPE_POINTER
             || VAR[vi].TYPE == TYPE_DISCRETE
             || VAR[vi].TYPE == TYPE_FLOAT
             || VAR[vi].TYPE == TYPE_DOUBLE
             )
        ) {
      continue; 
    } 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      if (   VAR[vi].OFFSET == OFFSET_MODE 
          || (VAR[vi].STATUS & FLAG_SYNC_PLACE)
          )
        continue; 
      break; 
    case TYPE_POINTER: 
      if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) 
        continue; 
      break; 
    } 

    RT[w = RT_TOP++] = red_bop(SUBTRACT, RT[IN], VAR[vi].RED_ACTIVE);
    if (RT[w] == NORM_FALSE) {
      RT_TOP--; // w 
      continue; 
    }   
    /*
      print_cpu_time("In inactive_variable_eliminate()"); 
      fprintf(RED_OUT, "VAR[%1d]:%s\n", vi, VAR[vi].NAME); 
      fprintf(RED_OUT, "\nDetect an inactive RED fragment for %1d:%s\n", vi, VAR[vi].NAME);
      red_print_graph(RT[w]);
     */
    RT[IN] = red_bop(EXTRACT, RT[IN], VAR[vi].RED_ACTIVE);
    switch (VAR[vi].TYPE) {
    case TYPE_CLOCK:
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
        RT[w] = red_variable_eliminate(RT[w], vi);
      }
      else
        RT[w] = red_time_clock_eliminate(RT[w], VAR[vi].U.CLOCK.CLOCK_INDEX);
      /*
        print_cpu_time("after clock inactive elimination"); 
        probe(PROBE_PRERISK, "after an inactive elimination", RT[w]);
       */
      break;
    case TYPE_DENSE:
      RT[w] = red_variable_eliminate(RT[w], vi);
      /*
        print_cpu_time("after dense inactive elimination"); 
       */
      break;
    default:
      /*
      fprintf(RED_OUT, "\nbefore an inactive elimination\n");
      print_variable(vi);
      red_print_graph(RT[w]);
      */
      RT[w] = red_variable_eliminate(RT[w], vi);
      if (VAR[vi].TYPE == TYPE_POINTER && !(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS))
        RT[w] = red_bop(AND, RT[w], ddd_atom(vi, 0, 0));
      /*
        print_cpu_time("after default inactive elimination"); 
        probe(PROBE_PRERISK1, "after an inactive elimination", RT[w]);
       */
    }
    /*
      fprintf(RED_OUT, "\nAfter processing the inactive variable %1d:%s\n", vi, VAR[vi].NAME);
      red_print_graph(RT[w]);
      */

    RT[IN] = red_bop(OR, RT[IN], RT[w]);
    RT_TOP--; // w
    garbage_collect(FLAG_GC_SILENT);
    /*
      print_cpu_time("after garbage collection"); 
     */
  }

  return(RT[IN]);
}
/* inactive_variable_eliminate_noxtive() */




struct red_type *process_inactive_variable_eliminate_noxtive(IN, pi)
     int  IN, pi;
{
  int     		w, vi, ci, zi, zj;
  struct red_type 	*conj;

  for (vi = variable_index[TYPE_DISCRETE][pi][0]; 
       vi < VARIABLE_COUNT && VAR[vi].PROC_INDEX == pi; 
       vi++
       ) {
    if (   (VAR[vi].STATUS & FLAG_SPEC_REFERENCED)
        || (VAR[vi].STATUS & FLAG_VAR_PRIMED)
        || !(   VAR[vi].TYPE == TYPE_CLOCK
             || VAR[vi].TYPE == TYPE_DENSE
             || VAR[vi].TYPE == TYPE_POINTER
             || VAR[vi].TYPE == TYPE_DISCRETE
             || VAR[vi].TYPE == TYPE_FLOAT
             || VAR[vi].TYPE == TYPE_DOUBLE
             )
        ) {
      continue; 
    } 
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
      if (   VAR[vi].OFFSET == OFFSET_MODE 
          || (VAR[vi].STATUS & FLAG_SYNC_PLACE)
          )
        continue;
      break; 
    case TYPE_POINTER: 
      if (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC) 
        continue; 
      break; 
    } 

    RT[w = RT_TOP++] = red_bop(SUBTRACT, RT[IN], VAR[vi].RED_ACTIVE);
    if (RT[w] == NORM_FALSE) {
      RT_TOP--; // w
      continue; 
    } 
    /*
      fprintf(RED_OUT, "\nDetect an inactive RED fragment for %1d:%s\n", vi, VAR[vi].NAME);
      red_print_graph(RT[w]);
     */

    RT[IN] = red_bop(EXTRACT, RT[IN], VAR[vi].RED_ACTIVE);
    switch (VAR[vi].TYPE) {
    case TYPE_CLOCK:
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
        RT[w] = red_variable_eliminate(RT[w], vi);
      }
      else
        RT[w] = red_time_clock_eliminate(RT[w], VAR[vi].U.CLOCK.CLOCK_INDEX);
        /*
          probe(PROBE_PRERISK, "after an inactive elimination", RT[w]);
         */
      break;
    case TYPE_DENSE:
      RT[w] = red_variable_eliminate(RT[w], vi);
      break;
    default:
      RT[w] = red_variable_eliminate(RT[w], vi);
      if (VAR[vi].TYPE == TYPE_POINTER && !(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS))
        RT[w] = red_bop(AND, RT[w], ddd_atom(vi, 0, 0));
    }
    /*
    fprintf(RED_OUT, "\nAfter processing the inactive variable %1d:%s\n", vi, VAR[vi].NAME);
    red_print_graph(RT[w]);
    */

    RT[IN] = red_bop(OR, RT[IN], RT[w]);
    RT_TOP--; // w
    garbage_collect(FLAG_GC_SILENT);
  }

  return(RT[IN]);
}
/* process_inactive_variable_eliminate_noxtive() */




/********************************************************************
* The following procedure is very special in its design of cache query. 
* The thing is that the query only cares about the current mode of the 
* current process in the path. 
* This is because that we assume that the local variables are right  
* directly after the current local process mode varialbe in the variable 
* ordering. 
*/




int 	TIA_VI, TIA_MVI, TIA_MI, TIA_PI, TIA_VI_BOUND;


void  rec_timed_invariance_bounds(d, mi)
     struct red_type  *d;
     int    mi;
{
  int     		ci, c1, c2, vi;
  struct rec_type 	*rec, *nrec;

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
      d, d->var_index
      );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return;

  /* Note that we are only interested at the bound of each mode.
   * Thus the second parameter in the cache is the mode index. 
   */
  rec = rec_new(d, (struct red_type *) mi);
  nrec = (struct rec_type *) add_23tree(rec, peer_tree, rec_comp, rec_free,
          rec_nop, rec_parent_set, rec_print
          );
  if (rec != nrec)
    return;
  else
    nrec->result = NORM_NO_RESTRICTION;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (mi >= 0) {
      c1 = VAR[d->var_index].U.CRD.CLOCK1;
      c2 = VAR[d->var_index].U.CRD.CLOCK2;
      if (c1) {
        if (c2) {
          fprintf(RED_OUT, "\nError: in RT[REFINED_GLOBAL_INVARIANCE], there should not be any difference.\n");
          fflush(RED_OUT);
          exit(0);
        }
        else {
          vi = CLOCK[c1];
          ci = d->u.crd.child_count-1;
          if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY)
            ci--;
          if (   (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
                  && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
                  )
              || (d->u.crd.arc[ci].upper_bound
                  * VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator
                  < VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator
                  )
              ) {
            VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator = d->u.crd.arc[ci].upper_bound;
            VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator = 1;
          }
        }
      }
      else {
        if (c2) {
          vi = CLOCK[c2];
          if (   (   VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator == HYBRID_NEG_INFINITY
                  && VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator == 1
                  )
              || (d->u.crd.arc[0].upper_bound
                  * VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
                  > VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator
                  )
              ) {
            VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator = -1*d->u.crd.arc[0].upper_bound;
            VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator = 1;
          }
        }
      }
    }
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      rec_timed_invariance_bounds(d->u.crd.arc[ci].child, mi);
    }
    break;
  case TYPE_HRD:
    if (mi >= 0) {
      if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1) {
        vi = d->u.hrd.hrd_exp->hrd_term[0].var_index;
        if (   VAR[vi].PROC_INDEX && (VAR[vi].TYPE == TYPE_CLOCK 
            || VAR[vi].TYPE == TYPE_DENSE
            )) {
          if (d->u.hrd.hrd_exp->hrd_term[0].coeff > 0) {
            if (   (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
                    && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
                    )
                || (d->u.hrd.arc[0].ub_numerator
                    * VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator
                    < VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator
                      * d->u.hrd.arc[0].ub_denominator
                    )
                ) {
              VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator 
              = d->u.hrd.arc[0].ub_numerator;
              VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator 
              = d->u.hrd.arc[0].ub_denominator;
            }
          }
          else {
            ci = d->u.hrd.child_count-1;
            if (d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
                && d->u.hrd.arc[ci].ub_denominator == 1
                )
              ci--;
/*
            fprintf(RED_OUT, 
              "\n**[3294]************\nVAR[vi=%1d].MODE_TIMED_INACTIVE=%x\n", 
              vi, VAR[vi].MODE_TIMED_INACTIVE  
            ); 
            fprintf(RED_OUT, 
              "\nVAR[vi=%1d].MODE_TIMED_INACTIVE[mi=%1d]=%x\n", 
              vi, mi, &(VAR[vi].MODE_TIMED_INACTIVE[mi]) 
            ); 
            fprintf(RED_OUT, 
              "\nVAR[vi=%1d].MODE_TIMED_INACTIVE[mi=%1d].lb_nuerator=%1d\n", 
              vi, mi, VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator 
            ); 
            fprintf(RED_OUT, 
              "\nVAR[vi=%1d].MODE_TIMED_INACTIVE[mi=%1d].lb_denominator=%1d\n", 
              vi, mi, VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator 
            ); 
*/
            if (   (   VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator == HYBRID_NEG_INFINITY
                    && VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator == 1
                    )
                || (d->u.hrd.arc[ci].ub_numerator
                    * VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
                    > VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator
                      * d->u.hrd.arc[ci].ub_denominator
                    )
                ) {
              VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator = -1*d->u.hrd.arc[ci].ub_numerator;
              VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator = d->u.hrd.arc[ci].ub_denominator;
            }
          }
        }
      }
    }
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_timed_invariance_bounds(d->u.hrd.arc[ci].child, mi);
    }
    break;
  case TYPE_FLOAT:
    if (   VAR[d->var_index].PROC_INDEX 
        && VAR[d->var_index].OFFSET == 0
        ) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++)
        for (mi = d->u.fdd.arc[ci].lower_bound;
             mi <= d->u.fdd.arc[ci].upper_bound;
             mi++
             ) {
          rec_timed_invariance_bounds(d->u.fdd.arc[ci].child, mi);
        }
    }
    else 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        rec_timed_invariance_bounds(d->u.fdd.arc[ci].child, mi);
      }
    break;
  case TYPE_DOUBLE:
    if (   VAR[d->var_index].PROC_INDEX 
        && VAR[d->var_index].OFFSET == 0
        ) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++)
        for (mi = d->u.dfdd.arc[ci].lower_bound;
             mi <= d->u.dfdd.arc[ci].upper_bound;
             mi++
             ) {
          rec_timed_invariance_bounds(d->u.dfdd.arc[ci].child, mi);
        }
    }
    else 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        rec_timed_invariance_bounds(d->u.dfdd.arc[ci].child, mi);
      }
    break;
  default:
    if (   VAR[d->var_index].PROC_INDEX 
        && VAR[d->var_index].OFFSET == 0
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++)
        for (mi = d->u.ddd.arc[ci].lower_bound;
             mi <= d->u.ddd.arc[ci].upper_bound;
             mi++
             ) {
          rec_timed_invariance_bounds(d->u.ddd.arc[ci].child, mi);
        }
    }
    else 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        rec_timed_invariance_bounds(d->u.ddd.arc[ci].child, mi);
      }
  } 
}
/* rec_timed_invariance_bounds() */




/* We have not taken care of inequalities like x = y */
void  record_timed_invariance_bounds(d)
     struct red_type  *d;
{
  int imi, mi, pi, vi;

  for (vi = 7; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX;
    if (pi && (VAR[vi].TYPE == TYPE_CLOCK || VAR[vi].TYPE == TYPE_DENSE)) {
      VAR[vi].MODE_TIMED_INACTIVE = ((struct mode_timed_inactive_type *)
        malloc(  (PROCESS[pi].reachable_upper_mode - PROCESS[pi].reachable_lower_mode + 1)
               * sizeof(struct mode_timed_inactive_type)
               )
      ) - PROCESS[pi].reachable_lower_mode;
/*
      fprintf(RED_OUT, 
        "\n**[3338]************\nVAR[vi=%1d:%s].MODE_TIMED_INACTIVE=%x\n", 
        vi, VAR[vi].NAME, VAR[vi].MODE_TIMED_INACTIVE  
      ); 
      fprintf(RED_OUT, 
        "\nPROCESS[pi=%1d].reachable_lower_mode=%1d\n", 
        pi, PROCESS[pi].reachable_lower_mode 
      ); 
*/
      for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
        mi = PROCESS[pi].reachable_mode[imi];
        VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator = HYBRID_NEG_INFINITY;
        VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator = 1;
        VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator = HYBRID_POS_INFINITY;
        VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator = 1;
        VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive = NORM_NO_RESTRICTION;
      }
    }
  }
  init_23tree(&peer_tree);
  rec_timed_invariance_bounds(d, -1);
  free_entire_23tree(peer_tree, rec_free);
/*
  fprintf(RED_OUT, "\n======(timed inactive intervals)====================\n");
  for (vi = 7; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX;
    if (pi && (VAR[vi].TYPE == TYPE_CLOCK || VAR[vi].TYPE == TYPE_DENSE)) {
      fprintf(RED_OUT, "%1d:%s: ", vi, VAR[vi].NAME);
      for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
        mi = PROCESS[pi].reachable_mode[imi];
        fprintf(RED_OUT, "%1d:%s:", mi, MODE[mi].name);
        if (VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator % 2)
          fprintf(RED_OUT, "(");
        else
          fprintf(RED_OUT, "[");
        print_rational(VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator,
          VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
        );
        fprintf(RED_OUT, ",");
        print_rational(VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator,
          VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator
        );
        if (VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator % 2)
          fprintf(RED_OUT, ") ");
        else
          fprintf(RED_OUT, "] ");
      }
      fprintf(RED_OUT, "\n");
    }
  }
*/
}
/* record_timed_invariance_bounds() */





int 	timed_inactive_empty(lbn, lbd, ubn, ubd)
  int lbn, lbd, ubn, ubd;
{
  if (   ubn != HYBRID_POS_INFINITY && ubd != 1
      && lbn != HYBRID_NEG_INFINITY && lbd != 1
      && lbn * ubd > ubn * lbd
      )
    return(TYPE_TRUE);
  else
    return(TYPE_FALSE);
}
  /* timed_inactive_empty() */





/* If all incoming transitions have an assignment in the inactive area, then it is inactive. */ 
int timed_inactive_type_I_incoming_assignment_match(pi, vi, mi)
  int pi, vi, mi;
{
  int ixi, xi, lhs_vi, ai, lbn, lbd, ubn, ubd;

  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
    xi = PROCESS[pi].firable_xtion[ixi];
    if (XTION[xi].dst_mode_index == mi) { 
      if (!vi_range_match_in_statement(vi, pi, mi, XTION[xi].statement)) 
        return(TYPE_FALSE); 
    }
  }
  return(TYPE_TRUE);
}
  /* timed_inactive_type_I_incoming_assignment_match() */





int timed_inactive_type_I_outgoing_assignment_match(pi, vi, mi)
  int pi, vi, mi;
{
  int     ixi, xi, lhs_vi;
  struct red_type *filter;

  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_TIMED:
    if (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
        && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
        )
      filter = NORM_NO_RESTRICTION;
    else
      filter = crd_atom(ZONE[VAR[vi].U.CLOCK.CLOCK_INDEX][0],
        VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator - 1
      );
    if (   VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator != HYBRID_NEG_INFINITY
        || VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator != 1
        )
      filter = red_bop(AND, filter,
        crd_atom(ZONE[0][VAR[vi].U.CLOCK.CLOCK_INDEX],
          1-VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator
        )
      );
    break;
  case FLAG_SYSTEM_HYBRID:
    if (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
        && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
        )
      filter = NORM_NO_RESTRICTION;
    else
      filter = hrd_atom(
         (VAR[vi].TYPE == TYPE_CLOCK) 
         ? VAR[vi].U.CLOCK.HE_UB : VAR[vi].U.DENSE.HE_UB,
         VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator - 1,
         VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator
         );
    if (   VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator != HYBRID_NEG_INFINITY
        || VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator != 1
        )
      filter = red_bop(AND, filter,
        hrd_atom(
          (VAR[vi].TYPE == TYPE_CLOCK) 
          ? VAR[vi].U.CLOCK.HE_LB: VAR[vi].U.DENSE.HE_LB,
          1-VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator,
          VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
        )
      );
    break;
  }

  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
    xi = PROCESS[pi].firable_xtion[ixi];
    if (XTION[xi].src_mode_index == mi) {
      if (red_bop(AND, filter, XTION[xi].red_trigger[pi]) != NORM_FALSE)
        return(TYPE_FALSE);
    }
  }
  return(TYPE_TRUE);
}
  /* timed_inactive_type_I_outgoing_assignment_match() */




/* 1. All incoming arcs are labeled with assignment to clocks that matches with
      the mode invariance condition.
   2. All outgoing arcs happen at endpoints.
*/
int timed_inactive_type_I_check(vi, mi)
  int vi, mi;
{
  int pi, ri, rate_lb_numerator, rate_lb_denominator, rate_ub_numerator, rate_ub_denominator;

  pi = VAR[vi].PROC_INDEX;
  /* check if all incoming assignments match the invariance interval. */
  if (   !timed_inactive_type_I_incoming_assignment_match(pi, vi, mi)
      || !timed_inactive_type_I_outgoing_assignment_match(pi, vi, mi)
      )
    return(TYPE_FALSE);

  if (VAR[vi].TYPE == TYPE_CLOCK) {
    rate_lb_numerator = 1;
    rate_lb_denominator = 1;
    rate_ub_numerator = 1;
    rate_ub_denominator = 1;
  }
  else {
    rate_lb_numerator = HYBRID_NEG_INFINITY;
    rate_lb_denominator = 1;
    rate_ub_numerator = HYBRID_POS_INFINITY;
    rate_ub_denominator = 1;
    for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
      if (MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index == vi) {
  rate_lb_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
  rate_lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
  rate_ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
  rate_ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
      }
    }
  }
  if (   VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator == HYBRID_NEG_INFINITY
      && VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator == 1
      ) {
    if (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
        && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
        ) {
      return(TYPE_FALSE);
    }
    else /* (-oo,c] */ {
      if (rate_ub_numerator <= 0) {
  return(TYPE_FALSE);
      }
      else {
        return(TYPE_TRUE);
      }
    }
  }
  else
    if /* [c,oo) */
       (   VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator == HYBRID_POS_INFINITY
  && VAR[vi].MODE_TIMED_INACTIVE[mi].ub_denominator == 1
  ) {
      if (rate_lb_numerator >= 0) {
  return(TYPE_FALSE);
      }
      else {
        return(TYPE_TRUE);
      }
    }
    else /* [c,c'] */ {
      if (rate_lb_numerator >= 0 || rate_ub_numerator <= 0) {
  return(TYPE_FALSE);
      }
      else
        return(TYPE_TRUE);
    }
}
  /* timed_inactive_type_I_check() */





int 	VI_INACTIVE; 

int rec_variable_active(d)
     struct red_type  *d;
{
  struct ddd_child_type 	*ic; 
  int     			ci, dn, dd;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
      d, d->var_index
      );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(TYPE_FALSE);

  ce = cache2_check_result_key(
    OP_VARIABLE_ACTIVE, d, 
    (struct red_type *) VI_INACTIVE
  ); 
  if (ce->result) {
    if (ce->result == NORM_FALSE)
      return(TYPE_FALSE);
    else
      return(TYPE_TRUE);
  }
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (d->u.hrd.hrd_exp->hrd_term[ci].var_index == VI_INACTIVE) {
        ce->result = NORM_TRUE;
        return(TYPE_TRUE);
      }

    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      if (rec_variable_active(d->u.hrd.arc[ci].child)) {
        ce->result = NORM_TRUE;
        return(TYPE_TRUE);
      }

    break;

  default:
    if (d->var_index == VI_INACTIVE) {
      ce->result = NORM_TRUE;
      return(TYPE_TRUE);
    }
    else for (ci = 0; ci < d->u.ddd.child_count; ci++)
      if (rec_variable_active(d->u.ddd.arc[ci].child)) {
        ce->result = NORM_TRUE;
        return(TYPE_TRUE);
      }
  }
  ce->result = NORM_FALSE;
  return(TYPE_FALSE);
}
/* rec_variable_active() */



int 	variable_active(d, vi)
  struct red_type *d;
  int   vi;
{
  int result;

  VI_INACTIVE = vi;
  result = rec_variable_active(d);

  return(result);
}
  /* variable_active() */



int 	timed_inactive_type_II_check(vi, mi)
  int vi, mi;
{
  int pi, ixi, xi, lhs_vi, ai;

  pi = VAR[vi].PROC_INDEX;
  if (variable_active(MODE[mi].invariance[pi].red, vi))
    return(TYPE_FALSE);

  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
    xi = PROCESS[pi].firable_xtion[ixi];
    if (XTION[xi].src_mode_index == mi) {
      if (variable_active(XTION[xi].red_trigger[pi], vi)) {
  return (TYPE_FALSE);
      } 
      if (!vi_writing_in_statement(vi, pi, XTION[xi].statement)) 
        return(TYPE_FALSE);
    }
  }
  return(TYPE_TRUE);
}
  /* timed_inactive_type_II_check() */




struct hrd_exp_type 	**PAR;
int 			par_top, T3_VI, *PAR_ub_numerator, *PAR_ub_denominator;
struct red_type 	*d_mode;


int rec_check_not_type_III(d, e)
     struct red_type  *d, *e;
{
  int     			ci, c1, c2, vi, len, ti, result; 
  struct red_type		*ne; 
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
      d, d->var_index
      );
*/
  if (d->var_index == TYPE_TRUE)
    return(TYPE_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(TYPE_FALSE);

  ce = cache2_check_result_key(
    OP_CHECK_NOT_TYPE_III, d, (struct red_type *) e
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == VAR[T3_VI].U.CLOCK.CLOCK_INDEX) {
      if (c2 == VAR[T3_VI].U.CLOCK.CLOCK_INDEX) {
        fprintf(RED_OUT, "\nError: in RT[REFINED_GLOBAL_INVARIANCE], there should not be any difference.\n");
        fflush(RED_OUT);
        exit(0);
      }
      else if (c2) {
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));  
      }
    }
    else if (c2 == VAR[T3_VI].U.CLOCK.CLOCK_INDEX) {
      if (c1) 
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
    }
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      if (!rec_check_not_type_III(d->u.crd.arc[ci].child, e))
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
    }
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH; 
    ne = e; 
    if (len > 1) {
      if (   d->u.hrd.hrd_exp->hrd_term[len-1].var_index == T3_VI
          && VAR[d->u.hrd.hrd_exp->hrd_term[len-2].var_index].TYPE == TYPE_DENSE
          && !VAR[d->u.hrd.hrd_exp->hrd_term[len-2].var_index].PROC_INDEX
          ) {
        for (ti = 0; ti < par_top; ti++)
          if (PAR[ti] == d->u.hrd.hrd_exp)
            break;
        if (ti >= par_top) {
          PAR[par_top] = d->u.hrd.hrd_exp;
          ci = d->u.hrd.child_count-1;
          if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
              && d->u.hrd.arc[ci].ub_denominator == 1
              )
            ci--;
          PAR_ub_numerator[par_top] = d->u.hrd.arc[ci].ub_numerator;
          PAR_ub_denominator[par_top++] = d->u.hrd.arc[ci].ub_denominator; 
          ne = hrd_one_constraint(e, d->u.hrd.hrd_exp, 
            d->u.hrd.arc[ci].ub_numerator, 
            d->u.hrd.arc[ci].ub_denominator
          ); 
        }
      }
      else {
        for (ti = len-1; ti >= 0; ti--)
          if (d->u.hrd.hrd_exp->hrd_term[ti].var_index == T3_VI)
            return((int) (ce->result = (struct red_type *) TYPE_FALSE));
      }
    }
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      if (!rec_check_not_type_III(d->u.hrd.arc[ci].child, ne))
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
    }
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      if (!rec_check_not_type_III(d->u.fdd.arc[ci].child, e))
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      if (!rec_check_not_type_III(d->u.dfdd.arc[ci].child, e))
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      if (!rec_check_not_type_III(d->u.ddd.arc[ci].child, e))
        return((int) (ce->result = (struct red_type *) TYPE_FALSE));
  }
  return((int) (ce->result = (struct red_type *) TYPE_TRUE));
}
/* rec_check_not_type_III() */




int check_not_type_III(d, vi)
  struct red_type *d;
{
  int result;

  T3_VI = vi;
  result = rec_check_not_type_III(d, ddd_atom(VI_VALUE, vi, vi)); 
  
  return(result);
}
  /* check_not_type_III() */






int timed_inactive_type_III_check(vi, mi, riptr)
  int vi, mi, *riptr;
{
  int pi, ixi, xi, lhs_vi, ai, iri;

  pi = VAR[vi].PROC_INDEX;
  if (VAR[vi].TYPE == TYPE_DENSE) {
    for (iri = 0; iri < MODE[mi].rate_spec_count; iri++)
      if (MODE[mi].process_rate_spec[pi].rate_spec[iri].var_index == vi) {
        *riptr = iri;
  if (MODE[mi].process_rate_spec[pi].rate_spec[iri].lb_numerator < 0)
    if (MODE[mi].process_rate_spec[pi].rate_spec[iri].ub_numerator > 0)
      return(TYPE_FALSE);
  break;
      }
    if (iri >= MODE[mi].rate_spec_count)
      return(TYPE_FALSE);
  }

  PAR = (struct hrd_exp_type **) malloc(DENSE_COUNT * sizeof(struct hrd_exp_type *));
  PAR_ub_numerator = (int *) malloc(DENSE_COUNT * sizeof(int));
  PAR_ub_denominator = (int *) malloc(DENSE_COUNT * sizeof(int));
  par_top = 0;
  d_mode = ddd_atom(variable_index[TYPE_DISCRETE][pi][0], mi, mi);

  for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
    xi = PROCESS[pi].firable_xtion[ixi];
    if (XTION[xi].src_mode_index == mi) {
      if (!vi_writing_in_statement(vi, pi, XTION[xi].statement)) {        
  free(PAR);
        return(TYPE_FALSE);
      }
    }
  }
  for (mi = 0; mi < MODE_COUNT; mi++) {
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      if (check_not_type_III(red_bop(AND, d_mode, MODE[mi].invariance[pi].red), vi)) {
        free(PAR);
        return(TYPE_FALSE);
      }
    }
  }
  for (xi = 0; xi < XTION_COUNT; xi++) {
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      if (check_not_type_III(red_bop(AND, d_mode, XTION[xi].red_trigger[pi]), vi)) {
        free(PAR);
  return (TYPE_FALSE);
      }
    }
  }

  if (check_not_type_III(red_bop(AND, d_mode, SPEC_EXP->u.rpred.red), vi)) {
    free(PAR);
    return(TYPE_FALSE);
  }
  return(TYPE_TRUE);
}
  /* timed_inactive_type_III_check() */



#define TIA_BOUND_VARIABLE  -1
#define TIA_BOUND_IRRELEVANT  -2

int flag_hrd_exp_parametric_position(he, vi, poshe_ptr, neghe_ptr, gptr)
  struct hrd_exp_type *he, **poshe_ptr, **neghe_ptr;
  int     vi, *gptr;
{
  int     		len, ti, vi_position;
  struct hrd_exp_type 	*poshe, *neghe;

  len = he->status & MASK_HYBRID_LENGTH;
  vi_position = TIA_BOUND_IRRELEVANT;
  for (ti = 0; ti < len; ti++) {
    if (he->hrd_term[ti].var_index == vi)
      vi_position = ti;
    else if (vi_position != TIA_BOUND_IRRELEVANT && VAR[he->hrd_term[ti].var_index].PROC_INDEX)
      return(TIA_BOUND_VARIABLE);
  }
  if (vi_position != TIA_BOUND_IRRELEVANT) {
    poshe = hrd_exp_alloc(len-1);
    neghe = hrd_exp_alloc(len-1);
    for (ti = 0; ti < len; ti++)
      if (ti < vi_position) {
  poshe->hrd_term[ti].var_index = he->hrd_term[ti].var_index;
  poshe->hrd_term[ti].coeff = he->hrd_term[ti].coeff;
  neghe->hrd_term[ti].var_index = he->hrd_term[ti].var_index;
  neghe->hrd_term[ti].coeff = -1 * he->hrd_term[ti].coeff;
      }
      else if (ti > vi_position) {
  poshe->hrd_term[ti-1].var_index = he->hrd_term[ti].var_index;
  poshe->hrd_term[ti-1].coeff = he->hrd_term[ti].coeff;
  neghe->hrd_term[ti-1].var_index = he->hrd_term[ti].var_index;
  neghe->hrd_term[ti-1].coeff = -1 * he->hrd_term[ti].coeff;
      }
    for (*gptr = poshe->hrd_term[0].coeff, ti = 1; ti < len-1; ti++)
      *gptr = gcd(*gptr, poshe->hrd_term[ti].coeff);
    *gptr = abs(*gptr);

    for (ti = 0; ti < len-1; ti++) {
      poshe->hrd_term[ti].coeff = poshe->hrd_term[ti].coeff / *gptr;
      neghe->hrd_term[ti].coeff = neghe->hrd_term[ti].coeff / *gptr;
    }
    *poshe_ptr = hrd_exp_fillin(poshe, FLAG_HRD_EXP_STATIC);
    *neghe_ptr = hrd_exp_fillin(neghe, FLAG_HRD_EXP_STATIC);
  }
  return(vi_position);
}
  /* flag_hrd_exp_parametric_position() */






void  rec_collect_red_timed_constant_exclusion(d, mi)
     struct red_type  *d;
     int    mi;
{
  struct red_type *result;
  int     c1, c2, ci, b, bn, bd, sbn, sbd, ti, coeff, g;
  struct hrd_exp_type *poshe, *neghe;
  struct rec_type *rec, *nrec;

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
      d, d->var_index
      );
*/
  if (   d->var_index == TYPE_TRUE
      || d->var_index == TYPE_FALSE
      || VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive == NORM_FALSE
      )
    return;

  rec = rec_new(d, NORM_FALSE);
  nrec = (struct rec_type *) add_23tree(rec, peer_tree, rec_comp, rec_free,
          rec_nop, rec_parent_set, rec_print
          );
  if (rec != nrec) {
    return;
  }
  else
    nrec->result = NORM_NO_RESTRICTION;

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (CLOCK[c1] == TIA_VI) {
      if (c2) {
        VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
      }
      else {
        for (ci = 0; ci < d->u.crd.child_count; ci++) {
          b = d->u.crd.arc[ci].upper_bound;
          if (b != CLOCK_POS_INFINITY) {
            if (b % 2)
              b++;
            if (   b < VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator
                && b > VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator
                ) {
              VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
              break;
            }
          }
        }
      }
    }
    else if (CLOCK[c2] == TIA_VI) {
      if (c1) {
        VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
      }
      else {
        for (ci = 0; ci < d->u.crd.child_count; ci++) {
          b = -1*d->u.crd.arc[ci].upper_bound;
          if (b != CLOCK_POS_INFINITY) {
            if (b % 2)
              b++;
            if (   b < VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator
                && b > VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator
                ) {
              VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
              break;
            }
          }
        }
      }
    }
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      rec_collect_red_timed_constant_exclusion(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1) {
      if (TIA_VI == d->u.hrd.hrd_exp->hrd_term[0].var_index) {
        if (d->u.hrd.hrd_exp->hrd_term[0].coeff > 0) {
          for (ci = 0; ci < d->u.hrd.child_count; ci++) {
            bn = d->u.hrd.arc[ci].ub_numerator;
            bd = d->u.hrd.arc[ci].ub_denominator;
            if (bn != HYBRID_POS_INFINITY && bd != 1) {
              if (b % 2)
                b++;
              if (   (   (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator == HYBRID_POS_INFINITY
                          && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator == 1
                          )
                      || bn * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator
                         < VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator * bd
                      )
                  && (   (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator == HYBRID_NEG_INFINITY
                          && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator == 1
                          )
                      || bn * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator
                         > VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator * bd
                      )
                  ) {
                VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
                break;
              }
            }
          }
        }
        else {
          for (ci = 0; ci < d->u.hrd.child_count; ci++) {
            bn = -1*d->u.hrd.arc[ci].ub_numerator;
            bd = d->u.hrd.arc[ci].ub_denominator;
            if (bn != HYBRID_POS_INFINITY && bd != 1) {
              if (b % 2)
                b++;
              if (   (   (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator == HYBRID_POS_INFINITY
                          && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator == 1
                          )
                      || bn * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator
                         < VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator * bd
                      )
                  && (   (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator == HYBRID_NEG_INFINITY
                          && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator == 1
                          )
                      || bn * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator
                         > VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator * bd
                      )
                  ) {
                VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
                break;
              }
            }
          }
        }
      }
    }
    else switch (ti = flag_hrd_exp_parametric_position(d->u.hrd.hrd_exp, TIA_VI, &poshe, &neghe, &g)) {
    case TIA_BOUND_VARIABLE:
      VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
      break;
    case TIA_BOUND_IRRELEVANT:
      break;
    default:
      coeff = d->u.hrd.hrd_exp->hrd_term[ti].coeff;
      if (coeff > 0) {
        /* ax+gB~c L<=x<=U
   * --> x ~ (c-gB)/a --> U <= (c-gB)/a --> gB/a <= c/a - U --> B<= c/g - aU/g
   *                  --> (c-gB)/a <= L --> -gB/a <= L - c/a --> -B <= aL/g - c/g
   */
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          bn = d->u.hrd.arc[ci].ub_numerator;
          bd = d->u.hrd.arc[ci].ub_denominator;
          if (bn != HYBRID_POS_INFINITY || bd != 1) {
            if (bn % 2)
              bn++;
            if (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator == HYBRID_POS_INFINITY
                && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator == 1
                )
              result = NORM_FALSE;
            else {
              hybrid_ub_add(-1* coeff * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator,
                VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator,
                bn, bd,
                &sbn, &sbd
                );
              result = hrd_atom(poshe, sbn, sbd);
            }
            if (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator != HYBRID_NEG_INFINITY
                || VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator != 1
                ) {
              hybrid_ub_add(coeff * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator,
                g * VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator,
                -1*bn, bd * g,
                &sbn, &sbd
                );
              result = red_bop(OR, result, hrd_atom(neghe, sbn, sbd));
            }
            VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive
            = red_bop(AND, result, VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive);
          }
        }
      }
      else {
        /* -ax+gB~c L<=x<=U
   * --> x ~ (gB-c)/a --> U <= (gB-c)/a --> -gB/a <= -c/a - U --> -B<= -c/g - aU/g
   *                  --> (gB-c)/a <= L --> gB/a <= L + c/a --> B <= aL/g + c/g
   */
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          bn = d->u.hrd.arc[ci].ub_numerator;
          bd = d->u.hrd.arc[ci].ub_denominator;
          if (bn != HYBRID_POS_INFINITY || bd != 1) {
            if (bn % 2)
              bn++;
            if (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator == HYBRID_POS_INFINITY
                && VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator == 1
                )
              result = NORM_FALSE;
            else {
              hybrid_ub_add(coeff*VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_numerator,
                g*VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].ub_denominator,
                -1*bn, g*bd,
                &sbn, &sbd
                );
              result = hrd_atom(neghe, sbn, sbd);
            }
            if (   VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator != HYBRID_NEG_INFINITY
                || VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator != 1
                ) {
              hybrid_ub_add(-1*coeff*VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_numerator,
                g*VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].lb_denominator,
                bn, g*bd,
                &sbn, &sbd
                );
              result = red_bop(OR, result, hrd_atom(poshe, sbn, sbd));
            }
            VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive
            = red_bop(AND, result, VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive);
          }
        }
      }
    }
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_collect_red_timed_constant_exclusion(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_LAZY_EXP:
    if (check_vi_in_exp_possibly(d->u.lazy.exp, TIA_VI) != TYPE_FALSE) { 
      VAR[TIA_VI].MODE_TIMED_INACTIVE[TIA_MI].red_timed_inactive = NORM_FALSE;
    }
    rec_collect_red_timed_constant_exclusion(d->u.lazy.true_child);
    rec_collect_red_timed_constant_exclusion(d->u.lazy.false_child);
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_collect_red_timed_constant_exclusion(d->u.fdd.arc[ci].child);
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_collect_red_timed_constant_exclusion(d->u.dfdd.arc[ci].child);
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_collect_red_timed_constant_exclusion(d->u.ddd.arc[ci].child);
  }
}
/* rec_collect_red_timed_constant_exclusion() */




/* We have not taken care of inequalities like x = y */
void  collect_red_timed_constant_exclusion(d)
     struct red_type  *d;
{
  init_23tree(&peer_tree);
  rec_collect_red_timed_constant_exclusion(d);
  free_entire_23tree(peer_tree, rec_free);
}
/* collect_red_timed_constant_exclusion() */








void  collect_timed_constant_exclusion(vi, mi)
  int vi, mi;
{
  int pi, imi, mip, ixi, xi;

  TIA_PI = VAR[vi].PROC_INDEX;
  TIA_VI = vi;
  TIA_MI = mi;
  VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive = NORM_NO_RESTRICTION;

  collect_red_timed_constant_exclusion(SPEC_EXP->u.rpred.red);
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    if (pi != TIA_PI) {
      for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
        mip = PROCESS[pi].reachable_mode[imi];
        collect_red_timed_constant_exclusion(MODE[mip].invariance[pi].red);
      }
      for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
        xi = PROCESS[pi].firable_xtion[ixi];
        collect_red_timed_constant_exclusion(XTION[xi].red_trigger[pi]);
      }
    }

  red_mark(VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive, FLAG_GC_STABLE);
}
  /* collect_timed_constant_exclusion() */





void  mode_timed_inactive_analyze()
{
  int     vi, pi, imi, mi, svi;
  struct hrd_exp_type *he;
/*
  fprintf(RED_OUT, 
    "Entering mode_timed_inactive_analyze() with RT[REFINED_GLOBAL_INVARIANCE=%1d]:\n", 
    REFINED_GLOBAL_INVARIANCE
  ); 
  red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
*/
  record_timed_invariance_bounds(RT[REFINED_GLOBAL_INVARIANCE]);
  
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    if (!(pi = VAR[vi].PROC_INDEX))
      continue;
    else switch (VAR[vi].TYPE) {
    case TYPE_DENSE:
    case TYPE_CLOCK:
      if (VAR[vi].STATUS & FLAG_VAR_PRIMED) {
        VAR[vi].RED_TIMED_INACTIVE 
        = hybrid_given_primed_replace(
          VAR[VAR[vi].PRIMED_VI].RED_TIMED_INACTIVE, 
          VAR[vi].PRIMED_VI
        );
        red_mark(VAR[vi].RED_TIMED_INACTIVE, FLAG_GC_STABLE);

        #if RED_DEBUG_INACTIVE_MODE
        fprintf(RED_OUT, "\nVAR[%1d:%s].RED_TIMED_INACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_TIMED_INACTIVE);
	#endif 
	
        VAR[vi].RED_TIMED_ACTIVE 
        = hybrid_given_primed_replace(
            VAR[VAR[vi].PRIMED_VI].RED_TIMED_ACTIVE, 
            VAR[vi].PRIMED_VI
          );
        red_mark(VAR[vi].RED_TIMED_ACTIVE, FLAG_GC_STABLE);

        #if RED_DEBUG_INACTIVE_MODE
        fprintf(RED_OUT, "\nVAR[%1d:%s].RED_TIMED_ACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_TIMED_ACTIVE);
	#endif 
      }
      else {
        VAR[vi].RED_TIMED_INACTIVE = NORM_FALSE;
        for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) {
          mi = PROCESS[pi].reachable_mode[imi];
          if (timed_inactive_empty(
                VAR[vi].MODE_TIMED_INACTIVE[mi].lb_numerator,
                VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator,
                VAR[vi].MODE_TIMED_INACTIVE[mi].ub_numerator,
                VAR[vi].MODE_TIMED_INACTIVE[mi].lb_denominator
                )
              ) {
            VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive = NORM_FALSE;
            continue;
          }

    /* Detection of type 1:
     * incoming with matching interval assignment and outgoing endpoint triggering points.
     */
          if (   timed_inactive_type_I_check(vi, mi)
/*
              || timed_inactive_type_II_check(vi, mi)
*/
              ) {
    /* Detection of type 2:
     * no invariance conditon and no triggering condition at all and outgoing constant assignment.
     */
            collect_timed_constant_exclusion(vi, mi);
          }
/*
    else if (timed_inactive_type_III_check(vi, mi)) {
      collect_timed_constant_below(vi, mi);
    }
*/
          VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive = NORM_FALSE;

          VAR[vi].RED_TIMED_INACTIVE
          = red_bop(OR, VAR[vi].RED_TIMED_INACTIVE,
              ddd_one_constraint(
                VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive,
                variable_index[TYPE_DISCRETE][pi][0], mi, mi
            ) ); 
/*
          fprintf(RED_OUT, "\nVAR[%1d:%s].MODE_TIMED_INACTIVE[%1d:%s].red_timed_inactive:\n",
            vi, VAR[vi].NAME, mi, MODE[mi].name
          );
          red_print_graph(VAR[vi].MODE_TIMED_INACTIVE[mi].red_timed_inactive);
*/
        }
        red_mark(VAR[vi].RED_TIMED_INACTIVE, FLAG_GC_STABLE);

        #if RED_DEBUG_INACTIVE_MODE
        fprintf(RED_OUT, "\nVAR[%1d:%s].RED_TIMED_INACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_TIMED_INACTIVE);
        #endif 

        switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
        case FLAG_SYSTEM_HYBRID:
          VAR[vi].RED_TIMED_ACTIVE = red_complement(VAR[vi].RED_TIMED_INACTIVE);
          break;
        case FLAG_SYSTEM_TIMED:
          VAR[vi].RED_TIMED_ACTIVE = red_complement(VAR[vi].RED_TIMED_INACTIVE);
          break;
        }
        VAR[vi].RED_TIMED_ACTIVE 
        = red_bop(AND, VAR[vi].RED_TIMED_ACTIVE, RED_INVARIANCE[pi]);
        red_mark(VAR[vi].RED_TIMED_ACTIVE, FLAG_GC_STABLE);

        #if RED_DEBUG_INACTIVE_MODE
        fprintf(RED_OUT, "\nVAR[%1d:%s].RED_TIMED_ACTIVE:\n", vi, VAR[vi].NAME);
        red_print_graph(VAR[vi].RED_TIMED_ACTIVE);
        #endif 

        break;
      }
      break; 
    }
  }
//  exit(0); 
}
  /* mode_timed_inactive_analyze() */






struct red_type *timed_inactive_variable_eliminate(IN)
     int  IN;
{
  int     w, vi, pi, imi, mi, mode, inactive;
  struct red_type *conj;

  for (vi = 2; vi < VARIABLE_COUNT; vi++) {
    pi = VAR[vi].PROC_INDEX;
    if (   pi
	&& !(VAR[vi].STATUS & FLAG_VAR_PRIMED)
	&& (VAR[vi].TYPE == TYPE_CLOCK || VAR[vi].TYPE == TYPE_DENSE)
	) {
      RT[inactive = RT_TOP++] = red_bop(AND, RT[IN], VAR[vi].RED_TIMED_INACTIVE);
      if (RT[inactive] == NORM_FALSE)
        RT_TOP--;
      else {
	RT[IN] = red_bop(AND, RT[IN], VAR[vi].RED_TIMED_ACTIVE);
	RT[inactive] = red_variable_eliminate(RT[inactive], vi);
	RT[inactive] = red_bop(AND, RT[inactive], VAR[vi].RED_TIMED_INACTIVE);
	RT[inactive] = red_bop(AND, RT[inactive], RT[REFINED_GLOBAL_INVARIANCE]);
	RT[IN] = red_bop(OR, RT[IN], RT[inactive]);
	RT_TOP--; /* inactive */
	garbage_collect(FLAG_GC_SILENT);
      }
    }
  }

  return(RT[IN]);
}
/* timed_inactive_variable_eliminate() */




