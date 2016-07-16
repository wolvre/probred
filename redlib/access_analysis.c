/* There are two things that this module needs to do. 
 *  1. delete all the race conditions. 
 *  2. We no longer add in write lhs coherence constraint 
 *     for the equivalence and inclusion checking. 
 *     The reason is that it is too difficult to implement. 
 *     Instead, we check and forbid the following conditions. 
 *      a. If a global variable is used only by one role, then it is OK. 
 *      b. No global variable can be used by more than one role.  
 *	c. No role can access the address of the other role. 
 *	d. The only communication between roles is synchronization without quantification.  
 *     If a role want to modify another role's variables, local or global, 
 *     it must do it with synchronizations without quantifications.  
 * Moreover, we need to overhaul the precision of the access pattern of all xtions, 
 * sync_xtions, and filter_sync_xtions.  
 */ 

#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include "redbasics.h"  
#include "redbasics.e"  

#include "redbop.h"  
#include "redbop.e"  

#include "zone.h" 
#include "zone.e" 

#include "fxp.h"

#include "hybrid.e" 

#include "redparse.h" 
#include "redparse.e"  

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "bisim.e" 

#define INDEX_MODL_WRITE		0
#define	INDEX_MODL_READ_IN_STATEMENT	1
#define	INDEX_MODL_READ_IN_TRIGGER	2
#define	INDEX_MODL_READ_IN_INVARIANCE	3

#define INDEX_SPEC_WRITE		4 
#define	INDEX_SPEC_READ_IN_STATEMENT	5 
#define	INDEX_SPEC_READ_IN_TRIGGER	6 
#define	INDEX_SPEC_READ_IN_INVARIANCE	7

#define INDEX_ENVR_WRITE		8
#define	INDEX_ENVR_READ_IN_STATEMENT	9
#define	INDEX_ENVR_READ_IN_TRIGGER	10
#define	INDEX_ENVR_READ_IN_INVARIANCE	11

#define	FLAG_GAME_QSYNC_USED		(0x01000)
#define	FLAG_GAME_QCONS_USED		(0x02000) 
#define FLAG_GAME_GLOBAL_READ		(0x04000)
#define FLAG_GAME_GLOBAL_WRITE		(0x08000)
/* The following two constants are defined in redbasics for the direction of the 
 * synchronizations. 
#define	FLAG_ACCESS_WRITE		-1
#define	FLAG_ACCESS_READ		1
*/
struct rw_type {
  int			proc_index, xtion_index, type; 
  struct rw_type	*next_rw; 
};



struct var_access_type { 
  int			status, *count; 
  struct rw_type	**access; 
}
  *va; 
 
#define	SCOPE_CONTEXT_INVARIANCE	1
#define	SCOPE_CONTEXT_TRIGGER		2
#define	SCOPE_CONTEXT_STATEMENT		3
#define	SCOPE_CONTEXT_INITIAL		4
#define	SCOPE_CONTEXT_SPEC		5


/* If there are quantified syncs in this xi, then the address calculation can be 
 * complicated and we need to process it with sync_xtion. 
 */ 




struct rw_type	*add_rw(list, vi, pi, xi, type)
     struct rw_type	*list; 
     int		vi, pi, xi, type; 
{
  struct rw_type	*ip, *next_ip, dummy_rw, *new_ip; 

  dummy_rw.next_rw = list; 
/* 
  fprintf(RED_OUT, "\n----add write pi=%1d; xi = %1d; type = %1d; value = %1d ----\n", 
  	  pi, xi, type, value
  	  ); 
*/ 
  for (ip = &dummy_rw, next_ip = list; 
          next_ip != NULL
       && (   next_ip->proc_index < pi 
	   || (next_ip->proc_index == pi && next_ip->xtion_index < xi)
	   || (next_ip->proc_index == pi && next_ip->xtion_index == xi && next_ip->type < type)
	   ); 
       ip = next_ip, next_ip = next_ip->next_rw
       ) {
/* 
    fprintf(RED_OUT, "searching next_ip->pi = %1d; xi = %1d\n", 
    	    next_ip->proc_index, next_ip->xtion_index
    	    ); 
*/ 
  } 
       
  if (   next_ip == NULL 
      || next_ip->proc_index > pi 
      || (next_ip->proc_index == pi && next_ip->xtion_index > xi)
      || (next_ip->proc_index == pi && next_ip->xtion_index == xi && next_ip->type > type)
      ) { 
    new_ip = (struct rw_type *) malloc(sizeof(struct rw_type));
/*
    fprintf(RED_OUT, "new rw=%x..%x added in add_write(vi=%1d).\n", new_ip, new_ip+1, vi); 
    fflush(RED_OUT); 
*/
    new_ip->proc_index = pi; 
    new_ip->xtion_index = xi; 
    new_ip->type = type; 
/* 
    new_ip->value = value; 
*/
    ip->next_rw = new_ip; 
    new_ip->next_rw = next_ip; 
  } 
  return(dummy_rw.next_rw);  
}
/* add_rw() */ 






free_rw_list(list)
     struct rw_type	*list;
{
  struct rw_type	*nip;

  for (; list; ) {
    nip = list;
    list = list->next_rw;
/*
    fprintf(RED_OUT, "old rw=%x..%x freed in free_rw_list().\n", nip, nip+1); 
    fflush(RED_OUT); 
*/
    free(nip);
  }
}
/* free_rw_list() */




void	register_var_access(vi, pi, context, xi, type) 
	int	vi, pi, context, xi, type; 
{ 
  switch (type) { 
  case FLAG_ACCESS_WRITE:  
    switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
      va[vi].access[INDEX_SPEC_WRITE] = add_rw(va[vi].access[INDEX_SPEC_WRITE], 
					       vi, pi, xi, type
					       );  
      va[vi].count[INDEX_SPEC_WRITE]++; 
      break; 
    case FLAG_GAME_MODL: 
      va[vi].access[INDEX_MODL_WRITE] = add_rw(va[vi].access[INDEX_MODL_WRITE], 
					       vi, pi, xi, type
					       );  
      va[vi].count[INDEX_MODL_WRITE]++; 
      break; 
    case FLAG_GAME_ENVR: 
      va[vi].access[INDEX_ENVR_WRITE] = add_rw(va[vi].access[INDEX_ENVR_WRITE], 
					       vi, pi, xi, type
					       );  
      va[vi].count[INDEX_ENVR_WRITE]++; 
      break; 
    default: 
      fprintf(RED_OUT, "Illegal process roles %x in register_var_access().\n", 
	      PROCESS[pi].status & MASK_GAME_ROLES
	      ); 
      fflush(RED_OUT); 
      bk(); 
    } 
    break; 
  case FLAG_ACCESS_READ: 
    switch (context) { 
    case SCOPE_CONTEXT_INVARIANCE: 
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        va[vi].access[INDEX_SPEC_READ_IN_INVARIANCE] 
        = add_rw(va[vi].access[INDEX_SPEC_READ_IN_INVARIANCE], vi, pi, xi, type);  
        va[vi].count[INDEX_SPEC_READ_IN_INVARIANCE]++; 
        break; 
      case FLAG_GAME_MODL: 
        va[vi].access[INDEX_MODL_READ_IN_INVARIANCE] 
        = add_rw(va[vi].access[INDEX_MODL_READ_IN_INVARIANCE], vi, pi, xi, type);  
        va[vi].count[INDEX_MODL_READ_IN_INVARIANCE]++; 
        break; 
      case FLAG_GAME_ENVR: 
        va[vi].access[INDEX_ENVR_READ_IN_INVARIANCE] 
        = add_rw(va[vi].access[INDEX_ENVR_READ_IN_INVARIANCE], vi, pi, xi, type);  
        va[vi].count[INDEX_ENVR_READ_IN_INVARIANCE]++; 
        break; 
      default: 
        fprintf(RED_OUT, "Illegal process roles %x in register_var_access().\n", 
	        PROCESS[pi].status & MASK_GAME_ROLES
	        ); 
        fflush(RED_OUT); 
        bk(); 
      } 
      break; 
    case SCOPE_CONTEXT_TRIGGER: 
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        va[vi].access[INDEX_SPEC_READ_IN_TRIGGER] 
        = add_rw(va[vi].access[INDEX_SPEC_READ_IN_TRIGGER], vi, pi, xi, type);  
        va[vi].count[INDEX_SPEC_READ_IN_TRIGGER]++; 
        break; 
      case FLAG_GAME_MODL: 
        va[vi].access[INDEX_MODL_READ_IN_TRIGGER] 
        = add_rw(va[vi].access[INDEX_MODL_READ_IN_TRIGGER], vi, pi, xi, type);  
        va[vi].count[INDEX_MODL_READ_IN_TRIGGER]++; 
        break; 
      case FLAG_GAME_ENVR: 
        va[vi].access[INDEX_ENVR_READ_IN_TRIGGER] 
        = add_rw(va[vi].access[INDEX_ENVR_READ_IN_TRIGGER], vi, pi, xi, type);  
        va[vi].count[INDEX_ENVR_READ_IN_TRIGGER]++; 
        break; 
      default: 
        fprintf(RED_OUT, "Illegal process roles %x in register_var_access().\n", 
	        PROCESS[pi].status & MASK_GAME_ROLES
	        ); 
        fflush(RED_OUT); 
        bk(); 
      } 
      break; 
    case SCOPE_CONTEXT_STATEMENT: 
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        va[vi].access[INDEX_SPEC_READ_IN_STATEMENT] 
        = add_rw(va[vi].access[INDEX_SPEC_READ_IN_STATEMENT], vi, pi, xi, type);  
        va[vi].count[INDEX_SPEC_READ_IN_STATEMENT]++; 
        break; 
      case FLAG_GAME_MODL: 
        va[vi].access[INDEX_MODL_READ_IN_STATEMENT] 
        = add_rw(va[vi].access[INDEX_MODL_READ_IN_STATEMENT], vi, pi, xi, type);  
        va[vi].count[INDEX_MODL_READ_IN_STATEMENT]++; 
        break; 
      case FLAG_GAME_ENVR: 
        va[vi].access[INDEX_ENVR_READ_IN_STATEMENT] 
        = add_rw(va[vi].access[INDEX_ENVR_READ_IN_STATEMENT], vi, pi, xi, type);  
        va[vi].count[INDEX_ENVR_READ_IN_STATEMENT]++; 
        break; 
      default: 
        fprintf(RED_OUT, "Illegal process roles %x in register_var_access().\n", 
	        PROCESS[pi].status & MASK_GAME_ROLES
	        ); 
        fflush(RED_OUT); 
        bk(); 
      } 
      break; 
    } 
    break; 
  default: 
    fprintf(RED_OUT, "Error: an illegal operation on variable %1d:%s!\n", vi, VAR[vi].NAME); 
    fflush(RED_OUT); 
    bk(""); 
    exit(0); 
  } 
}
  /* register_var_access() */  
  
  
  
  
void	register_xtion_ec_sync_status(pi, xi) 
	int	pi, xi; 
{ 
  int	isi, vi; 
  
  for (isi = 0; isi < XTION[xi].sync_count; isi++) { 
    vi = XTION[xi].sync[isi].sync_index; 
    vi = variable_index[TYPE_SYNCHRONIZER][0][vi]; 
    register_var_access(vi, pi, SCOPE_CONTEXT_TRIGGER, xi, XTION[xi].sync[isi].type); 
    switch (XTION[xi].sync[isi].status) { 
    /* What about the synchronization quantifiers ? 
     * Since the address calculation with synchronization quantifiers can 
     * be complicated, we do it through the sync_xtions. 
     */ 
    case FLAG_NO_QUANTIFIED_SYNC:
    case FLAG_ADDRESS_NULL:
      break; 
    case FLAG_ADDRESS_HOLDER: 
      va[vi].status = va[vi].status | FLAG_GAME_QSYNC_USED; 
      break; 
    case FLAG_ADDRESS_ENFORCER: 
      va[vi].status = va[vi].status | FLAG_GAME_QCONS_USED; 
      break; 
    }
  } 
}
  /* register_xtion_ec_sync_status() */   







int	SCOPE_CONTEXT_RED;

int	AA_RED_PI, AA_RED_CONTEXT, AA_RED_XI;  
void	register_var_read_ec_status(); 
void	rec_register_exp_read( 
  struct ps_exp_type	*psub 
); 

void	rec_register_red_read(d)
     struct red_type	*d;
{
  int				ci, term_count, ti;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return;

  ce = cache4_check_result_key(OP_REGISTER_RED_READ, d, 
    (struct hrd_exp_type *) AA_RED_PI,  
    AA_RED_CONTEXT,  
    AA_RED_XI
  ); 
  if (ce->result) {
    return; 
  } 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  if (d == NORM_NO_RESTRICTION) { 
    return; 
  } 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    register_var_access(CLOCK[VAR[d->var_index].U.CRD.CLOCK1], 
      AA_RED_PI, AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ
    ); 
    register_var_access(CLOCK[VAR[d->var_index].U.CRD.CLOCK2], 
      AA_RED_PI, AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ
    ); 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      rec_register_red_read(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    term_count = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH; 
    for (ti = 0; ti < term_count; ti++) { 
      register_var_access(d->u.hrd.hrd_exp->hrd_term[ti].var_index, 
			  AA_RED_PI, AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ
			  ); 
    } 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_register_red_read(d->u.hrd.arc[ci].child);
    }
    break; 

  case TYPE_LAZY_EXP: 
    rec_register_exp_read(d->u.lazy.exp); 
    rec_register_red_read(d->u.lazy.false_child);
    rec_register_red_read(d->u.lazy.true_child);
    break; 

  case TYPE_FLOAT:
    register_var_access(d->var_index, AA_RED_PI, 
      AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ
    ); 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_register_red_read(d->u.fdd.arc[ci].child);
    }
    break; 

  case TYPE_DOUBLE:
    register_var_access(d->var_index, AA_RED_PI, 
      AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ
    ); 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_register_red_read(d->u.dfdd.arc[ci].child);
    }
    break; 

  default:
    register_var_access(d->var_index, AA_RED_PI, AA_RED_CONTEXT, AA_RED_XI, FLAG_ACCESS_READ); 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_register_red_read(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_register_red_read() */




void	register_red_read(
  struct red_type	*d,  
  int			pi, 
  int			context, 
  int			xi 
) { 
  AA_RED_PI = pi; 
  AA_RED_CONTEXT = context; 
  AA_RED_XI = xi; 
  
  rec_register_red_read(d); 
}
  /* register_red_read() */  



int	AA_EXP_PI, AA_EXP_CONTEXT, AA_EXP_XI; 

void	rec_register_exp_read( 
  struct ps_exp_type	*psub 
) { 
  int				vi, pi, i, jj, flag; 
//  struct parse_indirect_type	*pt; 
  struct ps_bunit_type		*pbu; 
  
  switch (psub->type) { 
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_CONSTANT:
  case TYPE_NULL:
  case TYPE_QFD: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
    return;
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
    if (psub->u.atom.var_name == NULL) {
    // I forgot when the var_name could be NULL. 
      vi = variable_index[psub->u.atom.var->type][AA_EXP_PI][psub->u.atom.var->index];
      register_var_access(vi, AA_EXP_PI, AA_EXP_CONTEXT, AA_EXP_XI, FLAG_ACCESS_READ); 
    }
    else if (!(psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)) {
    // If it is a global, then simply register it. 
      vi = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index]; 
      register_var_access(vi, AA_EXP_PI, AA_EXP_CONTEXT, AA_EXP_XI, FLAG_ACCESS_READ); 
    } 
    else { 
      // Now it is a local.
      // First we register the variables in the address expression. 
      rec_register_exp_read(psub->u.atom.exp_base_proc_index);
    }  
    // Then we try to work on the variables and the indirections. 
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      rec_register_exp_read(psub->u.atom.indirect_exp[i]); 
    } 
*/
    return;
  case ARITH_ADD :
  case ARITH_MINUS :
  case ARITH_MULTIPLY :
  case ARITH_DIVIDE :
  case ARITH_MODULO: 
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    rec_register_exp_read(psub->u.arith.lhs_exp);
    rec_register_exp_read(psub->u.arith.rhs_exp);
    return;
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    for (jj = 0; jj < psub->u.ineq.term_count; jj++)
      rec_register_exp_read(psub->u.ineq.term[jj].operand);
    return;
  case AND :
  case OR :
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist; 
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      rec_register_exp_read(pbu->subexp); 
    }
    return;
  case NOT :
    rec_register_exp_read(psub->u.bexp.blist->subexp); 
    return; 
  case IMPLY :
    rec_register_exp_read(psub->u.bexp.blist->subexp);
    rec_register_exp_read(psub->u.bexp.blist->bnext->subexp); 
    return;
  case FORALL : 
  case EXISTS :
    rec_register_exp_read(psub->u.qexp.child);
    return; 
  case RESET:
/*
    fprintf(RED_OUT, "Test: reset clock %s with clock id %1d.\n", psub->u.reset.clock_name, psub->u.reset.clock_index);
*/
    rec_register_exp_read(psub->u.reset.child); 
    return; 
  	
  } 
}
  /* rec_register_exp_read() */ 
  


void	register_exp_read(psub, pi, context, xi) 
	struct ps_exp_type	*psub; 
	int			pi, context, xi; 
{ 
  AA_EXP_PI = pi; 
  AA_EXP_CONTEXT = context; 
  AA_EXP_XI = xi; 
  rec_register_exp_read(psub); 	
} 
  /* register_exp_read() */  
  
  
  
  

void	register_exp_write(psub, pi, context, xi) 
	struct ps_exp_type	*psub; 
{ 
//  struct parse_indirect_type	*pt; 
  int				vi, flag; 
  
  switch (psub->type) { 
  case TYPE_REFERENCE: 
    if (   psub->u.exp->type != TYPE_REFERENCE
        && !(psub->u.exp->var_status & FLAG_EXP_STATE_INSIDE)
        ) {
      vi = get_value(psub->u.exp, pi, &flag); 
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE);       
    } 
    else { 
/*
      fprintf(RED_OUT, 
        "\nWarning: difficulty in offline race analysis due to indirection in:"
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
*/
      return; 
    }
    break; 
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
/*
    if (psub->u.atom.indirect_count > 0) { 
/*
      fprintf(RED_OUT, 
        "\nWarning: difficulty in offline race analysis due to indirection in:"
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
*//* 
      return; 
    }
*/
    if (!(psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)) {
    // If it is a global, then simply register it. 
      vi = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index]; 
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
    } 
    else { 
    // I forgot when the var_name could be NULL. 
      vi = variable_index[psub->u.atom.var->type][pi][psub->u.atom.var->index];
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
    }
    return;
  default:
    fprintf(RED_OUT, "ERROR: wrong LHS types %1d.\n", psub->type);
    bk(0); 
    return; 
  } 
}
  /* register_exp_write() */ 




int	count_rerwtw = 0; 

void	register_exp_read_while_tracing_write(psub, pi, context, xi) 
	struct ps_exp_type	*psub; 
{ 
  int				i, vi, flag; 
//  struct parse_indirect_type	*pt; 
  
  switch (psub->type) { 
  case TYPE_REFERENCE: 
    register_exp_read(psub->u.exp, pi, context, xi);
    break; 
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
    register_exp_read(psub->u.atom.exp_base_proc_index, pi, context, xi);
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      register_exp_read(psub->u.atom.indirect_exp[i], pi, context, xi);
    }       
*/
/*
    if (psub->u.atom.indirect_count > 0) { 
/*
      fprintf(RED_OUT, 
        "\nWarning: difficulty in offline race analysis due to indirection in:"
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
*/
/*
      return; 
    }

    else 
*/  
    if (psub->u.atom.var_name == NULL) {
    // I forgot when the var_name could be NULL. 
      vi = variable_index[psub->u.atom.var->type][pi][psub->u.atom.var->index];
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
    }
    else if (!(psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)) {
    // If it is a global, then simply register it. 
      vi = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index]; 
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
    } 
    else switch (psub->u.atom.exp_base_proc_index->type) { 
    case TYPE_CONSTANT:
      vi = variable_index[psub->u.atom.var->type][psub->u.atom.exp_base_proc_index->u.value][psub->u.atom.var->index];
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
      break; 
    case TYPE_NULL: 
      vi = variable_index[psub->u.atom.var->type][0][psub->u.atom.var->index];
      register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
      break;         
    default: 
//      tpsubve(psub); 
      vi = get_address(psub->u.atom.exp_base_proc_index, pi, &flag);  
      if (flag == FLAG_SPECIFIC_VALUE) {
 /*
      	fprintf(RED_OUT, "\nregister_exp_read_while_tracing_write=%1d\n", 
      	  ++count_rerwtw
      	); 
      	fflush(RED_OUT); 
*/
	vi = variable_index[psub->u.atom.var->type][vi][psub->u.atom.var->index];
        register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
      }
      else for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
	vi = variable_index[psub->u.atom.var->type][pi][psub->u.atom.var->index];
        register_var_access(vi, pi, context, xi, FLAG_ACCESS_WRITE); 
      } 
    }
    return;
  default:
    fprintf(RED_OUT, "ERROR: wrong LHS types %1d.\n", psub->type);
    bk(0); 
    return; 
  } 
}
  /* register_exp_read_while_tracing_write() */ 
  
  
  
  


int	AA_ST_PI, AA_ST_XI; 

#if RED_DEBUG_ACCESS_MODE
int	rsa_count = 0; 
#endif 

void 	rec_register_statement_access(st) 
	struct statement_type	*st; 
{ 
  int	i; 

  #if RED_DEBUG_ACCESS_MODE
  fprintf(RED_OUT, "rsa_count = %1d, st = %x\n", ++rsa_count, st); 
  #endif 
  
  if (!st) 
    return; 
    
  #if RED_DEBUG_ACCESS_MODE
/*
  for (; rsa_count == 129; ); 
*/
  print_statement_line(st, 1); 
  fflush(RED_OUT); 
  #endif 
  
  switch (st->op) { 
  case UNCHANGED: 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    register_exp_read(st->u.act.lhs, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    register_exp_write(st->u.act.lhs, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    break; 
  case ST_GUARD: 
    register_exp_read(st->u.guard.cond, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    break; 
  case ST_ERASE: 
    register_exp_write(st->u.erase.var, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    register_exp_read(st->u.act.rhs_exp, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    register_exp_read_while_tracing_write(st->u.act.lhs, AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      rec_register_statement_access(st->u.seq.statement[i]); 
    break; 
  case ST_WHILE: 
    register_red_read(st->u.loop.red_cond[AA_ST_PI], 
      AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI
    ); 
    rec_register_statement_access(st->u.loop.statement); 
    break; 
  case ST_IF:  
    register_red_read(st->u.branch.red_cond[AA_ST_PI], 
      AA_ST_PI, SCOPE_CONTEXT_STATEMENT, AA_ST_XI
    ); 
    rec_register_statement_access(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      rec_register_statement_access(st->u.branch.else_statement); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
    break; 
  default: 
    fprintf(RED_OUT, "ERROR: illegal statement operation code %1d\n", st->op); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* rec_register_statement_access() */   
  


void 	register_statement_access(st, pi, xi) 
	struct statement_type	*st; 
	int			pi, xi; 
{ 
  AA_ST_PI = pi; 
  AA_ST_XI = xi; 
  rec_register_statement_access(st); 	
} 
  /* register_statement_access() */  
  
  
  
  	
  
/* recording the variable access behaviors by the roles. 
 * All information are recorded in va[]. 

 */
int	crva_count = 0; 

void	collect_roles_var_accesses_from_xtions() { 
  struct red_type	*tr;   
  int			vi, pi, ixi, xi, sxi, ai, xsi, qfd_sync_value; 
    
  va = (struct var_access_type *) malloc(VARIABLE_COUNT * sizeof(struct var_access_type)); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    va[vi].access = (struct rw_type **) malloc(12 * sizeof(struct rw_type *)); 
    va[vi].count = (int *) malloc(12 * sizeof(int)); 
    for (ai = 0; ai < 12; ai++) {
      va[vi].access[ai] = NULL;  
      va[vi].count[ai] = 0; 
    }  
  }
  
  /* Label events of the roles that used them. 
   * If there is a synchronizer used between the SPEC and the DSCR, 
   * this is a bug and we report it and exit. 
   */ 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      xi = PROCESS[pi].firable_xtion[ixi]; 
      #if RED_DEBUG_ACCESS_MODE
      fprintf(RED_OUT, "crva=%1d, pi=%1d, ixi=%1d, xi=%1d\n", ++crva_count, pi, ixi, xi); 
      fflush(RED_OUT); 
      #endif 
      
      if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC) 
        continue; 
  
      register_xtion_ec_sync_status(pi, xi); 
      register_red_read(XTION[xi].red_trigger[pi], 
        pi, SCOPE_CONTEXT_TRIGGER, xi
      ); 
      register_statement_access(XTION[xi].statement, pi, xi); 
    } 
  } 
} 
  /* collect_roles_var_accesses_from_xtions() */ 
  
  
  
  


struct xw_type { 
  int			vi, pi; 
  struct xw_type	*next_xw; 	
}
  **xw; 
  
struct xw_type	*add_xw_list(list, vi, pi)
	struct xw_type	*list; 
	int		vi, pi; 
{
  struct xw_type	dummy_head, *pw, *w, *nw; 

  dummy_head.next_xw = list; 
  pw = &dummy_head; 
  nw = list; 
  for (;
	  nw != NULL 
       && (nw->vi < vi || (nw->vi == vi && nw->pi < pi)); 
       pw = nw, nw = nw->next_xw
       ); 
  if (nw && nw->vi == vi && nw->pi == pi)
    return(list); 

  w = (struct xw_type *) malloc(sizeof(struct xw_type));
  w->vi = vi; 
  w->pi = pi; 
  w->next_xw = nw; 
  pw->next_xw = w; 
  
  return(dummy_head.next_xw); 
}
/* add_xw_list() */ 




void	collect_xi_plants_writes() {
  struct rw_type	*rw; 
  int			xi, vi; 
  
  xw = (struct xw_type **) malloc(XTION_COUNT * sizeof(struct xw_type *)); 
  for (xi = 0; xi < XTION_COUNT; xi++) { 
    xw[xi] = NULL; 	
  } 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    if (VAR[vi].PROC_INDEX) 
      continue; 
    switch (VAR[vi].TYPE) { 
    case TYPE_POINTER: 
    case TYPE_DISCRETE: 
    case TYPE_CLOCK: 
    case TYPE_DENSE: 
      for (rw = va[vi].access[INDEX_SPEC_WRITE]; rw; rw = rw->next_rw) { 
        xw[rw->xtion_index] = add_xw_list(xw[rw->xtion_index], vi, rw->proc_index); 
      } 
      for (rw = va[vi].access[INDEX_MODL_WRITE]; rw; rw = rw->next_rw) { 
        xw[rw->xtion_index] = add_xw_list(xw[rw->xtion_index], vi, rw->proc_index); 
      }
      break; 
    }  
  } 
}
  /* collect_xi_plants_writes() */ 
  
  
  
  
  

struct red_type	*red_write_consistency_from_opponents(pi, xi)
	int	pi, xi; 
{ 
  int			flag_opponent, op_opponent; 
  struct xw_type	*role_xw; 
  struct rw_type	*opponent_rw; 
  struct red_type	*result, *conj; 
  
  switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
  case FLAG_GAME_SPEC: 
    flag_opponent = FLAG_GAME_MODL; 
    op_opponent = INDEX_MODL_WRITE; 
    break; 
  case FLAG_GAME_MODL: 
    flag_opponent = FLAG_GAME_SPEC; 
    op_opponent = INDEX_SPEC_WRITE; 
    break; 	
  } 
  
  role_xw = xw[xi]; 
  result = NORM_NO_RESTRICTION; 
  for (; role_xw; role_xw = role_xw->next_xw) { 
    if (role_xw->pi == pi && !(VAR[role_xw->vi].PROC_INDEX)) { 
      conj = NORM_FALSE; 
      for (opponent_rw = va[role_xw->vi].access[op_opponent]; 
           opponent_rw; 
           opponent_rw = opponent_rw->next_rw
           ) { 
        if (PROCESS[opponent_rw->proc_index].status & flag_opponent) { 
          conj = red_bop(OR, conj, ddd_atom(variable_index[TYPE_XTION_INSTANCE][opponent_rw->proc_index][0], 
					    opponent_rw->xtion_index, 
					    opponent_rw->xtion_index
					    )
			 ); 	
        } 
      } 
      result = red_bop(AND, result, conj); 
    } 	
  } 
  return(result); 
}
  /* red_write_consistency_from_opponents() */ 
  
  
  
  
  
  
#define	FLAG_GAME_ROLE_WRITE	(0x20) 

int	ROLE_GAME_ACTIVE; 


int	flag_ec_role_writes(xi, pi)  
	int	xi, pi; 
{ 
  struct xw_type	*xw_node; 
  
  for (xw_node = xw[xi]; xw_node; xw_node = xw_node->next_xw) 
    if (xw_node->pi == pi) 
      return(FLAG_GAME_ROLE_WRITE); 
  return(TYPE_FALSE); 
} 
  /* flag_ec_role_writes() */ 
  
  


struct red_type	*rec_filter_role_writes(d, flag_role_accesses)
     struct red_type	*d;
     int		flag_role_accesses; 
{
  int			ci, pi, xi;
  struct red_type	*child, *result;
  struct ddd_child_type	*ic;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);
  else if (d == NORM_NO_RESTRICTION) {
    if ((flag_role_accesses & ROLE_GAME_ACTIVE) && (flag_role_accesses & FLAG_GAME_ROLE_WRITE)) 
      return(d);
    else 
      return(NORM_FALSE); 
  }
  
  ce = cache4_check_result_key(
    OP_FILTER_ROLE_WRITES, d, 
    NULL, 
    ROLE_GAME_ACTIVE, 
    flag_role_accesses 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    switch (PROCESS[pi = VAR[d->var_index].PROC_INDEX].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
    case FLAG_GAME_MODL: 
      if ((PROCESS[pi].status & MASK_GAME_ROLES) != ROLE_GAME_ACTIVE) 
        if (d->u.ddd.arc[0].lower_bound) 
          result = NORM_FALSE; 
        else 
          result = ddd_one_constraint
		(rec_filter_role_writes(d->u.ddd.arc[0].child, flag_role_accesses), 
		 d->var_index, 0, 0
		 );
      else for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) { 
          child = rec_filter_role_writes(ic->child, 
        				   flag_role_accesses 
        			         | (PROCESS[pi].status & MASK_GAME_ROLES)
        			         | flag_ec_role_writes(xi, pi) 
        			         );
          child = ddd_one_constraint(child, d->var_index, xi, xi); 
          result = red_bop(OR, result, child);
        }
      } 
      break; 
    case FLAG_GAME_ENVR: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_filter_role_writes(ic->child);
        child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound); 
        result = red_bop(OR, result, child);
      }
      break; 
    }
    break; 
  default:
    fprintf(RED_OUT, 
	    "ERROR: There is something wrong with RT[XI_SYNC_BULK=%1d]\n", 
	    XI_SYNC_BULK
	    ); 
    fflush(RED_OUT); 
    bk(""); 
  }

  return(ce->result 
    = (struct red_type *) result
  );
}
  /* rec_filter_role_writes() */




struct red_type	*red_filter_role_writes(f, role_active) 
	struct red_type	*f; 
{ 
  struct red_type	*result; 
  
  ROLE_GAME_ACTIVE = role_active; 
  
  result = rec_filter_role_writes(f, 0);

  return(result);
}
  /* red_filter_role_writes() */ 
  
  
  


struct red_type	*rec_dscr_spec_write_synchronizations(d)
     struct red_type	*d;
{
  int			ci, pi, xi;
  struct red_type	*gchild, *child, *result;
  struct ddd_child_type	*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_DSCR_SPEC_WRITE_SYNCHRONIZATIONS, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    switch (PROCESS[pi = VAR[d->var_index].PROC_INDEX].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
    case FLAG_GAME_MODL: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_dscr_spec_write_synchronizations(ic->child);
        for (xi = ic->lower_bound; xi <= ic->upper_bound; xi++) { 
          gchild = ddd_one_constraint(child, d->var_index, xi, xi); 
          if (xi) 
            gchild = red_bop(AND, gchild, red_write_consistency_from_opponents(pi, xi)); 
          result = red_bop(OR, result, gchild);
        } 
      }
      break; 
    case FLAG_GAME_ENVR: 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_dscr_spec_write_synchronizations(ic->child);
        child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound); 
        result = red_bop(OR, result, child);
      }
      break; 
    }
    break; 
  default:
    fprintf(RED_OUT, "ERROR: There is something wrong with RT[XI_SYNC_BULK=%1d]\n", 
	    XI_SYNC_BULK
	    ); 
    fflush(RED_OUT); 
    bk(""); 
  }

  return(ce->result = result); 
}
  /* rec_dscr_spec_write_synchronizations() */






/*********************************************************************************
 *
 */  
void	collect_roles_var_accesses_from_sync_xtions() { 
  struct red_type	*tr;   
  int			vi, pi, ixi, xi, sxi, ai, xsi, qfd_sync_value; 
    
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    for (ai = 0; ai < SYNC_XTION[sxi].qfd_sync_count; ai++) 
      VAR[SYNC_XTION[sxi].qfd_sync[ai].vi].U.DISC.WORKING_QFD_SYNC_VALUE 
      = SYNC_XTION[sxi].qfd_sync[ai].value;  
    RT[qfd_sync_value = RT_TOP++] = NORM_NO_RESTRICTION; 
    for (xsi = 0; xsi < SYNC_XTION[sxi].qfd_sync_count; xsi++) 
      RT[qfd_sync_value] 
      = ddd_one_constraint(RT[qfd_sync_value], 
        SYNC_XTION[sxi].qfd_sync[xsi].vi, 
	SYNC_XTION[sxi].qfd_sync[xsi].value, 
	SYNC_XTION[sxi].qfd_sync[xsi].value
      ); 
    for (ixi = 0; ixi < SYNC_XTION[sxi].party_count; ixi++) { 
      xi = SYNC_XTION[sxi].party[ixi].xtion; 
      pi = SYNC_XTION[sxi].party[ixi].proc; 
      register_xtion_ec_sync_status(pi, xi); 
      tr = eliminate_simple_qfd_sync(red_bop(AND, SYNC_XTION[sxi].party[ixi].red_trigger, 
					     RT[qfd_sync_value]
					     )
				     ); 
      register_red_read(tr, pi, SCOPE_CONTEXT_TRIGGER, xi); 
      register_statement_access(SYNC_XTION[sxi].party[ixi].statement, pi, xi); 
    } 	
    RT_TOP--; /* qfd_sync_value */ 
  } 
} 
  /* collect_roles_var_accesses_from_sync_xtions() */ 
  




struct red_type	*rec_eliminate_MODL_SPEC_consisitency(d, flag_roles) 
	struct red_type	*d; 
	int		flag_roles; 
{
  int			i, ci, xi, pi; 
  struct red_type	*result, *conj; 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_FALSE: 
    return(NORM_FALSE); 
  case TYPE_TRUE: 
    if (flag_roles & FLAG_GAME_ENVR) 
      return(NORM_NO_RESTRICTION); 
    else if ((flag_roles & FLAG_GAME_SPEC) && (flag_roles & FLAG_GAME_MODL)) { 
      return(NORM_FALSE); 
    }
    else 
      return(NORM_NO_RESTRICTION); 
    break;     
  case TYPE_XTION_INSTANCE: 
    pi = VAR[d->var_index].PROC_INDEX; 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) { 
      	if (xi && write_through_to_roles_in_statement
		  (XTION[xi].statement, pi, PROCESS[pi].status & MASK_GAME_ROLES)
	    )  
      	  conj = rec_eliminate_MODL_SPEC_consisitency
		 (d->u.ddd.arc[ci].child, flag_roles | (PROCESS[pi].status & MASK_GAME_ROLES)); 
      	else 
      	  conj = rec_eliminate_MODL_SPEC_consisitency(d->u.ddd.arc[ci].child, flag_roles); 
      	conj = ddd_one_constraint(conj, d->var_index, xi, xi); 
      	result = red_bop(OR, result, conj); 
      } 
    } 
    return(result); 
    break; 	
  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      conj = rec_eliminate_MODL_SPEC_consisitency(d->u.ddd.arc[ci].child, flag_roles); 
      conj = ddd_one_constraint(conj, d->var_index, xi, xi); 
      result = red_bop(OR, result, conj); 
    } 
    return(result); 
    break; 	
  } 	
}
  /* rec_eliminate_MODL_SPEC_consisitency() */  



  
struct red_type	*red_eliminate_MODL_SPEC_consisitency(d)
	struct red_type	*d; 
{
  return (rec_eliminate_MODL_SPEC_consisitency(d, 0)); 
}
  /* red_eliminate_MODL_SPEC_consisitency(); */ 
  
  
  
  
struct race_rec_type { 
  int	xtion, proc; 
} 
  *race_rec; 
  
int	top_race_rec; 

void	rec_print_race_pairs(d) 
	struct red_type	*d; 
{
  int	i, ci, xi; 
  
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_FALSE: 
    fprintf(RED_OUT, "\nERROR: There is something fishy! XX*XX\n"); 
    fflush(RED_OUT); 
    exit(0); 
  case TYPE_TRUE: 
    if (top_race_rec > 0) { 
      fprintf(RED_OUT, "(pi=%1d,xi=%1d)", race_rec[0].proc, race_rec[0].xtion); 
      for (i = 1; i < top_race_rec; i++) { 
        fprintf(RED_OUT, ",(pi=%1d,xi=%1d)", race_rec[i].proc, race_rec[i].xtion); 
      } 
      fprintf(RED_OUT, " generate a race condition.\n"); 
    }
    break;     
  case TYPE_XTION_INSTANCE: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) { 
      	if (xi == 0) 
      	  rec_print_race_pairs(d->u.ddd.arc[ci].child); 
      	else { 
      		fprintf(RED_OUT, "top_race_rec = %1d\n", top_race_rec); 
      	  race_rec[top_race_rec].proc = VAR[d->var_index].PROC_INDEX; 
      	  race_rec[top_race_rec].xtion = xi; 
      		fprintf(RED_OUT, "race_rec[top_race_rec=%1d].proc=%1d; race_rec[top_race_rec=%1d].xtion=%1d\n", 
                  top_race_rec, race_rec[top_race_rec].proc, 
                  top_race_rec, race_rec[top_race_rec].xtion
                  ); 
      	  top_race_rec++; 
      	  rec_print_race_pairs(d->u.ddd.arc[ci].child); 
      	  top_race_rec--; 
      	} 
      } 
    } 
    break; 	
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      rec_print_race_pairs(d->u.ddd.arc[ci].child); 
    } 
    break; 	
  } 	
}
  /* rec_print_race_pairs() */  
  
  
  
void	print_race_pairs(d) 
	struct red_type	*d; 
{ 
  race_rec = (struct race_rec_type *) malloc(PROCESS_COUNT * sizeof(struct race_rec_type)); 
  top_race_rec = 0; 
  
  rec_print_race_pairs(d);   
  free(race_rec); 
} 
  /* print_race_pairs() */ 
  



struct red_type	*rec_eliminate_single_party(d, party_count)
     struct red_type	*d;
     int		party_count; 
{
  int			ci; 
  struct red_type	*conj, *result;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_FALSE )
    return(NORM_FALSE); 
  else if (d == NORM_NO_RESTRICTION)
    if (party_count < 2) 
      return(NORM_FALSE); 
    else 
      return(d);

  ce = cache2_check_result_key(
    OP_ELIMINATE_SINGLE_PARTY, d, (struct red_type *) party_count
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    if (d->u.ddd.arc[0].lower_bound == 0) { 
      conj = rec_eliminate_single_party(d->u.ddd.arc[0].child, party_count);
      result = ddd_one_constraint(conj, d->var_index, 0, 0);
      if (d->u.ddd.arc[0].upper_bound > 0) {
        conj = rec_eliminate_single_party(d->u.ddd.arc[0].child, party_count+1); 
        conj = ddd_one_constraint(conj, d->var_index, 1, d->u.ddd.arc[0].upper_bound);
        result = red_bop(OR, result, conj); 
      }
      ci = 1; 
    } 
    else { 
      result = NORM_FALSE; 
      ci = 0; 
    } 
    for (; ci < d->u.ddd.child_count; ci++) { 
      conj = rec_eliminate_single_party(d->u.ddd.arc[ci].child, party_count+1); 
      conj = ddd_one_constraint
		(conj, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, conj); 
    }
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  
  return(ce->result = result); 
}
  /* rec_eliminate_single_party() */



struct red_type	*red_eliminate_single_party(d)
	struct red_type	*d; 
{ 
  struct red_type	*result; 
  
  result = rec_eliminate_single_party(d, 0);
  
  return(result);
}
  /* red_eliminate_single_party() */  
  



/* This procedure is executed before the preparation of the synchronous transitions. 
 * It is assumed that there is no dense constraints in f. 
 */ 
void	race_eliminate(f) 
	int	f; 
{ 
  struct red_type	**red_write, **red_read, *red_race, *conj, *disj; 
  int			vi, rw_race, ww_race, sxi, ipi, xi, pi, pj; 
  struct rw_type	*r; 

  /* The following procedure collects varaible access information from SYNC_XTION[].
   * The information is stored in array va[]. 
   * Note that a previous procedure, collect_roles_var_accesses_from_xtions() invoked by 
   * red_dscr_spec_write_synchronizations(),  
   * also have collected such information from XTION[].  
   * The information from both SYNC_XTION[] and XTION[] will be used in race_elimiante(). 
   */ 
/*
  fprintf(RED_OUT, "\nRace eliminate: Input synchronization diagram:\n");  
  red_print_graph(RT[f]); 
*/
  collect_roles_var_accesses_from_xtions(); 
  collect_xi_plants_writes(); 
  collect_roles_var_accesses_from_sync_xtions(); 

  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
/*
    fprintf(RED_OUT, "VAR[vi=%1d].NAME:%s in race_eliminate()\n", vi, VAR[vi].NAME); 
    fflush(RED_OUT); 
*/
    switch (VAR[vi].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
    case TYPE_DENSE: 
    case TYPE_CLOCK: 
      break; 
    default: 
      continue; 
    }
    /* 1. we check the races in RT[XI_SYNC_BULK] */ 
    /* For the ww races. */ 
    red_write = (struct red_type **) malloc((PROCESS_COUNT + 1)*sizeof(struct red_type *)); 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      red_write[pi] = NORM_FALSE; 
    }
    for (r = va[vi].access[INDEX_MODL_WRITE]; r; r = r->next_rw) { 
      red_write[r->proc_index] = red_bop(OR, 
        red_write[r->proc_index], 
	ddd_atom(variable_index[TYPE_XTION_INSTANCE][r->proc_index][0], 
	  r->xtion_index, r->xtion_index
      ) ); 
    } 
/*    
    if (vi == 16) { 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        fprintf(RED_OUT, "\nred_write[pi=%1d] for vi=%1d:%s:\n", 
          pi, vi, VAR[vi].NAME
        ); 
        red_print_graph(red_write[pi]); 
    } }
*/
    /* construct the condition for write-write races. */
    RT[ww_race = RT_TOP++] = NORM_FALSE; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      for (pj = pi+1; pj <= PROCESS_COUNT; pj++) { 
/*
      fprintf(RED_OUT, "\nFor vi = %1d:%s, red_write[pi=%1d]:\n", 
        vi, VAR[vi].NAME, pi
      ); 
      red_print_graph(red_write[pi]); 
*/      
        RT[ww_race] = red_bop(OR, RT[ww_race], 
          red_bop(AND, red_write[pi], red_write[pj])
        ); 
    } }
/*
    if (vi == 16) { 
      fprintf(RED_OUT, "\nFor vi = %1d:%s, RT[ww_race=%1d]:\n", 
        vi, VAR[vi].NAME, ww_race
      ); 
      red_print_graph(RT[ww_race]); 
    }
*/  
    RT[ww_race] = red_eliminate_single_party(RT[ww_race]); 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) { 
    case TASK_BRANCHING_BISIM_CHECKING: 
    case TASK_BRANCHING_SIM_CHECKING: 
      /* We use the following procedure to skip those write conflicts only by SPEC and DSCR. 
       * Such conflicts will be checked for their write consistency later in the red_ec_risk(). 
       * Note that we do not check whether the write-values are the same or not. 
       */
      RT[ww_race] = red_eliminate_MODL_SPEC_consisitency(RT[ww_race]); 
/*
      fprintf(RED_OUT, "\nFor vi = %1d:%s, RT[ww_race=%1d] after model spec analysis:\n", 
        vi, VAR[vi].NAME, ww_race
      ); 
      red_print_graph(RT[ww_race]); 
*/
      break; 
    } 

    /* check those ww races in RT[XI_SYNC_BULK].  */ 
    red_race = red_bop(AND, RT[f], RT[ww_race]); 
    if (red_race != NORM_FALSE) { 
      fprintf(RED_OUT, "\nWARNING: write-write race on variable %1d:%s in the following synchronizations.\n", 
	      vi, VAR[vi].NAME
	      ); 
      fprintf(RED_OUT, "\n       Racing conditions will be automatically removed. \n"); 
      print_race_pairs(red_race); 
//      RT[f] = red_bop(SUBTRACT, RT[f], red_race); 
    } 
      
    /* For the rw races. */ 
    red_read = (struct red_type **) malloc((PROCESS_COUNT + 1)*sizeof(struct red_type *)); 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    	red_read[pi] = NORM_FALSE; 
    }
    for (r = va[vi].access[INDEX_MODL_READ_IN_STATEMENT]; r; r = r->next_rw) { 
      red_read[r->proc_index] = red_bop(OR, red_read[r->proc_index], 
        ddd_atom(variable_index[TYPE_XTION_INSTANCE][r->proc_index][0], 
	  r->xtion_index, r->xtion_index
	)
      ); 
    } 
/*
    if (vi == 16) { 
      fprintf(RED_OUT, 
        "\n---[collecting red_reads for vi=%1d:%s]--------\n", 
        vi, VAR[vi].NAME
      ); 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        fprintf(RED_OUT, "red_read[pi=%1d]:\n", pi); 
        red_print_graph(red_read[pi]); 
    } }
*/
/*
    if (vi == 16) { 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        fprintf(RED_OUT, "\nred_read[pi=%1d] for vi=%1d:%s:\n", 
          pi, vi, VAR[vi].NAME
        ); 
        red_print_graph(red_read[pi]); 
    } }
*/
    /* construct the condition for read-write races. */
    RT[rw_race = RT_TOP++] = NORM_FALSE; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      for (pj = pi+1; pj <= PROCESS_COUNT; pj++) { 
        RT[rw_race] = red_bop(OR, RT[rw_race], 
          red_bop(OR, 
            red_bop(AND, red_read[pi], red_write[pj]), 
            red_bop(AND, red_write[pi], red_read[pj])
        ) ); 
/* 
        red_variable_eliminate(
          red_write[pi], 
          variable_index[TYPE_XTION_INSTANCE][pi][0]
        )
      ); 
*/ 
      /*
      if (vi == 16) { 
      	fprintf(RED_OUT, "\n******************\nFor vi = %1d:%s, red_read[pi=%1d]:\n", 
          vi, VAR[vi].NAME, pi
        ); 
        red_print_graph(red_read[pi]); 
        fprintf(RED_OUT, "\nFor vi = %1d:%s, collective red_write[pj] :\n", 
          vi, VAR[vi].NAME 
        ); 
        red_print_graph(disj); 
        
        fprintf(RED_OUT, "\nFor vi = %1d:%s for pi=%1d, new fragment of rw_race:\n", 
          vi, VAR[vi].NAME, pi
        ); 
        red_print_graph(conj); 
      } 
      */
    } }
    free(red_write); 
    free(red_read); 
/* 
    if (vi == 16) { 
      fprintf(RED_OUT, "\nFor vi = %1d:%s, RT[rw_race=%1d]:\n", 
        vi, VAR[vi].NAME, rw_race
      ); 
      red_print_graph(RT[rw_race]); 
    }
*/    
    RT[rw_race] = red_eliminate_single_party(RT[rw_race]); 
    /* check those rw races in RT[XI_SYNC_BULK].  */ 
    red_race = red_bop(AND, RT[f], RT[rw_race]); 
    if (red_race != NORM_FALSE) { 
      fprintf(RED_OUT, "\nERROR: read-write race on variable %1d:%s in the following synchronizations.\n", 
	      vi, VAR[vi].NAME
	      ); 
      fprintf(RED_OUT, "\n       Racing conditions will be automatically removed. \n"); 
      print_race_pairs(red_race); 
//      RT[f] = red_bop(SUBTRACT, RT[f], red_race); 
    } 

    RT_TOP = RT_TOP-2; /* rw_race, ww_race */  
  } 
  
  /* free all the variable access information that we have collected. 
   */ 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    free(va[vi].count); 
    for (ipi = 0; ipi < 12; ipi++) {
      struct rw_type	*r2; 
      
      for (r = va[vi].access[ipi]; r; r2 = r, r = r->next_rw, free(r2)); 
    } 
    free(va[vi].access); 
  } 
  free(va); 
/*  
  fprintf(RED_OUT, "\nLeaving race eliminate with synchronization diagram:\n");  
  red_print_graph(RT[f]); 
*/
} 
  /* race_eliminate() */ 

  
