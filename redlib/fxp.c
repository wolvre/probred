//
// In Oct. 4, 2007, we changed the precondition and postcondition 
// evaluation to accommodate the role evaluation in simulation-checking or 
// bisimulation-checking. 
// However, this could be challenging since we do not know 
// when the users might change the role assignments. 
// As a result, we may need to separate the sync_bulk structure into 
// two groups. 
// One is for the regular sync bulk from the input. 
// This group should be built in the first place after parsing. 
// The second is for simulation checking. 
// This group should be built dynamically.  
// Everytime when we see a new role assignment, we will start 
// construction for this group again.  
// This design decisions means that we may pretty much need two sets of 
// sync_xtions and two sets of sync bulk data structures. 
// 
// The initial data structure for the 1st group is as follows.  
//   SYNC_XTION, 
//   SYNC_XTION_COUNT, 
//   XI_RESTRICITON_SYNC
// The derived data-structure for the 2nd group is as follows. 
//   SIM_SYNC_XTION, 
//   SIM_SYNC_XTION_COUNT, 
//   SIM_XI_RESTRICTION, ... 

/* What kind of static RT stack frames do we need ? 
   
#define	INDEX_FALSE				0
#define	INDEX_TRUE 				1

#define DECLARED_GLOBAL_INVARIANCE 		2
#define INDEX_INITIAL				3
#define	INDEX_GOAL 				4
#define INDEX_ZENO_FROM_DESCRIPTION		5

#define	XI_SYNC_ALL				6 
#define XI_SYNC_ALL_WITH_PROC_HOLDERS		7 
#define	XI_SYNC_BULK				8
#define XI_SYNC_BULK_WITH_POSTCONDITION		9
#define XI_SYNC_BULK_WITH_TRIGGERS		10

#define	XI_GAME_SYNC_ALL			11
#define XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS	12 // This actually not used 
						  // since we don't know how 
						  // to forbid the synchronization
						  // between SPEC and MODL.  
#define	XI_GAME_SYNC_BULK			13
#define XI_GAME_SYNC_BULK_WITH_POSTCONDITION	14
#define XI_GAME_SYNC_BULK_WITH_TRIGGERS		15

#define	OFFSET_WITH_PROC_HOLDERS		1
#define	OFFSET_BULK 				2
#define	OFFSET_BULK_WITH_POSTCONDITION		3
#define	OFFSET_BULK_WITH_TRIGGERS		4 

#define INDEX_REFINED_GLOBAL_INVARIANCE 			16
#define INDEX_NONZENO_BY_FAIRNESS_TERMINATION	17
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

#include "fxp.h" 

#include "vindex.e"

#include "treeman.h" 
#include "treeman.e" 

#include "redbop.h"
#include "redbop.e"

#include "hybrid.e"

#include "zone.h"  
#include "zone.e"
#include "zapprox.e"

#include "redparse.h"
#include "redparse.e"

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "redsymmetry.e"

#include "action.e"

#include "redstream.e" 

#include "bisim.e" 
#include "redgame.e" 

#include "inactive.e"

// #include "coverage.e"

#include "counter.e" 

#include "redlib.h" 
#include "redlib.e" 

#ifdef RED_DEBUG_FXP_MODE
struct red_type	*orig_rt46; 
#endif 

int	NZF; 
struct red_type	*red_tmp_goal; 

#define	FLAG_GOAL_EARLY_REACHED	1
#define FLAG_GOAL_NORMAL	0

/* return values of red_reachable_fwd() and red_reachable_bck(), 
 * When it is non-negative, then it means the iteration count at which 
 * a goal state is reached. 
 */ 
#define	FLAG_UNREACHABLE			-1
#define	FLAG_REACHABILITY_DEPTH_BOUND_FINISHED	-2


// The following constant is used to forbid the operation of exclusion of 
// reachability image in the current round of pre or post condition 
// evaluation. 
// 
#define FLAG_NO_CUR_REACHABLE_EXCLUSION	-1 


#define FLAG_OPPONENT_ELIMINATE	1
#define FLAG_OPPONENT_KEEP	0

#define FLAG_POST_PROCESSING	1
#define FLAG_NO_POST_PROCESSING	0



int	REACHABLE, PARAMETER_COMPLEMENT, REACHABLE_COMPLEMENT,
	**current_firable_xtion;
int	NULL_EVENTS; // used only when model-checking is used. 

int			*firable_xtion, firable_xtion_count, GXPI;
struct index_link_type	**fx_list;


int	FXPI;

/* assume that the pi is recorded in ascending order. */
int	*px;

#ifdef RED_DEBUG_FXP_DEBUG  
int	sxi_stack[100], sxi_top=0; 

void	push_sxi_stack(int iter, int sxi) { 
  sxi_top++; 
  if (sxi_top >= 100) { 
    fprintf(RED_OUT, "\nSXI stack overflow!\n"); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  else if (sxi_top != iter) { 
    fprintf(RED_OUT, "\nStack top index %1d!=%1d inconsistency\n", iter, sxi_top); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  else if (sxi < -1 || sxi >= SYNC_XTION_COUNT) { 
    fprintf(RED_OUT, "\nIllegal SXI in push_sxi_stack().\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  sxi_stack[sxi_top] = sxi; 
} 
  /* push_sxi_stack() */  


  
void 	reset_sxi_stack() { 
  sxi_top = 0; 	
} 
  /* reset_sxi_stack() */ 



int	check_sxi_stack(int iter, int sxi) { 
  if (iter > sxi_top) { 
    return(1); 
  } 
  else if (sxi_stack[iter] == sxi) { 
    return(1); 	
  } 
  else 
    return(0); 
} 
  /* check_sxi_stack() */  



void	print_sxi_stack(int iter, int sxi, struct red_type *d) { 
  if (iter > sxi_top) { 
    return; 
  } 
  else if (sxi_stack[iter] == sxi) { 
    if (sxi == -1) 
      fprintf(RED_OUT, "\n******(IT%1d, SXI BULK)***************\n", 
        iter 
      ); 
    else 
      fprintf(RED_OUT, "\n******(IT%1d, SXI %1d)***************\n", 
        iter, sxi
      ); 
    fprintf(RED_OUT, "result:\n"); 
    red_print_graph(d); 
    return; 	
  } 
  else 
    return; 
} 
  /* print_sxi_stack() */  
#endif 



void	init_fxp_management() { 
  int	pi; 
  
/* The restriction is removed for new tctl model-checking that 
 * supports primed variables and event predicates. 
 */
/*
  if (   (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE)
      || ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_SIMULATE)
      || ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_BRANCHING_BISIM_CHECKING)
      || ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_BRANCHING_SIM_CHECKING)
      || !(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
      ) {
*/
    px = ((int *) malloc(PROCESS_COUNT * sizeof(int))) - 1;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      px[pi] = FLAG_ANY_XTION;
    }

    current_firable_xtion = ((int **) malloc(PROCESS_COUNT*sizeof(int *)))-1;
    fx_list = ((struct index_link_type **)
	      malloc(PROCESS_COUNT*sizeof(struct index_link_type *)))-1;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
/*
      fprintf(RED_OUT, "pi=%1d, PROCESS[%1d].firable_xtion_count=%1d\n", 
	      pi, pi, PROCESS[pi].firable_xtion_count
	      ); 
*/
      current_firable_xtion[pi] 
      = (int *) malloc(PROCESS[pi].firable_xtion_count * sizeof(int));
    }
/*
  }
*/
}
  /* init_fxp_management() */  
  


  

void	runtime_report(s, flag_print_xtion, dx)
	char		*s;
	int		flag_print_xtion;
	struct red_type	*dx;
{
  fprintf(RED_OUT, "\nI=%1d, SYNC_XTION %1d, %s:\n", ITERATION_COUNT, ITERATE_SXI, s);
  if (flag_print_xtion)
    if (ITERATE_SXI < SYNC_XTION_COUNT) {
      fprintf(RED_OUT, "I%1d, SYNC:%1d\n", ITERATION_COUNT, ITERATE_SXI);
      print_sync_xtion(ITERATE_SXI, SYNC_XTION);
    }
    else
      fprintf(RED_OUT, "I%1d, sync bulk\n", ITERATION_COUNT);
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_TIME)
    print_resources(s);
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_MEMORY)
    report_red_management();
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_RED_INTERMEDIATE)
    red_print_graph(dx);
}
  /* runtime_report() */




int	PI_ELIM_QFD_SYNC; 
  
struct red_type	*rec_eliminate_proc_qfd_sync(d)
     struct red_type	*d;
{
  int				ci, c1, c2;
  struct red_type		*child, *result;
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE 
      || VAR[d->var_index].PROC_INDEX > PI_ELIM_QFD_SYNC
      )
    return(d);

  ce = cache2_check_result_key(
    OP_ELIMINATE_PROC_QFD_SYNC, d, 
    (struct red_type *) PI_ELIM_QFD_SYNC
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_eliminate_proc_qfd_sync(bc->child);
      child = crd_lone_subtree(child, d->var_index, bc->upper_bound);
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_HRD: 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      hc = &(d->u.hrd.arc[ci]);
      child = hrd_lone_subtree(rec_eliminate_proc_qfd_sync(hc->child),
				  d->var_index, d->u.hrd.hrd_exp,
				  hc->ub_numerator, hc->ub_denominator
				  );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_proc_qfd_sync(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_proc_qfd_sync(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_POINTER 
	&& (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) 
	&& VAR[d->var_index].PROC_INDEX == PI_ELIM_QFD_SYNC 
	) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_eliminate_proc_qfd_sync(ic->child);
        result = red_bop(OR, result, child);
      }
    }
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_eliminate_proc_qfd_sync(ic->child);
        child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
        result = red_bop(OR, result, child);
      }
    }
  }

  return(ce->result = result); 
}
  /* rec_eliminate_proc_qfd_sync() */





struct red_type	*red_eliminate_proc_qfd_sync(d, pi) 
	struct red_type	*d; 
	int		pi; 
{
  struct red_type	*result;

  PI_ELIM_QFD_SYNC = pi; 
  
  result = rec_eliminate_proc_qfd_sync(d); 

  return(result); 
}
  /* red_eliminate_proc_qfd_sync() */ 
  
  
  

  
struct red_type	*rec_eliminate_all_qfd_sync(d)
     struct red_type	*d;
{
  int				ci, c1, c2;
  struct red_type		*child, *result;
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_ELIMINATE_ALL_QFD_SYNC, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    ce->result = bdd_new(d->var_index, 
      rec_eliminate_all_qfd_sync(d->u.bdd.zero_child), 
      rec_eliminate_all_qfd_sync(d->u.bdd.one_child)
    );
    return(ce->result); 
    break; 

  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_eliminate_all_qfd_sync(bc->child);
      child = crd_lone_subtree(child, d->var_index, bc->upper_bound);
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_HRD: 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      hc = &(d->u.hrd.arc[ci]);
      child = hrd_lone_subtree(rec_eliminate_all_qfd_sync(hc->child),
				  d->var_index, d->u.hrd.hrd_exp,
				  hc->ub_numerator, hc->ub_denominator
				  );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_all_qfd_sync(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_all_qfd_sync(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE
        || (   VAR[d->var_index].TYPE == TYPE_POINTER 
	    && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC) 
	)   ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_eliminate_all_qfd_sync(ic->child);
        result = red_bop(OR, result, child);
      }
    }
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_eliminate_all_qfd_sync(ic->child);
        child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
        result = red_bop(OR, result, child);
      }
    }
  }

  return(ce->result = result); 
}
  /* rec_eliminate_all_qfd_sync() */





struct red_type	*red_eliminate_all_qfd_sync(d) 
	struct red_type	*d; 
{
  return(rec_eliminate_all_qfd_sync(d)); 
}
  /* red_eliminate_all_qfd_sync() */ 
  
  
  

  
  



struct red_type	*red_add_clock_lower_bound(d)
	struct red_type	*d;
{
  int	ci, vi;

  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_TIMED:
    if (GSTATUS[INDEX_MODAL_CLOCK] & FLAG_MODAL_CLOCK) { 
      d = red_bop(AND, d, crd_atom(ZONE[0][MODAL_CLOCK], 0));
    } 
    if ((GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK) { 
      d = red_bop(AND, d, crd_atom(ZONE[0][ZENO_CLOCK], 0));
    } 
    for (ci = ZENO_CLOCK+2; ci < CLOCK_COUNT; ci=ci+2) {
      vi = CLOCK[ci];
      if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
	struct red_type	*inactive;
/*
	fprintf(RED_OUT, "add clock lowerbound to ci=%1d:vi=%1d:%s\n", ci, vi, VAR[vi].NAME);
*/
	inactive = red_bop(AND, d, VAR[vi].RED_INACTIVE);
	d = red_bop(AND, d, VAR[vi].RED_ACTIVE);
	d = red_bop(AND, d, crd_atom(ZONE[0][ci], 0));
	d = red_bop(OR, d, inactive);
      }
    }
    break;
  case FLAG_SYSTEM_HYBRID:
    if (GSTATUS[INDEX_MODAL_CLOCK] & FLAG_MODAL_CLOCK) { 
      vi = CLOCK[MODAL_CLOCK]; 
      d = hrd_one_constraint(d, VAR[vi].U.CLOCK.HE_LB, 0, 1);
    } 
    if ((GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK) { 
      vi = CLOCK[ZENO_CLOCK]; 
      d = hrd_one_constraint(d, VAR[vi].U.CLOCK.HE_LB, 0, 1);
    } 
    for (ci = ZENO_CLOCK+1; ci < CLOCK_COUNT; ci++) {
      vi = CLOCK[ci];
      if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
/*
        fprintf(RED_OUT, "add clock lowerbound to ci=%1d:vi=%1d:%s\n", ci, vi, VAR[vi].NAME);
*/
	d = hrd_one_constraint(d,VAR[vi].U.CLOCK.HE_LB, 0, 1);
      }
    }
  }
  return(d);
}
  /* red_add_clock_lower_bound() */




rec_get_process_firable_xtions(d)
     struct red_type	*d;
{
  int				ci, xi;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE || d->var_index > GXPI)
    return;

  ce = cache1_check_result_key(OP_GET_PROCESS_FIRABLE_XTIONS, d); 
  if (ce->result) 
    return; 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  if (d->var_index == GXPI) {
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) {
	fx_list[FXPI] = add_index(fx_list[FXPI], xi);
      }
    }
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_get_process_firable_xtions(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_get_process_firable_xtions(d->u.hrd.arc[ci].child);
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) 
      rec_get_process_firable_xtions(d->u.fdd.arc[ci].child); 
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) 
      rec_get_process_firable_xtions(d->u.dfdd.arc[ci].child); 
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) 
      rec_get_process_firable_xtions(d->u.ddd.arc[ci].child); 
  }
}
/* rec_get_process_firable_xtions() */




get_process_firable_xtions(pi, w) 
     int	pi, w; 
{
  struct index_link_type	*fxp; 

  FXPI = pi; 
  GXPI = variable_index[TYPE_XTION_INSTANCE][pi][0];
  fx_list[pi] = NULL; 
  cache1_clear(OP_GET_PROCESS_FIRABLE_XTIONS, OP_GET_PROCESS_FIRABLE_XTIONS); 
  rec_get_process_firable_xtions(RT[w]);

  /*
  fprintf(RED_OUT, "Caught for pi = %1d, with xi's= ", pi); 
  */
  for (firable_xtion_count = 0; 
       fx_list[pi];
       fxp = fx_list[pi], fx_list[pi] = fx_list[pi]->next_index_link, free(fxp)
       ) {
    /*
    fprintf(RED_OUT, " %1d", fx_list->index); 
    */
    firable_xtion[firable_xtion_count++] = fx_list[pi]->index;
  }
  /*
  fprintf(RED_OUT, "\nRT[w=%1d] for comparison:\n", w); 
  red_print_graph(RT[w]);
  */
}
/* get_process_firable_xtions() */ 






rec_get_all_firable_xtions(d)
     struct red_type	*d; 
{
  int				ci, xi, pi; 
  struct cache1_hash_entry_type	*ce; 

  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
      || d->var_index 
         > variable_index[TYPE_XTION_INSTANCE][PROCESS_COUNT][0] 
      ) 
    return;

  ce = cache1_check_result_key(OP_GET_ALL_FIRABLE_XTIONS, d); 
  if (ce->result) 
    return; 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    rec_get_all_firable_xtions(d->u.bdd.zero_child); 
    rec_get_all_firable_xtions(d->u.bdd.one_child);
    break; 

  case TYPE_XTION_INSTANCE:
    pi = VAR[d->var_index].PROC_INDEX;
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) {
	fx_list[pi] = add_index(fx_list[pi], xi);
      }
      rec_get_all_firable_xtions(d->u.ddd.arc[ci].child);
    }
    break;
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_get_all_firable_xtions(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_get_all_firable_xtions(d->u.hrd.arc[ci].child);
    break;
  case TYPE_LAZY_EXP: 
    rec_get_all_firable_xtions(d->u.lazy.false_child); 
    rec_get_all_firable_xtions(d->u.lazy.true_child);
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_get_all_firable_xtions(d->u.fdd.arc[ci].child);
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_get_all_firable_xtions(d->u.dfdd.arc[ci].child);
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_get_all_firable_xtions(d->u.ddd.arc[ci].child);
  }
}
/* rec_get_all_firable_xtions() */ 




int  cgafx = 0; 

void	get_all_firable_xtions(
  int	w, 
  int	flag_roles
) {
  int				pi, xc; 
  struct index_link_type	*fxp; 

  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    fx_list[pi] = NULL; 

  cache1_clear(OP_GET_ALL_FIRABLE_XTIONS, OP_GET_ALL_FIRABLE_XTIONS); 
  rec_get_all_firable_xtions(RT[w]);

  /*
  fprintf(RED_OUT, "Caught for pi = %1d, with xi's= ", pi); 
  */
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (xc = 0; 
         fx_list[pi]; 
         fxp = fx_list[pi], 
         fx_list[pi] = fx_list[pi]->next_index_link, 
         free(fxp)
         ) {
      #ifdef RED_DEBUG_FXP_MODE 
      fprintf(RED_OUT, 
        "\n****[cgafx=%1d]****************************\n", 
        ++cgafx
      ); 
      fprintf(RED_OUT, 
        "  pi=%1d, xc=%1d, copy fx_list[pi=%1d]->index=%1d \n", 
        pi, xc, pi, fx_list[pi]->index
      );
      fprintf(RED_OUT, 
        "    to current_firable_xtion[pi=%1d][xc=%1d]\n", 
        pi, xc 
      );
      fflush(RED_OUT); 
/*
      fprintf(RED_OUT, "count_get_all_firable_xtions = %1d\n", ++cgafx); 
      fflush(RED_OUT); 
      for (; cgafx == 16; ); 
*/      
      #endif 
      current_firable_xtion[pi][xc++] = fx_list[pi]->index; 
    }
    if (xc < PROCESS[pi].firable_xtion_count) 
      current_firable_xtion[pi][xc] = -1; 
  }
  /*
  fprintf(RED_OUT, "\nRT[w=%1d] for comparison:\n", w);
  red_print_graph(RT[w]);
  */
}
/* get_all_firable_xtions() */ 




int	execution_clock_activeness(w, xi, pi, flag_activeness)
     int	w, xi, pi, flag_activeness; 
{
  int			offset, vi;
  struct red_type	*conj; 

  if (   (!(GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY))
      && (XTION[xi].status & FLAG_XTION_CLOCK_INACTIVE) 
      && flag_activeness != FLAG_PARTIALLY_ACTIVE
      ) { 
    conj = NORM_FALSE; 
    for (offset = 0; offset < GLOBAL_COUNT[TYPE_CLOCK]; offset++) {
      vi = variable_index[TYPE_CLOCK][0][offset]; 
      conj = red_bop(OR, conj, red_bop(EXTRACT, RT[w], VAR[vi].RED_ACTIVE)); 
    }
    for (offset = 0; offset < LOCAL_COUNT[TYPE_CLOCK]; offset++) {
      vi = variable_index[TYPE_CLOCK][pi][offset]; 
      conj = red_bop(OR, conj, red_bop(EXTRACT, RT[w], VAR[vi].RED_ACTIVE)); 
    }
    
    if (conj == RT[w]) {
      if (flag_activeness == FLAG_CLOCK_INACTIVE) 
	return(FLAG_PARTIALLY_ACTIVE); 
      else if (flag_activeness == FLAG_CLOCK_UNKNOWN)
	return(FLAG_CLOCK_ACTIVE);
    }
    else if (conj == NORM_FALSE) {
      if (flag_activeness == FLAG_CLOCK_ACTIVE) 
	return(FLAG_PARTIALLY_ACTIVE); 
      else if (flag_activeness == FLAG_CLOCK_UNKNOWN)  
	return(FLAG_CLOCK_INACTIVE); 
    }
    else 
      return(FLAG_PARTIALLY_ACTIVE); 
  } 
  return(flag_activeness);
}
/* execution_clock_activeness() */ 










/*************************************************************
 *
 */
struct red_type	*red_assign_interval_bck(d, vi, lb, ub)
     struct red_type 	*d;
     int		vi, lb, ub;
{
  d = ddd_one_constraint(d, vi, lb, ub);
  d = red_variable_eliminate(d, vi);
  return(d);
}
/* red_assign_interval_bck() */











/*****************************************************************
 * The correctness of the routine is dependent on the fact that a transition
 can only be fired by a particular process in a synchronized transitions. 
 While this can be syntactically determined to some extent, the detection is 
 not implemented yet. 
 */ 


int	AS_LVI, AS_RVI, AS_COEFF, AS_OFFSET; 

// Note that this procedure may rely on an implicit references to two 
// static variables: REACHABLE, ITERATE_RESULT, and ITERATE_PI. 
// RT[REACHABLE] has something to do with the post-processing.  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
// 
// ITERATE_PI has something to do with the sync bulk evaluation. 
// In the sync bulk evaluation, each time we are done with a process, 
// we will eliminate the corresponding TYPE_XTION_INSTANCE variable 
// for that process.  
// As a result, if we come to postprocessing due to early detection of 
// postcondition evaluation termination throught red_stop conjunction, 
// it could be the case that we are not done with all the processes 
// and there might be some TYPE_XTION_INSTANCE left in the sync bulk image. 
// So we need to check whether ITERATE_PI is done with the last process. 
// Note that this ITERATE_PI parameter will always be used with the 
// assumption that the postprocessing in the sync bulk evaluation (with 
// sxt_ptr == NULL) will 
// always be called with some meaningful ITERATE_PI values.  
// And we make sure that it is in sync bulk mode before we check ITERATE_PI. 

int	count_check_dphil = 0; 

void	check_dphil(struct red_type *d) {
  struct red_type	*conj; 
  
  fprintf(RED_OUT, "\n%1d: dphil checking v%1d:%s=0\n", 
    ++count_check_dphil, 
    variable_index[TYPE_DISCRETE][5][1], 
    VAR[variable_index[TYPE_DISCRETE][5][1]].NAME
  ); 
  fflush(RED_OUT); 
  conj = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][5][1], 0, 0); 
/*
  conj = NORM_FALSE; 
  for (i = 4; i <= PROCESS_COUNT; i++) 
    conj = red_bop(OR, conj, ddd_atom(
      variable_index[TYPE_DISCRETE][i][0], 5, 5
    ) ); 
  for (i = 1; i <= 3; i++) { 
    conj = ddd_one_constraint(conj, 
      variable_index[TYPE_DISCRETE][i][0], 0, 0
    ); 
  } 
  for (i = 4; i <= 9; i++) { 
    conj = ddd_one_constraint(conj, 
      variable_index[TYPE_DISCRETE][i][0], 3, 3
    ); 
  }
*/
/*
  conj = ddd_one_constraint(conj, 
    variable_index[TYPE_DISCRETE][12][0], 3, 3
  ); 
*/
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, "\n >> caught!\n"); 
    red_print_graph(conj); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* check_dphil() */ 
  
  
  
int	count_reachable_fwd = 0; 
  
struct red_type	*red_postcondition_postprocessing(
  int				explore, 
  int				path, 
  struct red_type		*red_cur_reachable, // red_cur_reachable is the accummulated 
  struct red_type		*red_reachable, // red_cur_reachable is the accummulated 
	                                 // image of the current round of 
	                                 // postcondition evaluation. 
	                                 // If the postprocessing is done 
	                                 // for only one sync transition, 
	                                 // then we will not use this 
	                                 // parameter and we set 
	                                 // cur_reachable to FLAG_NO_CUR_REACHABLE_EXCLUSION.  
	                                 // Otherwise, it should always be 
	                                 // RESULT_ITERATE.  
  struct sync_xtion_type	*sxt_ptr,// This is a pointer to a 
	                               	 // sync_xtion in a sync_xtion table. 	
                                         // It is not really used for processing like the  
                                         // postprocessing for precondition.
  int				flag_post_processing // TYPE_FLASE for no 
) {
/*
  fprintf(RED_OUT, "=========================================\n"); 
  if (sxt_ptr) 
    fprintf(RED_OUT, 
      "IT:%1d, sxi=%1d, Entering postcondition postprocessing()\n", 
      ITERATION_COUNT, sxt_ptr->index 
    );
  else 
    fprintf(RED_OUT, 
      "IT:%1d, sxi=****, Entering postcondition postprocessing()\n", 
      ITERATION_COUNT  
    );
  red_print_graph(RT[explore]); 

  // check_dphil(RT[explore]); 
*/  
  if (!sxt_ptr) { 
    RT[explore] = red_pi_eliminate(RT[explore]); 
    RT[explore] = red_eliminate_all_qfd_sync(RT[explore]); 
  } 
  if (   (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) == FLAG_ROOT_OAPPROX 
      && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_SPEC_GAME) 
      	  >= FLAG_OAPPROX_SPEC_GAME_MAGNITUDE
      && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_MODL_GAME) 
      	  >= FLAG_OAPPROX_MODL_GAME_MAGNITUDE
      && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_ENVR_GAME) 
      	  >= FLAG_OAPPROX_ENVR_GAME_MAGNITUDE
      && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_GLOBAL_GAME) 
      	  >= FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE 
      ) {
    switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) { 
    case FLAG_OAPPROX_GAME_UNTIMED: 
      RT[explore] = red_through_all_invariance(explore);
      RT[explore] = inactive_variable_eliminate_noxtive(explore);
      RT[explore] = red_time_eliminate(RT[explore]);
      return(RT[explore]); 
    case FLAG_OAPPROX_GAME_MAGNITUDE: 
      reduce_symmetry(explore);

      if (   (   sxt_ptr == NULL 
              && (  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                  & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              )   )  
          || (   sxt_ptr 
              && (sxt_ptr->status & FLAG_XTION_FWD_ACTION_INV_INTERFERE)
          )   ) { 
        RT[explore] = red_through_all_invariance(explore);
        RT[explore] = inactive_variable_eliminate_noxtive(explore);
      } 

      if (flag_post_processing == FLAG_NO_POST_PROCESSING) 
        return(RT[explore]); 

      if (red_cur_reachable != NULL) 
        RT[explore] = red_bop(EXCLUDE, RT[explore], red_cur_reachable);
      RT[explore] = red_bop(EXCLUDE, RT[explore], red_reachable);
      if (CLOCK_COUNT + DENSE_COUNT) {
        RT[explore] = red_time_progress_noxtive_fwd(explore);
        RT[explore] = red_through_all_invariance(explore);
/*
        RT[explore] = red_abs_game(RT[explore], FLAG_OAPPROX_GAME_MAGNITUDE); 
*/
      }
/*
  print_resources("FILTERING=%1d, SXI=%1d, after abstract post processing\n", ITERATION_COUNT, ITERATE_SXI); 
*/
      break; 
  } }
  else { 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, before post processing\n", ITERATION_COUNT); 
      #endif 
    #endif 
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
      runtime_report("after sync execution", FLAG_PRINT_XTION, RT[explore]);

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, after pi elimination in post processing\n", ITERATION_COUNT); 
      #endif 
    #endif 
    if (   (   sxt_ptr == NULL 
            && (  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
            )   )  
        || (   sxt_ptr 
            && (sxt_ptr->status & FLAG_XTION_FWD_ACTION_INV_INTERFERE)
        )   ) {
      RT[explore] = red_bop(AND, RT[explore], RT[path]);
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
        runtime_report("after 1st global invariancing", FLAG_NO_PRINT_XTION, RT[explore]);
      switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
      case FLAG_NO_REDUCTION_INACTIVE: 
	break; 
      case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
        RT[explore] = inactive_variable_eliminate_noxtive(explore);
        break; 
      case FLAG_REDUCTION_INACTIVE: 
        RT[explore] = inactive_variable_eliminate(explore);
        break; 
      }
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
        runtime_report("after 1st global deactivating", FLAG_NO_PRINT_XTION, RT[explore]);
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, after 1st inactivating\n", ITERATION_COUNT); 
      #endif 
    #endif 
    RT[explore] = red_subsume(RT[explore]);
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
      runtime_report("after reduction", FLAG_NO_PRINT_XTION, RT[explore]);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, after 1st reduction\n", ITERATION_COUNT); 
      #endif 
    #endif 
    
    if (flag_post_processing == FLAG_NO_POST_PROCESSING) 
      return(RT[explore]); 

    if (red_cur_reachable != NULL) 
      RT[explore] = red_bop(EXCLUDE, RT[explore], red_cur_reachable);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, after local exclusion\n", ITERATION_COUNT); 
      #endif 
    #endif 
    
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
      runtime_report("after exclusion from cur_reachable", FLAG_NO_PRINT_XTION, RT[explore]);
    RT[explore] = red_bop(EXCLUDE, RT[explore], red_reachable);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, after global exclusion\n", ITERATION_COUNT); 
      #endif 
    #endif 
    
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
      runtime_report("after exclusion from REACHABLE", FLAG_NO_PRINT_XTION, RT[explore]);
    reduce_symmetry(explore);

    if (CLOCK_COUNT > 1 || DENSE_COUNT > 0) {
      if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
          && (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS)
          && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING)
          ) {
        int consistent;

        RT[consistent = RT_TOP++] = red_bop( 
          AND, RT[explore], RT[PARAMETER_COMPLEMENT] 
        ); 
        RT[consistent] = hybrid_eliminate_inconsistency_DOWNWARD( 
          consistent 
        );
        RT[explore] = RT[consistent]; 
        RT_TOP--; /* consistent */ 
/*
      print_resources("after parametric analysis overhead");
      probe(PROBE_PRERISK2, "WEAKEST: after parameter exclusion", RT[explore]);
      report_status("After parameter exclusion");
*/
      }
    }
  /* We add this option for the benefit of the redlib users. 
   * The users may just want to see post condition without time progress. 
   */ 
    if (!(GSTATUS[INDEX_TIME_PROGRESS] & FLAG_TIME_PROGRESS)) 
      return(RT[explore]); 
    
    if (CLOCK_COUNT + DENSE_COUNT) {
      RT[explore] = red_time_progress_fwd(explore, path);
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
        runtime_report("after saturation", FLAG_NO_PRINT_XTION, RT[explore]);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        print_cpu_time("FW %d, after time progress\n", ITERATION_COUNT); 
        #endif 
      #endif 
/*
      print_resources("ITERATION:%1d, new RT[sxi] after saturation", ITERATION_COUNT);
      red_print_graph(RT[explore]);
      probe(BENCHMARK_PCD5a, "after saturation", RT[explore]);
      report_red_management();
*/
      RT[explore] = red_bop(AND, RT[explore], RT[path]);
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
        runtime_report("after 2nd global invariancing", FLAG_NO_PRINT_XTION, RT[explore]);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        print_cpu_time("FW %d, after 2nd global invariancing\n", ITERATION_COUNT); 
        #endif 
      #endif 
/* 
      print_resources("ITERATION:%1d, new RT[sxi] after 2nd global invariancing", ITERATION_COUNT);
      red_print_graph(RT[explore]);
      probe(BENCHMARK_PCD5a, "after 2nd global invariancing", RT[explore]);
      report_red_management();
*/
      RT[explore] = red_hull_normalize(explore); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        print_cpu_time("FW %d, after normalization\n", ITERATION_COUNT); 
        #endif 
      #endif 
      
      if ((GSTATUS[INDEX_APPROX] & MASK_OAPPROX) == FLAG_OAPPROX_GAME_DIAGONAL) { 
        RT[explore] = red_abs_game(RT[explore], FLAG_OAPPROX_GAME_DIAGONAL); 
      } 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        print_cpu_time("FW %d, after abs game\n", ITERATION_COUNT);
        #endif  
      #endif 
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING)
        runtime_report("after normalization", FLAG_NO_PRINT_XTION, RT[explore]);
/*
      print_resources("IT:%1d, after normalization", ITERATION_COUNT);
      red_print_graph(RT[explore]);
      probe(BENCHMARK_PCD5a, "after normalization", RT[explore]);
      report_red_management();
*/
    }
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING) {
      print_resources("It %1d; SXI=%1d; Leaving sync_bulk_xtion()", 
        ITERATION_COUNT, ITERATE_SXI
      );
      if (sxt_ptr != NULL)
        print_sync_xtion_ptr(sxt_ptr);
      fprintf(RED_OUT, "\n");
      red_print_graph(RT[explore]);
    }
/*
  probe(PROBE_PRERISK2, "test the risk after red-hulling the sync bulk execution", RT[explore]);
      red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  }
/*
  if (ITERATION_COUNT == 2) { 
    if (sxt_ptr) 
      fprintf(RED_OUT, 
	    "IT:%1d, sxi=%1d, Leaving postcondition postprocessing()\n", 
	    ITERATION_COUNT, sxt_ptr->index 
	    );
    else 
      fprintf(RED_OUT, 
	    "IT:%1d, sxi=****, Leaving postcondition postprocessing()\n", 
	    ITERATION_COUNT 
	    );
    red_print_graph(RT[explore]); 
  }
*/
  garbage_collect(FLAG_GC_SILENT);

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
    fprintf(RED_OUT, "\nAt the end of red_postcondition_postprocessing().\n"); 
    // check_dphil(RT[explore]); 
    #endif 
  #endif 
  
  return(RT[explore]);
}
  /* red_postcondition_postprocessing() */



// Note that this procedure works on REACHABLE as a global side-effect. 
int	goal_check_fwd(
  struct reachable_return_type	*rr,  
  int				explore, 
  struct red_type 		*red_cur_reachable, 
  int				goal
) {
  int	tmp; 

  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
      && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_REACHABLE_COMPLEMENT)
      ) {
    struct red_type	*d_tmp;
/*
    probe(PROBE_PRERISK1, "spec reach complement", RT[REACHABLE_COMPLEMENT]);
    probe(PROBE_PRERISK1, "spec rt explore", RT[explore]);
*/
    d_tmp = red_complement(RT[explore]);
/*
    probe(PROBE_PRERISK1, "spec rt explore complement", d_tmp);
*/
    RT[REACHABLE_COMPLEMENT] = red_bop(AND, RT[REACHABLE_COMPLEMENT], d_tmp);
/*
    probe(PROBE_PRERISK1, "spec new reach complement", RT[REACHABLE_COMPLEMENT]);
*/
  }
//  if ((GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) == FLAG_ROOT_NOAPPROX) {
//  We remove the last line to enable the research for interpolation and 
//  CEGAR related research. 

  switch (GSTATUS[INDEX_TASK] & MASK_TASK) { 
  case TASK_ZENO: 
  case TASK_DEADLOCK: 
  case TASK_RISK: 
  case TASK_SAFETY: 
  case TASK_GOAL: 
    RT[tmp = RT_TOP++] = red_bop(AND, RT[explore], RT[goal]);
    if (   RT[tmp] != NORM_FALSE
        && ((CLOCK_COUNT+DENSE_COUNT <= 1) || (red_hull_test_emptiness(tmp) != NORM_FALSE))
	) {
/*
      fprintf(RED_OUT, "\nGoal state reachable!\n");
      red_print_graph(RT[tmp]);
*/
//        fxp_update_coverage();

      rr->status = rr->status | FLAG_RESULT_EARLY_REACHED;  
      if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
          && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)
          ) {
	add_counter_path(
	  locate_one_instance(RT[tmp], NULL, 0), 
	  ITERATION_COUNT
	);
        rr->status = rr->status | FLAG_COUNTER_EXAMPLE_GENERATED; 
        rr->counter_example_length = ITERATION_COUNT; 
        rr->counter_example = generate_counter_example_fwd(); 
      }
      if (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)) { 
	fflush(RED_OUT);
	RT_TOP--; /* tmp */ 
        rr->iteration_count = ITERATION_COUNT; 
        RT[REACHABLE] = red_bop(OR, red_cur_reachable, RT[REACHABLE]); 
        RT[REACHABLE] = red_bop(OR, RT[REACHABLE], RT[explore]); 
        rr->reachability = RT[REACHABLE]; 
        return(FLAG_RESULT_EARLY_REACHED); 
      }
      else if (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) {
        if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
	  int	consistent;

	  RT[tmp] = hybrid_parameter_extract(RT[tmp]); 
	  RT[consistent = RT_TOP++] = red_bop( 
	    AND, RT[tmp], RT[PARAMETER_COMPLEMENT] 
	  ); 
	  RT[consistent] = hybrid_eliminate_inconsistency_DOWNWARD(consistent);
	  RT[tmp] = RT[consistent];
	  
	  RT_TOP--; /* consistent */
	  RT[PARAMETER_COMPLEMENT] = red_bop(AND, RT[PARAMETER_COMPLEMENT],
	    red_complement(RT[tmp])
	  );
/*
          fprintf(RED_OUT, "\n%%%%%%%%%%%%%[New reachable state]%%%%%%%%%%%%%%%%%\n");
	  red_print_graph(RT[tmp]);
	  fprintf(RED_OUT, "new parameter restriction complement:\n");
	  red_print_graph(RT[PARAMETER_COMPLEMENT]);
*/
	}
	else {
	  fprintf(RED_OUT, "Woops! parametric analysis for timed systems are not supported!\n");
	  exit(0);
	} 
      }
    }
    RT_TOP--; /* tmp */
  }

  return(FLAG_GOAL_NORMAL);
}
  /* goal_check_fwd() */




struct red_type	*red_postcondition_stream_sync_bulk(
  int	src_sxi_bulk 
) {
  int			cur_xi, cur_pi, 
			urgent, pi, ixi, ci, fxi, flag, 
			result;
  struct red_type	*conj;

  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) { 
    if (!(  GSTATUS[INDEX_GAME_ROLES] 
          & (PROCESS[ITERATE_PI].status & MASK_GAME_ROLES)
        ) ) 
      continue; 
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    if (px[ITERATE_PI] != FLAG_ANY_XTION) {
      ITERATE_XI = px[ITERATE_PI];
      RT[cur_pi] = red_postcondition_stream(
	RT[src_sxi_bulk],  
	ITERATE_PI, ITERATE_XI
      ); 
    }
    else for (ixi = 0;
	         ixi < PROCESS[ITERATE_PI].firable_xtion_count
	      && current_firable_xtion[ITERATE_PI][ixi] != -1;
	      ixi++
	      ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      RT[cur_pi] = red_bop(OR, RT[cur_pi], 
        red_postcondition_stream(
	  RT[src_sxi_bulk],  
	  ITERATE_PI, ITERATE_XI  
      ) ); 
    }

    RT[src_sxi_bulk] = RT[cur_pi];
    RT_TOP--; /* cur_pi */ 
    RT[src_sxi_bulk] = red_subsume(RT[src_sxi_bulk]);
  }
  return(RT[src_sxi_bulk]);
}
/* red_postcondition_stream_sync_bulk() */



// Note that this procedure may rely on an implicit reference to 
// RT[REACAHBLE] to do the post-processing (by calling 
// red_postcondition_postprocessing).  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
int	count_sync_bulk_specific = 0; 

struct red_type	*red_postcondition_sync_bulk_specific(
  struct reachable_return_type	*rr,  
  int				explore, 
  int				path, 
  int				goal, 
  struct red_type		*red_cur_reachable, 

  struct red_type		*red_reachable, 
  int				pi, 
  int				xi, 
  int				fxi, 
  int				final_result, // this is for the side-effect

  int				flag_post_processing, // TYPE_FALSE for no
  int				*result_status_ptr 
) {
  int			cur_xi, stop; 
  struct red_type	*conj; 
  
  RT[cur_xi = RT_TOP++] 
  = red_bop(EXTRACT, RT[explore], ddd_atom(fxi, xi, xi));
  /*
    fprintf(RED_OUT, "\n===FW %1d; ITERATE_PI=%1d; ITERATE_XI=%1d;=========================\n",
      ITERATION_COUNT, ITERATE_PI, ITERATE_XI
    );
    print_xtion_line(ITERATE_XI, ITERATE_PI);
    fprintf(RED_OUT, "\n");
    print_resources("before xtion");
    report_red_management();
    if (ITERATION_COUNT == 6 && ITERATE_PI == 3 && ITERATE_XI == 13)
      probe(PROBE_PRERISK1, "before xtion", RT[cur_xi]);
    red_print_graph(RT[cur_xi]);
   */
  if (RT[cur_xi] == NORM_FALSE) {
    RT_TOP--; // cur_xi 
    *result_status_ptr = FLAG_GOAL_NORMAL;
    return(NORM_FALSE); 
  }
 /*
    probe(PROBE_PRERISK1, "after triggering", RT[cur_xi]);
    print_resources("after triggering");
    red_print_graph(RT[cur_xi]);
  */
/*
    if (!(GSTATUS[INDEX_XTION_INSTANCE] & FLAG_XTION_INSTANCE_MAINTAIN)) 
      RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi);
*/
  if (ITERATE_XI) { 
    RT[cur_xi] = red_general_statement_fwd(
      cur_xi, 
      pi, 
      XTION[xi].statement, 
      GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
      FLAG_ACTION_DELAYED_EVAL  
    );
    // check_dphil(RT[cur_xi]); 
    if (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
          & FLAG_BULK_TRIGGER_ACTION_INTERFERE
        ) ) {
      if (valid_mode_index(XTION[xi].dst_mode_index)) { 
        RT[cur_xi] = red_delayed_eval( 
          MODE[XTION[xi].dst_mode_index].invariance[pi].red, 
          pi, RT[cur_xi]
        );
      }
      /*
	print_resources("after process invariancing");
	report_red_management();
	red_print_graph(RT[cur_xi]);
	if (ITERATION_COUNT == 6 && ITERATE_PI == 3 && ITERATE_XI == 13)
	  probe(PROBE_PRERISK1, "after process invariancing", RT[cur_xi]);
	probe(PROBE_PRERISK1, "after process invariancing", RT[cur_xi]);
       */
      if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC) 
        RT[cur_xi] = red_eliminate_proc_qfd_sync(RT[cur_xi], pi); 
	/*
          if (ITERATION_COUNT == 6 && ITERATE_PI == 3 && ITERATE_XI == 13)
            probe(PROBE_PRERISK1, "after xtion", RT[cur_xi]);
	  print_resources("after actions");
	  report_red_management();
	  red_print_graph(RT[cur_xi]);
	  probe(PROBE_PRERISK1, "after xtions", RT[cur_xi]);
         */

      switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
      case FLAG_NO_REDUCTION_INACTIVE: 
	break; 
      case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
        RT[cur_xi] = process_inactive_variable_eliminate_noxtive(
          cur_xi, ITERATE_PI
        );
        break; 
      case FLAG_REDUCTION_INACTIVE: 
        RT[cur_xi] = process_inactive_variable_eliminate(
          cur_xi, ITERATE_PI
        );
        break; 
      }
      /*
        print_resources("FW %1d, after eliminating process inactives", 
          ITERATION_COUNT
        );
        report_red_management();
        red_print_graph(RT[cur_xi]);
        if (ITERATION_COUNT == 6 && ITERATE_PI == 3 && ITERATE_XI == 13)
          probe(PROBE_PRERISK1, "after process inactives", RT[cur_xi]);
          probe(PROBE_PRERISK1, "after process inactive eliminations", RT[cur_xi]);
       */
    }
    /*
      print_resources("FW %1d, after reduction", ITERATION_COUNT);
      report_red_management();
      probe(PROBE_PRERISK1, "test after reductions", RT[cur_xi]);
      red_print_graph(RT[cur_xi]);
     */

    conj = red_bop(EXTRACT, RT[cur_xi], PROCESS[pi].red_stop);
    if (conj != NORM_FALSE) { 
      RT[cur_xi] = red_bop(SUBTRACT, RT[cur_xi], PROCESS[pi].red_stop);
      RT[stop = RT_TOP++] = conj; 

      RT[stop] = red_postcondition_postprocessing(
        stop, 
        path, 
        red_cur_reachable, 
        red_reachable, 
        NULL, // There is no sync_xtion pointer here. 
        flag_post_processing 
      );
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        fprintf(RED_OUT, "FW %1d, sync bulk specific %1d, after post processing:\n", 
          ITERATION_COUNT, count_sync_bulk_specific++
        ); 
        red_print_graph(RT[stop]);
        #endif 
      #endif 
      if (   (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)) 
          && rr 
          && goal_check_fwd(rr, stop, red_cur_reachable, goal) 
             == FLAG_GOAL_EARLY_REACHED
          ) {
        RT_TOP = RT_TOP -2; /* stop, cur_xi */
        *result_status_ptr = FLAG_GOAL_EARLY_REACHED;
        
        return(RT[stop]); 
      }
      else {
        RT_TOP--; // stop 
        RT[final_result] = red_bop(OR, RT[final_result], RT[stop]); 
      }
    }
  }
/*
    print_resources("after unioning");
    report_red_management();
*/
  RT_TOP--; // cur_xi 
  garbage_collect(FLAG_GC_SILENT);
  *result_status_ptr = FLAG_GOAL_NORMAL; 
  
  return(RT[cur_xi]); 
}
  /* red_postcondition_sync_bulk_specific() */ 
  
  
  
// This procedure calculates the postcondition from states in RT[explore]
// through only synchronous transitions in RT[sxi_bulk]. 
// The procedure has a side-effect on RT[RESULT_ITERATE].  
// In fact, the post-condition is to be saved with the 
// the value in RT[RESULT_ITERATE].  
// Flag_time tells us to do the time-progress calculation or not. 
//
// Note that this procedure may rely on an implicit reference to 
// RT[REACAHBLE] to do the post-processing (by calling 
// red_postcondition_postprocessing).  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
struct red_type	*red_postcondition_sync_bulk(
  struct reachable_return_type	*rr,  
  int				src, 
  int				path, // RT[path] is an invariance condition for reachable states
  int				goal, // RT[goal] is the goal for reachability 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  int				sxi_bulk, // RT[sxi_bulk] is the bulk representation of the 
                          		// sync transitions.  
  int				flag_post_processing, 
  int				*result_status_ptr  
) {
  int			cur_xi, cur_pi, result, 
			urgent, pi, ixi, ci, fxi, flag;
  struct red_type	*conj;

  RT[src] = red_bop(AND, RT[src], RT[sxi_bulk]);
  RT[src] = red_delayed_eval(RT[src], PROC_GLOBAL, RT[src]);
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
    fprintf(RED_OUT, 
      "FW %1d, Entering postconditioning sync bulk", ITERATION_COUNT
    );
//    report_red_management();
    red_print_graph(RT[src]);
    #endif 
  #endif 
  // check_dphil(RT[src]); 
  
/*
  switch (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE) {
  case FLAG_TRIGGER_COVERAGE:
  case FLAG_DISCRETE_TRIGGER_COVERAGE:
  case FLAG_ARC_COVERAGE: 
  case FLAG_ALL_COVERAGE: 
    RT[TRIGGER_COVERAGE] = red_bop(OR, RT[TRIGGER_COVERAGE], RT[src]);
    break;
  }
  print_resources("after global xi restrictions in sync bulk");
  report_red_management();

  fprintf(RED_OUT, 
    "\nFW %1d, sync bulk, RT[src=%1d]:\n", 
    ITERATION_COUNT, src
  ); 
  red_print_graph(RT[src]);
*/
  get_all_firable_xtions(src, MASK_GAME_ROLES);
  count_sync_bulk_specific = 0; 
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) { 
    if (!(  GSTATUS[INDEX_GAME_ROLES] 
          & (PROCESS[ITERATE_PI].status & MASK_GAME_ROLES)
        ) ) 
      continue; 
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    if (px[ITERATE_PI] != FLAG_ANY_XTION) {
      ITERATE_XI = px[ITERATE_PI];
      conj = red_postcondition_sync_bulk_specific(
	rr, 
	src, path, goal, 
	red_cur_reachable, 
	
	red_reachable, 
	ITERATE_PI, ITERATE_XI, 
	fxi, 
	result, 
	
	flag_post_processing, 
	&flag  
      ); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        fprintf(RED_OUT, "\nFW %1d, pi=%1d, specific=%1d, RT[RESULT_ITERATE]=%x\n", 
      	      ITERATION_COUNT, ITERATE_PI, px[ITERATE_PI], RT[RESULT_ITERATE]
      	      ); 
        fflush(RED_OUT); 
        #endif 
      #endif 
      if (flag == FLAG_GOAL_EARLY_REACHED) {
      	RT_TOP--; /* cur_pi */ 
      	*result_status_ptr = flag; 
      	RT_TOP--; // result 
      	
        return(conj); 
      } 
      RT[cur_pi] = red_bop(OR, RT[cur_pi], conj); 
    }
    else for (ixi = 0;
	         ixi < PROCESS[ITERATE_PI].firable_xtion_count
	      && current_firable_xtion[ITERATE_PI][ixi] != -1;
	      ixi++
	      ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      conj = red_postcondition_sync_bulk_specific(
	rr, 
	src, path, goal, 
	red_cur_reachable, 
	
	red_reachable, 
	ITERATE_PI, ITERATE_XI, 
	fxi, 
	result, 
	
	flag_post_processing, 
	&flag  
      ); 
/*
      fprintf(RED_OUT, "\nFW %1d, pi=%1d, no-specific xi=%1d, RT[RESULT_ITERATE]=%x\n", 
              ITERATION_COUNT, ITERATE_PI, ITERATE_XI, RT[RESULT_ITERATE]
              ); 
      fflush(RED_OUT); 
*/
      if (flag == FLAG_GOAL_EARLY_REACHED) {
      	RT_TOP--; /* cur_pi */ 
      	RT_TOP--; // result 
        *result_status_ptr = flag; 
        
        return(conj); 
      } 
      RT[cur_pi] = red_bop(OR, RT[cur_pi], conj); 
    }

    RT[src] = RT[cur_pi];
    RT_TOP--; /* cur_pi */ 
    RT[src] = red_subsume(RT[src]);
/*
    fprintf(RED_OUT, 
      "\nFW %1d, after sync bulk PI=%1d, RT[src=%1d]:\n", 
      ITERATION_COUNT, ITERATE_PI, src 
    ); 
    red_print_graph(RT[src]);
    print_resources("after reduction");
    report_red_management();
*/

  }
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
    fprintf(RED_OUT, 
      "FW %1d, Leaving postconditioning sync bulk", ITERATION_COUNT
    );
//    report_red_management();
    red_print_graph(RT[src]);
    #endif 
  #endif 
  *result_status_ptr = FLAG_GOAL_NORMAL; 
  RT_TOP--; // result 
  
  return (RT[result]);
}
/* red_postcondition_sync_bulk() */






  
// This procedure calculates the postcondition from states in RT[explore]
// through only synchronous transitions in table SYNC_XTION[]. 
// The procedure has a side-effect on RT[RESULT_ITERATE].  
// In fact, the post-condition is to be saved with the 
// the value in RT[RESULT_ITERATE].  
// The procedure also allows for partial execution by certain roles 
// in a simulation-checking and bisimulation-checking.  
// 
// Note that if sync_xtion is SIM_SYNC_XTION, 
// then flag_roles should be MASK_GAME_ROLES for efficiencey consideration. 
// The reason is that we need to check duplication in SIM_SYNC_XTION 
// with quantification over the parties not included in flag_roles.  
// Previously, we do this by choosing a representative for each group of 
// sync xtions with the same flag_roles like SPCR+ENVR.  
// Now as long as we always execute cases like SPCR+ENVR with 
// SYNC_XTION and the original sync_bulk, then we don't have to worry 
// about the representative things. 
// Since no direct or indirect syncs between the SPCR and DSCR are possible.  
//
// Note that this procedure may rely on an implicit reference to 
// RT[REACAHBLE] to do the post-processing (by calling 
// red_postcondition_postprocessing.  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
struct red_type	*red_postcondition_sync_ITERATIVE(
  struct reachable_return_type	*rr,  
  int				src, // RT[src] describes the source state. 
  int				path, // RT[path] is an invariance condition for reachable states
  int				goal, // RT[goal] is the goal for reachability 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion, 
  int				sync_xtion_count, 
  int				flag_post_processing, 
  int				*result_status_ptr 
) {
  int			sxi, ipi, urgent, ixi, fxi, flag, 
			result, local_reachable;
  struct red_type	*conj, *trigger;
/*
  print_cpu_time("\n\n*****(FW %d, postconditioning sync ENUMERATIVE)**********************************\n",
  	  ITERATION_COUNT
   	  );
  print_resources("Entering postconditioning sync ITERATIVE");
  report_red_management();
  red_print_graph(RT[explore]);
  */
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[local_reachable = RT_TOP++] = red_cur_reachable; 
  for (ITERATE_SXI = 0; ITERATE_SXI < sync_xtion_count; ITERATE_SXI++) {
    // The following if-statements look to reduce the overhead of 
    // partial execution by a role with the environment. 
    // If we are now evaluating for spec+envr only, 
    // there can be many sync xtions that have the same SPEC+ENVR part 
    // but with different DSCR part. 
    // Since the DSCR does not really execute, we only have to execute 
    // one representative in this group of sync xtions. 
    if (  sync_xtion[ITERATE_SXI].status 
        & MASK_GAME_ROLES 
        & ~(GSTATUS[INDEX_GAME_ROLES])
        ) { 
      continue; 
    } 

/* // THIS IS FOR DEBUGGING A TRACE. 
    if (!check_trace(ITERATION_COUNT, ITERATE_SXI)) 
      continue; 
*/
    // If we are now evaluating for dscr+envr only, 
    // there can be many sync xtions that have the same DSCR+ENVR part 
    // but with different SPCR part. 
    // Since the SPCR does not really execute, we only have to execute 
    // one representative in this group of sync xtions. 

    RT[sxi = RT_TOP++] = RT[src]; 
/*
      	fprintf(RED_OUT, 
      	  "FW %1d, sxi=%1d, RT[sxi=%1d], after triggering:\n", 
          ITERATION_COUNT, ITERATE_SXI, sxi, ITERATE_PI
        ); 
        print_sync_xtion_lines(ITERATE_SXI, SYNC_XTION); 
        red_print_graph(RT[sxi]);
*/
    RT[sxi] = red_delayed_eval(
      sync_xtion[ITERATE_SXI].red_trigger, 
      PROC_GLOBAL, 
      RT[sxi]
    ); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
//      if (ITERATION_COUNT == 7/* && ITERATE_SXI == 20*/) { 
      	fprintf(RED_OUT, 
      	  "FW %1d, sxi=%1d, RT[sxi=%1d], after triggering:\n", 
          ITERATION_COUNT, ITERATE_SXI, sxi, ITERATE_PI
        ); 
        print_sync_xtion_lines(ITERATE_SXI, SYNC_XTION); 
        red_print_graph(RT[sxi]);
//      }
      #endif 
    #endif 
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("after triggering execution", FLAG_PRINT_XTION, RT[sxi]);

/*
      print_resources("after red_triggering");
      report_red_management();
      probe(PROBE_PRERISK1, "before process actions", RT[sxi]);
    red_print_graph(RT[sxi]);
    report_red_management();
*/
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--; /* sxi */ 
      continue;
    }

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT, "FW %1d, sxi=%1d, RT[sxi=%1d], before statements:\n", 
        ITERATION_COUNT, ITERATE_SXI, sxi
      ); 
      red_print_graph(RT[sxi]);
      #endif 
    #endif 

    for (ipi = 0; ipi < sync_xtion[ITERATE_SXI].party_count; ipi++) {
      ITERATE_PI = sync_xtion[ITERATE_SXI].party[ipi].proc;
      if (!(  PROCESS[ITERATE_PI].status 
	    & GSTATUS[INDEX_GAME_ROLES] 
	    & MASK_GAME_ROLES
	    )) 
        continue;  
      ITERATE_XI = sync_xtion[ITERATE_SXI].party[ipi].xtion;
      RT[sxi] = red_general_statement_fwd(
	sxi, 
	ITERATE_PI, 
	sync_xtion[ITERATE_SXI].party[ipi].statement, 
	GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
	FLAG_ACTION_DELAYED_EVAL  
      );
      // check_dphil(RT[sxi]); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        if (ITERATION_COUNT == 7/* && ITERATE_SXI == 20*/) { 
          fprintf(RED_OUT, "FW %1d, sxi=%1d, RT[sxi=%1d], after statement for pi=%1d:\n", 
            ITERATION_COUNT, ITERATE_SXI, sxi, ITERATE_PI
          ); 
          red_print_graph(RT[sxi]);
        }
        #endif 
      #endif 
      if (XTION[ITERATE_XI].status & FLAG_XTION_QUANTIFIED_SYNC) {
        RT[sxi] = red_eliminate_proc_qfd_sync(RT[sxi], ITERATE_PI); 
      }
      if (!(  SYNC_XTION[ITERATE_SXI].status 
            & FLAG_XTION_FWD_ACTION_INV_INTERFERE
          ) ) {
        if (valid_mode_index(XTION[ITERATE_XI].dst_mode_index)) { 
	  RT[sxi] = red_bop(AND, RT[sxi], 
	    MODE[XTION[ITERATE_XI].dst_mode_index].invariance[ITERATE_PI].red
	  );
	}
        switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
	case FLAG_NO_REDUCTION_INACTIVE: 
	  break; 
        case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
          RT[sxi] = process_inactive_variable_eliminate_noxtive(
            sxi, ITERATE_PI
          );
          break; 
        case FLAG_REDUCTION_INACTIVE: 
          RT[sxi] = process_inactive_variable_eliminate(
            sxi, ITERATE_PI
          );
          break; 
	}
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
          fprintf(RED_OUT, "FW %1d, sxi=%1d, RT[sxi=%1d], after process inactive for pi=%1d:\n", 
            ITERATION_COUNT, ITERATE_SXI, sxi, ITERATE_PI
          ); 
          red_print_graph(RT[sxi]);
	  #endif 
	#endif 
      }
    }

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT, 
        "\n***************************\nFW %1d, sxi=%1d, RT[sxi=%1d], before post processing:\n", 
        ITERATION_COUNT, ITERATE_SXI, sxi 
      ); 
      print_sync_xtion_lines(ITERATE_SXI, SYNC_XTION); 
      red_print_graph(RT[sxi]);
      #endif 
    #endif 
    RT[sxi] = red_postcondition_postprocessing(
      sxi, path, RT[local_reachable], red_reachable, 
      &(sync_xtion[ITERATE_SXI]), 
      flag_post_processing  
    );

//    check_print_trace(ITERATION_COUNT, ITERATE_SXI, RT[sxi]); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT, "FW %1d, sxi=%1d, RT[sxi=%1d], after post processing:\n", 
        ITERATION_COUNT, ITERATE_SXI, sxi 
      ); 
      red_print_graph(/* red_bop(AND, red_tmp_goal, */ RT[sxi]/*)*/);
      #endif 
    #endif 
    
    if (   rr 
        && goal_check_fwd(rr, sxi, RT[local_reachable], goal) 
           == FLAG_GOAL_EARLY_REACHED
        ) {
      RT_TOP = RT_TOP-3; /* sxi, local_reachable, result */
      *result_status_ptr = FLAG_GOAL_EARLY_REACHED;
      return(RT[sxi]); 
    } 
    RT[result] = red_bop(OR, RT[result], RT[sxi]);
    RT[local_reachable] = red_bop(OR, RT[local_reachable], RT[sxi]);
    RT_TOP--; /* sxi */
  }
  RT[result] = red_subsume(RT[result]);
  RT_TOP = RT_TOP-2; // local_reachable, result 
  *result_status_ptr = FLAG_GOAL_NORMAL;
  
  return(RT[result]); 
}
/* red_postcondition_sync_ITERATIVE() */





// This procedure returns the postcondition from states in RT[explore]
// through only synchronous transitions sync_xtion_index 
// in table SYNC_XTION[]. 
struct red_type	*red_postcondition_sync_SPECIFIC(
  int				explore, /* RT[explore] is the source state description for the 
               		                  * postcondition calculation. 
                           	          */
  int				path, // RT[path] is an invariance condition for reachable states
                	              // We leave it to the users to 
                	              // make sure that RT[path] 
                	              // is compatible with flag_roles. 
                	              // That is, RT[path] does not 
                	              // contain constraints on roles 
                	              // other than those specified in 
                	              // flag_roles. 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion_ptr, /* The postcondition will be done for 
                                    		* sync transition sync_xtion_index. 
                                    		*/
  int				flag_post_processing
) {
  int			sxi, ipi, urgent, ixi, fxi, flag;
  struct red_type	*conj;
/*
  print_resources("Entering postconditioning sync ITERATIVE");
  report_red_management();
  red_print_graph(RT[explore]);
  fprintf(RED_OUT, "\n\n*****(FW %1d, postconditioning sync ENUMERATIVE)**********************************\n",
  	  ITERATION_COUNT
   	  );
  */ 
  if (  sync_xtion_ptr->status 
      & MASK_GAME_ROLES 
      & ~(GSTATUS[INDEX_GAME_ROLES])
      ) 
    return(NORM_FALSE);

  ITERATE_SXI = sync_xtion_ptr->index;
/*
    fprintf(RED_OUT, "\nFW %1d, SXI=%1d, before xi restrictions\n", ITERATION_COUNT, ITERATE_SXI);
    print_resources("before global xi restrictions in sync ENUMERATIVE", ITERATION_COUNT);
    print_sync_xtion_ptr(sync_xtion_ptr);
*/
  RT[sxi = RT_TOP++] = RT[explore];
/*
    if (ITERATION_COUNT == 8 && ITERATE_SXI == 1) {
      fprintf(RED_OUT, "\nITERATION:%1d, new RT[sxi] to be processed\n", ITERATION_COUNT);
      probe(PROBE_PRERISK2, "before triggering", RT[sxi]);
    }
*/
  RT[sxi] = red_delayed_eval(
    sync_xtion_ptr->red_trigger, 
    PROC_GLOBAL, 
    RT[sxi]
  );
/*
      print_resources("after red_triggering");
      report_red_management();
      probe(PROBE_PRERISK1, "before process actions", RT[sxi]);
    red_print_graph(RT[sxi]);
    report_red_management();
*/
  if (RT[sxi] == NORM_FALSE) {
    RT_TOP--;
    return(NORM_FALSE);
  }
/*
  red_print_graph(RT[explore]);
*/

  for (ipi = 0; ipi < sync_xtion_ptr->party_count; ipi++) { 
    ITERATE_XI = sync_xtion_ptr->party[ipi].xtion;
    ITERATE_PI = sync_xtion_ptr->party[ipi].proc;
    RT[sxi] = red_general_statement_fwd(
      sxi, 
      ITERATE_PI, 
      sync_xtion_ptr->party[ipi].statement, 
      GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
      FLAG_ACTION_DELAYED_EVAL   
    );
    // check_dphil(RT[sxi]); 

    if (!(sync_xtion_ptr->status & FLAG_XTION_FWD_ACTION_INV_INTERFERE)) {
      if (valid_mode_index(XTION[ITERATE_XI].dst_mode_index)) { 
        RT[sxi] = red_bop(AND, RT[sxi], 
          MODE[XTION[ITERATE_XI].dst_mode_index].invariance[ITERATE_PI].red
        ); 
      }
/* 	print_resources("after process invariancing");
	report_red_management();
*/
	/*
	    red_print_graph(RT[cur_xi]);
	    */
      switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
      case FLAG_NO_REDUCTION_INACTIVE: 
	break; 
      case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
        RT[sxi] = process_inactive_variable_eliminate_noxtive(
          sxi, ITERATE_PI
        );
        break; 
      case FLAG_REDUCTION_INACTIVE: 
        RT[sxi] = process_inactive_variable_eliminate(
          sxi, ITERATE_PI
        );
        break; 
      }
/*
	print_resources("after eliminating process inactives");
	report_red_management();
*/
	/*
	    red_print_graph(RT[cur_xi]);
	    */
    }
  }
  RT[sxi] = red_postcondition_postprocessing(
    sxi, path, red_cur_reachable, red_reachable,  
    sync_xtion_ptr, 
    flag_post_processing  
  );

/*
  fprintf(RED_OUT, "\nFW %1d, after a postprocessing, RT_TOP=%1d\n", ITERATION_COUNT, RT_TOP);
  red_print_graph(RT[sxi]);
  fflush(RED_OUT);
*/
  garbage_collect(FLAG_GC_SILENT);

  RT[sxi] = red_subsume(RT[sxi]);
  RT_TOP--; /* sxi */
  /*
  print_resources("Leaving sync_bulk_xtion()");
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  return(RT[sxi]);
}
/* red_postcondition_sync_SPECIFIC() */




  

/* The procedure calculates the forward reachability from states in 
 * RT[init] as a parameter. 
 * It returns a flag for the forward reachability to the goal (or risk) states. 
 * It also has the side-effect on RT[init]. 
 * After the computation, RT[init] is the forward reachability to the 
 * input value of parameter RT[init]. 
 *
 * NOTE 2007/10/31: 
 * the abstraction flags are set in GSTATUS instead of the input parameters. 
 */ 
  
  
struct reachable_return_type	*alloc_reachable_return() {
  struct reachable_return_type	*rr; 
  
  rr = (struct reachable_return_type *) 
  	malloc(sizeof(struct reachable_return_type)); 
  rr->status = 0; 
  
  switch (GSTATUS[INDEX_TASK] & MASK_TASK) { 
  case TASK_MODEL_CHECK: 
    fprintf(RED_OUT, "\nError: print_reachable return() is called inside \n"); 
    fprintf(RED_OUT, "       a model-checking task.\n"); 
    exit(0); 
  case TASK_RISK: 
    rr->status = (rr->status & ~MASK_LFP_TASK_TYPE) | FLAG_LFP_TASK_RISK; 
    break; 
  case TASK_GOAL: 
    rr->status = (rr->status & ~MASK_LFP_TASK_TYPE) | FLAG_LFP_TASK_GOAL; 
    break; 
  case TASK_SAFETY: 
    rr->status = (rr->status & ~MASK_LFP_TASK_TYPE) | FLAG_LFP_TASK_SAFETY; 
    break; 
  case TASK_SIMULATE: 
    fprintf(RED_OUT, "\nError: print_reachable return() is called inside \n"); 
    fprintf(RED_OUT, "       a simulation task.\n"); 
    exit(0); 
  case TASK_ZENO: 
    rr->status = (rr->status & ~MASK_LFP_TASK_TYPE) | FLAG_LFP_TASK_ZENO; 
    break; 
  case TASK_DEADLOCK: 
    rr->status = (rr->status & ~MASK_LFP_TASK_TYPE) | FLAG_LFP_TASK_DEADLOCK; 
    break; 
  default: 
    fprintf(RED_OUT, "\nError: unexpected verification task in \n"); 
    fprintf(RED_OUT, "       print_reachable_return().\n"); 
    exit(0); 
  } 
  
  rr->iteration_count = 0; 
  rr->counter_example_length = 0; 
  rr->counter_example = NULL; 
  rr->reachability = NULL; 
  
  return(rr);  			
}
  /* alloc_reachable_return() */  
  
  
   

   
  

struct reachable_return_type	*red_reachable_fwd(
	int			init, // the initial state of the reachability 
	int			path, // the invariance condition of the reachability 
	int			goal, // the goal state of the reachability, 
	struct sync_xtion_type	*sync_xtion, 
	int			sync_xtion_count, 
	int			sxi_bulk // must come with triggering conditions
) {
  struct red_type		*conj, *filter;
  int				explore, explore_sync, i, pi, xi, new_red, 
				flag, tmp, flag_polarity, result;
  double			fgain; 
  struct reachable_return_type	*rr; 
  
  count_reachable_fwd++; 
  conditional_init_counter_example_management(); 

  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nBK 0: In red_reachable()\nInitial RED:\n");
  #endif 
  
  ITERATION_COUNT = 0;
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) 
    fprintf(RED_OUT, "\nStarting computing reachable state set:\n");

  RT[REACHABLE = RT_TOP++] = RT[init];
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
    runtime_report("initial REACHABLE", FLAG_NO_PRINT_XTION, RT[REACHABLE]);

  RT[REACHABLE_COMPLEMENT = RT_TOP++] = RT[path];
  RT[PARAMETER_COMPLEMENT = RT_TOP++] = NORM_NO_RESTRICTION;

  RT[REACHABLE] = red_bop(AND, RT[REACHABLE], RT[path]);
  if (   (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) 
         == FLAG_OAPPROX_GAME_MAGNITUDE
      && (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
         != FLAG_SYSTEM_HYBRID
      ) 
    RT[REACHABLE] = inactive_variable_eliminate_noxtive(REACHABLE);
  else 
    RT[REACHABLE] = inactive_variable_eliminate(REACHABLE);
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
    runtime_report("initial deactivation", FLAG_NO_PRINT_XTION, RT[REACHABLE]);

  flag_polarity = GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY; 
  if (CLOCK_COUNT + DENSE_COUNT) {
    /* With side-effect on RED_NEW_REACHABLE */
    if (   (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) 
            != FLAG_OAPPROX_GAME_MAGNITUDE
        || (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
           == FLAG_SYSTEM_HYBRID
        )  
      RT[REACHABLE] = red_add_clock_lower_bound(RT[REACHABLE]);
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("initial lowerbound", FLAG_NO_PRINT_XTION, RT[REACHABLE]);
    if ((GSTATUS[INDEX_APPROX] & MASK_OAPPROX) == FLAG_OAPPROX_GAME_MAGNITUDE) 
      RT[REACHABLE] = red_time_progress_noxtive_fwd(REACHABLE);
    else 
      RT[REACHABLE] = red_time_progress_fwd(REACHABLE, path);
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("initial saturation", FLAG_NO_PRINT_XTION, RT[REACHABLE]);
    RT[REACHABLE] = red_bop(AND, RT[REACHABLE], RT[path]);
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("initial invariancing", FLAG_NO_PRINT_XTION, RT[REACHABLE]);
    if ((GSTATUS[INDEX_APPROX] & MASK_OAPPROX) != FLAG_OAPPROX_GAME_MAGNITUDE) { 
      RT[REACHABLE] = red_hull_normalize(REACHABLE);
      if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
        runtime_report("initial normalization", FLAG_NO_PRINT_XTION, RT[REACHABLE]); 
      red_abs(REACHABLE, flag_polarity);
    } 

    /*
    fprintf(RED_OUT, "\nCPU time after time saturation at iteration %1d\n", ITERATION_COUNT);
    print_resources("before iterations");

    fprintf(RED_OUT, "\nIteration %1d, after time_saturate()\n",
	    ITERATION_COUNT
	    );
    red_print_graph(RT[REACHABLE]);

    fflush(RED_OUT);
    */
  }

  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
    add_counter_path(RT[init], ITERATION_COUNT = 0);
    /*
    fprintf(RED_OUT, "\nITERATION %1d, after adding counter path\nRT[REACHABLE=%1d]:\n", ITERATION_COUNT, REACHABLE);
    red_print_graph(RT[REACHABLE]);
    */
  } 
  
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
    print_cpu_time("\nFW 0: initial reachable:\n"); 
    red_print_graph(RT[REACHABLE]); 
    #endif 
  #endif 

  RT[explore = RT_TOP++] = RT[REACHABLE];
  rr = alloc_reachable_return(); 
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (rr && goal_check_fwd(rr, explore, NORM_FALSE, goal) == FLAG_GOAL_EARLY_REACHED) {
    if (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)) { 
      RT_TOP = RT_TOP - 5; /* RESULT_ITERATE, 
                            * explore, REACHABLE_COMPLEMENT, 
                            * PARAMETER_COMPLEMENT, REACHABLE 
                            */
      return(rr); 
    } 
  }
  RT_TOP--; // result 

  for (fgain = 1.0, ITERATION_COUNT = 1; RT[explore] != NORM_FALSE; ITERATION_COUNT++) {
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      print_cpu_time("FW %d, RED before an lfp :\n", ITERATION_COUNT);
    // check_dphil(RT[explore]); 
      #endif 
    #endif 
    
    if (!(ITERATION_COUNT % 10))
      fprintf(RED_OUT, "*");
    else
      fprintf(RED_OUT, "%1d", (ITERATION_COUNT % 10));
    fflush(RED_OUT);

    if (GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND) {
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
        fprintf(RED_OUT, "%1d %1f %1d", 
	      ITERATION_COUNT-1, red_user_time(), simple_red_memory()
	      ); 
//      simple_fxp_coverage(); 
        fprintf(RED_OUT, "\n"); 
        #endif 
      #endif 
      
      if ((  GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
           & MASK_REACHABILITY_DEPTH_BOUND
           ) 
	  < ITERATION_COUNT
	  ) { 
        if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
            && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)
            ) { 
          rr->status = rr->status & ~FLAG_COUNTER_EXAMPLE_GENERATED; 
          free_counter_example_record(rr->counter_example); 
          rr->counter_example = NULL; // no counter-example
        }
        rr->status = rr->status | FLAG_RESULT_DEPTH_BOUND_FINISHED;  
        rr->iteration_count = ITERATION_COUNT-1; 
        rr->counter_example_length = 0; 
        rr->reachability = RT[REACHABLE]; 

        RT_TOP = RT_TOP - 4; /* explore, REACHABLE_COMPLEMENT, PARAMETER_COMPLEMENT, REACHABLE */
        return(rr); 
      }
    } 

    /*
    red_print_graph(RT[explore]);
    fflush(RED_OUT);
    */

    RT[result = RT_TOP++] = red_postcondition_sync_ITERATIVE(
      rr, 
      explore, 
      path, 
      goal, 
      NORM_FALSE, 
      RT[REACHABLE], 
      sync_xtion, 
      sync_xtion_count, 
      TYPE_TRUE, // for postprocessing 
      &flag 
    );
    if (flag == FLAG_GOAL_EARLY_REACHED) {
      if (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)) { 
        RT_TOP = RT_TOP - 5; /* result, explore, REAHABLE_COMPLEMENT, PARAMETER_COMPLEMENT, REACHABLE */
        RT[init] = rr->reachability; 
        return(rr); 
      }
    }
    else if (  (//    (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE) /* In coverage estimation, 
    		//					       * the enumeration depth is set to 0
    		//					       * since in simulation, we need 
    		//					       * sync_bulk execution. 
    		//					       */
		// || 
		!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
		 )
	     ) { 
      
      RT[result] = red_bop(OR, RT[result], red_postcondition_sync_bulk(
	rr, 
	explore, 
	path, 
	goal, 
	RT[result], 
	RT[REACHABLE], 
	sxi_bulk, 
	TYPE_TRUE, // for postprocessing 
	&flag 
      ) );  /* with side-effect on RT[explore], RT[RESULT_ITERATE] */
      if (   flag == FLAG_GOAL_EARLY_REACHED
          && !(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)
          ) { 
        RT_TOP = RT_TOP - 5; /* result, explore, REACHABLE_COMPLEMENT, PARAMETER_COMPLEMENT, REACHABLE */
        RT[init] = rr->reachability; 
        return(rr); 
      } 
    }
    RT[explore] = RT[result];
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT, "\nAfter iteration %1d postconditioning\n", 
        ITERATION_COUNT
      ); 
      // check_dphil(RT[explore]); 
      #endif 
    #endif 
    
    RT_TOP--; /* result */ 

    /*
    fprintf(RED_OUT, "\nCPU time after next_xtion() at iteration %1d\n", ITERATION_COUNT);
    print_resources("after an iteration of xtion3()");
    */
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT,
	"\nFW %1d, the next states after one lfp iteration\n",
	ITERATION_COUNT
      );
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
      #endif 
    #endif 
    /*
    probe(PROBE_RISK1, "test the risk after xtion", RED_NEW_REACHABLE);
    */
/*
    fprintf(RED_OUT, "\n****************************************************************\n");
    fprintf(RED_OUT, "FWD %1d: old reachable before subtraction\nreachable:\n", ITERATION_COUNT);
    red_print_graph(RT[REACHABLE]);
    fprintf(RED_OUT, "FWD %1d: old reachable before subtraction\nexplore:\n", ITERATION_COUNT);
    red_print_graph(RT[explore]);
*/
    union_abstract_new(REACHABLE, explore, flag_polarity);
    if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
        && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)
        ) { 
      add_counter_path(RT[explore], ITERATION_COUNT);
      /*
      fprintf(RED_OUT, "\nITERATION %1d, after adding counter path\nRT[REACHABLE=%1d]:\n", ITERATION_COUNT, REACHABLE);
      red_print_graph(RT[REACHABLE]);
      */
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_REFINEMENT 
      fprintf(RED_OUT, 
        "\nFWD %1d, after union abstraction\n", 
        ITERATION_COUNT
      ); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
//    fxp_update_coverage();

/*
    fprintf(RED_OUT, "I:%1d, after iteration exclusion\n", ITERATION_COUNT);
    report_red_management();
    red_print_graph(RT[explore]);
    fflush(RED_OUT);
    fprintf(RED_OUT, "\n-------------\n");
    fprintf(RED_OUT, "I=%1d: new reachable after subtraction\nreachable:\n", ITERATION_COUNT);
    probe(PROBE_PRERISK1, "new reachable", RT[REACHABLE]);
    fprintf(RED_OUT, "\nI=%1d: new explore after subtraction \n", ITERATION_COUNT);
    probe(PROBE_PRERISK1, "new explore", RT[explore]);
    red_print_graph(RT[REACHABLE]);
    red_print_graph(RT[explore]);
    probe(PROBE_OOO, "test ooo at iteration end", RED_NEW_REACHABLE);
    exit(0);
    */
  }

  RT_TOP--; /* RT[explore] */

  if (   (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS)
      && RT[PARAMETER_COMPLEMENT] != NORM_NO_RESTRICTION
      ) {
    if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
      fprintf(RED_OUT, "\nBug, this counter example should already have been detected before.\n");
      bk(); 
    }
    switch(GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_SAFETY:
      fprintf(RED_OUT, "\nThe system is safe with the following parameter restriction.\n");
      RT[PARAMETER_COMPLEMENT] = red_hull_normalize(PARAMETER_COMPLEMENT);
      RT[PARAMETER_COMPLEMENT] = red_bop(AND, RT[PARAMETER_COMPLEMENT],
				         hybrid_parameter_extract(SPEC_EXP->u.rpred.red)
				         );
      RT[PARAMETER_COMPLEMENT] = hybrid_parameter_reduce(PARAMETER_COMPLEMENT);
      red_print_line(RT[PARAMETER_COMPLEMENT]);
      fprintf(RED_OUT, "\n");
      break;
    case TASK_RISK:
    case TASK_GOAL:
      fprintf(RED_OUT, "\nThe %s state is reachable with the following parameter restriction.\n",
	      TASK_TYPE_NAME
	      );
      RT[PARAMETER_COMPLEMENT] = red_complement(RT[PARAMETER_COMPLEMENT]);
      RT[PARAMETER_COMPLEMENT] = red_hull_normalize(PARAMETER_COMPLEMENT);
      RT[PARAMETER_COMPLEMENT] = red_bop(AND, RT[PARAMETER_COMPLEMENT],
				         hybrid_parameter_extract(SPEC_EXP->u.rpred.red)
				         );
      RT[PARAMETER_COMPLEMENT] = hybrid_parameter_reduce(PARAMETER_COMPLEMENT);
      red_print_line(RT[PARAMETER_COMPLEMENT]);
      fprintf(RED_OUT, "\n");

      break;
    }
  }
  if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
      && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)
      ) { 
    rr->status = rr->status & ~FLAG_COUNTER_EXAMPLE_GENERATED; 
    rr->counter_example_length = 0; 
    free_counter_example_record(rr->counter_example); 
    rr->counter_example = NULL; // no counter-example
  }
  rr->status = rr->status | FLAG_RESULT_FULL_FIXPOINT; 
  rr->iteration_count = ITERATION_COUNT-1; 
  rr->reachability = RT[REACHABLE]; 

  RT_TOP = RT_TOP-3; /* PARAMETER_COMPLEMENT, REACHABLE_COMPLEMENT, REACHABLE */

  return(rr);

}
  /* red_reachable_fwd() */




/************************************************************************************************
 *
 *
 *	For model-checking exists until
 */


struct red_type	*rec_extract_no_upperbound(d)
     struct red_type	*d;
{
  struct red_type		*result, *child;
  struct ddd_child_type		*ic;
  int				nvi, ci, cj, cxi;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_EXTRACT_NO_UPPERBOUND, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (VAR[d->var_index].TYPE == TYPE_CRD) {
    if (   VAR[d->var_index].U.CRD.CLOCK1 > 0 
        && VAR[d->var_index].U.CRD.CLOCK2 == 0
        ) {
      if (d->u.crd.arc[d->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY) {
	result = rec_extract_no_upperbound(d->u.crd.arc[d->u.crd.child_count-1].child);
      }
      else
	result = NORM_FALSE;
    }
    else { 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_extract_no_upperbound(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, 
			 crd_one_constraint
			 (child, d->var_index, d->u.crd.arc[ci].upper_bound)
			 ); 
      }
    }
  }
  else {
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_extract_no_upperbound(d->u.ddd.arc[ci].child); 
      result = red_bop(OR, result,
		       ddd_one_constraint
		       (child, d->var_index,
		        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
			)
		       ); 
    }
  } 
  return(ce->result = result); 
}
/* rec_extract_no_upperbound() */



struct red_type	*red_extract_no_upperbound(d)
     struct red_type	*d; 
{
  struct red_type	*result; 
  
  result = rec_extract_no_upperbound(d);  

  return(result);
}
/* check_for_pbound_redundancy() */







struct red_type	*TEST_REACHABLE;
int		TEST_REACHABLE_INDEX;


void	cgt(d) 
	struct red_type	*d; 
{ 
/*
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 8, 8); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 10, 10); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][5][0], 13, 13); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][6][0], 16, 16); 
*/
  red_print_graph(d); 	
}
  /* cgt() */ 
  
  
// Note that this procedure may rely on an implicit references to 
// RT[REACAHBLE] and RT[REACHABLE_COMPLEMENT] to do the post-processing.  
// If it is called in a precondition calculation routine without 
// a reachability calculation, then we have to properly set 
// RT[REACHABLE] and RT[REACHABLE_COMPLEMENT] to NORM_FALSE. 
//
// Note that this procedure can also be used to process the initial goal 
// state image. 
// In such a case, sxt_ptr == NULL and sxi_bulk_with_trigger == -1. 
int	count_prepost = 0; 

struct red_type	*red_precondition_postprocessing(
  int				explore, 
  struct ps_exp_type		*path_exp, 
  int				path, 
				  // RT[cur_reachable] is the accummulated 
	                          // image of the current round of 
	                          // postcondition evaluation. 
	                          // If the postprocessing is done 
	                          // for only one sync transition, 
	                          // then we will not use this 
	                          // parameter and we set cur_reachable to 
	                          // FLAG_NO_CUR_REACHABLE_EXCLUSION.  
	                          // Otherwise, it should always be 
	                          // RESULT_ITERATE. 
  struct red_type		*red_cur_reachable, // red_cur_reachable is the accummulated 
  struct red_type		*red_reachable, // red_cur_reachable is the accummulated 
	                                // image of the current round of 
	                                // postcondition evaluation. 
	                                // If the postprocessing is done 
	                                // for only one sync transition, 
	                                // then we will not use this 
	                                // parameter and we set 
	                                // cur_reachable to FLAG_NO_CUR_REACHABLE_EXCLUSION.  
	                                // Otherwise, it should always be 
	                                // RESULT_ITERATE.   

  struct sync_xtion_type	*sxt_ptr, // This is a pointer to a 
	                          // sync_xtion in a sync_xtion table. 	
	                          // If this is NULL, it means that 
	                          // sxi_bulk must be greater than zero and 
	                          // RT[sxi_bulk] must be a meaningful 
	                          // diagram for sync_xtion restrictions.  
	                          // since we must be doing postprocessing 
	                          // for sync bulk evaluation. 
  int				sxi_bulk_with_trigger,   
				  // This is an index to RT. 
	                          // RT[sxi_bulk_with_trigger] is only used in sync bulk evaluation  
	                          // in preconditon evaluation when trigger-action interference is 
				  // is possible. 
                                  // In sync bulk evaluation with trigger-action evaluation, we will 
	                          // postpone the conjunction of the triggering condition to the postprocessing
	                          // after all processes have done their actions precondition evaluation.  
  int				flag_post_processing 
) {
  int	consistent;

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_POST_PROC
    fprintf(RED_OUT, 
      "=========================================\n"); 
    if (sxt_ptr) 
      fprintf(RED_OUT, 
	"BK %1d, sxi=%1d, Entering precondition postprocessing()\n", 
        ITERATION_COUNT, sxt_ptr->index 
      );
    else 
      fprintf(RED_OUT, 
	"BK %1d, sxi=****, Entering precondition postprocessing()\n", 
	ITERATION_COUNT  
      );
    if (sxt_ptr)
      print_sync_xtion_ptr(sxt_ptr);
      red_print_graph(RT[explore]); 
    #endif 
  #endif 
/*  
  fprintf(RED_OUT, "\npre postp %1d\n", ++count_prepost); 
  fflush(RED_OUT); 
*/  
  if (sxt_ptr) {
/*
    if (sxt_ptr->index >= 9 && sxt_ptr->index <= 12) { 
      print_sync_xtion(sxt_ptr->index, SYNC_XTION); 
      fflush(RED_OUT); 
    } 
*/  
    RT[explore] = red_delayed_eval(
      sxt_ptr->red_trigger, PROC_GLOBAL, RT[explore]
    ); 
  }
  else {
    if (sxi_bulk_with_trigger != -1) { 
      RT[explore] = red_bop(AND, RT[explore], RT[sxi_bulk_with_trigger]);
      RT[explore] = red_delayed_eval(RT[explore], PROC_GLOBAL, RT[explore]); 
    } 
    RT[explore] = red_pi_eliminate(RT[explore]); 
  } 
  if (   (sxt_ptr && (sxt_ptr->status & FLAG_SYNC_XTION_QUANTIFIED_SYNC)) 
      || sxt_ptr == NULL 
      ) 
    RT[explore] = red_eliminate_all_qfd_sync(RT[explore]); 

  // I don't really understand why trigger_action inteference and quantified 
  // sync has any influence on the sync bulk or sync iterative evaluation 
  // in the postprocesing. 
  if (   (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) == FLAG_ROOT_OAPPROX
      && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) == FLAG_OAPPROX_GAME_UNTIMED
      ) { 
    RT[explore] = red_through_all_invariance(explore);
    RT[explore] = inactive_variable_eliminate_noxtive(explore);
    RT[explore] = red_time_eliminate(RT[explore]);
    print_cpu_time("a. after untimed eliminate\n");  
    if (flag_post_processing  == FLAG_NO_POST_PROCESSING) 
      return(RT[explore]); 
  } 
  else if (   (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) 
              == FLAG_ROOT_OAPPROX
           && (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) 
              == FLAG_OAPPROX_GAME_MAGNITUDE
           ) { 
    RT[explore] = red_bop(AND, RT[explore], RT[path]);
    RT[explore] = inactive_variable_eliminate_noxtive(explore);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("b. after magnitude approx eliminate\n");  
      #endif 
    #endif 
    if (flag_post_processing == FLAG_NO_POST_PROCESSING) 
      return(RT[explore]); 
    
    if (red_cur_reachable != NULL) 
      RT[explore] = red_bop(EXCLUDE, RT[explore], red_cur_reachable); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      fprintf(RED_OUT, "*** subtracting REACHABLE from explore ***\n"); 
      red_print_graph(RT[explore]); 
      red_print_graph(RT[REACHABLE]); 
      #endif 
    #endif 
    
    RT[explore] = red_bop(EXCLUDE, RT[explore], red_reachable);
    if (CLOCK_COUNT + DENSE_COUNT) { 
      RT[explore] = red_time_progress_noxtive_bck(explore);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "I:%1d, after bck saturating\n", ITERATION_COUNT);
        print_resources("after bck saturating");
        red_print_graph(RT[explore]);
        fflush(RED_OUT);
      /*
        probe(PROBE_PRERISK3, "WEAKEST: after bck saturation", RT[explore]);
        red_order_check(RT[explore]);
      */
        #endif 
      #endif 
      
      RT[explore] = red_bop(AND, RT[explore], RT[path]);
      RT[explore] = red_abs_game(RT[explore], FLAG_OAPPROX_GAME_MAGNITUDE); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
        probe(BENCHMARK_PCD5a1, "ABSTRACT: after abstract normalization", RT[explore]);
*/
        fprintf(RED_OUT, "I:%1d, SXI=%1d, after 2nd global invariancing\n", ITERATION_COUNT, ITERATE_SXI);
/*
        print_resources("after 2nd global invariancing");
*/
        red_print_graph(RT[explore]);
/*
        red_order_check(RT[explore]);
      */
        #endif 
      #endif 
    }
  } 
  else {  
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      fprintf(RED_OUT, 
        "In precondition postprocessing, before conjuncting with RT[path=%1d]:\n", 
        path
      ); 
      red_print_graph(RT[path]); 
      fprintf(RED_OUT, "RT[explore=%1d]:\n", explore); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
    
    RT[explore] = red_bop(AND, RT[explore], RT[path]);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_resources("after pi elimination and post xi restrictions");
      red_print_graph(RT[explore]);
      print_cpu_time("I:%d, sync xi=%d, after 1st reverse invariancing, RT_TOP=%d\n",
	ITERATION_COUNT, ITERATE_SXI, RT_TOP
      );
      #endif 
    #endif 
    
    if (RT[explore] == NORM_FALSE)
      return(NORM_FALSE);

    switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
    case FLAG_NO_REDUCTION_INACTIVE: 
      break; 
    case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
      RT[explore] = inactive_variable_eliminate_noxtive(explore);
      break; 
    case FLAG_REDUCTION_INACTIVE: 
      RT[explore] = inactive_variable_eliminate(explore);
      break; 
    }
    RT[explore] = red_bop(AND, RT[explore], RT[path]);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("after global inactive eliminations");
      red_print_graph(RT[explore]);
      probe(PROBE_PRERISK2, "WEAKEST: after inactive eliminating", RT[explore]);
      report_status("After global inactive elimination");
      #endif 
    #endif 

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("I:%d, after global inactive elimination, RT_TOP=%d\n", 
        ITERATION_COUNT, RT_TOP
      );
      #endif 
    #endif 
    
    if (red_cur_reachable != NULL) 
      RT[explore] = red_bop(EXCLUDE, RT[explore], red_cur_reachable);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("*** subtracting REACHABLE from explore ***\nRT[explore]:\n"); 
      print_resources("after current exclusion");
      red_print_graph(RT[explore]);
      probe(PROBE_PRERISK2, "WEAKEST: RT[explore] before reachable exclusion", RT[explore]);
      red_print_graph(RT[explore]); 
      fprintf(RED_OUT, "RT[REACHABLE]:\n"); 
      red_print_graph(RT[REACHABLE]); 
      #endif 
    #endif 
    
    RT[explore] = red_bop(EXCLUDE, RT[explore], red_reachable);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("RT[explore] result:\n"); 
      red_print_graph(RT[explore]); 
      print_resources("after whole exclusion");
      fprintf(RED_OUT, "I:%1d, SXI:%1d, WEAKEST: after reachable exclusion\n", ITERATION_COUNT, ITERATE_SXI);
      red_print_graph(RT[explore]);
      fprintf(RED_OUT, "\nThe whole reachable for reference:\n");
      red_print_graph(RT[REACHABLE]);
      probe(PROBE_PRERISK2, "WEAKEST: after reachable exclusion", RT[explore]);
      report_status("After exclusion");
      #endif 
    #endif 
    
    if (RT[explore] == NORM_FALSE)
      return(NORM_FALSE); 

    if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
        && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_REACHABLE_COMPLEMENT)
        ) {
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "\n=========================================\nI:%1d, SXI:%1d, RT explore before complement exclusion.\n");
        red_print_graph(RT[explore]);
        #endif 
      #endif 
      
      RT[consistent = RT_TOP++] = red_bop(AND, RT[explore], RT[REACHABLE_COMPLEMENT]);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "\nI:%1d, SXI:%1d, RT explore after complement restriction.\n");
        red_print_graph(RT[consistent]);
        #endif 
      #endif 
      
      RT[consistent] = hybrid_eliminate_inconsistency_DOWNWARD(consistent);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "\nI:%1d, SXI:%1d, RT explore after complement consistency.\n");
        red_print_graph(RT[consistent]);
        #endif 
      #endif 
      
      RT[explore] = RT[consistent];

      RT_TOP--; /* consistent */
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
        print_resources("after hybrid complement exclusion");
*/
        fprintf(RED_OUT, "\nI:%1d, SXI:%1d, RT explore after complement exclusion.\n");
        red_print_graph(RT[explore]);
        #endif 
      #endif 
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC

      fprintf(RED_OUT, "RT[explore] after hybrid reduction:\n"); 
      red_print_graph(RT[explore]); 
      fprintf(RED_OUT, "I:%1d, after global exclusion, RT_TOP=%1d\n", ITERATION_COUNT, RT_TOP);
/*
  probe(PROBE_PRERISK1, "WEAKEST: before bck saturating", RT[explore]);
*/
      #endif 
    #endif 
    
    // The following condition is for the users of redlib. 
    // It shows that the users do not want to do time progress operation. 
    // So we quit here. 
    if (!(GSTATUS[INDEX_TIME_PROGRESS] & FLAG_TIME_PROGRESS))  
      return(RT[explore]); 
    
    if (CLOCK_COUNT + DENSE_COUNT) {
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "I:%1d, before bck saturating\n", ITERATION_COUNT);
        red_print_graph(RT[explore]);
        #endif 
      #endif 
      
      RT[explore] = red_game_time_progress_bck(
        path_exp, explore, path, MASK_GAME_ROLES, TYPE_TRUE  
      );
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        print_cpu_time("I:%d, sxi:%d, after bck saturating\n", ITERATION_COUNT, ITERATE_SXI);
/*
        print_resources("after bck saturating");
*/
        red_print_graph(RT[explore]);
/*
        probe(PROBE_PRERISK2, "WEAKEST: after bck saturation", RT[explore]);
*/
        fprintf(RED_OUT, "I:%1d, after saturation, RT_TOP=%1d\n", ITERATION_COUNT, RT_TOP);
        fprintf(RED_OUT, "I:%1d, after bck saturating\n", ITERATION_COUNT);
        red_print_graph(RT[explore]);
        fflush(RED_OUT);
/*
      red_order_check(RT[explore]);
      report_status("After saturation");
*/
        #endif 
      #endif 
      
      RT[explore] = red_bop(AND, RT[explore], RT[path]);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        if (ITERATE_SXI >= 0 && ITERATE_SXI < SYNC_XTION_COUNT) 
          print_sync_xtion(ITERATE_SXI, SYNC_XTION); 
        print_cpu_time("FW %d, SXI %d, before hybrid time inactive eliminate in pre-post\n", 
          ITERATION_COUNT, ITERATE_SXI 
        ); 
/*
      cgt(RT[explore]);
    print_resources("after 2nd global invariancing");
*/
        fprintf(RED_OUT, "I:%1d, SXI:%1d, after 2nd invariancing\n", ITERATION_COUNT, ITERATE_SXI);
/*
    probe(PROBE_PRERISK2, "WEAKEST: after 2nd reverse invariancing", RT[explore]);
*/
        fprintf(RED_OUT, "I:%1d, after 2nd invariancing, RT_TOP=%1d\n", ITERATION_COUNT, RT_TOP);
        fflush(RED_OUT);
/*
      red_order_check(RT[explore]);
    report_status("After 2nd invariancing");
*/
        #endif 
      #endif 
      
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
        RT[explore] = timed_inactive_variable_eliminate(explore);
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
          if (ITERATE_SXI >= 0 && ITERATE_SXI < SYNC_XTION_COUNT) 
            print_sync_xtion(ITERATE_SXI, SYNC_XTION); 
          print_cpu_time("FW %d, SXI %d, after hybrid time inactive eliminate in pre-post\n", 
            ITERATION_COUNT, ITERATE_SXI 
          ); 
/*
        cgt(RT[explore]);
*/
          fprintf(RED_OUT, "I:%1d, SXI:%1d, after timed inactive elimination\n", ITERATION_COUNT, ITERATE_SXI);
/*
    probe(PROBE_PRERISK2, "WEAKEST: after timed inactive elimination", RT[explore]);
*/
          red_print_graph(RT[explore]); 
/*
    report_status("After timed inactive elimination");
*/
          #endif 
        #endif 
        
        RT[explore] = red_bop(AND, RT[explore], RT[path]);
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
        print_resources("after 3rd global invariancing");
*/
          #endif 
	#endif 
      }
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      fprintf(RED_OUT, "RT[explore], after time progression:\n"); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
    
    reduce_symmetry(explore);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
      print_resources("after symmetry");
*/
      #endif 
    #endif 
    
    if (CLOCK_COUNT > 1 || DENSE_COUNT > 0) {
      struct red_type	*red_tmp; 
      
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        fprintf(RED_OUT, "I:%1d, after path filtering\n", ITERATION_COUNT);
        red_print_graph(RT[explore]);
/*
      print_resources("after path filtering");
*/
        fflush(RED_OUT);
/*
      red_order_check(RT[explore]);
      report_red_management();
    */
        #endif 
      #endif 
      
      if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
	  && (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS)
          && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING)
          ) {
        RT[consistent = RT_TOP++] = red_bop(AND, RT[explore], RT[PARAMETER_COMPLEMENT]);
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
          print_cpu_time(
            "IT:%d, SXI:%d, before hybrid elimiante inconsistency in pre-post\n", 
            ITERATION_COUNT, ITERATE_SXI
          ); 
          #endif 
        #endif 
        
        RT[consistent] = hybrid_eliminate_inconsistency_DOWNWARD(consistent);
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
          print_cpu_time(
            "IT:%d, SXI:%d, after hybrid elimiante inconsistency in pre-post\n", 
            ITERATION_COUNT, ITERATE_SXI
          ); 
          #endif 
        #endif 
        
        RT[explore] = RT[consistent];
        RT_TOP--; /* consistent */
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
        print_resources("after parametric analysis overhead");
        probe(PROBE_PRERISK2, "WEAKEST: after parameter exclusion", RT[explore]);
        report_status("After parameter exclusion");
*/
          #endif 
        #endif 
      }
      RT[explore] = red_hull_normalize(explore);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        print_cpu_time("I:%d, SXI:%d, after normalization\n", 
          ITERATION_COUNT, ITERATE_SXI
        );
        #endif 
      #endif 
      
      if ((GSTATUS[INDEX_APPROX] & MASK_OAPPROX)
          == FLAG_OAPPROX_GAME_DIAGONAL
	  ) { 
        RT[explore] = red_abs_game(RT[explore], FLAG_OAPPROX_GAME_DIAGONAL); 
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_POST_PROC
          fprintf(RED_OUT, 
            "I:%d, SXI:%d, after abs game\n", ITERATION_COUNT, ITERATE_SXI
          );
          #endif 
        #endif 
      } 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
/*
      print_resources("after normalization");
*/
        fprintf(RED_OUT, "I:%1d, SXI:%1d, after normalization\n", ITERATION_COUNT, ITERATE_SXI);
        red_print_graph(RT[explore]);
/*
      probe(PROBE_PRERISK2, "WEAKEST: after normalizatoin", RT[explore]);
      fprintf(RED_OUT, "I:%1d, after global normalization, RT_TOP=%1d\n", ITERATION_COUNT, RT_TOP); 
      report_status("After 2nd normalization");
*/
        #endif 
      #endif 
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      fprintf(RED_OUT, "RT[explore], after normalization:\n"); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
    
    RT[explore] = red_subsume(RT[explore]);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      print_cpu_time("I:%d, SXI:%d, after reduction\n", ITERATION_COUNT, ITERATE_SXI);
/*
    print_resources("after global reduction");
*/
      red_print_graph(RT[explore]);
      #endif 
    #endif 
    
    if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
        && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_REACHABLE_COMPLEMENT)
        ) {
      struct red_type	*d_tmp;
      
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        print_cpu_time("\n*** iterative rt explore ***\n");
        red_print_graph(RT[explore]);
        #endif 
      #endif 
      
      d_tmp = red_complement(RT[explore]);
      RT[REACHABLE_COMPLEMENT] = red_bop(AND, RT[REACHABLE_COMPLEMENT], d_tmp);
      RT[REACHABLE_COMPLEMENT] = hybrid_subsume(REACHABLE_COMPLEMENT, TYPE_FALSE);
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_POST_PROC
        print_cpu_time("\ntarget zone already included.\n");
/*
      print_resources("after optional global complement");
*/
        #endif 
      #endif 
    }
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_POST_PROC
      fprintf(RED_OUT, "RT[explore], after pspsc:\n"); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
  }
  garbage_collect(FLAG_GC_SILENT);
  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_POSTPROCESSING) {
    print_resources("Leaving sync_bulk_xtion()");
    if (sxt_ptr)
      print_sync_xtion_ptr(sxt_ptr);
    fprintf(RED_OUT, "\n");
    red_print_graph(RT[explore]);
  }
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_POST_PROC
    print_cpu_time(
      "IT:%d, sxi=****, Leaving precondition postprocessing()\n", 
      ITERATION_COUNT 
    );
    if (sxt_ptr) 
      fprintf(RED_OUT, 
	"IT:%1d, sxi=%1d, Leaving precondition postprocessing()\n", 
	ITERATION_COUNT, sxt_ptr->index 
      );
    else 
      fprintf(RED_OUT, 
	"IT:%1d, sxi=****, Leaving precondition postprocessing()\n", 
	ITERATION_COUNT 
      );
    red_print_graph(RT[explore]);
/*
      report_red_management();
*/
    #endif 
  #endif 

  return(RT[explore]);
}
  /* red_precondition_postprocessing() */ 




struct red_type	*get_risk_parameter( 
  int	pc 
) { 
  RT[pc] = red_complement(RT[pc]);
  RT[pc] = red_hull_normalize(pc);
  RT[pc] = red_bop(AND, RT[pc], 
    hybrid_parameter_extract(SPEC_EXP->u.rpred.red)
  ); 
  RT[pc] = hybrid_parameter_reduce(pc);
  return(RT[pc]); 
} 
  /* get_risk_parameter() */ 
  
  
  
int 	count_parameter_complement = 0; 

int	goal_check_bck(
  struct reachable_return_type	*rr, 
  int				explore, 
  struct red_type		*red_cur_reachable, 
  int				init
) {
  int	tmp;

  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
      && (GSTATUS[INDEX_HYBRID_STRATEGY] & FLAG_HYBRID_REACHABLE_COMPLEMENT)
      ) {
    struct red_type	*d_tmp;

    d_tmp = red_complement(RT[explore]);
    RT[REACHABLE_COMPLEMENT] = red_bop(AND, RT[REACHABLE_COMPLEMENT], d_tmp);
  }
  
/*
  fprintf(RED_OUT, "\nIteration 0 goal HRD:\n");
  red_print_graph(RT[explore]);
*/
//  if ((GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) == FLAG_ROOT_NOAPPROX) {
//  We remove the last line to allow for the research of interpolation and 
//  CEGAR related techniques. 

  tmp = RT_TOP++;
  RT[tmp] = red_bop(AND, RT[explore], RT[init]);
  if (   RT[tmp] != NORM_FALSE
      && ((CLOCK_COUNT+DENSE_COUNT <= 1) || (red_hull_test_emptiness(tmp) != NORM_FALSE))
      ) {
/*
	fprintf(RED_OUT, "\nInitial state reachable!\n");
	red_print_graph(RT[tmp]);
*/
//      fxp_update_coverage();
    rr->status = rr->status | FLAG_RESULT_EARLY_REACHED;  
    if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) 
        && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED) 
        ) { 
      fprintf(RED_OUT, "\ncounter example detected at length %1d\n", 
        ITERATION_COUNT
      ); 
      fflush(RED_OUT); 
      add_counter_path(
        locate_one_instance(RT[tmp], NULL, 0), 
        ITERATION_COUNT
      );
      rr->status = rr->status | FLAG_COUNTER_EXAMPLE_GENERATED; 
      rr->counter_example_length = ITERATION_COUNT; 
      if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
        rr->counter_example = generate_counter_example_bck(); 
    } 
    if (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) {
      if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
	int	consistent;
/*
	fprintf(RED_OUT, 
	  "\nPC %1d, IT %1d, SXI %1d: new PARAMETER COMPLEMENT source:\n", 
	  ++count_parameter_complement, ITERATION_COUNT, ITERATE_SXI 
	);
	red_print_graph(RT[tmp]);
*/

	RT[tmp] = hybrid_parameter_extract(RT[tmp]); 
/*
	fprintf(RED_OUT, 
	  "\nPC %1d, IT %1d, SXI %1d: new PARAMETER COMPLEMENT piece:\n", 
	  count_parameter_complement, ITERATION_COUNT, ITERATE_SXI
	);
	red_print_graph(RT[tmp]);
*/
	RT[consistent = RT_TOP++] = red_bop( 
	  AND, RT[tmp], RT[PARAMETER_COMPLEMENT] 
	); 
/*
	fprintf(RED_OUT, 
	  "\nPC %1d, IT %1d, SXI %1d: new PARAMETER COMPLEMENT consistent:\n", 
	  count_parameter_complement, ITERATION_COUNT, ITERATE_SXI 
	);
	red_print_graph(RT[consistent]);
*/
	RT[consistent] = hybrid_eliminate_inconsistency_DOWNWARD(consistent);
/*
	fprintf(RED_OUT, "\n2: new PARAMETER COMPLEMENT after eliminating inconsistency:\n");
	red_print_graph(RT[consistent]);
*/
	RT[tmp] = RT[consistent];
/*
	fprintf(RED_OUT, "\n3: new PARAMETER COMPLEMENT after super intersection:\n");
	red_print_graph(RT[tmp]);
*/
	RT_TOP--; /* consistent */
	RT[PARAMETER_COMPLEMENT] = red_bop( 
	  AND, RT[PARAMETER_COMPLEMENT], red_complement(RT[tmp]) 
	); 
/*
	fprintf(RED_OUT, 
	  "\nPC %1d, IT %1d, SXI %1d: new PARAMETER COMPLEMENT at last\n", 
	  count_parameter_complement, ITERATION_COUNT, ITERATE_SXI
	);
	red_print_graph(RT[PARAMETER_COMPLEMENT]); 
	fprintf(RED_OUT, "\n%%%%%%%%%%%%%[New reachable state]%%%%%%%%%%%%%%%%%\n");
	red_print_graph(RT[tmp]);
	fprintf(RED_OUT, "new parameter restriction complement:\n");
	red_print_graph(RT[PARAMETER_COMPLEMENT]);
*/
      }
      else {
        fprintf(RED_OUT, "Woops! parametric analysis for timed systems are not supported!\n");
	exit(0);
      }
    }
    if (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)) { 
      fflush(RED_OUT); 
      RT_TOP = RT_TOP--; /* tmp */ 
      rr->iteration_count = 0; 
      RT[REACHABLE] = red_bop(OR, RT[REACHABLE], red_cur_reachable); 
      RT[REACHABLE] = red_bop(OR, RT[REACHABLE], RT[explore]); 
      rr->reachability = RT[REACHABLE]; 
      if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
             == FLAG_SYSTEM_HYBRID
          && (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) 
          ) {
        rr->status = rr->status | FLAG_RESULT_PARAMETRIC_ANALYSIS; 
        rr->risk_parameter = get_risk_parameter(PARAMETER_COMPLEMENT); 
      }
      else { 
        rr->status = rr->status & ~FLAG_RESULT_PARAMETRIC_ANALYSIS; 
        rr->risk_parameter = NORM_FALSE; 
      } 
      return(FLAG_GOAL_EARLY_REACHED);
    } 
  }
  RT_TOP--; /* tmp */

  return(FLAG_GOAL_NORMAL);
}
  /* goal_check_bck() */



// Note that this procedure may rely on an implicit reference to 
// RT[REACAHBLE] to do the post-processing (by calling 
// red_precondition_postprocessing(_abstract).  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
struct red_type	*red_precondition_sync_bulk(
  struct reachable_return_type	*rr, 
  int				dst, 
				// index of diagram for destination 
  struct ps_exp_type		*path_exp, 
  int				path, 
  int				init, 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  int				sxi_bulk, 
  int				sxi_bulk_with_trigger,  
				// This is an index to RT. 
		                // RT[sxi_bulk_with_trigger] is only used in sync bulk evaluation  
		                // in preconditon evaluation when trigger-action interference is 
				// is possible. 
	                        // In sync bulk evaluation with trigger-action evaluation, we will 
		                // postpone the conjunction of the triggering condition to the postprocessing
		                // after all processes have done their actions precondition evaluation.  
  int				*flag_result_ptr, 
  int				flag_post_processing  
) {
  int			cur_xi, cur_pi, urgent, flag, fxi, ixi, explore, result;
  struct red_type	*conj;

  #ifdef RED_DEBUG_FXP_DEBUG  
  if (!check_sxi_stack(ITERATION_COUNT, -1)) 
    return(FLAG_GOAL_NORMAL); 
  #endif 
  
  RT[explore = RT_TOP++] = red_bop(AND, RT[dst], RT[sxi_bulk]);
/*
  switch (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE) {
  case FLAG_TRIGGER_COVERAGE:
  case FLAG_DISCRETE_TRIGGER_COVERAGE:
  case FLAG_ARC_COVERAGE:
  case FLAG_ALL_COVERAGE:
    RT[TRIGGER_COVERAGE] = red_bop(OR, RT[TRIGGER_COVERAGE], RT[dst]);
    break;
  }
*/
  get_all_firable_xtions(explore, GSTATUS[INDEX_GAME_ROLES]);
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) { 
    if (  PROCESS[ITERATE_PI].status 
	& MASK_GAME_ROLES 
        & ~(GSTATUS[INDEX_GAME_ROLES]) 
        ) 
      continue; 

    #ifdef RED_DEBUG_FXP_MODE 
    fprintf(RED_OUT, "\nBK %1d, pi %1d, Executing sxi bulk\n", 
      ITERATION_COUNT, ITERATE_PI
    ); 
    #endif 
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    for (ixi = 0;
            ixi < PROCESS[ITERATE_PI].firable_xtion_count
         && current_firable_xtion[ITERATE_PI][ixi] != -1;
         ixi++ 
         ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(
      	RT[explore], fxi, ITERATE_XI, ITERATE_XI
      	);
      if (RT[cur_xi] == NORM_FALSE) {
        RT_TOP--; // cur_xi 
        continue;
      }

/*
      if (   (!(GSTATUS[INDEX_XTION_INSTANCE] & FLAG_XTION_INSTANCE_MAINTAIN)) 
          && (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) )
          && (!(XTION[ITERATE_XI].status & FLAG_XTION_QUANTIFIED_SYNC))
          ) 
        RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi);
*/

      if (ITERATE_XI) { 
        #ifdef RED_DEBUG_FXP_MODE 
	fprintf(RED_OUT, 
	  "\n>>>>>>>>>>>>>>>>>>>\nBK %1d sync bulk bck, before pi %1d, xi %1d:\n", 
	  ITERATION_COUNT, ITERATE_PI, ITERATE_XI
	); 
	print_xtion_line(ITERATE_XI, ITERATE_PI); 
	fprintf(RED_OUT, "\n"); 
	red_print_graph(RT[cur_xi]); 
        #endif 
        RT[cur_xi] = red_general_statement_bck(
	  cur_xi, 
	  ITERATE_PI, 
	  XTION[ITERATE_XI].statement, 
	  GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
	  FLAG_ACTION_DELAYED_EVAL 
	);
        #ifdef RED_DEBUG_FXP_MODE 
	fprintf(RED_OUT, "\nBK %1d sync bulk bck, after pi %1d, xi %1d:\n", 
	  ITERATION_COUNT, ITERATE_PI, ITERATE_XI
	); 
	red_print_graph(RT[cur_xi]); 
        #endif 
        
        if (RT[cur_xi] == NORM_FALSE) {
          RT_TOP--; // cur_xi 
          continue; 
        }
        if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                  & FLAG_BULK_TRIGGER_ACTION_INTERFERE
                ) ) 
            && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
            ) {
          RT[cur_xi] = red_delayed_eval(
            XTION[ITERATE_XI].red_trigger[ITERATE_PI], 
            ITERATE_PI, 
            RT[cur_xi]
          ); 
          if (valid_mode_index(XTION[ITERATE_XI].src_mode_index)) {
            RT[cur_xi] = red_delayed_eval(
              MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red, 
              ITERATE_PI, 
              RT[cur_xi]
            ); 
          }
          if (RT[cur_xi] == NORM_FALSE) {
            RT_TOP--; // cur_xi 
            continue;
          }
          switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
          case FLAG_NO_REDUCTION_INACTIVE: 
	    break; 
          case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
            RT[cur_xi] = process_inactive_variable_eliminate_noxtive(
              cur_xi, ITERATE_PI
            );
            break; 
          case FLAG_REDUCTION_INACTIVE: 
            RT[cur_xi] = process_inactive_variable_eliminate(
              cur_xi, ITERATE_PI
            );
            break; 
          }
        }
        conj = red_bop(EXTRACT, RT[cur_xi], PROCESS[ITERATE_PI].red_stop);
        if (conj != NORM_FALSE) { 
          RT[cur_xi] = red_bop(SUBTRACT, RT[cur_xi], PROCESS[ITERATE_PI].red_stop);
          RT[cur_pi] = red_bop(OR, RT[cur_pi], RT[cur_xi]);
          RT[cur_xi] = conj; 
          RT[cur_xi] = red_precondition_postprocessing( 
            cur_xi, 
            path_exp, path,   
            RT[cur_pi], 
            red_reachable, 
            NULL, sxi_bulk_with_trigger, 
            flag_post_processing  
          );
          #ifdef RED_DEBUG_FXP_MODE 
	  fprintf(RED_OUT, "\nBK %1d sync bulk bck, after post processing\n", 
	    ITERATION_COUNT 
	  ); 
	  red_print_graph(RT[cur_xi]); 
          #endif 
/*
          fprintf(RED_OUT, "Red_precondition_sync_bulk(), after postprocessing, ");
*/
          if (   rr
              && goal_check_bck(rr, cur_xi, red_cur_reachable, init) 
                 == FLAG_GOAL_EARLY_REACHED
              && !(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)
              ) { 
/*
            fprintf(RED_OUT, " early reached:\n"); 
            red_print_graph(RT[RESULT_ITERATE]); 
*/
            RT_TOP = RT_TOP-4; /* cur_xi, cur_pi, result, explore  */
            *flag_result_ptr = FLAG_GOAL_EARLY_REACHED;
            return(RT[result]); 
          }
          RT[result] = red_bop(OR, RT[cur_xi], RT[result]); 
/*
          fprintf(RED_OUT, " newly reached:\n"); 
          red_print_graph(RT[RESULT_ITERATE]); 
*/
        }
        else
          RT[cur_pi] = red_bop(OR, RT[cur_xi], RT[cur_pi]);
      }
      else
        RT[cur_pi] = red_bop(OR, RT[cur_xi], RT[cur_pi]);

      RT_TOP--; /* cur_xi */
      garbage_collect(FLAG_GC_SILENT);
    }

    RT[explore] = RT[cur_pi];
    RT_TOP--; /* cur_pi */
    RT[explore] = red_subsume(RT[explore]);
  }
/*
  fprintf(RED_OUT, "Red_precondition_sync_bulk(), final result:\n"); 
  red_print_graph(RT[RESULT_ITERATE]); 
*/
  #ifdef RED_DEBUG_FXP_DEBUG  
  print_sxi_stack(ITERATION_COUNT, -1, RT[result]); 
  #endif 
  
  RT_TOP = RT_TOP-2; // result, explore 
  *flag_result_ptr = FLAG_GOAL_NORMAL;
  
  return(RT[result]); 
}
/* red_precondition_sync_bulk() */





// Note that this procedure may rely on an implicit reference to 
// RT[REACAHBLE] to do the post-processing (by calling 
// red_precondition_postprocessing(_abstract).  
// If it is called without a reachability calculation, 
// then we have to properly set RT[REACHABLE] to NORM_FALSE. 
struct red_type	*red_precondition_sync_ITERATIVE(
  struct reachable_return_type	*rr, 
  int				explore, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  int				init, 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion, 
  int				sync_xtion_count, 
  int				*flag_result_ptr, 
  int				flag_post_processing  
) {
  int			sxi, urgent, flag, ipi, ai, tmp, 
			result, local_reachable;
  struct red_type	*conj;

  #ifdef RED_DEBUG_FXP_MODE 
  fprintf(RED_OUT, 
    "BK %1d, entering red_precondition_sync_ITERATIVE() with %1d sync xtions\n", 
    ITERATION_COUNT, sync_xtion_count
  ); 
  red_print_graph(RT[explore]); 
  #endif 

  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[local_reachable = RT_TOP++] = red_cur_reachable; 
  for (ITERATE_SXI = 0; ITERATE_SXI < sync_xtion_count; ITERATE_SXI++) {
    #ifdef RED_DEBUG_FXP_MODE 
    fprintf(RED_OUT, "sxi=%1d, sync.role=%x, exec.role=%x\n", 
      	    ITERATE_SXI, 
      	    sync_xtion[ITERATE_SXI].status & MASK_GAME_ROLES, 
	    sync_xtion[ITERATE_SXI].status & GSTATUS[INDEX_GAME_ROLES]
	    ); 
    fflush(RED_OUT); 
    #endif 
    if (  sync_xtion[ITERATE_SXI].status 
	& MASK_GAME_ROLES 
	& ~GSTATUS[INDEX_GAME_ROLES]
	) { 
      continue; 
    } 
    RT[sxi = RT_TOP++] = red_delayed_eval(
      sync_xtion[ITERATE_SXI].red_post, 
      PROC_GLOBAL, 
      RT[explore]
    );
    if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
      runtime_report("before backward inferencing", FLAG_PRINT_XTION, RT[sxi]);
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--; /* sxi */ 
      continue;
    }
    #ifdef RED_DEBUG_FXP_MODE 
    fprintf(RED_OUT, "\nBK %1d, Executing sxi %1d\n", 
      ITERATION_COUNT, ITERATE_SXI
    ); 
    print_sync_xtion_lines(ITERATE_SXI, sync_xtion); 
    red_print_graph(RT[sxi]); 
    #endif 
/*
    fprintf(RED_OUT, "before pi loop in red_precondition_sync_ITERATIVE()\n"); 
*/
    for (ipi = 0; ipi < sync_xtion[ITERATE_SXI].party_count; ipi++) {
      ITERATE_XI = sync_xtion[ITERATE_SXI].party[ipi].xtion;
      ITERATE_PI = sync_xtion[ITERATE_SXI].party[ipi].proc;
      if (RT[sxi] == NORM_FALSE) {
        break;
      }

      RT[sxi] = red_general_statement_bck(
        sxi, 
        ITERATE_PI, 
	sync_xtion[ITERATE_SXI].party[ipi].statement, 
	GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
	FLAG_ACTION_DELAYED_EVAL   
      );
      #ifdef RED_DEBUG_FXP_MODE 
      fprintf(RED_OUT, "\nBK %1d sync %1d bck, after pi %1d, xi %1d:\n", 
	ITERATION_COUNT, ITERATE_SXI, ITERATE_PI, ITERATE_XI
      ); 
      red_print_graph(RT[sxi]); 
      #endif 
      if (RT[sxi] == NORM_FALSE) {
        break;
      }
      if (   (!(  sync_xtion[ITERATE_SXI].status 
                & FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE
              ) ) 
          && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
          ) { 
        RT[sxi] = red_delayed_eval(
          XTION[ITERATE_XI].red_trigger[ITERATE_PI], 
          ITERATE_PI, 
          RT[sxi]
        ); 
        if (valid_mode_index(XTION[ITERATE_XI].src_mode_index)) { 
          RT[sxi] = red_delayed_eval(
            MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red, 
            ITERATE_PI, 
            RT[sxi]
          ); 
        }
        if (RT[sxi] == NORM_FALSE) { 
          break; 
        }
        switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
        case FLAG_NO_REDUCTION_INACTIVE: 
	  break; 
        case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
          RT[sxi] = process_inactive_variable_eliminate_noxtive(
            sxi, ITERATE_PI
          );
          break; 
        case FLAG_REDUCTION_INACTIVE: 
          RT[sxi] = process_inactive_variable_eliminate(
            sxi, ITERATE_PI
          );
          break; 
        }
      }
    }
/*
    fprintf(RED_OUT, "\nBK %1d, postcondition for sxi %1d:\n", 
      ITERATION_COUNT, ITERATE_SXI
    ); 
    red_print_graph(RT[sxi]); 
*/
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--; /* sxi */ 
      continue;
    }
    #ifdef RED_DEBUG_FXP_DEBUG  
    if (red_check_ooo(RT[sxi])) { 
      fprintf(RED_OUT, "\nBK%1d, SXI=%1d, ooo after precondition.\n", 
        ITERATION_COUNT, ITERATE_SXI
      ); 
      fflush(RED_OUT); 
    }
    #endif 
     
    RT[sxi] = red_precondition_postprocessing(
      sxi, 
      path_exp, path, 
      RT[local_reachable], 
      red_reachable, 
      &(sync_xtion[ITERATE_SXI]), 
      -1,  // not an index to RT[sync_bulk]
      flag_post_processing 
    );
    #ifdef RED_DEBUG_FXP_DEBUG  
    if (red_check_ooo(RT[sxi])) { 
      fprintf(RED_OUT, "\nBK%1d, SXI=%1d, ooo after precondition postprocessing.\n", 
        ITERATION_COUNT, ITERATE_SXI
      ); 
      fflush(RED_OUT); 
    }
    #endif 

    #ifdef RED_DEBUG_FXP_DEBUG  
    fprintf(RED_OUT, "\nBK %1d, post processing postcondition for sxi %1d:\n", 
      ITERATION_COUNT, ITERATE_SXI
    ); 
    red_print_graph(RT[sxi]); 
//    print_sxi_stack(ITERATION_COUNT, ITERATE_SXI, RT[sxi]); 
    #endif 

    if (   rr 
        && goal_check_bck(rr, sxi, RT[local_reachable], init) 
           == FLAG_GOAL_EARLY_REACHED
        && (!(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY))
        ) {
      RT_TOP = RT_TOP-3; // sxi, local_reachable, result 
      *flag_result_ptr = FLAG_GOAL_EARLY_REACHED;
      return(RT[sxi]); 
    }
  
    RT[result] = red_bop(OR, RT[result], RT[sxi]);
    RT[local_reachable] = red_bop(OR, RT[local_reachable], RT[sxi]); 
    RT_TOP--; /* sxi */
    garbage_collect(FLAG_GC_SILENT);

    RT[result] = red_subsume(RT[result]);
  }
/*
  print_resources("Leaving sync_ITERATIVE_xtion()");
  red_print_graph(RT[RESULT_ITERATE]);
  garbage_collect(FLAG_GC_SILENT);
*/
  *flag_result_ptr = FLAG_GOAL_NORMAL;
  RT_TOP--; // local_reachable 
  RT_TOP--; // result 

  return(RT[result]); 
}
/* red_precondition_sync_ITERATIVE() */




struct red_type	*red_precondition_sync_SPECIFIC(
  int				explore, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion_ptr, 
  int				*flag_result_ptr, 
  int				flag_post_processing 
) {
  int			sxi, urgent, flag, ipi, ai, tmp;
  struct red_type	*conj;

  if (  sync_xtion_ptr->status 
      & MASK_GAME_ROLES 
      & ~(GSTATUS[INDEX_GAME_ROLES])
      ) { 
    *flag_result_ptr = FLAG_GOAL_NORMAL;
    return(RT[explore]);
  } 
  RT[sxi = RT_TOP++] = red_bop(AND, RT[explore], sync_xtion_ptr->red_post);
  if (RT[sxi] == NORM_FALSE) {
    RT_TOP--; /* sxi */ 
    *flag_result_ptr = FLAG_GOAL_NORMAL;
    return(NORM_FALSE);
  }

  if (GSTATUS[INDEX_PRINT] & FLAG_PRINT_ALL)
    runtime_report("before backward inferencing", FLAG_PRINT_XTION, RT[sxi]);
  for (ipi = 0; ipi < sync_xtion_ptr->party_count; ipi++) {
    ITERATE_XI = sync_xtion_ptr->party[ipi].xtion;
    ITERATE_PI = sync_xtion_ptr->party[ipi].proc;
    if (RT[sxi] == NORM_FALSE) {
      break;
    }

    RT[sxi] = red_general_statement_bck(
      sxi, 
      ITERATE_PI, 
      sync_xtion_ptr->party[ipi].statement, 
      GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
      FLAG_ACTION_DELAYED_EVAL   
    );

    if (RT[sxi] == NORM_FALSE) {
      break;
    }
    if (   (!(  sync_xtion_ptr->status 
              & FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE
            ) ) 
        && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
        ) { 
      RT[sxi] = red_delayed_eval(
        XTION[ITERATE_XI].red_trigger[ITERATE_PI], 
        ITERATE_PI, 
        RT[sxi]
      ); 
      if (valid_mode_index(XTION[ITERATE_XI].src_mode_index)) { 
        RT[sxi] = red_delayed_eval(
          MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red, 
          ITERATE_PI, 
          RT[sxi]
        ); 
      }
      if (RT[sxi] == NORM_FALSE) {
        break;
      }
      switch (GSTATUS[INDEX_REDUCTION_INACTIVE] & MASK_REDUCTION_INACTIVE) { 
      case FLAG_NO_REDUCTION_INACTIVE: 
	break; 
      case FLAG_REDUCTION_INACTIVE_NOXTIVE: 
        RT[sxi] = process_inactive_variable_eliminate_noxtive(
          sxi, ITERATE_PI
        );
        break; 
      case FLAG_REDUCTION_INACTIVE: 
        RT[sxi] = process_inactive_variable_eliminate(
          sxi, ITERATE_PI
        );
        break; 
      }
    }
  }
  if (RT[sxi] != NORM_FALSE) {
    RT[sxi] = red_precondition_postprocessing(
      sxi, 
      path_exp, path,  
      red_cur_reachable, 
      red_reachable, 
      sync_xtion_ptr, 
      -1, // not an index to RT[sync_bulk] 
      flag_post_processing 
    );
  } 
  garbage_collect(FLAG_GC_SILENT);
/*
  print_resources("Leaving sync_ITERATIVE_xtion()");
  red_print_graph(RT[RESULT_ITERATE]);
  garbage_collect(FLAG_GC_SILENT);
*/
  RT_TOP--; /* sxi */
  *flag_result_ptr = FLAG_GOAL_NORMAL; 

  return(RT[sxi]);
}
/* red_precondition_sync_SPECIFIC() */








/* The procedure calculates the backward reachability to states in 
 * RT[goal] as a parameter. 
 * It returns a flag for the reachability from the initial states. 
 * It also has the side-effect on RT[goal]. 
 * After the computation, RT[goal] is the backward reachability to the 
 * input value of parameter RT[goal]. 
 *
 * NOTE 2007/10/31: 
 * the abstraction flags are set in GSTATUS instead of input parameters. 
 */ 

 
struct reachable_return_type	*red_reachable_bck( 
  int				init, 
  int				path, 
  int				goal, 
  struct sync_xtion_type	*sync_xtion, 
  int				sync_xtion_count, 
  int				sxi_bulk, // an index to the RT statck 
  int				sxi_bulk_with_trigger // an index to the RT stack
) {
  struct red_type		*conj, *filter;
  int				i, pi, xi, new_red, flag, flag_polarity, 
				flag_result, result, 
				explore, explore_sync, tmp, 
				orig_time_progress;
  double			fgain; 
  struct reachable_return_type	*rr; 
  
  conditional_init_counter_example_management(); 

  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nBK 0, In red_reachable(%x)\nGoal RED:\n", goal);
  red_print_graph(RT[goal]);
  #endif 

  ITERATION_COUNT = 0;
  if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) 
    fprintf(RED_OUT, "\nStarting computing reachable state set:\n");

  RT[REACHABLE = RT_TOP++] = RT[goal]; 

  RT[REACHABLE] = red_add_clock_lower_bound(RT[REACHABLE]);

  RT[REACHABLE_COMPLEMENT = RT_TOP++] = RT[path];
  RT[PARAMETER_COMPLEMENT = RT_TOP++] = NORM_NO_RESTRICTION;
  #ifdef RED_DEBUG_FXP_MODE
  fprintf(RED_OUT, "\n))) Before postprocessing goal\n"); 
  red_print_graph(RT[REACHABLE]); 
  #endif 

  RT[result = RT_TOP++] = NORM_FALSE;
  flag_polarity = GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY;

  // In the following, we need to swap the value of RT[REACHABLE] to NORM_FALSE, 
  // since in the postcondtion processing will use RT[REACHABLE] to 
  // remove already-reachable. 
  RT[explore = RT_TOP++] = RT[REACHABLE]; 
  RT[REACHABLE] = NORM_FALSE; 

  RT[explore] = red_precondition_postprocessing(
    explore, 
    NULL, path,  
    NORM_FALSE, 
    NORM_FALSE, 
    NULL, // no sync_xtion_ptr, together with the -1 for 
  	      // the index to RT stack, we know this is for 
  	      // an initial condition postprocessing. 
    -1, // not a sync bulk evaluation
    FLAG_POST_PROCESSING 
  );
  RT[REACHABLE] = RT[explore]; 
  RT_TOP = RT_TOP-2; /* RESULT_ITERATE, explore */
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\n))) Before postprocessing goal before fixpointing\n"); 
  red_print_graph(RT[REACHABLE]); 
  #endif 
  
  rr = alloc_reachable_return(); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\n))) after initial reachable return\n"); 
  #endif 
  
  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
    add_counter_path(RT[REACHABLE], ITERATION_COUNT = 0);
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nITERATION %d, after adding counter path\nRT[REACHABLE=%d]:\n", 
      ITERATION_COUNT, REACHABLE
    );
    red_print_graph(RT[goal]);
    #endif 
  }
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("BK 0: initial reachable:\n"); 
  red_print_graph(RT[REACHABLE]); 
  #endif 
  
  RT[explore = RT_TOP++] = RT[REACHABLE];
  if (   rr 
      && goal_check_bck(rr, explore, NORM_FALSE, init) == FLAG_GOAL_EARLY_REACHED
      && !(GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY)
      ) { 
    RT_TOP--; /* explore */
    RT_TOP = RT_TOP - 3; /* REACHABLE_COMPLEMENT, PARAMETER_COMPLEMENT, REACHABLE */
    return(rr);
  }
  for (fgain = 1.0, ITERATION_COUNT = 1; 
       RT[explore] != NORM_FALSE; 
       ITERATION_COUNT++
       ) { 
    if (!(GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & FLAG_REACHABILITY_DEPTH_BOUND)) { 
      if (!(ITERATION_COUNT % 10))
        fprintf(RED_OUT, "*");
      else
        fprintf(RED_OUT, "%1d", (ITERATION_COUNT % 10));
      fflush(RED_OUT);
    }
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nBK %d, the new states before an lfp iteration: \n",
      ITERATION_COUNT
    );
    red_print_graph(RT[explore]);
    fflush(RED_OUT);
    #endif 
    
    /* with side-effect on RED_NEW_REACHABLE */ 
    TEST_REACHABLE = RT[REACHABLE];
/*
    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID)
      RT[REACHABLE_COMPLEMENT = RT_TOP++] = red_complement(RT[REACHABLE]);
*/
    RT[result = RT_TOP++] = red_precondition_sync_ITERATIVE( 
      rr, 
      explore, 
      NULL /* no path expression */, path,  
      init, 
      NORM_FALSE, 
      RT[REACHABLE], 
      sync_xtion, 
      sync_xtion_count, 
      &flag_result, 
      TYPE_TRUE  
    );
    if (flag_result == FLAG_GOAL_EARLY_REACHED) {
      rr->iteration_count = ITERATION_COUNT; 
//      rr->status = rr->status | FLAG_RESULT_EARLY_REACHED; 
//      is done in goal_check_bck(). 
      RT_TOP--; /* RESULT_ITERATE */
      break; 
    }
    else if (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)) {
      RT[result] = red_bop(OR, RT[result], 
        red_precondition_sync_bulk(
          rr, 
       	  explore, 
          NULL /* no path expression */, path,  
          init, 
          RT[result], 
          RT[REACHABLE], 
	  sxi_bulk, 		// an index to the RT statck 
	  sxi_bulk_with_trigger,// an index to the RT stack 
	  &flag_result, 
	  TYPE_TRUE  
      )	); 
      if (flag_result == FLAG_GOAL_EARLY_REACHED) {
        rr->iteration_count = ITERATION_COUNT;  
//      rr->status = rr->status | FLAG_RESULT_EARLY_REACHED; 
//      is done in goal_check_bck(). 
        RT_TOP--; /* RESULT_ITERATE */ 
        break; 
      }
    } 

    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("BK %1d, the new states after an lfp iteration\n", ITERATION_COUNT);
    red_print_graph(RT[RESULT_ITERATE]);
    fflush(RED_OUT);
/*
    print_resources("after an iteration of xtion3()");
*/
    #endif 
    
    RT[explore] = RT[result]; 
    RT_TOP--; // result  
    #ifdef RED_DEBUG_FXP_MODE
    fprintf(RED_OUT,
      "\nBK %1d, the new states after an lfp iteration: \n",
      ITERATION_COUNT
    );
//    print_cpu_time("after next_xtion() at iteration %1d\n", ITERATION_COUNT);
//    red_print_graph(RT[explore]);
    if (red_check_ooo(RT[explore])) { 
      fprintf(RED_OUT, "\nBK%1d, ooo after an iteration.\n", 
        ITERATION_COUNT 
      ); 
      fflush(RED_OUT); 
    }
    #endif 

    union_abstract_new(REACHABLE, explore, flag_polarity);
    #ifdef RED_DEBUG_FXP_MODE
    fprintf(RED_OUT,
      "\nBK %1d, the new states after an lfp iteration subsumption: \n",
      ITERATION_COUNT
    );
//    print_cpu_time("after congregated subsumption at iteration %1d\n", ITERATION_COUNT);
    red_print_graph(RT[explore]);
/*
    if (red_check_ooo(RT[explore])) { 
      fprintf(RED_OUT, "\nBK%1d, ooo after an iteration subsumption.\n", 
        ITERATION_COUNT 
      ); 
      fflush(RED_OUT); 
    }
*/
    #endif 
    if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) 
        && (!(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)) 
        ) {
      add_counter_path(RT[explore], ITERATION_COUNT);
      #ifdef RED_DEBUG_FXP_MODE
      fprintf(RED_OUT, "\nITERATION %1d, after adding counter path\nRT[REACHABLE=%1d]:\n", ITERATION_COUNT, REACHABLE);
      red_print_graph(RT[REACHABLE]);
      #endif 
    }
    #ifdef RED_DEBUG_FXP_MODE
      fprintf(RED_OUT, "%1d %1f %1d", 
	      ITERATION_COUNT-1, red_user_time(), simple_red_memory()
	      );
//       simple_fxp_coverage(); 
      fprintf(RED_OUT, "\n"); 
    #endif 
    
    if (   (GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
            & FLAG_REACHABILITY_DEPTH_BOUND
            )
        && (GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] & MASK_REACHABILITY_DEPTH_BOUND)
	   < ITERATION_COUNT
	) { 
      rr->status = rr->status | FLAG_RESULT_DEPTH_BOUND_FINISHED;  
      rr->iteration_count = ITERATION_COUNT-1; 
      break; 
    }
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("BK%1d, after one backward fixpoint iteration\n", ITERATION_COUNT);
    red_print_graph(RT[explore]);
    fflush(RED_OUT);
    #endif 
//    fxp_update_coverage();
    garbage_collect(FLAG_GC_SILENT);
    
  }
  #ifdef RED_DEBUG_FXP_MODE
  fprintf(RED_OUT, "\nThe final backward reachable state space :\n");
  red_print_graph(RT[REACHABLE]);
  #endif 
  
  RT_TOP = RT_TOP--; /* RT[explore] */
  
  if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
      && !(rr->status & FLAG_COUNTER_EXAMPLE_GENERATED)
      ) { 
    free_counter_example_record(rr->counter_example); 
    rr->counter_example_length = 0; 
    rr->counter_example = NULL; // no counter-example
  }
  if (   (GSTATUS[INDEX_FULL_REACHABILITY] & FLAG_FULL_REACHABILITY) 
      || !(rr->status & MASK_REACHABLE_RETURN) 
      ) {
    rr->status = rr->status | FLAG_RESULT_FULL_FIXPOINT; 
    rr->iteration_count = ITERATION_COUNT-1; 
  } 
  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
         == FLAG_SYSTEM_HYBRID
      && (GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & FLAG_PARAMETRIC_ANALYSIS) 
      ) {
    rr->status = rr->status | FLAG_RESULT_PARAMETRIC_ANALYSIS; 
    rr->risk_parameter = get_risk_parameter(PARAMETER_COMPLEMENT); 
  } 
  else {
    rr->status = rr->status & ~FLAG_RESULT_PARAMETRIC_ANALYSIS; 
    rr->risk_parameter = NORM_FALSE; 
  } 

  RT_TOP = RT_TOP-3; /* REACHABLE_COMPLEMENT, PARAMETER_COMPLEMENT, 
                      * REACHABLE 
                      */

  rr->reachability = RT[REACHABLE]; 

  return(rr);
  /*
  fprintf(RED_OUT, "\nEnd of reachable state set computation\n");
  fflush(RED_OUT);
  */
}
  /* red_reachable_bck() */
  
  


void	print_hybrid_parameters(goal_name, rr) 
	char				*goal_name; 
	struct reachable_return_type	*rr; 
{
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) { 
  case FLAG_SYSTEM_HYBRID: 
    if (rr->risk_parameter != NORM_NO_RESTRICTION) { 
      switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
      case TASK_SAFETY:
	fprintf(RED_OUT, 
	  "RED>> The system may run into risk in %1d steps with the following parameter values:\nRED>> ", 
	  rr->iteration_count
	); 
        break; 
      default:
        fprintf(RED_OUT, 
          "\nRED>> The %s state are reachable from the initial states in %1d steps \n",
	  goal_name, rr->iteration_count 
	);
        fprintf(RED_OUT, 
          "      with the following parameter values:\nRED>> "
        );
      } 
      red_print_line(rr->risk_parameter); 
      fprintf(RED_OUT, "\n"); 
    } 
    break; 
  } 
} 
  /* print_hybrid_parameters() */ 
  
  
  
  
 
void	print_reachable_return(struct reachable_return_type *rr) { 
  char	*goal_name; 
  int	ic; 
  
  switch (rr->status & MASK_LFP_TASK_TYPE) { 
  case FLAG_LFP_TASK_RISK: 
    goal_name = "risk"; 
    break; 
  case FLAG_LFP_TASK_GOAL: 
    goal_name = "goal"; 
    break; 
  case FLAG_LFP_TASK_SAFETY: 
    goal_name = "unsafe"; 
    break; 
  case FLAG_LFP_TASK_ZENO: 
    goal_name = "zeno"; 
    break; 
  case FLAG_LFP_TASK_DEADLOCK: 
    goal_name = "deadlock"; 
    break; 
  } 

  if (rr->status & FLAG_COUNTER_EXAMPLE_GENERATED) {
    print_counter_example(goal_name, rr->counter_example); 
  }
  switch (rr->status & MASK_REACHABLE_RETURN) { 
  case FLAG_RESULT_EARLY_REACHED: 
    fprintf(RED_OUT, 
      "\nRED>> %s states are reachable from the initial states in %1d steps.\n", 
      goal_name, rr->iteration_count 
    ); 
    break; 
    
  case FLAG_RESULT_DEPTH_BOUND_FINISHED: 
    fprintf(RED_OUT, 
      "\nRED>> No %s states found in bounded reachability calculated in %1d steps\n\n", 
      goal_name, rr->iteration_count
    ); 
    break; 
    
  case FLAG_RESULT_DEPTH_BOUND_FINISHED | FLAG_RESULT_EARLY_REACHED: 
    fprintf(RED_OUT, "\nRED>> Bounded reachability calculated in %1d steps\n", 
      rr->iteration_count
    ); 
    fprintf(RED_OUT, "RED>> %s states are reachable from the initial states in %1d steps.\n", 
      goal_name, rr->counter_example_length 
    ); 
    break; 
    
  case FLAG_RESULT_FULL_FIXPOINT: 
    fprintf(RED_OUT, 
      "\nRED>> No %s states found in full reachability calculated in %1d steps\n\n", 
      goal_name, rr->iteration_count
    ); 
    break; 
    
  case FLAG_RESULT_FULL_FIXPOINT | FLAG_RESULT_EARLY_REACHED: 
    fprintf(RED_OUT, "\nRED>> Full reachability calculated in %1d steps\n\n", 
      rr->iteration_count
    ); 
    fprintf(RED_OUT, "RED>> %s states are reachable from the initial states in %1d steps.\n", 
      goal_name, rr->counter_example_length 
    ); 
    break; 
    
  default: 
    fprintf(RED_OUT, 
      "\nError: I don't think this is is a correct reachable result %1x.\n", 
      rr->status & MASK_REACHABLE_RETURN
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
  print_hybrid_parameters(goal_name, rr);  
  fflush(RED_OUT); 
}
  /* print_reachable_return() */ 
  
  

/**************************************************************************
* routines for backward model-checking
*/




#define FLAG_LFP	0
#define	FLAG_GFP	1
#define	MASK_FXPOINT	1

#define FLAG_NO_EVENT	0
#define	FLAG_EVENT	2

#define	FLAG_LOWERING_PRIMED		1
#define	FLAG_LOWERING_NO_PRIMED		0


struct red_type	*RED_XI_SYNC_SIGNIFICANT;










/* The following procedure extract the part in a path constraint d 
 * that corresponds to real time progress. 
 * Supposedly, d describes a precondition-event-postcondition 
 * relation. 
 * If a path in d can be satisfied with all null-transitions, 
 * then it is eligible for no transition and real time progress. 
 * Such a path constraint, represent a real path constraint for  
 * pure time progress. 
 */ 
struct red_type	*red_true_path_for_time(d) 
	struct red_type	*d; 
{
  struct red_type	*conj; 
  int			pi; 
  
  // First construct a simpler path for true time-progression. 
  conj = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    conj = ddd_one_constraint(
      conj, variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0
    ); 	
  } 
  conj = red_bop(AND, conj, d); 
  conj = red_type_eliminate(conj, TYPE_XTION_INSTANCE); 
  conj = red_eliminate_all_qfd_sync(conj); 
  conj = red_lower_all_primed(conj); 

  return(conj); 
}
  /* red_true_path_for_time() */ 
  
  
  
  
/* This procedure is used only in tctl model-checking. 
   
 */ 
// #ifdef RED_DEBUG_FXP_MODE
//   #ifdef RED_DEBUG_FXP_MODE_EVENTS
  int	count_event_precondition = 0; 
//   #endif 
// #endif 


struct a23tree_type	*event_sync_tree, *events_tree; 


  
  

#define	FLAG_EVENT_EXISTS	0
#define	FLAG_EVENT_FORALL	1

int	FLAG_EVENT_QUANTIFICATION, // either FLAG_EVENT_EXISTS or FLAG_EVENT_EXISTS_FORALL
	FLAG_EVENT_TIME_PROGRESS, 
	FLAG_EVENT_POST_PROCESSING, 
	INDEX_EVENTS, EVENT_SYNC_PATH; 


  
inline int	index_game_role_invariance(int flag_roles) { 
  switch (flag_roles) { 
  case FLAG_GAME_MODL: 
  case (FLAG_GAME_MODL | FLAG_GAME_ENVR): 
    return(GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]);  
  case FLAG_GAME_SPEC: 
  case (FLAG_GAME_SPEC | FLAG_GAME_ENVR): 
    return(GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]); 
  case MASK_GAME_ROLES: 
    return(DECLARED_GLOBAL_INVARIANCE); 
  default: 
    fprintf(RED_OUT, 
      "\nError: Illegal flag_roles %x in index_game_role_invariance().\n", 
      flag_roles
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* index_game_role_invariance() */ 



struct red_type	*red_sync_bulk_from_event_diagram(
  struct red_type	*red_events, 
  int			sync_bulk
) { 
  red_events = red_bop(AND, red_events, RT[sync_bulk+OFFSET_WITH_EVENTS]); 
  red_events = red_type_eliminate(red_events, TYPE_SYNCHRONIZER); 
  return(red_events); 
} 
  /* red_sync_bulk_from_event_diagram() */ 





int	check_sxi_event_exp(
  int				sxi,
  struct sync_xtion_type	*sync_xtion_table,  
  struct ps_exp_type		*event_exp
) {
  int			i, vt, vi, ipi, pi, xi, isi; 
  struct ps_bunit_type	*pbu; 

  if (event_exp == PS_EXP_TRUE /* PS_EXP_TRUE is type RED. */) 
    return(TYPE_TRUE); 
  else if (event_exp == PS_EXP_FALSE /* PS_EXP_FALSE is type RED. */) 
    return(TYPE_FALSE); 
  else switch(event_exp->type) {
  case TYPE_FALSE :
    return (TYPE_FALSE); 
  case TYPE_TRUE :
    return (TYPE_TRUE); 
  case TYPE_SYNCHRONIZER: 
    vt = event_exp->u.atom.var_index; 
    if (event_exp->u.atom.exp_base_proc_index == PS_EXP_GLOBAL_IDENTIFIER) { 
      for (ipi = 0; ipi < sync_xtion_table[sxi].party_count; ipi++) { 
      	pi = sync_xtion_table[sxi].party[ipi].proc; 
      	xi = sync_xtion_table[sxi].party[ipi].xtion; 
      	vi = variable_index[TYPE_SYNCHRONIZER][pi][VAR[vt].OFFSET]; 
      	for (isi = 0; isi < XTION[xi].sync_count; isi++) { 
      	  if (XTION[xi].sync[isi].sync_index == VAR[vt].OFFSET)
      	    return (TYPE_TRUE); 
      	} 
      }
      return (TYPE_FALSE); 
    } 
    else { 
      i = get_value(event_exp->u.atom.exp_base_proc_index, 0, &vi); 
      vi = variable_index[TYPE_SYNCHRONIZER][i][VAR[vt].OFFSET]; 
      for (ipi = 0; ipi < sync_xtion_table[sxi].party_count; ipi++) { 
      	pi = sync_xtion_table[sxi].party[ipi].proc; 
      	if (pi == i) { 
          xi = sync_xtion_table[sxi].party[ipi].xtion; 
          vi = variable_index[TYPE_SYNCHRONIZER][pi][VAR[vt].OFFSET]; 
          for (isi = 0; isi < XTION[xi].sync_count; isi++) { 
      	    if (XTION[xi].sync[isi].sync_index == VAR[vt].OFFSET)
      	      return (TYPE_TRUE); 
      	  }
      	} 
      }
      return (TYPE_FALSE); 
    }
    break; 
  case AND :
    for (pbu = event_exp->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (check_sxi_event_exp(sxi, sync_xtion_table, pbu->subexp) 
          == TYPE_FALSE
          ) 
        return (TYPE_FALSE); 
    }
    return(TYPE_TRUE);
  case OR :
    for (pbu = event_exp->u.bexp.blist; pbu; pbu = pbu->bnext) {
      if (check_sxi_event_exp(sxi, sync_xtion_table, pbu->subexp) 
          == TYPE_TRUE
          ) 
        return (TYPE_TRUE); 
    }
    return(TYPE_FALSE);
  case NOT :
    if (check_sxi_event_exp(
          sxi, sync_xtion_table, event_exp->u.bexp.blist->subexp
        ) == TYPE_TRUE) 
      return (TYPE_FALSE); 
    else 
      return (TYPE_TRUE); 
  case IMPLY :
    if (check_sxi_event_exp(
          sxi, sync_xtion_table, event_exp->u.bexp.blist->subexp
        ) == TYPE_FALSE) {
      return (TYPE_TRUE); 
    } 
    else 
      return (check_sxi_event_exp(sxi, sync_xtion_table, 
        event_exp->u.bexp.blist->bnext->subexp
      ) ); 

  default:
    fprintf(RED_OUT, 
      "\nError 2 in check_sxi_event_exp(): Unrecognized condition operator %1d.\n", 
      event_exp->type
    );
    print_parse_subformula(event_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n");
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
  /* check_sxi_event_exp() */ 



/*********************************************************
 *  
 */
struct red_type	*red_weak_event_precond_filter(
  struct red_type		*red_src, 
  struct red_type		*red_dst, 
  int				path, 
  int				sxi, 
  struct sync_xtion_type	*sync_xtion_table, 
  struct ps_fairness_link_type	*weak_fairness_list
) {
  int	pre, tmpre, flag; 
  
  RT[pre = RT_TOP++] = red_src; 
  for (; 
       weak_fairness_list && RT[pre] != NORM_FALSE; 
       weak_fairness_list = weak_fairness_list->next_ps_fairness_link 
       ) { 
    if (   weak_fairness_list->fairness->u.eexp.event_exp
        && weak_fairness_list->fairness->u.eexp.red_postcond 
           != NORM_NO_RESTRICTION
        && check_sxi_event_exp(sxi, sync_xtion_table,  
             weak_fairness_list->fairness->u.eexp.event_exp  
           ) != TYPE_FALSE 
        ) { 
      RT[tmpre = RT_TOP++] = red_bop(AND, red_dst, 
        weak_fairness_list->fairness->u.eexp.red_postcond
      ); 
      if (red_dst == RT[tmpre]) { 
        RT_TOP--; // tmpre 
        continue; 	
      } 
      RT[tmpre] = red_precondition_sync_SPECIFIC(
        tmpre, 
        NULL, 
        path, 
        NORM_FALSE, 
        NORM_FALSE, 
        &(sync_xtion_table[sxi]), 
        &flag, 
        FLAG_NO_POST_PROCESSING
      );  
      RT[tmpre] = red_bop(AND, RT[tmpre], 
        weak_fairness_list->fairness->u.eexp.red_precond
      ); 
      RT[pre] = red_bop(OR, RT[tmpre], 
        red_bop(AND, RT[pre], 
          red_complement(weak_fairness_list->fairness->u.eexp.red_precond)
      ) ); 
      RT_TOP--; // tmpre 
    } 	
  } 
  RT_TOP--; // pre 
  return(RT[pre]); 
}
  /* red_weak_event_precond_filter() */ 





struct red_type	*red_weak_event_precond_filter_sync_bulk(
  struct red_type		*red_src, 
  struct red_type		*red_dst, 
  int				path, 
  struct red_type		*red_sync_bulk, 
  struct red_type		*red_sync_bulk_w_triggers, 
  struct ps_fairness_link_type	*weak_fairness_list
) {
  int	pre, tmpre, flag, tmp_xi_bulk, tmp_xi_bulk_w_triggers; 
  struct red_type	*conj; 

  RT[pre = RT_TOP++] = red_src; 
  for (; 
       weak_fairness_list && red_src != NORM_FALSE; 
       weak_fairness_list = weak_fairness_list->next_ps_fairness_link 
       ) { 
    if (   weak_fairness_list->fairness->u.eexp.event_exp 
        && weak_fairness_list->fairness->u.eexp.red_postcond 
           != NORM_NO_RESTRICTION
        ) {
      RT[tmpre = RT_TOP++] = red_bop(AND, red_dst, 
        weak_fairness_list->fairness->u.eexp.red_postcond
      ); 
      if (red_dst == RT[tmpre]) { 
        RT_TOP--; // tmpre 
        continue; 	
      } 
      
      // Calculate those that satisfy the weak condition chain. 
      RT[tmp_xi_bulk = RT_TOP++] = red_bop(AND, red_sync_bulk, 
        weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp 
      ); 
      RT[tmp_xi_bulk_w_triggers = RT_TOP++] = red_bop(AND, 
      	red_sync_bulk_w_triggers, 
        weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp 
      ); 
      RT[tmpre] = red_precondition_sync_bulk(
        NULL, 
        tmpre, 
        NULL /* no path expression */, 
        path,  
        INDEX_FALSE, 
        NORM_FALSE, 
        NORM_FALSE, 
	tmp_xi_bulk, 		// an index to the RT statck 
	tmp_xi_bulk_w_triggers,// an index to the RT stack 
	&flag, 
	TYPE_FALSE   
      ); 
      RT_TOP = RT_TOP-2; // red_sync_bulk, red_sync_bulk_w_triggers 
      RT[tmpre] = red_bop(AND, RT[tmpre], 
        weak_fairness_list->fairness->u.eexp.red_precond
      ); 
      
      // Then add in those that do not satisfy the precontion. 
      // Note that at this statement, the content of RT[pre] of the 
      // previous round is destroyed. 
      RT[pre] = red_bop(OR, RT[tmpre], 
        red_bop(AND, RT[pre], 
          red_complement(weak_fairness_list->fairness->u.eexp.red_precond)
      ) ); 

      // Then add in those that do not satisfy the event condition. 
      RT[tmpre] = red_dst; 
      RT[tmp_xi_bulk = RT_TOP++] = red_bop(AND, red_sync_bulk, 
        red_complement(
          weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp 
      ) ); 
      RT[tmp_xi_bulk_w_triggers = RT_TOP++] = red_bop(AND, 
      	red_sync_bulk_w_triggers, 
        red_complement(
          weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp
      ) ); 
      RT[tmpre] = red_precondition_sync_bulk(
        NULL, 
        tmpre, 
        NULL /* no path expression */, 
        path,  
        INDEX_FALSE, 
        NORM_FALSE, 
        NORM_FALSE, 
	tmp_xi_bulk, 		// an index to the RT statck 
	tmp_xi_bulk_w_triggers,// an index to the RT stack 
	&flag, 
	TYPE_FALSE   
      ); 
      RT_TOP = RT_TOP-2; // red_sync_bulk, red_sync_bulk_w_triggers 

      RT[pre] = red_bop(OR, RT[tmpre], RT[pre]); 
      RT_TOP--; // tmpre 
    } 	
  } 
  return(red_src); 
}
  /* red_weak_event_precond_filter_sync_bulk() */ 





struct red_type	*red_weak_event_postcond_filter(
  struct red_type		*red_dest, 
  int				sxi, 
  struct sync_xtion_type	*sync_xtion_table,  
  struct ps_fairness_link_type	*weak_fairness_list
) {
  for (; 
       weak_fairness_list && red_dest != NORM_FALSE; 
       weak_fairness_list = weak_fairness_list->next_ps_fairness_link 
       ) { 
    if (   weak_fairness_list->fairness->u.eexp.event_exp
        && check_sxi_event_exp(sxi, sync_xtion_table, 
             weak_fairness_list->fairness->u.eexp.event_exp  
           ) != TYPE_FALSE 
        ) { 
      red_dest = red_bop(AND, red_dest, 
        weak_fairness_list->fairness->u.eexp.red_postcond
      ); 
    } 	
  } 
  return(red_dest); 
}
  /* red_weak_event_postcond_filter() */ 


struct red_type	*red_weak_event_postcond_filter_sync_bulk(
  struct red_type		*red_dest, 
  struct red_type		*red_sync_bulk, 
  struct ps_fairness_link_type	*weak_fairness_list
) {
  struct red_type	*conj; 
  
  for (; 
       weak_fairness_list && red_dest != NORM_FALSE; 
       weak_fairness_list = weak_fairness_list->next_ps_fairness_link 
       ) { 
    if (weak_fairness_list->fairness->u.eexp.event_exp) { 
      if (red_sync_bulk == RT[XI_SYNC_BULK]) { 
        conj = red_bop(AND, red_dest, 
          weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp
        ); 
        conj = red_bop(AND, conj, 
          weak_fairness_list->fairness->u.eexp.red_postcond
        ); 
        red_dest = red_bop(AND, red_dest, red_complement(
          weak_fairness_list->fairness->u.eexp.red_sync_bulk_from_event_exp 
        ) ); 
      }
      else { 
        conj = red_bop(AND, red_dest, 
          weak_fairness_list->fairness->u.eexp.red_game_sync_bulk_from_event_exp
        ); 
        conj = red_bop(AND, conj, 
          weak_fairness_list->fairness->u.eexp.red_postcond
        ); 
        red_dest = red_bop(AND, red_dest, red_complement(
          weak_fairness_list->fairness->u.eexp.red_game_sync_bulk_from_event_exp 
        ) ); 
      } 
      red_dest = red_bop(AND, red_dest, conj); 
    } 	
  } 
  return(red_dest); 
}
  /* red_weak_event_postcond_filter_sync_bulk() */ 




int	check_events_in_list(
  struct ps_fairness_link_type	*fairness_list
) { 
  for (; 
       fairness_list; 
       fairness_list = fairness_list->next_ps_fairness_link
       ) { 
    if (fairness_list->fairness->type == LINEAR_EVENT) 
      return(TYPE_TRUE); 
  } 
  return(TYPE_FALSE); 
} 
  /* check_events_in_list() */ 




struct red_type	*red_role_event_precondition_sync_bulk(
  struct red_type		*red_sync_bulk_from_event_exp, 
  struct red_type		*red_precond, 
  int 				dst, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  int				sync_bulk, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  int				flag_roles, 

  int				flag_opp_eok, // eliminate or keep
  int				flag_polarity, 
  int				flag_post_processing 
) {
  int			cur_xi, cur_pi, flag, fxi, ixi, result, pre, 
			flag_events;
  struct red_type	*conj;

//   #ifdef RED_DEBUG_FXP_MODE
//     #ifdef RED_DEBUG_FXP_MODE_EVENTS
    ++count_event_precondition; 
//     #endif 
//   #endif 
  #ifdef RED_DEBUG_FXP_MODE 
  fprintf(RED_OUT, 
    "Event BK %1d, entering red_event_precondition_sync bulk()\n", 
    ITERATION_COUNT  
  ); 
  red_print_graph(RT[dst]); 
  #endif 
  // The following section is for the addition of the trivial 
  // satisfaction of the destination. 
  // 
/*
  fprintf(RED_OUT, "\n(%1d) red_role_event_precondition_sync_bulk()\n", 
    count_event_precondition 
  ); 
  fprintf(RED_OUT, "red_sync_bulk_from_event_exp:\n"); 
  red_print_graph(red_sync_bulk_from_event_exp); 
  fflush(RED_OUT); 
*/
  RT[result = RT_TOP++] = NORM_FALSE; 
  if (   (   red_sync_bulk_from_event_exp == NULL 
          || red_sync_bulk_from_event_exp == NORM_NO_RESTRICTION
          )
      && !check_events_in_list(weak_fairness_list)
      ) { 
    flag_events = TYPE_FALSE; 
    RT[pre = RT_TOP++] = red_bop(AND, RT[dst], RT[sync_bulk]); 
  }
  else {
    flag_events = TYPE_TRUE; 
    RT[pre = RT_TOP++] = red_bop(AND, RT[dst], red_sync_bulk_from_event_exp); 
    RT[pre] = red_bop(AND, RT[pre], RT[sync_bulk]); 
//    RT[pre] = red_type_eliminate(RT[pre], TYPE_SYNCHRONIZER); 
  }
  get_all_firable_xtions(pre, flag_roles);

  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) { 
    if (PROCESS[ITERATE_PI].status & flag_opponent(flag_roles)) 
      continue; 

    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0]; 
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    for (ixi = 0; 
            ixi < PROCESS[ITERATE_PI].firable_xtion_count
         && current_firable_xtion[ITERATE_PI][ixi] != -1;
         ixi++ 
         ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(
        RT[pre], fxi, ITERATE_XI, ITERATE_XI
      ); 
      if (RT[cur_xi] == NORM_FALSE) {
        RT_TOP--; // cur_xi 
        continue;
      }
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_EVENTS
        fprintf(RED_OUT, "I%1d, event sync bulk %1d:%1d:%1d, before statement\n", 
          NZF, 
          count_event_precondition, ITERATE_PI, ITERATE_XI
        ); 
        red_print_graph(RT[cur_xi]); 
        #endif 
      #endif 
      if (ITERATE_XI) {
        RT[cur_xi] = red_general_statement_bck(
          cur_xi, 
	  ITERATE_PI, 
	  XTION[ITERATE_XI].statement, 
	  GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
	  FLAG_ACTION_DELAYED_EVAL   
        );
        if (RT[cur_xi] == NORM_FALSE) {
          RT_TOP--; // cur_xi 
          continue; 
        }
        #ifdef RED_DEBUG_FXP_MODE
          #ifdef RED_DEBUG_FXP_MODE_EVENTS
          fprintf(RED_OUT, 
            "I%1d, event sync bulk %1d:%1d:%1d, after statement:\n", 
            NZF, 
            count_event_precondition, ITERATE_PI, ITERATE_XI
          ); 
          red_print_graph(RT[cur_xi]); 
          #endif 
        #endif 

        conj = red_bop(EXTRACT, RT[cur_xi], PROCESS[ITERATE_PI].red_stop);
        if (conj != NORM_FALSE) { 
          RT[cur_xi] = red_bop(SUBTRACT, RT[cur_xi], PROCESS[ITERATE_PI].red_stop);
          RT[cur_pi] = red_bop(OR, RT[cur_pi], RT[cur_xi]); 
          RT[cur_xi] = conj;  
          RT[cur_xi] = red_bop(AND, RT[cur_xi], red_precond); 
          RT[cur_xi] = red_weak_event_precond_filter_sync_bulk(
            RT[cur_xi], RT[dst], path, 
            RT[sync_bulk], 
            (sync_bulk == XI_SYNC_BULK) 
            ? RT[XI_SYNC_BULK_WITH_TRIGGERS] 
            : RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS], 
            weak_fairness_list
          ); 
          RT[cur_xi] = red_type_eliminate(RT[cur_xi], TYPE_QSYNC_HOLDER); 
          if (flag_opp_eok == FLAG_OPPONENT_ELIMINATE) 
            RT[cur_xi] = red_bop(AND, RT[cur_xi], 
              red_game_eliminate_opponent(RT[sync_bulk + OFFSET_WITH_TRIGGERS], flag_roles)
            ); 
          else 
            RT[cur_xi] = red_bop(AND, RT[cur_xi], 
              RT[sync_bulk + OFFSET_WITH_TRIGGERS]
            ); 
          RT[cur_xi] = red_type_eliminate(RT[cur_xi], TYPE_XTION_INSTANCE); 
          RT[cur_xi] = inactive_variable_eliminate(cur_xi);
 
          if (flag_post_processing == FLAG_POST_PROCESSING) {
            RT[cur_xi] = red_precondition_postprocessing( 
              cur_xi, 
              path_exp, path, 
              RT[result], 
              red_reachable, 
              NULL, sync_bulk + OFFSET_WITH_TRIGGERS, 
              flag_post_processing  
            ); 
            if (flag_opp_eok == FLAG_OPPONENT_ELIMINATE) 
              RT[cur_xi] = red_game_eliminate_opponent(
                RT[cur_xi], flag_roles
              ); 
          }
          RT[result] = red_bop(OR, RT[result], RT[cur_xi]); 
        }
        else 
          RT[cur_pi] = red_bop(OR, RT[cur_pi], RT[cur_xi]); 
      }

      RT_TOP--; /* cur_xi */
    } 
    RT[pre] = RT[cur_pi]; 
    RT_TOP--; // cur_pi 
  }
  RT_TOP--; // pre   
  RT_TOP--; // result 
  
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    fprintf(RED_OUT, 
      "Event BK %1d, leaving red_event_precondition_sync bulk()\n", 
      ITERATION_COUNT  
    ); 
    red_print_graph(RT[result]); 
    #endif 
  #endif 
  return(RT[result]); 
}
/* red_role_event_precondition_sync_bulk() */
  
  


/* When the following standard precondition routine is used, 
 * it is important to know that there is a side-effect of 
 * state exclusion from RT[RESULT_ITERATE] and RT[REACHABLE]. 
 * If you do not use this side-effect, please set RESULT_ITERATE to 
 * FLAG_NO_CUR_REACHABLE_EXCLUSION and REACHABLE to zero. 
 */ 
int	count_role_event_precondition_sync_ITERATIVE = 0; 

struct red_type	*red_role_event_precondition_sync_specific(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_precond, 
  int 				dst, 
  struct ps_exp_type		*path_exp, 
  int				path, 

  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  int				sync_xtion_index, 
  struct sync_xtion_type	*sync_xtion_table, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  
  int				flag_roles, 
  int				flag_opp_eok, 
  int				flag_polarity, 
  int				flag_post_processing 
) { 
  int			sxi, neg_events, urgent, flag, ipi, ai, tmp;
  struct red_type	*conj, *redpost;

  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    count_role_event_precondition_sync_ITERATIVE++; 
    if (sync_xtion_index >= 9 && sync_xtion_index <= 12) { 
      fprintf(RED_OUT, 
        "Event BK %1d(%1d), sxi=%1d, entering red_event_precondition_sync_specific() with sync xtions\n", 
        ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
        sync_xtion_index 
      ); 
      fprintf(RED_OUT, "red_events:\n"); 
      red_print_graph(red_events); 
      fprintf(RED_OUT, "SYNC_XTION[%1d].red_events:\n", sync_xtion_index); 
      red_print_graph(SYNC_XTION[ITERATE_SXI].red_events); 
//      red_print_graph(RT[dst]); 
    }
    #endif 
  #endif 

  ITERATE_SXI = sync_xtion_index; 
  if (check_sxi_event_exp(ITERATE_SXI, sync_xtion_table, event_exp) 
      == TYPE_FALSE
      ) 
    return(NORM_FALSE); 
/*
    fprintf(RED_OUT, "sxi=%1d, sync.role=%x, exec.role=%x\n", 
      	    ITERATE_SXI, 
      	    sync_xtion[ITERATE_SXI].status & MASK_GAME_ROLES, 
	    sync_xtion[ITERATE_SXI].status & GSTATUS[INDEX_GAME_ROLES]
	    ); 
    fflush(RED_OUT); 
*/
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    fprintf(RED_OUT, "\nBK %1d(%1d), Executing sxi %1d\n", 
      ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
      ITERATE_SXI
    ); 
    print_sync_xtion(ITERATE_SXI, sync_xtion_table); 
    #endif 
  #endif 

  RT[sxi = RT_TOP++] = RT[dst]; 
              
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    fprintf(RED_OUT, 
      "\nBK %1d(%1d) sync %1d bck, after conjuncting with events:\n", 
      ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
      ITERATE_SXI 
    ); 
    red_print_graph(RT[sxi]); 
    #endif 
  #endif 
  if (flag_opp_eok == FLAG_OPPONENT_ELIMINATE) {
    redpost = red_game_eliminate_opponent(
      sync_xtion_table[ITERATE_SXI].red_post, flag_roles
    ); 
    RT[sxi] = red_bop(AND, RT[sxi], redpost);
  }

  RT[sxi] = red_precondition_sync_SPECIFIC(
    sxi, 
    NULL, 
    path, 
    NORM_FALSE, 
    NORM_FALSE, 
    &(sync_xtion_table[ITERATE_SXI]), 
    &flag, 
    FLAG_NO_POST_PROCESSING
  );  
  RT[sxi] = red_bop(AND, RT[sxi], red_precond); 
  RT[sxi] = red_weak_event_precond_filter(
    RT[sxi], RT[dst], path, 
    ITERATE_SXI, sync_xtion_table, weak_fairness_list
  ); 
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
  if (ITERATE_SXI == 49) { 
    fprintf(RED_OUT, 
      "\nEBK %1d(%1d) sync %1d bck, after weak fair pre-filtering:\n", 
      ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
      ITERATE_SXI 
    ); 
    red_print_graph(RT[sxi]); 
    fflush(RED_OUT); 
  }
    #endif 
  #endif 
  RT[sxi] = red_delayed_eval(sync_xtion_table[ITERATE_SXI].red_trigger, 
    PROC_GLOBAL, RT[sxi]
  ); 
  if (sync_xtion_table == SYNC_XTION) 
    RT[sxi] = red_bop(AND, RT[sxi], RT[DECLARED_GLOBAL_INVARIANCE]); 
  else 
    RT[sxi] = red_bop(AND, RT[sxi], RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
  if (flag_opp_eok == FLAG_OPPONENT_ELIMINATE) 
    RT[sxi] = red_game_eliminate_opponent(RT[sxi], flag_roles); 
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    fprintf(RED_OUT, 
      "\nBK %1d(%1d) sync %1d bck, after conjuncting the triggers:\n", 
      ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
      ITERATE_SXI 
    ); 
    red_print_graph(RT[sxi]); 
    #endif 
  #endif 
  if (RT[sxi] == NORM_FALSE) {
    RT_TOP--; /* sxi */ 
    return(NORM_FALSE);
  }
  if (flag_post_processing  == FLAG_POST_PROCESSING) { 
    RT[sxi] = red_precondition_postprocessing(
      sxi, 
      path_exp, path,  
      red_cur_reachable, 
      red_reachable, 
      &(sync_xtion_table[sync_xtion_index]), 
      -1, // not a sync bulk evaluation 
      flag_post_processing 
    );
    if (flag_opp_eok == FLAG_OPPONENT_ELIMINATE) 
      RT[sxi] = red_game_eliminate_opponent(RT[sxi], flag_roles); 
    #ifdef RED_DEBUG_FXP_MODE 
      #ifdef RED_DEBUG_FXP_MODE_EVENTS 
      fprintf(RED_OUT, 
        "\nBK %1d(%1d) sync %1d bck, after post processing:\n", 
        ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
        ITERATE_SXI 
      ); 
      red_print_graph(RT[sxi]); 
      #endif 
    #endif 
  }

  RT_TOP--; // sxi 
/*
  print_resources("Leaving role event sync_ITERATIVE_xtion()");
  red_print_graph(RT[RESULT_ITERATE]);
  garbage_collect(FLAG_GC_SILENT);
*/
  return(RT[sxi]);
}
  /* red_role_event_precondition_sync_specific() */ 





struct red_type	*red_role_event_precondition_sync_ITERATIVE(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_precond, 
  int 				dst, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion_table, 
  int				count_sync_xtions, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_roles, 
  int				flag_opp_eok, // eliminate or keep 
  int				flag_polarity, 
  int				flag_post_processing 
) { 
  int	newdst, result;

  #ifdef RED_DEBUG_FXP_MODE 
  count_role_event_precondition_sync_ITERATIVE++; 
  fprintf(RED_OUT, 
    "Event BK %1d(%1d), entering red_role_event_precondition_sync_ITERATIVE() with %1d sync xtions\n", 
    ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE, 
    SYNC_XTION_COUNT 
  ); 
  red_print_graph(RT[dst]); 
  #endif 

  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    fprintf(RED_OUT, "\nRE BK %1d(%1d), the destination with events\n", 
      ITERATION_COUNT, 
      count_role_event_precondition_sync_ITERATIVE 
    ); 
    pcform(event_exp); 
    fprintf(RED_OUT, "to dest:\n"); 
    red_print_graph(RT[dst]); 
    #endif 
  #endif 
  RT[newdst = RT_TOP++] = RT[dst]; 
  RT[result = RT_TOP++] = NORM_FALSE; 
  for (ITERATE_SXI = 0; ITERATE_SXI < count_sync_xtions; ITERATE_SXI++) {
    if (sync_xtion_table[ITERATE_SXI].status & MASK_GAME_ROLES & ~flag_roles) { 
      continue; 
    } 
    #ifdef RED_DEBUG_FXP_MODE 
      #ifdef RED_DEBUG_FXP_MODE_EVENTS 
      fprintf(RED_OUT, "\nRE BK %1d(%1d), Executing sxi %1d\n", 
        ITERATION_COUNT, 
        count_role_event_precondition_sync_ITERATIVE, 
        ITERATE_SXI
      ); 
      print_sync_xtion(ITERATE_SXI, sync_xtion_table); 
      #endif 
    #endif 
    RT[result] = red_bop(OR, RT[result], 
      red_role_event_precondition_sync_specific(
        event_exp, 
        red_precond, 
	newdst, 
	path_exp, 
	path, 
	RT[result], 
	red_reachable, 
	ITERATE_SXI, 
	sync_xtion_table, 
        weak_fairness_list, 
        flag_roles, 
        flag_opp_eok, 
        flag_polarity, 
        flag_post_processing
    ) );
    RT[newdst] = red_bop(OR, RT[newdst], RT[result]); 
    #ifdef RED_DEBUG_FXP_MODE 
      #ifdef RED_DEBUG_FXP_MODE_EVENTS 
      fprintf(RED_OUT, "\nRE BK %1d(%1d) sync %1d bck, after precondition specific execution:\n", 
	ITERATION_COUNT, 
	count_role_event_precondition_sync_ITERATIVE, 
	ITERATE_SXI 
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 

  }
  RT[result] = red_subsume(RT[result]);
  RT_TOP--; // result 
  RT_TOP--; // newdst 

  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_EVENTS 
    print_resources(
      "BK %1d(%1d), Leaving red_role_event_precondition_sync_ITERATIVE()", 
      ITERATION_COUNT, count_role_event_precondition_sync_ITERATIVE
    );
    red_print_graph(RT[result]);
    garbage_collect(FLAG_GC_SILENT);
    #endif 
  #endif 
  return(RT[result]);
}
  /* red_role_event_precondition_sync_ITERATIVE() */ 





struct red_type	*red_role_event_precondition(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_sync_bulk_from_event_exp, 
  struct red_type		*red_precond, 
  int 				dst, 
  struct ps_exp_type		*path_exp, 
  
  int				path, 
  struct red_type		*red_cur_reachable, 
  struct red_type		*red_reachable, 
  struct sync_xtion_type	*sync_xtion_table, 
  int				count_sync_xtions, 

  int				sync_bulk, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_roles, 
  int				flag_opp_eok, // eliminate or keep ? 
  int				flag_polarity, 
  int				flag_post_processing 
) { 
  int	result; 
  
  RT[result = RT_TOP++] = red_role_event_precondition_sync_bulk(
    red_sync_bulk_from_event_exp, 
    red_precond, 
    dst, 
    path_exp, path, 
    
    red_cur_reachable, 
    red_reachable, 
    sync_bulk, 
    weak_fairness_list, 
    flag_roles, 
    
    flag_opp_eok, 
    flag_polarity, 
    flag_post_processing 
  ); 
  RT[result] = red_bop(OR, 
    RT[result], 
    red_role_event_precondition_sync_ITERATIVE(
      event_exp, 
      red_precond, 
      dst, 
      path_exp, path, 
      RT[result], 
      red_reachable, 
      sync_xtion_table, 
      count_sync_xtions, 
      weak_fairness_list,  
      flag_roles, 
      flag_opp_eok, 
      flag_polarity, 
      flag_post_processing  
  ) ); 
  RT[result] = red_subsume(RT[result]); 
  RT_TOP--; // result 

  return(RT[result]); 
} 
  /* red_role_event_precondition() */  
  
  
  
/***********************************************************************************
 *
 *  This is a very general-purpose backward reachability analyzer that supports the following 
 *  tasks. 
 *  1. least fixpoint calculation 
 *  2. non-Zeno computation
 *  3. inner loop iteration of greatest fixpoint calculation 
 * 
 *  Since it also is meant to be used in the construction of the greatest 
 *  fixpoint evaluation, 
 *  if RT[path] does not cover RT[dest], 
 *  it does not include the destination states. 
 * 
 *  Notes 090614: 
 *  Now we assume that if there is a preliminary time progress operation to 
 *  this euntil bck procedure's dest argument. 
 */
#ifdef RED_DEBUG_FXP_MODE
#endif 
int	count_euntil = 0; 

struct red_type	*red_role_euntil_bck(
  int				dest, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  struct sync_xtion_type	*sync_xtion_table, 
  int				count_sync_xtions, 
  int				sync_bulk, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_roles, 
  int				flag_polarity 
) { 
  int			fxp, i, pi, xi, new_red, flag, explore, 
			local_path, tmp, orig_gstatus_norm;
  struct ps_exp_type	EXP_UNTIL; 

  #ifdef RED_DEBUG_FXP_MODE
  int	orig_rttop = RT_TOP; 
  print_cpu_time("\nrole euntil %1d, RT_TOP=%1d", 
    ++count_euntil, 
    RT_TOP
  ); 
  fflush(RED_OUT);   
  #endif 

/*

  fprintf(RED_OUT, "\nIn red_reachable(%x)\nInitial RED:\n", RED_NEW_REACHABLE);
  red_print_graph(RED_NEW_REACHABLE);
  */
  ITERATION_COUNT = 0;
  /*
  fprintf(RED_OUT, "\nStarting computing reachable state set:\n");
  */

  /* We first need to calculate the suffix to the destination of 
   * the until image. 
   */ 
    
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_EUNTIL
    print_cpu_time(
      "M%1d;\nEUNTIL %1d: after the initial event precondition (NTP), RT[dest=%1d]:\n", 
      simple_red_memory(), count_euntil, dest  
    ); 
    red_print_graph(RT[dest]); 
    #endif 
  #endif 
  
  orig_gstatus_norm = GSTATUS[INDEX_NORM_ZONE];
  GSTATUS[INDEX_NORM_ZONE] 
  = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE)
  | FLAG_NORM_ZONE_CLOSURE; 

  RT[fxp = RT_TOP++] = RT[dest]; 
  RT[fxp] = red_hull_normalize(fxp); 
    
  if (GSTATUS[INDEX_APPROX] & MASK_SYMMETRY) 
    reduce_symmetry(fxp);

  REACHABLE = fxp;
  RT[explore = RT_TOP++] = RT[fxp];
  for (ITERATION_COUNT = 1; RT[explore] != NORM_FALSE; ITERATION_COUNT++) {
/*
    fprintf(RED_OUT, "\n=================================================================\n");
    fprintf(RED_OUT, "EUNTIL in the %1d'th iteration :\n", ITERATION_COUNT);
//    print_resources("EUNTIL"); 
    red_print_graph(RT[explore]); 
    fflush(RED_OUT);

//    fprintf(RED_OUT, "EUNTIL in the %1d'th iteration :\n", ITERATION_COUNT);
*/
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_EUNTIL
      print_cpu_time("M%1d;\nEUNTIL %1d:%1d: RT[explore]:\n", 
        simple_red_memory(), count_euntil, ITERATION_COUNT
      ); 
      red_print_graph(RT[explore]); 
      #endif 
    #endif 
/*
    print_cpu_time("In Analyze red_RT[explore=%1d]\n", explore);
    if (!(ITERATION_COUNT % 10))
      fprintf(RED_OUT, "*");
    else
      fprintf(RED_OUT, "%1d", (ITERATION_COUNT % 10));
    fflush(RED_OUT);
    fprintf(RED_OUT,
	    "\nIteration %1d, the RED_REACHABLE before next_xtion3\n",
	    ITERATION_COUNT
	    );
    red_print_graph(RED_REACHABLE);
    fflush(RED_OUT);
    */

    /* with side-effect on RED_NEW_REACHABLE */ 
    RT[explore] = red_role_event_precondition( 
      PS_EXP_TRUE, 
      NORM_NO_RESTRICTION, 
      NORM_NO_RESTRICTION, 
      explore, 
      path_exp, 
      
      path, 
      NORM_FALSE, 
      RT[REACHABLE], 
      sync_xtion_table,
      count_sync_xtions, 
      
      sync_bulk, 
      weak_fairness_list, 
      flag_roles, 
      FLAG_OPPONENT_ELIMINATE, 
      flag_polarity, 
      
      TYPE_TRUE 
    ); 
    union_abstract_new(fxp, explore, flag_polarity);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_EUNTIL
      fprintf(RED_OUT,
	"M%1d;\nEUNTIL %1d:%1d, the next states after next_xtion3\n",
	simple_red_memory(), count_euntil, ITERATION_COUNT
      );
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
      #endif 
    #endif 
/*
    print_cpu_time("\nCPU time after next_xtion() at iteration %1d\n", ITERATION_COUNT);
    print_resources("after an iteration of xtion3()");

    probe(PROBE_PRERISK3, "EUNTIL_BCK: test the risk after xtion", RT[explore]);
    */


    /*
    probe(PROBE_OOO, "test ooo at iteration end", RED_NEW_REACHABLE);
    exit(0);
    */
  }

  RT_TOP--; /* explore */ 
  RT_TOP--; // fxp 
  GSTATUS[INDEX_NORM_ZONE] = orig_gstatus_norm;
  
  #ifdef RED_DEBUG_FXP_MODE
  if (orig_rttop != RT_TOP) { 
    print_cpu_time(
      "Error: the RT_TOP value %1d is not consistent \n", RT_TOP
    ); 
    print_cpu_time(
      "       with the entering value %1d in red_role_euntil_bck!\n",
      orig_rttop  
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  #endif 
  
  return(RT[fxp]);

  /*
  print_cpu_time("\nEnd of reachable state set computation\n");
  fflush(RED_OUT);
  */
}
  /* red_role_euntil_bck() */



  
struct red_type	*red_label_bck(
  struct ps_exp_type	*, 
  int			, 
  int			, 
  int			,  
  int			// -1 for under-approx
			// 0 for no-approx 
			// 1 for over-approx 
); 



inline int	setup_role_fairness_before_gfp(
  struct ps_exp_type	*game_exp, 
  int			w, 
  int			token_strong_fairness, 
  int			flag_polarity, 
  int			easy_state_strong    
) { 
  struct ps_fairness_link_type	*fl;
  int				flag_tctctl = FLAG_TCTCTL_SUBFORM; 

  if (GSTATUS[INDEX_GFP] & FLAG_IN_GFP_EASY_STRONG_FAIRNESS) 
    RT[easy_state_strong] = RT[w]; 
  else 
    RT[easy_state_strong] = NORM_FALSE; 
  for (fl = game_exp->u.mexp.weak_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) {
    if (fl->fairness->u.eexp.event_exp == NULL) {
      flag_tctctl = flag_tctctl 
      & (  fl->fairness->u.eexp.precond_exp->exp_status 
         & FLAG_TCTCTL_SUBFORM
         ); 
      RT[w] = red_label_bck( 
        fl->fairness->u.eexp.precond_exp, 
        TYPE_TRUE , 
        w, 
        w, // This won't change in the evaluation of red_label_bck().      
        flag_polarity
      ); 
    } 
    else { 
      RT[easy_state_strong] = NORM_FALSE; 
      fl->fairness->u.eexp.red_precond = red_label_bck( 
        fl->fairness->u.eexp.precond_exp, 
        TYPE_TRUE , 
        w, 
        w, // This won't change in the evaluation of red_label_bck().      
        flag_polarity
      ); 
      protect_from_gc_with_token(
        fl->fairness->u.eexp.red_precond, 
        token_strong_fairness, TOKEN_PROTECTION_LIST
      ); 
      fl->fairness->u.eexp.red_postcond = red_label_bck( 
        fl->fairness->u.eexp.postcond_exp, 
        TYPE_TRUE, 
        w, 
        w, // This won't change in the evaluation of red_label_bck().      
        flag_polarity
      ); 
      protect_from_gc_with_token(
        fl->fairness->u.eexp.red_postcond, 
        token_strong_fairness, TOKEN_PROTECTION_LIST
      ); 
    } 
  } 

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_LABEL
    print_cpu_time("The weak fairness path : \n"); 
    red_print_graph(RT[w]); 
    print_cpu_time("The weak events : \n"); 
    red_print_graph(RT[weak_events]); 
    print_cpu_time("The weak event dest : \n"); 
    red_print_graph(RT[weak_event_dest]); 
    #endif 
  #endif 

  if (   (GSTATUS[INDEX_GFP] & FLAG_IN_GFP_EASY_STRONG_FAIRNESS) 
      && RT[easy_state_strong] != NORM_FALSE
      )
    RT[easy_state_strong] = RT[w]; 

  for (fl = game_exp->u.mexp.strong_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) { 
    fl->fairness->u.eexp.red_precond = red_label_bck( 
      fl->fairness->u.eexp.precond_exp, 
      TYPE_TRUE , 
      w, 
      w, // This won't change in the evaluation of red_label_bck().      
      flag_polarity
    ); 
    protect_from_gc_with_token(
      fl->fairness->u.eexp.red_precond, 
      token_strong_fairness, TOKEN_PROTECTION_LIST
    ); 
    if (fl->fairness->u.eexp.event_exp) {
      fl->fairness->u.eexp.red_postcond = red_label_bck( 
        fl->fairness->u.eexp.postcond_exp, 
        TYPE_TRUE, 
        w, 
        w, // This won't change in the evaluation of red_label_bck().      
        flag_polarity
      ); 
      protect_from_gc_with_token(
        fl->fairness->u.eexp.red_postcond, 
        token_strong_fairness, TOKEN_PROTECTION_LIST
      ); 
      RT[easy_state_strong] = NORM_FALSE; 
    } 
    else 
      RT[easy_state_strong] = red_bop(AND, RT[easy_state_strong], 
        fl->fairness->u.eexp.red_precond
      ); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
/*        print_resources("Connecting strong fairness"); 
*/
      print_cpu_time("\nstrong fairness for "); 
      pcform(fl->fairness); 
      print_cpu_time("\n"); 
      print_cpu_time("\nstrong red fairness for "); 
      red_print_graph(fl->red_fairness); 
      print_cpu_time("\n"); 
      #endif 
    #endif 
  }
  return(flag_tctctl); 
} 
  /* setup_role_fairness_before_gfp() */ 



/* The current implementation is based on assumption that 
 * invariance conditions have already been enforced in 
 * RT[path].
 */ 
struct a23tree_type	*timeless_tree; 

void	rec_gfp_guess_timeless( 
  struct red_type	*d, 
  struct red_type	**timeless_ptr, 
  struct red_type	**timed_ptr 
) { 
  struct red_type	*child_timeless, *child_timed, 
			*result_timeless, *result_timed;
  struct hrd_exp_type	*he;
  struct crd_child_type	*bc;
  struct hrd_child_type	*hc;
  struct ddd_child_type	*ic;
  int			c2, ci; 
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) {
    *timeless_ptr = d; 
    *timed_ptr = NORM_FALSE; 
    return;
  }
  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, timeless_tree, rec_single_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    *timeless_ptr = nrec->redy; 
    *timed_ptr = nrec->result; 
    return; 
  }

  result_timeless = NORM_FALSE;
  result_timed = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (!c2) { 
      /* This is an upperbound inequality. */ 
      ci = d->u.crd.child_count-1; 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
        rec_gfp_guess_timeless(d->u.crd.arc[ci].child, 
          &child_timeless, &child_timed
        ); 
        result_timeless = child_timeless; 
        result_timed = child_timed; 
      } 
      for (ci--; ci >= 0; ci--) { 
        child_timed = crd_lone_subtree(d->u.crd.arc[ci].child, 
          d->var_index, d->u.crd.arc[ci].upper_bound
        );
        result_timed = red_bop(OR, result_timed, child_timed);
      } 
    }
    else { 
      result_timeless = NORM_FALSE;
      result_timed = d;
    }
    break;

  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      rec_gfp_guess_timeless(hc->child, &child_timeless, &child_timed); 
      child_timeless = hrd_lone_subtree(child_timeless, 
	d->var_index, d->u.hrd.hrd_exp,
        hc->ub_numerator, hc->ub_denominator
      );
      result_timeless = red_bop(OR, result_timeless, child_timeless);
      child_timed = hrd_lone_subtree(child_timed, 
	d->var_index, d->u.hrd.hrd_exp,
        hc->ub_numerator, hc->ub_denominator
      );
      result_timed = red_bop(OR, result_timed, child_timed);
    }
    break; 
    
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      rec_gfp_guess_timeless(d->u.fdd.arc[ci].child, &child_timeless, &child_timed);
      child_timeless = fdd_lone_subtree(child_timeless, 
        d->var_index, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result_timeless = red_bop(OR, result_timeless, child_timeless);
      child_timed = fdd_lone_subtree(child_timed, 
        d->var_index, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result_timed = red_bop(OR, result_timed, child_timed);
    }
    break; 
    
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      rec_gfp_guess_timeless(d->u.dfdd.arc[ci].child, &child_timeless, &child_timed);
      child_timeless = dfdd_lone_subtree(child_timeless, 
        d->var_index, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result_timeless = red_bop(OR, result_timeless, child_timeless);
      child_timed = dfdd_lone_subtree(child_timed, 
        d->var_index, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result_timed = red_bop(OR, result_timed, child_timed);
    }
    break; 
    
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      rec_gfp_guess_timeless(ic->child, &child_timeless, &child_timed);
      child_timeless = ddd_lone_subtree(child_timeless, 
        d->var_index, ic->lower_bound, ic->upper_bound
      );
      result_timeless = red_bop(OR, result_timeless, child_timeless);
      child_timed = ddd_lone_subtree(child_timed, 
        d->var_index, ic->lower_bound, ic->upper_bound
      );
      result_timed = red_bop(OR, result_timed, child_timed);
    }
  }

  *timeless_ptr = nrec->redy = result_timeless; 
  *timed_ptr = nrec->result = result_timed; 
} 
  /* rec_gfp_guess_timeless() */ 
  
  
void	gfp_guess_timeless( 
  struct red_type	*d, 
  struct red_type	**timeless_ptr, 
  struct red_type	**timed_ptr 
) {
  int	result; 

  init_23tree(&timeless_tree); 
  rec_gfp_guess_timeless(d, timeless_ptr, timed_ptr); 
  free_entire_23tree(timeless_tree, rec_free); 
}
  /* gfp_guess_timeless() */  
  
 


struct red_type	*rec_system_clocks_unbounded( 
  struct red_type	*d 
) { 
  struct red_type	*conj, *result;
  int			c2, ci; 
  struct rec_type	*rec, *nrec; 

  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE 
      || d->var_index > ZONE[ZENO_CLOCK][0]
      ) {
    return(d);
  }
  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, timeless_tree, rec_single_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  }

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (   VAR[d->var_index].U.CRD.CLOCK1 == ZENO_CLOCK 
            || VAR[d->var_index].U.CRD.CLOCK1 == TIME
            || VAR[d->var_index].U.CRD.CLOCK1 == PLAY_TIME
            || VAR[d->var_index].U.CRD.CLOCK1 == MODAL_CLOCK
            )
        && VAR[d->var_index].U.CRD.CLOCK2 == 0
        ) { 
      /* This is an upperbound inequality. */ 
      ci = d->u.crd.child_count-1; 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
        result = rec_system_clocks_unbounded(d->u.crd.arc[ci].child); 
      } 
      else 
        result = NORM_FALSE; 
    }
    else { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_system_clocks_unbounded(d->u.crd.arc[ci].child);
        conj = crd_lone_subtree(conj, 
          d->var_index, d->u.crd.arc[ci].upper_bound
        );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_system_clocks_unbounded(d->u.hrd.arc[ci].child); 
      conj = hrd_lone_subtree(conj, 
	d->var_index, d->u.hrd.hrd_exp,
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
      );
      result = red_bop(OR, result, conj);
    }
    break; 
    
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_system_clocks_unbounded(d->u.fdd.arc[ci].child);
      conj = fdd_lone_subtree(conj, 
        d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
    
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_system_clocks_unbounded(d->u.dfdd.arc[ci].child);
      conj = dfdd_lone_subtree(conj, 
        d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
    
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_system_clocks_unbounded(d->u.ddd.arc[ci].child);
      conj = ddd_lone_subtree(conj, 
        d->var_index, 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
  }

  return(nrec->result = result); 
} 
  /* rec_system_clocks_unbounded() */ 
  
  
struct red_type	*red_system_clocks_unbounded( 
  struct red_type	*d
) {
  struct red_type	*result; 

  if (CLOCK_COUNT + DENSE_COUNT) { 
    init_23tree(&timeless_tree); 
    result = rec_system_clocks_unbounded(d); 
    free_entire_23tree(timeless_tree, rec_free); 
  }
  else 
    result = d; 
  return(result); 
}
  /* red_system_clocks_unbounded() */  
  
 





int 
  ROLE_FAIRNESS_ITER = 0, 
  ROLE_FAIRNESS_STRONG_ITER = 0; 
  
struct red_type	*red_fair_cycle_through_strong_fairness( 
  struct ps_exp_type		*game_exp, 
  int				w, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  struct ps_fairness_link_type	*weak_fairness_list, 

  int				flag_roles,   
  int				flag_polarity
) { 
  struct ps_fairness_link_type	*fl;
  int 				orig_rttop = RT_TOP; 

  for (ROLE_FAIRNESS_STRONG_ITER = 1, 
       fl = game_exp->u.mexp.strong_fairness_list; 
       fl; 
       ROLE_FAIRNESS_STRONG_ITER++, fl = fl->next_ps_fairness_link
       ) { 
    if (fl->fairness->u.eexp.event_exp == NULL) { 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time(
          "\nROLE FAIRNESS %s:%1d:%1d, before ROLE state for strong state fairness:\n", 
          role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
          ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
        ); 
        pcform(fl->fairness); 
        red_print_graph(RT[w]); 
        #endif 
      #endif 
      RT[w] = red_bop(AND, RT[w], fl->fairness->u.eexp.red_precond); 
      if (   (fl->fairness->u.eexp.precond_exp->var_status & FLAG_CLOCK)
          || (fl->fairness->u.eexp.precond_exp->exp_status & FLAG_HYBRID)
          ) { 
        RT[w] = red_game_time_progress_bck(
          path_exp, 
          w, path, flag_roles, 
          TYPE_TRUE   
        ); 
        RT[w] = red_hull_normalize(w); 
      }
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time(
          "\nROLE FAIRNESS %s:%1d:%1d, after ROLE state for strong state fairness:\n", 
          role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
          ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
        ); 
        red_print_graph(RT[w]); 
        #endif 
      #endif 
    }
    else { 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time(
          "\nROLE FAIRNESS %s:%1d:%1d, before ROLE event for strong event fairness:\n", 
          role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
          ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
        ); 
        pcform(fl->fairness); 
        red_print_graph(RT[w]); 
        #endif 
      #endif 
      RT[w] = red_bop(AND, RT[w], fl->fairness->u.eexp.red_postcond); 
      RT[w] = red_role_event_precondition( 
        fl->fairness->u.eexp.event_exp, 
        fl->fairness->u.eexp.red_sync_bulk_from_event_exp, 
        fl->fairness->u.eexp.red_precond, 
        w, 
        path_exp, 
        
        path, 
        NORM_FALSE, 
        NORM_FALSE, 
        SYNC_XTION, 
        SYNC_XTION_COUNT, 
        
        XI_SYNC_BULK, 
        weak_fairness_list, 
        flag_roles, 
        FLAG_OPPONENT_ELIMINATE, 
        flag_polarity, 
        
        TYPE_FALSE 
      ); 
      RT[w] = red_game_time_progress_bck(
        path_exp, 
        w, path, flag_roles, 
        TYPE_TRUE   
      ); 
      RT[w] = red_hull_normalize(w); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time(
          "\nROLE FAIRNESS %s:%1d:%1d, after ROLE event for strong event fairness:\n", 
          role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
          ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
        ); 
        red_print_graph(RT[w]); 
        #endif 
      #endif 
    } 

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time(
        "\nROLE FAIRNESS %s:%1d:%1d, ROLE reachability from destination:\n", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
      ); 
      red_print_graph(RT[w]); 
      #endif 
    #endif 
    
    RT[w] = red_role_euntil_bck(
      w, 
      path_exp, path, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      XI_SYNC_BULK, 
      weak_fairness_list, 
      flag_roles, 
      flag_polarity
    ); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time(
        "\nROLE FAIRNESS %s:%1d:%1d, After ROLE strong fairness progress.\n", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER, ROLE_FAIRNESS_STRONG_ITER
      ); 
      pcform(fl->fairness); 
      red_print_graph(RT[w]); 
/* 
      print_resources("Connecting strong fairness"); 
*/
      #endif 
    #endif 
  }
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "\ninconsistent RT_TOP %1d->%1d in red_fair_cycle_through_strong_fairness.\n", 
      orig_rttop, RT_TOP
    ); 	
    fflush(RED_OUT); 
    bk(0); 
  } 
  return(RT[w]); 
} 
  /* red_fair_cycle_through_strong_fairness() */ 
  
  
  
inline void	gfp_process_easy_strong(
  int				fair_cycle, 
  int				easy_state_strong, 
  struct ps_exp_type		*path_exp, 
  int				path,  
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_roles, 
  int				flag_polarity   
) { 
  struct red_type	*easy_timed; 
  int			time_path; 
  #ifdef RED_DEBUG_FXP_MODE
  int orig_rttop = RT_TOP; 
  #endif 

  gfp_guess_timeless(RT[easy_state_strong], 
    &(RT[easy_state_strong]), &easy_timed 
  ); 
    
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS 
    print_cpu_time(
      "\nROLE FAIRNESS %s:%1d, in gfp_process_easy_strong(), after splitting timeless", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      ROLE_FAIRNESS_ITER 
    ); 
    red_print_graph(RT[easy_state_strong]); 
    #endif 
  #endif 
  RT[easy_state_strong] = red_game_time_progress_bck(
    path_exp, 
    easy_state_strong, path, MASK_GAME_ROLES, 
    TYPE_TRUE // can assume that 
              // the destination is included in the path.
  ); 
  RT[easy_state_strong] = red_role_euntil_bck(
    easy_state_strong /* dest */,  
    path_exp, path, 
    SYNC_XTION, 
    SYNC_XTION_COUNT, 
    XI_SYNC_BULK, 
    weak_fairness_list, 
    flag_roles, 
    flag_polarity 
  ); 
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS 
    print_cpu_time(
      "\nROLE FAIRNESS %s:%1d, in gfp_process_easy_strong(), after backward timeless", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      ROLE_FAIRNESS_ITER 
    ); 
    red_print_graph(RT[easy_state_strong]); 
    #endif 
  #endif 
  RT[fair_cycle] = red_bop(AND, RT[fair_cycle], 
    red_complement(RT[easy_state_strong])
  ); 
  RT[fair_cycle] = red_hull_normalize(fair_cycle); 
  #ifdef RED_DEBUG_FXP_MODE 
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS 
    print_cpu_time(
      "\nROLE FAIRNESS %s:%1d, in gfp_process_easy_strong(), the remaining timed", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      ROLE_FAIRNESS_ITER 
    ); 
    red_print_graph(RT[fair_cycle]); 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_FXP_MODE
  if (orig_rttop != RT_TOP) { 
    print_cpu_time(
      "Error: the RT_TOP value (old:%1d-->new:%1d) is not consistent \n       in gfp_process_easy_strong()!\n", 
      orig_rttop, RT_TOP 
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
  #endif 
}
  /* gfp_process_easy_strong() */ 
  




struct reachable_return_type	rr_static; 

inline struct red_type	*gfp_zenook_no_strong_fairness( 
  int				dest, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  struct ps_fairness_link_type	*weak_fairness_list 
) { 
  int	flag_result, result; 
  
  RT[result = RT_TOP++] = red_precondition_sync_ITERATIVE( 
    &rr_static, 
    dest,  
    path_exp, path,  
    INDEX_FALSE, 
    NORM_FALSE, 
    NORM_FALSE, 
    SYNC_XTION, 
    SYNC_XTION_COUNT, 
    &flag_result, 
    TYPE_TRUE  
  );
  RT[result] = red_bop(OR, RT[result], 
    red_precondition_sync_bulk(
      &rr_static, 
      dest, 
      path_exp, path,  
      INDEX_FALSE, 
      RT[result], 
      NORM_FALSE, 
      XI_SYNC_BULK, 
      XI_SYNC_BULK_WITH_TRIGGERS, // an index to the RT stack 
      &flag_result, 
      TYPE_TRUE  
  ) ); 
  RT_TOP--; // result  
  return(RT[result]); 
} 
  /* gfp_zenook_no_strong_fairness() */ 
  
  
  
  
inline struct red_type	*gfp_general_fairness(
  struct ps_exp_type		*spec, 
  int				dest, 
  int				prev_fxp, 
  struct ps_exp_type		*path_exp, 
  int				path, 
  int 				flag_roles, 
  int				flag_polarity
) { 
  int	diff, orig_rttop = RT_TOP; 
  
  if (   CLOCK_COUNT 
      && (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK
      ) { 
    RT[dest] = crd_one_constraint(
      RT[dest], ZONE[0][ZENO_CLOCK], CLOCK_NEG_INFINITY
    ); 
    RT[dest] = red_game_time_progress_bck(
      path_exp, 
      dest, path, flag_roles, 
      TYPE_TRUE   
    ); 
    RT[dest] = red_hull_normalize(dest); 
    RT[dest] = red_role_euntil_bck(
      dest/* dest */,  
      path_exp, path, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      XI_SYNC_BULK, 
      spec->u.mexp.weak_fairness_list, 
      flag_roles, 
      flag_polarity 
    );
    RT[dest] = crd_one_constraint(
      RT[dest], ZONE[ZENO_CLOCK][0], 0
    );

    #ifdef RED_DEBUG_FXP_MODE 
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS 
      print_cpu_time(
        "ROLE FAIRNESS %s:%1d, before deactivating ZENO_CLOCK=%1d", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER, ZENO_CLOCK
      ); 
      red_print_graph(RT[dest]); 
      #endif 
    #endif 
    RT[dest] = red_time_clock_eliminate(RT[dest], ZENO_CLOCK); 
    #ifdef RED_DEBUG_FXP_MODE 
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS 
      print_cpu_time(
        "ROLE FAIRNESS %s:%1d, after strong non-Zeno progress", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER 
      ); 
      red_print_graph(RT[dest]); 
      #endif 
    #endif 

    RT[dest] = red_bop(AND, RT[dest], RT[prev_fxp]); 
    RT[dest] = red_subsume(RT[dest]);
    RT[dest] = red_hull_normalize(dest);
    RT[dest] = red_subsume(RT[dest]);
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time(
        "ROLE FAIRNESS %s:%1d, after Checking nonZeno requirement", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER
      ); 
      red_print_graph(RT[dest]);
      #endif 
    #endif 
  } 

  red_fair_cycle_through_strong_fairness( 
    spec, 
    dest /* dest */,  
    path_exp, 
    path, 
    spec->u.mexp.weak_fairness_list, 

    flag_roles,       
    flag_polarity
  ); 

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    print_cpu_time(
      "\nROLE FAIRNESS %s:%1d, a fair_cycle end, new RT[cur_fair_cycle=%1d]:\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      ROLE_FAIRNESS_ITER, dest
    );
    RT[dest] = red_hull_normalize(dest); 
    red_print_graph(RT[dest]);
    #endif 
  #endif 

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    /* We are just curious at what has been eliminated. 
     */ 
    print_cpu_time("\nNZF%1d: newly eliminated states for :\n", NZF);
    pcform(spec); 
    RT[diff = RT_TOP++] = red_complement(RT[dest]); 
    RT[diff] = red_bop(AND, RT[prev_fxp], RT[diff]); 
    RT[diff] = red_hull_normalize(diff); 
    red_print_graph(RT[diff]); 
    RT_TOP--; // diff 
    #endif 
  #endif 
  
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "\ninconsistent RT_TOP %1d->%1d in gfp_general_fairness.\n", 
      orig_rttop, RT_TOP
    ); 	
    fflush(RED_OUT); 
    bk(0); 
  } 
  return(RT[dest]); 
}
  /* gfp_general_fairness() */  










/* The invariance is that RT[share_discontinuity] is for RT[path]. 
 * One important restriction for the correct execution of the 
 * procedure is that path_start and path_stop together specify 
 * a consecutive range of RT frames such that 
 * path_stop = RT_TOP-1 at the time of the procedure invocation.  
 */ 
struct red_type	*role_fairness_bck( 
  struct ps_exp_type		*spec, 
  int				reset_inheritance, 
  int				path, 
  int				early_decision, 
  int				flag_roles, 
  int				flag_polarity, 
  int				flag_path_tctctl  
) {
  int				prev_fair_cycle, cur_fair_cycle, 
				token_strong_fairness, 
				fair_cycle, 
				orig_rttop = RT_TOP, 
				i, orig_time_progress, 
				easy_state_strong; 
  struct ps_fairness_link_type	*fl;
  struct ps_exp_type		*tail_exp; 

  #ifdef RED_DEBUG_FXP_MODE
  int orig_rttop = RT_TOP; 
  #endif 
  
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    print_cpu_time("\n===============================================\n"); 
    fprintf(RED_OUT, 
      "ROLE FAIRNESS %s, RT_TOP=%1d, Evaluating the fairness of :\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      RT_TOP
    ); 
    pcform(spec); 
    #endif 
  #endif 
 
  if (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
         == FLAG_ZENO_CYCLE_OK
      && spec->u.mexp.strong_fairness_count == 0 
      && spec->u.mexp.weak_fairness_count == 0
      ) { 
    return(RT[path]); 
  } 

  RT[fair_cycle = RT_TOP++] = RT[path]; 
  RT[easy_state_strong = RT_TOP++] = NORM_FALSE; 
  token_strong_fairness = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    print_cpu_time(
      "RT_TOP=%1d, after setting up the fairness for model\n", 
      RT_TOP
    ); 
    #endif 
  #endif 
  flag_path_tctctl = flag_path_tctctl 
  & setup_role_fairness_before_gfp(
      spec, 
      fair_cycle, 
      token_strong_fairness, 
      flag_polarity, 
      easy_state_strong 
    ); 
  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    print_cpu_time("ROLE FAIRNESS %s, For RT[fair_cycle=%1d]:\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      fair_cycle
    ); 
    red_print_graph(RT[fair_cycle]); 
    fprintf(RED_OUT, "ROLE FAIRNESS %s, For RT[weak_events=%1d]:\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      weak_events
    ); 
    red_print_graph(RT[weak_events]); 
    fprintf(RED_OUT, "ROLE FAIRNESS %s, For RT[weak_event_dest=%1d]:\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      weak_event_dest
    ); 
    red_print_graph(RT[weak_event_dest]); 
    #endif 
  #endif 

  switch (spec->type) { 
  case EXISTS_UNTIL: 
  case TYPE_GAME_SIM: 
    if (flag_path_tctctl) 
      tail_exp = PS_EXP_TRUE; 
    else 
      tail_exp = NULL; 
    break; 
  case EXISTS_ALWAYS: 
    if (flag_path_tctctl) 
      tail_exp = spec->u.mexp.path_child; 
    else 
      tail_exp = NULL; 
    break; 
  default: 
    fprintf(RED_OUT, "\nIllegal operator in spec role fairness.\n"); 
    fflush(RED_OUT); 
    exit(0); 
    break; 
  } 

  if (RT[easy_state_strong] != NORM_FALSE) { 
  // In this case, we have easy strong state fairness assumptions 
  // that have non-empty intersection. 
  // Then all backward reachability to this easy strong states are also 
  // strong fairness states.  
    gfp_process_easy_strong(
      fair_cycle, 	// side effect may happen to RT[fair_cycle] and  
      easy_state_strong, // RT[easy_state_strong].  
      tail_exp, 
      path, 
      spec->u.mexp.weak_fairness_list, 
      flag_roles, 
      flag_polarity   
    ); 
    fprintf(RED_OUT, "\nEasy fairness detected:\n"); 
/*
    red_print_graph(RT[easy_state_strong]); 
    fprintf(RED_OUT, "\nRemaining fair cycle: \n"); 
    red_print_graph(RT[fair_cycle]); 
*/
  } 
  else 
    fprintf(RED_OUT, "\nEasy fairness NOT detected:\n"); 
    
  RT[fair_cycle] = red_system_clocks_unbounded(RT[fair_cycle]); 
  RT[cur_fair_cycle = RT_TOP++] = RT[fair_cycle]; 
  RT[prev_fair_cycle = RT_TOP++] = NORM_FALSE; 
  for (ROLE_FAIRNESS_ITER = 1; 
       RT[cur_fair_cycle] != RT[prev_fair_cycle]; 
       ROLE_FAIRNESS_ITER++
       ) {
    int	dest; 

    /* Check if early decision has happend.
     */ 
    if (red_bop(AND, RT[cur_fair_cycle], RT[early_decision]) == NORM_FALSE) { 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time(
          "\nROLE FAIRNESS %s:%1d, Early termination of greatest fixpoint.\n", 
          role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
          ROLE_FAIRNESS_ITER
        ); 
        fflush(RED_OUT); 
        #endif 
      #endif 
      spec->exp_status = spec->exp_status | FLAG_GFP_EARLY_DECISION; 
      spec->u.mexp.red_early_decision_maker = RT[early_decision]; 
      red_mark(RT[early_decision], FLAG_GC_USER_STATIC1); 
      break; 
    } 

    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time(
        "\nROLE FAIRNESS %s:%1d, after checking for early decision\n", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        ROLE_FAIRNESS_ITER
      ); 
/* 
    print_resources("NZF"); 
*/
      #endif 
    #endif 

    RT[prev_fair_cycle] = RT[cur_fair_cycle]; 
    if (   (   CLOCK_COUNT == 0 
            || (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               == FLAG_ZENO_CYCLE_OK
            )
        && spec->u.mexp.strong_fairness_list == NULL
        ) { 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time("\nRF %1d, before gfp_zenook_no_strong_fairness()"); 
        #endif 
      #endif 
      RT[cur_fair_cycle] = gfp_zenook_no_strong_fairness( 
        cur_fair_cycle, 
        tail_exp, 
        fair_cycle, // path,  
        spec->u.mexp.weak_fairness_list 
      ); 
      #ifdef RED_DEBUG_FXP_MODE
        #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
        print_cpu_time("\nRF %1d, after gfp_zenook_no_strong_fairness()"); 
        #endif 
      #endif 
    } 
    else { 
      RT[cur_fair_cycle] = gfp_general_fairness( 
        spec, 
        cur_fair_cycle, 
        prev_fair_cycle, 
        tail_exp, 
        fair_cycle, // path, 
	flag_roles, 
	flag_polarity
      ); 
    } 
    RT[cur_fair_cycle] = red_bop(AND, 
      RT[cur_fair_cycle], RT[prev_fair_cycle]
    ); 
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time("\nRF %1d, after an iteration()"); 
      red_print_graph(RT[cur_fair_cycle]); 
      #endif 
    #endif 
  } 
  if (RT[path] == RT[fair_cycle]) { 
    RT[fair_cycle] = RT[cur_fair_cycle]; 
    RT_TOP--; /* prev_fair_cycle */ 
    RT_TOP--; // cur_fair_cycle 
    release_gc_token(token_strong_fairness, &TOKEN_PROTECTION_LIST); 
  
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time("\n===============================================\n"); 
      fprintf(RED_OUT, "ROLE FAIRNESS %s, RT_TOP:%1d->%1d, after the fairness GFP :\n", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        orig_rttop, RT_TOP
      ); 
      pcform(spec); 
/*
      print_resources("\nThe result of fair path evaluation"); 
*/
      red_print_graph(RT[fair_cycle]); 
      #endif 
    #endif 
  }
  else { 
    RT[fair_cycle] = RT[cur_fair_cycle]; 
    RT_TOP--; /* prev_fair_cycle */ 
    RT_TOP--; // cur_fair_cycle 
    release_gc_token(token_strong_fairness, &TOKEN_PROTECTION_LIST); 
  
    #ifdef RED_DEBUG_FXP_MODE
      #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
      print_cpu_time("\n===============================================\n"); 
      fprintf(RED_OUT, "ROLE FAIRNESS %s, RT_TOP:%1d->%1d, after the fairness GFP :\n", 
        role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
        orig_rttop, RT_TOP
      ); 
      pcform(spec); 
/*
      print_resources("\nThe result of fair path evaluation"); 
*/
      red_print_graph(RT[fair_cycle]); 
      #endif 
    print_cpu_time("\nRF final: before final role_euntil_bck()"); 
    #endif 

    RT[fair_cycle] = red_role_euntil_bck(
      fair_cycle, 
      tail_exp, 
      path, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      XI_SYNC_BULK, 
      spec->u.mexp.weak_fairness_list, 
      flag_roles, 
      flag_polarity 
    ); 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nRF final: after final role_euntil_bck()"); 
    #endif 
  }
  RT[fair_cycle] = red_bop(OR, RT[fair_cycle], RT[easy_state_strong]); 
  RT_TOP--; // easy_state_strong  

  #ifdef RED_DEBUG_FXP_MODE
    #ifdef RED_DEBUG_FXP_MODE_FAIRNESS
    print_cpu_time("\n===============================================\n"); 
    fprintf(RED_OUT, "ROLE FAIRNESS %s, leaving the fairness of :\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)) 
    ); 
/*
    fprintf(RED_OUT, "ROLE FAIRNESS %s, RT_TOP:%1d->%1d, leaving the fairness of :\n", 
      role_name(flag_roles & (FLAG_GAME_MODL | FLAG_GAME_SPEC)), 
      orig_rttop, RT_TOP
    ); 
*/
    pcform(spec); 
/*
    print_resources("\nThe result of fair path evaluation"); 
*/
    red_print_graph(RT[fair_cycle]); 
    #endif 
  #endif 
  
  RT_TOP--; /* fair_cycle */ 

//  #ifdef RED_DEBUG_FXP_MODE
  if (orig_rttop != RT_TOP) { 
    print_cpu_time(
      "Error: inconsisitent RT_TOP %1d->%1d in role_fairness_bck()!\n", 
      orig_rttop, RT_TOP 
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
//  #endif 
  
  return(RT[fair_cycle]);
}
  /* role_fairness_bck() */ 




struct red_type	*red_fair_tail(
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			fxp, 
  int			early_decision, 
  int			flag_polarity, 
  int			flag_path_tctctl 	
) { 
  struct red_type	*result; 

  if (   spec->u.mexp.weak_fairness_count 
      || spec->u.mexp.strong_fairness_count 
      ) { 
    result = role_fairness_bck(
      spec, 
      reset_inheritance, 
      fxp, // path 
      early_decision, 
      MASK_GAME_ROLES, 
      flag_polarity, 
      flag_path_tctctl 
    ); 
/*
      print_resources("Exists UNTIL after fairness bck"); 
*/
  } 
  else if (GSTATUS[INDEX_ZENO_CYCLE] & FLAG_ZENO_CYCLE_OK) { 
    result = NORM_NO_RESTRICTION; 
  } 
  else if ((GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) 
           == FLAG_ROOT_UAPPROX
           ) { 
    if (RT[INDEX_NONZENO_BY_FAIRNESS_TERMINATION] == NULL) { 
      RT[INDEX_NONZENO_BY_FAIRNESS_TERMINATION] = role_fairness_bck(
	spec, 
	reset_inheritance, 
	fxp, 
	early_decision, 
        MASK_GAME_ROLES, 
	flag_polarity, 
	flag_path_tctctl 
      ); 
      red_mark(RT[INDEX_NONZENO_BY_FAIRNESS_TERMINATION], FLAG_GC_STABLE); 
    } 
    result = RT[INDEX_NONZENO_BY_FAIRNESS_TERMINATION]; 
  } 
  else { 
    result = RT[INDEX_NONZENO_FROM_DESCRIPTION]; 
  } 
  return(result); 
} 
  /* red_fair_tail() */  



struct red_type	*exists_modal_clock_at_zero(int	d) { 
  // Now existentially quantify the result with mc==0. 
  RT[d] = crd_one_constraint(RT[d], ZONE[MODAL_CLOCK][0], 0); 
  RT[d] = crd_one_constraint(RT[d], ZONE[0][MODAL_CLOCK], 0); 
  RT[d] = red_time_clock_eliminate(RT[d], MODAL_CLOCK); 
  return(RT[d]); 
}
  /* exists_modal_clock_at_zero() */   
  
  
  

inline void	push_for_time_convex(int *orig_time_progress_ptr) {
  *orig_time_progress_ptr = GSTATUS[INDEX_TIME_PROGRESS]; 
  GSTATUS[INDEX_TIME_PROGRESS] 
  = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
  | FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
}
  /* push_for_time_convex() */ 
  
  
  
inline void	pop_for_time_convex(int orig_time_progress) {
  GSTATUS[INDEX_TIME_PROGRESS] = orig_time_progress; 
}
  /* pop_for_time_convex() */ 




  
  
inline struct red_type	*red_umprimed_invariance_from_event_invariance(
  struct red_type	*d
) { 
  return(red_lower_all_primed(
    red_type_eliminate(red_bop(AND, RT[NULL_EVENTS], d), TYPE_SYNCHRONIZER)
  ) ); 
} 
  /* red_umprimed_invariance_from_event_invariance() */  


inline struct red_type	*red_primed_invariance_from_event_invariance(
  struct red_type	*d
) { 
  return(red_lift_all_umprimed(
    red_type_eliminate(red_bop(AND, RT[NULL_EVENTS], d), TYPE_SYNCHRONIZER)
  ) ); 
} 
  /* red_primed_invariance_from_event_invariance() */  



int			count_label_bck = 0; 
struct ps_exp_type	*AUX_EXISTS_ALWAYS; 


struct ps_exp_type	*aux_event_exists_always(
  struct ps_exp_type	*spec, 
  struct red_type	*red_path_child
) { 
  struct ps_fairness_link_type	*fl; 
      
  if (spec->u.mexp.event_restriction == NULL) { 
    return(spec); 
  }

  AUX_EXISTS_ALWAYS = ps_exp_alloc(EXISTS_ALWAYS); 
  *AUX_EXISTS_ALWAYS = *spec; 
  fl 
  = AUX_EXISTS_ALWAYS->u.mexp.weak_fairness_list 
  = (struct ps_fairness_link_type *) 
    malloc(sizeof(struct ps_fairness_link_type)); 
  fl->status = 0; 
  if (spec->u.mexp.time_ub == CLOCK_POS_INFINITY) {
    AUX_EXISTS_ALWAYS->u.mexp.weak_fairness_count++; 
    fl->next_ps_fairness_link = spec->u.mexp.weak_fairness_list; 
  }
  else { 
    AUX_EXISTS_ALWAYS->u.mexp.weak_fairness_count = 1; 
    fl->next_ps_fairness_link = NULL; 
  } 
  fl->red_fairness = NORM_NO_RESTRICTION; 
  fl->fairness = ps_exp_alloc(LINEAR_EVENT); 
  fl->fairness->u.eexp.postcond_exp = spec->u.mexp.path_child; 
  fl->fairness->u.eexp.precond_exp = PS_EXP_TRUE; 
  fl->fairness->u.eexp.event_exp = spec->u.mexp.event_restriction; 
  fl->fairness->u.eexp.red_early_decision_maker = NORM_NO_RESTRICTION; 
  fl->fairness->u.eexp.red_sync_bulk_from_event_exp 
  = spec->u.mexp.red_xi_restriction; 
  fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp = NORM_FALSE; 
  fl->fairness->u.eexp.red_postcond = red_path_child;  
  fl->fairness->u.eexp.red_precond = NORM_NO_RESTRICTION;
  
  return(AUX_EXISTS_ALWAYS); 
} 
  /* aux_event_exists_always() */ 




inline struct red_type	*red_exists_always_no_segmented_evaluation( 
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			assumption, 
  int			early_decision,  
  int			flag_polarity 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
) { 
  int	notlive, result, events, 
	flag_path_tctctl, 
	flag_modal_clock = TYPE_FALSE, 
	local_count_label = count_label_bck, 
	orig_time_progress; 

//  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nlabel %1d, EG, no segmented EA\n", local_count_label); 
//  #endif 
  RT[notlive = RT_TOP++] = red_label_bck(
    spec->u.mexp.path_child, reset_inheritance, 
    assumption,   
    assumption, flag_polarity
  ); 
  if (spec->u.mexp.time_lb <= spec->u.mexp.time_ub) { 
    if (spec->u.mexp.time_ub < CLOCK_POS_INFINITY) {
      RT[notlive] = red_bop(OR, RT[notlive], 
        crd_one_constraint(RT[assumption], 
//        crd_atom( // one_constraint(RT[assumption], 
          ZONE[0][MODAL_CLOCK], -1-spec->u.mexp.time_ub
      ) ); 
      flag_modal_clock = TYPE_TRUE; 
    }
    if (spec->u.mexp.time_lb > 0) { 
      RT[notlive] = red_bop(OR, RT[notlive], 
        crd_one_constraint(RT[assumption], 
//        crd_atom( // one_constraint(RT[assumption], 
          ZONE[MODAL_CLOCK][0], -1+spec->u.mexp.time_lb 
      ) ); 
      flag_modal_clock = TYPE_TRUE; 
    } 
  }
  else if (   (spec->u.mexp.time_lb % 2) 
           && spec->u.mexp.time_lb == spec->u.mexp.time_ub + 2
           ) { 
  // This is the case of NEQ
    struct red_type	*conj; 
    
    conj = crd_one_constraint(
      crd_one_constraint(RT[assumption], 
//      crd_atom(  
        ZONE[0][MODAL_CLOCK], 1-spec->u.mexp.time_ub
      ),  
      ZONE[MODAL_CLOCK][0], -1+spec->u.mexp.time_ub
    ); 
    RT[notlive] = red_bop(OR, RT[notlive], conj); 
    flag_modal_clock = TYPE_TRUE; 
  }
  flag_path_tctctl = spec->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM;
  if (spec->exp_status & FLAG_TAIL_CONVEXITY_EVALUATION) { 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d, EU, checking tctctl, notlive convexity\n", local_count_label); 
    #endif 
    push_for_time_convex(&orig_time_progress); 
  } 
  
  RT[notlive] = role_fairness_bck(
    spec, 
    reset_inheritance, 
    notlive, 
    early_decision,  
    MASK_GAME_ROLES, 
    flag_polarity, 
    flag_path_tctctl  
  ); 
  result = notlive; 
  RT[result] = red_bop(AND, RT[result], RT[assumption]); 
  if (flag_modal_clock == TYPE_TRUE)
    RT[result] = exists_modal_clock_at_zero(result); 
  if (spec->exp_status & FLAG_TAIL_CONVEXITY_EVALUATION) { 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d, EU, checking tctctl, notlive convexity\n", local_count_label); 
    #endif 
    pop_for_time_convex(orig_time_progress); 
  } 
  RT_TOP--; // notlive 
 
  print_resources("End of EXACT analysis of e often"); 

  return(RT[result]); 
}
  /* red_exists_always_no_segmented_evaluation() */ 
  





inline struct red_type	*red_exists_always_segmented_evaluation_head(
  struct ps_exp_type	*spec, 
  struct ps_exp_type	*path_exp, 			
  int			local_assumption, 
  int			mid, 
  int			flag_polarity 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
) {  
  if (spec->u.mexp.time_lb > 0) { /* case [0,d] or [0,d) */ 
    int	time_path, local_count_label = count_label_bck;  

    // In this case, there is no head segment. 
    //
    RT[time_path = RT_TOP++] = crd_one_constraint(
      RT[REFINED_GLOBAL_INVARIANCE], 
      ZONE[MODAL_CLOCK][0], spec->u.mexp.time_lb-1
    ); 
    RT[mid] = red_game_time_progress_bck(
      path_exp, 
      mid, time_path, MASK_GAME_ROLES, 
      TYPE_FALSE // can assume that 
               // the destination is included in the path.
    ); 
    RT_TOP--; // time_path 
    
    RT[mid] = crd_one_constraint(RT[mid], 
      ZONE[MODAL_CLOCK][0], spec->u.mexp.time_lb-1
    ); 
    RT[mid] = red_hull_normalize(mid); 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time(
      "\nlabel %1d: EG <c,d>, progress to the head segment.", 
      local_count_label
    );             
    fprintf(RED_OUT, "RT[mid=%1d]:\n", mid); 
    red_print_graph(RT[mid]); 
    #endif 

    // It is interesting to know that in this case, since 
    // the first interval is with no restriction, 
    // the path actually includes the destination in the time progress 
    // procedure. 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nEG UBFIN: before euntil of the head seg"); 
    #endif 
    
    RT[mid] = red_role_euntil_bck(
      mid, 
      path_exp, 
      local_assumption, 
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      XI_SYNC_BULK, 
      NULL, 
      MASK_GAME_ROLES, 
      flag_polarity
    ); 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d: EG <c,d>, end the head segment.", 
      local_count_label
    );             
    fprintf(RED_OUT, "RT[mid=%1d]:\n", mid); 
    red_print_graph(RT[mid]); 
    #endif 
  }
  
  return(RT[mid]); 
}
  /* red_exists_always_segmented_evaluation_head() */ 




inline struct red_type	*red_exists_always_segmented_evaluation_uboo(
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			local_assumption, 
  int			early_decision,  
  int			flag_polarity, 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
  int			flag_path_tctctl 
) { 
  int	tail, result,  
	local_count_label = count_label_bck, 
	orig_time_progress; 

  RT[tail = RT_TOP++] = red_label_bck(
    spec->u.mexp.path_child, reset_inheritance, 
    local_assumption,  
    local_assumption, flag_polarity
  ); 
  RT[tail] = role_fairness_bck(
    aux_event_exists_always(spec, RT[tail]), 
    reset_inheritance, 
    tail, 
    early_decision, 
    MASK_GAME_ROLES, 
    flag_polarity, 
    flag_path_tctctl 
  ); 
  RT[tail] = red_exists_always_segmented_evaluation_head(
    spec, 
    (flag_path_tctctl) ? spec->u.mexp.path_child:NULL, // path_exp 
    local_assumption, 
    tail, 
    flag_polarity
  ); 
  RT[result = tail] = exists_modal_clock_at_zero(tail); 

  RT_TOP = RT_TOP-1; // result = tail 
  
  return(RT[result]); 
}
  /* red_exists_always_segmented_evaluation_uboo() */ 
  
  
  
  

inline struct red_type	*red_exists_always_segmented_evaluation_ubfin(
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			local_assumption, 
  int			early_decision,  
  int			flag_polarity, 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
  int			flag_path_tctctl 
) { 
  int	tail, result, local_path, notlive, 
	local_count_label = count_label_bck, 
	orig_time_progress; 

  // In this case, there is a tail segment that is irrelevant 
  // to the path child of the modal operator. 
  RT[tail = RT_TOP++] = role_fairness_bck(
    spec, reset_inheritance, 
    local_assumption, 
    early_decision, 
    MASK_GAME_ROLES, 
    flag_polarity, 
    flag_path_tctctl 
  ); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nEG UBFIN: after role fairness bck()"); 
  #endif 
  
  // Now we start processing the middle segment. 
//  This is not necessary since the procedure is called with this assumption.
//  if (spec->u.mexp.time_ub < CLOCK_POS_INFINITY) 
  RT[tail] = crd_one_constraint(RT[tail], 
    ZONE[0][MODAL_CLOCK], -1-spec->u.mexp.time_ub
  ); 

  RT[local_path = RT_TOP++] = red_label_bck(
    spec->u.mexp.path_child, reset_inheritance, 
    local_assumption,   
    local_assumption, flag_polarity
  ); 
  RT[local_path] = crd_one_constraint(RT[local_path], 
    ZONE[MODAL_CLOCK][0], spec->u.mexp.time_ub
  ); 
  RT[local_path] = crd_one_constraint(RT[local_path], 
    ZONE[0][MODAL_CLOCK], -spec->u.mexp.time_lb
  ); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nEG UBFIN: before time progress of the middle seg"); 
  #endif 
  
  RT[tail] = red_game_time_progress_bck(
    (flag_path_tctctl) ? spec->u.mexp.path_child : NULL, 
    tail, local_path, MASK_GAME_ROLES, 
    TYPE_FALSE // can assume that 
               // the destination is included in the path.
  ); 
  RT[tail] = crd_one_constraint(RT[tail], 
    ZONE[MODAL_CLOCK][0], spec->u.mexp.time_ub
  ); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("\nEG UBFIN: before euntil of the middle seg"); 
  red_print_graph(RT[tail]); 
  #endif 
  
  AUX_EXISTS_ALWAYS = aux_event_exists_always(spec, RT[local_path]); 
  RT[tail] = red_role_euntil_bck(
    tail, // dest 
    (flag_path_tctctl) ? spec->u.mexp.path_child:NULL, // path_exp 
    local_path,  // path 
    SYNC_XTION, 
    SYNC_XTION_COUNT, 
    XI_SYNC_BULK, 
    AUX_EXISTS_ALWAYS->u.mexp.weak_fairness_list, 
    MASK_GAME_ROLES, 
    flag_polarity
  ); 
  RT_TOP--; // local_path 
  
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time(
    "\nlabel %1d: EG <c,d>, before the head segment.\n", 
    local_count_label
  );             
  red_print_graph(RT[tail]); 
  #endif 

  RT[tail] = red_exists_always_segmented_evaluation_head(
    spec, 
    (flag_path_tctctl) ? spec->u.mexp.path_child:NULL, // path_exp 
    local_assumption, 
    tail, 
    flag_polarity
  ); 

  // Now existentially quantify the result with mc==0. 
            
  RT[result = tail] = exists_modal_clock_at_zero(tail); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time(
    "\nlabel %1d: EG <c,d>, exists modal clock.\n", 
    local_count_label
  );             
  red_print_graph(RT[tail]); 
  #endif 

  RT_TOP--; // tail = result 

  return(RT[result]); 
}
  /* red_exists_always_segmented_evaluation_ubfin() */ 
  
  
  

inline struct red_type	*red_exists_always_segmented_evaluation( 
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			assumption, 
  int			early_decision,  
  int			flag_polarity 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
) { 
  int			tail, local_path, 
			local_assumption,  // This is the assumption. 
			local_count_label = count_label_bck, 
			orig_time_progress, 
			flag_path_tctctl 
			= spec->u.mexp.path_child->exp_status
			& FLAG_TCTCTL_SUBFORM; 
  struct red_type	*result; 

  /* In general, there are three segments to evaluate successively. 
   * The last is the tail. 
   * Then we have a middle path. 
   * Then we have the head path. 
   * Depending the values of time_lb and time_ub, the segments may 
   * merge. 
   */
  flag_path_tctctl = spec->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM; 
  RT[local_assumption = RT_TOP++] = RT[assumption];  
  if (   spec->u.mexp.time_lb == 0 
      && spec->u.mexp.time_ub == CLOCK_POS_INFINITY
      ) { 
  // This is the degenerate case with only one segment. 
    RT[tail = RT_TOP++] = red_label_bck(
      spec->u.mexp.path_child, reset_inheritance, 
      local_assumption,  
      local_assumption, flag_polarity
    ); 
    result = role_fairness_bck(
      aux_event_exists_always(spec, RT[tail]), 
      reset_inheritance, 
      tail, 
      early_decision, 
      MASK_GAME_ROLES, 
      flag_polarity, 
      flag_path_tctctl 
    ); 
    RT_TOP--; // tail 
  } 
  else if (spec->u.mexp.time_ub == CLOCK_POS_INFINITY) {
  // This is the case with a nontrivial tail segment. 
  // Nontriviality means that we need to enforce the always property 
  // in the segment. 
    result = red_exists_always_segmented_evaluation_uboo(
      spec, 
      reset_inheritance, 
      tail, 
      early_decision,  
      flag_polarity, 	// -1 for under-approx
			// 0 for no-approx 
			// 1 for over-approx 
      flag_path_tctctl 
    ); 
  } 
  else { 
  // This is the case with a nontrivial head or middle segment. 
    result = red_exists_always_segmented_evaluation_ubfin(
      spec, 
      reset_inheritance, 
      local_assumption, 
      early_decision,  
      flag_polarity, 	// -1 for under-approx
			// 0 for no-approx 
			// 1 for over-approx 
      flag_path_tctctl 
    ); 
  } 
  RT_TOP--; // local_assumption 
  return(result); 
} 
  /* red_exists_always_segmented_evaluation() */ 








struct red_type	*red_label_bck(
  struct ps_exp_type	*spec, 
  int			reset_inheritance, 
  int			assumption, 
  int			early_decision,  
  int			flag_polarity 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
) {
  int			ci, fair, tail, result, new_reset_inheritance, 
  			local_path, local_assumption, events, 
  			dest, new_early_decision, 
			tmp_xi_bulk, tmp_xi_bulk_with_trigger, 
  			flag_path_tctctl, flag_tail_tctctl, 
  			orig_time_progress, orig_convex_start, orig_convex_stop; 
  struct ps_bunit_type	*pbu;
  struct red_type	*child;

  #ifdef RED_DEBUG_FXP_MODE
  int	orig_rttop = RT_TOP, local_count_label; 

  local_count_label = ++count_label_bck; 
  print_cpu_time(
    "\nlabel %1d: Entering red_label_bck() for :", 
    count_label_bck
  ); 
  pcform(spec); 
  fprintf(RED_OUT, "\n"); 
  #endif   
  
  switch (spec->type) {
  case RED:
    RT[result = RT_TOP++] = red_bop(AND, RT[assumption], RT[reset_inheritance]);
    RT[result] = red_bop(AND, RT[result], spec->u.rpred.red);
    break;
  case AND:
    RT[result = RT_TOP++] = NORM_NO_RESTRICTION;
    if (GSTATUS[INDEX_GFP_NO_EARLY_DECISION] & FLAG_GFP_NO_EARLY_DECISION)
      new_early_decision = early_decision;
    else {
      RT[new_early_decision = RT_TOP++] = RT[early_decision];
      for (ci = spec->u.bexp.len, pbu = spec->u.bexp.blist; 
           ci; 
           ci--, pbu = pbu->bnext
           ) {
        if (pbu->subexp->type == RED) {
      	  RT[new_early_decision] = red_bop(AND, RT[new_early_decision], pbu->subexp->u.rpred.red);
        }
      }
    }
    for (ci = spec->u.bexp.len, pbu = spec->u.bexp.blist; 
         ci; 
         ci--, pbu = pbu->bnext
         ) {
      child = red_label_bck(
        pbu->subexp, reset_inheritance, 
        assumption, 
	new_early_decision, flag_polarity
      );
      if (pbu->subexp->type != RED && ci > 1)
	RT[new_early_decision] = red_bop(AND, RT[new_early_decision], child);
      RT[result] = red_bop(AND, RT[result], child);
    }
    if (!(GSTATUS[INDEX_GFP_NO_EARLY_DECISION] & FLAG_GFP_NO_EARLY_DECISION))
      RT_TOP--; /* new_early_decision */
    if (CLOCK_COUNT > 1)
      red_abs(result, flag_polarity);
    break;
  case OR:
    RT[result = RT_TOP++] = NORM_FALSE;
    for (ci = spec->u.bexp.len, pbu = spec->u.bexp.blist; 
    	 ci; 
    	 ci--, pbu = pbu->bnext
    	 ) {
      child = red_label_bck(
	pbu->subexp, 
	reset_inheritance, 
	assumption,   
	early_decision, 
	flag_polarity
      );
      RT[result] = red_bop(OR, RT[result], child);
    }
    red_abs(result, flag_polarity);
    break;
  case NOT:
    child = red_label_bck(
		spec->u.bexp.blist->subexp, 
		reset_inheritance, 
		assumption,   
		REFINED_GLOBAL_INVARIANCE, 
		-1*flag_polarity
		);
    RT[result = RT_TOP++] 
    = red_bop(AND, RT[assumption], red_complement(child));
    RT[result] = red_bop(AND, RT[result], RT[early_decision]); 
    if (CLOCK_COUNT > 1) {
      RT[result] = red_hull_normalize(result);
      red_abs(result, flag_polarity);
    }
    break;
  case RESET:
    ci = spec->u.reset.clock_index;
/*
    print_cpu_time("RESET CLOCK %1d at vi = %1d: %s\n", ci, CLOCK[ci], VAR[CLOCK[ci]].NAME);
*/
    RT[new_reset_inheritance = RT_TOP++] 
    = crd_one_constraint(RT[reset_inheritance], ZONE[0][ci], 0);
/*
    print_cpu_time("1st printing MAX RT Height %1d in RESET\n", MAX_RT_HEIGHT);
*/
    if (GSTATUS[INDEX_GFP_NO_EARLY_DECISION] & FLAG_GFP_NO_EARLY_DECISION)
      new_early_decision = early_decision;
    else
      RT[new_early_decision = RT_TOP++] 
      = crd_one_constraint(RT[early_decision], ZONE[ci][0], 0);
    child = red_label_bck(
      spec->u.reset.child, 
      new_reset_inheritance, 
      assumption, 
      new_early_decision, 
      flag_polarity
    );
    if (!(GSTATUS[INDEX_GFP_NO_EARLY_DECISION] & FLAG_GFP_NO_EARLY_DECISION))
      RT_TOP--; /* new_early_decision */
/*
    print_cpu_time("2nd printing MAX RT Height %1d in RESET\n", MAX_RT_HEIGHT);
*/
    RT_TOP--; /* new_reset_inheritance */ 
    RT[result = RT_TOP++] = crd_one_constraint(child, ZONE[ci][0], 0);
//    RT[result] = red_hull_normalize(result);
    RT[result] = red_time_clock_eliminate(RT[result], ci);
    break; 

  case EXISTS_UNTIL :

    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d, EU\n", local_count_label); 
    print_resources("Exists UNTIL before fairness bck"); 
    pcform(spec); 
    fflush(RED_OUT); 
    #endif 
    /* Now first calculate the tail in consideration of 
     * the convexity checking efficiency. 
     */ 
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d, EU, no checking tctctl\n", local_count_label); 
    #endif 
    tail = RT_TOP++; 
    flag_path_tctctl = spec->u.mexp.path_child->exp_status & FLAG_TCTCTL_SUBFORM;
    switch (GSTATUS[INDEX_TIME_MODE_SHAPES] & MASK_TIME_MODE_SHAPES) {
    case FLAG_TIME_MODE_SOME_TCONCAVE: 
      flag_tail_tctctl = 0; 
      break;
    case FLAG_TIME_MODE_ALL_TCONVEX: 
      flag_tail_tctctl = FLAG_TCTCTL_SUBFORM;
      break; 
    } 
    RT[local_assumption = RT_TOP++] = RT[assumption];  
    RT[tail] = red_fair_tail( 
      spec, 
      reset_inheritance, 
      local_assumption, 
      local_assumption, 
      flag_polarity, 
      flag_tail_tctctl 
    ); 

    RT[result = RT_TOP++] = NORM_NO_RESTRICTION; 
    RT[result] = red_label_bck(
      spec->u.mexp.dest_child, 
      reset_inheritance, 
      local_assumption,  
      result, 
      flag_polarity
    );
    RT[tail] = red_bop(AND, RT[tail], RT[result]); 
    RT_TOP--; // result 
    
    RT[local_path = RT_TOP++] = red_label_bck(
      spec->u.mexp.path_child, 
      reset_inheritance, 
      local_assumption,  
      local_assumption, 
      flag_polarity
    ); 
    if (spec->u.mexp.event_restriction) { 
      RT[tail] = red_role_event_precondition( 
        spec->u.mexp.event_restriction, 
        spec->u.mexp.red_xi_restriction, 
        NORM_NO_RESTRICTION, 
        tail, 
        spec->u.mexp.path_child, 
        
        local_path, 
        NORM_FALSE, 
        NORM_FALSE, 
        SYNC_XTION, 
        SYNC_XTION_COUNT, 
        
        XI_SYNC_BULK, 
        NULL, 
        MASK_GAME_ROLES, 
        0, 
        flag_polarity, 
        
        TYPE_FALSE 
      ); 
    }
    if (spec->u.mexp.time_ub < CLOCK_POS_INFINITY)  
      RT[tail] = crd_one_constraint(
        RT[tail], ZONE[MODAL_CLOCK][0], spec->u.mexp.time_ub
      ); 
    if (spec->u.mexp.time_lb > 0) 
      RT[tail] = crd_one_constraint(
        RT[tail], ZONE[0][MODAL_CLOCK], -1*spec->u.mexp.time_lb
      );             


    // In this case, the timing constraint has already been compiled 
    // into the destination constraint.  
    // So we do not have to add in the destination constraint on line. 
    // 
/*
    print_resources("Exists UNTIL after destination bck"); 
*/ 
    RT[tail] = red_game_time_progress_bck(
      (flag_path_tctctl) ? spec->u.mexp.path_child:NULL, 
      tail, local_path, MASK_GAME_ROLES, 
      TYPE_FALSE // cannot assume that 
                 // the destination is included in the path.
    ); 

    RT[tail] = red_role_euntil_bck(
      tail, 
      (flag_path_tctctl) ? spec->u.mexp.path_child:NULL, 
      local_path,  
      SYNC_XTION, 
      SYNC_XTION_COUNT, 
      XI_SYNC_BULK, 
      NULL, 
      MASK_GAME_ROLES, 
      flag_polarity
    ); 
    RT_TOP--; // local_path 
    RT_TOP--; // local_assumption 
    // Now existentially quantify the result with mc==0. 
    RT[result = tail] = exists_modal_clock_at_zero(tail);
    result = tail; 
    break;

  case EXISTS_ALWAYS:
    #ifdef RED_DEBUG_FXP_MODE
    print_cpu_time("\nlabel %1d, EG\n", local_count_label); 
/* 
    print_resources("Exists Always"); 
    pcform(spec); 
    fflush(RED_OUT); 
*/
/* 
    print_cpu_time("EXACT analysis in Exists Always:\n");
*/  
    #endif 
    
    switch (GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_ANALYSIS) { 
    case FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED: 
      /* In general, there are three segments to evaluate successively. 
       * The last is the tail. 
       * Then we have a middle path. 
       * Then we have the head path. 
       * Depending the values of time_lb and time_ub, the segments may 
       * merge. 
       */
      if (spec->u.mexp.time_lb <= spec->u.mexp.time_ub) {  
        RT[result = RT_TOP++] = red_exists_always_segmented_evaluation(
          spec, 
          reset_inheritance, 
          assumption, 
          early_decision,  
          flag_polarity 	// -1 for under-approx
				// 0 for no-approx 
				// 1 for over-approx 
        ); 
        break; 
      }
                  
    case FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL: 
    case FLAG_TIME_PROGRESS_ANALYSIS_NONE: 
      RT[result = RT_TOP++] = red_exists_always_no_segmented_evaluation( 
        spec, 
        reset_inheritance, 
        assumption, 
        early_decision,  
        flag_polarity 	// -1 for under-approx
					// 0 for no-approx 
					// 1 for over-approx 
      ); 
      break; 

    } 
    break;
    

  default:
    print_cpu_time("\nBug: Illegal specification type: %1d during model-checking.\n", spec->type);
    fflush(RED_OUT);
    bk(0);
  }

  RT[result] = red_bop(AND, RT[result], RT[early_decision]); 
/*
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("label %d:%1d->%1d, normalization before leaving the red_label_bck() for :\n", 
    local_count_label, orig_rttop, RT_TOP
  ); 
  pcform(spec); 
  red_print_graph(RT[result]);
  #endif 
*/  
  RT[result] = red_hull_normalize(result); 
  #ifdef RED_DEBUG_FXP_MODE
  print_cpu_time("label %1d:%1d->%1d, \nleaving red_label_bck() for :", 
    local_count_label, orig_rttop, RT_TOP
  ); 
  pcform(spec); 
  fprintf(RED_OUT, "\n"); 
  red_print_graph(RT[result]);
  #endif 
  
  red_mark(RT[result], FLAG_GC_USER_STATIC1); 

  RT_TOP--; /* result */

  #ifdef RED_DEBUG_FXP_MODE
  if (orig_rttop != RT_TOP) { 
    print_cpu_time("Error: the RT_TOP value is not consistent in red_label_bck()!\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  #endif 

  return(spec->diagram_label = RT[result]);
}
/* red_label_bck() */










struct model_check_return_type	*red_model_chk(
  int			init, 
  int			path, 
  struct ps_exp_type	*nspec
) { 
  int					si, result, orig_time_progress, 
  					local_path; 
  struct model_check_return_type	*mr; 
  
  mr = (struct model_check_return_type *) 
    malloc(sizeof(struct model_check_return_type)); 
  mr->status = 0; 

  mr->neg_formula = nspec; 
  mr->initial_state_diagram = RT[init]; 
  red_mark(RT[init], FLAG_GC_USER_STATIC1); 
  
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[NULL_EVENTS = RT_TOP++] = NORM_NO_RESTRICTION; 
  for (si = 0; si < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; si++) 
    RT[NULL_EVENTS] = bdd_one_constraint(RT[NULL_EVENTS], 
      variable_index[TYPE_SYNCHRONIZER][0][si], TYPE_FALSE
    ); 
  RT[local_path = RT_TOP++] = red_bop(AND, RT[path], RT[REFINED_GLOBAL_INVARIANCE]); 

  RT[result] = red_label_bck(
    nspec, 
    DECLARED_GLOBAL_INVARIANCE, // reset_inheritance
    local_path, //path 
    path,  
    FLAG_ROOT_NOAPPROX  
  ); 
  
  #ifdef RED_DEBUG_LIB_MODE
  fprintf(RED_OUT, "After the labeling algorithm, result = %1d\n", 
    result
  ); 
  red_print_graph(RT[result]); 
  #endif  

  RT_TOP = RT_TOP-2; // local_path  
  
  mr->failed_state_diagram = RT[result]; 
  red_mark(mr->failed_state_diagram, FLAG_GC_USER_STATIC1);
  
  RT[result] = red_bop(AND, RT[result], RT[init]); 
  RT[result] = red_hull_normalize(result);  
  if (RT[result] == NORM_FALSE) { 
    mr->status = mr->status | FLAG_MODEL_CHECK_SATISFIED; 
  } 
  else { 
    mr->status = mr->status & ~FLAG_MODEL_CHECK_SATISFIED; 
  }
  RT_TOP--; // result 
  return (mr); 
} 
  /* red_model_chk() */ 
  
  


/************************************************************************
 * procedures for abstract reachability analysis. 
 */
void	clear_while_gfp_statement(st)
     struct statement_type	*st;
{
  int	i;

  if (!st) 
    return; 
  
  switch (st->op) { 
  case ST_IF: 
    clear_while_gfp_statement(st->u.branch.if_statement); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      clear_while_gfp_statement(st->u.branch.else_statement); 
    } 
    break; 
  case ST_WHILE: 
    for (i = 1; i <= PROCESS_COUNT; i++) { 
      st->u.loop.red_gfp[i] = NULL; 
    } 
    clear_while_gfp_statement(st->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (i = st->u.seq.count-1; i>=0; i--) { 
      clear_while_gfp_statement(st->u.seq.statement[i]); 
    } 
    break; 
  default: 
    return; 
  } 
}
  /* clear_while_gfp_statement() */ 





void	clear_while_gfp() { 
  int	xi; 
  
  for (xi = 1; xi < XTION_COUNT; xi++) 
    clear_while_gfp_statement(XTION[xi].statement); 
}
  /* clear_while_gfp() */ 
  
  
/* The following procedure can help us in pruning the search space.  
   The idea is to use alternative exploration in the reverse direction 
   to restrain the search space related to the anwser of reachability. 
   For example, if we want to use red_safety_fwd() to check a state goal. 
   Any state in the forward analysis that cannot reach the goal 
   does not have to be visited. 
   In other words, any state that is not backward reachable from 
   goal should not be visited. 
   Of course, exact analysis of the backward reachability could also be 
   as expensive as the forward reachability that we have to do. 
   So what we do is to calculate an over-approximation of the backward 
   reachability.  
   In fact, what we do is two-phase alternation. 
   We first calculate an untimed forward analysis followed by 
   a magnitude backward analysis. 
   
   It is not to be used by the users. 
   They are only directly used by 
      red_safety_fwd(), 
      red_safety_bck(), 
      red_risk_fwd(), 
      red_risk_bck(), 
      red_parametric_safety_fwd(), 
      red_parametric_safety_bck(), 
      red_parametric_risk_fwd(), 
      red_parametric_risk_bck(), 
      red_label_bck(), 
      and the corresponding procedures 
// in model-checking.  
// The reason is that in redlib, we don't really know whether 
// the users have told us 
//   what the inference direction is, 
//   what the initial and goal conditions are, 
//   whether they will dynamically change the initial conditions online.  
//   Supposedly, the procedure, together with red_analysis_untimed, 
*/

void 	preliminary_decision_check(type_task, w, d, cpu_time_parsing) 
	int		type_task, w; 
	struct red_type	*d; 
  	float		cpu_time_parsing; 
{
  switch (type_task) {
  case TASK_DEADLOCK:
  case TASK_SAFETY:
  case TASK_RISK:
  case TASK_GOAL:
  case TASK_ZENO: 
    if (red_bop(AND, d, RT[w]) == NORM_FALSE) { 
      switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
      case TASK_SAFETY:
        fprintf(RED_OUT, "\nAll states reachable from the initial states are safe.\n");
        break; 
      default:
        fprintf(RED_OUT, "\nThe %s state is NOT reachable from the initial states.\n",
	      TASK_TYPE_NAME
	      );
      }
      exit_with_summary(cpu_time_parsing); 
    } 
  }
}
  /* preliminary_decision_check() */  
  
  
  
/* There are several design issues here. 
 1. do we have to change the sxt_bulk construction here ? 
    Changing here will hurt the modularity or not ? 
    What sxt_bulks do we have to change ? 
    The sim ones or the original ones ? 
    
    DESIGN DECISIONS: 
    We will for the time being leave as it is now. 
    Let us see how it works out later. 
    
 2. does the framework we outlined here also works for simulation checking ? 
    Do we have to consider the factors of roles ? 
    Do we have to support the abstract space of only certain roles ? 
    
    DESIGN DECISIONS: 
    we let the roles play. 
    But when not all roles are included in this evaluation, 
    we don't allow the preliminary decision checking. 
    We think that does not make sense.  
    First all there is not really a goal for simulation checking, right ? 
    
*/



struct red_type	*red_abstract_space_fwd(
	int	init, 
	int	path, 
	int	goal, 
	int	type_task, 
	int	flag_root_oapprox,   
	int	flag_print    
	) 
{ 
  int				w, apath, orig_gstatus[GSTATUS_SIZE]; 
  float				cpu_time_parsing; 
  struct reachable_return_type	*rr; 

  for (w = 0; w < GSTATUS_SIZE; w++) { 
    orig_gstatus[w] = GSTATUS[w]; 	
  } 
  switch (type_task) { 
  case TASK_BRANCHING_BISIM_CHECKING: 
  case TASK_BRANCHING_SIM_CHECKING: 
    fprintf(RED_OUT, "\nThis is not supposed to be used by bisim and sim.\n"); 
    exit(0); 
    break; 
  default: 
    GSTATUS[INDEX_GAME_ROLES] = (GSTATUS[INDEX_GAME_ROLES] & ~MASK_GAME_ROLES)
			    | FLAG_GAME_MODL; 
//    cpu_time_parsing = red_user_time(); 
    clear_while_gfp(); 
    switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) { 
    case FLAG_SYSTEM_UNTIMED: 
      RT[REFINED_GLOBAL_INVARIANCE] 
      = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
      break; 

    case FLAG_SYSTEM_TIMED: 
    case FLAG_SYSTEM_HYBRID: 
      switch (flag_root_oapprox) { 
      case FLAG_OAPPROX_GAME_UNTIMED: 
        RT[REFINED_GLOBAL_INVARIANCE] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
        break; 
      case FLAG_OAPPROX_GAME_MAGNITUDE: 
      case FLAG_OAPPROX_GAME_DIAGONAL: 
        RT[REFINED_GLOBAL_INVARIANCE] = RT[goal]; 
        RT[apath = RT_TOP++] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
        
        GSTATUS[INDEX_PRINT] 
        = (GSTATUS[INDEX_PRINT] & ~MASK_PRINT) 
        | (flag_print & MASK_PRINT); 
        GSTATUS[INDEX_APPROX] 
        = FLAG_ROOT_OAPPROX | FLAG_OAPPROX_GAME_UNTIMED; 
        GSTATUS[INDEX_GAME_ROLES] = MASK_GAME_ROLES; 
        GSTATUS[INDEX_TIME_PROGRESS] 
        = GSTATUS[INDEX_TIME_PROGRESS] & ~FLAG_TIME_PROGRESS; 

        GSTATUS[INDEX_NORM_ZONE] 
        = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
        | FLAG_NORM_ZONE_NONE; 
        GSTATUS[INDEX_NORM_HYBRID] 
        = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_HYBRID); 

        GSTATUS[INDEX_ACTION_APPROX] 
        = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
        | FLAG_ACTION_APPROX_UNTIMED; 
        GSTATUS[INDEX_REDUCTION_INACTIVE] 
        = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
        | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
        GSTATUS[INDEX_COUNTER_EXAMPLE] 
        = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE; 
        GSTATUS[INDEX_ZENO_CYCLE] 
        = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
        | FLAG_ZENO_CYCLE_OK; 
        GSTATUS[INDEX_FULL_REACHABILITY] 
        = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY; 
        GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        & ~FLAG_REACHABILITY_DEPTH_BOUND; 
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
        GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
        = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & ~FLAG_PARAMETRIC_ANALYSIS; 
        
        rr = red_reachable_bck(
          INDEX_FALSE, 
          apath, 
          REFINED_GLOBAL_INVARIANCE, 
          SYNC_XTION, 
          SYNC_XTION_COUNT, 
          XI_SYNC_BULK, 
          XI_SYNC_BULK_WITH_TRIGGERS
        ); 
        RT[REFINED_GLOBAL_INVARIANCE] = rr->reachability; 
        preliminary_decision_check(
    	  type_task, 
    	  REFINED_GLOBAL_INVARIANCE, 
    	  RT[init], 
    	  cpu_time_parsing
    	  ); 
    	RT_TOP--; // apath 
        break; 
      default: 
        // To prune the search space, we first do an untimed exploration 
        // in the same direction as the final one. 
        // Then we do a magnitude exploration in the reverse direction as 
        // the final one. 
        RT[REFINED_GLOBAL_INVARIANCE] = RT[init]; 
        RT[apath = RT_TOP++] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 

        GSTATUS[INDEX_PRINT] 
        = (GSTATUS[INDEX_PRINT] & ~MASK_PRINT) 
        | (flag_print & MASK_PRINT); 
        GSTATUS[INDEX_APPROX] 
        = FLAG_ROOT_OAPPROX | FLAG_OAPPROX_GAME_UNTIMED; 
        GSTATUS[INDEX_GAME_ROLES] = MASK_GAME_ROLES; 
        GSTATUS[INDEX_COUNTER_EXAMPLE] 
        = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE; 
        GSTATUS[INDEX_TIME_PROGRESS] 
        = GSTATUS[INDEX_TIME_PROGRESS] & ~FLAG_TIME_PROGRESS; 

        GSTATUS[INDEX_NORM_ZONE] 
        = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
        | FLAG_NORM_ZONE_NONE; 
        GSTATUS[INDEX_NORM_HYBRID] 
        = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID); 
        
        GSTATUS[INDEX_ACTION_APPROX] 
        = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
        | FLAG_ACTION_APPROX_UNTIMED; 
        GSTATUS[INDEX_REDUCTION_INACTIVE] 
        = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
        | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
        GSTATUS[INDEX_ZENO_CYCLE] 
        = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
        | FLAG_ZENO_CYCLE_OK; 
        GSTATUS[INDEX_FULL_REACHABILITY] 
        = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY; 
        GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        & ~FLAG_REACHABILITY_DEPTH_BOUND; 
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
        GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
        = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & ~FLAG_PARAMETRIC_ANALYSIS; 
        
        rr = red_reachable_fwd(
          REFINED_GLOBAL_INVARIANCE, apath, INDEX_FALSE, 
          SYNC_XTION, 
          SYNC_XTION_COUNT, 
          XI_SYNC_BULK_WITH_TRIGGERS
        ); 
        RT[REFINED_GLOBAL_INVARIANCE] = rr->reachability; 
        preliminary_decision_check(
    	  type_task, 
    	  REFINED_GLOBAL_INVARIANCE, 
    	  RT[goal], 
    	  cpu_time_parsing
    	); 
    	
        // This is when we do a magnitude exploration 
        // in the reverse direction as the final one. 
        GSTATUS[INDEX_APPROX] 
        = FLAG_OAPPROX_GAME_MAGNITUDE | FLAG_ROOT_OAPPROX; 
        GSTATUS[INDEX_ACTION_APPROX] 
        = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
        | FLAG_ACTION_APPROX_NOXTIVE; 

        RT[apath] = red_bop(AND, RT[REFINED_GLOBAL_INVARIANCE], RT[DECLARED_GLOBAL_INVARIANCE]); 
        RT[REFINED_GLOBAL_INVARIANCE] = RT[goal]; 
        rr = red_reachable_bck(
          INDEX_FALSE, 
          apath, 
          REFINED_GLOBAL_INVARIANCE, 
          SYNC_XTION, 
          SYNC_XTION_COUNT, 
          XI_SYNC_BULK, 
          XI_SYNC_BULK_WITH_TRIGGERS
        ); 
        RT[REFINED_GLOBAL_INVARIANCE] = rr->reachability; 
        preliminary_decision_check(
    	  type_task, 
    	  REFINED_GLOBAL_INVARIANCE, 
    	  RT[init], 
    	  cpu_time_parsing
    	  ); 
        RT_TOP--; /* apath */ 
      }
    }
  }
  RT[XI_SYNC_BULK] 
  = red_bop(AND, RT[XI_SYNC_BULK], RT[REFINED_GLOBAL_INVARIANCE]);
  RT[XI_SYNC_BULK] = red_only_xi(RT[XI_SYNC_BULK]);
  RT[XI_SYNC_BULK_WITH_TRIGGERS] 
  = red_bop(AND, RT[XI_SYNC_BULK_WITH_TRIGGERS], RT[REFINED_GLOBAL_INVARIANCE]);
  RT[XI_SYNC_BULK_WITH_POSTCONDITION] 
  = red_bop(AND, RT[XI_SYNC_BULK_WITH_POSTCONDITION], RT[REFINED_GLOBAL_INVARIANCE]);

  for (w = 2; w < INDEX_BOTTOM_OF_RUNTIME_STACK; w++) 
    red_mark(RT[w], FLAG_GC_STABLE); 
  RT_TOP = RT_DYNAMIC = INDEX_BOTTOM_OF_RUNTIME_STACK; 
  RED_XI_SYNC_SIGNIFICANT = RT[XI_SYNC_BULK_WITH_POSTCONDITION]; 
  clear_while_gfp(); 
  garbage_collect(FLAG_GC_SILENT);  
  
  for (w = 0; w < GSTATUS_SIZE; w++) { 
    GSTATUS[w] = orig_gstatus[w]; 	
  } 
  return(RT[REFINED_GLOBAL_INVARIANCE]); 
}
  /* red_abstract_space_fwd() */ 
  
  
  

  


/*********************************************
 *  This procedure is to be called before not to be used in sim and bisim checking. 
 */
struct red_type	*red_abstract_space_bck(
	int	init, 
	int	path, 
	int	goal, 
	int	type_task, 
	int	flag_root_oapprox, // This is the approx flag for the final 
				   // reachability or model-checking task.  
	int	flag_print    
	) 
{ 
  int				w, apath, orig_gstatus[GSTATUS_SIZE];
  float				cpu_time_parsing; 
  struct reachable_return_type	*rr; 

  for (w = 0; w < GSTATUS_SIZE; w++) { 
    orig_gstatus[w] = GSTATUS[w]; 
  } 
  switch (type_task) { 
  case TASK_BRANCHING_BISIM_CHECKING: 
  case TASK_BRANCHING_SIM_CHECKING: 
    fprintf(RED_OUT, "\nThis is not supposed to be used by bisim and sim.\n"); 
    exit(0); 
    break; 
  default: 
    GSTATUS[INDEX_GAME_ROLES] = (GSTATUS[INDEX_GAME_ROLES] & ~MASK_GAME_ROLES)
			    | FLAG_GAME_MODL; 
//    cpu_time_parsing = red_user_time(); 
    clear_while_gfp(); 
    switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) { 
    case FLAG_SYSTEM_UNTIMED: 
/*
      RT[REFINED_GLOBAL_INVARIANCE] 
      = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
      break; 
*/
    case FLAG_SYSTEM_TIMED: 
    case FLAG_SYSTEM_HYBRID: 
      switch (flag_root_oapprox) { 
      case FLAG_OAPPROX_GAME_UNTIMED: 
        RT[REFINED_GLOBAL_INVARIANCE] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
        break; 
      case FLAG_OAPPROX_GAME_MAGNITUDE: 
      case FLAG_OAPPROX_GAME_DIAGONAL: 
        RT[REFINED_GLOBAL_INVARIANCE] = RT[init]; 
        RT[apath = RT_TOP++] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 

        GSTATUS[INDEX_PRINT] 
        = (GSTATUS[INDEX_PRINT] & ~MASK_PRINT) 
        | (flag_print & MASK_PRINT); 
        GSTATUS[INDEX_APPROX] 
//        = FLAG_ROOT_OAPPROX | FLAG_OAPPROX_GAME_GAME_MODE_ONLY; 
        = FLAG_ROOT_OAPPROX | FLAG_OAPPROX_GAME_MAGNITUDE; 
        GSTATUS[INDEX_GAME_ROLES] = MASK_GAME_ROLES; 
        GSTATUS[INDEX_COUNTER_EXAMPLE] 
        = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE; 
        GSTATUS[INDEX_TIME_PROGRESS] 
        = GSTATUS[INDEX_TIME_PROGRESS] & ~FLAG_TIME_PROGRESS; 
        
        GSTATUS[INDEX_NORM_ZONE] 
        = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
        | FLAG_NORM_ZONE_NONE; 
        GSTATUS[INDEX_NORM_HYBRID] 
        = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID); 

        GSTATUS[INDEX_ACTION_APPROX] 
        = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
        | FLAG_ACTION_APPROX_UNTIMED; 
        GSTATUS[INDEX_REDUCTION_INACTIVE] 
        = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
        | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
        GSTATUS[INDEX_ZENO_CYCLE] 
        = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
        | FLAG_ZENO_CYCLE_OK; 
        GSTATUS[INDEX_FULL_REACHABILITY] 
        = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY; 
        GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        & ~FLAG_REACHABILITY_DEPTH_BOUND; 
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
        GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
        = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & ~FLAG_PARAMETRIC_ANALYSIS; 

        rr = red_reachable_fwd(
          REFINED_GLOBAL_INVARIANCE, apath, INDEX_FALSE, 
          SYNC_XTION, 
          SYNC_XTION_COUNT, 
          XI_SYNC_BULK_WITH_TRIGGERS
        ); 
        RT[REFINED_GLOBAL_INVARIANCE] = rr->reachability; 
        preliminary_decision_check(
    	  type_task, 
    	  REFINED_GLOBAL_INVARIANCE, 
    	  RT[goal], 
    	  cpu_time_parsing
    	  ); 
    	RT_TOP--; // apath 
        break; 
      default: 
        // To prune the search space, we first do an untimed exploration 
        // in the same direction as the final one. 
        // Then we do a magnitude exploration in the reverse direction as 
        // the final one. 
        RT[REFINED_GLOBAL_INVARIANCE] = RT[init] /* RT[goal] */; 
        RT[apath = RT_TOP++] 
        = red_bop(AND, RT[path], RT[DECLARED_GLOBAL_INVARIANCE]); 
        
        GSTATUS[INDEX_PRINT] 
        = (GSTATUS[INDEX_PRINT] & ~MASK_PRINT) 
        | (flag_print & MASK_PRINT); 
        GSTATUS[INDEX_APPROX] 
        = FLAG_OAPPROX_GAME_MAGNITUDE | FLAG_ROOT_OAPPROX; 
        GSTATUS[INDEX_GAME_ROLES] = MASK_GAME_ROLES; 
        GSTATUS[INDEX_COUNTER_EXAMPLE] 
        = GSTATUS[INDEX_COUNTER_EXAMPLE] & ~FLAG_COUNTER_EXAMPLE; 
        GSTATUS[INDEX_TIME_PROGRESS] 
        = GSTATUS[INDEX_TIME_PROGRESS] & ~FLAG_TIME_PROGRESS; 
        
        GSTATUS[INDEX_NORM_ZONE] 
        = (GSTATUS[INDEX_NORM_ZONE] & ~MASK_NORM_ZONE) 
        | FLAG_NORM_ZONE_NONE; 
        GSTATUS[INDEX_NORM_HYBRID] 
        = (GSTATUS[INDEX_NORM_HYBRID] & ~MASK_NORM_HYBRID); 

        GSTATUS[INDEX_ACTION_APPROX] 
        = (GSTATUS[INDEX_ACTION_APPROX] & ~MASK_ACTION_APPROX) 
        | FLAG_ACTION_APPROX_NOXTIVE; 
        GSTATUS[INDEX_REDUCTION_INACTIVE] 
        = (GSTATUS[INDEX_REDUCTION_INACTIVE] & ~MASK_REDUCTION_INACTIVE) 
        | FLAG_REDUCTION_INACTIVE_NOXTIVE; 
        GSTATUS[INDEX_ZENO_CYCLE] 
        = (GSTATUS[INDEX_ZENO_CYCLE] & ~MASK_ZENO_CYCLE) 
        | FLAG_ZENO_CYCLE_OK; 
        GSTATUS[INDEX_FULL_REACHABILITY] 
        = GSTATUS[INDEX_FULL_REACHABILITY] | FLAG_FULL_REACHABILITY; 
        GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        = GSTATUS[INDEX_REACHABILITY_DEPTH_BOUND] 
        & ~FLAG_REACHABILITY_DEPTH_BOUND; 
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL; 
        GSTATUS[INDEX_PARAMETRIC_ANALYSIS] 
        = GSTATUS[INDEX_PARAMETRIC_ANALYSIS] & ~FLAG_PARAMETRIC_ANALYSIS; 
        
        rr = red_reachable_fwd(
          REFINED_GLOBAL_INVARIANCE, apath, INDEX_FALSE, 
          SYNC_XTION, 
          SYNC_XTION_COUNT, 
          XI_SYNC_BULK_WITH_TRIGGERS
        ); 
        RT[REFINED_GLOBAL_INVARIANCE] = rr->reachability; 
        preliminary_decision_check(
    	  type_task, 
    	  REFINED_GLOBAL_INVARIANCE, 
    	  RT[goal], 
    	  cpu_time_parsing
    	); 
        RT_TOP--; /* apath */ 
      }
    }
  }

  #ifdef RED_DEBUG_FXP_MODE
  fprintf(RED_OUT, "Newly generated refined global invariance:\n"); 
  red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
  #endif 

  RT[XI_SYNC_BULK] 
  = red_bop(AND, RT[XI_SYNC_BULK], RT[REFINED_GLOBAL_INVARIANCE]);
  RT[XI_SYNC_BULK] = red_only_xi(RT[XI_SYNC_BULK]);
  RT[XI_SYNC_BULK_WITH_TRIGGERS] 
  = red_bop(AND, RT[XI_SYNC_BULK_WITH_TRIGGERS], RT[REFINED_GLOBAL_INVARIANCE]);
  RT[XI_SYNC_BULK_WITH_POSTCONDITION] 
  = red_bop(AND, RT[XI_SYNC_BULK_WITH_POSTCONDITION], RT[REFINED_GLOBAL_INVARIANCE]);

  for (w = 2; w < INDEX_BOTTOM_OF_RUNTIME_STACK; w++) 
    red_mark(RT[w], FLAG_GC_STABLE); 
  RT_TOP = RT_DYNAMIC = INDEX_BOTTOM_OF_RUNTIME_STACK; 
  RED_XI_SYNC_SIGNIFICANT = RT[XI_SYNC_BULK_WITH_POSTCONDITION]; 
  clear_while_gfp(); 
  garbage_collect(FLAG_GC_SILENT);

  for (w = 0; w < GSTATUS_SIZE; w++) { 
    GSTATUS[w] = orig_gstatus[w]; 	
  } 
  #ifdef RED_DEBUG_FXP_MODE
  fprintf(RED_OUT, 
    "\nEnhanced global invariance after red_abstract_space_bck():\n"
  ); 
  red_print_graph(RT[REFINED_GLOBAL_INVARIANCE]); 
  #endif 

  #ifdef RED_DEBUG_FXP_DEBUG  
  push_sxi_stack(1, 30); 
  push_sxi_stack(2, 10); 
  push_sxi_stack(3, 8); 
  push_sxi_stack(4, 25); 
  push_sxi_stack(5, -1); 
  push_sxi_stack(6, 29); 
  push_sxi_stack(7, 28); 
  push_sxi_stack(8, 20); 
  push_sxi_stack(9, 19); 
  push_sxi_stack(10, 13); 
  push_sxi_stack(11, 18); 
  push_sxi_stack(12, -1); 
  push_sxi_stack(13, 14); 
  push_sxi_stack(14, 14); 
  
  #endif 

  return(RT[REFINED_GLOBAL_INVARIANCE]); 
}
  /* red_abstract_space_bck() */ 
  
  
  



