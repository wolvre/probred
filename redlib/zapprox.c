#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
*/
#include <float.h>
#include <limits.h> 

#include "redbasics.h"
#include "redbasics.e"

#include "vindex.e"

#include "redparse.h"

#include "redbop.h"
#include "redbop.e"

#include "redsymmetry.e"

#include "inactive.e"
#include "redparse.e"

#include "hashman.h" 
#include "hashman.e" 

#include "zone.h"  
#include "zone.e"

#include "hybrid.e"


int	**closure;

void	init_zapprox_management() 
{
  int	ci; 

  closure = (int **) malloc(CLOCK_COUNT*sizeof(int *)); 
  for (ci = 0; ci < CLOCK_COUNT; ci++) 
    closure[ci] = (int *) malloc(CLOCK_COUNT*sizeof(int)); 
}
/* init_zapprox_management() */ 


int	TS_HULL_FILTER; 

struct red_type	*rec_hull_filter(d)
     struct red_type	*d; 
{
  int				ci, b; 
  struct ddd_child_type		*ic; 
  struct red_type		*result, *child; 
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE || d->var_index == TYPE_TRUE) 
    return(d); 

  ce = cache1_check_result_key(OP_HULL_FILTER, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    ci = d->u.crd.child_count-1; 
    result = rec_hull_filter(d->u.crd.arc[ci].child); 
    if (d->u.crd.arc[ci].upper_bound != CLOCK_POS_INFINITY) 
      result = crd_one_constraint(result, 
	d->var_index, d->u.crd.arc[ci].upper_bound
      ); 
    return(ce->result = result); 

  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_hull_filter(d->u.fdd.arc[ci].child); 
      result = red_bop(OR, result, 
	fdd_one_constraint(child, 
	  d->var_index, 
	  d->u.fdd.arc[ci].lower_bound, 
	  d->u.fdd.arc[ci].upper_bound
      ) ); 
    }

    return(ce->result = result); 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_hull_filter(d->u.dfdd.arc[ci].child); 
      result = red_bop(OR, result, 
	dfdd_one_constraint(child, 
	  d->var_index, 
	  d->u.dfdd.arc[ci].lower_bound, 
	  d->u.dfdd.arc[ci].upper_bound
      ) ); 
    }

    return(ce->result = result); 

  default: 
    result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      child = rec_hull_filter(d->u.ddd.arc[ci].child); 
      result = red_bop(OR, result, 
	ddd_one_constraint(child, 
	  d->var_index, 
	  d->u.ddd.arc[ci].lower_bound, 
	  d->u.ddd.arc[ci].upper_bound
      ) ); 
    }

    return(ce->result = result); 
  }
}
/* rec_hull_filter() */ 






struct red_type	*zone_hull_filter(d)
     struct red_type	*d; 
{
  d = rec_hull_filter(d); 

  return(d); 
}
/* zone_hull_filter() */ 





struct 	hull_record_type {
  struct red_type	*d, *result; 
  int			ci; 
} 
  *HULL; 

int		HULLING_STOP, HULL_TOP;
struct red_type	*RED_HULLING_STOP; 


int	rec_one_convex_hull(d)
     struct red_type	*d; 
{
  int				ci, c1, c2, next_vi, vi; 
  struct crd_child_type		*bc;
  struct red_type		*child; 
  int				result; 
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE) {
    fprintf(RED_OUT, "\nThis TYPE_FALSE node should not be here.\n"); 
    fflush(RED_OUT); 
    for (;1 ; ); 
  }
  else if (d == RED_HULLING_STOP) 
    return(TYPE_TRUE); 
  else if (d->var_index == TYPE_TRUE || d->var_index >= HULLING_STOP) 
    return(TYPE_FALSE); 
  

  ce = cache1_check_result_key(OP_ONE_CONVEX_HULL, d); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = TYPE_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) 
      if (rec_one_convex_hull(d->u.crd.arc[ci].child)) { 
	result = TYPE_TRUE; 
	c1 = VAR[d->var_index].U.CRD.CLOCK1; 
	c2 = VAR[d->var_index].U.CRD.CLOCK2; 
	if (closure[c1][c2] < d->u.crd.arc[ci].upper_bound)
	  closure[c1][c2] = d->u.crd.arc[ci].upper_bound; 
      }
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) 
      if (rec_one_convex_hull(d->u.fdd.arc[ci].child)) 
	result = TYPE_TRUE; 
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) 
      if (rec_one_convex_hull(d->u.dfdd.arc[ci].child)) 
	result = TYPE_TRUE; 
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) 
      if (rec_one_convex_hull(d->u.ddd.arc[ci].child)) 
	result = TYPE_TRUE; 
  } 
  return((int) (ce->result 
    = (struct red_type *) result
  ) ); 
}
/* rec_one_convex_hull() */ 




inline void	one_convex_hull_postprocessing(
  int 			phi, 
  struct red_type 	*d
) { 
  int			vi, cv; 
  struct red_type	*result; 
  
  for (vi = HULL[phi].d->var_index; vi < d->var_index; vi++) 
    if (VAR[vi].TYPE == TYPE_CRD) 
      closure[VAR[vi].U.CRD.CLOCK1][VAR[vi].U.CRD.CLOCK2] = CLOCK_NEG_INFINITY - 1; 
  
  if (d == NORM_NO_RESTRICTION) { 
    HULLING_STOP = VARIABLE_COUNT; 
    RED_HULLING_STOP = NORM_NO_RESTRICTION;
  }
  else { 
    HULLING_STOP = d->var_index;
    RED_HULLING_STOP = d;
  }
  rec_one_convex_hull(HULL[phi].d); 
  if (d == NORM_NO_RESTRICTION) 
    result = NORM_NO_RESTRICTION; 
  else 
    result = HULL[phi].result; 
  for (vi = HULL[phi-1].d->var_index; vi < d->var_index; vi++) {
    if (VAR[vi].TYPE == TYPE_CRD) { 
      cv = closure[VAR[vi].U.CRD.CLOCK1][VAR[vi].U.CRD.CLOCK2]; 
      if (cv < CLOCK_POS_INFINITY && cv != CLOCK_NEG_INFINITY - 1) 
        result = crd_one_constraint(result, vi, cv); 
    } 
  }
  switch (VAR[HULL[phi].d->var_index].TYPE) { 
  case TYPE_CRD: 
    HULL[phi].result = red_bop(OR, HULL[phi].result, result);
    break; 
  case TYPE_FLOAT: {
    float flb, fub; 
    flb = HULL[phi].d->u.fdd.arc[HULL[phi].ci].lower_bound; 
    fub = HULL[phi].d->u.fdd.arc[HULL[phi].ci].upper_bound; 
    HULL[phi].result = red_bop(OR, HULL[phi].result, 
      fdd_one_constraint(result, HULL[phi].d->var_index, flb, fub)
    ); 
    break; 
  }
  case TYPE_DOUBLE: {
    double	dflb, dfub; 
    
    dflb = HULL[phi].d->u.dfdd.arc[HULL[phi].ci].lower_bound; 
    dfub = HULL[phi].d->u.dfdd.arc[HULL[phi].ci].upper_bound; 
    HULL[phi].result = red_bop(OR, HULL[phi].result, 
      dfdd_one_constraint(result, HULL[phi].d->var_index, dflb, dfub)
    ); 
    break; 
  }
  default: {
    int	lb, ub; 
    
    lb = HULL[phi].d->u.ddd.arc[HULL[phi].ci].lower_bound; 
    ub = HULL[phi].d->u.ddd.arc[HULL[phi].ci].upper_bound; 
    HULL[phi].result = red_bop(OR, HULL[phi].result, 
      ddd_one_constraint(result, HULL[phi].d->var_index, lb, ub)
    ); 
    break; 
  } } 
}
  /* one_convex_hull_postprocessing() */ 




void	rec_zone_convex_hull(parent, d, hi)
     struct red_type	*parent, *d; 
     int		hi; 
{
  int				ci, vi, cv, lb, ub; 
  struct red_type		*result;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE) 
    return; 
  
  ce = cache2_check_result_key(OP_ZONE_CONVEX_HULL, d, parent); 
  if (ce->result) {
    return; 
  } 
  /*
  fprintf(RED_OUT, "rec_zone_convex_hull(%x)\n", d); 
  red_print_graph(d); 
  */
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
      rec_zone_convex_hull(parent, d->u.crd.arc[ci].child, hi); 
    }
    return; 
  case TYPE_TRUE: 
    break; 
/*       
    for (vi = HULL[hi-1].d->var_index; vi < VARIABLE_COUNT; vi++) 
      if (VAR[vi].TYPE == TYPE_CRD) 
        closure[VAR[vi].U.CRD.CLOCK1][VAR[vi].U.CRD.CLOCK2] = CLOCK_NEG_INFINITY - 1; 
      
    HULLING_STOP = VARIABLE_COUNT; 
    RED_HULLING_STOP = NORM_NO_RESTRICTION;
    rec_one_convex_hull(HULL[hi-1].d); 
        
    result = NORM_NO_RESTRICTION; 
    for (vi = HULL[hi-1].d->var_index; vi < VARIABLE_COUNT; vi++) {
      if (VAR[vi].TYPE == TYPE_CRD) { 
        cv = closure[VAR[vi].U.CRD.CLOCK1][VAR[vi].U.CRD.CLOCK2];
        if (cv < CLOCK_POS_INFINITY && cv != CLOCK_NEG_INFINITY - 1) 
          result = red_bop(AND, result, crd_atom(vi, cv)); 
      } 
    }
    if (VAR[HULL[hi-1].d->var_index].TYPE != TYPE_CRD) { 
      lb = HULL[hi-1].d->u.ddd.arc[HULL[hi-1].ci].lower_bound; 
      ub = HULL[hi-1].d->u.ddd.arc[HULL[hi-1].ci].upper_bound; 
      HULL[hi-1].result = red_bop(OR, HULL[hi-1].result, 
				  red_bop(AND, result, 
      				 	  ddd_atom(HULL[hi-1].d->var_index, lb, ub)
      				  	  )
      				  ); 
    }
    else 
      HULL[hi-1].result = red_bop(OR, HULL[hi-1].result, result);  
    break;  
*/ 
  case TYPE_FLOAT: 
    HULL[hi].d = d; 
    HULL[hi].result = NORM_FALSE; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) { 
      HULL[hi].ci = ci; 
      rec_zone_convex_hull(d, d->u.fdd.arc[ci].child, hi+1); 
    }
    break; 

  case TYPE_DOUBLE: 
    HULL[hi].d = d; 
    HULL[hi].result = NORM_FALSE; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) { 
      HULL[hi].ci = ci; 
      rec_zone_convex_hull(d, d->u.dfdd.arc[ci].child, hi+1); 
    }
    break; 

  default: 
    HULL[hi].d = d; 
    HULL[hi].result = NORM_FALSE; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      HULL[hi].ci = ci; 
      rec_zone_convex_hull(d, d->u.ddd.arc[ci].child, hi+1); 
    }
    break; 
  }
  if (hi > 0) { 
    one_convex_hull_postprocessing(hi-1, d); 
  }
}
/* rec_zone_covnex_hull() */ 





struct red_type	*zone_convex_hull(d) 
     struct red_type	*d; 
{
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return(d); 
    
  HULL = (struct hull_record_type *) 
	malloc((VARIABLE_COUNT-CLOCK_INEQUALITY_COUNT)*sizeof(struct hull_record_type));  

  cache1_clear(OP_ZONE_CONVEX_HULL); 
  if (VAR[d->var_index].TYPE == TYPE_CRD) { 
    HULL_TOP = 0; 
    HULL[0].d = d; 
    HULL[0].result = NORM_FALSE; 	
    HULL[0].ci = 0; 
  
    rec_zone_convex_hull(NULL, d, 1); 
  }
  else {
    HULL_TOP = 0; 
    rec_zone_convex_hull(NULL, d, 0);
  } 
  d = HULL[0].result; 
  free(HULL); 
  
  return(d); 
}
/* zone_convex_hull() */






/************************************************************************************
 * union filter
 */



struct red_type	*rec_union_filter();


struct red_type	*rec_union_right_filter(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_CRD:
    return(dx);
  default:
    child_stack_level_push();
    ub = VAR[dy->var_index].U.DISC.UB;
    for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > dy->u.ddd.arc[ciy].upper_bound) {
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);
      }

      new_child = rec_union_filter(dx, dy->u.ddd.arc[ciy].child);
      ichild_stack_push(new_child, dy->u.ddd.arc[ciy].lower_bound,
				 dy->u.ddd.arc[ciy].upper_bound
				 );

      ub = dy->u.ddd.arc[ciy].lower_bound-1;
    }

    if (ub >= VAR[dy->var_index].U.DISC.LB)
      ichild_stack_push(dx, VAR[dy->var_index].U.DISC.LB, ub);

    return(ddd_new(dy->var_index));
  }
}
/* rec_union_right_filter() */







struct red_type	*rec_union_left_filter(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    return(dy);
  case TYPE_FLOAT: {
    float fub; 
    
    child_stack_level_push();
    fub = VAR[dx->var_index].U.FLT.UB;
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      if (fub > dx->u.fdd.arc[cix].upper_bound) {
	fchild_stack_push(dy, 
	  feps_plus(dx->u.fdd.arc[cix].upper_bound), fub
	);
      }

      new_child = rec_union_filter(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	dx->u.fdd.arc[cix].upper_bound
      );

      fub = feps_minus(dx->u.fdd.arc[cix].lower_bound);
    }

    if (fub >= VAR[dx->var_index].U.DISC.LB)
      fchild_stack_push(dy, VAR[dx->var_index].U.DISC.LB, fub);

    return(fdd_new(dx->var_index));
  } 
  case TYPE_DOUBLE: {
    double	dfub; 
    
    child_stack_level_push();
    dfub = VAR[dx->var_index].U.DBLE.UB;
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      if (dfub > dx->u.dfdd.arc[cix].upper_bound) {
	dfchild_stack_push(dy, 
	  dfeps_plus(dx->u.dfdd.arc[cix].upper_bound), dfub
	);
      }

      new_child = rec_union_filter(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	dx->u.dfdd.arc[cix].upper_bound
      );

      dfub = dfeps_minus(dx->u.dfdd.arc[cix].lower_bound);
    }

    if (dfub >= VAR[dx->var_index].U.DBLE.LB)
      fchild_stack_push(dy, VAR[dx->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(dx->var_index));
  } 
  default:
    child_stack_level_push();
    ub = VAR[dx->var_index].U.DISC.UB;
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      if (ub > dx->u.ddd.arc[cix].upper_bound) {
	ichild_stack_push(dy, dx->u.ddd.arc[cix].upper_bound+1, ub);
      }

      new_child = rec_union_filter(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
				 dx->u.ddd.arc[cix].upper_bound
				 );

      ub = dx->u.ddd.arc[cix].lower_bound-1;
    }

    if (ub >= VAR[dx->var_index].U.DISC.LB)
      ichild_stack_push(dy, VAR[dx->var_index].U.DISC.LB, ub);

    return(ddd_new(dx->var_index));
  }
}
/* rec_union_left_filter() */ 





struct red_type	*rec_union_filter(dx, dy) 
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy;
  struct red_type		*new_child, *new;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_NO_RESTRICTION || dy == NORM_NO_RESTRICTION) 
    return(NORM_NO_RESTRICTION); 

  ce = cache2_check_result_key(OP_UNION_FILTER, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  if (dx->var_index < dy->var_index) 
    return(ce->result
      = rec_union_left_filter(dx, dy)
    );
  else if (dx->var_index > dy->var_index) 
    return(ce->result 
      = rec_union_right_filter(dx, dy)
    ); 
  
  switch (VAR[dx->var_index].TYPE) { 
  case TYPE_CRD: 
    cix = dx->u.crd.child_count-1; 
    ciy = dy->u.crd.child_count-1;
    if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) 
      return(dx->u.crd.arc[cix].child); 
    else if (dy->u.crd.arc[ciy].upper_bound == CLOCK_POS_INFINITY) 
      return(dy->u.crd.arc[ciy].child); 
    else if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound)
      return(ce->result 
        = crd_one_constraint(dy->u.crd.arc[ciy].child, 
	  dy->var_index, dy->u.crd.arc[ciy].upper_bound
      ) ); 
    else {
      new_child = rec_union_filter(dx->u.crd.arc[cix].child, dy->u.crd.arc[ciy].child); 
      return(ce->result 
        = crd_one_constraint(new_child, 
	  dx->var_index, dx->u.crd.arc[cix].upper_bound
      ) ); 
    }
    break; 
  case TYPE_FLOAT: {
    float	flb, fub; 
    
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0; 
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          ) 
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_union_filter(dx->u.fdd.arc[cix].child, 
	    dy->u.fdd.arc[ciy].child
	  ); 
	else 
	  new_child = dx->u.fdd.arc[cix].child; 
      else 
	new_child = dy->u.fdd.arc[ciy].child; 

      fchild_stack_push(new_child, flb, fub);
    }
    
    return(ce->result = fdd_new(dx->var_index));
  }
  case TYPE_DOUBLE: {
    double	dflb, dfub; 
    
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0; 
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          ) 
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_union_filter(dx->u.dfdd.arc[cix].child, 
	    dy->u.dfdd.arc[ciy].child
	  ); 
	else 
	  new_child = dx->u.dfdd.arc[cix].child; 
      else 
	new_child = dy->u.dfdd.arc[ciy].child; 

      dfchild_stack_push(new_child, dflb, dfub);
    }
    
    return(ce->result = dfdd_new(dx->var_index));
  }
  default: 
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0; 
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) 
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_union_filter(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child); 
	else 
	  new_child = dx->u.ddd.arc[cix].child; 
      else 
	new_child = dy->u.ddd.arc[ciy].child; 

      ichild_stack_push(new_child, lb, ub);
    }
    
    return(ce->result = ddd_new(dx->var_index));
  }
}
  /* rec_union_filter() */ 




struct red_type	*zone_union_filter(dx, dy) 
     struct red_type	*dx, *dy; 
{
  dx = rec_union_filter(dx, dy); 

  return(dx); 
}
/* zone_union_filter() */ 







int	sig_word() { 
  int	sig, i, p; 
/* 
  fprintf(RED_OUT, "\nGame-based abstraction for all insigs\n");
  red_print_graph(d); 
*/
  if (PROCESS_COUNT > 32) { 
    fprintf(RED_OUT, "Now, we cannot handle more than 32 processes in \n"); 
    fprintf(RED_OUT, "game based abstraction.\n"); 
    exit(0); 	
  } 
  // FOR NOW we only can handle up to 32 processes in this procedure. 
  sig = 0; 
  for (i = 1, p = 1; p <= PROCESS_COUNT; i = i*2, p++) { 
    if (PROCESS[p].status & FLAG_PROC_SIGNIFICANT) 
      sig = sig | i; 
  } 
  return (sig); 
} 
  /* sig_word() */ 
  
  
  
int	SIG_GAME; 

struct red_type	*rec_abstraction_game_based_insig(d)
     struct red_type	*d; 
{
  int				ci, pi, pj; 
  struct red_type		*result, *child;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(d); 

  ce = cache2_check_result_key(OP_ABSTRACTION_GAME_BASED_INSIG, d, 
    (struct red_type *) SIG_GAME 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT))
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT))
        ) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 crd_atom(d->var_index,
					  d->u.crd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result = result); 
    } 
    break; 

  case TYPE_CDD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK2]].PROC_INDEX;
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT))
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT))
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 ddd_atom(d->var_index, 
					  d->u.ddd.arc[ci].lower_bound, 
					  d->u.ddd.arc[ci].upper_bound
					  )
				 )
			 );
      }
      return(ce->result = result); 
    } 
    break; 

  case TYPE_FLOAT:  
    pi = VAR[d->var_index].PROC_INDEX;
    if (pi && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.fdd.arc[ci].child); 
        result = red_bop(OR, result, child);
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.fdd.arc[ci].child); 
        result = red_bop(OR, result,
	  fdd_one_constraint(child, d->var_index, 
	    d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	  )
	); 
      }
      return(ce->result = result); 
    }
    break; 

  case TYPE_DOUBLE:  
    pi = VAR[d->var_index].PROC_INDEX;
    if (pi && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.dfdd.arc[ci].child); 
        result = red_bop(OR, result, child);
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.dfdd.arc[ci].child); 
        result = red_bop(OR, result,
	  dfdd_one_constraint(child, d->var_index, 
	    d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	  )
	); 
      }
      return(ce->result = result); 
    }
    break; 

  default: 
    pi = VAR[d->var_index].PROC_INDEX;
    if (pi && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result, child);
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abstraction_game_based_insig(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result,
	  ddd_one_constraint(child, d->var_index, 
	    d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
          )
        ); 
      }
      return(ce->result = result); 
    }
    break; 
  }
}
/* rec_abstraction_game_based_insig() */





struct red_type	*red_abstraction_game_based_insig(d) 
	struct red_type	*d; 
{
  SIG_GAME = sig_word(); 
  d = rec_abstraction_game_based_insig(d);  
/* 
  fprintf(RED_OUT, "-----------------\n");
  red_print_graph(d); 
  */ 
  return(d); 
}
  /* red_abstraction_game_based_insig() */ 



  


struct red_type	*rec_abstraction_game_based_insig_discrete(d)
     struct red_type	*d; 
{
  int				ci, pi, pj; 
  struct red_type		*result, *child; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(d); 

  ce = cache2_check_result_key(
    OP_ABSTRACTON_GAME_BASED_INSIG_DISCRETE, d, 
    (struct red_type *) SIG_GAME 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT))
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT))
        ) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_discrete(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_discrete(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result,
			 red_bop(AND, child, 
				 crd_atom(d->var_index, 
					  d->u.crd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result = result); 
    } 
    break; 

  case TYPE_CDD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK2]].PROC_INDEX; 
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT))
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT))
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_discrete(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_discrete(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 ddd_atom(d->var_index, 
					  d->u.ddd.arc[ci].lower_bound, 
					  d->u.ddd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result= result); 
    } 
    break; 

  case TYPE_FLOAT: 
    pi = VAR[d->var_index].PROC_INDEX;
    if (   pi 
        && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)
        && (   VAR[d->var_index].TYPE != TYPE_DISCRETE 
            || VAR[d->var_index].OFFSET != OFFSET_MODE
            )
        ) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(
          d->u.fdd.arc[ci].child
        ); 
        result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(
          d->u.fdd.arc[ci].child
        ); 
        result = red_bop(OR, result, 
	  fdd_one_constraint(child, d->var_index, 
	    d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	  )
	);
      }
      return(ce->result = result); 
    }
    break; 

  case TYPE_DOUBLE: 
    pi = VAR[d->var_index].PROC_INDEX;
    if (   pi 
        && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)
        && (   VAR[d->var_index].TYPE != TYPE_DISCRETE 
            || VAR[d->var_index].OFFSET != OFFSET_MODE
            )
        ) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(
          d->u.dfdd.arc[ci].child
        ); 
        result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(
          d->u.dfdd.arc[ci].child
        ); 
        result = red_bop(OR, result, 
	  dfdd_one_constraint(child, d->var_index, 
	    d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	  )
	);
      }
      return(ce->result = result); 
    }
    break; 

  default: 
    pi = VAR[d->var_index].PROC_INDEX;
    if (   pi 
        && !(PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)
        && (   VAR[d->var_index].TYPE != TYPE_DISCRETE 
            || VAR[d->var_index].OFFSET != OFFSET_MODE
            )
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    }
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abstraction_game_based_insig_discrete(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result, 
	  ddd_one_constraint(child, d->var_index, 
	    d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
	  )
	);
      }
      return(ce->result = result); 
    }
    break; 
  }
}
/* rec_abstraction_game_based_insig_discrete() */ 





struct red_type	*red_abstraction_game_based_insig_discrete(d)
	struct red_type	*d; 
{
/* 
  fprintf(RED_OUT, "\nGame-based abstraction for all insigs\n"); 
  red_print_graph(d); 
*/   
  SIG_GAME = sig_word(); 
  d = rec_abstraction_game_based_insig_discrete(d, sig_word());  
/* 
  fprintf(RED_OUT, "-----------------\n"); 
  red_print_graph(d); 
  */ 
  return(d); 
}
  /* red_abstraction_game_based_insig_discrete() */ 
  




struct red_type	*rec_abstraction_game_based_insig_time(d)
     struct red_type	*d; 
{
  int				ci, pi, pj; 
  struct red_type		*result, *child; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(d); 

  ce = cache2_check_result_key(OP_ABSTRACTON_GAME_BASED_INSIG_TIME, 
    d, (struct red_type *) SIG_GAME
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT))
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT))
        ) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_time(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_time(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 crd_atom(d->var_index, 
					  d->u.crd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result = result); 
    } 
    break; 

  case TYPE_CDD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK2]].PROC_INDEX; 
    if (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) 
        || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT)) 
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_time(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_time(d->u.ddd.arc[ci].child);
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 ddd_atom(d->var_index,
					  d->u.ddd.arc[ci].lower_bound, 
					  d->u.ddd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result = result); 
    } 
    break; 

  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_time(d->u.fdd.arc[ci].child); 
      result = red_bop(OR, result, 
	fdd_one_constraint(child, d->var_index, 
	  d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	)
      ); 
    }
    return(ce->result = result); 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_time(d->u.dfdd.arc[ci].child); 
      result = red_bop(OR, result, 
	dfdd_one_constraint(child, d->var_index, 
	  d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	)
      ); 
    }
    return(ce->result = result); 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_time(d->u.ddd.arc[ci].child); 
      result = red_bop(OR, result, 
	ddd_one_constraint(child, d->var_index, 
	  d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
	)
      ); 
    }
    return(ce->result = result); 
    break; 
  }
}
/* rec_abstraction_game_based_insig_time() */ 





struct red_type	*red_abstraction_game_based_insig_time(d) 
	struct red_type	*d; 
{
/* 
  fprintf(RED_OUT, "\nGame-based abstraction for all insigs\n"); 
  red_print_graph(d);
  */ 
  SIG_GAME = sig_word(); 
  d = rec_abstraction_game_based_insig_time(d);  
/* 
  fprintf(RED_OUT, "-----------------\n"); 
  red_print_graph(d); 
  */ 
  return(d); 
}
  /* red_abstraction_game_based_insig_time() */ 
  




struct red_type	*rec_abstraction_game_based_insig_magnitude(d)
     struct red_type	*d; 
{
  int				ci, pi, pj; 
  struct red_type		*result, *child; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(d);

  ce = cache2_check_result_key(
    OP_ABSTRACTION_GAME_BASED_INSIG_MAGNITUDE, 
    d, (struct red_type *) SIG_GAME
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   VAR[d->var_index].U.CRD.CLOCK1 
        && VAR[d->var_index].U.CRD.CLOCK2
        && (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) 
            || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT)) 
            ) 
        ) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_magnitude(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_magnitude(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, 
			 red_bop(AND, child, 
				 crd_atom(d->var_index,
					  d->u.crd.arc[ci].upper_bound
					  )
				 )
			 ); 
      }
      return(ce->result = result); 
    }
    break; 

  case TYPE_CDD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK1]].PROC_INDEX; 
    pj = VAR[CLOCK[VAR[d->var_index].U.CDD.CLOCK2]].PROC_INDEX; 
    if (   VAR[d->var_index].U.CDD.CLOCK1 
        && VAR[d->var_index].U.CDD.CLOCK2
        && (   !(pi == 0 || (PROCESS[pi].status & FLAG_PROC_SIGNIFICANT)) 
            || !(pj == 0 || (PROCESS[pj].status & FLAG_PROC_SIGNIFICANT)) 
            )
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_magnitude(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
    } 
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	child = rec_abstraction_game_based_insig_magnitude(d->u.ddd.arc[ci].child); 
	result = red_bop(OR, result, 
			 ddd_one_constraint(child, 
				 d->var_index, 
				  d->u.ddd.arc[ci].lower_bound,
				  d->u.ddd.arc[ci].upper_bound
				 )
			 ); 
      }
      return(ce->result = result); 
    }
    break; 

  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_magnitude(d->u.fdd.arc[ci].child); 
      result = red_bop(OR, result, fdd_one_constraint(child, d->var_index, 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ) ); 
    }
    return(ce->result = result); 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_magnitude(d->u.dfdd.arc[ci].child); 
      result = red_bop(OR, result, dfdd_one_constraint(child, d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ) ); 
    }
    return(ce->result = result); 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_abstraction_game_based_insig_magnitude(d->u.ddd.arc[ci].child); 
      result = red_bop(OR, result, ddd_one_constraint(child, d->var_index, 
	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ) ); 
    }
    return(ce->result = result); 
    break; 
  }
}
/* rec_abstraction_game_based_insig_magnitude() */ 





struct red_type	*red_abstraction_game_based_insig_magnitude(d) 
	struct red_type	*d;
{
/* 
  fprintf(RED_OUT, "\nGame-based abstraction for all insigs\n"); 
  red_print_graph(d); 
 */
  SIG_GAME = sig_word(); 
  d = rec_abstraction_game_based_insig_magnitude(d);  
/* 
  fprintf(RED_OUT, "-----------------\n"); 
  red_print_graph(d); 
  */ 
  return(d); 
}
  /* red_abstraction_game_based_insig_magnitude() */ 




#define FLAG_GENERIC_NOAPPROX		0
#define FLAG_GENERIC_OAPPROX_DIAG_MAG	1
#define FLAG_GENERIC_OAPPROX_DIAGONAL	2
#define FLAG_GENERIC_OAPPROX_MAGNITUDE	3
#define FLAG_GENERIC_OAPPROX_UNTIMED	4
#define FLAG_GENERIC_OAPPROX_MODE_ONLY	5
#define FLAG_GENERIC_OAPPROX_NONE	6

int	FLAG_GAME_OAPPROX; 

#ifdef RED_DEBUG_ZAPPROX_MODE
int	count_generic_oapprox = 0; 
#endif 

int	flag_generic_oapprox(pi) 
	int	pi; 
{ 
  #ifdef RED_DEBUG_ZAPPROX_MODE
  fprintf(RED_OUT, "\ncount_generic_oapprox = %1d\n", 
    ++count_generic_oapprox
  ); 
  fflush(RED_OUT); 
  #endif 
  
  switch (GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY) { 
  case FLAG_ROOT_NOAPPROX: 
  case FLAG_ROOT_UAPPROX: 
    return(FLAG_GENERIC_NOAPPROX); 
  case FLAG_ROOT_OAPPROX: 
    if (pi) 
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_SPEC_GAME) { 
        case FLAG_NOAPPROX_SPEC_GAME: 
          return(FLAG_GENERIC_NOAPPROX); 
        case FLAG_OAPPROX_SPEC_GAME_DIAG_MAG:
          return(FLAG_GENERIC_OAPPROX_DIAG_MAG); 
        case FLAG_OAPPROX_SPEC_GAME_DIAGONAL:
          return(FLAG_GENERIC_OAPPROX_DIAGONAL); 
        case FLAG_OAPPROX_SPEC_GAME_MAGNITUDE:
          return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
        case FLAG_OAPPROX_SPEC_GAME_UNTIMED: 
          return(FLAG_GENERIC_OAPPROX_UNTIMED); 
        case FLAG_OAPPROX_SPEC_GAME_MODE_ONLY: 
          return(FLAG_GENERIC_OAPPROX_MODE_ONLY); 
        }
        break; 

      case FLAG_GAME_MODL: 
        switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_MODL_GAME) { 
        case FLAG_NOAPPROX_MODL_GAME: 
          return(FLAG_GENERIC_NOAPPROX); 
        case FLAG_OAPPROX_MODL_GAME_DIAG_MAG:
          return(FLAG_GENERIC_OAPPROX_DIAG_MAG); 
        case FLAG_OAPPROX_MODL_GAME_DIAGONAL:
          return(FLAG_GENERIC_OAPPROX_DIAGONAL); 
        case FLAG_OAPPROX_MODL_GAME_MAGNITUDE:
          return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
        case FLAG_OAPPROX_MODL_GAME_UNTIMED: 
          return(FLAG_GENERIC_OAPPROX_UNTIMED); 
        case FLAG_OAPPROX_MODL_GAME_MODE_ONLY: 
          return(FLAG_GENERIC_OAPPROX_MODE_ONLY); 
        }
        break; 
      
      case FLAG_GAME_ENVR: 
        switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_ENVR_GAME) { 
        case FLAG_NOAPPROX_ENVR_GAME: 
          return(FLAG_GENERIC_NOAPPROX); 
        case FLAG_OAPPROX_ENVR_GAME_DIAG_MAG:
          return(FLAG_GENERIC_OAPPROX_DIAG_MAG); 
        case FLAG_OAPPROX_ENVR_GAME_DIAGONAL:
          return(FLAG_GENERIC_OAPPROX_DIAGONAL); 
        case FLAG_OAPPROX_ENVR_GAME_MAGNITUDE:
          return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
        case FLAG_OAPPROX_ENVR_GAME_UNTIMED: 
          return(FLAG_GENERIC_OAPPROX_UNTIMED); 
        case FLAG_OAPPROX_ENVR_GAME_MODE_ONLY: 
          return(FLAG_GENERIC_OAPPROX_MODE_ONLY); 
        }
        break; 
      } 
    else 
      switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_GLOBAL_GAME) { 
      case FLAG_NOAPPROX_GLOBAL_GAME: 
        return(FLAG_GENERIC_NOAPPROX); 
      case FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG:
        return(FLAG_GENERIC_OAPPROX_DIAG_MAG); 
      case FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL:
        return(FLAG_GENERIC_OAPPROX_DIAGONAL); 
      case FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE:
        return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
      case FLAG_OAPPROX_GLOBAL_GAME_UNTIMED: 
        return(FLAG_GENERIC_OAPPROX_UNTIMED); 
      }
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal approximation root value %x \n",
      GSTATUS[INDEX_APPROX] & MASK_ROOT_POLARITY
    ); 
    fprintf(RED_OUT, 
      "       in procedure flag_generic_oapprox(pi=%1d).\n", 
      pi
    ); 
    fflush(RED_OUT); 
    bk(0);  
  } 
}
  /* flag_generic_oapprox() */ 
  
  
  
/*    
int	count_gcineq_tba = 0; 
*/
int	game_clock_ineq_to_be_abstracted(ci, cj) 
	int	ci; 
{ 
  int	vi, vj, pi, pj, flag_oapprox_pi, flag_oapprox_pj; 
  
  vi = CLOCK[ci]; 
  pi = VAR[vi].PROC_INDEX; 
  vj = CLOCK[cj]; 
  pj = VAR[vj].PROC_INDEX; 
  
/*
  fprintf(RED_OUT, "\ngame clock ineq tba %1d, %1d:%s, %1d:%s\n", 
    ++count_gcineq_tba, vi, VAR[vi].NAME, vj, VAR[vj].NAME
  ); 
*/
  flag_oapprox_pi = flag_generic_oapprox(pi); 
  flag_oapprox_pj = flag_generic_oapprox(pj); 
    
  if (ci && cj) { 
    if (   (   flag_oapprox_pi == FLAG_GENERIC_OAPPROX_DIAGONAL 
            || flag_oapprox_pi == FLAG_GENERIC_OAPPROX_DIAG_MAG
            || flag_oapprox_pi == FLAG_GENERIC_NOAPPROX
            ) 
        && (   flag_oapprox_pj == FLAG_GENERIC_OAPPROX_DIAGONAL 
            || flag_oapprox_pj == FLAG_GENERIC_OAPPROX_DIAG_MAG
            || flag_oapprox_pj == FLAG_GENERIC_NOAPPROX
            )
        ) 
      if (   flag_oapprox_pi == FLAG_GENERIC_NOAPPROX
          && flag_oapprox_pj == FLAG_GENERIC_NOAPPROX
          ) 
        return(FLAG_GENERIC_NOAPPROX); 
      else 
        return(FLAG_GENERIC_OAPPROX_DIAGONAL); 
    else 
      return(FLAG_GENERIC_OAPPROX_UNTIMED); 
  } 
  else 
    if (   (   flag_oapprox_pi == FLAG_GENERIC_OAPPROX_MAGNITUDE 
            || flag_oapprox_pi == FLAG_GENERIC_OAPPROX_DIAG_MAG
            || flag_oapprox_pi == FLAG_GENERIC_NOAPPROX
            ) 
        && (   flag_oapprox_pj == FLAG_GENERIC_OAPPROX_MAGNITUDE  
            || flag_oapprox_pj == FLAG_GENERIC_OAPPROX_DIAG_MAG
            || flag_oapprox_pj == FLAG_GENERIC_NOAPPROX
            )
        ) 
      if (   flag_oapprox_pi == FLAG_GENERIC_NOAPPROX
          && flag_oapprox_pj == FLAG_GENERIC_NOAPPROX
          ) 
        return(FLAG_GENERIC_NOAPPROX); 
      else 
        return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
    else 
      return(FLAG_GENERIC_OAPPROX_UNTIMED); 
}
  /* game_clock_ineq_to_be_abstracted() */  
  
  


int	count_dynamics(he)
	struct hrd_exp_type	*he; 
{ 
  int	count_dynamic, len, hi, vi, pi; 
  
  count_dynamic = 0; 
  len = he->status & MASK_HYBRID_LENGTH; 
  for (hi = 0; hi < len; hi++) { 
    vi = he->hrd_term[hi].var_index; 
    pi = VAR[vi].PROC_INDEX; 
    if ((VAR[vi].STATUS & FLAG_VAR_STATIC) && VAR[vi].TYPE == TYPE_DENSE) 
      continue; 
    count_dynamic++; 
  } 
  return(count_dynamic); 
}
  /* count_dynamics() */ 
  
  
  
int 	game_hybrid_ineq_to_be_abstracted(he) 
	struct hrd_exp_type	*he; 
{ 
  int	len, hi, pi, vi, 
	flag_global, flag_envr, flag_modl, flag_spec, 
  	min, fa; 
  
  flag_global = flag_envr = flag_modl = flag_spec = 0; 
  len = he->status & MASK_HYBRID_LENGTH; 
  for (hi = 0; hi < len; hi++) { 
    vi = he->hrd_term[hi].var_index; 
    pi = VAR[vi].PROC_INDEX; 
    if (!pi) 
      flag_global = 1; 
    else switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_MODL: 
      flag_global = 1; 
      break; 
    case FLAG_GAME_ENVR: 
      flag_global = 1; 
      break; 
    case FLAG_GAME_SPEC: 
      flag_global = 1; 
      break; 
    } 
  } 
  min = FLAG_GENERIC_NOAPPROX; 
  if (flag_global) {
    fa = (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_GLOBAL_GAME & ~(0xF0000)) / (0x1000); 
    if (min < fa) 
      min = fa; 
  } 
  if (flag_envr) {
    fa = (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_ENVR_GAME & ~(0xF0000)) / (0x100); 
    if (min < fa) 
      min = fa; 
  } 
  if (flag_modl) {
    fa = (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_MODL_GAME & ~(0xF0000)) / (0x10); 
    if (min < fa) 
      min = fa; 
  } 
  if (flag_spec) {
    fa = (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_SPEC_GAME & ~(0xF0000)); 
    if (min < fa) 
      min = fa; 
  } 
  switch (min) { 
  case FLAG_GENERIC_NOAPPROX: 
    return(FLAG_GENERIC_NOAPPROX); 
  case FLAG_GENERIC_OAPPROX_DIAG_MAG: 
    if (len == 2)
      if (   (he->hrd_term[0].coeff < 0 && he->hrd_term[1].coeff > 0) 
          || (he->hrd_term[0].coeff > 0 && he->hrd_term[1].coeff < 0) 
          )
        return (FLAG_GENERIC_OAPPROX_DIAGONAL); 
      else 
        return (FLAG_GENERIC_OAPPROX_UNTIMED); 
    else if (len > 2 && count_dynamics(he) > 2) 
      return(FLAG_GENERIC_OAPPROX_UNTIMED); 
    else 
      return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
  case FLAG_GENERIC_OAPPROX_DIAGONAL: 
    if (len == 2)
      if (   (he->hrd_term[0].coeff < 0 && he->hrd_term[1].coeff > 0) 
          || (he->hrd_term[0].coeff > 0 && he->hrd_term[1].coeff < 0) 
          ) 
        return (FLAG_GENERIC_OAPPROX_DIAGONAL); 
      else 
        return (FLAG_GENERIC_OAPPROX_UNTIMED); 
    else if (len > 2 && count_dynamics(he) > 2) 
      return(FLAG_GENERIC_OAPPROX_UNTIMED); 
    else 
      return(FLAG_GENERIC_OAPPROX_MAGNITUDE); 
  case FLAG_GENERIC_OAPPROX_MAGNITUDE: 
    if (len > 1 && count_dynamics(he) > 1) 
      return(FLAG_GENERIC_OAPPROX_UNTIMED); 
    else 
      return(FLAG_GENERIC_OAPPROX_MAGNITUDE);       
  case FLAG_GENERIC_OAPPROX_UNTIMED: 
  case FLAG_GENERIC_OAPPROX_MODE_ONLY: 
  case FLAG_GENERIC_OAPPROX_NONE: 
    return(FLAG_GENERIC_OAPPROX_UNTIMED); 
  } 
}
  /* game_hybrid_ineq_to_be_abstracted() */ 
  
    

  
  
int 	game_discrete_to_be_abstracted(vi) 
	int	vi; 
{ 
  int	pi; 
  
  pi = VAR[vi].PROC_INDEX; 
  if (!pi) 
    return ((GSTATUS[INDEX_APPROX] & MASK_OAPPROX_GLOBAL_GAME) / (0x1000)); 
  else switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
  case FLAG_GAME_ENVR: 
    return(
      (  GSTATUS[INDEX_APPROX] 
       & MASK_OAPPROX_ENVR_GAME 
       & ~MASK_OAPPROX_STRATEGY
       ) / (0x100)
    ); 
  case FLAG_GAME_MODL: 
    return(
      (  GSTATUS[INDEX_APPROX] 
       & MASK_OAPPROX_MODL_GAME 
       & ~MASK_OAPPROX_STRATEGY
       ) / (0x10)
    ); 
  case FLAG_GAME_SPEC: 
    return(
        GSTATUS[INDEX_APPROX] 
      & MASK_OAPPROX_SPEC_GAME 
      & ~MASK_OAPPROX_STRATEGY
    ); 
  } 
}
  /* game_discrete_to_be_abstracted() */ 
  
    


#ifdef RED_DEBUG_ZAPPROX_MODE
int	count_abs_game = 0; 
#endif 

struct red_type	*rec_abs_game(d)
     struct red_type	*d; 
{
  int				c1, c2, ci, vi, cvi, cci, flag_abs; 
  struct red_type		*result, *child, *gchild; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(d);

  ce = cache2_check_result_key(OP_ABS_GAME, d, 
    (struct red_type *) FLAG_GAME_OAPPROX
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 

    #ifdef RED_DEBUG_ZAPPROX_MODE
    fprintf(RED_OUT, "abs game %1d:%s\n", 
      ++count_abs_game, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
    #endif 

    switch (game_clock_ineq_to_be_abstracted(c1, c2)) { 
    case FLAG_GENERIC_OAPPROX_DIAGONAL: 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        if (   d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY
            && !(d->u.crd.arc[ci].upper_bound % 2)
            ) { 
          child = d->u.crd.arc[ci].child; 
          cvi = child->var_index; 
          if (   cvi == ZONE[c2][c1] 
              && child->u.crd.child_count == 1
              && d->u.crd.arc[ci].upper_bound 
		 + child->u.crd.arc[0].upper_bound == 0
	      ) {
	    gchild = rec_abs_game(child->u.crd.arc[0].child); 
	    gchild = crd_one_constraint(
	      gchild, d->var_index, 
	      d->u.crd.arc[ci].upper_bound
	    ); 
	    gchild = crd_one_constraint(
	      gchild, ZONE[c2][c1], 
	      child->u.crd.arc[0].upper_bound
	    ); 
	    result = red_bop(OR, result, gchild); 
	  } 
	  else { 
	    child = rec_abs_game(d->u.crd.arc[ci].child); 
	    result = red_bop(OR, result, child); 
	  } 
        } 
        else { 
	  child = rec_abs_game(d->u.crd.arc[ci].child); 
	  result = red_bop(OR, result, child); 
	} 
      }
      return(ce->result = result); 
      break; 

    case FLAG_GENERIC_OAPPROX_UNTIMED: 
    case FLAG_GENERIC_OAPPROX_NONE: 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abs_game(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
      break; 
    case FLAG_GENERIC_OAPPROX_MAGNITUDE: 
    case FLAG_GENERIC_NOAPPROX: 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_abs_game(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, 
			 crd_one_constraint(
				child, 
				d->var_index,
				d->u.crd.arc[ci].upper_bound
				)
			 ); 
      }
      return(ce->result = result); 
      break; 
    }
    break; 
    
  case TYPE_HRD: 
    switch (game_hybrid_ineq_to_be_abstracted(d->u.hrd.hrd_exp)) { 
    case FLAG_GENERIC_OAPPROX_DIAGONAL: 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) { 
        if (   (   d->u.hrd.arc[ci].ub_numerator < HYBRID_POS_INFINITY
                || d->u.hrd.arc[ci].ub_denominator > 1
                ) 
            && !(d->u.hrd.arc[ci].ub_numerator % 2)
            ) { 
          child = d->u.hrd.arc[ci].child; 
          cvi = child->var_index;   
          if (   hrd_exp_converse_test(d->u.hrd.hrd_exp, child)
              && child->u.hrd.child_count == 1
              && d->u.hrd.arc[ci].ub_numerator 
	         + child->u.hrd.arc[0].ub_numerator == 0
	      && d->u.hrd.arc[ci].ub_denominator 
	         == child->u.hrd.arc[0].ub_denominator 
	      ) { 
	    gchild = rec_abs_game(child->u.hrd.arc[0].child); 
	    gchild = hrd_one_constraint(
	      gchild, d->u.hrd.hrd_exp, 
	      d->u.hrd.arc[ci].ub_numerator, 
	      d->u.hrd.arc[ci].ub_denominator
	    ); 
	    gchild = hrd_one_constraint(
	      gchild, child->u.hrd.hrd_exp, 
	      child->u.hrd.arc[0].ub_numerator, 
	      child->u.hrd.arc[0].ub_denominator
	    ); 
	    result = red_bop(OR, result, gchild); 
	  } 
	  else { 
	    child = rec_abs_game(d->u.hrd.arc[ci].child); 
	    result = red_bop(OR, result, child); 
	  } 
        } 
        else { 
	  child = rec_abs_game(d->u.hrd.arc[ci].child); 
	  result = red_bop(OR, result, child); 
	} 
      }
      return(ce->result = result); 
      break; 

    case FLAG_GENERIC_OAPPROX_UNTIMED: 
    case FLAG_GENERIC_OAPPROX_NONE: 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = rec_abs_game(d->u.hrd.arc[ci].child); 
	result = red_bop(OR, result, child); 
      }
      return(ce->result = result); 
      break; 
    case FLAG_GENERIC_OAPPROX_MAGNITUDE: 
    case FLAG_GENERIC_NOAPPROX: 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = rec_abs_game(d->u.hrd.arc[ci].child); 
	result = red_bop(OR, result, 
			 hrd_one_constraint(
				child, d->u.hrd.hrd_exp, 
				d->u.hrd.arc[ci].ub_numerator, 
				d->u.hrd.arc[ci].ub_denominator
	    		 )); 
      }
      return(ce->result = result); 
      break; 
    }
    break; 
    
  case TYPE_FLOAT: 
    flag_abs = game_discrete_to_be_abstracted(d->var_index); 
    // first when to abstract, 
    if (   flag_abs == FLAG_GENERIC_OAPPROX_NONE 
        || (   flag_abs == FLAG_GENERIC_OAPPROX_MODE_ONLY
            && VAR[d->var_index].PROC_INDEX
            && VAR[d->var_index].OFFSET != OFFSET_MODE
            ) 
	) { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abs_game(d->u.fdd.arc[ci].child); 
        result = red_bop(OR, result, child); 
      } 
    }
    else { 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        child = rec_abs_game(d->u.fdd.arc[ci].child); 
        result = red_bop(OR, result, 
	  fdd_one_constraint(child, d->var_index, 
	    d->u.fdd.arc[ci].lower_bound, 
	    d->u.fdd.arc[ci].upper_bound
	  )
	); 
      } 
    } 
    return(ce->result = result); 
    break; 
  case TYPE_DOUBLE: 
    flag_abs = game_discrete_to_be_abstracted(d->var_index); 
    // first when to abstract, 
    if (   flag_abs == FLAG_GENERIC_OAPPROX_NONE 
        || (   flag_abs == FLAG_GENERIC_OAPPROX_MODE_ONLY
            && VAR[d->var_index].PROC_INDEX
            && VAR[d->var_index].OFFSET != OFFSET_MODE
            ) 
	) { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abs_game(d->u.dfdd.arc[ci].child); 
        result = red_bop(OR, result, child); 
      } 
    }
    else { 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        child = rec_abs_game(d->u.dfdd.arc[ci].child); 
        result = red_bop(OR, result, 
	  dfdd_one_constraint(child, d->var_index, 
	    d->u.dfdd.arc[ci].lower_bound, 
	    d->u.dfdd.arc[ci].upper_bound
	  )
	); 
      } 
    } 
    return(ce->result = result); 
    break; 
  default: 
    flag_abs = game_discrete_to_be_abstracted(d->var_index); 
    // first when to abstract, 
    if (   flag_abs == FLAG_GENERIC_OAPPROX_NONE 
        || (   flag_abs == FLAG_GENERIC_OAPPROX_MODE_ONLY
            && VAR[d->var_index].PROC_INDEX
            && VAR[d->var_index].OFFSET != OFFSET_MODE
            ) 
	) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abs_game(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result, child); 
      } 
    }
    else { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_abs_game(d->u.ddd.arc[ci].child); 
        result = red_bop(OR, result, 
	  ddd_one_constraint(child, d->var_index, 
	    d->u.ddd.arc[ci].lower_bound, 
	    d->u.ddd.arc[ci].upper_bound
	  )
	); 
      } 
    } 
    return(ce->result = result); 
    break; 
  }
}
/* rec_abs_game() */ 





struct red_type	*red_abs_game(d, flag_oapprox) 
	struct red_type	*d;
{
/*
  fprintf(RED_OUT, "\nred abs game()\n"); 
  red_print_graph(d); 
*/
  FLAG_GAME_OAPPROX = flag_oapprox; 
  d = rec_abs_game(d);  
/*  
  fprintf(RED_OUT, "-----------------\n"); 
  red_print_graph(d); 
*/
  return(d); 
}
  /* red_abs_game() */ 







void	union_abstract_new(old, new, flag_polarity)
	int old, new, flag_polarity;
{
  int	tmp, post;
/*
  fprintf(RED_OUT, "\n==[I%1d]=======================================\n", 
  	  ITERATION_COUNT
  	  ); 
  fprintf(RED_OUT, "IT:%1d, RT[old=%1d] in union_abstract_new(), entering union_abstract_new()\n", 
	  ITERATION_COUNT, old 
	  ); 
  red_print_graph(RT[old]); 
*/
  RT[tmp = RT_TOP++] = RT[old];
  switch (flag_polarity) {
  case FLAG_ROOT_OAPPROX: 
/*
    fprintf(RED_OUT, "IT:%1d, RT[new] in union_abstract_new(), before \n", 
	    ITERATION_COUNT
	    ); 
    red_print_graph(RT[new]); 
*/
    switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_STRATEGY) { 
    case FLAG_OAPPROX_STRATEGY_SLICE: 
      switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) {
      case FLAG_OAPPROX_SLICE_MAGNITUDE:
        if (CLOCK_COUNT > 1)
	  RT[new] = red_abstraction_game_based_insig_magnitude(RT[new]);
        RT[old] = red_bop(OR, RT[old], RT[new]);
        if (CLOCK_COUNT > 1)
	  RT[old] = red_subsume(RT[old]);
        break;
      case FLAG_OAPPROX_SLICE_NONE:
        if (CLOCK_COUNT > 1)
	  RT[new] = red_abstraction_game_based_insig(RT[new]);
        RT[old] = red_bop(OR, RT[old], RT[new]);
        if (CLOCK_COUNT > 1)
	  RT[old] = red_subsume(RT[old]);
        break;
      case FLAG_OAPPROX_SLICE_UNTIMED:
        if (CLOCK_COUNT > 1)
	  RT[new] = red_abstraction_game_based_insig_time(RT[new]);
        RT[old] = red_bop(OR, RT[old], RT[new]);
        if (CLOCK_COUNT > 1)
	  RT[old] = red_subsume(RT[old]);
        break;
      case FLAG_OAPPROX_SLICE_MODE_ONLY:
        if (CLOCK_COUNT > 1)
	  RT[new] = red_abstraction_game_based_insig_discrete(RT[new]);
        RT[old] = red_bop(OR, RT[old], RT[new]);
        if (CLOCK_COUNT > 1)
	  RT[old] = red_subsume(RT[old]);
        break;

      default:
        RT[old] = red_bop(OR, RT[old], RT[new]);
/* 
        if (CLOCK_COUNT > 1)
	  RT[old] = zone_convex_hull(RT[old]);
*/
        break;
      }
      break; 
    case FLAG_OAPPROX_STRATEGY_GAME: 
      RT[new] = red_abs_game(RT[new], GSTATUS[INDEX_APPROX] & MASK_OAPPROX);
/*
      fprintf(RED_OUT, "IT:%1d, RT[new=%1d] in union_abstract_new(), after game abstraction\n", 
	      ITERATION_COUNT, new 
	      ); 
      red_print_graph(RT[new]); 
*/
      RT[old] = red_bop(OR, RT[old], RT[new]); 
/*
      fprintf(RED_OUT, "IT:%1d, RT[old=%1d] in union_abstract_new(), after OR\n", 
	      ITERATION_COUNT, old 
	      ); 
      red_print_graph(RT[old]); 
*/
      if (CLOCK_COUNT > 1) {
	RT[old] = red_subsume(RT[old]);
/*
        fprintf(RED_OUT, "IT:%1d, RT[old=%1d] in union_abstract_new(), after subsumption\n", 
	        ITERATION_COUNT, old 
	        ); 
        red_print_graph(RT[old]); 
*/
      } 
      break; 
    }
    RT[new] = red_bop(EXCLUDE, RT[old], RT[tmp]);
/*
    fprintf(RED_OUT, "IT:%1d, RT[new] in union_abstract_new(), after exclusion\n", 
	    ITERATION_COUNT
	    ); 
    red_print_graph(RT[new]); 
*/
    break;
  default:
    RT[old] = red_bop(OR, RT[old], RT[new]);

    if (CLOCK_COUNT > 1)
      RT[old] = red_subsume(RT[old]);
    bug_flag1 = TYPE_TRUE;
    RT[new] = red_bop(EXCLUDE, RT[old], RT[tmp]);
    bug_flag1 = TYPE_FALSE;
  }
  RT_TOP--; // tmp 
}
/* union_abstract_new() */





void	red_abs(w, flag_oapprox)
	int 	w, flag_oapprox; 
{
  if (CLOCK_COUNT <= 1)
    return;

  if (flag_oapprox == FLAG_ROOT_OAPPROX) { 
    switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX_STRATEGY) { 
    case FLAG_OAPPROX_STRATEGY_SLICE: 
      switch (GSTATUS[INDEX_APPROX] & MASK_OAPPROX) { 
      case FLAG_OAPPROX_SLICE_MAGNITUDE: 
        RT[w] = red_abstraction_game_based_insig_magnitude(RT[w]); 
        RT[w] = red_subsume(RT[w]); 
        break; 
      case FLAG_OAPPROX_SLICE_NONE:  
        RT[w] = red_abstraction_game_based_insig(RT[w]); 
        RT[w] = red_subsume(RT[w]); 
        break; 
      case FLAG_OAPPROX_SLICE_UNTIMED: 
        RT[w] = red_abstraction_game_based_insig_time(RT[w]); 
        RT[w] = red_subsume(RT[w]); 
        break;
      case FLAG_OAPPROX_SLICE_MODE_ONLY: 
        RT[w] = red_abstraction_game_based_insig_discrete(RT[w]); 
        RT[w] = red_subsume(RT[w]); 
        break; 

      default: 
/*
        RT[w] = zone_convex_hull(RT[w]); 
*/
        break; 
      }
    case FLAG_OAPPROX_STRATEGY_GAME: 
      RT[w] = red_abs_game(RT[w], GSTATUS[INDEX_APPROX] & MASK_OAPPROX);
      RT[w] = red_subsume(RT[w]); 
      break; 
    } 
  }
  else { 
    RT[w] = red_subsume(RT[w]); 
  } 
}
/* red_abs() */ 



  

void	zapprox_test_print(d, s, pi)
	struct red_type	*d; 
	char		*s; 
	int		pi; 
{
  fprintf(RED_OUT, "\n================================================\n"); 
  fprintf(RED_OUT, "Test abstraction on %s:\n", s); 
  red_print_graph(d); 
  fprintf(RED_OUT, "\n------------------------------------------------\n");
  fprintf(RED_OUT, "Test zone_convex_hull(%s):\n", s); 
  red_print_graph(zone_convex_hull(d)); 
  
  fprintf(RED_OUT, "\n------------------------------------------------\n"); 
  pi = (pi-1)%PROCESS_COUNT + 1; 
  fprintf(RED_OUT, "Test game based(%s) on process %1d:\n", s, pi); 
  red_abstraction_game_based_insig(d, pi); 
  fprintf(RED_OUT, "\n------------------------------------------------\n"); 
  fprintf(RED_OUT, "Test game based insig discrete (%s):\n", s); 
  red_abstraction_game_based_insig_discrete(d); 
  fprintf(RED_OUT, "\n------------------------------------------------\n"); 
  fprintf(RED_OUT, "Test game based insig time (%s):\n", s);
  red_abstraction_game_based_insig_time(d); 
  fprintf(RED_OUT, "\n------------------------------------------------\n"); 
  fprintf(RED_OUT, "Test game based insig magnitude (%s):\n", s); 
  red_abstraction_game_based_insig_magnitude(d); 	
}
/* zapprox_test_print() */ 



void 	zapprox_test() 
{
  int			pi; 
  struct red_type	*t0, *t1, *t2, *t3, *t4, *result; 

  /* construct the first test */ 
  t0 = ddd_atom(variable_index[TYPE_DISCRETE][1][0], 0, 0); 

  if (CLOCK_COUNT > 1) { 
    t0 = red_bop(AND, t0, crd_atom(ZONE[2][0], 0)); 
  }
  zapprox_test_print(t0, "t0", 1); 
  
  /* construct the first test */ 
  t1 = ddd_atom(variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  if (PROCESS_COUNT > 1) 
    t1 = red_bop(AND, t1, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 0, 0));  
  if (PROCESS_COUNT > 2) 
    t1 = red_bop(AND, t1, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 0, 0));  

  if (CLOCK_COUNT > 0) {
    t1 = red_bop(AND, t1, crd_atom(ZONE[0][1], -2)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[1][0], 4));
  }
  if (CLOCK_COUNT > 1) { 
    t1 = red_bop(AND, t1, crd_atom(ZONE[0][2], -4)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[2][0], 6)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[1][2], -6)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[2][1], 8)); 
  }
  if (CLOCK_COUNT > 2) { 
    t1 = red_bop(AND, t1, crd_atom(ZONE[0][3], -8)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[3][0], 10)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[1][3], -10)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[3][1], 12)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[2][3], -12)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[3][2], 14)); 
  }
  if (CLOCK_COUNT > 3) { 
    t1 = red_bop(AND, t1, crd_atom(ZONE[0][4], -14)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[4][0], 16)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[2][4], -16)); 
    t1 = red_bop(AND, t1, crd_atom(ZONE[4][2], 18));
  }  
  
  zapprox_test_print(t1, "t1", 1); 
  result = t1; 
  
  /* construct the 2nd test */ 
  t2 = ddd_atom(variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  if (PROCESS_COUNT > 1) 
    t2 = red_bop(AND, t2, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 0, 0));  
  if (PROCESS_COUNT > 2) 
    t2 = red_bop(AND, t2, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 0, 0));  

  if (CLOCK_COUNT > 0) {
    t2 = red_bop(AND, t2, crd_atom(ZONE[0][1], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[1][0], 2)); 
  }
  if (CLOCK_COUNT > 1) { 
    t2 = red_bop(AND, t2, crd_atom(ZONE[0][2], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[2][0], 4)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[1][2], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[2][1], 6)); 
  }
  if (CLOCK_COUNT > 2) { 
    t2 = red_bop(AND, t2, crd_atom(ZONE[0][3], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[3][0], 8)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[1][3], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[3][1], 10)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[2][3], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[3][2], 12)); 
  }
  if (CLOCK_COUNT > 3) { 
    t2 = red_bop(AND, t2, crd_atom(ZONE[0][4], 0));
    t2 = red_bop(AND, t2, crd_atom(ZONE[4][0], 14)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[2][4], 0)); 
    t2 = red_bop(AND, t2, crd_atom(ZONE[4][2], 16)); 
  }  

  zapprox_test_print(t2, "t2", 2); 
  result = red_bop(OR, result, t2); 
  zapprox_test_print(result, "result/t2", 2);   

  /* construct the 3rd test */ 
  t3 = ddd_atom(variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  if (PROCESS_COUNT > 1)
    t3 = red_bop(AND, t3, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 1, 1));  
  if (PROCESS_COUNT > 2) 
    t3 = red_bop(AND, t3, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 0, 0));  

  if (CLOCK_COUNT > 0) {
    t3 = red_bop(AND, t3, crd_atom(ZONE[0][1], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[1][0], 2)); 
  }
  if (CLOCK_COUNT > 1) { 
    t3 = red_bop(AND, t3, crd_atom(ZONE[0][2], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[2][0], 4)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[1][2], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[2][1], 6)); 
  }
  if (CLOCK_COUNT > 2) { 
    t3 = red_bop(AND, t3, crd_atom(ZONE[0][3], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[3][0], 8)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[1][3], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[3][1], 10)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[2][3], 0));
    t3 = red_bop(AND, t3, crd_atom(ZONE[3][2], 12)); 
  }
  if (CLOCK_COUNT > 3) { 
    t3 = red_bop(AND, t3, crd_atom(ZONE[0][4], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[4][0], 14)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[2][4], 0)); 
    t3 = red_bop(AND, t3, crd_atom(ZONE[4][2], 16)); 
  }  
  zapprox_test_print(t3, "t3", 3); 
  result = red_bop(OR, result, t3); 
  zapprox_test_print(result, "result/t3", 3);   

  /* construct the 3rd test */ 
  t4 = ddd_atom(variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  if (PROCESS_COUNT > 1) 
    t4 = red_bop(AND, t4, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 0, 0));  
  if (PROCESS_COUNT > 2) 
    t4 = red_bop(AND, t4, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 0, 0));  

  if (CLOCK_COUNT > 0) {
    t4 = red_bop(AND, t4, crd_atom(ZONE[0][1], 0)); 
    t4 = red_bop(AND, t4, crd_atom(ZONE[1][0], 2)); 
  }
  if (CLOCK_COUNT > 1) { 
    t4 = red_bop(AND, t4, crd_atom(ZONE[0][2], 0)); 
    t4 = red_bop(AND, t4, crd_atom(ZONE[2][1], -5)); 
  }
  if (CLOCK_COUNT > 2) { 
    t4 = red_bop(AND, t4, crd_atom(ZONE[3][0], 7)); 
    t4 = red_bop(AND, t4, crd_atom(ZONE[1][3], -3)); 
    t4 = red_bop(AND, t4, crd_atom(ZONE[3][2], 9)); 
  }
  if (CLOCK_COUNT > 3) { 
    t4 = red_bop(AND, t4, crd_atom(ZONE[2][4], -10)); 
    t4 = red_bop(AND, t4, crd_atom(ZONE[4][2], -7)); 
  }  
  zapprox_test_print(t4, "t4", 4);   
  result = red_bop(OR, result, t4); 
  zapprox_test_print(result, "result/t4", 4);   

  
}
/* zapprox_test() */ 
