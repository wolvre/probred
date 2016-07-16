#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
*/
#include <string.h> 
#include <math.h>

#include <float.h>
#include <limits.h> 

#include "redbasics.h"
#include "redbasics.e"

#include "fxp.h" 
#include "counter.e"

#include "vindex.e"

#include "redbop.h"
#include "redparse.h"
#include "redparse.e"

#include "exp.e" 

#include "zone.h"  
#include "zone.e" 

#include "action.e" 

#include "treeman.h"
#include "treeman.e"

#include "hashman.h"
#include "hashman.e"

#include "hybrid.e"

#include "mbdd.h" 


int	*MASK_STACK, *MASK_STACK_REFERENCED, *MASK_STACK_MULTIPLE,
	TOP_LEVEL_RESULT_STACK;


struct variable_type	*VAR;
struct vop_type		*VAR_OP;
int			VARIABLE_COUNT, VOP_LIMIT;

int		ichild_count, ichild_link_count; 
int		fchild_count, fchild_link_count; 
int		dfchild_count, dfchild_link_count; 
int 		bchild_count, bchild_link_count;

int		result_count, rec_count, rec3_count, rec5_count; 

int	drec_count, qrec_count; 

int	red_gc_all_count, red_gc_mark_count, red_gc_unmarked_count; 

int	MAX_MEM;

int	red_count;

struct red_type	*NORM_FALSE, *NORM_TRUE, *NORM_NO_RESTRICTION;

struct child_stack_frame_type 	*CHILD_STACK; 

int	TOP_CHILD_STACK = -1; 
int	TOP_LEVEL_CHILD_STACK = -1, *LEVEL_CHILD_COUNT; 
int	HEIGHT_CHILD_STACK, HEIGHT_LEVEL_CHILD_STACK; 

int	count_top_level_child_stack = 0; 
int	count_top_child_stack = 0; 

int	mbug_flag, FLAG_ZONE_REPRESENTATION;

int 	mop_count;

char	BUFFER_LINE[256];

struct red_type	
  *bdd_one_constraint(struct red_type *, int, int); 
struct red_type	
  *red_bop(int, struct red_type *, struct red_type *); 





int	MAX_TREE_USAGE, MAX_RESULT_USAGE, MAX_RESULT_STACK_HEIGHT, MAX_RT_HEIGHT; 

extern void hsp(); 

void	red_print_graph(
  struct red_type	*
); 

void	check_order(vi, d) 
	int		vi; 
	struct red_type	*d; 
{ 
  if (   vi >= d->var_index 
      && d != NORM_NO_RESTRICTION
      && d != NORM_FALSE
      ) { 
    fprintf(RED_OUT, "Out of order in rec_or\n"); 
    bk(0);   	
  } 
}
  /* check_order() */  
  
  



  
  
void	  update_memory_usage() 
{
  int cur_mem; 

  cur_mem = report_hash_management(FLAG_GC_SILENT);
  if (cur_mem > MAX_TREE_USAGE)
    MAX_TREE_USAGE = cur_mem;
  if (TOP_LEVEL_RESULT_STACK > MAX_RESULT_STACK_HEIGHT)
    MAX_RESULT_STACK_HEIGHT = TOP_LEVEL_RESULT_STACK;
  if (RT_TOP > MAX_RT_HEIGHT)
    MAX_RT_HEIGHT = RT_TOP;
  cur_mem
    = cur_mem
    + GARBAGE_OVERHEAD
    + red_count*sizeof(struct red_type)
    + ichild_count*sizeof(struct ddd_child_type)
    + bchild_count*sizeof(struct crd_child_type)
    + rec_count*sizeof(struct rec_type)
    + drec_count * sizeof(struct double_rec_type);

  if (cur_mem > MAX_MEM)
    MAX_MEM = cur_mem;
}
/* update_memory_usage() */






int	node_count, arc_count;

int	rec_size(d)
     struct red_type	*d;
{
  int				ci, size;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE || d == NORM_NO_RESTRICTION)
    return(0);

  ce = cache1_check_result_key(OP_QUERY_SIZE, d); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  size = sizeof(struct red_type); 
  node_count = node_count + 1; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    arc_count = arc_count + 2; 
    size = size + rec_size(d->u.bdd.zero_child) + rec_size(d->u.bdd.one_child); 
    break; 
  case TYPE_CRD: 
    arc_count = arc_count + d->u.crd.child_count;
    size = size + d->u.crd.child_count * sizeof(struct crd_child_type); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    arc_count = arc_count + d->u.hrd.child_count;
    size = size + d->u.hrd.child_count * sizeof(struct hrd_child_type); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size(d->u.hrd.arc[ci].child);
    }
    break; 

  case TYPE_LAZY_EXP: 
    arc_count = arc_count + 2; 
    size = size 
    + rec_size(d->u.lazy.false_child) 
    + rec_size(d->u.lazy.true_child); 
    break; 
  
  case TYPE_FLOAT: 
    arc_count = arc_count + d->u.fdd.child_count;
    size = size + d->u.fdd.child_count * sizeof(struct fdd_child_type); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size(d->u.fdd.arc[ci].child);
    }
    break; 

  case TYPE_DOUBLE: 
    arc_count = arc_count + d->u.dfdd.child_count;
    size = size + d->u.dfdd.child_count * sizeof(struct dfdd_child_type); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size(d->u.dfdd.arc[ci].child);
    }
    break; 

  default:
    arc_count = arc_count + d->u.ddd.child_count;
    size = size + d->u.ddd.child_count * sizeof(struct ddd_child_type); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size(d->u.ddd.arc[ci].child);
    }
  }
  ce->result = (struct red_type *) size;
  return(size);
}
/* rec_size() */


int 	red_size(d, flag_report, node_count_ptr, arc_count_ptr)
     struct red_type	*d;
     int		flag_report, *node_count_ptr, *arc_count_ptr;
{
  int	size;

  node_count = arc_count = 0;

  size = rec_size(d) + sizeof(struct red_type) /* for false or true */;
  if (flag_report == SIZE_REPORT)
    fprintf(RED_OUT, "\nRED at %x:%s is of %1d nodes, %1d arcs, and memory size: %1d.\n",
	    (unsigned int) d, VAR[d->var_index].NAME,
	    node_count, arc_count, size
	    );
  if (node_count_ptr) 
    *node_count_ptr = node_count; 
  if (arc_count_ptr) 
    *arc_count_ptr = arc_count; 
  
  return(size);
}
/* red_size() */






int	rec_size_space(d)
     struct red_type	*d;
{
  int				ci, size;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  ce = cache1_check_result_key(OP_SIZE_SPACE, d); 
  if (ce->result) {
    return(0);
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_FALSE: 
  case TYPE_TRUE: 
    return(SIZEOF_RED_BASIC);
  case TYPE_CRD: 
    size = SIZEOF_RED_BASIC 
    + d->u.crd.child_count * SIZEOF_RED_CRD_CHILD; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size_space(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    size = SIZEOF_RED_BASIC 
    + SIZEOF_RED_HRD + d->u.hrd.child_count * SIZEOF_RED_HRD_CHILD; 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size_space(d->u.hrd.arc[ci].child);
    }
    break; 

  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    size = SIZEOF_RED_BASIC + SIZEOF_RED_BDD 
	 + rec_size_space(d->u.bdd.one_child) 
	 + rec_size_space(d->u.bdd.zero_child); 
    break; 
    
  case TYPE_FLOAT:
    size = SIZEOF_RED_BASIC + d->u.fdd.child_count * SIZEOF_RED_DDD_CHILD; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size_space(d->u.fdd.arc[ci].child);
    }
    break; 
    
  case TYPE_DOUBLE:
    size = SIZEOF_RED_BASIC + d->u.dfdd.child_count * SIZEOF_RED_DDD_CHILD; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size_space(d->u.dfdd.arc[ci].child);
    }
    break; 
    
  default:
    size = SIZEOF_RED_BASIC + d->u.ddd.child_count * SIZEOF_RED_DDD_CHILD; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      size = size + rec_size_space(d->u.ddd.arc[ci].child);
    }
  }
  ce->result = NORM_NO_RESTRICTION;  
  return(size);
}
/* rec_size_space() */




int 	size_space(count, d)
     int		count; 
     struct red_type	**d;
{
  int	i, size;

  size = 0;  
  for (i = 0; i < count; i++) 
    size = size + rec_size_space(d[i]);

  return(size);
}
/* size_space() */






int	count_red_alloc = 0; 

struct red_type	*test_d;

struct red_type *red_alloc(vi)
     int	vi;
{
  struct red_type		*d;
  int				flag, i;
  struct ddd_child_link_type	*ic;

  if (vi < 0 || vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\n\nAn illegal vi in red_alloc(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0);
  }
/* 
  else if (vi == 311) { 
    fprintf(RED_OUT, "\nred_alloc(vi=%1d) caught!\n", vi); 
    fflush(RED_OUT); 

//    bk(0); 
  } 
*/ 
//  if (!((++count_red_alloc)%10000))
//    garbage_collect_from_red_alloc(FLAG_GC_SILENT); 
/*
  fprintf(RED_OUT, "count red allocate = %1d.\n", ++count_red_alloc); 
  fflush(RED_OUT); 
  for (; count_red_alloc == 0; ); 
*/  
/*
  switch (VAR[vi].TYPE) { 
  case TYPE_FALSE:
  case TYPE_TRUE:  
    d = (struct red_type *) malloc(SIZEOF_RED_TERMINAL);
    break; 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    d = (struct red_type *) malloc(SIZEOF_RED_BDD); 
    break; 
  case TYPE_CRD: 
    d = (struct red_type *) malloc(SIZEOF_RED_CRD); 
    break; 
  case TYPE_HRD: 
    d = (struct red_type *) malloc(SIZEOF_RED_HRD); 
    break; 
  case TYPE_HDD: 
    d = (struct red_type *) malloc(SIZEOF_RED_HDD); 
    break; 

  case TYPE_CDD: 
  default: 
    d = (struct red_type *) malloc(SIZEOF_RED_DDD); 
  } 
*/
  d = (struct red_type *) malloc(sizeof(struct red_type)); 
  red_count++;

  d->var_index = vi; 
  switch (VAR[vi].TYPE) { 
  case TYPE_FALSE:
  case TYPE_TRUE:  
    d->status = 0; 
    break; 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    d->status = 0; 
    d->u.bdd.zero_child = NULL;  
    d->u.bdd.one_child = NULL;  
    break; 
  case TYPE_CRD: 
    d->status = 0; 
    d->u.crd.child_count = 0; 
    d->u.crd.arc = NULL;
    break; 

  case TYPE_HRD: 
    d->status = 0; 
    d->u.hrd.child_count = 0; 
    d->u.hrd.hrd_exp = NULL; 
    d->u.hrd.arc = NULL; 
    break; 
  case TYPE_HDD: 
    d->status = 0; 
    d->u.hdd.child_count = 0; 
    d->u.hdd.hrd_exp = NULL; 
    d->u.hdd.arc = NULL; 
    break; 
  case TYPE_LAZY_EXP: 
    d->status = FLAG_RED_LAZY;   
    d->u.lazy.exp = NULL; 
    d->u.lazy.false_child = NULL; 
    d->u.lazy.true_child = NULL; 
    break; 
  case TYPE_FLOAT: 
    d->status = 0; 
    d->u.fdd.child_count = 0; 
    d->u.fdd.arc = NULL;
    break; 
  case TYPE_DOUBLE: 
    d->status = 0; 
    d->u.dfdd.child_count = 0; 
    d->u.dfdd.arc = NULL;
    break; 
  case TYPE_CDD: 
  default: 
    d->status = 0; 
    d->u.ddd.child_count = 0; 
    d->u.ddd.arc = NULL;
    break; 
  } 
/*
  fprintf(RED_OUT, "  red alloc(%x)\n", (unsigned int) d); 
  if (d == (struct red_type *) 135922208) {
    test_d = new;
    fprintf(RED_OUT, "\nred %x is allocated !\n", (unsigned int) d);
    fflush(RED_OUT);
  }
*/
  return(d); 
}
/* red_alloc() */


/* It is assumed that no reference count need be updated by red_free(). 
 * Thus when it is a duplicate one in addition, then 
 * the reference counts are not incremented before the duplication checking.
 * If it is a not-used-anymore, then all the bdds and he are already 
 * dereferenced. 
 */ 
void	red_free(d) 
	struct red_type	*d; 
{ 
  int	vi; 
  
/*
  fprintf(RED_OUT, "  red free(%x)\n", (unsigned int) d); 
*/
  vi = d->var_index; 
  switch (VAR[vi].TYPE) { 
  case TYPE_FALSE: 
  case TYPE_TRUE: 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    free(d); 
    return; 

  case TYPE_CRD: 
    free(d->u.crd.arc); 
    free(d); 
    return; 
    
  case TYPE_HRD: 
/*
    free(d->u.hrd.hrd_exp->name); 
    free(d->u.hrd.hrd_exp->hrd_term); 
*/
    free(d->u.hrd.arc); 
    free(d); 
    return; 
    
  case TYPE_HDD: 
/*
    free(d->u.hdd.hrd_exp->name); 
    free(d->u.hdd.hrd_exp->hrd_term); 
*/
    free(d->u.hdd.arc); 
    free(d); 
    return; 
    
  case TYPE_FLOAT: 
    free(d->u.fdd.arc); 
    free(d); 
    return; 

  case TYPE_DOUBLE: 
    free(d->u.dfdd.arc); 
    free(d); 
    return; 

  case TYPE_CDD: 
  default: 
    free(d->u.ddd.arc); 
    free(d); 
    return; 
  } 
}
  /* red_free() */ 



red_count_reset(red)
     struct red_type	*red;
{
  red_gc_all_count++;
  red->status = 0;
}
/* red_count_reset() */ 



int	count_check_interval = 0; 

check_interval(vid, lb, ub)
     int	vid, lb, ub; 
{
/*
  fprintf(RED_OUT, "\ncheck interval %1d, %1d:%s, lb=%1d, ub=%1d\n", 
    ++count_check_interval, vid, VAR[vid].NAME, lb, ub
  ); 
  fflush(RED_OUT); 
  if (count_check_interval == 157) {
    fprintf(RED_OUT, "Caught!\n"); 
    fflush(RED_OUT); 	
  } 
*/
  if (lb > ub) {
    fprintf(RED_OUT, "\nError: check_interval(%1d:%s,%1d,%1d) lb > ub.\n", 
	    vid, VAR[vid].NAME, lb, ub
	    );
    bk(); 
  } 
  else if (lb > VAR[vid].U.DISC.UB) {
    fprintf(RED_OUT, "\nError: check_interval(%1d:%s,%1d,%1d) large lb.\n", 
	    vid, VAR[vid].NAME, lb, ub
	    ); 
    bk("Error"); 
  } 
  else if (ub < VAR[vid].U.DISC.LB) {
    fprintf(RED_OUT, "\nError: check_interval(%1d:%s,%1d,%1d) small ub.\n", 
	    vid, VAR[vid].NAME, lb, ub
	    );
    bk(); 
  } 
  else if (lb < VAR[vid].U.DISC.LB) {
    fprintf(RED_OUT, "\nError: check_interval(%1d:%s,%1d,%1d) small lb.\n", 
	    vid, VAR[vid].NAME, lb, ub
	    ); 
    bk(); 
  } 
}
/* check_interval() */ 





int	red_comp(redx, redy)
	struct red_type	*redx, *redy;
{ 
  int			flag, comp, ci;
  float			fcomp; 
  double		dfcomp; 
  struct ddd_child_type	*icx, *icy;

  if (comp = redx->var_index - redy->var_index)
    return(comp);
  else if ((redx->var_index == TYPE_TRUE) || (redx->var_index == TYPE_FALSE))
    return(0);

  switch (VAR[redx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (redx->u.bdd.zero_child < redy->u.bdd.zero_child) 
      return(-1); 
    else if (redx->u.bdd.zero_child > redy->u.bdd.zero_child) 
      return(1);  
    else if (redx->u.bdd.one_child < redy->u.bdd.one_child) 
      return(-1); 
    else if (redx->u.bdd.one_child > redy->u.bdd.one_child) 
      return(1);  
    else 
      return(0); 
  case TYPE_CRD:
    if (comp = redx->u.crd.child_count - redy->u.crd.child_count)
      return(comp);
    else for (ci = 0; ci < redx->u.crd.child_count; ci++)
      if (comp = redx->u.crd.arc[ci].upper_bound - redy->u.crd.arc[ci].upper_bound)
	return(comp);
      else if (redx->u.crd.arc[ci].child < redy->u.crd.arc[ci].child)
	return(-1);
      else if (redx->u.crd.arc[ci].child > redy->u.crd.arc[ci].child)
	return(1);

    return(0);
    break;
  case TYPE_HRD:
    return(hrd_comp(&(redx->u.hrd), redx->u.hrd.child_count, 
      &(redy->u.hrd), 
      redy->u.hrd.child_count
    ));
    break;
  case TYPE_HDD:
    return(hdd_comp(&(redx->u.hdd), 
      redx->u.hdd.child_count, &(redy->u.hdd), 
      redy->u.hdd.child_count
    ));
    break; 
  
  case TYPE_LAZY_EXP: 
    if (redx->u.lazy.exp < redy->u.lazy.exp)  
      return(-1); 
    else if (redx->u.lazy.exp > redy->u.lazy.exp)  
      return(1); 
    else if (redx->u.lazy.false_child < redy->u.lazy.false_child) 
      return(-1); 
    else if (redx->u.lazy.false_child > redy->u.lazy.false_child) 
      return(1); 
    else if (redx->u.lazy.true_child < redy->u.lazy.true_child)
      return(-1); 
    else if (redx->u.lazy.true_child > redy->u.lazy.true_child)
      return(1); 
    else 
      return(0); 
    break; 

  case TYPE_FLOAT:
    if (comp = redx->u.fdd.child_count - redy->u.fdd.child_count)
      return(comp);
    else for (ci = 0; ci < redx->u.fdd.child_count; ci++) { 
      fcomp = redx->u.fdd.arc[ci].lower_bound 
      - redy->u.fdd.arc[ci].lower_bound; 
      if (fcomp < 0)
	return(-1);
      else if (fcomp > 0)
	return(1);
      fcomp = redx->u.fdd.arc[ci].upper_bound 
      - redy->u.fdd.arc[ci].upper_bound; 
      if (fcomp < 0)
	return(-1);
      else if (fcomp > 0)
	return(1);
      if (redx->u.fdd.arc[ci].child < redy->u.fdd.arc[ci].child)
	return(-1);
      else if (redx->u.fdd.arc[ci].child > redy->u.fdd.arc[ci].child)
	return(1);
    } 
    return(0);

  case TYPE_DOUBLE:
    if (comp = redx->u.dfdd.child_count - redy->u.dfdd.child_count)
      return(comp);
    else for (ci = 0; ci < redx->u.dfdd.child_count; ci++) { 
      dfcomp = redx->u.dfdd.arc[ci].lower_bound 
      - redy->u.dfdd.arc[ci].lower_bound; 
      if (dfcomp < 0)
	return(-1);
      else if (dfcomp > 0)
	return(1);
      dfcomp = redx->u.dfdd.arc[ci].upper_bound 
      - redy->u.dfdd.arc[ci].upper_bound; 
      if (dfcomp < 0)
	return(-1);
      else if (dfcomp > 0)
	return(1);
      if (redx->u.dfdd.arc[ci].child < redy->u.dfdd.arc[ci].child)
	return(-1);
      else if (redx->u.dfdd.arc[ci].child > redy->u.dfdd.arc[ci].child)
	return(1);
    } 
    return(0);

  default:
    if (comp = redx->u.ddd.child_count - redy->u.ddd.child_count)
      return(comp);
    else for (ci = 0; ci < redx->u.ddd.child_count; ci++)
      if (comp = redx->u.ddd.arc[ci].lower_bound - redy->u.ddd.arc[ci].lower_bound)
	return(comp);
      else if (comp = redx->u.ddd.arc[ci].upper_bound - redy->u.ddd.arc[ci].upper_bound)
	return(comp);
      else if (redx->u.ddd.arc[ci].child < redy->u.ddd.arc[ci].child)
	return(-1);
      else if (redx->u.ddd.arc[ci].child > redy->u.ddd.arc[ci].child)
	return(1);

    return(0);
  }
}
  /* red_comp() */



  
  
  

struct red_link_type	*push_result(stack) 
	struct red_link_type	*stack; 
{
  struct red_link_type	*result; 
  
  result = (struct red_link_type *) malloc(sizeof(struct red_link_type)); 
  result_count++; 
  result->result = NULL; 
  result->next_red_link = stack; 
  return(result); 
}
/* push_result() */ 


struct red_link_type	*pop_result(stack) 
	struct red_link_type	*stack; 
{ 
  struct red_link_type	*result;

  result = stack->next_red_link;
  free(stack);
  result_count--;
  return(result);
}
/* pop_result() */



// int	rec_init_result_count = 0; 

void	rec_init_result(d)
     struct red_type	*d;
{
  int	ci;
/*
  fprintf(RED_OUT, 
    "\nrec_init_result_count=%1d, d=%x\n", ++rec_init_result_count, (unsigned int) d
  );
  if (rec_init_result_count == 17) {
    fprintf(RED_OUT, "Caught, rec_init_result_count=%1d!\n", 
      rec_init_result_count
    ); 
    fprintf(RED_OUT, "***\n"); 
  } 
  fflush(RED_OUT);
*/
  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
/*
    fprintf(RED_OUT, " already visited.\n");
    fflush(RED_OUT);
*/
    if (!(d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])) {
      d->status = d->status | MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK];
      d->result_stack = push_result(d->result_stack);
    }
  }
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK];
    switch (VAR[d->var_index].TYPE) {
    case TYPE_FALSE: 
    case TYPE_TRUE: 
      break; 
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      rec_init_result(d->u.bdd.zero_child); 
      rec_init_result(d->u.bdd.one_child); 
      break; 
    case TYPE_CRD:
/*
      fprintf(RED_OUT, " C:%1d, %s", d->var_index, VAR[d->var_index].NAME);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d", d->u.bchild[ci].upper_bound);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.crd.child_count; ci++)
	rec_init_result(d->u.crd.arc[ci].child);
      break;
    case TYPE_HRD:
/*
      fprintf(RED_OUT, " H:%1d, %s", d->var_index, d->u.hrd.hrd_exp->name);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d/%1d", d->u.hrd.hchild[ci].ub_numerator, d->u.hrd.hchild[ci].ub_denominator);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.hrd.child_count; ci++)
	rec_init_result(d->u.hrd.arc[ci].child);
      break;
    case TYPE_HDD:
/*
      fprintf(RED_OUT, " H:%1d, %s", d->var_index, d->u.hrd.hrd_exp->name);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d/%1d", d->u.hrd_filter.hfchild[ci].ub_numerator, d->u.hrd_filter.hfchild[ci].ub_denominator);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.hdd.child_count; ci++)
	rec_init_result(d->u.hdd.arc[ci].child);
      break; 
      
    case TYPE_LAZY_EXP: 
      rec_init_result(d->u.lazy.false_child); 
      rec_init_result(d->u.lazy.true_child); 
      break; 

    case TYPE_FLOAT:
/*
      fprintf(RED_OUT, " D:%1d, %s", d->var_index, VAR[d->var_index].NAME);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d--%1d", d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.fdd.child_count; ci++)
	rec_init_result(d->u.fdd.arc[ci].child); 
      break; 
 
    case TYPE_DOUBLE:
/*
      fprintf(RED_OUT, " D:%1d, %s", d->var_index, VAR[d->var_index].NAME);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d--%1d", d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.dfdd.child_count; ci++)
	rec_init_result(d->u.dfdd.arc[ci].child);
      break; 

    default:
/*
      fprintf(RED_OUT, " D:%1d, %s", d->var_index, VAR[d->var_index].NAME);
      fflush(RED_OUT);
      for (ci = 0; ci < d->child_count; ci++)
	fprintf(RED_OUT, ", %1d--%1d", d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      fprintf(RED_OUT, "\n");
      fflush(RED_OUT);
*/
      for (ci = 0; ci < d->u.ddd.child_count; ci++)
	rec_init_result(d->u.ddd.arc[ci].child);
    }
  }
}
/* rec_init_result() */



void	red_init_result(d)
     struct red_type	*d;
{
  TOP_LEVEL_RESULT_STACK++;
/*
  fprintf(RED_OUT, "TOP_LEVEL_RESULT_STACK=%1d, MASK_STACK_REFERENCED[%1d]=%x, MASK_STACK_MULTIPLE[%1d]=%x\n",
	  TOP_LEVEL_RESULT_STACK,
	  TOP_LEVEL_RESULT_STACK, MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK],
	  TOP_LEVEL_RESULT_STACK, MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]
	  );
  fflush(RED_OUT);
*/
  rec_init_result(d);
}
/* red_init_result() */





void	rec_clear_result(d)
     struct red_type	*d;
{
  int	ci;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      d->result_stack = pop_result(d->result_stack);
    d->status = d->status & ~MASK_STACK[TOP_LEVEL_RESULT_STACK];
    switch (VAR[d->var_index].TYPE) { 
    case TYPE_FALSE: 
    case TYPE_TRUE: 
      break; 
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      rec_clear_result(d->u.bdd.zero_child); 
      rec_clear_result(d->u.bdd.one_child); 
      break; 
    case TYPE_CRD:
      for (ci = 0; ci < d->u.crd.child_count; ci++)
	rec_clear_result(d->u.crd.arc[ci].child);
      break;
    case TYPE_HRD:
      for (ci = 0; ci < d->u.hrd.child_count; ci++)
	rec_clear_result(d->u.hrd.arc[ci].child);
      break;
    case TYPE_HDD:
      for (ci = 0; ci < d->u.hdd.child_count; ci++)
	rec_clear_result(d->u.hdd.arc[ci].child);
      break;            

    case TYPE_LAZY_EXP: 
      rec_clear_result(d->u.lazy.false_child); 
      rec_clear_result(d->u.lazy.true_child); 
      break; 
            
    case TYPE_FLOAT:
      for (ci = 0; ci < d->u.fdd.child_count; ci++)
	rec_clear_result(d->u.fdd.arc[ci].child);
      break; 
            
    case TYPE_DOUBLE:
      for (ci = 0; ci < d->u.dfdd.child_count; ci++)
	rec_clear_result(d->u.dfdd.arc[ci].child);
      break; 
            
    default:
      for (ci = 0; ci < d->u.ddd.child_count; ci++)
	rec_clear_result(d->u.ddd.arc[ci].child);
    }
  }
}
/* rec_clear_result() */



void	red_clear_result(d) 
  struct red_type	*d; 
{ 
  rec_clear_result(d);
  TOP_LEVEL_RESULT_STACK--; 
}
  /* red_clear_result() */ 




int	hash_key(d)
     struct red_type	*d;
{
  int			k, ci; 

  k = d->var_index; 
  if (VAR[d->var_index].TYPE == TYPE_CRD) { 
    struct crd_child_type	*bc; 

    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
      bc = &(d->u.crd.arc[ci]); 
      k = k + bc->upper_bound;
      k = k + ((int) bc->child / 3) % 10000; 
    }
  }
  else {
    struct ddd_child_type	*ic; 

    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ic = &(d->u.ddd.arc[ci]); 
      k = k + ic->lower_bound + ic->upper_bound; 
      k = k + ((int) ic->child / 3) % 10000; 
    }
  }
  k = k % 10000;

  return(k); 
}
/* hash_key() */ 



struct red_type	*add_red(d)
     struct red_type	*d;
{
  int	key;

  /*
  key = hash_key(d);
  fprintf(RED_OUT, "key=%1d\n", key);
  */
}
/* add_red() */



struct current_mode_type { 
  int	lb, ub; 	
}
  *CURRENT_RED_MODE; 

void	red_print(red, depth)
     struct red_type	*red;
     int		depth;
{
  int			i, flag, ci;

  for (i = depth; i; i--)
    fprintf(RED_OUT, "  ");

  if (!red) {
    fprintf(RED_OUT, "NULL RED\n");
    return;
  }

  fprintf(RED_OUT, "%x;S=%d", (unsigned int) red, red->status);

  if (red->var_index == TYPE_TRUE)
    fprintf(RED_OUT, "TRUE\n");
  else if (red->var_index == TYPE_FALSE)
    fprintf(RED_OUT, "FALSE\n");
  else {
    fprintf(RED_OUT, "*RED=%d:%s:", red->var_index, VAR[red->var_index].NAME);
    switch (VAR[red->var_index].TYPE) {
    case TYPE_CRD:
      fprintf(RED_OUT, "IC=%d;", red->u.crd.child_count);
      for (ci = 0; ci < red->u.crd.child_count; ci++) {
	if (red->u.crd.arc[ci].upper_bound % 2) {
	  if (red->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY)
	    fprintf(RED_OUT, "<oo:");
	  else
	    fprintf(RED_OUT, "<%1d:", (red->u.crd.arc[ci].upper_bound+1)/2);
	}
	else
	  fprintf(RED_OUT, "<=%1d:", (red->u.crd.arc[ci].upper_bound)/2);
	if (red->u.crd.arc[ci].child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
	else if (red->u.crd.arc[ci].child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
	else
	  fprintf(RED_OUT, "%x;", (unsigned int) red->u.crd.arc[ci].child);
      }
      break;
    case TYPE_HRD:
      fprintf(RED_OUT, "IC=%d;", red->u.hrd.child_count);
      for (ci = 0; ci < red->u.hrd.child_count; ci++) {
	if (red->u.hrd.arc[ci].ub_numerator % 2) {
	  if (   red->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	      && red->u.hrd.arc[ci].ub_denominator == 1
	      )
	    fprintf(RED_OUT, "<oo:");
	  else if (red->u.hrd.arc[ci].ub_denominator == 1)
	    fprintf(RED_OUT, "<%1d:", (red->u.hrd.arc[ci].ub_numerator+1)/2);
	  else
	    fprintf(RED_OUT, "<%1d/%1d:", (red->u.hrd.arc[ci].ub_numerator+1)/2,
		    red->u.hrd.arc[ci].ub_denominator
		    );
	}
	else
	  if (red->u.hrd.arc[ci].ub_denominator == 1)
	    fprintf(RED_OUT, "<=%1d:", (red->u.hrd.arc[ci].ub_numerator)/2);
	  else
	    fprintf(RED_OUT, "<=%1d/%1d:", (red->u.hrd.arc[ci].ub_numerator)/2,
		    red->u.hrd.arc[ci].ub_denominator
		    );
	if (red->u.hrd.arc[ci].child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
	else if (red->u.hrd.arc[ci].child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
	else
	  fprintf(RED_OUT, "%x;", (unsigned int) red->u.hrd.arc[ci].child);
      }
      break;
    case TYPE_FLOAT:
      fprintf(RED_OUT, "IC=%d;", red->u.fdd.child_count);
      for (ci = 0; ci < red->u.fdd.child_count; ci++) {
	fprintf(RED_OUT, "[%G,%G]", 
	  red->u.fdd.arc[ci].lower_bound, red->u.fdd.arc[ci].upper_bound
	);
	if (red->u.fdd.arc[ci].child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
	else if (red->u.fdd.arc[ci].child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
	else
	  fprintf(RED_OUT, "%x;", (unsigned int) red->u.fdd.arc[ci].child);
      }
      break;
    case TYPE_DOUBLE:
      fprintf(RED_OUT, "IC=%d;", red->u.dfdd.child_count);
      for (ci = 0; ci < red->u.dfdd.child_count; ci++) {
	fprintf(RED_OUT, "[%G,%G]", 
	  red->u.dfdd.arc[ci].lower_bound, red->u.dfdd.arc[ci].upper_bound
	);
	if (red->u.dfdd.arc[ci].child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
	else if (red->u.dfdd.arc[ci].child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
	else
	  fprintf(RED_OUT, "%x;", (unsigned int) red->u.dfdd.arc[ci].child);
      }
      break;
    default:
      fprintf(RED_OUT, "IC=%d;", red->u.ddd.child_count);
      for (ci = 0; ci < red->u.ddd.child_count; ci++) {
	fprintf(RED_OUT, "[%1d,%1d]", 
	  red->u.ddd.arc[ci].lower_bound, red->u.ddd.arc[ci].upper_bound
	);
	if (red->u.ddd.arc[ci].child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
	else if (red->u.ddd.arc[ci].child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
	else
	  fprintf(RED_OUT, "%x;", (unsigned int) red->u.ddd.arc[ci].child);
      }
    }
    fprintf(RED_OUT, "\n");
  }
}
  /* red_print() */



struct red_type	*bdd_new(vi, false_child, true_child)
     int		vi; 
     struct red_type	*false_child, *true_child; 
{
  struct red_type		*d, *fd, *td ; 
  int				flag, i; 

  if (vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, 
      "\n\nA big vi in bdd_new(vi=%1d)\n", vi
    ); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
  }
  else if (VAR[vi].TYPE == TYPE_CRD) { 
    fprintf(RED_OUT, 
      "\n\nA type CLOCK_INEQUALITY vi in bdd_new(vi=%1d)\n", vi
    ); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
  else if (VAR[vi].TYPE != TYPE_BDD && VAR[vi].TYPE != TYPE_SYNCHRONIZER) { 
    fprintf(RED_OUT, 
      "\n\nA type %1d vi in bdd_new(vi=%1d)\n", VAR[vi].TYPE, vi
    ); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
  } 
  fd = NORM_FALSE; 
  if (false_child != NORM_FALSE && false_child != NORM_NO_RESTRICTION) 
    if (vi >= false_child->var_index) { 
      fd = bdd_one_constraint(false_child, vi, TYPE_FALSE); 
      false_child = NORM_FALSE; 
/*
      fprintf(RED_OUT, "BDD construction out of order at the false-child side.\n"); 
      fflush(RED_OUT); 
      bk(0); 
*/
    } 
  
  td = NORM_FALSE; 
  if (true_child != NORM_FALSE && true_child != NORM_NO_RESTRICTION) 
    if (vi >= true_child->var_index) { 
      td = bdd_one_constraint(true_child, vi, TYPE_TRUE); 
      true_child = NORM_FALSE; 
/*
      fprintf(RED_OUT, "BDD construction out of order at the true-child side.\n"); 
      fflush(RED_OUT); 
      bk(0); 
*/
    } 
    
  /*
  if (red_pool == NULL && free_red_count != 0) {
    fprintf(RED_OUT, "\nwhack!\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }

  if (red_pool != NULL && free_red_count == 0) { 
    fprintf(RED_OUT, "\nwhack!\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  */

  if (false_child == true_child) 
    d = false_child; 
  else { 
    d = red_alloc(vi); 
    d->status = (false_child->status | true_child->status) & FLAG_RED_LAZY; 
    d->u.bdd.zero_child = false_child; 
    d->u.bdd.one_child = true_child; 
    d = red_share(d); 
  } 
  if (td != NORM_FALSE) 
    d = red_bop(OR, d, td); 
  if (fd != NORM_FALSE) 
    d = red_bop(OR, d, fd); 

  return(d); 
}
  /* bdd_new() */





int	count_ddd_new = 0; 

struct red_type *ddd_new(vi)
     int			vi; 
{
  struct red_type	*d; 
  int			flag, i; 

  if (vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\n\nA big vi in ddd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
  else switch (VAR[vi].TYPE) { 
  case TYPE_CRD:
  case TYPE_HDD:
  case TYPE_HRD: 
  case TYPE_BDD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, "\n\nA type CLOCK_INEQUALITY vi in ddd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
    
  get_to_next_valid_child(); 
  if (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 0) {
    child_stack_level_pop(); 
    return(NORM_FALSE); 
  }
/*  
  fprintf(RED_OUT, "\n==ddd_new %1d, ", 
    ++count_ddd_new 
  ); 
  fprintf(RED_OUT, "%1d:%s, VLB:%1d, VUB:%1d==", 
    vi, VAR[vi].NAME, VAR[vi].LB, VAR[vi].UB 
  ); 
  fprintf(RED_OUT, " LEVEL %1d, cc %1d, lb:%1d, ub:%1d.\n", 
    TOP_LEVEL_CHILD_STACK, 
    LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK], 
    CHILD_STACK[TOP_CHILD_STACK].lb, 
    CHILD_STACK[TOP_CHILD_STACK].ub 
  ); 
//  fflush(RED_OUT); 
  if (count_ddd_new == -1) {
    bk(0); 
  }
*/
  if (   LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 1 
      && CHILD_STACK[TOP_CHILD_STACK].u.disc.ub == VAR[vi].U.DISC.UB 
      && CHILD_STACK[TOP_CHILD_STACK].u.disc.lb == VAR[vi].U.DISC.LB
      ) {
    d = CHILD_STACK[TOP_CHILD_STACK].d; 
    child_stack_pop(); 
    get_to_next_valid_child(); 
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "ddd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(d); 
  }
  else { 
    d = red_alloc(vi); 
    d->status = 0; 
    d->u.ddd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    ichild_count = ichild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    d->u.ddd.arc = (struct ddd_child_type *) 
      malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] * sizeof(struct ddd_child_type)); 
    for (i = 0; i < d->u.ddd.child_count; i++) { 
      d->u.ddd.arc[i].lower_bound 
      = CHILD_STACK[TOP_CHILD_STACK].u.disc.lb; 
      d->u.ddd.arc[i].upper_bound 
      = CHILD_STACK[TOP_CHILD_STACK].u.disc.ub; 
      d->u.ddd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d; 
      d->status = d->status | (d->u.ddd.arc[i].child->status & FLAG_RED_LAZY); 
      child_stack_pop(); 
      get_to_next_valid_child(); 
    }
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "ddd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(red_share(d)); 
  }
}
  /* ddd_new() */



int	count_fdd_new = 0; 

struct red_type *fdd_new(vi)
     int			vi; 
{
  struct red_type	*d; 
  int			flag, i; 

  if (vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\n\nA big vi in fdd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
  else switch (VAR[vi].TYPE) { 
  case TYPE_FLOAT:
    break; 
  default: 
    fprintf(RED_OUT, "\n\nA non-FDD vi in fdd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
    
  get_to_next_valid_child(); 
  if (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 0) {
    child_stack_level_pop(); 
    return(NORM_FALSE); 
  }
/*  
  fprintf(RED_OUT, "\n==fdd_new %1d, ", 
    ++count_fdd_new 
  ); 
  fprintf(RED_OUT, "%1d:%s, VLB:%G, VUB:%G==", 
    vi, VAR[vi].NAME, VAR[vi].U.FLT.LB, VAR[vi].U.FLT.UB 
  ); 
  fprintf(RED_OUT, " LEVEL %1d, cc %1d, lb:%G, ub:%G.\n", 
    TOP_LEVEL_CHILD_STACK, 
    LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK], 
    CHILD_STACK[TOP_CHILD_STACK].u.flt.lb, 
    CHILD_STACK[TOP_CHILD_STACK].u.flt.ub 
  ); 
//  fflush(RED_OUT); 
  if (count_fdd_new == -1) {
    bk(0); 
  }
*/
  if (   LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 1 
      && CHILD_STACK[TOP_CHILD_STACK].u.flt.ub == VAR[vi].U.FLT.UB 
      && CHILD_STACK[TOP_CHILD_STACK].u.flt.lb == VAR[vi].U.FLT.LB
      ) {
    d = CHILD_STACK[TOP_CHILD_STACK].d; 
    child_stack_pop(); 
    get_to_next_valid_child(); 
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "fdd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(d); 
  }
  else { 
    d = red_alloc(vi); 
    d->status = 0; 
    d->u.fdd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    fchild_count = fchild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    d->u.fdd.arc = (struct fdd_child_type *) 
    malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] 
      * sizeof(struct fdd_child_type)
    ); 
    for (i = 0; i < d->u.fdd.child_count; i++) { 
      d->u.fdd.arc[i].lower_bound = CHILD_STACK[TOP_CHILD_STACK].u.flt.lb; 
      d->u.fdd.arc[i].upper_bound = CHILD_STACK[TOP_CHILD_STACK].u.flt.ub; 
      d->u.fdd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d; 
      d->status = d->status | (d->u.fdd.arc[i].child->status & FLAG_RED_LAZY); 
      child_stack_pop(); 
      get_to_next_valid_child(); 
    }
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "fdd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(red_share(d)); 
  }
}
  /* fdd_new() */



int	count_dfdd_new = 0; 

struct red_type *dfdd_new(vi)
     int			vi; 
{
  struct red_type	*d; 
  int			flag, i; 

  if (vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\n\nA big vi in dfdd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  }
  else switch (VAR[vi].TYPE) { 
  case TYPE_DOUBLE:
    break; 
  default: 
    fprintf(RED_OUT, "\n\nA non-DBLE vi in dfdd_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
    
  get_to_next_valid_child(); 
  if (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 0) {
    child_stack_level_pop(); 
    return(NORM_FALSE); 
  }
/*  
  fprintf(RED_OUT, "\n==dfdd_new %1d, ", 
    ++count_dfdd_new 
  ); 
  fprintf(RED_OUT, "%1d:%s, VLB:%G, VUB:%G==", 
    vi, VAR[vi].NAME, VAR[vi].U.DBLE.LB, VAR[vi].U.DBLE.UB 
  ); 
  fprintf(RED_OUT, " LEVEL %1d, cc %1d, lb:%G, ub:%G.\n", 
    TOP_LEVEL_CHILD_STACK, 
    LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK], 
    CHILD_STACK[TOP_CHILD_STACK].u.dble.lb, 
    CHILD_STACK[TOP_CHILD_STACK].u.dble.ub 
  ); 
//  fflush(RED_OUT); 
  if (count_fdd_new == -1) {
    bk(0); 
  }
*/
  if (   LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 1 
      && CHILD_STACK[TOP_CHILD_STACK].u.dble.ub == VAR[vi].U.DBLE.UB 
      && CHILD_STACK[TOP_CHILD_STACK].u.dble.lb == VAR[vi].U.DBLE.LB
      ) {
    d = CHILD_STACK[TOP_CHILD_STACK].d; 
    child_stack_pop(); 
    get_to_next_valid_child(); 
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "dfdd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(d); 
  }
  else { 
    d = red_alloc(vi); 
    d->status = 0; 
    d->u.dfdd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    dfchild_count = dfchild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    d->u.dfdd.arc = (struct dfdd_child_type *) 
    malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] 
      * sizeof(struct dfdd_child_type)
    ); 
    for (i = 0; i < d->u.dfdd.child_count; i++) { 
      d->u.dfdd.arc[i].lower_bound = CHILD_STACK[TOP_CHILD_STACK].u.dble.lb; 
      d->u.dfdd.arc[i].upper_bound = CHILD_STACK[TOP_CHILD_STACK].u.dble.ub; 
      d->u.dfdd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d; 
      d->status = d->status | (d->u.dfdd.arc[i].child->status & FLAG_RED_LAZY); 
      child_stack_pop(); 
      get_to_next_valid_child(); 
    }
    child_stack_level_pop(); 
/*
    fprintf(RED_OUT, "dfdd for vi=%1d\n", vi); 
    red_print_graph(d); 
*/
    return(red_share(d)); 
  }
}
  /* dfdd_new() */



struct red_type	*crd_new(vi)
     int	vi; 
{
  struct red_type	*d; 
  int			flag, i; 

  if (vi >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\n\nA big vi in ineq_new(vi=%1d)\n", vi); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  else if (VAR[vi].TYPE != TYPE_CRD) { 
    fprintf(RED_OUT, "\n\nA type non CLOCK_INEQUALITY vi in ineq_new(vi=%1d)\n", vi); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0);
  }

  get_to_next_valid_child()
  if (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 0) {
    child_stack_level_pop();; 
    return(NORM_FALSE); 
  }
  else if (   LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] == 1 
           && CHILD_STACK[TOP_CHILD_STACK].u.crd.ub == CLOCK_POS_INFINITY
           ) {
    d = CHILD_STACK[TOP_CHILD_STACK].d; 
    child_stack_pop(); 
    get_to_next_valid_child(); 
    child_stack_level_pop();; 
    return(d); 
  }
  else { 
    d = red_alloc(vi); 
    d->status = 0; 
    d->u.crd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    bchild_count = bchild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]; 
    d->u.crd.arc = (struct crd_child_type *) 
      malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] * sizeof(struct crd_child_type)); 
    for (i = 0; i < d->u.crd.child_count; i++) { 
      d->u.crd.arc[i].upper_bound = CHILD_STACK[TOP_CHILD_STACK].u.crd.ub; 
      d->u.crd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d; 
      d->status = d->status | (d->u.crd.arc[i].child->status & FLAG_RED_LAZY); 
      child_stack_pop(); 
      get_to_next_valid_child();  
    }
    child_stack_level_pop();; 
    return(red_share(d)); 
  } 
}
  /* crd_new() */



int	flag_red_management;

init_red_management()
{
  int	i, r, m;

  mbug_flag = TYPE_FALSE;
  mop_count = 0;
  flag_red_management = 0; 

  MAX_MEM = 0; 
  MAX_TREE_USAGE 
  = MAX_RESULT_USAGE 
  = MAX_RESULT_STACK_HEIGHT 
  = MAX_RT_HEIGHT = 0; 
  TOP_LEVEL_RESULT_STACK = -1; 

  FLAG_ZONE_REPRESENTATION = TYPE_TRUE; 

  red_count = 0;

  ichild_count = 0; 
  ichild_link_count = 0; 

  bchild_count = 0;
  bchild_link_count = 0; 
/*
  fprintf(RED_OUT, "SIZEOF_RED_TERMINAL = %1d\n", SIZEOF_RED_TERMINAL);
  fprintf(RED_OUT, "SIZEOF_RED_BDD = %1d\n", SIZEOF_RED_BDD); 
  fprintf(RED_OUT, "SIZEOF_RED_CRD = %1d\n", SIZEOF_RED_CRD); 
  fprintf(RED_OUT, "SIZEOF_RED_HRD = %1d\n", SIZEOF_RED_HRD); 
  fprintf(RED_OUT, "SIZEOF_RED_HDD = %1d\n", SIZEOF_RED_HDD); 
  fprintf(RED_OUT, "SIZEOF_RED_TERMINAL = %1d\n", SIZEOF_RED_TERMINAL); 
  fprintf(RED_OUT, "SIZEOF_RED_DDD = %1d\n", SIZEOF_RED_DDD); 
  fprintf(RED_OUT, "SIZEOF_RED_FLT = %1d\n", SIZEOF_RED_FLT); 
  fprintf(RED_OUT, "SIZEOF_RED_DBLE = %1d\n", SIZEOF_RED_DBLE); 
*/
  NORM_NO_RESTRICTION 
  = NORM_TRUE 
  = red_alloc(TYPE_TRUE); // (struct red_type *) malloc(sizeof(struct red_type)); 
  red_count++; 
  NORM_TRUE->status = FLAG_GC_STABLE;
//  NORM_TRUE->var_index = TYPE_TRUE;
  red_mark(NORM_TRUE, FLAG_GC_STABLE); 
  red_share(NORM_TRUE); 

  NORM_FALSE = red_alloc(TYPE_FALSE); // (struct red_type *) malloc(sizeof(struct red_type));
  red_count++;
  NORM_FALSE->status = FLAG_GC_STABLE;
//  NORM_FALSE->var_index = TYPE_FALSE;
  red_mark(NORM_FALSE, FLAG_GC_STABLE); 
  red_share(NORM_FALSE);

  PS_EXP_TRUE->type = RED; 
  PS_EXP_TRUE->u.rpred.red 
  = PS_EXP_TRUE->u.rpred.original_red 
  = NORM_TRUE; 
  PS_EXP_FALSE->type = RED; 
  PS_EXP_FALSE->u.rpred.red 
  = PS_EXP_FALSE->u.rpred.original_red 
  = NORM_FALSE; 
  
  /* Supposedly, this should use offset to save 4 bytes. 
 * I hate valgrind who would flag such usage as faults. 
 */  
  CHILD_STACK = (struct child_stack_frame_type *) 
    malloc(VARIABLE_COUNT * sizeof(struct child_stack_frame_type)); 
  HEIGHT_CHILD_STACK = VARIABLE_COUNT; 
  
  LEVEL_CHILD_COUNT = (int *) malloc(VARIABLE_COUNT * sizeof(int)); 
  HEIGHT_LEVEL_CHILD_STACK = VARIABLE_COUNT; 
/*
  fprintf(RED_OUT, "LEVEL_CHILD_COUNT:%x\n", (unsigned int) LEVEL_CHILD_COUNT); 
*/
  MASK_STACK = (int *) malloc(13*sizeof(int));
  MASK_STACK_REFERENCED = (int *) malloc(13*sizeof(int));
  MASK_STACK_MULTIPLE = (int *) malloc(13*sizeof(int));

  for (i = 0, r = MASK0_REFERENCED, m = MASK0_MULTIPLE; i < 12; i++) {
    MASK_STACK[i] = r | m;
    MASK_STACK_REFERENCED[i] = r;
    MASK_STACK_MULTIPLE[i] = m;
/*
    fprintf(RED_OUT, "MASK_STACK_REFERENCED[i=%1d] = %x;\n", 
      i, MASK_STACK_REFERENCED[i]
    ); 
    fprintf(RED_OUT, "MASK_STACK_MULTIPLE[i=%1d] = %x;\n", 
      i, MASK_STACK_MULTIPLE[i]
    ); 
*/
    r = 4*r;
    m = 4*m;
  }

  CURRENT_RED_MODE = ((struct current_mode_type *)
    malloc((PROCESS_COUNT+(1-DEBUG_PROCESS_OFFSET)) * sizeof(struct current_mode_type)) 
  ) - DEBUG_PROCESS_OFFSET; 
/*  
  test_hashman(); 
*/
}
/* init_red_management() */



/********************************************************
 *
 *	Garbage-collecting routines
 */


/*****************************************************
*  The returned string of search_var_name is volatile and does not 
*  guarantee to be stable. 
*/


// int	count_print_graph = 0; 

void	rec_print_graph(red, depth)
     struct red_type	*red; 
     int		depth; 
{
  int				i, mi, ci, pi, key;
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct hdd_child_type		*hfc;

/*
  fprintf(RED_OUT, "count_print_graph = %1d\n", ++count_print_graph); 
  for (; count_print_graph == 119; ) ; 
*/
  if (!red) { 
    for (i = 1; i <= depth; i++)
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, " (%1d)NULL RED\n", depth); 
    return;
  } 
  else if (red->var_index == TYPE_TRUE) {
    if (red != NORM_TRUE) {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, " (%1d), unnormalized TRUE\n", depth); 
    }
    /* 
    else {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, " (%1d), TRUE\n", depth); 
    }
    */
    return;
  } 
  else if (red->var_index == TYPE_FALSE) {
    if (red != NORM_FALSE) {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, " (%1d), unnmormalized FALSE\n", depth);
    }
    /*
    else {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, "  (%1d), FALSE\n", depth);
    }
    */
    return; 
  } 

  for (i = 1; i <= depth; i++)
    fprintf(RED_OUT, "  "); 
  fprintf(RED_OUT, " (%1d)", depth);

  /*  fprintf(RED_OUT, "\nnew rec %x = (%x,%x)\n", (unsigned int) rec, (unsigned int) rec->redx, (unsigned int) rec->redy);
   */
  if (red->status & FLAG_GC_PRINT) {
    fprintf(RED_OUT, "%x already printed.\n", (unsigned int) red);
    return;
  } 
  else 
    red->status = red->status | FLAG_GC_PRINT; 

  switch (VAR[red->var_index].TYPE) {
    
  case TYPE_BDD:
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT, "V=%d:%s;%x;%x;", 
	    red->var_index, 
	    VAR[red->var_index].NAME,  
	    (unsigned int) red, (unsigned int) red->status
	    );
    if (red->u.bdd.zero_child == NORM_FALSE) 
      fprintf(RED_OUT, "FALSE-->FALSE;"); 
    else if (red->u.bdd.zero_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "FALSE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "FALSE-->(%x);", (unsigned int) red->u.bdd.zero_child); 
    if (red->u.bdd.one_child == NORM_FALSE) 
      fprintf(RED_OUT, "TRUE-->FALSE;"); 
    else if (red->u.bdd.one_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "TRUE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "TRUE-->(%x);", (unsigned int) red->u.bdd.one_child); 
    fprintf(RED_OUT, "\n"); 

    rec_print_graph(red->u.bdd.zero_child, depth+1); 
    rec_print_graph(red->u.bdd.one_child, depth+1); 
    break; 
  case TYPE_CRD /* TYPE_CRD*/ :
    fprintf(RED_OUT, "V=%d:%s;(%x)%x;IC=%d;", red->var_index, 
    	    VAR[red->var_index].NAME,
	    (unsigned int) red, red->status, red->u.crd.child_count
	    );
    for (ci = 0; ci < red->u.crd.child_count; ci++) {
      bc = &(red->u.crd.arc[ci]);
      if (bc->upper_bound > CLOCK_POS_INFINITY) {
	if (VAR[red->var_index].U.CRD.CLOCK1 != TIME) { 
	  fprintf(RED_OUT, "\nError: out of bound clock inequality differences: %1d catched.\n", bc->upper_bound);
	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
      } }
      else if (bc->upper_bound < CLOCK_NEG_INFINITY) {
	if (VAR[red->var_index].U.CRD.CLOCK2 != TIME) { 
	  fprintf(RED_OUT, "\nError: under bound clock inequality differences: %1d catched.\n", bc->upper_bound);
	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
      } }
      else if (bc->upper_bound == CLOCK_POS_INFINITY) {
//	if (VAR[red->var_index].U.CRD.CLOCK1 != TIME) { 
	  fprintf(RED_OUT, "<oo:");
//	  continue; 
//	} 
      }
      else if (bc->upper_bound % 2) {
	fprintf(RED_OUT, "<%1d:", (bc->upper_bound+1)/2);
      }
      else
	fprintf(RED_OUT, "<=%1d:", (bc->upper_bound)/2);
      if (bc->child == NORM_FALSE)
	fprintf(RED_OUT, "FALSE;");
      else if (bc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;");
      else
	fprintf(RED_OUT, "%x;", (unsigned int) bc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.crd.child_count; ci++)
      rec_print_graph(red->u.crd.arc[ci].child, depth+1);
    break;
  case TYPE_HRD /* TYPE_HRD*/ :
    fprintf(RED_OUT, "V=%d:(%s);(%x)%x;IC=%d;", 
	    red->var_index, red->u.hrd.hrd_exp->name,
	    (unsigned int) red, red->status, red->u.hrd.child_count
	    );
    for (ci = 0; ci < red->u.hrd.child_count; ci++) {
      hc = &(red->u.hrd.arc[ci]);
      if (hc->ub_numerator == HYBRID_POS_INFINITY && hc->ub_denominator == 1)
        fprintf(RED_OUT, "<oo");
      else {
        if (hc->ub_numerator % 2) {
	  fprintf(RED_OUT, "<%1d", (hc->ub_numerator+1)/2);
        }
        else
	  fprintf(RED_OUT, "<=%1d", (hc->ub_numerator)/2);
        if (hc->ub_denominator != 1 && hc->ub_numerator) {
	  fprintf(RED_OUT, "/%1d:", hc->ub_denominator);
        }
      }
      if (hc->child == NORM_FALSE)
	fprintf(RED_OUT, ":FALSE;");
      else if (hc->child == NORM_TRUE)
	fprintf(RED_OUT, ":TRUE;");
      else
	fprintf(RED_OUT, ":%x;", (unsigned int) hc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.hrd.child_count; ci++)
      rec_print_graph(red->u.hrd.arc[ci].child, depth+1);
    break;
    
  case TYPE_CDD /* TYPE_CDD*/ : 
    fprintf(RED_OUT, "V=%d:%s;(%x)%x;IC=%d;", 
	    red->var_index, 
	    VAR[red->var_index].NAME,  
	    (unsigned int) red, red->status, red->u.ddd.child_count
	    );
    
    for (ci = 0; ci < red->u.ddd.child_count; ci++) {
      ic = &(red->u.ddd.arc[ci]);
        
      if (ic->lower_bound == NEG_INFINITY)
        fprintf(RED_OUT, "(-oo,");       
      else
        if(ic->lower_bound%2)
          fprintf(RED_OUT, "[%1d,", ic->lower_bound/2);   
        else
          fprintf(RED_OUT, "(%1d,", (ic->upper_bound-1)/2);   
                  
      if (ic->upper_bound == POS_INFINITY)
        fprintf(RED_OUT, "oo)");       
      else if(ic->upper_bound%2)
        fprintf(RED_OUT, "%1d]", ic->upper_bound/2);   
      else
        fprintf(RED_OUT, "%1d)", (ic->upper_bound+1)/2);   	
                    
        
      if (ic->child == NORM_FALSE)
	fprintf(RED_OUT, "FALSE;");
      else if (ic->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;");
      else
	fprintf(RED_OUT, "%x;", (unsigned int) ic->child);
    }
      
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.ddd.child_count; ci++)
      rec_print_graph(red->u.ddd.arc[ci].child, depth+1);
    break; 
    
  case TYPE_HDD /* TYPE_HDD*/ :

    fprintf(RED_OUT, "V=%d:(%s);(%x)%x;IC=%d;", 
      red->var_index, 
      red->u.hdd.hrd_exp->name,  
      (unsigned int) red, red->status, red->u.hdd.child_count
      );
  
    for (ci = 0; ci < red->u.hdd.child_count; ci++) {
      hfc = &(red->u.hdd.arc[ci]);
 
      if (   hfc->lb_numerator == HYBRID_NEG_INFINITY 
          && hfc->lb_denominator == 1
          )
        fprintf(RED_OUT, "(-oo,");       
      else if (hfc->lb_denominator == 1)
        if(hfc->lb_numerator%2)
          fprintf(RED_OUT, "[%1d,", hfc->lb_numerator/2);
        else
          fprintf(RED_OUT, "(%1d,", (hfc->lb_numerator-1)/2);
      else
        if(hfc->lb_numerator%2)
          fprintf(RED_OUT, "[%1d/%1d,", hfc->lb_numerator/2,hfc->lb_denominator);   
        else
          fprintf(RED_OUT, "(%1d/%1d,", (hfc->lb_numerator-1)/2,hfc->lb_denominator);   

      if (hfc->ub_numerator == HYBRID_POS_INFINITY && hfc->ub_denominator == 1)
        fprintf(RED_OUT, "oo)");       
      else if (hfc->ub_denominator == 1)
        if(hfc->ub_numerator%2)
          fprintf(RED_OUT, "%1d]", hfc->ub_numerator/2);
        else
          fprintf(RED_OUT, "%1d),", (hfc->ub_numerator+1)/2);
      else
        if(hfc->ub_numerator%2)
          fprintf(RED_OUT, "%1d/%1d],", hfc->ub_numerator/2,hfc->lb_denominator);   
        else
          fprintf(RED_OUT, "%1d/%1d)", (hfc->lb_numerator+1)/2,hfc->lb_denominator);  			

      
      if (hfc->child == NORM_FALSE)
  			fprintf(RED_OUT, "FALSE;");
      else if (hfc->child == NORM_TRUE)
  			fprintf(RED_OUT, "TRUE;");
      else
  			fprintf(RED_OUT, "%x;", (unsigned int) hfc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.hdd.child_count; ci++)
      rec_print_graph(red->u.hdd.arc[ci].child, depth+1);

    break; 
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "V=%1d:%s;(%x)%x;", 
      red->var_index, VAR[red->var_index].NAME, 
      (unsigned int) red, red->status
    ); 
    print_parse_subformula(red->u.lazy.exp, VAR[red->var_index].PROC_INDEX); 
    if (red->u.lazy.false_child == NORM_FALSE) 
      fprintf(RED_OUT, "FALSE-->FALSE;"); 
    else if (red->u.lazy.false_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "FALSE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "FALSE-->(%x);", (unsigned int) red->u.lazy.false_child); 
    if (red->u.lazy.true_child == NORM_FALSE) 
      fprintf(RED_OUT, "TRUE-->FALSE;"); 
    else if (red->u.lazy.true_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "TRUE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "TRUE-->(%x);", (unsigned int) red->u.lazy.true_child); 
    fprintf(RED_OUT, "\n"); 

    if (   red->u.lazy.false_child != NORM_FALSE
        && red->u.lazy.false_child != NORM_NO_RESTRICTION 
        ) 
      rec_print_graph(red->u.lazy.false_child, depth+1); 
    if (   red->u.lazy.true_child != NORM_FALSE
        && red->u.lazy.true_child != NORM_NO_RESTRICTION 
        ) 
      rec_print_graph(red->u.lazy.true_child, depth+1); 
    break; 

  case TYPE_FLOAT:
    fprintf(RED_OUT, "V=%d:%s;%x;%x;IC=%d;", 
	    red->var_index, 
	    VAR[red->var_index].NAME,  
	    (unsigned int) red, red->status, red->u.fdd.child_count
	    );
    
    for (ci = 0; ci < red->u.fdd.child_count; ci++) {
      fc = &(red->u.fdd.arc[ci]);
      fprintf(RED_OUT, "[%.10f,%.10f]", fc->lower_bound, fc->upper_bound);
      if (fc->child == NORM_FALSE)
	fprintf(RED_OUT, "FALSE;");
      else if (fc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;");
      else
	fprintf(RED_OUT, "%x;", (unsigned int) fc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.fdd.child_count; ci++)
      rec_print_graph(red->u.fdd.arc[ci].child, depth+1);
    break; 

  case TYPE_DOUBLE:
    fprintf(RED_OUT, "V=%d:%s;%x;%x;IC=%d;", 
	    red->var_index, 
	    VAR[red->var_index].NAME,  
	    (unsigned int) red, red->status, red->u.dfdd.child_count
	    );
    
    for (ci = 0; ci < red->u.dfdd.child_count; ci++) {
      dfc = &(red->u.dfdd.arc[ci]);
      fprintf(RED_OUT, "[%f,%f]", dfc->lower_bound, dfc->upper_bound);
      if (dfc->child == NORM_FALSE)
	fprintf(RED_OUT, "FALSE;");
      else if (dfc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;");
      else
	fprintf(RED_OUT, "%x;", (unsigned int) dfc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.dfdd.child_count; ci++)
      rec_print_graph(red->u.dfdd.arc[ci].child, depth+1);
    break; 

  default:
    if (VAR[red->var_index].STATUS & FLAG_MODE) { 
      pi = VAR[red->var_index].PROC_INDEX; 
      fprintf(RED_OUT, "V=%d:%s;(%x)%x;IC=%d;", 
	      red->var_index, VAR[red->var_index].NAME,
	      (unsigned int) red, red->status, red->u.ddd.child_count
	      );
	      
      for (ci = 0; ci < red->u.ddd.child_count; ci++) {
        ic = &(red->u.ddd.arc[ci]);
        if (ic->upper_bound >= MODE_COUNT) {
	  fprintf(RED_OUT, 
	    "\nError: out-of-bound mode index %1d for %1d:%s\n", 
	    ic->upper_bound, red->var_index, VAR[red->var_index].NAME 
	  );
    	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
        }
          
        CURRENT_RED_MODE[pi].lb = ic->lower_bound; 
        CURRENT_RED_MODE[pi].ub = ic->upper_bound; 

        fprintf(RED_OUT, "[");
        mi = ic->lower_bound;
        fprintf(RED_OUT, "%s", MODE[mi].name);
        for (mi++; mi < MODE_COUNT && mi <= ic->upper_bound; mi++) {
	  fprintf(RED_OUT, ",%s", MODE[mi].name);
        }
        fprintf(RED_OUT, "]");
        if (ic->child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
        else if (ic->child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
        else
	  fprintf(RED_OUT, "%x;", (unsigned int) ic->child);

      }
      
      fprintf(RED_OUT, "\n");
      for (ci = 0; ci < red->u.ddd.child_count; ci++)
        rec_print_graph(red->u.ddd.arc[ci].child, depth+1);
    }
    else {
      fprintf(RED_OUT, "V=%d:%s;%x;%x;IC=%d;", 
	      red->var_index, 
	      VAR[red->var_index].NAME,  
	      (unsigned int) red, red->status, red->u.ddd.child_count
	      );
    
      for (ci = 0; ci < red->u.ddd.child_count; ci++) {
        ic = &(red->u.ddd.arc[ci]);
        fprintf(RED_OUT, "[%1d,%1d]", ic->lower_bound, ic->upper_bound);
        if (ic->child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
        else if (ic->child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
        else
	  fprintf(RED_OUT, "%x;", (unsigned int) ic->child);
      }
      fprintf(RED_OUT, "\n");

      for (ci = 0; ci < red->u.ddd.child_count; ci++)
        rec_print_graph(red->u.ddd.arc[ci].child, depth+1);
    }
  }
}
  /* rec_print_graph() */




void	red_print_graph(
  struct red_type	*red
) {
  int	i; 
  
  if (red == NORM_FALSE) {
    fprintf(RED_OUT, " (0), FALSE\n");
    return;
  }
  else if (red == NORM_TRUE) {
    fprintf(RED_OUT, " (0), TRUE\n");
    return;
  }

  for (i = 0; i <= PROCESS_COUNT; i++) { 
    CURRENT_RED_MODE[i].lb = CURRENT_RED_MODE[i].ub = -1; 
  }
  rec_print_graph(red, 0); 
  red_unmark(red, FLAG_GC_PRINT);  
  fflush(RED_OUT); 
}
/* red_print_graph() */ 







void	red_print_graph_depth(red, depth)
     struct red_type	*red; 
     int		depth; 
{
  int	i; 
  
  if (red == NORM_FALSE) {
    for (; depth; depth--)
      fprintf(RED_OUT, "  "); 
    fprintf(RED_OUT, " (0), FALSE\n"); 
    return;
  }
  else if (red == NORM_TRUE) {
    for (; depth; depth--)
      fprintf(RED_OUT, "  "); 
    for (; depth; depth--)
      fprintf(RED_OUT, "  ");
    fprintf(RED_OUT, " (0), TRUE\n");
    return;
  }

  for (i = 1; i <= PROCESS_COUNT; i++) { 
    CURRENT_RED_MODE[i].lb = CURRENT_RED_MODE[i].ub = -1; 
  }
  
  rec_print_graph(red, depth);
  red_unmark(red, FLAG_GC_PRINT); 
  fflush(RED_OUT); 
}
/* red_print_graph_depth() */




void	rec_print_graph_tree(red, depth)
     struct red_type	*red; 
     int		depth; 
{
  int				i, mi, ci, key; 
  struct red_link_type		*r; 
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;

  if (!red) {
    for (i = 1; i <= depth; i++)
      fprintf(RED_OUT, "  ");
    fprintf(RED_OUT, " (%1d)NULL RED\n", depth); 
    return; 
  } 
  else if (red->var_index == TYPE_TRUE) {
    if (red != NORM_TRUE) {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  ");
      fprintf(RED_OUT, " (%1d), unnormalized TRUE\n", depth); 
    }
    /* 
    else {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, " (%1d), TRUE\n", depth); 
    }
    */
    return; 
  } 
  else if (red->var_index == TYPE_FALSE) {
    if (red != NORM_FALSE) {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  "); 
      fprintf(RED_OUT, " (%1d), unnmormalized FALSE\n", depth); 
    }
    /*
    else {
      for (i = 1; i <= depth; i++)
	fprintf(RED_OUT, "  ");
      fprintf(RED_OUT, "  (%1d), FALSE\n", depth); 
    }
    */
    return;
  } 

  for (i = 1; i <= depth; i++)
    fprintf(RED_OUT, "  "); 
  fprintf(RED_OUT, " (%1d)", depth); 

  /*  fprintf(RED_OUT, "\nnew rec %x = (%x,%x)\n", (unsigned int) rec, (unsigned int) rec->redx, (unsigned int) rec->redy);
   */
  if (red->status & FLAG_GC_PRINT) {
    fprintf(RED_OUT, "%x already printed.\n", (unsigned int) red);
    return;
  } 
  else 
    red->status = red->status | FLAG_GC_PRINT; 

  switch (VAR[red->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (red->u.bdd.zero_child == NORM_FALSE) 
      fprintf(RED_OUT, "FALSE-->FALSE;"); 
    else if (red->u.bdd.zero_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "FALSE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "FALSE-->(%x);", (unsigned int) red->u.bdd.zero_child); 
    if (red->u.bdd.one_child == NORM_FALSE) 
      fprintf(RED_OUT, "TRUE-->FALSE;"); 
    else if (red->u.bdd.one_child == NORM_NO_RESTRICTION) 
      fprintf(RED_OUT, "TRUE-->TRUE;"); 
    else  
      fprintf(RED_OUT, "TRUE-->(%x);", (unsigned int) red->u.bdd.one_child); 
    fprintf(RED_OUT, "\n"); 

    rec_print_graph_tree(red->u.bdd.zero_child, depth+1); 
    rec_print_graph_tree(red->u.bdd.one_child, depth+1); 
    break; 
  case TYPE_CRD: 
    fprintf(RED_OUT, "V=%d:%s;%x;%x;r:", 
	    red->var_index, VAR[red->var_index].NAME,
	    (unsigned int) red, red->status
	    );
    fprintf(RED_OUT, ";IC=%d;", red->u.crd.child_count);
    for (ci = 0; ci < red->u.crd.child_count; ci++) {
      bc = &(red->u.crd.arc[ci]);
      if (bc->upper_bound > CLOCK_POS_INFINITY) {
	fprintf(RED_OUT, "\nError: out of bound clock inequality differences: %1d catched.\n", bc->upper_bound);
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	exit(0);
      }
      else if (bc->upper_bound < CLOCK_NEG_INFINITY) {
	fprintf(RED_OUT, "\nError: under bound clock inequality differences: %1d catched.\n", bc->upper_bound);
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	exit(0);
      }
      else if (bc->upper_bound >= CLOCK_POS_INFINITY) {
	fprintf(RED_OUT, "<oo:)");
      }
      else if (bc->upper_bound % 2) {
	fprintf(RED_OUT, "<%1d:", (bc->upper_bound+1)/2);
      }
      else
	fprintf(RED_OUT, "<=%1d:", (bc->upper_bound)/2);
      if (bc->child == NORM_FALSE)
	fprintf(RED_OUT, "FALSE;");
      else if (bc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;");
      else
	fprintf(RED_OUT, "%x;", (unsigned int) bc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.crd.child_count; ci++)
      rec_print_graph_tree(red->u.crd.arc[ci].child, depth+1);
    break; 
  case TYPE_HRD: 
    fprintf(RED_OUT, "V=%d:(%s);%x;%x;", 
	    red->var_index, red->u.hrd.hrd_exp->name, 
	    (unsigned int) red, red->status
	    );
    fprintf(RED_OUT, "IC=%d;", red->u.hrd.child_count);
    for (ci = 0; ci < red->u.hrd.child_count; ci++) {
      hc = &(red->u.hrd.arc[ci]);
      if (hc->ub_numerator % 2) {
	fprintf(RED_OUT, "<%1d", (hc->ub_numerator+1)/2);
      }
      else
	fprintf(RED_OUT, "<=%1d", (hc->ub_numerator)/2);
      if (hc->ub_denominator != 1 && hc->ub_numerator) {
	fprintf(RED_OUT, "/%1d:", hc->ub_denominator);
      }
      if (hc->child == NORM_FALSE)
	fprintf(RED_OUT, ":FALSE;");
      else if (hc->child == NORM_TRUE)
	fprintf(RED_OUT, ":TRUE;");
      else
	fprintf(RED_OUT, ":%x;", (unsigned int) hc->child);
    }
    fprintf(RED_OUT, "\n");

    for (ci = 0; ci < red->u.hrd.child_count; ci++)
      rec_print_graph_tree(red->u.hrd.arc[ci].child, depth+1);
    break; 

  case TYPE_FLOAT: 
    fprintf(RED_OUT, "V=%d:%s;%x;%x;r:", red->var_index, 
      VAR[red->var_index].NAME,
      (unsigned int) red, red->status
    );
    fprintf(RED_OUT, ";IC=%d;", red->u.fdd.child_count);
    for (ci = 0; ci < red->u.fdd.child_count; ci++) {
      fc = &(red->u.fdd.arc[ci]); 
      fprintf(RED_OUT, "[%G,%G]", fc->lower_bound, fc->upper_bound); 
      if (fc->child == NORM_FALSE) 
	fprintf(RED_OUT, "FALSE;"); 
      else if (fc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;"); 
      else 
        fprintf(RED_OUT, "%x;", (unsigned int) fc->child); 
    }
    fprintf(RED_OUT, "\n"); 

    for (ci = 0; ci < red->u.fdd.child_count; ci++) 
      rec_print_graph_tree(red->u.fdd.arc[ci].child, depth+1); 
    break; 

  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "V=%d:%s;%x;%x;r:", red->var_index, 
      VAR[red->var_index].NAME,
      (unsigned int) red, red->status
    );
    fprintf(RED_OUT, ";IC=%d;", red->u.dfdd.child_count);
    for (ci = 0; ci < red->u.dfdd.child_count; ci++) {
      dfc = &(red->u.dfdd.arc[ci]); 
      fprintf(RED_OUT, "[%G,%G]", dfc->lower_bound, dfc->upper_bound); 
      if (dfc->child == NORM_FALSE) 
	fprintf(RED_OUT, "FALSE;"); 
      else if (fc->child == NORM_TRUE)
	fprintf(RED_OUT, "TRUE;"); 
      else 
        fprintf(RED_OUT, "%x;", (unsigned int) dfc->child); 
    }
    fprintf(RED_OUT, "\n"); 

    for (ci = 0; ci < red->u.dfdd.child_count; ci++) 
      rec_print_graph_tree(red->u.dfdd.arc[ci].child, depth+1); 
    break; 

  default: 
    if (VAR[red->var_index].STATUS & FLAG_MODE) { 
      fprintf(RED_OUT, "V=%d:%s;%x;%x;r:", red->var_index, VAR[red->var_index].NAME,
	      (unsigned int) red, red->status
	      );
      fprintf(RED_OUT, ";IC=%d;", red->u.ddd.child_count);
      for (ci = 0; ci < red->u.ddd.child_count; ci++) {
        ic = &(red->u.ddd.arc[ci]);
        if (ic->upper_bound >= MODE_COUNT) {
	  fprintf(RED_OUT, "\nError: out-of-bound mode index\n");
    	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
        } 
        fprintf(RED_OUT, "[");
        mi = ic->lower_bound;
        fprintf(RED_OUT, "%s", MODE[mi].name);
        for (mi++; mi < MODE_COUNT && mi <= ic->upper_bound; mi++) {
	  fprintf(RED_OUT, ",%s", MODE[mi].name);
        }
        fprintf(RED_OUT, "]");
        if (ic->child == NORM_FALSE)
	  fprintf(RED_OUT, "FALSE;");
        else if (ic->child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;");
        else
	  fprintf(RED_OUT, "%x;", (unsigned int) ic->child);

      }
      fprintf(RED_OUT, "\n"); 
      for (ci = 0; ci < red->u.ddd.child_count; ci++) 
        rec_print_graph_tree(red->u.ddd.arc[ci].child, depth+1); 
    }
    else { 
      fprintf(RED_OUT, "V=%d:%s;%x;%x;r:", red->var_index, 
	    VAR[red->var_index].NAME,
	    (unsigned int) red, red->status
	    );
      fprintf(RED_OUT, ";IC=%d;", red->u.ddd.child_count);
      for (ci = 0; ci < red->u.ddd.child_count; ci++) {
        ic = &(red->u.ddd.arc[ci]); 
        fprintf(RED_OUT, "[%1d,%1d]", ic->lower_bound, ic->upper_bound); 
        if (ic->child == NORM_FALSE) 
	  fprintf(RED_OUT, "FALSE;"); 
        else if (ic->child == NORM_TRUE)
	  fprintf(RED_OUT, "TRUE;"); 
        else 
	  fprintf(RED_OUT, "%x;", (unsigned int) ic->child); 
      }
      fprintf(RED_OUT, "\n"); 

      for (ci = 0; ci < red->u.ddd.child_count; ci++) 
        rec_print_graph_tree(red->u.ddd.arc[ci].child, depth+1); 
    }
  }
}
  /* rec_print_graph_tree() */




void	red_print_graph_tree(red)
     struct red_type	*red;
{
  int 	i; 
  
  if (red == NORM_FALSE) {
    fprintf(RED_OUT, " (0), FALSE\n"); 
    return;
  }
  else if (red == NORM_TRUE) {
    fprintf(RED_OUT, " (0), TRUE\n"); 
    return;
  }
    
  for (i = 1; i <= PROCESS_COUNT; i++) { 
    CURRENT_RED_MODE[i].lb = CURRENT_RED_MODE[i].ub = -1; 
  }
  
  rec_print_graph_tree(red, 0); 
  red_unmark(red, FLAG_GC_PRINT); 
}
/* red_print_graph_tree() */ 



void	red_print_formulus(); 

void	red_print_long_disj(flag_clause_head, d, linestart, curpos)
     struct red_type	*d;
     int		flag_clause_head, linestart, curpos; 
{ 
  char	*name; 
  int	ci, i, b, den, mi; 

  if (curpos + 3 > 80) {
    for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
    curpos = linestart;
  }
  if (flag_clause_head)
    fprintf(RED_OUT, "(\n");
  else
    fprintf(RED_OUT, "&&(\n");
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD:   
    name = VAR[d->var_index].NAME; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) {
        fprintf(RED_OUT, " ||");
        red_print_formulus(TYPE_TRUE, d->u.crd.arc[ci].child, linestart + 3,
      	  		   linestart+3 + strlen(name)
      	  		   );
      }
      else if (d->u.crd.arc[ci].upper_bound % 2) {
        b = (d->u.crd.arc[ci].upper_bound + 1)/2;
        fprintf(RED_OUT, " ||%s<%1d", name, b);
        red_print_formulus(TYPE_FALSE, d->u.crd.arc[ci].child, linestart + 3,
       		     linestart+4 + strlen(name) + intlen(b)
       		     );
      }
      else {
        b = d->u.crd.arc[ci].upper_bound /2;
        fprintf(RED_OUT, " ||%s<=%1d", name, b);
        red_print_formulus(TYPE_FALSE, d->u.crd.arc[ci].child, linestart + 3,
       		     linestart+5 + strlen(name) + intlen(b)
       		     );
      }
    }
    break; 
  case TYPE_HRD:
    name = d->u.hrd.hrd_exp->name; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
      b = d->u.hrd.arc[ci].ub_numerator;
      den = d->u.hrd.arc[ci].ub_denominator;
      if (den == 1) {
	if (b % 2) {
	  if (b == HYBRID_POS_INFINITY)
	    fprintf(RED_OUT, " ||%s<oo", name);
	  else
	    fprintf(RED_OUT, " ||%s<%1d", name, (b+1)/2);
	  red_print_formulus(TYPE_FALSE, d->u.hrd.arc[ci].child, linestart + 3,
	     linestart+4 + strlen(name) + intlen((b+1)/2)
	     );
	}
	else {
	  fprintf(RED_OUT, " ||%s<=%1d", name, b/2);
	  red_print_formulus(TYPE_FALSE, d->u.hrd.arc[ci].child, linestart + 3,
			     linestart+5 + strlen(name) + intlen(b/2)
			     );
	}
      }
      else
	if (b % 2) {
	  fprintf(RED_OUT, " ||%s<%1d/%1d", name, (b+1)/2, den);
	  red_print_formulus(TYPE_FALSE, d->u.hrd.arc[ci].child, linestart + 3,
			       linestart+5 + strlen(name) + intlen((b+1)/2) + intlen(den)
			       );
	}
	else {
	  fprintf(RED_OUT, " ||%s<=%1d", name, b/2, den);
	  red_print_formulus(TYPE_FALSE, d->u.hrd.arc[ci].child, linestart + 3,
			     linestart+6 + strlen(name) + intlen(b/2) + intlen(den)
			     );
	}
    }
    break; 

  case TYPE_FLOAT: {
      char	*name; 
      
      name = VAR[d->var_index].NAME; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) {
        for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
        if (d->u.fdd.arc[ci].lower_bound = d->u.fdd.arc[ci].upper_bound) {
          fprintf(RED_OUT, " ||%s=%G", name, d->u.fdd.arc[0].lower_bound);
          curpos = curpos + 4 + strlen(name)
    	         + fltlen(d->u.fdd.arc[ci].lower_bound);
        } 
        else {
          fprintf(RED_OUT, " ||%G<=%s<=%G", d->u.fdd.arc[ci].lower_bound,  
            name, d->u.fdd.arc[ci].upper_bound
          ); 
          curpos = curpos + 7 + strlen(name)  
      	         + fltlen(d->u.fdd.arc[ci].lower_bound) 
      	         + fltlen(d->u.fdd.arc[ci].upper_bound);
        } 
        red_print_formulus(TYPE_FALSE, d->u.fdd.arc[ci].child, linestart+3, curpos); 
      }      
    } 
    for (i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
    fprintf(RED_OUT, ")\n"); 
    break; 

  case TYPE_DOUBLE: {
      char	*name; 
      
      name = VAR[d->var_index].NAME; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
        for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
        if (d->u.dfdd.arc[ci].lower_bound = d->u.dfdd.arc[ci].upper_bound) {
          fprintf(RED_OUT, " ||%s=%G", name, d->u.dfdd.arc[0].lower_bound);
          curpos = curpos + 4 + strlen(name)
    	         + dbllen(d->u.dfdd.arc[ci].lower_bound);
        } 
        else {
          fprintf(RED_OUT, " ||%G<=%s<=%G", d->u.dfdd.arc[ci].lower_bound,  
            name, d->u.dfdd.arc[ci].upper_bound
          ); 
          curpos = curpos + 7 + strlen(name)  
      	         + dbllen(d->u.dfdd.arc[ci].lower_bound) 
      	         + dbllen(d->u.dfdd.arc[ci].upper_bound);
        } 
        red_print_formulus(TYPE_FALSE, d->u.dfdd.arc[ci].child, linestart+3, curpos); 
      }      
    } 
    for (i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
    fprintf(RED_OUT, ")\n"); 
    break; 

  default: 
    if (VAR[d->var_index].STATUS == FLAG_MODE) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
        mi = d->u.ddd.arc[ci].lower_bound;
        fprintf(RED_OUT, " ||%s=[%s", VAR[d->var_index].NAME, MODE[mi].name);
        curpos = linestart + 5 + strlen(VAR[d->var_index].NAME) + strlen(MODE[mi].name);
        for (mi++; 
          mi < MODE_COUNT && mi <= d->u.ddd.arc[ci].upper_bound; 
          mi++
          ) {
          fprintf(RED_OUT, ",%s", MODE[mi].name);
	  curpos = curpos + 1 + strlen(MODE[mi].name);
        }
        fprintf(RED_OUT, "]");
        curpos = curpos + 1;
        red_print_formulus(TYPE_FALSE, d->u.ddd.arc[ci].child, linestart+3, curpos);
      }
    }
    else {
      char	*name; 
      
      name = VAR[d->var_index].NAME; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
        if (d->u.ddd.arc[ci].lower_bound = d->u.ddd.arc[ci].upper_bound) {
          fprintf(RED_OUT, " ||%s=%1d", name, d->u.ddd.arc[0].lower_bound);
          curpos = curpos + 4 + strlen(name)
    	         + intlen(d->u.ddd.arc[ci].lower_bound);
        } 
        else {
          fprintf(RED_OUT, " ||%1d<=%s<=%1d", d->u.ddd.arc[ci].lower_bound,  
            name, d->u.ddd.arc[ci].upper_bound
          ); 
          curpos = curpos + 7 + strlen(name)  
      	         + intlen(d->u.ddd.arc[ci].lower_bound) 
      	         + intlen(d->u.ddd.arc[ci].upper_bound);
        } 
        red_print_formulus(TYPE_FALSE, d->u.ddd.arc[ci].child, linestart+3, curpos); 
      }      
    } 
    for (i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
    fprintf(RED_OUT, ")\n"); 
  }
}
  /* red_print_long_disj() */ 
  





void	red_print_formulus(flag_clause_head, d, linestart, curpos)
     struct red_type	*d;
     int		flag_clause_head, linestart, curpos;
{
  int			i, mi, ci, namelen, b, den;
  struct rec_type	*rec, *nrec;

  if (!d) {
    if (curpos + 10 > 80)
      for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
    if (flag_clause_head) 
      fprintf(RED_OUT, "(NULL RED)\n"); 
    else 
      fprintf(RED_OUT, "&&(NULL RED)\n");
    return; 
  }
  else if (d == NORM_NO_RESTRICTION) {
    fprintf(RED_OUT, "\n"); 
  }
  else if (d == NORM_FALSE) { 
    if (curpos + 7 > 80)
      for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
    if (flag_clause_head)
      fprintf(RED_OUT, "(TYPE_FALSE)\n");
    else
      fprintf(RED_OUT, "&&(TYPE_FALSE)\n");
    return;
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    if (d->u.crd.child_count == 1) {
      char	*name; 
      	  
      if (d->u.crd.arc[0].upper_bound == CLOCK_POS_INFINITY) {
        red_print_formulus(flag_clause_head, d->u.crd.arc[0].child, linestart, curpos);
      }
      else if (d->u.crd.arc[0].upper_bound % 2) {
      	name = VAR[d->var_index].NAME; 
      	b = (d->u.crd.arc[0].upper_bound + 1)/2;
      	if (flag_clause_head) {
	  if (curpos + strlen(name) + 1 + intlen(b) > 80) {
	    for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
	    curpos = linestart;
	  }

	  fprintf(RED_OUT, "%s<%1d", name, b);
	  curpos = curpos + strlen(name) + 1 + intlen(b);
        }
        else {
	  if (curpos + strlen(name) + 3 + intlen(b) > 80) {
	    for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
	    curpos = linestart;
	  }

	  fprintf(RED_OUT, "&&%s<%1d", name, b);
	  curpos = curpos + strlen(name) + 3 + intlen(b);
        }
        red_print_formulus(TYPE_FALSE, d->u.crd.arc[0].child, linestart, curpos);
      }
      else {
        name = VAR[d->var_index].NAME; 
      	b = d->u.crd.arc[0].upper_bound / 2;
      	if (flag_clause_head) {
	  if (curpos + strlen(name) + 2 + intlen(b) > 80) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
            curpos = linestart;
      	  }
      	  fprintf(RED_OUT, "%s<=%1d", name, b);
      	  curpos = curpos + strlen(name) + 2 + intlen(b);
        }
        else {
	  if (curpos + strlen(name) + 4 + intlen(b) > 80) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
            curpos = linestart;
      	  }
      	  fprintf(RED_OUT, "&&%s<=%1d", name, b);
      	  curpos = curpos + strlen(name) + 4 + intlen(b);
        }
        red_print_formulus(TYPE_FALSE, d->u.crd.arc[0].child, linestart, curpos);
      }
    }
    else 
      red_print_long_disj(flag_clause_head, d, linestart, curpos); 
    break; 
  case TYPE_HRD:
    if (d->u.hrd.child_count == 1) {
      char	*name; 
      
      for (i = 0; i < linestart; i++, fprintf(RED_OUT, " "));
      b = d->u.hrd.arc[0].ub_numerator;
      den = d->u.hrd.arc[0].ub_denominator;
      name = d->u.hrd.hrd_exp->name; 
      
      if (den == 1) {
	if (b % 2) {
	  if (flag_clause_head) {
	    if (b == HYBRID_POS_INFINITY)
	      fprintf(RED_OUT, "%s<oo", name);
	    else
	      fprintf(RED_OUT, "%s<%1d", name, (b+1)/2);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart,
			       linestart+1 + strlen(name) + intlen((b+1)/2)
			       );
	  }
	  else {
	    if (b == HYBRID_POS_INFINITY)
	      fprintf(RED_OUT, "&&%s<oo", name);
	    else
	      fprintf(RED_OUT, "&&%s<%1d", name, (b+1)/2);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart + 2,
			       linestart+3 + strlen(name) + intlen((b+1)/2)
			       );
	  }
	}
	else {
	  if (flag_clause_head) {
	    fprintf(RED_OUT, "%s<=%1d", name, b/2);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart+2,
			       linestart+2 + strlen(name) + intlen(b/2)
			       );
	  }
	  else {
	    fprintf(RED_OUT, "&&%s<=%1d", name, b/2);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart + 2,
			       linestart+4 + strlen(name) + intlen(b/2)
			       );
	  }
	}
      }
      else
	if (b % 2) {
	  if (flag_clause_head) {
	    fprintf(RED_OUT, "%s<=%1d/%1d", name, (b+1)/2, den);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart+2,
			       linestart+3 + strlen(name) + intlen((b+1)/2) + intlen(den)
			       );
	  }
	  else {
	    fprintf(RED_OUT, "&&%s<=%1d/%1d", name, (b+1)/2, den);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart + 2,
			       linestart+5 + strlen(name) + intlen((b+1)/2) +  intlen(den)
			       );
	  }
	}
	else {
	  if (flag_clause_head) {
	    fprintf(RED_OUT, "%s<=%1d/%1d", name, b/2, den);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart+2,
			       linestart+3 + strlen(name) + intlen(b/2) + intlen(den)
			       );
	  }
	  else {
	    fprintf(RED_OUT, "&&%s<=%1d/%1d", name, b/2, den);
	    red_print_formulus(TYPE_FALSE, d->u.hrd.arc[0].child, linestart + 2,
			       linestart+5 + strlen(name) + intlen(b/2) + intlen(den)
			       );
	  }
	}
    }
    else 
      red_print_long_disj(flag_clause_head, d, linestart, curpos); 
    break; 

  case TYPE_FLOAT:  
    if (d->u.fdd.child_count > 1)
      red_print_long_disj(flag_clause_head, d, linestart, curpos); 
    else {
      char	*name; 
      
      name = VAR[d->var_index].NAME; 
      if (d->u.fdd.arc[0].lower_bound == d->u.fdd.arc[0].upper_bound) { 
        if (flag_clause_head) {
	  if (curpos + 1 + strlen(name)
	    + fltlen(d->u.fdd.arc[0].lower_bound)
           > 80
           ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          } 
          fprintf(RED_OUT, "%s=%G", name, d->u.fdd.arc[0].lower_bound); 
          curpos = curpos + 1 + strlen(name)
          + fltlen(d->u.fdd.arc[0].lower_bound);
        }
        else { 
	  if (curpos + 3 + strlen(name)  
	    + intlen(d->u.fdd.arc[0].lower_bound)
            > 80
            ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          } 
          fprintf(RED_OUT, "&&%s=%G", name, d->u.fdd.arc[0].lower_bound); 
          curpos = curpos + 3 + strlen(name)
          + fltlen(d->u.fdd.arc[0].lower_bound);
        } 
      }  
      else { 
        if (flag_clause_head) { 
      	  if (curpos + 4 + strlen(name)  
      	    + fltlen(d->u.fdd.arc[0].lower_bound) + fltlen(d->u.fdd.arc[0].upper_bound) 
      	    > 80
      	    ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart;
          }
          fprintf(RED_OUT, "%G<=%s<=%G", d->u.fdd.arc[0].lower_bound,  
            name, d->u.fdd.arc[0].upper_bound
          );
          curpos = curpos + 4 + strlen(name)  
      	       + fltlen(d->u.fdd.arc[0].lower_bound) + fltlen(d->u.fdd.arc[0].upper_bound);
        } 
        else { 
      	  if (curpos + 6 + strlen(name)
      	    + fltlen(d->u.fdd.arc[0].lower_bound) + fltlen(d->u.fdd.arc[0].upper_bound)
      	    > 80
      	    ) { 
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          }
          fprintf(RED_OUT, "&&%G<=%s<=%G", d->u.fdd.arc[0].lower_bound, 
            name, d->u.fdd.arc[0].upper_bound
          ); 
          curpos = curpos + 6 + strlen(name)
          + fltlen(d->u.fdd.arc[0].lower_bound) + fltlen(d->u.fdd.arc[0].upper_bound);

        }
      }
      red_print_formulus(TYPE_FALSE, d->u.fdd.arc[0].child, linestart, curpos);
    }
    break; 
    
  case TYPE_DOUBLE:  
    if (d->u.dfdd.child_count > 1)
      red_print_long_disj(flag_clause_head, d, linestart, curpos); 
    else {
      char	*name; 
      
      name = VAR[d->var_index].NAME; 
      if (d->u.dfdd.arc[0].lower_bound == d->u.dfdd.arc[0].upper_bound) { 
        if (flag_clause_head) {
	  if (curpos + 1 + strlen(name)
	    + intlen(d->u.dfdd.arc[0].lower_bound)
           > 80
           ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          } 
          fprintf(RED_OUT, "%s=%G", name, d->u.dfdd.arc[0].lower_bound); 
          curpos = curpos + 1 + strlen(name)
          + dbllen(d->u.dfdd.arc[0].lower_bound);
        }
        else { 
	  if (curpos + 3 + strlen(name)  
	    + intlen(d->u.dfdd.arc[0].lower_bound)
            > 80
            ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          } 
          fprintf(RED_OUT, "&&%s=%G", name, d->u.dfdd.arc[0].lower_bound); 
          curpos = curpos + 3 + strlen(name)
          + dbllen(d->u.dfdd.arc[0].lower_bound);
        } 
      }  
      else { 
        if (flag_clause_head) { 
      	  if (curpos + 4 + strlen(name)  
      	    + intlen(d->u.dfdd.arc[0].lower_bound) + intlen(d->u.dfdd.arc[0].upper_bound) 
      	    > 80
      	    ) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart;
          }
          fprintf(RED_OUT, "%G<=%s<=%G", d->u.dfdd.arc[0].lower_bound,  
            name, d->u.dfdd.arc[0].upper_bound
          );
          curpos = curpos + 4 + strlen(name)  
      	       + dbllen(d->u.dfdd.arc[0].lower_bound) + dbllen(d->u.dfdd.arc[0].upper_bound);
        } 
        else { 
      	  if (curpos + 6 + strlen(name)
      	    + dbllen(d->u.dfdd.arc[0].lower_bound) + dbllen(d->u.dfdd.arc[0].upper_bound)
      	    > 80
      	    ) { 
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          }
          fprintf(RED_OUT, "&&%G<=%s<=%G", d->u.dfdd.arc[0].lower_bound, 
            name, d->u.dfdd.arc[0].upper_bound
          ); 
          curpos = curpos + 6 + strlen(name)
          + dbllen(d->u.dfdd.arc[0].lower_bound) + dbllen(d->u.dfdd.arc[0].upper_bound);

        }
      }
      red_print_formulus(TYPE_FALSE, d->u.dfdd.arc[0].child, linestart, curpos);
    }
    break; 

  default: 
    if (d->u.ddd.child_count == 1) {
      if (VAR[d->var_index].STATUS & FLAG_MODE) { 
        if (d->u.ddd.arc[0].upper_bound >= MODE_COUNT) {
	  fprintf(RED_OUT, "\nError: out-of-bound mode index\n");
    	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	  exit(0);
        }
        if (flag_clause_head) {
          namelen = strlen(VAR[d->var_index].NAME) + 3
		+ d->u.ddd.arc[0].upper_bound - d->u.ddd.arc[0].lower_bound;
          for (mi=d->u.ddd.arc[0].lower_bound; mi <= d->u.ddd.arc[0].upper_bound; mi++) {
	    namelen = namelen + strlen(MODE[mi].name); 
          }

          if (curpos + namelen > 80) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart;
          } 
          mi = d->u.ddd.arc[0].lower_bound; 
          fprintf(RED_OUT, "%s=[%s", VAR[d->var_index].NAME, MODE[mi].name); 
        }
        else {
          namelen = strlen(VAR[d->var_index].NAME) + 5
		+ d->u.ddd.arc[0].upper_bound - d->u.ddd.arc[0].lower_bound; 
          for (mi=d->u.ddd.arc[0].lower_bound; mi <= d->u.ddd.arc[0].upper_bound; mi++) {
	    namelen = namelen + strlen(MODE[mi].name); 
          }

          if (curpos + namelen > 80) {
            for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
            curpos = linestart; 
          } 
          mi = d->u.ddd.arc[0].lower_bound; 
          fprintf(RED_OUT, "&&%s=[%s", VAR[d->var_index].NAME, MODE[mi].name);
        }
        for (mi++; mi < MODE_COUNT && mi <= d->u.ddd.arc[0].upper_bound; mi++) {
	  fprintf(RED_OUT, ",%s", MODE[mi].name); 
        }
        fprintf(RED_OUT, "]"); 
        curpos = curpos + namelen; 
        red_print_formulus(TYPE_FALSE, d->u.ddd.arc[0].child, linestart, curpos); 
      } 
      else {
        char	*name; 
      
        name = VAR[d->var_index].NAME; 
        if (d->u.ddd.arc[0].lower_bound == d->u.ddd.arc[0].upper_bound) { 
      	  if (flag_clause_head) {
	    if (curpos + 1 + strlen(name)
	      + intlen(d->u.ddd.arc[0].lower_bound)
      	      > 80
      	      ) {
              for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
              curpos = linestart; 
            } 
            fprintf(RED_OUT, "%s=%1d", name, d->u.ddd.arc[0].lower_bound); 
            curpos = curpos + 1 + strlen(name)
      	         + intlen(d->u.ddd.arc[0].lower_bound);
          }
          else { 
	    if (curpos + 3 + strlen(name)  
	      + intlen(d->u.ddd.arc[0].lower_bound)
      	      > 80
      	      ) {
              for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
              curpos = linestart; 
            } 
            fprintf(RED_OUT, "&&%s=%1d", name, d->u.ddd.arc[0].lower_bound); 
            curpos = curpos + 3 + strlen(name)
      	         + intlen(d->u.ddd.arc[0].lower_bound);
          } 
        }  
        else { 
      	  if (flag_clause_head) { 
      	    if (curpos + 4 + strlen(name)  
      	      + intlen(d->u.ddd.arc[0].lower_bound) + intlen(d->u.ddd.arc[0].upper_bound) 
      	      > 80
      	      ) {
              for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
              curpos = linestart;
            }
            fprintf(RED_OUT, "%1d<=%s<=%1d", d->u.ddd.arc[0].lower_bound,  
              name, d->u.ddd.arc[0].upper_bound
            );
            curpos = curpos + 4 + strlen(name)  
      	         + intlen(d->u.ddd.arc[0].lower_bound) + intlen(d->u.ddd.arc[0].upper_bound);
          } 
          else { 
      	    if (curpos + 6 + strlen(name)
      	      + intlen(d->u.ddd.arc[0].lower_bound) + intlen(d->u.ddd.arc[0].upper_bound)
      	      > 80
      	      ) { 
              for (fprintf(RED_OUT, "\n"), i = 0; i < linestart; i++, fprintf(RED_OUT, " ")); 
              curpos = linestart; 
            }
            fprintf(RED_OUT, "&&%1d<=%s<=%1d", d->u.ddd.arc[0].lower_bound, 
              name, d->u.ddd.arc[0].upper_bound
            ); 
            curpos = curpos + 6 + strlen(name)
      	           + intlen(d->u.ddd.arc[0].lower_bound) + intlen(d->u.ddd.arc[0].upper_bound);

          }
        }
        red_print_formulus(TYPE_FALSE, d->u.ddd.arc[0].child, linestart, curpos);
      }
    }
    else 
      red_print_long_disj(flag_clause_head, d, linestart, curpos); 
  }
}
/* red_print_formulus() */







void red_print_atom(d, lb, ub)
     struct red_type	*d;
     int		lb, ub;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
  case TYPE_HRD:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;

  default:
    if (VAR[d->var_index].STATUS & FLAG_MODE) 
      if (lb == ub) {
        if (VAR[d->var_index].STATUS & FLAG_VAR_PRIMED) 
          fprintf(RED_OUT, "%s'@(%1d)", 
            MODE[lb].name, VAR[d->var_index].PROC_INDEX
          );
        else 
          fprintf(RED_OUT, "%s@(%1d)", 
            MODE[lb].name, VAR[d->var_index].PROC_INDEX
          );
      }
      else if (lb < ub) { 
        if (VAR[d->var_index].STATUS & FLAG_VAR_PRIMED) 
          fprintf(RED_OUT, "(%s'@(%1d)", 
            MODE[lb].name, VAR[d->var_index].PROC_INDEX
          );
        else 
          fprintf(RED_OUT, "(%s@(%1d)", 
            MODE[lb].name, VAR[d->var_index].PROC_INDEX
          );
      	for (lb++; lb <= ub; lb++) { 
          if (VAR[d->var_index].STATUS & FLAG_VAR_PRIMED) 
            fprintf(RED_OUT, "||%s'@(%1d)", 
              MODE[lb].name, VAR[d->var_index].PROC_INDEX
            );
          else 
            fprintf(RED_OUT, "||%s@(%1d)", 
              MODE[lb].name, VAR[d->var_index].PROC_INDEX
            );
      	} 
      	fprintf(RED_OUT, ")"); 
      } 
      else { 
      	fprintf(RED_OUT, "An error at printing a CRD atom. \n"); 
      	exit(0); 
      } 
    else if (lb == ub)
      if (   d->var_index >= MEMORY_START_VI 
          && d->var_index < VARIABLE_COUNT
          ) 
        fprintf(RED_OUT, "%s==%1d", VAR[d->var_index].NAME, ub);
      else 
        fprintf(RED_OUT, "%s==0x%x", VAR[d->var_index].NAME, ub);
    else
      if (   d->var_index >= MEMORY_START_VI 
          && d->var_index < VARIABLE_COUNT
          ) 
        fprintf(RED_OUT, "(0x%x<=%s&&%s<=0x%x)", 
          lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
        );
      else 
        fprintf(RED_OUT, "(%1d<=%s&&%s<=%1d)", 
          lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
        );
  }
}
/* red_print_atom() */



void red_print_fatom(d, lb, ub)
     struct red_type	*d;
     float		lb, ub;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_FLOAT: 
    if (lb == ub)
      fprintf(RED_OUT, "%s==%G", VAR[d->var_index].NAME, ub);
    else
      fprintf(RED_OUT, "(%G<=%s&&%s<=%G)", 
        lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
      );
    break; 
  case TYPE_CRD:
  case TYPE_HRD:
  case TYPE_DOUBLE: 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;

  }
}
/* red_print_fatom() */



void red_print_datom(d, lb, ub)
     struct red_type	*d;
     double		lb, ub;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_DOUBLE: 
    if (lb == ub)
      fprintf(RED_OUT, "%s==%G", VAR[d->var_index].NAME, ub);
    else
      fprintf(RED_OUT, "(%G<=%s&&%s<=%G)", 
        lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
      );
    break; 
  case TYPE_CRD:
  case TYPE_HRD:
  case TYPE_FLOAT: 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;

  }
}
/* red_print_datom() */



void red_print_ineq(d, ub)
     struct red_type	*d;
     int		ub;
{
  if (VAR[d->var_index].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub != CLOCK_POS_INFINITY) {
    if (VAR[d->var_index].U.CRD.CLOCK1 == 0) {
      if (ub == CLOCK_NEG_INFINITY)
	fprintf(RED_OUT, "%1d<%s", -(ub+1)/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		);
      else if (ub % 2)
	fprintf(RED_OUT, "%1d<%s", -(ub+1)/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		);
      else
	fprintf(RED_OUT, "%1d<=%s", -ub/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		);
    }
    else if (VAR[d->var_index].U.CRD.CLOCK2 == 0) {
      if (ub == CLOCK_NEG_INFINITY)
	fprintf(RED_OUT, "%s<-%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		ub/2
		);
      else if (ub % 2)
	fprintf(RED_OUT, "%s<%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		(ub+1)/2
		);
      else
	fprintf(RED_OUT, "%s<=%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		ub/2
		);
    }
    else if (ub == CLOCK_NEG_INFINITY)
      fprintf(RED_OUT, "%s<-%1d", VAR[d->var_index].NAME, ub/2);
    else if (ub % 2)
      fprintf(RED_OUT, "%s<%1d", VAR[d->var_index].NAME, (ub+1)/2);
    else
      fprintf(RED_OUT, "%s<=%1d", VAR[d->var_index].NAME, ub/2);
  }
}
/* red_print_ineq() */





void red_print_hybrid_ineq(d, ub_numerator, ub_denominator)
     struct red_type	*d;
     int		ub_numerator, ub_denominator;
{
  if (VAR[d->var_index].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub_denominator == 1) {
    if (ub_numerator % 2)
      if (ub_numerator == HYBRID_POS_INFINITY)
        fprintf(RED_OUT, "%s<oo", d->u.hrd.hrd_exp->name);
      else 
        fprintf(RED_OUT, "%s<%1d", d->u.hrd.hrd_exp->name, (ub_numerator+1)/2);
    else
      fprintf(RED_OUT, "%s<=%1d", d->u.hrd.hrd_exp->name, ub_numerator/2);
  }
  else {
    if (ub_numerator % 2)
      fprintf(RED_OUT, "%s<%1d/%1d", d->u.hrd.hrd_exp->name, (ub_numerator+1)/2, ub_denominator);
    else
      fprintf(RED_OUT, "%s<=%1d/%1d", d->u.hrd.hrd_exp->name, ub_numerator/2, ub_denominator);
  }
}
/* red_print_hybrid_ineq() */





void 	red_print_line();

void	red_print_conj(d, ci)
     struct red_type	*d;
     int		ci;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) 
      red_print_line(d->u.crd.arc[ci].child);      
    else if (d->u.crd.arc[ci].child == NORM_TRUE)
      red_print_ineq(d, d->u.crd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_ineq(d, d->u.crd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line(d->u.crd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_HRD:
    if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY 
        && d->u.hrd.arc[ci].ub_denominator == 1
        )
      red_print_line(d->u.hrd.arc[ci].child);
    else if (d->u.hrd.arc[ci].child == NORM_TRUE)
      red_print_hybrid_ineq(d, d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator);
    else {
      fprintf(RED_OUT, "(");
      red_print_hybrid_ineq(d, d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator);
      fprintf(RED_OUT, " && ");
      red_print_line(d->u.hrd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "(((~("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, "))&&("); 
    red_print_line(d->u.lazy.false_child); 
    fprintf(RED_OUT, "))||(("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, ")&&("); 
    red_print_line(d->u.lazy.true_child); 
    fprintf(RED_OUT, ")))"); 
    break; 
  case TYPE_FLOAT:
    if (d->u.fdd.arc[ci].child == NORM_TRUE)
      red_print_fatom(d, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_fatom(d, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line(d->u.fdd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break; 
  case TYPE_DOUBLE:
    if (d->u.dfdd.arc[ci].child == NORM_TRUE)
      red_print_datom(d, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_datom(d, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line(d->u.dfdd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break; 
  default:
    if (d->u.ddd.arc[ci].child == NORM_TRUE)
      red_print_atom(d, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_atom(d, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line(d->u.ddd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
  }
}
  /* red_print_conj() */


int	count_rpl = 0; 

void	red_print_line(d)
     struct red_type	*d;
{
  struct index_link_type	*pil, *pi_list, *xil, *xi_list;
  struct red_type		*result;
  int				ci;

/*
  printf("\nrpl %1d:\n", ++count_rpl); 
  red_print_graph(d); 
*/  
  if (VAR[d->var_index].TYPE == TYPE_FALSE)
    fprintf(RED_OUT, "FALSE");
  else if (VAR[d->var_index].TYPE == TYPE_TRUE)
    fprintf(RED_OUT, "TRUE");
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (d->u.bdd.zero_child == d->u.bdd.one_child) { 
      fprintf(RED_OUT, "Error: Something wrong, both children of a bdd node are the same.\n"); 
      exit(0); 
    } 
    else if (d->u.bdd.zero_child == NORM_FALSE) {
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION)  
        fprintf(RED_OUT, "%s", VAR[d->var_index].NAME); 
      else { 
        fprintf(RED_OUT, "(%s&&", VAR[d->var_index].NAME); 
        red_print_line(d->u.bdd.one_child); 
        fprintf(RED_OUT, ")"); 
      } 
    }
    else if (d->u.bdd.one_child == NORM_FALSE) { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION)  
        fprintf(RED_OUT, "(not %s)", VAR[d->var_index].NAME); 
      else { 
        fprintf(RED_OUT, "((not %s)&&", VAR[d->var_index].NAME); 
        red_print_line(d->u.bdd.zero_child); 
        fprintf(RED_OUT, ")"); 
      } 
    } 
    else { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "((not %s)", VAR[d->var_index].NAME); 
      } 
      else { 
        fprintf(RED_OUT, "(((not %s)&&", VAR[d->var_index].NAME); 
        red_print_line(d->u.bdd.zero_child); 
        fprintf(RED_OUT, ")"); 
      } 
      fprintf(RED_OUT, "||"); 
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "%s)", VAR[d->var_index].NAME); 
      } 
      else { 
        fprintf(RED_OUT, "(%s&&", VAR[d->var_index].NAME); 
        red_print_line(d->u.bdd.one_child); 
        fprintf(RED_OUT, "))"); 
      } 
    } 
    break; 
  case TYPE_CRD:
    if (d->u.crd.child_count == 1) {
      red_print_ineq(d, d->u.crd.arc[0].upper_bound);
      if (d->u.crd.arc[0].child != NORM_NO_RESTRICTION) {
	if (d->u.crd.arc[0].upper_bound != CLOCK_POS_INFINITY)
	  fprintf(RED_OUT, " && ");
	red_print_line(d->u.crd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj(d, 0);
      for (ci = 1; ci < d->u.crd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_HRD:
    if (d->u.hrd.child_count == 1) {
      red_print_hybrid_ineq(d, d->u.hrd.arc[0].ub_numerator, d->u.hrd.arc[0].ub_denominator);
      if (d->u.hrd.arc[0].child != NORM_NO_RESTRICTION) {
        fprintf(RED_OUT, " && ");
	red_print_line(d->u.hrd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj(d, 0);
      for (ci = 1; ci < d->u.hrd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "(((~("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, "))&&("); 
    red_print_line(d->u.lazy.false_child); 
    fprintf(RED_OUT, "))||(("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, ")&&("); 
    red_print_line(d->u.lazy.true_child); 
    fprintf(RED_OUT, ")))");     
    break; 

  case TYPE_FLOAT:
    if (d->u.fdd.child_count == 1) {
      red_print_fatom(d, d->u.fdd.arc[0].lower_bound, d->u.fdd.arc[0].upper_bound);
      if (d->u.fdd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line(d->u.fdd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj(d, 0);
      for (ci = 1; ci < d->u.fdd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break; 

  case TYPE_DOUBLE:
    if (d->u.dfdd.child_count == 1) {
      red_print_fatom(d, d->u.dfdd.arc[0].lower_bound, d->u.dfdd.arc[0].upper_bound);
      if (d->u.dfdd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line(d->u.dfdd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj(d, 0);
      for (ci = 1; ci < d->u.dfdd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break; 

  default:
    if (d->u.ddd.child_count == 1) {
      red_print_atom(d, d->u.ddd.arc[0].lower_bound, d->u.ddd.arc[0].upper_bound);
      if (d->u.ddd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line(d->u.ddd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj(d, 0);
      for (ci = 1; ci < d->u.ddd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
  }
}
/* red_print_line() */




void 	red_print_line_break();

void	red_print_conj_break(d, ci)
     struct red_type	*d;
     int		ci;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY)
      red_print_line_break(d->u.crd.arc[ci].child);
    else if (d->u.crd.arc[ci].child == NORM_TRUE)
      red_print_ineq(d, d->u.crd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_ineq(d, d->u.crd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line_break(d->u.crd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_HRD:
    if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY 
        && d->u.hrd.arc[ci].ub_denominator == 1
        )
      red_print_line_break(d->u.hrd.arc[ci].child);
    else if (d->u.hrd.arc[ci].child == NORM_TRUE)
      red_print_hybrid_ineq(d, d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator);
    else {
      fprintf(RED_OUT, "(");
      red_print_hybrid_ineq(d, d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator);
      fprintf(RED_OUT, " && ");
      red_print_line_break(d->u.hrd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "(((~("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, "))&&("); 
    red_print_line(d->u.lazy.false_child); 
    fprintf(RED_OUT, "))||(("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, ")&&("); 
    red_print_line(d->u.lazy.true_child); 
    fprintf(RED_OUT, ")))");     
    break; 

  case TYPE_FLOAT:
    if (d->u.fdd.arc[ci].child == NORM_TRUE)
      red_print_fatom(d, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_fatom(d, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line_break(d->u.fdd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break; 

  case TYPE_DOUBLE:
    if (d->u.dfdd.arc[ci].child == NORM_TRUE)
      red_print_datom(d, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_datom(d, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line_break(d->u.dfdd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
    break; 

  default:
    if (d->u.ddd.arc[ci].child == NORM_TRUE)
      red_print_atom(d, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
    else {
      fprintf(RED_OUT, "(");
      red_print_atom(d, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      fprintf(RED_OUT, " && ");
      red_print_line_break(d->u.ddd.arc[ci].child);
      fprintf(RED_OUT, ")");
    }
  }
}
/* red_print_conj_break() */



void	red_print_line_break(d)
     struct red_type	*d;
{
  struct index_link_type	*pil, *pi_list, *xil, *xi_list;
  struct red_type		*result;
  int				ci;

  if (VAR[d->var_index].TYPE == TYPE_FALSE)
    fprintf(RED_OUT, "FALSE");
  else if (VAR[d->var_index].TYPE == TYPE_TRUE)
    fprintf(RED_OUT, "TRUE");
  else if (VAR[d->var_index].TYPE == TYPE_BDD) { 
    if (d->u.bdd.zero_child == d->u.bdd.one_child) { 
      fprintf(RED_OUT, "Error: Something wrong, both children of a bdd node are the same.\n"); 
      exit(0); 
    } 
    else if (d->u.bdd.zero_child == NORM_FALSE) {
      fprintf(RED_OUT, "%s", VAR[d->var_index].NAME); 
      if (d->u.bdd.one_child != NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "&&("); 
        red_print_line_break(d->u.bdd.one_child); 
        fprintf(RED_OUT, ")"); 
      } 
    }
    else if (d->u.bdd.one_child == NORM_FALSE) { 
      fprintf(RED_OUT, "(not %s)", VAR[d->var_index].NAME); 
      if (d->u.bdd.zero_child != NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "&&("); 
        red_print_line_break(d->u.bdd.zero_child); 
        fprintf(RED_OUT, ")"); 
      } 
    } 
    else { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "(not %s)", VAR[d->var_index].NAME); 
      } 
      else { 
        fprintf(RED_OUT, "((not %s)&&(", VAR[d->var_index].NAME); 
        red_print_line_break(d->u.bdd.zero_child); 
        fprintf(RED_OUT, "))"); 
      } 
      fprintf(RED_OUT, "||"); 
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION) { 
        fprintf(RED_OUT, "%s", VAR[d->var_index].NAME); 
      } 
      else { 
        fprintf(RED_OUT, "(%s&&(", VAR[d->var_index].NAME); 
         red_print_line_break(d->u.bdd.one_child); 
        fprintf(RED_OUT, "))"); 
      } 
    } 
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->u.crd.child_count == 1) {
          red_print_ineq(d, d->u.crd.arc[0].upper_bound);
      if (d->u.crd.arc[0].child != NORM_NO_RESTRICTION) {
	if (d->u.crd.arc[0].upper_bound != CLOCK_POS_INFINITY)
	  fprintf(RED_OUT, " && ");
	red_print_line_break(d->u.crd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj_break(d, 0);
      for (ci = 1; ci < d->u.crd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj_break(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_HRD:
    if (d->u.hrd.child_count == 1) {
      red_print_hybrid_ineq(d, d->u.hrd.arc[0].ub_numerator, d->u.hrd.arc[0].ub_denominator);
      if (d->u.hrd.arc[0].child != NORM_NO_RESTRICTION) {
        fprintf(RED_OUT, " && ");
	red_print_line_break(d->u.hrd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj_break(d, 0);
      for (ci = 1; ci < d->u.hrd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj_break(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break;
  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "(((~("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, "))&&("); 
    red_print_line(d->u.lazy.false_child); 
    fprintf(RED_OUT, "))||(("); 
    print_parse_subformula(d->u.lazy.exp, VAR[d->var_index].PROC_INDEX); 
    fprintf(RED_OUT, ")&&("); 
    red_print_line(d->u.lazy.true_child); 
    fprintf(RED_OUT, ")))");     
    break; 

  case TYPE_FLOAT:
    if (d->u.fdd.child_count == 1) {
      red_print_fatom(d, d->u.fdd.arc[0].lower_bound, d->u.fdd.arc[0].upper_bound);
      if (d->u.fdd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line_break(d->u.fdd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj_break(d, 0);
      for (ci = 1; ci < d->u.fdd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj_break(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break; 

  case TYPE_DOUBLE:
    if (d->u.dfdd.child_count == 1) {
      red_print_datom(d, d->u.dfdd.arc[0].lower_bound, d->u.dfdd.arc[0].upper_bound);
      if (d->u.dfdd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line_break(d->u.dfdd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj_break(d, 0);
      for (ci = 1; ci < d->u.dfdd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj_break(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
    break; 

  default:
    if (d->u.ddd.child_count == 1) {
      if (VAR[d->var_index].STATUS & FLAG_MODE)
	fprintf(RED_OUT, "\n");
      red_print_atom(d, d->u.ddd.arc[0].lower_bound, d->u.ddd.arc[0].upper_bound);
      if (d->u.ddd.arc[0].child != NORM_NO_RESTRICTION) {
	fprintf(RED_OUT, " && ");
	red_print_line_break(d->u.ddd.arc[0].child);
      }
    }
    else {
      fprintf(RED_OUT, "(");
      red_print_conj_break(d, 0);
      for (ci = 1; ci < d->u.ddd.child_count; ci++) {
        fprintf(RED_OUT, " || ");
        red_print_conj_break(d, ci);
      }
      fprintf(RED_OUT, ")");
    }
  }
}
/* red_print_line_break() */







/* The following procedures are for printing the lengthy tree-like representations 
 * of BDD-like diagrams. 
 */ 



char	buffer[256]; 

char	*extract_local_name(s)
     char	*s; 
{
  int	i; 

  for (i = 0; i < strlen(s) && s[i] != '\0' && s[i] != '['; i++) 
    buffer[i] = s[i]; 

  buffer[i] = '\0'; 

  return(buffer); 
}
/* extract_local_name() */ 



struct red_type	*bdd_atom(
  int	vid, 
  int	value
) {
  struct red_type	*d; 
  
  switch (VAR[vid].TYPE) { 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    break; 
  default: 
    fprintf(RED_OUT, "Error: A clock inequality in ddd_atom(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }
  d = red_alloc(vid); 
  if (value == TYPE_FALSE) { 
    d->u.bdd.zero_child = NORM_NO_RESTRICTION; 
    d->u.bdd.one_child = NORM_FALSE; 
  } 
  else { 
    d->u.bdd.zero_child = NORM_FALSE; 
    d->u.bdd.one_child = NORM_NO_RESTRICTION; 
  } 
  return(red_share(d)); 
}
  /* bdd_atom() */ 
  
  
struct red_type	*ddd_atom(
  int	vid, 
  int	lb, 
  int	ub 
) {
  struct red_type	*d; 
  int			flag; 
  struct ddd_child_type	*mic, *pic; 

  /* This is for the catching of type bug at transition */ 
  switch (VAR[vid].TYPE) { 
  case TYPE_FALSE: 
  case TYPE_TRUE: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_HDD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "Error: A clock inequality in ddd_atom(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }
 
  check_interval(vid, lb, ub); 
    
  if (lb <= VAR[vid].U.DISC.LB && ub >= VAR[vid].U.DISC.UB) {
    return(NORM_NO_RESTRICTION); 
  } 
    
  if (ub >= VAR[vid].U.DISC.UB) 
    ub = VAR[vid].U.DISC.UB; 
    
  if (lb <= VAR[vid].U.DISC.LB) 
    lb = VAR[vid].U.DISC.LB; 
    
  d = red_alloc(vid); 
  d->u.ddd.child_count = 1; 
  d->u.ddd.arc = (struct ddd_child_type *) malloc(sizeof(struct ddd_child_type)); 
  d->u.ddd.arc[0].lower_bound = lb; 
  d->u.ddd.arc[0].upper_bound = ub; 
  d->u.ddd.arc[0].child = NORM_NO_RESTRICTION; 

  ichild_count = ichild_count + d->u.ddd.child_count; 

  return (red_share(d));
}
  /* ddd_atom() */






struct red_type	*fdd_atom( 
	int	vid,  
	float 	lb, 
	float	ub 
) {
  struct red_type	*d; 
  int			flag; 
  struct fdd_child_type	*mic, *pic; 

  /* This is for the catching of type bug at transition */ 
  switch (VAR[vid].TYPE) { 
  case TYPE_FLOAT: 
    break; 
  default: 
    if (vid == FLOAT_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: An incompatible atom in fdd_atom(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }
 
  if (lb <= VAR[vid].U.FLT.LB && ub >= VAR[vid].U.FLT.UB) {
    return(NORM_NO_RESTRICTION); 
  } 
    
  if (ub >= VAR[vid].U.FLT.UB) 
    ub = VAR[vid].U.FLT.UB; 
    
  if (lb <= VAR[vid].U.FLT.LB) 
    lb = VAR[vid].U.FLT.LB; 
    
  d = red_alloc(vid); 
  d->u.fdd.child_count = 1; 
  d->u.fdd.arc = (struct fdd_child_type *) malloc(sizeof(struct fdd_child_type)); 
  d->u.fdd.arc[0].lower_bound = lb; 
  d->u.fdd.arc[0].upper_bound = ub; 
  d->u.fdd.arc[0].child = NORM_NO_RESTRICTION; 

  fchild_count = fchild_count + d->u.fdd.child_count; 

  return (red_share(d));
}
  /* fdd_atom() */




struct red_type	*dfdd_atom(
	int	vid,   
	double	lb, 
	double 	ub 
) {
  struct red_type	*d; 
  int			flag; 
  struct dfdd_child_type	*mic, *pic; 

  /* This is for the catching of type bug at transition */ 
  switch (VAR[vid].TYPE) { 
  case TYPE_DOUBLE: 
    break; 
  default: 
    if (vid == DOUBLE_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: An incompatible atom in dfdd_atom(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }
 
  if (lb <= VAR[vid].U.DBLE.LB && ub >= VAR[vid].U.DBLE.UB) {
    return(NORM_NO_RESTRICTION); 
  } 
    
  if (ub >= VAR[vid].U.DBLE.UB) 
    ub = VAR[vid].U.DBLE.UB; 
    
  if (lb <= VAR[vid].U.DBLE.LB) 
    lb = VAR[vid].U.DBLE.LB; 
    
  d = red_alloc(vid); 
  d->u.dfdd.child_count = 1; 
  d->u.dfdd.arc = (struct dfdd_child_type *) malloc(sizeof(struct dfdd_child_type)); 
  d->u.dfdd.arc[0].lower_bound = lb; 
  d->u.dfdd.arc[0].upper_bound = ub; 
  d->u.dfdd.arc[0].child = NORM_NO_RESTRICTION; 

  dfchild_count = dfchild_count + d->u.fdd.child_count; 

  return (red_share(d));
}
  /* dfdd_atom() */






struct red_type	*bdd_lone_subtree(child, vid, value)
     struct red_type	*child;
     int		vid, value;
{
  struct ddd_child_type	*mic, *pic; 
  struct red_type	*d; 
  
  /* This is for the catching of type bug at transition */
  switch (VAR[vid].TYPE) { 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    break; 
  default: 
    fprintf(RED_OUT, 
      "Error: An unexpected variable in bdd_lone_subtree(vid=%1d)\n", 
      vid 
    );
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  if (child != NORM_FALSE && child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "Error: Interval lone subtree violating variable-ordering.\n");
    fflush(RED_OUT); 
    for (value = TYPE_TRUE; value; );
  }

  if (child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "\nWrong variable ordering in ddd_lone_subtree() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  d = red_alloc(vid); 
  if (value == TYPE_FALSE) { 
    d->u.bdd.zero_child = child; 
    d->u.bdd.one_child = NORM_FALSE; 
  } 
  else { 
    d->u.bdd.zero_child = NORM_FALSE; 
    d->u.bdd.one_child = child; 
  } 
  return(red_share(d)); 
}
/* bdd_lone_subtree() */ 



struct red_type	*ddd_lone_subtree(child, vid, lb, ub)
     struct red_type	*child;
     int		vid, lb, ub;
{
  struct ddd_child_type	*mic, *pic; 
  struct red_type	*d; 
  
  /* This is for the catching of type bug at transition */
  switch (VAR[vid].TYPE) { 
  case TYPE_FALSE: 
  case TYPE_TRUE: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_HDD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "Error: A dense inequality in ddd_lone_subtree(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  if (child != NORM_FALSE && child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "Error: Interval lone subtree violating variable-ordering.\n");
    fflush(RED_OUT); 
    for (lb = TYPE_TRUE; lb; );
  }

  if (vid == TYPE_FALSE || child == NORM_FALSE)
    return(NORM_FALSE); 
  else if (vid == TYPE_TRUE)
    return(NORM_TRUE); 
  else if (child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "\nWrong variable ordering in ddd_lone_subtree() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  else {
    check_interval(vid, lb, ub);
     
    if (lb <= VAR[vid].U.DISC.LB && ub >= VAR[vid].U.DISC.UB) {
      return(child); 
    }
    if (ub >= VAR[vid].U.DISC.UB) 
      ub = VAR[vid].U.DISC.UB; 

    if (lb <= VAR[vid].U.DISC.LB) 
      lb = VAR[vid].U.DISC.LB; 

    d = red_alloc(vid); 
    d->u.ddd.child_count = 1; 
    d->u.ddd.arc = (struct ddd_child_type *) malloc(sizeof(struct ddd_child_type)); 
    d->u.ddd.arc[0].lower_bound = lb; 
    d->u.ddd.arc[0].upper_bound = ub; 
    d->u.ddd.arc[0].child = child; 
    ichild_count = ichild_count + d->u.ddd.child_count; 
    if (child->status & FLAG_RED_LAZY) 
      d->status = d->status | FLAG_RED_LAZY; 
    return (red_share(d)); 
  }

}
/* ddd_lone_subtree() */ 



struct red_type	*fdd_lone_subtree( 
     struct red_type	*child, 
     int		vid,  
     float 		lb, 
     float		ub
) {
  struct fdd_child_type	*mic, *pic; 
  struct red_type	*d; 
  
  /* This is for the catching of type bug at transition */
  switch (VAR[vid].TYPE) { 
  case TYPE_FLOAT: 
    break; 
  default: 
    if (vid == FLOAT_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: An illegal atom in fdd_lone_subtree(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  if (child != NORM_FALSE && child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "Error: Interval lone subtree violating variable-ordering.\n");
    fflush(RED_OUT); 
    for (d = NORM_NO_RESTRICTION; d; );
  }

  if (vid == TYPE_FALSE || child == NORM_FALSE)
    return(NORM_FALSE); 
  else if (vid == TYPE_TRUE)
    return(NORM_TRUE); 
  else if (child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "\nWrong variable ordering in fdd_lone_subtree() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  else {
    if (lb <= VAR[vid].U.FLT.LB && ub >= VAR[vid].U.FLT.UB) {
      return(child); 
    }
    if (ub >= VAR[vid].U.FLT.UB) 
      ub = VAR[vid].U.FLT.UB; 

    if (lb <= VAR[vid].U.FLT.LB) 
      lb = VAR[vid].U.FLT.LB; 

    d = red_alloc(vid); 
    d->u.fdd.child_count = 1; 
    d->u.fdd.arc = (struct fdd_child_type *) malloc(sizeof(struct fdd_child_type)); 
    d->u.fdd.arc[0].lower_bound = lb; 
    d->u.fdd.arc[0].upper_bound = ub; 
    d->u.fdd.arc[0].child = child; 
    fchild_count = fchild_count + d->u.fdd.child_count; 
    if (child->status & FLAG_RED_LAZY) 
      d->status = d->status | FLAG_RED_LAZY; 
    return (red_share(d)); 
  }

}
/* fdd_lone_subtree() */ 



struct red_type	*dfdd_lone_subtree( 
  struct red_type	*child, 
  int			vid,  
  double 		lb, 
  double		ub
) {
  struct dfdd_child_type	*mic, *pic; 
  struct red_type	*d; 
  
  /* This is for the catching of type bug at transition */
  switch (VAR[vid].TYPE) { 
  case TYPE_DOUBLE: 
    break; 
  default: 
    if (vid == DOUBLE_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: An illegal atom in dfdd_lone_subtree(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  if (child != NORM_FALSE && child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "Error: Interval lone subtree violating variable-ordering.\n");
    fflush(RED_OUT); 
    for (d = NORM_NO_RESTRICTION; d; );
  }

  if (vid == TYPE_FALSE || child == NORM_FALSE)
    return(NORM_FALSE); 
  else if (vid == TYPE_TRUE)
    return(NORM_TRUE); 
  else if (child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "\nWrong variable ordering in fdd_lone_subtree() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  else {
    if (lb <= VAR[vid].U.DBLE.LB && ub >= VAR[vid].U.DBLE.UB) {
      return(child); 
    }
    if (ub >= VAR[vid].U.DBLE.UB) 
      ub = VAR[vid].U.DBLE.UB; 

    if (lb <= VAR[vid].U.DBLE.LB) 
      lb = VAR[vid].U.DBLE.LB; 

    d = red_alloc(vid); 
    d->u.dfdd.child_count = 1; 
    d->u.dfdd.arc = (struct dfdd_child_type *) malloc(sizeof(struct dfdd_child_type)); 
    d->u.dfdd.arc[0].lower_bound = lb; 
    d->u.dfdd.arc[0].upper_bound = ub; 
    d->u.dfdd.arc[0].child = child; 
    dfchild_count = dfchild_count + d->u.dfdd.child_count; 
    if (child->status & FLAG_RED_LAZY) 
      d->status = d->status | FLAG_RED_LAZY; 
    return (red_share(d)); 
  }

}
/* dfdd_lone_subtree() */ 



struct red_type	*crd_atom(vid, ub)
     	int	vid, ub; 
{
  struct ddd_child_type	*mic, *pic; 
  struct red_type	*d; 
  
  if (VAR[vid].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, 
      "Errr: A non clock inequality in red_ineq(vid=%1d:%s)\n", 
      vid, VAR[vid].NAME
    ); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
 
  if (VAR[vid].U.CRD.CLOCK1 == VAR[vid].U.CRD.CLOCK2) {
    if (ub < 0)
      return(NORM_FALSE); 
    else 
      return(NORM_NO_RESTRICTION); 
  } 
  else if (   ub >= CLOCK_POS_INFINITY
           && VAR[vid].U.CRD.CLOCK1 != TIME 
           ) {
    return(NORM_NO_RESTRICTION); 
  }
  else if (   ub < CLOCK_NEG_INFINITY
           && VAR[vid].U.CRD.CLOCK2 != TIME 
           ) {
    ub = CLOCK_NEG_INFINITY; 
  }
  
  d = red_alloc(vid); 
  /*
    lb = ub; 
  */
  d->u.crd.child_count = 1; 
  d->u.crd.arc = (struct crd_child_type *) 
    malloc(sizeof(struct crd_child_type)); 
  bchild_count = bchild_count + d->u.crd.child_count; 
  d->u.crd.arc[0].upper_bound = ub; 
  d->u.crd.arc[0].child = NORM_TRUE;
      
  return (red_share(d)); 
}
  /* crd_atom() */ 








struct red_type	*crd_lone_subtree(child, vid, ub)
     struct red_type	*child;
     int		vid, ub;
{
  struct ddd_child_type	*mic, *pic;
  struct red_type 	*d; 
  
  if (VAR[vid].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "Error: A non clock inequality in red_lone_ineq_subtree(vid=%1d)\n", vid);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (child != NORM_FALSE && child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "Error: Zone lone subtree violating variable-ordering.\n");
    fflush(RED_OUT);
    for (ub = TYPE_TRUE; ub; );
  }

  if (child == NORM_FALSE) {
    return(NORM_FALSE);
  } 
  else if (child != NORM_NO_RESTRICTION && vid >= child->var_index) {
    fprintf(RED_OUT, "\nWrong variable ordering in crd_lone_subtree() \n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }

  if (VAR[vid].U.CRD.CLOCK1 == VAR[vid].U.CRD.CLOCK2) {
    if (ub < 0) 
      return(NORM_FALSE); 
    else 
      return(child); 
  } 
  else if (   ub >= CLOCK_POS_INFINITY
           && VAR[vid].U.CRD.CLOCK1 != TIME 
           ) {
    return(child); 
  } 
  else if (   ub < CLOCK_NEG_INFINITY 
           && VAR[vid].U.CRD.CLOCK2 != TIME 
           ) {
    ub = CLOCK_NEG_INFINITY; 
  }

  d = red_alloc(vid); 
  d->u.crd.child_count = 1; 
  d->u.crd.arc = (struct crd_child_type *) malloc(sizeof(struct crd_child_type)); 
  bchild_count = bchild_count + d->u.crd.child_count; 
  d->u.crd.arc[0].upper_bound = ub; 
  d->u.crd.arc[0].child = child; 
    
  if (child->status & FLAG_RED_LAZY) 
    d->status = d->status | FLAG_RED_LAZY; 
  return(red_share(d)); 
}
/* crd_lone_subtree() */ 





/**************************************************************************
 *
 */

struct red_type	*red_bop();

void	expand_child_stack() { 
  struct child_stack_frame_type	*new_cs; 
  int				i; 
  
  new_cs = (struct child_stack_frame_type *) 
    malloc(2*HEIGHT_CHILD_STACK*sizeof(struct child_stack_frame_type)); 
  for (i = 0; i < HEIGHT_CHILD_STACK; i++) { 
    new_cs[i] = CHILD_STACK[i]; 	
  } 
  HEIGHT_CHILD_STACK = 2*HEIGHT_CHILD_STACK; 
  free(CHILD_STACK); 
  CHILD_STACK = new_cs; 
} 
  /* expand_child_stack() */ 



void	expand_level_child_stack() { 
  int	*new_cs, i; 
  
  new_cs = (int *) malloc(2*HEIGHT_LEVEL_CHILD_STACK*sizeof(int)); 
  for (i = 0; i < HEIGHT_LEVEL_CHILD_STACK; i++) { 
    new_cs[i] = LEVEL_CHILD_COUNT[i]; 	
  } 
  HEIGHT_LEVEL_CHILD_STACK = 2*HEIGHT_LEVEL_CHILD_STACK; 
  free(LEVEL_CHILD_COUNT); 
  LEVEL_CHILD_COUNT = new_cs; 
} 
  /* expand_level_child_stack() */ 



int	count_complex_ichild_stack_push = 0; 

void	ichild_stack_push(d, lb, ub)
     struct red_type	*d;
     int		lb, ub;
{
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", (unsigned int) ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK >= 0
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK 
      && ub == CHILD_STACK[TOP_CHILD_STACK].u.disc.lb - 1
      && d == CHILD_STACK[TOP_CHILD_STACK].d
      ) {  
    CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = lb; 
    return; 
  }

  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = lb; 
  CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* ichild_stack_push() */




void	ichild_stack_checkpush(d, lb, ub)
     struct red_type	*d;
     int		lb, ub;
{
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK < 0
      || CHILD_STACK[TOP_CHILD_STACK].level != TOP_LEVEL_CHILD_STACK 
      || ub < CHILD_STACK[TOP_CHILD_STACK].u.disc.lb - 1
      ) {
    child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
    CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
    CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = lb; 
    CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
  }
  else if (ub == CHILD_STACK[TOP_CHILD_STACK].u.disc.lb - 1) { 
    if (d == CHILD_STACK[TOP_CHILD_STACK].d) {  
      if (CHILD_STACK[TOP_CHILD_STACK].u.disc.lb > lb) 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = lb; 
    }
    else { 
      child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++; 
      CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
      CHILD_STACK[TOP_CHILD_STACK].d = d; 
      CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = lb; 
      CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
    }
  }
  else if (ub > CHILD_STACK[TOP_CHILD_STACK].u.disc.ub) { 
    fprintf(RED_OUT, "ERROR: An overlap variable range for discrete variables. \n"); 
    bk(0); 
  } 
  else { 
    int	nub, nlb, flag_top_not_used; 
    struct red_type	*dtop; 

    fprintf(RED_OUT, "complex ichild stack push: %1d\n", 
            ++count_complex_ichild_stack_push
            ); 

    dtop = CHILD_STACK[TOP_CHILD_STACK].d; 
    // for interval [ub+1, CHILD_STACK[TOP_CHILD_STACK].ub]. 
    flag_top_not_used = 1; 
    nub = CHILD_STACK[TOP_CHILD_STACK].u.disc.ub; // This is to check whether the 
    nlb = ub+1; // new interval is to the end of the orginal ones. 
    if (nlb <= nub) { 
      CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = nlb; 
      flag_top_not_used = 0; 
    }
    
    if (lb <= CHILD_STACK[TOP_CHILD_STACK].u.disc.lb) {
      // for [CHILD_STACK[TOP_CHILD_STACK].lb, ub]. 
      nub = ub; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.disc.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = nub; 
      } 
      // for [lb, CHILD_STACK[TOP_CHILD_STACK].lb-1].  
      nub = CHILD_STACK[TOP_CHILD_STACK].u.disc.lb-1; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = d; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = nub; 
      } 
    } 
    else /* (lb > CHILD_STACK[TOP_CHILD_STACK].lb) */ { 
      int		nub, nlb, flag_top_not_used; 
      struct red_type	*tmp, *dtop; 
      
      // for [lb, ub]. 
      nub = ub; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        tmp = d; 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = nub; 
      } 
      // for [CHILD_STACK[TOP_CHILD_STACK].lb, lb-1].  
      nub = lb-1; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.disc.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = tmp; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.disc.ub = nub; 
      } 
    } 
  } 
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* ichild_stack_checkpush() */





void	fchild_stack_push( 
  struct red_type	*d, 
  float			lb, 
  float			ub 
) {
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", (unsigned int) ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK >= 0
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK 
      && ub >= CHILD_STACK[TOP_CHILD_STACK].u.flt.lb
      && d == CHILD_STACK[TOP_CHILD_STACK].d
      ) {  
    CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = lb; 
    return; 
  }

  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = lb; 
  CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* fchild_stack_push() */




void	fchild_stack_checkpush( 
  struct red_type	*d, 
  float			lb, 
  float			ub 
) {
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK < 0
      || CHILD_STACK[TOP_CHILD_STACK].level != TOP_LEVEL_CHILD_STACK 
      || ub < CHILD_STACK[TOP_CHILD_STACK].u.flt.lb 
      ) {
    child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
    CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
    CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = lb; 
    CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
  }
  else if (ub >= CHILD_STACK[TOP_CHILD_STACK].u.flt.lb) { 
    if (d == CHILD_STACK[TOP_CHILD_STACK].d) {  
      if (CHILD_STACK[TOP_CHILD_STACK].u.flt.lb > lb) 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = lb; 
    }
    else { 
      child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++; 
      CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
      CHILD_STACK[TOP_CHILD_STACK].d = d; 
      CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = lb; 
      CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%G, ub:%G\n", nic, lb, ub);
    fflush(RED_OUT);
*/
    }
  }
  else if (ub > CHILD_STACK[TOP_CHILD_STACK].u.flt.ub) { 
    fprintf(RED_OUT, "ERROR: An overlap variable range for discrete variables. \n"); 
    bk(0); 
  } 
  else { 
    float		nub, nlb; 
    int			flag_top_not_used; 
    struct red_type	*dtop; 

    fprintf(RED_OUT, "complex fchild stack push: %1d\n", 
            ++count_complex_ichild_stack_push
            ); 

    dtop = CHILD_STACK[TOP_CHILD_STACK].d; 
    // for interval [ub+1, CHILD_STACK[TOP_CHILD_STACK].ub]. 
    flag_top_not_used = 1; 
    
    // We first see if [lb,ub] dissects the last interval. 
    nub = CHILD_STACK[TOP_CHILD_STACK].u.flt.ub; 
    nlb = feps_plus(ub); 
    if (nlb <= nub) { 
      CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = nlb; 
      flag_top_not_used = 0; 
    }
    
    if (lb <= CHILD_STACK[TOP_CHILD_STACK].u.flt.lb) {
      // for [CHILD_STACK[TOP_CHILD_STACK].u.flt.lb, ub]. 
      nub = ub; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.flt.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = nub; 
      } 
      // for [lb, CHILD_STACK[TOP_CHILD_STACK].lb-1].  
      nub = CHILD_STACK[TOP_CHILD_STACK].u.flt.lb-1; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = d; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = nub; 
      } 
    } 
    else /* (lb > CHILD_STACK[TOP_CHILD_STACK].lb) */ { 
      float		nub, nlb; 
      int		flag_top_not_used; 
      struct red_type	*tmp, *dtop; 
      
      // for [lb, ub]. 
      nub = ub; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        tmp = d; 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = nub; 
      } 
      // for [CHILD_STACK[TOP_CHILD_STACK].lb, lb-1].  
      nub = lb-1; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.flt.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = tmp; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.flt.ub = nub; 
      } 
    } 
  } 
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* fchild_stack_checkpush() */




void	dfchild_stack_push( 
  struct red_type	*d, 
  double		lb, 
  double		ub
) {
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", (unsigned int) ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK >= 0
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK 
      && ub >= CHILD_STACK[TOP_CHILD_STACK].u.dble.lb
      && d == CHILD_STACK[TOP_CHILD_STACK].d
      ) {  
    CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = lb; 
    return; 
  }

  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = lb; 
  CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* dfchild_stack_push() */




void	dfchild_stack_checkpush( 
  struct red_type	*d, 
  double		lb, 
  double		ub 
) {
  if (d == NORM_FALSE)
    return;
/*
  fprintf(RED_OUT, "ic_stack_push, a:%x\n", ic_stack);
  fflush(RED_OUT);
*/
  if (   TOP_CHILD_STACK < 0
      || CHILD_STACK[TOP_CHILD_STACK].level != TOP_LEVEL_CHILD_STACK 
      || ub < CHILD_STACK[TOP_CHILD_STACK].u.dble.lb 
      ) {
    child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
    CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
    CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = lb; 
    CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%1d, ub:%1d\n", nic, lb, ub);
    fflush(RED_OUT);
*/
  }
  else if (ub >= CHILD_STACK[TOP_CHILD_STACK].u.dble.lb) { 
    if (d == CHILD_STACK[TOP_CHILD_STACK].d) {  
      if (CHILD_STACK[TOP_CHILD_STACK].u.dble.lb > lb) 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = lb; 
    }
    else { 
      child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++; 
      CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
      CHILD_STACK[TOP_CHILD_STACK].d = d; 
      CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = lb; 
      CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = ub; 
/*
    fprintf(RED_OUT, "ic_stack_push, b:nic:%x, lb:%G, ub:%G\n", nic, lb, ub);
    fflush(RED_OUT);
*/
    }
  }
  else if (ub > CHILD_STACK[TOP_CHILD_STACK].u.dble.ub) { 
    fprintf(RED_OUT, "ERROR: An overlap variable range for discrete variables. \n"); 
    bk(0); 
  } 
  else { 
    double		nub, nlb; 
    int			flag_top_not_used; 
    struct red_type	*dtop; 

    fprintf(RED_OUT, "complex fchild stack push: %1d\n", 
            ++count_complex_ichild_stack_push
            ); 

    dtop = CHILD_STACK[TOP_CHILD_STACK].d; 
    // for interval [ub+1, CHILD_STACK[TOP_CHILD_STACK].ub]. 
    flag_top_not_used = 1; 
    
    // We first see if [lb,ub] dissects the last interval. 
    nub = CHILD_STACK[TOP_CHILD_STACK].u.dble.ub; 
    nlb = dfeps_plus(ub); 
    if (nlb <= nub) { 
      CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = nlb; 
      flag_top_not_used = 0; 
    }
    
    if (lb <= CHILD_STACK[TOP_CHILD_STACK].u.dble.lb) {
      // for [CHILD_STACK[TOP_CHILD_STACK].u.dble.lb, ub]. 
      nub = ub; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.dble.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = nub; 
      } 
      // for [lb, CHILD_STACK[TOP_CHILD_STACK].u.dble.lb-1].  
      nub = CHILD_STACK[TOP_CHILD_STACK].u.dble.lb-1; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = d; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = nub; 
      } 
    } 
    else /* (lb > CHILD_STACK[TOP_CHILD_STACK].lb) */ { 
      double		nub, nlb; 
      int		flag_top_not_used; 
      struct red_type	*tmp, *dtop; 
      
      // for [lb, ub]. 
      nub = ub; 
      nlb = lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        tmp = d; 
        CHILD_STACK[TOP_CHILD_STACK].d = red_bop(OR, d, dtop); 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = nub; 
      } 
      // for [CHILD_STACK[TOP_CHILD_STACK].lb, lb-1].  
      nub = lb-1; 
      nlb = CHILD_STACK[TOP_CHILD_STACK].u.dble.lb; 
      if (nlb <= nub) { 
        if (flag_top_not_used) 
          flag_top_not_used = 0; 
        else 
          child_stack_epush(); 
        CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
        // This is assuming that an OR cannot be used in an OR that 
        // triggers this part of the code. 
        // TS_OR will be polluted. 
        // 
        CHILD_STACK[TOP_CHILD_STACK].d = tmp; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.lb = nlb; 
        CHILD_STACK[TOP_CHILD_STACK].u.dble.ub = nub; 
      } 
    } 
  } 
/*
    fprintf(RED_OUT, "ic_stack_push, b:lb%1d\n", lb);
    fflush(RED_OUT);
*/
/*
  fprintf(RED_OUT, "ic_stack_push: c:\n");
  fflush(RED_OUT);
*/
}
/* dfchild_stack_checkpush() */






void	bchild_stack_push(
     struct red_type	*d, 
     int		ub 
) {
  int	i;

  /*
  if (ub > CLOCK_POS_INFINITY) {
    fprintf(RED_OUT, "\nError: overbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub < CLOCK_NEG_INFINITY) {
    fprintf(RED_OUT, "\nError: underbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  if (d == NORM_FALSE)
    return;

  for (i = TOP_CHILD_STACK; 
       i >= 0 && CHILD_STACK[i].level == TOP_LEVEL_CHILD_STACK; 
       i--
       ) 
    if (d == CHILD_STACK[i].d) 
      return;

  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++; 
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.crd.ub = ub; 
  
  return;
}
  /* bchild_stack_push() */






/* This is routine is basically like bchild_stack_push except that
   it checks for and eliminate simple binary negative cycles.
*/
void	bchild_stack_restrict(
  int			evi, 
  struct red_type	*d, 
  int			b
) {
  if (   d == NORM_FALSE
      || (   TOP_CHILD_STACK >= 0 
          && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK
          && CHILD_STACK[TOP_CHILD_STACK].d == d 
          && b <= CHILD_STACK[TOP_CHILD_STACK].u.crd.ub
          )
      )
    return;

  if (evi == d->var_index) {
    /* Simple binary negative cycles can happen. */
    if (   b == CLOCK_NEG_INFINITY 
        && VAR[evi].U.CRD.CLOCK1 != TIME
        ) {
      if (d->u.crd.arc[d->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
	d = d->u.crd.arc[d->u.crd.child_count-1].child;
      else
	return;
    }
    else {
      if (VAR[evi].U.CRD.CLOCK1 == TIME) 
        d = zone_extract_interval(d, evi, -1*b, HYBRID_POS_INFINITY);
      else 
        d = zone_extract_interval(d, evi, -1*b, CLOCK_POS_INFINITY);
      if (d == NORM_FALSE)
	return;
    }
  }

  if (   TOP_CHILD_STACK >= 0 
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK
      && CHILD_STACK[TOP_CHILD_STACK].u.crd.ub == b
      ) {
    CHILD_STACK[TOP_CHILD_STACK].d 
    = red_bop(OR, d, CHILD_STACK[TOP_CHILD_STACK].d);
  }
  else {
    child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
    CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
    CHILD_STACK[TOP_CHILD_STACK].u.crd.ub = b; 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
  }
}
/* bchild_stack_restrict() */





void	bchild_stack_insert( 
  struct red_type	*d, 
  int			b 
) {
  int	p, i;

  if (d == NORM_FALSE)
    return;

  /* First, scan ic_stack to exclude from d and from ic_stack */
  for (p = -1, i = TOP_CHILD_STACK; 
          i >= 0 
       && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK; 
       i--
       ) { 
    if (CHILD_STACK[i].u.crd.ub > b) {
      if (p == -1) 
        p = i; // p is the position at or right after 
               // which the new element should be placed. 
      d = red_bop(EXCLUDE, d, CHILD_STACK[i].d);
      if (d == NORM_FALSE) 
        break; 
    }
    else if (CHILD_STACK[i].u.crd.ub == b) { 
      p = i; // p is the position at which the new element should be placed.
    } 
    else {
      CHILD_STACK[i].d = red_bop(EXCLUDE, CHILD_STACK[i].d, d);
      if (CHILD_STACK[i].d == NORM_FALSE) {
	LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]--;
      }
    }
  }

  if (p == -1) {
    p = i; // if all elements are with lower upper-bound, 
           // we simply let the end of the level child stack be the right 
           // after position.  
  } 
  else if (CHILD_STACK[p].u.crd.ub == b) { 
    // The bound is already there. 
    // So we can return soon. 
    CHILD_STACK[i].d = red_bop(OR, CHILD_STACK[i].d, d); 
    return; 
  } 
  
  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK;  
  for (i = TOP_CHILD_STACK; i > p; i--) { 
    CHILD_STACK[i].d = CHILD_STACK[i-1].d; 
    CHILD_STACK[i].u.crd.ub = CHILD_STACK[i-1].u.crd.ub; 
  } 
  p++; 
  CHILD_STACK[p].d = d; 
  CHILD_STACK[p].u.crd.ub = b; 
}
/* bchild_stack_insert() */


struct red_type	*red_exclude_with_reduction(); 

void	bchild_stack_checkpush( 
  struct red_type	*d, 
  int			b
) {
  int	i, flag;

  if (d == NORM_FALSE) {
    return;
  }

  for (i = TOP_CHILD_STACK; 
       i >= 0 && CHILD_STACK[i].level == TOP_LEVEL_CHILD_STACK; 
       i--
       ) {
    d = red_exclude_with_reduction(d, CHILD_STACK[i].d);
    if (d == NORM_FALSE)
      return;
  }

  child_stack_epush(); // LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.crd.ub = b; 
}
/* bchild_stack_checkpush() */





/************************************************************
 *
 */
advance_bchild(dx, dy, cix_ptr, ciy_ptr, unionx_ptr, uniony_ptr)
	struct red_type	*dx, *dy, **unionx_ptr, **uniony_ptr;
	int		*cix_ptr, *ciy_ptr;
{
  if (*cix_ptr < 0 || *ciy_ptr < 0) {
    *cix_ptr = -1;
    *ciy_ptr = -1;
  }
  else if (*cix_ptr == 0) {
    if (*ciy_ptr == 0) {
      *cix_ptr = -1;
      *ciy_ptr = -1;
    }
    else if (*ciy_ptr > 0) {
      (*ciy_ptr)--;
      *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.crd.arc[*ciy_ptr].child);
    }
  }
  else if (*ciy_ptr == 0) {
    if (*cix_ptr == 0) {
      *cix_ptr = -1;
      *ciy_ptr = -1;
    }
    else if (*cix_ptr > 0) {
      (*cix_ptr)--;
      *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.crd.arc[*cix_ptr].child);
    }
  }
  else {
    int	nix, niy, comp;

    nix = *cix_ptr - 1;
    niy = *ciy_ptr - 1;
    comp = dx->u.crd.arc[nix].upper_bound - dy->u.crd.arc[niy].upper_bound;
    if (comp <= 0) {
      *ciy_ptr = niy;
      *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.crd.arc[*ciy_ptr].child);
    }
    if (comp >= 0) {
      *cix_ptr = nix;
      *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.crd.arc[*cix_ptr].child);
    }
  }
}
  /* advance_hchild() */



advance_hchild(dx, dy, cix_ptr, ciy_ptr, unionx_ptr, uniony_ptr)
	struct red_type	*dx, *dy, **unionx_ptr, **uniony_ptr;
	int		*cix_ptr, *ciy_ptr;
{
  if (*cix_ptr < 0 || *ciy_ptr < 0) {
    *cix_ptr = -1;
    *ciy_ptr = -1;
  }
  else if (*cix_ptr == 0) {
    if (*ciy_ptr == 0) {
      *cix_ptr = -1;
      *ciy_ptr = -1;
    }
    else if (*ciy_ptr > 0) {
      (*ciy_ptr)--;
      *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.hrd.arc[*ciy_ptr].child);
    }
  }
  else if (*ciy_ptr == 0) {
    if (*cix_ptr == 0) {
      *cix_ptr = -1;
      *ciy_ptr = -1;
    }
    else if (*cix_ptr > 0) {
      (*cix_ptr)--;
      *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.hrd.arc[*cix_ptr].child);
    }
  }
  else {
    int	nix, niy;

    nix = *cix_ptr - 1;
    niy = *ciy_ptr - 1;
    if (   dx->u.hrd.arc[nix].ub_numerator == HYBRID_NEG_INFINITY
	&& dx->u.hrd.arc[nix].ub_denominator == 1
	)
      if (   dy->u.hrd.arc[niy].ub_numerator == HYBRID_NEG_INFINITY
	  && dy->u.hrd.arc[niy].ub_denominator == 1
	  ) {
	*cix_ptr = nix;
        *ciy_ptr = niy;
        *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.hrd.arc[*cix_ptr].child);
        *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.hrd.arc[*ciy_ptr].child);
      }
      else {
        *ciy_ptr = niy;
        *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.hrd.arc[*ciy_ptr].child);
      }
    else
      if (   dy->u.hrd.arc[niy].ub_numerator == HYBRID_NEG_INFINITY
	  && dy->u.hrd.arc[niy].ub_denominator == 1
	  ) {
	*cix_ptr = nix;
        *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.hrd.arc[*cix_ptr].child);
      }
      else {
        int	 comp;

	comp = dx->u.hrd.arc[nix].ub_numerator * dy->u.hrd.arc[niy].ub_denominator
	     - dy->u.hrd.arc[niy].ub_numerator * dx->u.hrd.arc[nix].ub_denominator;
        if (comp <= 0) {
	  *ciy_ptr = niy;
          *uniony_ptr = red_bop(OR, *uniony_ptr, dy->u.hrd.arc[*ciy_ptr].child);
	}
        if (comp >= 0) {
	  *cix_ptr = nix;
          *unionx_ptr = red_bop(OR, *unionx_ptr, dx->u.hrd.arc[*cix_ptr].child);
	}
      }
  }
}
  /* advance_hchild() */



advance_hfchild(dx, dy, cix_ptr, ciy_ptr, lb_n_ptr, lb_d_ptr, ub_n_ptr, ub_d_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr, *lb_n_ptr, *lb_d_ptr, *ub_n_ptr, *ub_d_ptr;
{
  int	lbx, ubx, lby, uby;
  int lbxn, lbxd, ubxn, ubxd;
  int lbyn, lbyd, ubyn, ubyd;

  /* This is for the catching of type bug at transition */
  if (   dx->var_index != dy->var_index 
      || VAR[dx->var_index].TYPE == TYPE_HRD
      ) {
    fprintf(RED_OUT, "\nError: type mismatch in advance_hfchild()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  for (; 
          *cix_ptr >= 0 
       && rational_comp(dx->u.hdd.arc[*cix_ptr].lb_numerator, 
			dx->u.hdd.arc[*cix_ptr].lb_denominator,
			*lb_n_ptr,
			*lb_d_ptr
			) >=0 ; 
       (*cix_ptr)--
       ) ;

  for (; 
          *ciy_ptr >= 0 
       && rational_comp(dy->u.hdd.arc[*ciy_ptr].lb_numerator, 
		        dy->u.hdd.arc[*ciy_ptr].lb_denominator, 
		        *lb_n_ptr,
		        *lb_d_ptr
		        ) >=0 ; 
       (*ciy_ptr)--
       ) ;

  if (*cix_ptr < 0) {
    if (*ciy_ptr >= 0) {
      if (rational_comp(*lb_n_ptr,
			*lb_d_ptr, 
			dy->u.hdd.arc[*ciy_ptr].ub_numerator, 
			dy->u.hdd.arc[*ciy_ptr].ub_denominator
			)>0
	  ) {
	*ub_n_ptr = dy->u.hdd.arc[*ciy_ptr].ub_numerator;
	*ub_d_ptr = dy->u.hdd.arc[*ciy_ptr].ub_denominator;
      }
      else {
	*ub_n_ptr = *lb_n_ptr - 1;
	*ub_d_ptr = *lb_d_ptr;					
      }
      *lb_n_ptr = dy->u.hdd.arc[*ciy_ptr].lb_numerator;
      *lb_d_ptr = dy->u.hdd.arc[*ciy_ptr].lb_denominator;     
			            
    }
  }
  else if (*ciy_ptr < 0) {
    if (rational_comp(*lb_n_ptr,
		      *lb_d_ptr,
		      dx->u.hdd.arc[*cix_ptr].ub_numerator, 
		      dx->u.hdd.arc[*cix_ptr].ub_denominator
		      )>0
	) {
      *ub_n_ptr = dx->u.hdd.arc[*cix_ptr].ub_numerator;
      *ub_d_ptr = dx->u.hdd.arc[*cix_ptr].ub_denominator;    	  
    }
    else {
      *ub_n_ptr = *lb_n_ptr - 1;
      *ub_d_ptr = *lb_d_ptr;      
    }
		    
    *lb_n_ptr = dx->u.hdd.arc[*cix_ptr].lb_numerator;
    *lb_d_ptr = dx->u.hdd.arc[*cix_ptr].lb_denominator;        
  }
  else {
    lbxn = dx->u.hdd.arc[*cix_ptr].lb_numerator; 
    lbxd = dx->u.hdd.arc[*cix_ptr].lb_denominator;
    ubxn = dx->u.hdd.arc[*cix_ptr].ub_numerator; 
    ubxd = dx->u.hdd.arc[*cix_ptr].ub_denominator;
    lbyn = dy->u.hdd.arc[*ciy_ptr].lb_numerator; 
    lbyd = dy->u.hdd.arc[*ciy_ptr].lb_denominator;
    ubyn = dy->u.hdd.arc[*ciy_ptr].ub_numerator; 
    ubyd = dy->u.hdd.arc[*ciy_ptr].ub_denominator;

    if (rational_comp(*lb_n_ptr,*lb_d_ptr,ubxn,ubxd)>0) /* ubx < lb */
      if (rational_comp(*lb_n_ptr,*lb_d_ptr,ubyn,ubyd)>0) /* ubx, uby < lb */ {
	if (rational_comp(ubyn,ubyd,ubxn,ubxd)>0) /* ubx < uby < lb */ {
	  if (rational_comp(ubxn,ubxd,lbyn,lbyd)>=0) /* lby <= ubx < uby < lb */ {
	    *lb_n_ptr = ubxn + 1;
	    *lb_d_ptr = ubxd; 
	  }
	  else /* ubx < lby < uby < lb */ {
	    *lb_n_ptr = lbyn;
	    *lb_d_ptr = lbyd;   	    			
	  }
	  
	  *ub_n_ptr = dy->u.hdd.arc[*ciy_ptr].ub_numerator;
	  *ub_d_ptr = dy->u.hdd.arc[*ciy_ptr].ub_denominator;    
	}
	else if (rational_comp(ubxn,ubxd,ubyn,ubyd)>0) /* uby < ubx < lb */ {
	  if (rational_comp(ubyn,ubyd,lbxn,lbxd)>=0) /* lbx <= uby < ubx < lb */ {	    	
	    *lb_n_ptr = dy->u.hdd.arc[*ciy_ptr].lb_numerator + 1;
	    *lb_d_ptr = dy->u.hdd.arc[*ciy_ptr].lb_denominator;    	    			
	  }
	  else /* uby < lbx < ubx < lb */ {	
	    *lb_n_ptr = dx->u.hdd.arc[*cix_ptr].lb_numerator;
	    *lb_d_ptr = dx->u.hdd.arc[*cix_ptr].lb_denominator;    	    			
	  }

	  *ub_n_ptr = dx->u.hdd.arc[*cix_ptr].ub_numerator;
	  *ub_d_ptr = dx->u.hdd.arc[*cix_ptr].ub_denominator;    
	}
	else /* ubx = uby < lb */ {
	  if (rational_comp(lbxn,lbxd,lbyn,lbyd)>0) /* lby < lbx <= ubx = uby < lb */ {
	    *lb_n_ptr = dx->u.hdd.arc[*cix_ptr].lb_numerator;
	    *lb_d_ptr = dx->u.hdd.arc[*cix_ptr].lb_denominator;    	    			
	  }
	  else /* lbx <= lby <= ubx = uby < lb */ {
	    *lb_n_ptr = dy->u.hdd.arc[*ciy_ptr].lb_numerator;
	    *lb_d_ptr = dy->u.hdd.arc[*ciy_ptr].lb_denominator;    	    			
	  }	
          *ub_n_ptr = dx->u.hdd.arc[*cix_ptr].ub_numerator;
          *ub_d_ptr = dx->u.hdd.arc[*cix_ptr].ub_denominator;    
        }
      }
      else /* ubx < lb <= uby */ {
        *ub_n_ptr = *lb_n_ptr - 1;
        *ub_d_ptr = *lb_d_ptr;    

        if (rational_comp(*lb_n_ptr-1,*lb_d_ptr,ubxn,ubxd)==0) /* lb -1 == ubx < lb <= uby */
          if (rational_comp(lbyn,lbyd,lbxn,lbxd)>0) 
          /* lbx < lby <= lb-1 == ubx < lb <= uby */ {
            *lb_n_ptr = lbyn;
            *lb_d_ptr = lbyd;    	    			
          }
          else /* lby <= lbx <= lb-1 == ubx < lb <= uby */ { 
            *lb_n_ptr = lbxn;
            *lb_d_ptr = lbxd;    	    			
          }
        else if (rational_comp(lbyn,lbyd,ubxn+1,ubxd)>0) /* ubx+1 < lby < lb <= uby */ {
          *lb_n_ptr = lbyn;
          *lb_d_ptr = lbyd;   	  			
        }
	else /* lby <= ubx+1 < lb <= uby */ {	  			
	  *lb_n_ptr = ubxn + 1;
	  *lb_d_ptr = ubxd;   
	}
      }
      else if (rational_comp(*lb_n_ptr,*lb_d_ptr,ubyn,ubyd)>0) /* uby < lb <= ubx */ {
	*ub_n_ptr = *lb_n_ptr - 1;
	*ub_d_ptr = *lb_d_ptr;

        if (rational_comp(*lb_n_ptr-1,*lb_d_ptr,ubyn,ubyd)==0) 
        /* lb-1 == uby < lb <= ubx */
	  if (rational_comp(lbxn,lbxd,lbyn,lbyd)>0) 
	  /* lby < lbx <= lb-1 == uby < lb <= ubx */ {
	    *lb_n_ptr = lbxn;
	    *lb_d_ptr = lbxd;   	  			
	  }
	  else /* lbx <= lby <= lb-1 == uby < lb <= ubx */ {
	    *lb_n_ptr = lbyn;
	    *lb_d_ptr = lbyd;   	  			
	  }
        else if (rational_comp(lbxn,lbxd,ubyn+1,ubyd)>0) /* uby+1 < lbx < lb = ubx */ {				
	  *lb_n_ptr = lbxn;
	  *lb_d_ptr = lbxd;   				
	}
        else /* lbx <= ubx+1 < lb <= uby */ {
	  *lb_n_ptr = ubyn + 1;
	  *lb_d_ptr = ubyd;   				
	}
      }
      else /* lb <= ubx, uby */ {
	*ub_n_ptr = *lb_n_ptr - 1;
	*ub_d_ptr = *lb_d_ptr;   
					
        if (rational_comp(lbyn,lbyd,lbxn,lbxd)>0) /* lbx < lby < lb <= ubx, uby */ {
	  *lb_n_ptr = lbyn;
	  *lb_d_ptr = lbyd;   				
	}
        else /* lby <= lbx < lb <= ubx, uby */ {				
	  *lb_n_ptr = lbxn;
	  *lb_d_ptr = lbxd;   
	}
      }
  }
}
/* advance_hfchild() */


void 	last_ichild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr, *lb_ptr, *ub_ptr;
{ 
  *cix_ptr = dx->u.ddd.child_count-1; 
  *ciy_ptr = dy->u.ddd.child_count-1; 
  *ub_ptr = int_max(
    dx->u.ddd.arc[*cix_ptr].upper_bound, 
    dy->u.ddd.arc[*ciy_ptr].upper_bound
  );  
  
  if (dx->u.ddd.arc[*cix_ptr].lower_bound 
      > dy->u.ddd.arc[*ciy_ptr].upper_bound
      ) 
    *lb_ptr = dx->u.ddd.arc[*cix_ptr].lower_bound; 
  else if (dy->u.ddd.arc[*ciy_ptr].lower_bound 
           > dx->u.ddd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = dy->u.ddd.arc[*ciy_ptr].lower_bound; 
  else if (dy->u.ddd.arc[*ciy_ptr].upper_bound 
           > dx->u.ddd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = dx->u.ddd.arc[*cix_ptr].upper_bound+1; 
  else if (dx->u.ddd.arc[*cix_ptr].upper_bound 
           > dy->u.ddd.arc[*ciy_ptr].upper_bound
           ) 
    *lb_ptr = dy->u.ddd.arc[*ciy_ptr].upper_bound+1; 
  else if (dx->u.ddd.arc[*cix_ptr].lower_bound 
           > dy->u.ddd.arc[*ciy_ptr].lower_bound
           ) 
    *lb_ptr = dx->u.ddd.arc[*cix_ptr].lower_bound; 
  else 
    *lb_ptr = dy->u.ddd.arc[*ciy_ptr].lower_bound; 
}
  /* last_ichild() */ 




void	advance_ichild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr, *lb_ptr, *ub_ptr;
{
  int	lbx, ubx, lby, uby;

  /* This is for the catching of type bug at transition */
  if (dx->var_index != dy->var_index || VAR[dx->var_index].TYPE == TYPE_CRD) {
    fprintf(RED_OUT, "\nError: type mismatch in advance_child()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  for (; 
       *cix_ptr >= 0 && dx->u.ddd.arc[*cix_ptr].lower_bound >= *lb_ptr; 
       (*cix_ptr)--
       ) ;

  for (; 
       *ciy_ptr >= 0 && dy->u.ddd.arc[*ciy_ptr].lower_bound >= *lb_ptr; 
       (*ciy_ptr)--
       ) ;

  if (*cix_ptr < 0) {
    if (*ciy_ptr >= 0) {
      if (*lb_ptr > dy->u.ddd.arc[*ciy_ptr].upper_bound)
	*ub_ptr = dy->u.ddd.arc[*ciy_ptr].upper_bound;
      else
	*ub_ptr = *lb_ptr - 1;

      *lb_ptr = dy->u.ddd.arc[*ciy_ptr].lower_bound;
    }
  }
  else if (*ciy_ptr < 0) {
    if (*lb_ptr > dx->u.ddd.arc[*cix_ptr].upper_bound)
      *ub_ptr = dx->u.ddd.arc[*cix_ptr].upper_bound;
    else
      *ub_ptr = *lb_ptr - 1;

    *lb_ptr = dx->u.ddd.arc[*cix_ptr].lower_bound;
  }
  else {
    lbx = dx->u.ddd.arc[*cix_ptr].lower_bound;
    ubx = dx->u.ddd.arc[*cix_ptr].upper_bound;
    lby = dy->u.ddd.arc[*ciy_ptr].lower_bound;
    uby = dy->u.ddd.arc[*ciy_ptr].upper_bound;

    if (*lb_ptr > ubx) /* ubx < lb */
      if (*lb_ptr > uby) /* ubx, uby < lb */ {
	if (ubx < uby) /* ubx < uby < lb */ {
	  if (ubx >= lby) /* lby <= ubx < uby < lb */
	    *lb_ptr = ubx + 1;
	  else /* ubx < lby < uby < lb */
	    *lb_ptr = lby;
            *ub_ptr = uby;
	  }
	else if (ubx > uby) /* uby < ubx < lb */ {
	  if (uby >= lbx) /* lbx <= uby < ubx < lb */
	    *lb_ptr = uby + 1;
	  else /* uby < lbx < ubx < lb */
	    *lb_ptr = lbx;

      	  *ub_ptr = ubx;
	}
	else /* ubx = uby < lb */ {
	  if (lbx > lby) /* lby < lbx <= ubx = uby < lb */
	    *lb_ptr = lbx;
	  else /* lbx <= lby <= ubx = uby < lb */
	    *lb_ptr = lby;

	  *ub_ptr = ubx;
	}
      }
      else /* ubx < lb <= uby */ {
	*ub_ptr = *lb_ptr-1;

	if (*lb_ptr - 1 == ubx) /* lb -1 == ubx < lb <= uby */
	  if (lbx < lby) /* lbx < lby <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lby;
	  else           /* lby <= lbx <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lbx;
	  else if (ubx + 1 < lby) /* ubx+1 < lby < lb <= uby */
	    *lb_ptr = lby;
	  else                    /* lby <= ubx+1 < lb <= uby */
	    *lb_ptr = ubx + 1;
      }
      else if (*lb_ptr > uby) /* uby < lb <= ubx */ {
        *ub_ptr = *lb_ptr-1;

        if (*lb_ptr - 1 == uby) /* lb-1 == uby < lb <= ubx */
	  if (lby < lbx) /* lby < lbx <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lbx;
	  else           /* lbx <= lby <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lby;
        else if (uby + 1 < lbx) /* uby+1 < lbx < lb = ubx */
	  *lb_ptr = lbx;
        else                    /* lbx <= ubx+1 < lb <= uby */
	  *lb_ptr = uby + 1;
      }
      else /* lb <= ubx, uby */ {
        *ub_ptr = *lb_ptr - 1;

        if (lbx < lby) /* lbx < lby < lb <= ubx, uby */
	  *lb_ptr = lby;
        else           /* lby <= lbx < lb <= ubx, uby */
	  *lb_ptr = lbx;
      }
    }
}
/* advance_ichild() */




void 	last_fchild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr; 
     float		*lb_ptr, *ub_ptr;
{ 
  *cix_ptr = dx->u.fdd.child_count-1; 
  *ciy_ptr = dy->u.fdd.child_count-1; 
  *ub_ptr = flt_max(
    dx->u.fdd.arc[*cix_ptr].upper_bound, 
    dy->u.fdd.arc[*ciy_ptr].upper_bound
  );  
  
  if (dx->u.fdd.arc[*cix_ptr].lower_bound 
      > dy->u.fdd.arc[*ciy_ptr].upper_bound
      ) 
    *lb_ptr = dx->u.fdd.arc[*cix_ptr].lower_bound; 
  else if (dy->u.fdd.arc[*ciy_ptr].lower_bound 
           > dx->u.fdd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = dy->u.fdd.arc[*ciy_ptr].lower_bound; 
  else if (dy->u.fdd.arc[*ciy_ptr].upper_bound 
           > dx->u.fdd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = feps_plus(dx->u.fdd.arc[*cix_ptr].upper_bound); 
  else if (dx->u.fdd.arc[*cix_ptr].upper_bound 
           > dy->u.fdd.arc[*ciy_ptr].upper_bound
           ) 
    *lb_ptr = feps_plus(dy->u.fdd.arc[*ciy_ptr].upper_bound); 
  else if (dx->u.fdd.arc[*cix_ptr].lower_bound 
           > dy->u.fdd.arc[*ciy_ptr].lower_bound
           ) 
    *lb_ptr = dx->u.fdd.arc[*cix_ptr].lower_bound; 
  else 
    *lb_ptr = dy->u.fdd.arc[*ciy_ptr].lower_bound; 
}
  /* last_fchild() */ 




void	advance_fchild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr; 
     float 		*lb_ptr, *ub_ptr;
{
  float	lbx, ubx, lby, uby;

  /* This is for the catching of type bug at transition */
  if (dx->var_index != dy->var_index || VAR[dx->var_index].TYPE == TYPE_CRD) {
    fprintf(RED_OUT, "\nError: type mismatch in advance_fchild()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  for (; 
       *cix_ptr >= 0 && dx->u.fdd.arc[*cix_ptr].lower_bound >= *lb_ptr; 
       (*cix_ptr)--
       ) ;

  for (; 
       *ciy_ptr >= 0 && dy->u.fdd.arc[*ciy_ptr].lower_bound >= *lb_ptr; 
       (*ciy_ptr)--
       ) ;

  if (*cix_ptr < 0) {
    if (*ciy_ptr >= 0) {
      if (*lb_ptr > dy->u.fdd.arc[*ciy_ptr].upper_bound)
	*ub_ptr = dy->u.fdd.arc[*ciy_ptr].upper_bound;
      else
	*ub_ptr = feps_minus(*lb_ptr);

      *lb_ptr = dy->u.fdd.arc[*ciy_ptr].lower_bound;
    }
  }
  else if (*ciy_ptr < 0) {
    if (*lb_ptr > dx->u.fdd.arc[*cix_ptr].upper_bound)
      *ub_ptr = dx->u.fdd.arc[*cix_ptr].upper_bound;
    else
      *ub_ptr = feps_minus(*lb_ptr);

    *lb_ptr = dx->u.fdd.arc[*cix_ptr].lower_bound;
  }
  else {
    lbx = dx->u.fdd.arc[*cix_ptr].lower_bound;
    ubx = dx->u.fdd.arc[*cix_ptr].upper_bound;
    lby = dy->u.fdd.arc[*ciy_ptr].lower_bound;
    uby = dy->u.fdd.arc[*ciy_ptr].upper_bound;

    if (*lb_ptr > ubx) /* ubx < lb */
      if (*lb_ptr > uby) /* ubx, uby < lb */ {
	if (ubx < uby) /* ubx < uby < lb */ {
	  if (ubx >= lby) /* lby <= ubx < uby < lb */
	    *lb_ptr = feps_plus(ubx);
	  else /* ubx < lby < uby < lb */
	    *lb_ptr = lby;
            *ub_ptr = uby;
	  }
	else if (ubx > uby) /* uby < ubx < lb */ {
	  if (uby >= lbx) /* lbx <= uby < ubx < lb */
	    *lb_ptr = feps_plus(uby);
	  else /* uby < lbx < ubx < lb */
	    *lb_ptr = lbx;

      	  *ub_ptr = ubx;
	}
	else /* ubx = uby < lb */ {
	  if (lbx > lby) /* lby < lbx <= ubx = uby < lb */
	    *lb_ptr = lbx;
	  else /* lbx <= lby <= ubx = uby < lb */
	    *lb_ptr = lby;

	  *ub_ptr = ubx;
	}
      }
      else /* ubx < lb <= uby */ {
	*ub_ptr = feps_minus(*lb_ptr);

	if (feps_minus(*lb_ptr) == ubx) /* lb -1 == ubx < lb <= uby */
	  if (lbx < lby) /* lbx < lby <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lby;
	  else           /* lby <= lbx <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lbx;
	  else if (feps_plus(ubx) < lby) /* ubx+1 < lby < lb <= uby */
	    *lb_ptr = lby;
	  else                    /* lby <= ubx+1 < lb <= uby */
	    *lb_ptr = feps_plus(ubx);
      }
      else if (*lb_ptr > uby) /* uby < lb <= ubx */ {
        *ub_ptr = feps_minus(*lb_ptr);

        if (feps_minus(*lb_ptr) == uby) /* lb-1 == uby < lb <= ubx */
	  if (lby < lbx) /* lby < lbx <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lbx;
	  else           /* lbx <= lby <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lby;
        else if (feps_plus(uby) < lbx) /* uby+1 < lbx < lb = ubx */
	  *lb_ptr = lbx;
        else                    /* lbx <= ubx+1 < lb <= uby */
	  *lb_ptr = feps_plus(uby);
      }
      else /* lb <= ubx, uby */ {
        *ub_ptr = feps_minus(*lb_ptr);

        if (lbx < lby) /* lbx < lby < lb <= ubx, uby */
	  *lb_ptr = lby;
        else           /* lby <= lbx < lb <= ubx, uby */
	  *lb_ptr = lbx;
      }
    }
}
/* advance_fchild() */



void 	last_dfchild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr; 
     double		*lb_ptr, *ub_ptr;
{ 
  *cix_ptr = dx->u.dfdd.child_count-1; 
  *ciy_ptr = dy->u.dfdd.child_count-1; 
  *ub_ptr = dble_max(
    dx->u.dfdd.arc[*cix_ptr].upper_bound, 
    dy->u.dfdd.arc[*ciy_ptr].upper_bound
  );  
  
  if (dx->u.dfdd.arc[*cix_ptr].lower_bound 
      > dy->u.dfdd.arc[*ciy_ptr].upper_bound
      ) 
    *lb_ptr = dx->u.dfdd.arc[*cix_ptr].lower_bound; 
  else if (dy->u.dfdd.arc[*ciy_ptr].lower_bound 
           > dx->u.dfdd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = dy->u.dfdd.arc[*ciy_ptr].lower_bound; 
  else if (dy->u.dfdd.arc[*ciy_ptr].upper_bound 
           > dx->u.dfdd.arc[*cix_ptr].upper_bound
           ) 
    *lb_ptr = dfeps_plus(dx->u.dfdd.arc[*cix_ptr].upper_bound); 
  else if (dx->u.dfdd.arc[*cix_ptr].upper_bound 
           > dy->u.dfdd.arc[*ciy_ptr].upper_bound
           ) 
    *lb_ptr = dfeps_plus(dy->u.dfdd.arc[*ciy_ptr].upper_bound); 
  else if (dx->u.dfdd.arc[*cix_ptr].lower_bound 
           > dy->u.dfdd.arc[*ciy_ptr].lower_bound
           ) 
    *lb_ptr = dx->u.dfdd.arc[*cix_ptr].lower_bound; 
  else 
    *lb_ptr = dy->u.dfdd.arc[*ciy_ptr].lower_bound; 
}
  /* last_dfchild() */ 




void	advance_dfchild(dx, dy, cix_ptr, ciy_ptr, lb_ptr, ub_ptr)
     struct red_type	*dx, *dy;
     int		*cix_ptr, *ciy_ptr; 
     double 		*lb_ptr, *ub_ptr;
{
  double	lbx, ubx, lby, uby;

  /* This is for the catching of type bug at transition */
  if (dx->var_index != dy->var_index || VAR[dx->var_index].TYPE == TYPE_CRD) {
    fprintf(RED_OUT, "\nError: type mismatch in advance_dfchild()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  for (; 
       *cix_ptr >= 0 && dx->u.dfdd.arc[*cix_ptr].lower_bound >= *lb_ptr; 
       (*cix_ptr)--
       ) ;

  for (; 
       *ciy_ptr >= 0 && dy->u.dfdd.arc[*ciy_ptr].lower_bound >= *lb_ptr; 
       (*ciy_ptr)--
       ) ;

  if (*cix_ptr < 0) {
    if (*ciy_ptr >= 0) {
      if (*lb_ptr > dy->u.dfdd.arc[*ciy_ptr].upper_bound)
	*ub_ptr = dy->u.dfdd.arc[*ciy_ptr].upper_bound;
      else
	*ub_ptr = dfeps_minus(*lb_ptr);

      *lb_ptr = dy->u.dfdd.arc[*ciy_ptr].lower_bound;
    }
  }
  else if (*ciy_ptr < 0) {
    if (*lb_ptr > dx->u.dfdd.arc[*cix_ptr].upper_bound)
      *ub_ptr = dx->u.dfdd.arc[*cix_ptr].upper_bound;
    else
      *ub_ptr = dfeps_minus(*lb_ptr);

    *lb_ptr = dx->u.dfdd.arc[*cix_ptr].lower_bound;
  }
  else {
    lbx = dx->u.dfdd.arc[*cix_ptr].lower_bound;
    ubx = dx->u.dfdd.arc[*cix_ptr].upper_bound;
    lby = dy->u.dfdd.arc[*ciy_ptr].lower_bound;
    uby = dy->u.dfdd.arc[*ciy_ptr].upper_bound;

    if (*lb_ptr > ubx) /* ubx < lb */
      if (*lb_ptr > uby) /* ubx, uby < lb */ {
	if (ubx < uby) /* ubx < uby < lb */ {
	  if (ubx >= lby) /* lby <= ubx < uby < lb */
	    *lb_ptr = dfeps_plus(ubx);
	  else /* ubx < lby < uby < lb */
	    *lb_ptr = lby;
            *ub_ptr = uby;
	  }
	else if (ubx > uby) /* uby < ubx < lb */ {
	  if (uby >= lbx) /* lbx <= uby < ubx < lb */
	    *lb_ptr = dfeps_plus(uby);
	  else /* uby < lbx < ubx < lb */
	    *lb_ptr = lbx;

      	  *ub_ptr = ubx;
	}
	else /* ubx = uby < lb */ {
	  if (lbx > lby) /* lby < lbx <= ubx = uby < lb */
	    *lb_ptr = lbx;
	  else /* lbx <= lby <= ubx = uby < lb */
	    *lb_ptr = lby;

	  *ub_ptr = ubx;
	}
      }
      else /* ubx < lb <= uby */ {
	*ub_ptr = dfeps_minus(*lb_ptr);

	if (dfeps_minus(*lb_ptr) == ubx) /* lb -1 == ubx < lb <= uby */
	  if (lbx < lby) /* lbx < lby <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lby;
	  else           /* lby <= lbx <= lb-1 == ubx < lb <= uby */
	    *lb_ptr = lbx;
	  else if (dfeps_plus(ubx) < lby) /* ubx+1 < lby < lb <= uby */
	    *lb_ptr = lby;
	  else                    /* lby <= ubx+1 < lb <= uby */
	    *lb_ptr = dfeps_plus(ubx);
      }
      else if (*lb_ptr > uby) /* uby < lb <= ubx */ {
        *ub_ptr = dfeps_minus(*lb_ptr);

        if (dfeps_minus(*lb_ptr) == uby) /* lb-1 == uby < lb <= ubx */
	  if (lby < lbx) /* lby < lbx <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lbx;
	  else           /* lbx <= lby <= lb-1 == uby < lb <= ubx */
	    *lb_ptr = lby;
        else if (dfeps_plus(uby) < lbx) /* uby+1 < lbx < lb = ubx */
	  *lb_ptr = lbx;
        else                    /* lbx <= ubx+1 < lb <= uby */
	  *lb_ptr = dfeps_plus(uby);
      }
      else /* lb <= ubx, uby */ {
        *ub_ptr = dfeps_minus(*lb_ptr); 

        if (lbx < lby) /* lbx < lby < lb <= ubx, uby */
	  *lb_ptr = lby;
        else           /* lby <= lbx < lb <= ubx, uby */
	  *lb_ptr = lbx;
      }
    }
}
/* advance_dfchild() */




/*****************************************************************************************
 *
 *  Remember! This is the union of zone sets, not the union of state-spaces !!!!
 *
 *  Always remember that bound == CLOCK_POS_INFINITY is as good as no-restriction.
 */

int	count_rec_or = 0; 

struct red_type	*rec_or(); 

struct red_type	*rec_or_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, 
//  			local_count_rec_or, 
  			lb, ub, ub_n, ub_d;
  float			fub, flb; 
  double		dfub, dflb; 
  struct red_type	*false_child, *true_child;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(dy->var_index, 
		    rec_or(dx, dy->u.bdd.zero_child), 
		    rec_or(dx, dy->u.bdd.one_child)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    ciy = dy->u.crd.child_count-1;
    if (dy->u.crd.arc[ciy].upper_bound == CLOCK_POS_INFINITY) {
      true_child = rec_or(dx, dy->u.crd.arc[ciy].child);
      bchild_stack_push(true_child, CLOCK_POS_INFINITY);
      ciy--;
    } 
    else if (VAR[dy->var_index].U.CRD.CLOCK1 == 0) { 
      if (dy->u.crd.arc[ciy].upper_bound == 0) {
        true_child = rec_or(dx, dy->u.crd.arc[ciy].child);
        bchild_stack_push(true_child, 0);
        ciy--;
      } 
      else { 
      	bchild_stack_push(dx, 0);
      } 
    }
    else 
      bchild_stack_push(dx, CLOCK_POS_INFINITY);

    for (; ciy >= 0; ciy--) {
      bchild_stack_push(dy->u.crd.arc[ciy].child,
			dy->u.crd.arc[ciy].upper_bound
			);
    }

    return(crd_new(dy->var_index));

  case TYPE_HRD:
    child_stack_level_push();
    ciy = dy->u.hrd.child_count-1;
    if (dy->u.hrd.arc[ciy].ub_numerator / dy->u.hrd.arc[ciy].ub_denominator
	== HYBRID_POS_INFINITY
	) {
      true_child = rec_or(dx, dy->u.hrd.arc[ciy].child);
      hchild_stack_push(true_child, HYBRID_POS_INFINITY, 1);
      ciy--;
    }
    else
      hchild_stack_push(dx, HYBRID_POS_INFINITY, 1);

    for (; ciy >= 0; ciy--) {
      hchild_stack_push(dy->u.hrd.arc[ciy].child,
			dy->u.hrd.arc[ciy].ub_numerator,
			dy->u.hrd.arc[ciy].ub_denominator
			);
    }

    return(hrd_new(dy->var_index, dy->u.hrd.hrd_exp));
  case TYPE_HDD:
    child_stack_level_push();
    ub_n = HYBRID_POS_INFINITY;
    ub_d = 1; 
    for (ciy = dy->u.hdd.child_count-1; ciy >= 0; ciy--) {
    	//ub>u.hrd_filter.hfchild[ciy].ub
      if (rational_comp(ub_n, ub_d, 
			dy->u.hdd.arc[ciy].ub_numerator,
			dy->u.hdd.arc[ciy].ub_denominator
			)>0
	  ) {
	hfchild_stack_push(dx, 
			   dy->u.hdd.arc[ciy].ub_numerator+1, 
			   dy->u.hdd.arc[ciy].ub_denominator, 
			   ub_n, ub_d
			   );
      }

      true_child = rec_or(dx, dy->u.hdd.arc[ciy].child);
      hfchild_stack_push(true_child, 
      			 dy->u.hdd.arc[ciy].lb_numerator,
			 dy->u.hdd.arc[ciy].lb_denominator,
			 dy->u.hdd.arc[ciy].ub_numerator,
			 dy->u.hdd.arc[ciy].ub_denominator);

      ub_n = dy->u.hdd.arc[ciy].lb_numerator-1;
      ub_d = dy->u.hdd.arc[ciy].lb_denominator;
    }

    if(   (ub_n>=HYBRID_NEG_INFINITY || ub_d!=1)  // to avoid underflow in hybrid.c:rational_comp() 
       && ub_n/ub_d>=HYBRID_NEG_INFINITY 
       )
      hfchild_stack_push(dx, HYBRID_NEG_INFINITY, 1, ub_n, ub_d);

    return(hdd_new(dy->var_index, dy->u.hdd.hrd_exp));

  case TYPE_LAZY_EXP: 
//  fprintf(RED_OUT, "\ncount_rec_or = %1d.\n", 
//    local_count_rec_or = ++count_rec_or; 
//  ); 
/*
    if (local_count_rec_or == -1) { 
      fprintf(RED_OUT, "\nCaught local_count_rec_or = %1d in rec_or_right()\n", 
        local_count_rec_or
      ); 
      fprintf(RED_OUT, "\n==========================\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "\n--------------------------\ndy:\n"); 
      red_print_graph(dy); 
      fflush(RED_OUT); 	
    } 
*/
    false_child = rec_or(dx, dy->u.lazy.false_child);  
    true_child = rec_or(dx, dy->u.lazy.true_child);  
    return(lazy_subtree(
      false_child, true_child, 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    fub = VAR[dy->var_index].U.FLT.UB;
    for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
      if (fub > dy->u.fdd.arc[ciy].upper_bound) {
	fchild_stack_push(dx, feps_plus(dy->u.fdd.arc[ciy].upper_bound), fub);
      }

      true_child = rec_or(dx, dy->u.fdd.arc[ciy].child);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR right: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      fchild_stack_push(true_child, dy->u.fdd.arc[ciy].lower_bound,
			dy->u.fdd.arc[ciy].upper_bound
			);

      fub = feps_minus(dy->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);
/*
    fprintf(RED_OUT, "OR_right(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(fdd_new(dy->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    dfub = VAR[dy->var_index].U.DBLE.UB;
    for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
      if (dfub > dy->u.dfdd.arc[ciy].upper_bound) {
	dfchild_stack_push(dx, 
	  dfeps_plus(dy->u.dfdd.arc[ciy].upper_bound), dfub
	);
      }

      true_child = rec_or(dx, dy->u.dfdd.arc[ciy].child);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR right: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      fchild_stack_push(true_child, dy->u.dfdd.arc[ciy].lower_bound,
			dy->u.dfdd.arc[ciy].upper_bound
			);

      dfub = dfeps_minus(dy->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, dfub);
/*
    fprintf(RED_OUT, "OR_right(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(dfdd_new(dy->var_index));
    break; 

  default:
    child_stack_level_push();
    ub = VAR[dy->var_index].U.DISC.UB;
    for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > dy->u.ddd.arc[ciy].upper_bound) {
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);
      }

      true_child = rec_or(dx, dy->u.ddd.arc[ciy].child);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR right: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      ichild_stack_push(true_child, dy->u.ddd.arc[ciy].lower_bound,
			dy->u.ddd.arc[ciy].upper_bound
			);

      ub = dy->u.ddd.arc[ciy].lower_bound-1;
    }

    if (ub >= VAR[dy->var_index].U.DISC.LB)
      ichild_stack_push(dx, VAR[dy->var_index].U.DISC.LB, ub);
/*
    fprintf(RED_OUT, "OR_right(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(ddd_new(dy->var_index));
  }
}
/* rec_or_right() */







struct red_type	*rec_or_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, 
//  			local_count_rec_or, 
  			lb, ub, ub_n, ub_d;
  float			fub, flb; 
  double		dflb, dfub; 
  struct red_type	*false_child, *true_child;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(dx->var_index, 
		    rec_or(dx->u.bdd.zero_child, dy), 
		    rec_or(dx->u.bdd.one_child, dy)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    cix = dx->u.crd.child_count-1;
    if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) {
      true_child = rec_or(dx->u.crd.arc[cix].child, dy);
      bchild_stack_push(true_child, CLOCK_POS_INFINITY
      				 );
      cix--;
    }
    else if (VAR[dx->var_index].U.CRD.CLOCK1 == 0) { 
      if (dx->u.crd.arc[cix].upper_bound == 0) {
        true_child = rec_or(dx->u.crd.arc[cix].child, dy);
        bchild_stack_push(true_child, 0);
        cix--;
      } 
      else { 
      	bchild_stack_push(dy, 0);
      } 
    }
    else
      bchild_stack_push(dy, CLOCK_POS_INFINITY);

    for (; cix >= 0; cix--) {
      bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound
      				 );
    }

    return(crd_new(dx->var_index));

  case TYPE_HRD:
    child_stack_level_push();
    cix = dx->u.hrd.child_count-1;
    if (dx->u.hrd.arc[cix].ub_numerator / dx->u.hrd.arc[cix].ub_denominator
	== HYBRID_POS_INFINITY
	) {
      true_child = rec_or(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(true_child, HYBRID_POS_INFINITY, 1);
      cix--;
    }
    else
      hchild_stack_push(dy, HYBRID_POS_INFINITY, 1);

    for (; cix >= 0; cix--) {
      hchild_stack_push(dx->u.hrd.arc[cix].child,
			dx->u.hrd.arc[cix].ub_numerator,
			dx->u.hrd.arc[cix].ub_denominator
			);
    }

    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
  case TYPE_HDD:
    child_stack_level_push();
    ub_n = HYBRID_POS_INFINITY;
    ub_d = 1;
    for (cix = dx->u.hdd.child_count-1; cix >= 0; cix--) {
      //ub>u.hrd_filter.hfchild[cix].ub
      if (rational_comp(ub_n, ub_d, 
			dx->u.hdd.arc[cix].ub_numerator, 
			dx->u.hdd.arc[cix].ub_denominator
			)>0
	  ) {
	hfchild_stack_push(dy, 
			   dx->u.hdd.arc[cix].ub_numerator+1, 
			   dx->u.hdd.arc[cix].ub_denominator, 
			   ub_n, ub_d
			   );
      }

      true_child = rec_or(dx->u.hdd.arc[cix].child,dy);
      hfchild_stack_push(true_child, 
      	  		 dx->u.hdd.arc[cix].lb_numerator,
			 dx->u.hdd.arc[cix].lb_denominator,
			 dx->u.hdd.arc[cix].ub_numerator,
			 dx->u.hdd.arc[cix].ub_denominator
			 );

      ub_n = dx->u.hdd.arc[cix].lb_numerator-1;
      ub_d = dx->u.hdd.arc[cix].lb_denominator;
    }
	
    if(   (ub_n>=HYBRID_NEG_INFINITY || ub_d!=1) // to avoid underflow in hybrid.c:rational_comp() 
       && ub_n/ub_d>=HYBRID_NEG_INFINITY
       )
      hfchild_stack_push(dy, 
			 HYBRID_NEG_INFINITY, 1, ub_n, ub_d);
    return(hdd_new(dx->var_index, dx->u.hdd.hrd_exp));

  case TYPE_LAZY_EXP: 
//  fprintf(RED_OUT, "\ncount_rec_or = %1d.\n", 
//    local_count_rec_or = ++count_rec_or; 
//  ); 
/*
    if (local_count_rec_or == 91400) { 
      fprintf(RED_OUT, "\nCaught local_count_rec_or = %1d in rec_or_left()\n", 
        local_count_rec_or
      ); 
      fprintf(RED_OUT, "\n==========================\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "\n--------------------------\ndy:\n"); 
      red_print_graph(dy); 
      fflush(RED_OUT); 	
    } 
*/
    false_child = rec_or(dx->u.lazy.false_child, dy);  
    true_child = rec_or(dx->u.lazy.true_child, dy);  
    return(lazy_subtree(
      false_child, true_child, 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    fub = VAR[dx->var_index].U.FLT.UB;
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      if (ub > dx->u.fdd.arc[cix].upper_bound) {
	fchild_stack_push(dy, feps_plus(dx->u.fdd.arc[cix].upper_bound), fub);
      }

      true_child = rec_or(dx->u.fdd.arc[cix].child, dy);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR left: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      fchild_stack_push(true_child, dx->u.fdd.arc[cix].lower_bound,
			dx->u.fdd.arc[cix].upper_bound
			);

      fub = feps_minus(dx->u.fdd.arc[cix].lower_bound);
    }

    if (fub >= VAR[dx->var_index].U.FLT.LB)
      fchild_stack_push(dy, VAR[dx->var_index].U.FLT.LB, fub);

/*
    fprintf(RED_OUT, "OR_left(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(fdd_new(dx->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    dfub = VAR[dx->var_index].U.DBLE.UB;
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      if (ub > dx->u.dfdd.arc[cix].upper_bound) {
	dfchild_stack_push(dy, 
	  dfeps_plus(dx->u.dfdd.arc[cix].upper_bound), dfub
	);
      }

      true_child = rec_or(dx->u.dfdd.arc[cix].child, dy);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR left: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      dfchild_stack_push(true_child, dx->u.dfdd.arc[cix].lower_bound,
			dx->u.dfdd.arc[cix].upper_bound
			);

      dfub = dfeps_minus(dx->u.dfdd.arc[cix].lower_bound);
    }

    if (dfub >= VAR[dx->var_index].U.DBLE.LB)
      dfchild_stack_push(dy, VAR[dx->var_index].U.DBLE.LB, dfub);

/*
    fprintf(RED_OUT, "OR_left(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(dfdd_new(dx->var_index));
    break; 

  default:
    child_stack_level_push();
    ub = VAR[dx->var_index].U.DISC.UB;
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      if (ub > dx->u.ddd.arc[cix].upper_bound) {
	ichild_stack_push(dy, dx->u.ddd.arc[cix].upper_bound+1, ub);
      }

      true_child = rec_or(dx->u.ddd.arc[cix].child, dy);
      if (   true_child->var_index >= VARIABLE_COUNT 
          || true_child->var_index < 0
          ) {
        fprintf(RED_OUT, "OR left: A bad cached variable index %1d\n", 
                true_child->var_index
              ); 
        bk(0); 
      }
      ichild_stack_push(true_child, dx->u.ddd.arc[cix].lower_bound,
			dx->u.ddd.arc[cix].upper_bound
			);

      ub = dx->u.ddd.arc[cix].lower_bound-1;
    }

    if (ub >= VAR[dx->var_index].U.DISC.LB)
      ichild_stack_push(dy, VAR[dx->var_index].U.DISC.LB, ub);

/*
    fprintf(RED_OUT, "OR_left(%1d:%x,%1d:%x):checking\n", 
            dx->var_index, (unsigned int) dx, dy->var_index, (unsigned int) dy  
            ); 
    hsp(); 
*/
    return(ddd_new(dx->var_index));
  }
}
/* rec_or_left() */


// int	count_or_check = 0, b_or = 0; 


  
struct red_type	*rec_or(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, 
//                                local_count_rec_or, 
                                cix, ciy, lb_n, lb_d, ub_n, ub_d;
  float				fub, flb; 
  double			dflb, dfub; 
  struct red_type		*new_child, *child2;
  struct ddd_child_type		*icx, *icy;
  struct fdd_child_type		*fcx, *fcy;
  struct dfdd_child_type	*dfcx, *dfcy;
  int 				lbxn, lbxd, ubxn, ubxd, lbyn, lbyd, ubyn, ubyd;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_NO_RESTRICTION || dy == NORM_NO_RESTRICTION) {
    return(NORM_NO_RESTRICTION);
  }
  else if (dx == NORM_FALSE || dx == dy) 
    return(dy); 
  else if (dy == NORM_FALSE)
    return(dx); 

  ce = cache2_check_result_key_symmetric(OR, dx, dy);   
  if (ce->result != NULL) { 
    if (   ce->result->var_index >= VARIABLE_COUNT 
        || ce->result->var_index < 0
        ) {
      fprintf(RED_OUT, "(OR) A bad cached variable index %1d\n", 
              ce->result->var_index
              ); 
      bk(0); 
    }
    return(ce->result); 
  } 

  if (dx->var_index < dy->var_index) {
    return(ce->result = rec_or_left(dx, dy));
  }
  else if (dx->var_index > dy->var_index) {
    return(ce->result = rec_or_right(dx, dy));
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD:
  case TYPE_SYNCHRONIZER: 
    new_child = bdd_new(dx->var_index, 
			rec_or(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
			rec_or(dx->u.bdd.one_child, dy->u.bdd.one_child)
			); 
    return (ce->result = new_child); 
    break;
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	 cix >= 0 && ciy >= 0;
	 ) {
      if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound) {
	bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
	cix--;
      }
      else if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	bchild_stack_push(dy->u.crd.arc[ciy].child, dy->u.crd.arc[ciy].upper_bound);
	ciy--;
      }
      else {
	new_child = rec_or(dx->u.crd.arc[cix].child, dy->u.crd.arc[ciy].child);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	cix--; ciy--;
      }
    }

    if (cix >= 0) {
      for (; cix>=0; cix--)
	bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
    }
    else {
      for (; ciy>=0; ciy--)
	bchild_stack_push(dy->u.crd.arc[ciy].child, dy->u.crd.arc[ciy].upper_bound);
    }

    return (ce->result = crd_new(dx->var_index)); 
    break;

  case TYPE_HRD:
    if (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp)) {
      if (b < 0)
        return(ce->result = rec_or_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_or_right(dx, dy));
    }
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count - 1, ciy = dy->u.hrd.child_count - 1;
	 cix >= 0 && ciy >= 0;
	 ) {
      b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			dx->u.hrd.arc[cix].ub_denominator,
			dy->u.hrd.arc[ciy].ub_numerator,
			dy->u.hrd.arc[ciy].ub_denominator
			);

      if (b > 0) {
	hchild_stack_push(dx->u.hrd.arc[cix].child,
			  dx->u.hrd.arc[cix].ub_numerator,
			  dx->u.hrd.arc[cix].ub_denominator
			  );
	cix--;
      }
      else if (b < 0) {
	hchild_stack_push(dy->u.hrd.arc[ciy].child,
			  dy->u.hrd.arc[ciy].ub_numerator,
			  dy->u.hrd.arc[ciy].ub_denominator
			  );
	ciy--;
      }
      else {
	new_child = rec_or(dx->u.hrd.arc[cix].child, dy->u.hrd.arc[ciy].child);
	hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				   dx->u.hrd.arc[cix].ub_denominator
				   );
	cix--; ciy--;
      }
    }

    if (cix >= 0) {
      for (; cix>=0; cix--)
	hchild_stack_push(dx->u.hrd.arc[cix].child,
				   dx->u.hrd.arc[cix].ub_numerator,
				   dx->u.hrd.arc[cix].ub_denominator
				   );
    }
    else {
      for (; ciy>=0; ciy--)
	hchild_stack_push(dy->u.hrd.arc[ciy].child,
				   dy->u.hrd.arc[ciy].ub_numerator,
				   dy->u.hrd.arc[ciy].ub_denominator
				   );
    }

    return (ce->result
      = hrd_new(dx->var_index, dx->u.hrd.hrd_exp)
    ); 
    break;
  case TYPE_HDD:
    if (b = HRD_EXP_COMP(dx->u.hdd.hrd_exp, dy->u.hdd.hrd_exp)) {
      if (b < 0)
        return(ce->result = rec_or_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_or_right(dx, dy));
    }
    child_stack_level_push();
    cix = dx->u.hdd.child_count - 1;
    ciy = dy->u.hdd.child_count - 1;

    /* to avoid overflow in hybrid.c:rational_comp() */
    lbxn = dx->u.hdd.arc[cix].lb_numerator; 
    lbxd = dx->u.hdd.arc[cix].lb_denominator;
    ubxn = dx->u.hdd.arc[cix].ub_numerator; 
    ubxd = dx->u.hdd.arc[cix].ub_denominator;
    lbyn = dy->u.hdd.arc[ciy].lb_numerator; 
    lbyd = dy->u.hdd.arc[ciy].lb_denominator;
    ubyn = dy->u.hdd.arc[ciy].ub_numerator; 
    ubyd = dy->u.hdd.arc[ciy].ub_denominator;
    
    if (rational_comp(ubyn,ubyd,ubxn,ubxd)>0) /* ubx < uby < lb */ {
      if (rational_comp(ubxn,ubxd,lbyn,lbyd)>=0) /* lby <= ubx < uby < lb */ {
        lb_n = ubxn + 1;
        lb_d = ubxd; 
      }
      else /* ubx < lby < uby < lb */ {
        lb_n = lbyn;
        lb_d = lbyd;   	    			
      }

      ub_n = dy->u.hdd.arc[ciy].ub_numerator;
      ub_d = dy->u.hdd.arc[ciy].ub_denominator;    
    }
    else if (rational_comp(ubxn,ubxd,ubyn,ubyd)>0) /* uby < ubx < lb */ {
      if (rational_comp(ubyn,ubyd,lbxn,lbxd)>=0) /* lbx <= uby < ubx < lb */ {	    	
        lb_n = dy->u.hdd.arc[ciy].lb_numerator + 1;
        lb_d = dy->u.hdd.arc[ciy].lb_denominator;    	    			
      }
      else /* uby < lbx < ubx < lb */ {	
        lb_n = dx->u.hdd.arc[cix].lb_numerator;
        lb_d = dx->u.hdd.arc[cix].lb_denominator;    	    			
      }

      ub_n = dx->u.hdd.arc[cix].ub_numerator;
      ub_d = dx->u.hdd.arc[cix].ub_denominator;    
    }
    else /* ubx = uby < lb */ {
      if (rational_comp(lbxn,lbxd,lbyn,lbyd)>0) /* lby < lbx <= ubx = uby < lb */ {
        lb_n = dx->u.hdd.arc[cix].lb_numerator;
        lb_d = dx->u.hdd.arc[cix].lb_denominator;    	    			
      }
      else /* lbx <= s <= ubx = uby < lb */ {
        lb_n = dy->u.hdd.arc[ciy].lb_numerator;
        lb_d = dy->u.hdd.arc[ciy].lb_denominator;    	    			
      }	

      ub_n = dx->u.hdd.arc[cix].ub_numerator;
      ub_d = dx->u.hdd.arc[cix].ub_denominator;    
    }
    for (advance_hfchild(dx, dy, &cix, &ciy, &lb_n, &lb_d, &ub_n, &ub_d);
         cix >= 0 || ciy >= 0;
         advance_hfchild(dx, dy, &cix, &ciy, &lb_n, &lb_d, &ub_n, &ub_d)
         ) {

      if (cix >= 0  
          && rational_comp(lb_n, lb_d, 
			   dx->u.hdd.arc[cix].lb_numerator, 
			   dx->u.hdd.arc[cix].lb_denominator
			   ) >= 0 
	  && rational_comp(dx->u.hdd.arc[cix].ub_numerator, 
			   dx->u.hdd.arc[cix].ub_denominator, 
			   ub_n, ub_d
			   ) >= 0
	  )
        if (   ciy >= 0 
            && rational_comp(lb_n, lb_d, 
	    		     dy->u.hdd.arc[ciy].lb_numerator, 
	    		     dy->u.hdd.arc[ciy].lb_denominator 
	    		     ) >= 0 
            && rational_comp(dy->u.hdd.arc[ciy].ub_numerator, 
			     dy->u.hdd.arc[ciy].ub_denominator, 
			     ub_n, ub_d 
			     ) >= 0
	    )
          new_child = rec_or(dx->u.hdd.arc[cix].child, 
                               dy->u.hdd.arc[ciy].child);
        else
	  new_child = dx->u.hdd.arc[cix].child;
      else
	new_child = dy->u.hdd.arc[ciy].child;

      if(ub_n/ub_d>=HYBRID_NEG_INFINITY) {
        /* to avoid underflow in hybrid.c:rational_comp() */
        if(lb_n/lb_d<HYBRID_NEG_INFINITY)
          lb_n = HYBRID_NEG_INFINITY;
          
        hfchild_stack_push(new_child, lb_n, lb_d, ub_n, ub_d);          
      }
      
    }

    return (ce->result
      = hdd_new(dx->var_index, dx->u.hdd.hrd_exp)
    ); 
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_or_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_or_right(dx, dy));
    }
//  fprintf(RED_OUT, "\ncount_rec_or = %1d.\n", 
//    local_count_rec_or = ++count_rec_or; 
//  ); 
/*
    if (local_count_rec_or == -1) { 
      fprintf(RED_OUT, "\nCaught local_count_rec_or = %1d in rec_or()\n", 
        local_count_rec_or
      ); 
      fprintf(RED_OUT, "\n==========================\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "\n--------------------------\ndy:\n"); 
      red_print_graph(dy); 
      fflush(RED_OUT); 	
    } 
*/
    new_child = rec_or(dx->u.lazy.false_child, dy->u.lazy.false_child); 
    child2 = rec_or(dx->u.lazy.true_child, dy->u.lazy.true_child); 
    ce->result = lazy_subtree(
      new_child, child2, 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    return(ce->result); 

  case TYPE_FLOAT:
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
	    ){
	  new_child = rec_or(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
          if (   new_child->var_index >= VARIABLE_COUNT 
              || new_child->var_index < 0
              ) {
            fprintf(RED_OUT, "A bad OR variable index %1d\n", 
              new_child->var_index
              ); 
            bk(0); 
          }
	}
	else {
	  new_child = dx->u.fdd.arc[cix].child;
	}
      else {
	new_child = dy->u.fdd.arc[ciy].child;
      }
      fchild_stack_push(new_child, flb, fub);
    }
    return (ce->result = fdd_new(dx->var_index)); 
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &dflb, &dfub);
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
	    ){
	  new_child = rec_or(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
          if (   new_child->var_index >= VARIABLE_COUNT 
              || new_child->var_index < 0
              ) {
            fprintf(RED_OUT, "A bad OR variable index %1d\n", 
              new_child->var_index
              ); 
            bk(0); 
          }
	}
	else {
	  new_child = dx->u.dfdd.arc[cix].child;
	}
      else {
	new_child = dy->u.dfdd.arc[ciy].child;
      }
      dfchild_stack_push(new_child, dflb, dfub);
    }
    return (ce->result = dfdd_new(dx->var_index)); 
    break;

  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound){
	  new_child = rec_or(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
          if (   new_child->var_index >= VARIABLE_COUNT 
              || new_child->var_index < 0
              ) {
            fprintf(RED_OUT, "A bad OR variable index %1d\n", 
              new_child->var_index
              ); 
            bk(0); 
          }
	}
	else {
	  new_child = dx->u.ddd.arc[cix].child;
	}
      else {
	new_child = dy->u.ddd.arc[ciy].child;
      }
      ichild_stack_push(new_child, lb, ub);
    }
    return (ce->result = ddd_new(dx->var_index)); 
    break;
  }
}
  /* rec_or() */







/***************************************************************************************************
 *
 *  It is important to distinguish the interpretation of NORM_NO_RESTRICTION for clock inequalities.
 *
 *	. if we interpret them as (-oo, oo) for dx while (-oo, oo) for dy, then we should use RESTRICT
 *	. if we interpret them as (oo, oo) for dx while (-oo, oo) for dy, then we should use SUBTRACT and EXTRACT
 * 	. if we interpret them as (oo, oo) for both dx and dy, then we should use INTERSECT and EXCLUDE
 */


/*******************************
 *
 *  For RESTRICT, NORM_NO_RESTRICTION of clock inequalities is interpreted as (-oo, oo) for both dx, dy.
 */

int	count_and_check = 0, b_and = 0; 

/*
int	test_child_stack_level_push() { 
  TOP_LEVEL_CHILD_STACK++; 
  LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] = 0; 
// The following is the one that seems overwritten. 
// LEVEL_CHILD_COUNT = (int *) malloc(VARIABLE_COUNT * sizeof(int)); 
  fprintf(RED_OUT, "LEVEL_CHILD_COUNT:%x\n", LEVEL_CHILD_COUNT); 
  fprintf(RED_OUT, "LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK=%1d]:%x:%1d\n", 
    TOP_LEVEL_CHILD_STACK, 
    &(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]), 
    LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]
  ); 
}
*/
  /* test_child_stack_level_push() */ 



/******************************************************************
 *  The following procedure is for the and of two lazy expressions. 
 */ 
struct red_type	*red_and_lazy_exp(
  struct red_type	*dx, 
  struct red_type	*dy
) {
  int	vi; 
  struct red_type	*result; 
  struct ps_bunit_type	dummy_bu, dummy_bux, dummy_buy, *bu_tail, *bu, 
  			*bux, *buy; 
  
  vi = int_max(dx->var_index, dy->var_index); 
  if (dx->u.lazy.exp == dy->u.lazy.exp) { 
    fprintf(RED_OUT, 
      "\nERROR: This is a bug!  Identical operand in red_and() \n"
    ); 
    fprintf(RED_OUT, 
      "       should have been detected.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
    return(dx); 
  } 
  if (dx->u.lazy.exp->type == AND) { 
    bux = dx->u.lazy.exp->u.bexp.blist; 
  } 
  else { 
  // Create a dummy list for the non-AND dx.
    bux = &dummy_bux; 
    bux->subexp = dx->u.lazy.exp; 
    bux->bnext = NULL; 
  } 
  if (dy->u.lazy.exp->type == AND) { 
    buy = dy->u.lazy.exp->u.bexp.blist; 
  } 
  else {
  // Create a dummy list for the non-AND dy.
    buy = &dummy_buy; 
    buy->subexp = dy->u.lazy.exp; 
    buy->bnext = NULL; 
  } 

  bu_tail = &dummy_bu; 
  result = red_alloc(vi); 
  result->u.lazy.exp = ps_exp_alloc(AND); 
  result->u.lazy.exp->u.bexp.len = 0; 
  for (; bux || buy; ) { 
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));
    if (buy == NULL || (bux && bux->subexp <= buy->subexp)) { 
      bu->subexp = bux->subexp; 
    } 
    else if (bux == NULL || (buy && bux->subexp > buy->subexp)) { 
      bu->subexp = buy->subexp; 
    } 
    bu_tail->bnext = bu; 
    bu_tail = bu; 
    if (bux && bux->subexp == bu->subexp) 
      bux = bux->bnext; 
    if (buy && buy->subexp == bu->subexp) 
      buy = buy->bnext; 
    result->u.lazy.exp->u.bexp.len++; 
  } 
  bu_tail->bnext = NULL; 
  result->u.lazy.exp->u.bexp.blist = dummy_bu.bnext; 
  result->u.lazy.exp = ps_exp_share(result->u.lazy.exp); 
  return(red_share(result)); 
}
  /* red_and_lazy_exp() */  




struct red_type	*rec_and();

int	count_and = 0; 

struct red_type	*rec_and_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub, count_tmp, b_tmp, 
			local_count_and;
  struct red_type	*new_child, *new;
/*
  fprintf(RED_OUT, "\ncount and right %1d\n", 
    local_count_and = ++count_and
  ); 
  fflush(RED_OUT); 
*/
  switch (VAR[dy->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(dy->var_index, 
		    rec_and(dx, dy->u.bdd.zero_child), 
		    rec_and(dx, dy->u.bdd.one_child)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    if (VAR[dy->var_index].U.CRD.CLOCK1 < VAR[dy->var_index].U.CRD.CLOCK2) {
      for (ciy = dy->u.crd.child_count-1; ciy >= 0; ciy--) {
	new_child = rec_and(dx, dy->u.crd.arc[ciy].child);
	if (new_child->var_index 
	    == VAR[dy->var_index].U.CRD.CONVERSE_CRD_VI
	    ) {
	  if (VAR[dy->var_index].U.CRD.CLOCK2 == TIME) 
	    new_child = zone_extract_interval(new_child,
              new_child->var_index,
	      -1*dy->u.crd.arc[ciy].upper_bound,
	      HYBRID_POS_INFINITY
	    );
	  else if (dy->u.crd.arc[ciy].upper_bound == CLOCK_NEG_INFINITY) { 
	    if (new_child->u.crd.arc[new_child->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
	      new_child = new_child->u.crd.arc[new_child->u.crd.child_count-1].child;
	    else
	      new_child = NORM_FALSE;
	  }
	  else 
	    new_child = zone_extract_interval(new_child,
				              new_child->var_index,
					      -1*dy->u.crd.arc[ciy].upper_bound,
					      CLOCK_POS_INFINITY
					      );
	}

	bchild_stack_push(new_child, dy->u.crd.arc[ciy].upper_bound);
      }
    }
    else {
      for (ciy = dy->u.crd.child_count-1; ciy >= 0; ciy--) {
	new_child = rec_and(dx, dy->u.crd.arc[ciy].child);
	bchild_stack_push(new_child, dy->u.crd.arc[ciy].upper_bound);
      }
    }

    return(crd_new(dy->var_index));

  case TYPE_HRD:
    /*test_*/ child_stack_level_push();
    if (dy->u.hrd.hrd_exp->hrd_term[0].coeff < 0) {
      for (ciy = dy->u.hrd.child_count-1; ciy >= 0; ciy--) {
	new_child = rec_and(dx, dy->u.hrd.arc[ciy].child);
	if (hrd_converse_test(dy, new_child)) {
	  if (   dy->u.hrd.arc[ciy].ub_numerator == HYBRID_NEG_INFINITY
	      && dy->u.hrd.arc[ciy].ub_denominator == 1
	      ) {
	    if (   new_child->u.hrd.arc[new_child->u.hrd.child_count-1].ub_numerator == HYBRID_POS_INFINITY
	        || new_child->u.hrd.arc[new_child->u.hrd.child_count-1].ub_denominator == 1
		)
	      new_child = new_child->u.hrd.arc[new_child->u.hrd.child_count-1].child;
	    else
	      new_child = NORM_FALSE;
	  }
	  else
	    new_child = hybrid_root_extract_upperhalf(new_child,
						      -1*dy->u.hrd.arc[ciy].ub_numerator,
						      dy->u.hrd.arc[ciy].ub_denominator
						      );
	}

	hchild_stack_push(new_child, dy->u.hrd.arc[ciy].ub_numerator,
				   dy->u.hrd.arc[ciy].ub_denominator
				   );
      }
    }
    else {
      for (ciy = dy->u.hrd.child_count-1; ciy >= 0; ciy--) {
	new_child = rec_and(dx, dy->u.hrd.arc[ciy].child);
	hchild_stack_push(new_child, dy->u.hrd.arc[ciy].ub_numerator,
				   dy->u.hrd.arc[ciy].ub_denominator
				   );
      }
    }

    return(hrd_new(dy->var_index, dy->u.hrd.hrd_exp));

  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_and(dx, dy->u.lazy.false_child), 
      rec_and(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
//    b_tmp = ++b_and; 
//    for (; b_tmp == 6; ); 
    child_stack_level_push();
    for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx, dy->u.fdd.arc[ciy].child);
/*
      check_order(dy->var_index, new_child); 
*/
//      count_tmp = ++count_and_check; 
//      for (; count_tmp == 6; ); 
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
			dy->u.fdd.arc[ciy].upper_bound
			);
    }

    return(fdd_new(dy->var_index));

  case TYPE_DOUBLE:
//    b_tmp = ++b_and; 
//    for (; b_tmp == 6; ); 
    child_stack_level_push();
    for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx, dy->u.dfdd.arc[ciy].child);
/*
      check_order(dy->var_index, new_child); 
*/
//      count_tmp = ++count_and_check; 
//      for (; count_tmp == 6; ); 
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
			dy->u.dfdd.arc[ciy].upper_bound
			);
    }

    return(dfdd_new(dy->var_index));

  default:
//    b_tmp = ++b_and; 
//    for (; b_tmp == 6; ); 
    child_stack_level_push();
    for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx, dy->u.ddd.arc[ciy].child);
/*
      check_order(dy->var_index, new_child); 
*/
//      count_tmp = ++count_and_check; 
//      for (; count_tmp == 6; ); 
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      ichild_stack_push(new_child, dy->u.ddd.arc[ciy].lower_bound,
			dy->u.ddd.arc[ciy].upper_bound
			);
    }

    return(ddd_new(dy->var_index));
  }
}
/* rec_and_right() */







struct red_type	*rec_and_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, lb, ub, local_count_and; // , count_tmp;
  struct red_type	*new_child, *new;
/*
  fprintf(RED_OUT, "\ncount and left %1d\n", 
    local_count_and = ++count_and
  ); 
  fflush(RED_OUT); 
*/
  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(dx->var_index, 
		    rec_and(dx->u.bdd.zero_child, dy), 
		    rec_and(dx->u.bdd.one_child, dy)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    if (VAR[dx->var_index].U.CRD.CLOCK1 < VAR[dx->var_index].U.CRD.CLOCK2) {
      for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
	new_child = rec_and(dx->u.crd.arc[cix].child, dy);
	if (new_child->var_index 
	    == VAR[dx->var_index].U.CRD.CONVERSE_CRD_VI
	    ) {
	  if (VAR[dx->var_index].U.CRD.CLOCK2 == TIME) 
	    new_child = zone_extract_interval(new_child,
	      new_child->var_index,
	      -1*dx->u.crd.arc[cix].upper_bound,
	      HYBRID_POS_INFINITY
	    );
	  else if (dx->u.crd.arc[cix].upper_bound == CLOCK_NEG_INFINITY) {
	    if (new_child->u.crd.arc[new_child->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
	      new_child = new_child->u.crd.arc[new_child->u.crd.child_count-1].child;
	    else
	      new_child = NORM_FALSE;
	  }
	  else
	    new_child = zone_extract_interval(new_child,
	      new_child->var_index,
	      -1*dx->u.crd.arc[cix].upper_bound,
	      CLOCK_POS_INFINITY
	    );
	}

	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
      }
    }
    else {
      for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
	new_child = rec_and(dx->u.crd.arc[cix].child, dy);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
      }
    }

    return(crd_new(dx->var_index));

  case TYPE_HRD:
    child_stack_level_push();
    if (dx->u.hrd.hrd_exp->hrd_term[0].coeff < 0) {
      for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
	new_child = rec_and(dx->u.hrd.arc[cix].child, dy);

	if (hrd_converse_test(dx, new_child)) {
	  if (   dx->u.hrd.arc[cix].ub_numerator == HYBRID_NEG_INFINITY
	      && dx->u.hrd.arc[cix].ub_denominator == 1
	      ) {
	    if (   new_child->u.hrd.arc[new_child->u.hrd.child_count-1].ub_numerator == HYBRID_POS_INFINITY
	        || new_child->u.hrd.arc[new_child->u.hrd.child_count-1].ub_denominator == 1
		)
	      new_child = new_child->u.hrd.arc[new_child->u.hrd.child_count-1].child;
	    else
	      new_child = NORM_FALSE;
	  }
	  else
	    new_child = hybrid_root_extract_upperhalf(new_child,
						      -1*dx->u.hrd.arc[cix].ub_numerator,
						      dx->u.hrd.arc[cix].ub_denominator
						      );
	}

	hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				   dx->u.hrd.arc[cix].ub_denominator
				   );
      }
    }
    else {
      for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
	new_child = rec_and(dx->u.hrd.arc[cix].child, dy);
	hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				   dx->u.hrd.arc[cix].ub_denominator
				   );
      }
    }

    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));


  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_and(dx->u.lazy.false_child, dy), 
      rec_and(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx->u.fdd.arc[cix].child, dy);
/*
      check_order(dx->var_index, new_child); 
*/
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
			dx->u.fdd.arc[cix].upper_bound
			);
    }

    return(fdd_new(dx->var_index));

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx->u.dfdd.arc[cix].child, dy);
/*
      check_order(dx->var_index, new_child); 
*/
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      fchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
			dx->u.dfdd.arc[cix].upper_bound
			);
    }

    return(dfdd_new(dx->var_index));

  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
/*
      count_tmp = ++count_and_check; 
      if (count_tmp == -1) 
        for (; count_tmp; ); 
*/
      new_child = rec_and(dx->u.ddd.arc[cix].child, dy);
/*
      check_order(dx->var_index, new_child); 
*/
/*
      if (count_and == 226) { 
      	fprintf(RED_OUT, "\n****(dx=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dx, dx->var_index, VAR[dx->var_index]
      	); 
      	red_print_graph(dx); 
      	fprintf(RED_OUT, "\n****(dy=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) dy, dy->var_index, VAR[dy->var_index]
      	); 
      	red_print_graph(dy); 
      	fprintf(RED_OUT, "\n****(new_child=%x:vi=%1d:type=%1d)***********\n", 
      	  (unsigned int) new_child, new_child->var_index, VAR[new_child->var_index]
      	); 
      	red_print_graph(new_child); 
      } 
*/
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
			dx->u.ddd.arc[cix].upper_bound
			);
    }

    return(ddd_new(dx->var_index));
  }
}
/* rec_and_left() */





struct red_type	*rec_and(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy; // , count_tmp;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *new_child2;
  struct red_type		*unionx, *uniony;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_FALSE || dy == NORM_FALSE) 
    return(NORM_FALSE); 
  else if (dx == NORM_NO_RESTRICTION || dx == dy)
    return(dy);
  else if (dy == NORM_NO_RESTRICTION)
    return(dx);

/*
  fprintf(RED_OUT, "count_and = %1d\n", ++count_and); 
*/
  ce = cache2_check_result_key_symmetric(AND, dx, dy); 
  /*  fprintf(RED_OUT, "\nnew rec %x = (%x,%x)\n", (unsigned int) rec, (unsigned int) rec->redx, (unsigned int) rec->redy);
   */
  if (ce->result) {
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result); 
  } 

  if (dx->var_index < dy->var_index) {
    ce->result = rec_and_left(dx, dy); 
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result); 
  }
  else if (dx->var_index > dy->var_index) {
    ce->result = rec_and_right(dx, dy); 
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result);
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD:
  case TYPE_SYNCHRONIZER: 
    return(ce->result 
      = bdd_new(dx->var_index, 
	      rec_and(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
	      rec_and(dx->u.bdd.one_child, dy->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    cix = dx->u.crd.child_count - 1;
    ciy = dy->u.crd.child_count - 1;
    for (unionx = dx->u.crd.arc[cix].child;
	 cix > 0 && dx->u.crd.arc[cix-1].upper_bound >= dy->u.crd.arc[ciy].upper_bound;
	 ) {
      cix--; 
      unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
    }
    for (uniony = dy->u.crd.arc[ciy].child;
	 ciy > 0 && dx->u.crd.arc[cix].upper_bound <= dy->u.crd.arc[ciy-1].upper_bound;
	 ) {
      ciy--;
      uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
    }
    if (VAR[dx->var_index].U.CRD.CLOCK1 < VAR[dx->var_index].U.CRD.CLOCK2) {
      /* Use bchild_stack_restrict() to construct the child list. */
      for (; cix >= 0 && ciy >= 0; ) {
	if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	  new_child = rec_and(dx->u.crd.arc[cix].child, uniony);
	  bchild_stack_restrict(
	    VAR[dx->var_index].U.CRD.CONVERSE_CRD_VI, 
	    new_child, 
	    dx->u.crd.arc[cix].upper_bound
	  );
	}
	else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound) {
	  new_child = rec_and(unionx, dy->u.crd.arc[ciy].child);
	  bchild_stack_restrict(
	    VAR[dx->var_index].U.CRD.CONVERSE_CRD_VI, new_child, 
	    dy->u.crd.arc[ciy].upper_bound
	  );
	}
	else {
	  new_child = rec_and(unionx, dy->u.crd.arc[ciy].child);
	  new_child2 = rec_and(dx->u.crd.arc[cix].child, uniony);
	  new_child = red_bop(OR, new_child, new_child2);
	  bchild_stack_restrict(
	    VAR[dx->var_index].U.CRD.CONVERSE_CRD_VI, 
	    new_child, 
	    dy->u.crd.arc[ciy].upper_bound
	  );
	}
	if (cix> 0) {
	  cix--;
	  if (ciy>0) {
	    ciy--;
	    if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	      cix++;
	      uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	    }
	    else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound) {
	      ciy++;
	      unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	    }
	    else {
	      unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	      uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	    }
	  }
	  else
	    unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	}
	else
	  if (ciy > 0) {
	    ciy--;
	    uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	  }
	  else
	    break;
      }
    }
    else {
      /* use bchild_stack_push((struct crd_child_link_type *) ) to construct the child list. */
      for (; cix >= 0 && ciy >= 0; ) {
	if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	  new_child = rec_and(dx->u.crd.arc[cix].child, uniony);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	}
	else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound) {
	  new_child = rec_and(unionx, dy->u.crd.arc[ciy].child);
	  bchild_stack_push(new_child, dy->u.crd.arc[ciy].upper_bound);
	}
	else {
	  new_child = rec_and(unionx, dy->u.crd.arc[ciy].child);
	  new_child2 = rec_and(dx->u.crd.arc[cix].child, uniony);
	  new_child = red_bop(OR, new_child, new_child2);
	  bchild_stack_push(new_child, dy->u.crd.arc[ciy].upper_bound);
	}
	if (cix> 0) {
	  cix--;
	  if (ciy>0) {
	    ciy--;
	    if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	      cix++;
	      uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	    }
	    else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound) {
	      ciy++;
	      unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	    }
	    else {
	      unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	      uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	    }
	  }
	  else
	    unionx = red_bop(OR, unionx, dx->u.crd.arc[cix].child);
	}
	else
	  if (ciy > 0) {
	    ciy--;
	    uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
	  }
	  else
	    break;
      }
    }

    return(ce->result = crd_new(dx->var_index));
    break; 
  case TYPE_HRD: 
    if (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp)) {
      if (b < 0) {
        return(ce->result = rec_and_left(dx, dy));
      }
      else if (b > 0) {
        return(ce->result = rec_and_right(dx, dy));
      }
    }

    child_stack_level_push();
    cix = dx->u.hrd.child_count - 1;
    ciy = dy->u.hrd.child_count - 1;
    for (unionx = dx->u.hrd.arc[cix].child;
	 cix > 0 && rational_comp(dx->u.hrd.arc[cix-1].ub_numerator,
		       dx->u.hrd.arc[cix-1].ub_denominator,
		       dy->u.hrd.arc[ciy].ub_numerator,
		       dy->u.hrd.arc[ciy].ub_denominator
		       ) >= 0;
	 ) {
      cix--;
      unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
    }
    for (uniony = dy->u.hrd.arc[ciy].child;
	 ciy > 0 && rational_comp(dx->u.hrd.arc[cix].ub_numerator,
		       dx->u.hrd.arc[cix].ub_denominator,
		       dy->u.hrd.arc[ciy-1].ub_numerator,
		       dy->u.hrd.arc[ciy-1].ub_denominator
		       ) <= 0;
	 ) {
      ciy--;
      uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
    }
    if (dx->u.hrd.hrd_exp->hrd_term[0].coeff < 0) {
      /* Use bchild_stack_restrict() to construct the child list. */
      for (; cix >= 0 && ciy >= 0; ) {
        b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
		          dx->u.hrd.arc[cix].ub_denominator,
			  dy->u.hrd.arc[ciy].ub_numerator,
			  dy->u.hrd.arc[ciy].ub_denominator
			  );
	if (b < 0) {
	  new_child = rec_and(dx->u.hrd.arc[cix].child, uniony);
	  hchild_stack_restrict(dx->u.hrd.hrd_exp, 
	  			new_child, dx->u.hrd.arc[cix].ub_numerator,
				dx->u.hrd.arc[cix].ub_denominator
				);
	}
	else if (b > 0) {
	  new_child = rec_and(unionx, dy->u.hrd.arc[ciy].child);
	  hchild_stack_restrict(dy->u.hrd.hrd_exp, 
	  			new_child, dy->u.hrd.arc[ciy].ub_numerator,
				dy->u.hrd.arc[ciy].ub_denominator
				);
	}
	else {
	  new_child = rec_and(unionx, dy->u.hrd.arc[ciy].child);
	  new_child2 = rec_and(dx->u.hrd.arc[cix].child, uniony);
	  new_child = red_bop(OR, new_child, new_child2);
	  hchild_stack_restrict(dy->u.hrd.hrd_exp, new_child,
				dy->u.hrd.arc[ciy].ub_numerator,
				dy->u.hrd.arc[ciy].ub_denominator
				);
	}
	if (cix > 0) {
	  cix--;
	  if (ciy > 0) {
	    ciy--;
	    b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			      dx->u.hrd.arc[cix].ub_denominator,
			      dy->u.hrd.arc[ciy].ub_numerator,
			      dy->u.hrd.arc[ciy].ub_denominator
			      );
	    if (b < 0) {
	      cix++;
	      uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	    }
	    else if (b > 0) {
	      ciy++;
	      unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	    }
	    else {
	      unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	      uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	    }
	  }
	  else
	    unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	}
	else
	  if (ciy > 0) {
	    ciy--;
	    uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	  }
	  else
	    break;
      }
    }
    else {
      /* use bchild_stack_push((struct crd_child_link_type *) ) to construct the child list. */
      for (; cix >= 0 && ciy >= 0; ) {
        b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
		          dx->u.hrd.arc[cix].ub_denominator,
			  dy->u.hrd.arc[ciy].ub_numerator,
			  dy->u.hrd.arc[ciy].ub_denominator
			  );
	if (b < 0) {
	  new_child = rec_and(dx->u.hrd.arc[cix].child, uniony);
	  hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
			    dx->u.hrd.arc[cix].ub_denominator
			    );
	}
	else if (b > 0) {
	  new_child = rec_and(unionx, dy->u.hrd.arc[ciy].child);
	  hchild_stack_push(new_child, dy->u.hrd.arc[ciy].ub_numerator,
	  		    dy->u.hrd.arc[ciy].ub_denominator
			    );
	}
	else {
	  new_child = rec_and(unionx, dy->u.hrd.arc[ciy].child);
	  new_child2 = rec_and(dx->u.hrd.arc[cix].child, uniony);
	  new_child = red_bop(OR, new_child, new_child2);
	  hchild_stack_push(new_child, dy->u.hrd.arc[ciy].ub_numerator,
	  		    dy->u.hrd.arc[ciy].ub_denominator
			    );
	}
	if (cix > 0) {
	  cix--;
	  if (ciy > 0) {
	    ciy--;
	    b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			      dx->u.hrd.arc[cix].ub_denominator,
			      dy->u.hrd.arc[ciy].ub_numerator,
			      dy->u.hrd.arc[ciy].ub_denominator
			      );
	    if (b < 0) {
	      cix++;
	      uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	    }
	    else if (b > 0) {
	      ciy++;
	      unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	    }
	    else {
	      unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	      uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	    }
	  }
	  else
	    unionx = red_bop(OR, unionx, dx->u.hrd.arc[cix].child);
	}
	else
	  if (ciy > 0) {
	    ciy--;
	    uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
	  }
	  else
	    break;
      }
    }

    return(ce->result
      = hrd_new(dx->var_index, dx->u.hrd.hrd_exp)
    );
    break; 

  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_and_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_and_right(dx, dy));
    }
    ce->result = lazy_subtree(
      rec_and(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_and(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    return(ce->result); 
    break; 

  case TYPE_FLOAT: 
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 && ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    ) {
/*
	  count_tmp = ++count_and_check; 
	  if (count_tmp == -1) 
	    for (; count_tmp; ); 
*/
	  new_child = rec_and(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child); 
/*
	  check_order(dx->var_index, new_child); 
*/
	  fchild_stack_push(new_child, flb, fub);
	}
    }
    ce->result = fdd_new(dx->var_index); 
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result);

  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 && ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    ) {
/*
	  count_tmp = ++count_and_check; 
	  if (count_tmp == -1) 
	    for (; count_tmp; ); 
*/
	  new_child = rec_and(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child); 
/*
	  check_order(dx->var_index, new_child); 
*/
	  dfchild_stack_push(new_child, dflb, dfub);
	}
    }
    ce->result = dfdd_new(dx->var_index); 
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result);

  default: 
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 && ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
/*
	  count_tmp = ++count_and_check; 
	  if (count_tmp == -1) 
	    for (; count_tmp; ); 
*/
	  new_child = rec_and(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child); 
/*
	  check_order(dx->var_index, new_child); 
*/
	  ichild_stack_push(new_child, lb, ub);
	}
    }
    ce->result = ddd_new(dx->var_index); 
/*
    if (count_and >= 170) {
      fprintf(RED_OUT, "===(rec_and cached result)====\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "---(dy)--------------------\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "---(result)-----------------\n"); 
      red_print_graph(ce->result);
    } 
*/
    return(ce->result);
  }
}
  /* rec_and() */







/*******************************
 *  This procedure find the common zones (as difference sets) of the dx and 
 *  dy.
 *  For INTERSECT, NORM_NO_RESTRICTION of clock inequalities is interpreted
 *	as (oo, oo) for both dx and dy.
 */

struct red_type	*rec_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy; 
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_NO_RESTRICTION || dx == dy)  
    return(dy); 
  else if (dy == NORM_NO_RESTRICTION)
    return(dx);
  else if (dx == NORM_FALSE || dy == NORM_FALSE) 
    return(NORM_FALSE); 

  ce = cache2_check_result_key(INTERSECT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (   (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) 
      || dy == NORM_NO_RESTRICTION
      ) {
    struct crd_child_type	*bcx;
    struct hrd_child_type	*hcx;
    struct ddd_child_type	*icx;
    struct fdd_child_type	*fcx;
    struct dfdd_child_type	*dfcx;

    switch (VAR[dx->var_index].TYPE) { 
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      result = bdd_new(dx->var_index, 
		       rec_intersect(dx->u.bdd.zero_child, dy), 
		       rec_intersect(dx->u.bdd.one_child, dy)
		       ); 
      break; 
    case TYPE_CRD: 
      bcx = &(dx->u.crd.arc[dx->u.crd.child_count - 1]);
      if (bcx->upper_bound == CLOCK_POS_INFINITY)
	result = rec_intersect(bcx->child, dy);
      else
	result = NORM_FALSE;
      break; 
    case TYPE_HRD: 
      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_intersect(hcx->child, dy);
      else
	result = NORM_FALSE;
      break; 
    case TYPE_FLOAT: 
      child_stack_level_push();
      for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
        fcx = &(dx->u.fdd.arc[cix]);
        new_child = rec_intersect(fcx->child, dy);
        fchild_stack_push(new_child, fcx->lower_bound, fcx->upper_bound);
      }

      result = fdd_new(dx->var_index);
      break; 
    case TYPE_DOUBLE: 
      child_stack_level_push();
      for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
        dfcx = &(dx->u.dfdd.arc[cix]);
        new_child = rec_intersect(dfcx->child, dy);
        dfchild_stack_push(new_child, dfcx->lower_bound, dfcx->upper_bound);
      }

      result = dfdd_new(dx->var_index);
      break; 
    default: 
      child_stack_level_push();
      for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
        icx = &(dx->u.ddd.arc[cix]);
        new_child = rec_intersect(icx->child, dy);
        ichild_stack_push(new_child, icx->lower_bound, icx->upper_bound);
      }

      result = ddd_new(dx->var_index);
    }
    return(ce->result = result);
  }
  else if (   (dy != NORM_NO_RESTRICTION && dx->var_index > dy->var_index) 
           || dx == NORM_NO_RESTRICTION
           ) {
    struct crd_child_type	*bcy;
    struct hrd_child_type	*hcy;
    struct ddd_child_type	*icy;
    struct fdd_child_type	*fcy;
    struct dfdd_child_type	*dfcy;

    switch (VAR[dx->var_index].TYPE) { 
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      result = bdd_new(dy->var_index, 
		       rec_intersect(dx, dy->u.bdd.zero_child), 
		       rec_intersect(dx, dy->u.bdd.one_child)
		       ); 
      break; 
    case TYPE_CRD: 
      bcy = &(dy->u.crd.arc[dy->u.crd.child_count - 1]);
      if (bcy->upper_bound == CLOCK_POS_INFINITY)
	result = rec_intersect(dx, bcy->child);
      else
	result = NORM_FALSE;
      break; 
    case TYPE_HRD: 
      hcy = &(dy->u.hrd.arc[dy->u.hrd.child_count - 1]);
      if (hcy->ub_numerator == HYBRID_POS_INFINITY && hcy->ub_denominator == 1)
	result = rec_intersect(dx, hcy->child);
      else
	result = NORM_FALSE;
      break; 
    case TYPE_FLOAT: 
      child_stack_level_push();
      for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
        fcy = &(dy->u.fdd.arc[ciy]);
        new_child = rec_intersect(dx, fcy->child);
        fchild_stack_push(new_child, fcy->lower_bound, fcy->upper_bound);
      }

      result = fdd_new(dy->var_index);
      break; 
    case TYPE_DOUBLE: 
      child_stack_level_push();
      for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
        dfcy = &(dy->u.dfdd.arc[ciy]);
        new_child = rec_intersect(dx, dfcy->child);
        dfchild_stack_push(new_child, dfcy->lower_bound, dfcy->upper_bound);
      }

      result = dfdd_new(dy->var_index);
      break; 
    default: 
      child_stack_level_push();
      for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
        icy = &(dy->u.ddd.arc[ciy]);
        new_child = rec_intersect(dx, icy->child);
        ichild_stack_push(new_child, icy->lower_bound, icy->upper_bound);
      }

      result = ddd_new(dy->var_index);
    }
    return(ce->result = result);
  }
  else if (   VAR[dx->var_index].TYPE == TYPE_HRD
           && (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp))
	   ) {
    if (b < 0) {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_intersect(hcx->child, dy);
      else
	result = NORM_FALSE;
      return(ce->result = result);
    }
    else if (b > 0) {
      struct hrd_child_type	*hcy;

      hcy = &(dy->u.hrd.arc[dy->u.hrd.child_count - 1]);
      if (hcy->ub_numerator == HYBRID_POS_INFINITY && hcy->ub_denominator == 1)
	result = rec_intersect(dx, hcy->child);
      else
	result = NORM_FALSE;
      return(ce->result = result);
    }
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dx->var_index, 
		     rec_intersect(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
		     rec_intersect(dx->u.bdd.one_child, dy->u.bdd.one_child)
		     ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	 cix >= 0 && ciy >= 0;
	 ){
      if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound)
	ciy--;
      else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound)
	cix--;
      else {
	new_child = rec_intersect(dx->u.crd.arc[cix].child, dy->u.crd.arc[ciy].child);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	cix--;
	ciy--;
      }
    }

    result = crd_new(dx->var_index);
    break;
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count - 1, ciy = dy->u.hrd.child_count - 1;
	 cix >= 0 && ciy >= 0;
	 ){
      b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			dx->u.hrd.arc[cix].ub_denominator,
			dy->u.hrd.arc[ciy].ub_numerator,
			dy->u.hrd.arc[ciy].ub_denominator
			);
      if (b < 0)
	ciy--;
      else if (b > 0)
	cix--;
      else {
	new_child = rec_intersect(dx->u.hrd.arc[cix].child, dy->u.hrd.arc[ciy].child);
	hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
			  dx->u.hrd.arc[cix].ub_denominator
			  );
	cix--;
	ciy--;
      }
    }

    result = hrd_new(dx->var_index, dx->u.hrd.hrd_exp);
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 && ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_intersect(dx->u.fdd.arc[cix].child, 
	    dy->u.fdd.arc[ciy].child
	  );
	  fchild_stack_push(new_child, flb, fub);
	}
    }

    result = fdd_new(dx->var_index);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 && ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_intersect(dx->u.dfdd.arc[cix].child, 
	    dy->u.dfdd.arc[ciy].child
	  );
	  dfchild_stack_push(new_child, dflb, dfub);
	}
    }

    result = dfdd_new(dx->var_index);
    break;
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 && ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_intersect(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  ichild_stack_push(new_child, lb, ub);
	}
    }

    result = ddd_new(dx->var_index);
  }

  return(ce->result = result);
}
  /* rec_intersect() */






/*******************************
 *
 *  For EXCLUDE, NORM_NO_RESTRICTION of clock inequalities is interpreted
 *	as (oo, oo) for both dx and dy.
 */
struct red_type	*rec_exclude();

struct red_type	*rec_exclude_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub;
  float			flb, fub; 
  double		dflb, dfub; 
  struct red_type	*new_child, *result;
/*
  fprintf(RED_OUT, "  exR:%x;%x\n", (unsigned int) dx, (unsigned int) dy);
  fflush(RED_OUT);
*/
  switch (VAR[dy->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dy->var_index, 
		   rec_exclude(dx, dy->u.bdd.zero_child), 
		   rec_exclude(dx, dy->u.bdd.one_child)
		   )
	   ); 
    break; 
  case TYPE_CRD:
    if (dy->u.crd.arc[dy->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_exclude(dx, dy->u.crd.arc[dy->u.crd.child_count-1].child));
    else
      return(dx);

  case TYPE_HRD:
    if (   dy->u.hrd.arc[dy->u.hrd.child_count-1].ub_numerator == HYBRID_POS_INFINITY
        && dy->u.hrd.arc[dy->u.hrd.child_count-1].ub_denominator == 1
	)
      return(rec_exclude(dx, dy->u.hrd.arc[dy->u.hrd.child_count-1].child));
    else
      return(dx);

  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_exclude(dx, dy->u.lazy.false_child), 
      rec_exclude(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
/*
    fprintf(RED_OUT, "  exRdefault: \n");
    fflush(RED_OUT);
*/
    child_stack_level_push();
    for (fub = VAR[dy->var_index].U.FLT.UB, ciy = dy->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
/*
      fprintf(RED_OUT, "  exRdefault in cycle %1d\n", ciy);
      fflush(RED_OUT);
*/
      if (fub > dy->u.fdd.arc[ciy].upper_bound)
	fchild_stack_push(dx, feps_plus(dy->u.fdd.arc[ciy].upper_bound), fub);
/*
      fprintf(RED_OUT, "  before R%1d;\n", ciy);
      fflush(RED_OUT);
*/
      new_child = rec_exclude(dx, dy->u.fdd.arc[ciy].child);
/*
      fprintf(RED_OUT, "  after  R%1d;\n", ciy);
      fflush(RED_OUT);
*/
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
      fub = feps_minus(dy->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);

    return(fdd_new(dy->var_index));

  case TYPE_DOUBLE:
/*
    fprintf(RED_OUT, "  exRdefault: \n");
    fflush(RED_OUT);
*/
    child_stack_level_push();
    for (dfub = VAR[dy->var_index].U.DBLE.UB, ciy = dy->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
/*
      fprintf(RED_OUT, "  exRdefault in cycle %1d\n", ciy);
      fflush(RED_OUT);
*/
      if (dfub > dy->u.dfdd.arc[ciy].upper_bound)
	dfchild_stack_push(dx, 
	  dfeps_plus(dy->u.dfdd.arc[ciy].upper_bound), dfub
	);
/*
      fprintf(RED_OUT, "  before R%1d;\n", ciy);
      fflush(RED_OUT);
*/
      new_child = rec_exclude(dx, dy->u.dfdd.arc[ciy].child);
/*
      fprintf(RED_OUT, "  after  R%1d;\n", ciy);
      fflush(RED_OUT);
*/
      dfchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
				 dy->u.fdd.arc[ciy].upper_bound
				 );
      dfub = dfeps_minus(dy->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.DBLE.LB)
      dfchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(dy->var_index));
    
  default:
/*
    fprintf(RED_OUT, "  exRdefault: \n");
    fflush(RED_OUT);
*/
    child_stack_level_push();
    for (ub = VAR[dy->var_index].U.DISC.UB, ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
/*
      fprintf(RED_OUT, "  exRdefault in cycle %1d\n", ciy);
      fflush(RED_OUT);
*/
      if (ub > dy->u.ddd.arc[ciy].upper_bound)
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);
/*
      fprintf(RED_OUT, "  before R%1d;\n", ciy);
      fflush(RED_OUT);
*/
      new_child = rec_exclude(dx, dy->u.ddd.arc[ciy].child);
/*
      fprintf(RED_OUT, "  after  R%1d;\n", ciy);
      fflush(RED_OUT);
*/
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
/* rec_exclude_right() */








struct red_type	*rec_exclude_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    return(bdd_new(dx->var_index, 
		   rec_exclude(dx->u.bdd.zero_child, dy), 
		   rec_exclude(dx->u.bdd.one_child, dy)
		   )
	   ); 
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
      struct crd_child_type		*bcx;

      bcx = &(dx->u.crd.arc[cix]);
      new_child = rec_exclude(bcx->child, dy);
      bchild_stack_push(new_child, bcx->upper_bound);
    }
    return(crd_new(dx->var_index));

  case TYPE_HRD: 
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[cix]);
      new_child = rec_exclude(hcx->child, dy);
      hchild_stack_push(new_child, hcx->ub_numerator, hcx->ub_denominator);
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
  
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_exclude(dx->u.lazy.false_child, dy), 
      rec_exclude(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT: 
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      struct fdd_child_type	*fcx;

      fcx = &(dx->u.fdd.arc[cix]);
      new_child = rec_exclude(fcx->child, dy);
/*
      fprintf(RED_OUT, "  L%1d;\n", cix);
      fflush(RED_OUT);
*/
      fchild_stack_push(new_child, fcx->lower_bound, fcx->upper_bound);
    }
    return(fdd_new(dx->var_index));
    break; 

  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      struct dfdd_child_type	*dfcx;

      dfcx = &(dx->u.dfdd.arc[cix]);
      new_child = rec_exclude(dfcx->child, dy);
/*
      fprintf(RED_OUT, "  L%1d;\n", cix);
      fflush(RED_OUT);
*/
      dfchild_stack_push(new_child, dfcx->lower_bound, dfcx->upper_bound);
    }
    return(dfdd_new(dx->var_index));
    break; 

  default: 
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      struct ddd_child_type	*icx;

      icx = &(dx->u.ddd.arc[cix]);
      new_child = rec_exclude(icx->child, dy);
/*
      fprintf(RED_OUT, "  L%1d;\n", cix);
      fflush(RED_OUT);
*/
      ichild_stack_push(new_child, icx->lower_bound, icx->upper_bound);
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_exclude_left() */







// int count_exclude = 0; 

struct red_type	*rec_exclude(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, bx, by, lb, ub, cix, ciy, 
				lce;
  float				flb, fub; 
  float				dflb, dfub; 
  struct red_type		*new_child, *dy_child, *result;
  struct ddd_child_type		*icx, *icy;
  struct fdd_child_type		*fcx, *fcy;
  struct dfdd_child_type	*dfcx, *dfcy;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_FALSE || dx == dy) 
    return(NORM_FALSE); 
  else if (dy == NORM_FALSE) {
    return(dx); 
  }
  else if (dy == NORM_NO_RESTRICTION) {
    return(NORM_FALSE);
  }
/*
  lce = ++count_exclude; 
  fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
  for (; count_exclude == -1; ); 
*/
  ce = cache2_check_result_key(EXCLUDE, dx, dy); 
  if (ce->result) { 
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, cached result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "cached result:\n"); 
      red_print_graph(ce->result); 
    }
*/
    return(ce->result); 
  } 
/*
  if (ITERATION_COUNT == 20 && bug_flag1)
    fprintf(RED_OUT, "new exclude tree node %x registered with dx=%x; dy=%x\n", (unsigned int) nrec, (unsigned int) dx, (unsigned int) dy);
*/

  if ((dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) || dy == NORM_NO_RESTRICTION) {
    ce->result = rec_exclude_left(dx, dy); 
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, left root result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "left root result:\n"); 
      red_print_graph(ce->result); 
    }
*/
    return(ce->result);
  }
  else if (   (dy != NORM_NO_RESTRICTION && dy->var_index < dx->var_index) 
           || dx == NORM_NO_RESTRICTION
           ) {
    ce->result = rec_exclude_right(dx, dy); 
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, right root result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "right root result:\n"); 
      red_print_graph(ce->result); 
    }
*/
    return(ce->result);
  } 

  switch (VAR[dx->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dx->var_index, 
	      rec_exclude(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
	      rec_exclude(dx->u.bdd.one_child, dy->u.bdd.one_child)
            ); 
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    dy_child = NORM_FALSE;
    for (cix = dx->u.crd.child_count-1, ciy = dy->u.crd.child_count-1; cix >= 0; cix--) {
      for (; ciy >= 0 && dx->u.crd.arc[cix].upper_bound <= dy->u.crd.arc[ciy].upper_bound; ciy--)
	dy_child = red_bop(OR, dy_child, dy->u.crd.arc[ciy].child);
      if (dy_child != NORM_FALSE)
	new_child = rec_exclude(dx->u.crd.arc[cix].child, dy_child);
      else
	new_child = dx->u.crd.arc[cix].child;

      bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
    }

    result = crd_new(dx->var_index);
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, crd result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "crd result:\n"); 
      red_print_graph(result); 
    } 
*/
    break; 
  case TYPE_HRD: 
    if (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp)) {
      if (b < 0)
        return(ce->result = rec_exclude_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_exclude_right(dx, dy));
    }
    child_stack_level_push();
    dy_child = NORM_FALSE;
    for (cix = dx->u.hrd.child_count-1, ciy = dy->u.hrd.child_count-1; cix >= 0; cix--) {
      for (;
              ciy >= 0
           && rational_comp(dx->u.hrd.arc[cix].ub_numerator, dx->u.hrd.arc[cix].ub_denominator,
			    dy->u.hrd.arc[ciy].ub_numerator, dy->u.hrd.arc[ciy].ub_denominator
			    ) <= 0;
	   ciy--
	   )
	dy_child = red_bop(OR, dy_child, dy->u.hrd.arc[ciy].child);
      if (dy_child != NORM_FALSE)
	new_child = rec_exclude(dx->u.hrd.arc[cix].child, dy_child);
      else
	new_child = dx->u.hrd.arc[cix].child;

      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
 				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }

    result = hrd_new(dx->var_index, dx->u.hrd.hrd_exp);
    break; 
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_exclude_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_exclude_right(dx, dy));
    }
    result = lazy_subtree(
      rec_exclude(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_exclude(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT: 
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_exclude(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
	else
	  new_child = dx->u.fdd.arc[cix].child;
/*
	fprintf(RED_OUT, "  M%1d:%1d;\n", cix, ciy);
*/
	fchild_stack_push(new_child, flb, fub);
      }
    }

    result = fdd_new(dx->var_index);
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, ddd result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "ddd result:\n"); 
      red_print_graph(result); 
    } 
*/
    break; 

  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_exclude(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
	else
	  new_child = dx->u.dfdd.arc[cix].child;
/*
	fprintf(RED_OUT, "  M%1d:%1d;\n", cix, ciy);
*/
	dfchild_stack_push(new_child, dflb, dfub);
      }
    }

    result = dfdd_new(dx->var_index);
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, ddd result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "ddd result:\n"); 
      red_print_graph(result); 
    } 
*/
    break; 

  default: 
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_exclude(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	else
	  new_child = dx->u.ddd.arc[cix].child;
/*
	fprintf(RED_OUT, "  M%1d:%1d;\n", cix, ciy);
*/
	ichild_stack_push(new_child, lb, ub);
      }
    }

    result = ddd_new(dx->var_index);
/*
    if (ITERATION_COUNT == 4) { 
      fprintf(RED_OUT, "count_exclude=%1d\n", lce); 
      for (; count_exclude == -1; ); 
      fprintf(RED_OUT, "====(rec_exclude, ddd result)==========\ndx:\n"); 
      red_print_graph(dx); 
      fprintf(RED_OUT, "dy:\n"); 
      red_print_graph(dy); 
      fprintf(RED_OUT, "ddd result:\n"); 
      red_print_graph(result); 
    } 
*/
  }
  return(ce->result = result); 
}
  /* rec_exclude() */









/*******************************
 *
 *  For SUBTRACT, NORM_NO_RESTRICTION of clock inequalities is interpreted
 * 	as (oo, oo) for dx while (-oo, oo) for dy.
 */
struct red_type		*rec_subtract();

struct red_type	*rec_subtract_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dy->var_index, 
		   rec_subtract(dx, dy->u.bdd.zero_child), 
		   rec_subtract(dx, dy->u.bdd.one_child)
		   )
	   ); 
    break; 
  case TYPE_CDD:
    if (dy->u.ddd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_subtract(dx, dy->u.ddd.arc[dy->u.ddd.child_count-1].child));
    else
      return(dx);

  case TYPE_CRD:
    fprintf(RED_OUT, "\nWarning: inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HDD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality filter right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_subtract(dx, dy->u.lazy.false_child), 
      rec_subtract(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 
    
  case TYPE_FLOAT: {
    float flb, fub; 
    
    child_stack_level_push();
    for (fub = VAR[dy->var_index].U.FLT.UB, ciy = dy->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (fub > dy->u.fdd.arc[ciy].upper_bound)
	fchild_stack_push(dx, 
	  feps_plus(dy->u.fdd.arc[ciy].upper_bound), fub
	);

      new_child = rec_subtract(dx, dy->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
      fub = feps_minus(dy->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);

    return(fdd_new(dy->var_index));
    break; 
  }
  case TYPE_DOUBLE: {
    double dfub, dflb; 
    
    child_stack_level_push();
    for (dfub = VAR[dy->var_index].U.DBLE.UB, ciy = dy->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (dfub > dy->u.dfdd.arc[ciy].upper_bound)
	dfchild_stack_push(dx, 
	  dfeps_plus(dy->u.dfdd.arc[ciy].upper_bound), dfub
	);

      new_child = rec_subtract(dx, dy->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
	dy->u.dfdd.arc[ciy].upper_bound
      );
      dfub = dfeps_plus(dy->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.DBLE.LB)
      dfchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(dy->var_index));
    break; 
  }   
  default:
    child_stack_level_push();
    for (ub = VAR[dy->var_index].U.DISC.UB, ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > dy->u.ddd.arc[ciy].upper_bound)
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);

      new_child = rec_subtract(dx, dy->u.ddd.arc[ciy].child);
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
/* rec_subtract_right() */




struct red_type	*rec_subtract_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, ciy, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dx->var_index, 
		   rec_subtract(dx->u.bdd.zero_child, dy), 
		   rec_subtract(dx->u.bdd.one_child, dy)
		   )
	   ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    if (dy->var_index == VAR[dx->var_index].U.CRD.CORRESPONDING_CDD_VI) {
      for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	   cix >= 0 && ciy >= 0;
	   ){
	if (dy->u.ddd.arc[ciy].lower_bound > dx->u.crd.arc[cix].upper_bound)
	  ciy--;
	else if (dy->u.ddd.arc[ciy].upper_bound < dx->u.crd.arc[cix].upper_bound) {
	  bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
	else {
	  new_child = rec_subtract(dx->u.crd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
      }

      for (; cix >= 0; cix--) {
	bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
      }
    }
    else {
      for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
	new_child = rec_subtract(dx->u.crd.arc[cix].child, dy);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
      }
    }
    return(crd_new(dx->var_index));
  case TYPE_HDD:
    fprintf(RED_OUT, "\nError: a hybrid filter inequality is encountered.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_subtract(dx->u.lazy.false_child, dy), 
      rec_subtract(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	 dx->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(dx->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	 dx->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(dx->var_index));
    break; 

  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
	 dx->u.ddd.arc[cix].upper_bound
      );
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_subtract_left() */








struct red_type	*rec_subtract(dx, dy)
     struct red_type	*dx, *dy;
{
  int				dyi, b, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (VAR[dx->var_index].TYPE == TYPE_CDD) {
    fprintf(RED_OUT, "\nError: a dx with type filter inequality in rec_subtract() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (dy == NORM_NO_RESTRICTION || dx == dy)
    return(NORM_FALSE);
  else if (dy == NORM_FALSE)
    return(dx);

  ce = cache2_check_result_key(SUBTRACT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) 
    return(ce->result 
      = rec_subtract_left(dx, dy)
    );
  else if (dx->var_index > dy->var_index || dx == NORM_NO_RESTRICTION) {
    return(ce->result 
      = rec_subtract_right(dx, dy)
    ); 
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dx->var_index, 
	      rec_exclude(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
	      rec_exclude(dx->u.bdd.one_child, dy->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    fprintf(RED_OUT, "\nWARNING: inequality subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_HRD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality filter subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_subtract_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_subtract_right(dx, dy));
    }
    result = lazy_subtree(
      rec_subtract(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_subtract(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_subtract(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
	else
	  new_child = dx->u.fdd.arc[cix].child;

	fchild_stack_push(new_child, flb, fub);
      }
    }
    result = fdd_new(dx->var_index); 
    break; 
    
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_subtract(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
	else
	  new_child = dx->u.dfdd.arc[cix].child;

	dfchild_stack_push(new_child, dflb, dfub);
      }
    }
    result = dfdd_new(dx->var_index); 
    break; 
    
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_subtract(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	else
	  new_child = dx->u.ddd.arc[cix].child;

	ichild_stack_push(new_child, lb, ub);
      }
    }
    result = ddd_new(dx->var_index); 
  }
  return(ce->result = result); 
}
  /* rec_subtract() */


struct red_type	*rec_subtract_right_try_intersect(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dy->var_index, 
		   rec_subtract(dx, dy->u.bdd.zero_child), 
		   rec_subtract(dx, dy->u.bdd.one_child)
		   )
	   ); 
    break; 
  case TYPE_CDD:
    if (dy->u.ddd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_subtract(dx, dy->u.ddd.arc[dy->u.ddd.child_count-1].child));
    else
      return(dx);

  case TYPE_CRD:
    if (dy->u.crd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY) 
      return(rec_subtract(dx, dy->u.crd.arc[dy->u.ddd.child_count-1].child)); 
    else 
      return(dx); 
      
    fprintf(RED_OUT, "\nWarning: inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HDD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality filter right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_subtract(dx, dy->u.lazy.false_child), 
      rec_subtract(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 
    
  case TYPE_FLOAT: {
    float flb, fub; 
    
    child_stack_level_push();
    for (fub = VAR[dy->var_index].U.FLT.UB, ciy = dy->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (fub > dy->u.fdd.arc[ciy].upper_bound)
	fchild_stack_push(dx, 
	  feps_plus(dy->u.fdd.arc[ciy].upper_bound), fub
	);

      new_child = rec_subtract(dx, dy->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
      fub = feps_minus(dy->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);

    return(fdd_new(dy->var_index));
    break; 
  }
  case TYPE_DOUBLE: {
    double dfub, dflb; 
    
    child_stack_level_push();
    for (dfub = VAR[dy->var_index].U.DBLE.UB, ciy = dy->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (dfub > dy->u.dfdd.arc[ciy].upper_bound)
	dfchild_stack_push(dx, 
	  dfeps_plus(dy->u.dfdd.arc[ciy].upper_bound), dfub
	);

      new_child = rec_subtract(dx, dy->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
	dy->u.dfdd.arc[ciy].upper_bound
      );
      dfub = dfeps_plus(dy->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.DBLE.LB)
      dfchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(dy->var_index));
    break; 
  }   
  default:
    child_stack_level_push();
    for (ub = VAR[dy->var_index].U.DISC.UB, ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > dy->u.ddd.arc[ciy].upper_bound)
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);

      new_child = rec_subtract(dx, dy->u.ddd.arc[ciy].child);
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
/* rec_subtract_right() */




struct red_type	*rec_subtract_left_try_intersect(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, ciy, lb, ub;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dx->var_index, 
		   rec_subtract(dx->u.bdd.zero_child, dy), 
		   rec_subtract(dx->u.bdd.one_child, dy)
		   )
	   ); 
    break; 
  case TYPE_CRD:
    if (dy->var_index == VAR[dx->var_index].U.CRD.CORRESPONDING_CDD_VI) {
      child_stack_level_push();
      for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	   cix >= 0 && ciy >= 0;
	   ){
	if (dy->u.ddd.arc[ciy].lower_bound > dx->u.crd.arc[cix].upper_bound)
	  ciy--;
	else if (dy->u.ddd.arc[ciy].upper_bound < dx->u.crd.arc[cix].upper_bound) {
	  bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
	else {
	  new_child = rec_subtract(dx->u.crd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
      }

      for (; cix >= 0; cix--) {
	bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
      }
      return(crd_new(dx->var_index));
    }
    else {
      cix = dx->u.crd.child_count-1; 
      if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) {
        child_stack_level_push();
        new_child = rec_subtract(dx->u.crd.arc[cix].child, dy); 
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
        for (cix--; cix >= 0; cix--) {
	  new_child = dx->u.crd.arc[cix].child;
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
        }
        return(crd_new(dx->var_index));
      }
      else 
        return(dx); 
    }
    break; 
  case TYPE_HDD:
    fprintf(RED_OUT, "\nError: a hybrid filter inequality is encountered.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_subtract(dx->u.lazy.false_child, dy), 
      rec_subtract(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	 dx->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(dx->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	 dx->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(dx->var_index));
    break; 

  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_subtract(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
	 dx->u.ddd.arc[cix].upper_bound
      );
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_subtract_left() */








struct red_type	*rec_subtract_try_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  int				dyi, b, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (VAR[dx->var_index].TYPE == TYPE_CDD) {
    fprintf(RED_OUT, "\nError: a dx with type filter inequality in rec_subtract() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (dy == NORM_NO_RESTRICTION || dx == dy)
    return(NORM_FALSE);
  else if (dy == NORM_FALSE)
    return(dx);

  ce = cache2_check_result_key(SUBTRACT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) 
    return(ce->result 
      = rec_subtract_left(dx, dy)
    );
  else if (dx->var_index > dy->var_index || dx == NORM_NO_RESTRICTION) {
    return(ce->result 
      = rec_subtract_right(dx, dy)
    ); 
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dx->var_index, 
	      rec_subtract(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
	      rec_subtract(dx->u.bdd.one_child, dy->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = 0, ciy = 0; cix < dx->u.crd.child_count; cix++) { 
      while (   ciy < dy->u.crd.child_count 
             && dx->u.crd.arc[cix].upper_bound 
                > dy->u.crd.arc[ciy].upper_bound
             ) 
        ciy++; 
      if (   ciy < dy->u.crd.child_count 
          && dx->u.crd.arc[cix].upper_bound 
             == dy->u.crd.arc[ciy].upper_bound
          ) 
        new_child = rec_subtract(dx->u.crd.arc[cix].child, 
          dy->u.crd.arc[ciy].child
        ); 
      else 
        new_child = dx->u.crd.arc[cix].child; 
      bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
    }
    return(crd_new(dx->var_index));
    break;
    fprintf(RED_OUT, "\nWARNING: inequality subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_HRD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality filter subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_subtract_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_subtract_right(dx, dy));
    }
    result = lazy_subtree(
      rec_subtract(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_subtract(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_subtract(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
	else
	  new_child = dx->u.fdd.arc[cix].child;

	fchild_stack_push(new_child, flb, fub);
      }
    }
    result = fdd_new(dx->var_index); 
    break; 
    
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_subtract(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
	else
	  new_child = dx->u.dfdd.arc[cix].child;

	dfchild_stack_push(new_child, dflb, dfub);
      }
    }
    result = dfdd_new(dx->var_index); 
    break; 
    
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_subtract(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	else
	  new_child = dx->u.ddd.arc[cix].child;

	ichild_stack_push(new_child, lb, ub);
      }
    }
    result = ddd_new(dx->var_index); 
  }
  return(ce->result = result); 
}
  /* rec_subtract() */






/*******************************
 *
 *  For EXTRACT, NORM_NO_RESTRICTION of clock inequalities is interpreted
 *	as (oo, oo) for dx while (-oo, oo) for dy.
 */
struct red_type		*rec_extract();

struct red_type	*rec_extract_right(dx, dy)
     struct red_type	*dx, *dy;
{
  int			ciy;
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dy->var_index, 
		   rec_extract(dx, dy->u.bdd.zero_child), 
		   rec_extract(dx, dy->u.bdd.one_child)
		   )
	   ); 
    break; 
  case TYPE_CDD:
    if (dy->u.ddd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_extract(dx, dy->u.ddd.arc[dy->u.ddd.child_count-1].child));
    else
      return(NORM_FALSE);
    break;
  case TYPE_CRD:
    bk("\nWarning: inequality right extraction is forbidden\n");
    break;
  case TYPE_HRD:
    bk("\nWarning: hybrid inequality right extraction is forbidden\n");
    break;
  case TYPE_HDD:
    bk("\nWarning: hybrid filter inequality right extraction is forbidden\n");
    break;
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_extract(dx, dy->u.lazy.false_child), 
      rec_extract(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 
  
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
    }
    return(fdd_new(dy->var_index));
    break; 
  
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
	dy->u.dfdd.arc[ciy].upper_bound
      );
    }
    return(dfdd_new(dy->var_index));
    break; 
  
  default:
    child_stack_level_push();
    for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.ddd.arc[ciy].child);
      ichild_stack_push(new_child, dy->u.ddd.arc[ciy].lower_bound,
				 dy->u.ddd.arc[ciy].upper_bound
				 );
    }
    return(ddd_new(dy->var_index));
  }
}
/* rec_extract_right() */





// int	count_extract_left = 0; 

struct red_type	*rec_extract_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, ciy;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dx->var_index, 
		   rec_extract(dx->u.bdd.zero_child, dy), 
		   rec_extract(dx->u.bdd.one_child, dy)
		   )
	   ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    if (dy->var_index == VAR[dx->var_index].U.CRD.CORRESPONDING_CDD_VI) {
      for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	   cix >= 0 && ciy >= 0;
	   ){
	if (dy->u.ddd.arc[ciy].lower_bound > dx->u.crd.arc[cix].upper_bound)
	  ciy--;
	else if (dy->u.ddd.arc[ciy].upper_bound < dx->u.crd.arc[cix].upper_bound) {
	  cix--;
	}
	else {
	  new_child = rec_extract(dx->u.crd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
      }
    }
    else {
      for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
	new_child = rec_extract(dx->u.crd.arc[cix].child, dy);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
      }
    }
    return(crd_new(dx->var_index));
    break;
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
    break;
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_extract(dx->u.lazy.false_child, dy), 
      rec_extract(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 
  case TYPE_FLOAT:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	dx->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(dx->var_index));
    break; 
  case TYPE_DOUBLE:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	dx->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(dx->var_index));
    break; 
  default:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
				 dx->u.ddd.arc[cix].upper_bound
				 );
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_extract_left() */




struct red_type	*rec_extract(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, dyi, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (VAR[dx->var_index].TYPE == TYPE_CDD) {
    fprintf(RED_OUT, "\nError: a dx with type filter inequality in rec_extract() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  if (dy == NORM_NO_RESTRICTION || dx == NORM_FALSE || dx == dy)
    return(dx);
  else if (dy == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(EXTRACT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index)
    return(ce->result
      = rec_extract_left(dx, dy)
    );
  else if (dx->var_index > dy->var_index || dx == NORM_NO_RESTRICTION)
    return(ce->result
      = rec_extract_right(dx, dy)
    );
  else switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dy->var_index, 
      rec_extract(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
      rec_extract(dx->u.bdd.one_child, dy->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    fprintf(RED_OUT, "\nWARNING: inequality extraction is forbidden\n");
    bk(); 
    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality extraction is forbidden\n");
    bk(); 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality filter extraction is forbidden\n");
    bk(); 
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_extract_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_extract_right(dx, dy));
    }
    result = lazy_subtree(
      rec_extract(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_extract(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
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
	    && fub <= dy->u.fdd.arc[ciy].upper_bound) {
	  new_child = rec_extract(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );

	fchild_stack_push(new_child, flb, fub);
      }
    }

    result = fdd_new(dx->var_index);
    break; 
    
  case TYPE_DOUBLE:
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
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound) {
	  new_child = rec_extract(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );

	dfchild_stack_push(new_child, dflb, dfub);
      }
    }

    result = dfdd_new(dx->var_index);
    break; 
    
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
         cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_extract(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);

	ichild_stack_push(new_child, lb, ub);
      }
    }

    result = ddd_new(dx->var_index);
  }

  return(ce->result = result);
}
  /* rec_extract() */





struct red_type	*rec_extract_right_try_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  int			cix, ciy;
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dy->var_index, 
		   rec_extract(dx, dy->u.bdd.zero_child), 
		   rec_extract(dx, dy->u.bdd.one_child)
		   )
	   ); 
    break; 
  case TYPE_CDD:
    if (dy->u.ddd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_extract(dx, dy->u.ddd.arc[dy->u.ddd.child_count-1].child));
    else
      return(NORM_FALSE);
    break;
  case TYPE_CRD:
    if (dx->var_index == VAR[dy->var_index].U.CRD.CORRESPONDING_CDD_VI) {
      child_stack_level_push();
      for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	   cix >= 0 && ciy >= 0;
	   ){
	if (dx->u.ddd.arc[cix].lower_bound > dy->u.crd.arc[ciy].upper_bound)
	  cix--;
	else if (dx->u.ddd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound) {
	  ciy--;
	}
	else {
	  new_child = rec_extract(dx->u.crd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[ciy].upper_bound);
	  ciy--; 
	}
      }
      return(crd_new(dy->var_index));
    }
    else {
      ciy = dy->u.crd.child_count-1; 
      if (dy->u.crd.arc[ciy].upper_bound == CLOCK_POS_INFINITY) {
        return (rec_extract(dx, dy->u.crd.arc[ciy].child));
      }
      else 
        return(NORM_FALSE); 
    }
    break;

  case TYPE_HRD:
    bk("\nWarning: hybrid inequality right extraction is forbidden\n");
    break;
  case TYPE_HDD:
    bk("\nWarning: hybrid filter inequality right extraction is forbidden\n");
    break;
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_extract(dx, dy->u.lazy.false_child), 
      rec_extract(dx, dy->u.lazy.true_child), 
      VAR[dy->var_index].PROC_INDEX, 
      dy->u.lazy.exp 
    ) ); 
    break; 
  
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
    }
    return(fdd_new(dy->var_index));
    break; 
  
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
	dy->u.dfdd.arc[ciy].upper_bound
      );
    }
    return(dfdd_new(dy->var_index));
    break; 
  
  default:
    child_stack_level_push();
    for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      new_child = rec_extract(dx, dy->u.ddd.arc[ciy].child);
      ichild_stack_push(new_child, dy->u.ddd.arc[ciy].lower_bound,
				 dy->u.ddd.arc[ciy].upper_bound
				 );
    }
    return(ddd_new(dy->var_index));
  }
}
/* rec_extract_right() */





// int	count_extract_left = 0; 

struct red_type	*rec_extract_left_try_intersect(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, ciy;
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(dx->var_index, 
		   rec_extract(dx->u.bdd.zero_child, dy), 
		   rec_extract(dx->u.bdd.one_child, dy)
		   )
	   ); 
    break; 
  case TYPE_CRD:
    if (dy->var_index == VAR[dx->var_index].U.CRD.CORRESPONDING_CDD_VI) {
      child_stack_level_push();
      for (cix = dx->u.crd.child_count - 1, ciy = dy->u.crd.child_count - 1;
	   cix >= 0 && ciy >= 0;
	   ){
	if (dy->u.ddd.arc[ciy].lower_bound > dx->u.crd.arc[cix].upper_bound)
	  ciy--;
	else if (dy->u.ddd.arc[ciy].upper_bound < dx->u.crd.arc[cix].upper_bound) {
	  cix--;
	}
	else {
	  new_child = rec_extract(dx->u.crd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	  cix--;
	}
      }
      return(crd_new(dx->var_index));
    }
    else {
      cix = dx->u.crd.child_count-1; 
      if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) {
        return (rec_extract(dx->u.crd.arc[cix].child, dy));
      }
      else 
        return(NORM_FALSE); 
    }
    break;
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
    break;
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_extract(dx->u.lazy.false_child, dy), 
      rec_extract(dx->u.lazy.true_child, dy), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp 
    ) ); 
    break; 
  case TYPE_FLOAT:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	dx->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(dx->var_index));
    break; 
  case TYPE_DOUBLE:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	dx->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(dx->var_index));
    break; 
  default:
/*
    fprintf(RED_OUT, "\nrec extract left %1d, %1d:%s\n", 
      ++count_extract_left, 
      dx->var_index, VAR[dx->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_extract(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
				 dx->u.ddd.arc[cix].upper_bound
				 );
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_extract_left() */




struct red_type	*rec_extract_try_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, dyi, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (VAR[dx->var_index].TYPE == TYPE_CDD) {
    fprintf(RED_OUT, "\nError: a dx with type filter inequality in rec_extract() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  if (dy == NORM_NO_RESTRICTION || dx == NORM_FALSE || dx == dy)
    return(dx);
  else if (dy == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(EXTRACT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index)
    return(ce->result
      = rec_extract_left(dx, dy)
    );
  else if (dx->var_index > dy->var_index || dx == NORM_NO_RESTRICTION)
    return(ce->result
      = rec_extract_right(dx, dy)
    );
  else switch (VAR[dx->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(dy->var_index, 
      rec_extract(dx->u.bdd.zero_child, dy->u.bdd.zero_child), 
      rec_extract(dx->u.bdd.one_child, dy->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = 0, ciy = 0; cix < dx->u.crd.child_count; cix++) { 
      while (   ciy < dy->u.crd.child_count 
             && dx->u.crd.arc[cix].upper_bound 
                > dy->u.crd.arc[ciy].upper_bound
             ) 
        ciy++; 
      if (   ciy < dy->u.crd.child_count 
          && dx->u.crd.arc[cix].upper_bound 
             == dy->u.crd.arc[ciy].upper_bound
          ) {
        new_child = rec_extract(dx->u.crd.arc[cix].child, 
          dy->u.crd.arc[ciy].child
        ); 
        bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
    } }
    return(crd_new(dx->var_index));
    break;

    fprintf(RED_OUT, "\nWARNING: inequality extraction is forbidden\n");
    bk(); 
    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality extraction is forbidden\n");
    bk(); 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality filter extraction is forbidden\n");
    bk(); 
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(dx->u.lazy.exp, dy->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_extract_left(dx, dy));
      else if (b > 0)
        return(ce->result = rec_extract_right(dx, dy));
    }
    result = lazy_subtree(
      rec_extract(dx->u.lazy.false_child, dy->u.lazy.false_child), 
      rec_extract(dx->u.lazy.true_child, dy->u.lazy.true_child), 
      VAR[dx->var_index].PROC_INDEX, 
      dx->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
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
	    && fub <= dy->u.fdd.arc[ciy].upper_bound) {
	  new_child = rec_extract(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );

	fchild_stack_push(new_child, flb, fub);
      }
    }

    result = fdd_new(dx->var_index);
    break; 
    
  case TYPE_DOUBLE:
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
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound) {
	  new_child = rec_extract(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );

	dfchild_stack_push(new_child, dflb, dfub);
      }
    }

    result = dfdd_new(dx->var_index);
    break; 
    
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
         cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_extract(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);

	ichild_stack_push(new_child, lb, ub);
      }
    }

    result = ddd_new(dx->var_index);
  }

  return(ce->result = result);
}
  /* rec_extract() */








struct red_type	*red_bop(op, dx, dy)
     int		op;
     struct red_type	*dx, *dy;
{
  struct red_type	*result;

  switch (op) {
  case AND:
/*
    flag_red_management++;
*/
    if (dx == NORM_FALSE || dy == NORM_FALSE) {
      return(NORM_FALSE);
    }
    else if (dx == NORM_NO_RESTRICTION) { 
      return(dy); 
    }
    else if (dy == NORM_NO_RESTRICTION) {
      return(dx);
    }
    else { 
//       fprintf(RED_OUT, "start rec_and() at root level.\n"); 
      result = rec_and(dx, dy); 
      return(result);  
    }
    break; 

  case INTERSECT:
    if (dx == NORM_FALSE || dy == NORM_FALSE) {
      return(NORM_FALSE);
    }
    else { 
      result = rec_intersect(dx, dy);
      return(result); 
    }
    break;
  case OR: 
    if (dx == NORM_NO_RESTRICTION || dy == NORM_NO_RESTRICTION) {
      return(NORM_NO_RESTRICTION);
    }
    else if (dx == NORM_FALSE) {
      return(dy); 
    }
    else if (dy == NORM_FALSE) {
      return(dx);
    }
    else {
      result = rec_or(dx, dy); 
      return(result); 
    } 
    break;
  case EXCLUDE:
    if (dx == NORM_FALSE) {
      return(NORM_FALSE);
    }
    else if (dy == NORM_FALSE) {
      return(dx);
    }
    else {
      result = rec_exclude(dx, dy); 
      return(result); 
    }
    break;
  case EXTRACT:
    if (dx == NORM_FALSE || dy == NORM_FALSE) {
      return(NORM_FALSE);
    }
    else if (dy == NORM_NO_RESTRICTION) {
      return(dx); 
    } 
    else {
      result = rec_extract(dx, dy); 
      return(result); 
    }
    break;
  case SUBTRACT:
    if (dx == NORM_FALSE || dy == NORM_NO_RESTRICTION) {
      return(NORM_FALSE);
    }
    else if (dy == NORM_FALSE) {
      return(dx);
    }
    else {
      result = rec_subtract(dx, dy);
      return(result); 
    }
    break;
  }
}
/* red_bop() */



// QQQQQQQQQQQQQQQQ ? this is problematic!
struct red_type	*red_eliminate_top_negative_cycles(d)
     struct red_type	*d; 
{
  int			ci, cj;
  struct red_type	*child;

  if (   d == NORM_FALSE
      || d == NORM_NO_RESTRICTION
      || VAR[d->var_index].TYPE != TYPE_CRD
      || (   VAR[d->var_index].TYPE == TYPE_CRD
	  && VAR[d->var_index].U.CRD.CLOCK1 
	     >= VAR[d->var_index].U.CRD.CLOCK2
	  )
      ) {
    return(d); 
  } 
  else {
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      if (   d->u.crd.arc[ci].child->var_index 
             != VAR[d->var_index].U.CRD.CONVERSE_CRD_VI
	  || d->u.crd.arc[ci].child->u.crd.arc[0].upper_bound 
	     + d->u.crd.arc[ci].upper_bound >= 0
	  ) {
	child = d->u.crd.arc[ci].child; 
      }
      else {
        child_stack_level_push();
	for (cj = 1; cj < d->u.crd.arc[ci].child->u.crd.child_count; cj++) {
	  if (d->u.crd.arc[ci].upper_bound + d->u.crd.arc[ci].child->u.crd.arc[cj].upper_bound >= 0)
	    bchild_stack_restrict(
	      VAR[d->var_index].U.CRD.CONVERSE_CRD_VI, 
	      d->u.crd.arc[ci].child->u.crd.arc[cj].child,
	      d->u.crd.arc[ci].child->u.crd.arc[cj].upper_bound
	    );
	}
	child = crd_new(VAR[d->var_index].U.CRD.CONVERSE_CRD_VI);
      }
      bchild_stack_restrict(
        VAR[d->var_index].U.CRD.CONVERSE_CRD_VI, 
        child, d->u.crd.arc[ci].upper_bound
      );
    }

    return(crd_new(d->var_index));
  }
}
/* red_eliminate_top_negative_cycles() */








/*******************************************************************************
 *
 */ 

struct red_type	*rec_untimed_subtract(d)
     struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child, *result;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) 
    return(NORM_FALSE); 
    
  ce = cache1_check_result_key(OP_UNTIMED_SUBTRACT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    ci = d->u.crd.child_count-1; 
    if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
      new_child = rec_untimed_subtract(d->u.crd.arc[ci].child); 
      bchild_stack_push(new_child, CLOCK_POS_INFINITY
				 );
      ci--; 
    } 
    for (; ci >= 0; ci--) { 
      bchild_stack_push(d->u.crd.arc[ci].child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break; 
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_untimed_subtract(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, 
	d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_untimed_subtract(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, 
	d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_untimed_subtract(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, 
				 d->u.ddd.arc[ci].lower_bound,
				 d->u.ddd.arc[ci].upper_bound
				 );
    }
    result = ddd_new(d->var_index);
    break; 
  }
  return(ce->result = result);
}
  /* rec_untimed_subtract() */




struct red_type	*zone_untimed_subtract(d) 
	struct red_type	*d; 
{
  struct red_type	*result, *t; 
  
  result = rec_untimed_subtract(d); 
  
  return(result); 
}
  /* zone_untimed_subtract() */ 



struct red_type	*rec_zone_subtract(); 

struct red_type	*rec_zone_subtract_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			ciy, lb, ub;
  float			flb, fub; 
  double		dflb, dfub; 
  struct red_type	*new_child, *new;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_CRD:
    if (dy->u.ddd.arc[dy->u.crd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_zone_subtract(dx, dy->u.ddd.arc[dy->u.crd.child_count-1].child));
    else
      return(dx);

  case TYPE_CDD:
    if (dy->u.ddd.arc[dy->u.ddd.child_count-1].upper_bound == CLOCK_POS_INFINITY)
      return(rec_zone_subtract(dx, dy->u.ddd.arc[dy->u.ddd.child_count-1].child));
    else
      return(dx);

    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HDD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality filter right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;


  case TYPE_FLOAT:
    child_stack_level_push();
    for (fub = VAR[dy->var_index].U.FLT.UB, ciy = dy->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (fub > dy->u.fdd.arc[ciy].upper_bound)
	fchild_stack_push(dx, 
	  feps_plus(dy->u.fdd.arc[ciy].upper_bound), fub
	);

      new_child = rec_zone_subtract(dx, dy->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound,
	dy->u.fdd.arc[ciy].upper_bound
      );
      fub = feps_minus(dy->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);

    return(fdd_new(dy->var_index));

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (dfub = VAR[dy->var_index].U.DBLE.UB, ciy = dy->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (dfub > dy->u.dfdd.arc[ciy].upper_bound)
	dfchild_stack_push(dx, 
	  dfeps_plus(dy->u.dfdd.arc[ciy].upper_bound), dfub
	);

      new_child = rec_zone_subtract(dx, dy->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound,
	dy->u.dfdd.arc[ciy].upper_bound
      );
      dfub = dfeps_minus(dy->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.DBLE.LB)
      dfchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(dy->var_index));

  default:
    child_stack_level_push();
    for (ub = VAR[dy->var_index].U.DISC.UB, ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > dy->u.ddd.arc[ciy].upper_bound)
	ichild_stack_push(dx, dy->u.ddd.arc[ciy].upper_bound+1, ub);

      new_child = rec_zone_subtract(dx, dy->u.ddd.arc[ciy].child);
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
/* rec_zone_subtract_right() */





struct red_type	*rec_zone_subtract_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, ciy, lb, ub;
  float			flb, fub; 
  double		dflb, dfub; 
  struct red_type	*new_child, *new;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    cix = dx->u.crd.child_count-1; 
    if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) { 
      new_child = rec_zone_subtract(dx->u.crd.arc[cix].child, dy); 
      bchild_stack_push(new_child, CLOCK_POS_INFINITY
				 );
      cix--; 
    } 
    for (; cix >= 0; cix--) { 
      bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
    }
    return(crd_new(dx->var_index));
  case TYPE_HDD:
    fprintf(RED_OUT, "\nError: a hybrid filter inequality is encountered.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_zone_subtract(dx->u.hrd.arc[cix].child, dy);
      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));
  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_zone_subtract(dx->u.fdd.arc[cix].child, dy);
      fchild_stack_push(new_child, dx->u.fdd.arc[cix].lower_bound,
	dx->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(dx->var_index));
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_zone_subtract(dx->u.dfdd.arc[cix].child, dy);
      dfchild_stack_push(new_child, dx->u.dfdd.arc[cix].lower_bound,
	dx->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(dx->var_index));
  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_zone_subtract(dx->u.ddd.arc[cix].child, dy);
      ichild_stack_push(new_child, dx->u.ddd.arc[cix].lower_bound,
				 dx->u.ddd.arc[cix].upper_bound
				 );
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_zone_subtract_left() */




struct red_type	*rec_zone_subtract(dx, dy)
     struct red_type	*dx, *dy;
{
  int				dyi, b, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result;
  struct rec_type		*rec, *nrec;
  struct cache2_hash_entry_type	*ce; 

  if (VAR[dx->var_index].TYPE == TYPE_CDD) {
    fprintf(RED_OUT, "\nError: a dx with type filter inequality in rec_zone_subtract() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (dx == dy)
    return(NORM_FALSE);
  else if (dy == NORM_FALSE)
    return(dx);

  ce = cache2_check_result_key(OP_ZONE_SUBTRACT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dy == NORM_NO_RESTRICTION) { 
    return(ce->result
      = zone_untimed_subtract(dx)
    ); 
  }
  else if (dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) {
    return(ce->result
      = rec_zone_subtract_left(dx, dy)
    );
  }
  else if (dx->var_index > dy->var_index || dx == NORM_NO_RESTRICTION) {
    return(ce->result
      = rec_zone_subtract_right(dx, dy)
    );
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count-1, ciy = dy->u.crd.child_count-1; 
         cix >= 0 && ciy >= 0; 
         ) { 
      for (; ciy >= 0 && dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound; ciy--); 
      if (ciy >= 0) {
      	if (dx->u.crd.arc[cix].upper_bound == dy->u.crd.arc[ciy].upper_bound) {
      	  new_child = rec_zone_subtract(dx->u.crd.arc[cix].child, dy->u.crd.arc[ciy].child);
	  bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	  cix--; 
	}
        for (; cix >= 0 && dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound; cix--) {
	  bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
        } 
      }
    } 
    for (; cix >= 0; cix--) {
      bchild_stack_push(dx->u.crd.arc[cix].child, dx->u.crd.arc[cix].upper_bound);
    } 
    result = crd_new(dx->var_index);
    break;
  case TYPE_HRD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;
  case TYPE_HDD:
    fprintf(RED_OUT, "\nWARNING: hybrid inequality filter subtraction is forbidden\n");
    fflush(RED_OUT);
    exit(0);
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound) {
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_zone_subtract(dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child);
	else
	  new_child = dx->u.fdd.arc[cix].child;

	fchild_stack_push(new_child, flb, fub);
      }
    }

    result = fdd_new(dx->var_index);

    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound) {
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_zone_subtract(dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child);
	else
	  new_child = dx->u.dfdd.arc[cix].child;

	dfchild_stack_push(new_child, dflb, dfub);
      }
    }

    result = dfdd_new(dx->var_index);

    break;

  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_zone_subtract(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	else
	  new_child = dx->u.ddd.arc[cix].child;

	ichild_stack_push(new_child, lb, ub);
      }
    }

    result = ddd_new(dx->var_index);

  }
  return(ce->result = result);
}
  /* rec_zone_subtract() */




struct red_type	*zone_subtract( dx, dy) 
	struct red_type	*dx, *dy; 
{
  struct red_type	*result, *t; 
  
  if (dx == NORM_FALSE) { 
    return(NORM_FALSE); 
  }
  else if (dy == NORM_NO_RESTRICTION) 
    return(zone_untimed_subtract(dx));
  else if (dy == NORM_FALSE) {
    return(dx); 
  }
  else {
    result = rec_zone_subtract(dx, dy);
    return(result); 
  }
}
  /* zone_subtract() */ 








int	ONE_CONSTRAINT_INDEX, 
	ONE_CONSTRAINT_UB, ONE_CONSTRAINT_LB;
float	FONE_CONSTRAINT_UB, FONE_CONSTRAINT_LB;
double	DFONE_CONSTRAINT_UB, DFONE_CONSTRAINT_LB;
struct red_type	*CRD_CONSTRAINT_ATOM; 

struct red_type	*rec_crd_one_constraint_ascending(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*result;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) {
/*
    if (CRD_CONSTRAINT_ATOM == NULL)
      CRD_CONSTRAINT_ATOM = crd_atom(
        ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB
      ); 
*/
    return(CRD_CONSTRAINT_ATOM);
  }
  else if (d->var_index > ONE_CONSTRAINT_INDEX) {
    if (   d->var_index 
           == VAR[ONE_CONSTRAINT_INDEX].U.CRD.CONVERSE_CRD_VI
        && d->u.crd.arc[d->u.crd.child_count-1].upper_bound 
           + ONE_CONSTRAINT_UB 
           < 0
        ) {
      if (d->u.crd.arc[0].upper_bound + ONE_CONSTRAINT_UB >= 0)
        return(NORM_FALSE);
      // We do not do the red_chref since d is a formal parameter. 
      if (VAR[d->var_index].U.CRD.CLOCK1 == TIME) 
        d = red_bop(EXTRACT, d, 
                  ddd_atom(VAR[d->var_index].U.CRD.CORRESPONDING_CDD_VI,
      		           -1*ONE_CONSTRAINT_UB, HYBRID_POS_INFINITY
      			   )
      		  ); 
      else 
        d = red_bop(EXTRACT, d, 
                  ddd_atom(VAR[d->var_index].U.CRD.CORRESPONDING_CDD_VI,
      		           -1*ONE_CONSTRAINT_UB, CLOCK_POS_INFINITY
      			   )
      		  ); 
      // Here we need red_chref to deref the red_bop(EXTRACT, ...) result. 
      return(crd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB));
    }
    else 
      return(crd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB));
  }
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(AND, d, CRD_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_crd_one_constraint_ascending(d->u.bdd.zero_child), 
      rec_crd_one_constraint_ascending(d->u.bdd.one_child)
    ); 
    break;  
  case TYPE_CRD:
    child_stack_level_push();
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      ci = d->u.crd.child_count - 1;
      if (d->u.crd.arc[ci].upper_bound <= ONE_CONSTRAINT_UB) {
      	child_stack_level_pop(); 
        return(ce->result = d);
      }
      result = NORM_FALSE;
      for (; ci >= 0 && d->u.crd.arc[ci].upper_bound >= ONE_CONSTRAINT_UB; ci--) {
	result = red_bop(OR, result, d->u.crd.arc[ci].child);
      }
      bchild_stack_restrict(
        VAR[ONE_CONSTRAINT_INDEX].U.CRD.CONVERSE_CRD_VI,
        result, ONE_CONSTRAINT_UB
      );
      for (; ci >= 0; ci--) {
	bchild_stack_restrict(
	  VAR[ONE_CONSTRAINT_INDEX].U.CRD.CONVERSE_CRD_VI,
	  d->u.crd.arc[ci].child,
	  d->u.crd.arc[ci].upper_bound
	);
      }
      result = crd_new(d->var_index);
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	result = rec_crd_one_constraint_ascending(d->u.crd.arc[ci].child);
	bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index);
    }
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_ascending(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_crd_one_constraint_ascending(d->u.lazy.false_child), 
      rec_crd_one_constraint_ascending(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT: 
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_ascending(d->u.fdd.arc[ci].child);
      fchild_stack_push(result,
      			d->u.fdd.arc[ci].lower_bound,
      			d->u.fdd.arc[ci].upper_bound
      			);
    }

    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_ascending(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(result,
      			d->u.dfdd.arc[ci].lower_bound,
      			d->u.dfdd.arc[ci].upper_bound
      			);
    }

    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_ascending(d->u.ddd.arc[ci].child);
      ichild_stack_push(result,
      			d->u.ddd.arc[ci].lower_bound,
      			d->u.ddd.arc[ci].upper_bound
      			);
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
  /* rec_crd_one_constraint_ascending() */



struct red_type	*rec_crd_one_constraint_descending(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*result;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) {
/*
    if (CRD_CONSTRAINT_ATOM == NULL)
      CRD_CONSTRAINT_ATOM = crd_atom(
        ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB
      ); 
*/
    return(CRD_CONSTRAINT_ATOM);
  }
  else if (d->var_index > ONE_CONSTRAINT_INDEX)
    return(crd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB));
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(AND, d, CRD_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_crd_one_constraint_descending(d->u.bdd.zero_child), 
      rec_crd_one_constraint_descending(d->u.bdd.one_child)
    ); 
    break;  
  case TYPE_CRD:
    child_stack_level_push();
    if (d->var_index == VAR[ONE_CONSTRAINT_INDEX].U.CRD.CONVERSE_CRD_VI) {
      for (ci = d->u.crd.child_count-1;
      	   ci >= 0 && d->u.crd.arc[ci].upper_bound + ONE_CONSTRAINT_UB >= 0;
      	   ci--
      	   ) {
	result = rec_crd_one_constraint_descending(d->u.crd.arc[ci].child);
	bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index);
    }
    else if (d->var_index == ONE_CONSTRAINT_INDEX) {
      ci = d->u.crd.child_count - 1;
      if (d->u.crd.arc[ci].upper_bound <= ONE_CONSTRAINT_UB) {
      	child_stack_level_pop(); 
        return(ce->result = d);
      }
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1;
	   ci >= 0 && d->u.crd.arc[ci].upper_bound >= ONE_CONSTRAINT_UB;
	   ci--
	   ) {
	result = red_bop(OR, result, d->u.crd.arc[ci].child);
      }
      bchild_stack_push(result, ONE_CONSTRAINT_UB);
      for (; ci >= 0; ci--) {
	bchild_stack_push(d->u.crd.arc[ci].child,
	  d->u.crd.arc[ci].upper_bound
	);
      }
      result = crd_new(d->var_index);
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	result = rec_crd_one_constraint_descending(d->u.crd.arc[ci].child);
	bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index);
    }
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_descending(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, 
        d->u.hrd.arc[ci].ub_numerator,
      	d->u.hrd.arc[ci].ub_denominator
      );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_crd_one_constraint_descending(d->u.lazy.false_child), 
      rec_crd_one_constraint_descending(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_descending(d->u.fdd.arc[ci].child);
      fchild_stack_push(result, 
	d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }

    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_descending(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(result, 
	d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_crd_one_constraint_descending(d->u.ddd.arc[ci].child);
      ichild_stack_push(result, 
	d->u.ddd.arc[ci].lower_bound,
	d->u.ddd.arc[ci].upper_bound
      );
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
  /* rec_crd_one_constraint_descending() */



extern int	count_bpD; 

struct red_type	*crd_one_constraint(d, zvi, b)
     struct red_type	*d;
     int		zvi, b;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);
/*
  if (count_bpD == 5) 
    print_cpu_time("entering crd constraint"); 
*/
  ONE_CONSTRAINT_INDEX = zvi;
  ONE_CONSTRAINT_UB = b;
  CRD_CONSTRAINT_ATOM = crd_atom(
    ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_UB
  ); 
  if (VAR[zvi].U.CRD.CLOCK1 < VAR[zvi].U.CRD.CLOCK2)
    result = rec_crd_one_constraint_ascending(d);
  else
    result = rec_crd_one_constraint_descending(d);
/*
  if (count_bpD == 5) 
    print_cpu_time("leaving crd constraint"); 
*/
  return(result);
}
/* crd_one_constraint() */




struct red_type	*BDD_CONSTRAINT_ATOM; 

struct red_type	*rec_bdd_one_constraint(d)
     struct red_type	*d;
{
  int				ci, ub, lb;
  struct red_type		*result;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);
  else if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(bdd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_LB));

  ce = cache2_check_result_key(AND, d, BDD_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (d->var_index != ONE_CONSTRAINT_INDEX) { 
      result = bdd_new(d->var_index, 
        rec_bdd_one_constraint(d->u.bdd.zero_child), 
        rec_bdd_one_constraint(d->u.bdd.one_child)
      ); 
    } 
    else if (ONE_CONSTRAINT_LB == TYPE_FALSE) { 
      if (d->u.bdd.zero_child == NORM_FALSE) 
        result = NORM_FALSE; 
      else 
        result = bdd_lone_subtree(d->u.bdd.zero_child, 
          ONE_CONSTRAINT_INDEX, TYPE_FALSE
        ); 
    } 
    else { 
      if (d->u.bdd.one_child == NORM_FALSE) 
        result = NORM_FALSE; 
      else 
        result = bdd_lone_subtree(d->u.bdd.one_child, 
          ONE_CONSTRAINT_INDEX, TYPE_TRUE
        ); 
    } 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = rec_bdd_one_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_bdd_one_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_bdd_one_constraint(d->u.lazy.false_child), 
      rec_bdd_one_constraint(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_bdd_one_constraint(d->u.fdd.arc[ci].child);
      fchild_stack_push(result,
        d->u.fdd.arc[ci].lower_bound,
        d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_bdd_one_constraint(d->u.dfdd.arc[ci].child);
      fchild_stack_push(result,
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_bdd_one_constraint(d->u.ddd.arc[ci].child);
      ichild_stack_push(result,
        d->u.ddd.arc[ci].lower_bound,
        d->u.ddd.arc[ci].upper_bound
      );
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
  /* rec_bdd_one_constraint() */


struct red_type	*bdd_one_constraint(d, vi, value)
     struct red_type	*d;
     int		vi, value;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);
  else switch (VAR[vi].TYPE) { 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    break; 
  default: 
    fprintf(RED_OUT, "Error: A clock inequality in bdd_one_constraint(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  if (value < TYPE_FALSE || value > TYPE_TRUE) { 
    return(NORM_FALSE); 
  } 
  ONE_CONSTRAINT_INDEX = vi;
  ONE_CONSTRAINT_UB = ONE_CONSTRAINT_LB = value;
  
  BDD_CONSTRAINT_ATOM = bdd_atom(vi, ONE_CONSTRAINT_LB); 
  result = rec_bdd_one_constraint(d);
  return(result);
}
/* bdd_one_constraint() */




struct red_type	*bdd_2_constraints(
  struct red_type	*false_child, 
  struct red_type	*true_child, 
  int			vi
) { 
  switch (VAR[vi].TYPE) { 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    break; 
  default: 
    fprintf(RED_OUT, "Error: A clock inequality in bdd_2_constraints(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/ 
  false_child = bdd_one_constraint(false_child, vi, TYPE_FALSE); 
  true_child = bdd_one_constraint(true_child, vi, TYPE_TRUE); 
  return(red_bop(OR, false_child, true_child)); 
}
  /* bdd_2_constraints() */






struct red_type	*rec_fdd_one_constraint(d)
     struct red_type	*d;
{
  int				ci; 
  float				ub, lb;
  struct red_type		*result;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);
  else if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(fdd_lone_subtree(d, ONE_CONSTRAINT_INDEX, FONE_CONSTRAINT_LB, FONE_CONSTRAINT_UB));

  ce = cache4_check_result_key(OP_DDD_ONE_CONSTRAINT, d, 
    (struct hrd_exp_type *) ONE_CONSTRAINT_INDEX, 
    FONE_CONSTRAINT_LB, FONE_CONSTRAINT_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 


  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_fdd_one_constraint(d->u.bdd.zero_child), 
      rec_fdd_one_constraint(d->u.bdd.one_child)
    ); 
    break;  
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = rec_fdd_one_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_fdd_one_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_fdd_one_constraint(d->u.lazy.false_child), 
      rec_fdd_one_constraint(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      for (ci = d->u.fdd.child_count-1;
	   ci >= 0 && d->u.fdd.arc[ci].upper_bound >= FONE_CONSTRAINT_LB;
	   ci--
	   ) {
	if (d->u.fdd.arc[ci].upper_bound <= FONE_CONSTRAINT_UB)
	  ub = d->u.fdd.arc[ci].upper_bound;
	else
	  ub = FONE_CONSTRAINT_UB;
	if (d->u.fdd.arc[ci].lower_bound >= FONE_CONSTRAINT_LB)
	  lb = d->u.fdd.arc[ci].lower_bound;
	else
	  lb = FONE_CONSTRAINT_LB;
	if (lb <= ub) {
	  result = d->u.fdd.arc[ci].child;
	  fchild_stack_push(result, lb, ub);
	}
      }
    }
    else {
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	result = rec_fdd_one_constraint(d->u.fdd.arc[ci].child);
	fchild_stack_push(result,
      	  d->u.fdd.arc[ci].lower_bound,
      	  d->u.fdd.arc[ci].upper_bound
      	);
      }
    }
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_fdd_one_constraint(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(result,
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_fdd_one_constraint(d->u.ddd.arc[ci].child);
      ichild_stack_push(result,
        d->u.ddd.arc[ci].lower_bound,
        d->u.ddd.arc[ci].upper_bound
      );
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
  /* rec_fdd_one_constraint() */


struct red_type	*fdd_one_constraint(
  struct red_type	*d, 
  int			vi,  
  float 		lb, 
  float 		ub
) {
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);
  else switch (VAR[vi].TYPE) { 
  case TYPE_FLOAT: 
    break; 
  default: 
    if (vi == FLOAT_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: A clock inequality in ddd_atom(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  ONE_CONSTRAINT_INDEX = vi;
/*
  fprintf(RED_OUT, "\nIn fdd_one_c: lb=%.4f\n", lb); 
  fprintf(RED_OUT, "In fdd_one_c: ub=%.4f\n", ub); 
*/
  FONE_CONSTRAINT_UB = flt_min(ub, VAR[vi].U.FLT.UB);
  FONE_CONSTRAINT_LB = flt_max(lb, VAR[vi].U.FLT.LB);
  if (FONE_CONSTRAINT_LB > FONE_CONSTRAINT_UB) 
    return(NORM_FALSE); 
  
  result = rec_fdd_one_constraint(d);
  return(result);
}
/* fdd_one_constraint() */





struct red_type	*rec_dfdd_one_constraint(d)
     struct red_type	*d;
{
  int				ci, lb1, lb2, ub1, ub2; 
  double			ub, lb;
  struct red_type		*result;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);
  else if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(dfdd_lone_subtree(d, 
      ONE_CONSTRAINT_INDEX, DFONE_CONSTRAINT_LB, DFONE_CONSTRAINT_UB
    ) );

  lb1 = ((int *) &lb)[0]; 
  lb2 = ((int *) &lb)[1]; 
  ub1 = ((int *) &ub)[0]; 
  ub2 = ((int *) &ub)[1]; 
  ce = cache7_check_result_key(
    OP_DDD_ONE_CONSTRAINT_DOUBLE, d, 
    (struct hrd_exp_type *) lb1, lb2, ub1, 
    (struct hrd_exp_type *) ub2, 0, 0
  ); 
  if (ce->result) {
    return(ce->result); 
  } 


  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_dfdd_one_constraint(d->u.bdd.zero_child), 
      rec_dfdd_one_constraint(d->u.bdd.one_child)
    ); 
    break;  
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = rec_dfdd_one_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_dfdd_one_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_dfdd_one_constraint(d->u.lazy.false_child), 
      rec_dfdd_one_constraint(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_dfdd_one_constraint(d->u.fdd.arc[ci].child);
      dfchild_stack_push(result,
        d->u.fdd.arc[ci].lower_bound,
        d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      for (ci = d->u.dfdd.child_count-1;
	   ci >= 0 && d->u.dfdd.arc[ci].upper_bound >= DFONE_CONSTRAINT_LB;
	   ci--
	   ) {
	if (d->u.dfdd.arc[ci].upper_bound <= DFONE_CONSTRAINT_UB)
	  ub = d->u.dfdd.arc[ci].upper_bound;
	else
	  ub = DFONE_CONSTRAINT_UB;
	if (d->u.dfdd.arc[ci].lower_bound >= DFONE_CONSTRAINT_LB)
	  lb = d->u.dfdd.arc[ci].lower_bound;
	else
	  lb = DFONE_CONSTRAINT_LB;
	if (lb <= ub) {
	  result = d->u.dfdd.arc[ci].child;
	  dfchild_stack_push(result, lb, ub);
	}
      }
    }
    else {
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	result = rec_dfdd_one_constraint(d->u.dfdd.arc[ci].child);
	dfchild_stack_push(result,
      	  d->u.dfdd.arc[ci].lower_bound,
      	  d->u.dfdd.arc[ci].upper_bound
      	);
      }
    }
    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_dfdd_one_constraint(d->u.ddd.arc[ci].child);
      ichild_stack_push(result,
        d->u.ddd.arc[ci].lower_bound,
        d->u.ddd.arc[ci].upper_bound
      );
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
  /* rec_dfdd_one_constraint() */


struct red_type	*dfdd_one_constraint(
     struct red_type	*d, 
     int		vi,  
     double 		lb, 
     double		ub
) {
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);
  else switch (VAR[vi].TYPE) { 
  case TYPE_DOUBLE: 
    break; 
  default: 
    if (vi == DOUBLE_VALUE) 
      break; 
    fprintf(RED_OUT, "Error: A clock inequality in ddd_atom(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  ONE_CONSTRAINT_INDEX = vi;
  DFONE_CONSTRAINT_UB = dble_min(ub, VAR[vi].U.DBLE.UB);
  DFONE_CONSTRAINT_LB = dble_max(lb, VAR[vi].U.DBLE.LB);
  if (DFONE_CONSTRAINT_LB > DFONE_CONSTRAINT_UB) 
    return(NORM_FALSE); 
  
  result = rec_dfdd_one_constraint(d);
  return(result);
}
/* dfdd_one_constraint() */







struct red_type	*rec_ddd_one_constraint(d)
     struct red_type	*d;
{
  int				ci, ub, lb;
  struct red_type		*result;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);
  else if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(ddd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_LB, ONE_CONSTRAINT_UB));

  ce = cache4_check_result_key(OP_DDD_ONE_CONSTRAINT, 
    d, (struct hrd_exp_type *) ONE_CONSTRAINT_INDEX, 
    ONE_CONSTRAINT_LB, ONE_CONSTRAINT_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 


  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_ddd_one_constraint(d->u.bdd.zero_child), 
      rec_ddd_one_constraint(d->u.bdd.one_child)
    ); 
    break;  
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = rec_ddd_one_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(result, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_ddd_one_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(result, d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_ddd_one_constraint(d->u.lazy.false_child), 
      rec_ddd_one_constraint(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_ddd_one_constraint(d->u.fdd.arc[ci].child);
      fchild_stack_push(result,
        d->u.fdd.arc[ci].lower_bound,
        d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_ddd_one_constraint(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(result,
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      for (ci = d->u.ddd.child_count-1;
	   ci >= 0 && d->u.ddd.arc[ci].upper_bound >= ONE_CONSTRAINT_LB;
	   ci--
	   ) {
	if (d->u.ddd.arc[ci].upper_bound <= ONE_CONSTRAINT_UB)
	  ub = d->u.ddd.arc[ci].upper_bound;
	else
	  ub = ONE_CONSTRAINT_UB;
	if (d->u.ddd.arc[ci].lower_bound >= ONE_CONSTRAINT_LB)
	  lb = d->u.ddd.arc[ci].lower_bound;
	else
	  lb = ONE_CONSTRAINT_LB;
	if (lb <= ub) {
	  result = d->u.ddd.arc[ci].child;
	  ichild_stack_push(result, lb, ub);
	}
      }
    }
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	result = rec_ddd_one_constraint(d->u.ddd.arc[ci].child);
	ichild_stack_push(result,
      	  d->u.ddd.arc[ci].lower_bound,
      	  d->u.ddd.arc[ci].upper_bound
      	);
      }
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
  /* rec_ddd_one_constraint() */


struct red_type	*ddd_one_constraint( 
     struct red_type	*d, 
     int		vi, 
     int		lb, 
     int		ub
) {
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);
  else switch (VAR[vi].TYPE) { 
  case TYPE_FALSE: 
  case TYPE_TRUE: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
  case TYPE_CRD: 
  case TYPE_HRD: 
  case TYPE_HDD: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "Error: A clock inequality in ddd_atom(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0);
  }

/*
  fprintf(RED_OUT, "ddd_one_constraint vi=%1d\n", vi); 
  fprintf(RED_OUT, "ddd_one_constraint VAR[vi].UB=%1d\n", VAR[vi].UB); 
  fprintf(RED_OUT, "ddd_one_constraint ub=%1d\n", ub); 
  fflush(RED_OUT); 
*/
  ONE_CONSTRAINT_INDEX = vi;
  ONE_CONSTRAINT_UB = int_min(ub, VAR[vi].U.DISC.UB);
  ONE_CONSTRAINT_LB = int_max(lb, VAR[vi].U.DISC.LB);
  if (ONE_CONSTRAINT_LB > ONE_CONSTRAINT_UB) 
    return(NORM_FALSE); 
  
  result = rec_ddd_one_constraint(d);
  return(result);
}
/* ddd_one_constraint() */







struct red_type	*rec_ddd_project_through_one_constraint(d)
     struct red_type	*d;
{
  int				ci, ub, lb;
  struct red_type		*new_child, *result;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(ddd_lone_subtree(d, ONE_CONSTRAINT_INDEX, ONE_CONSTRAINT_LB, ONE_CONSTRAINT_UB));
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_DDD_PROJECT_THROUGH_ONE_CONSTRAINT, d, 
    (struct hrd_exp_type *) ONE_CONSTRAINT_INDEX, 
    ONE_CONSTRAINT_LB, ONE_CONSTRAINT_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bchild_stack_push(
        rec_ddd_project_through_one_constraint(d->u.crd.arc[ci].child), 
        d->u.crd.arc[ci].upper_bound
      ); 
    } 
    result = crd_new(d->var_index); 
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hchild_stack_push(
          rec_ddd_project_through_one_constraint(d->u.hrd.arc[ci].child), 
	  d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator 
      ); 
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
	rec_ddd_project_through_one_constraint(d->u.fdd.arc[ci].child), 
      	d->u.fdd.arc[ci].lower_bound,
      	d->u.fdd.arc[ci].upper_bound
      );
    }
    new_child = fdd_new(d->var_index);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
	rec_ddd_project_through_one_constraint(d->u.dfdd.arc[ci].child), 
      	d->u.dfdd.arc[ci].lower_bound,
      	d->u.dfdd.arc[ci].upper_bound
      );
    }
    new_child = dfdd_new(d->var_index);
    break;

  default:
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      for (ci = d->u.ddd.child_count-1;
	   ci >= 0 && d->u.ddd.arc[ci].upper_bound >= ONE_CONSTRAINT_LB;
	   ci--
	   ) {
	if (d->u.ddd.arc[ci].upper_bound <= ONE_CONSTRAINT_UB)
	  ub = d->u.ddd.arc[ci].upper_bound;
	else
	  ub = ONE_CONSTRAINT_UB;
	if (d->u.ddd.arc[ci].lower_bound >= ONE_CONSTRAINT_LB)
	  lb = d->u.ddd.arc[ci].lower_bound;
	else
	  lb = ONE_CONSTRAINT_LB;
	if (lb <= ub) {
	  result = red_bop(OR, result, d->u.ddd.arc[ci].child); 
	}
      }
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ichild_stack_push(
	  rec_ddd_project_through_one_constraint(d->u.ddd.arc[ci].child), 
      	  d->u.ddd.arc[ci].lower_bound,
      	  d->u.ddd.arc[ci].upper_bound
      	);
      }
      new_child = ddd_new(d->var_index);
    }
  }
  return(ce->result = result);
}
  /* rec_ddd_project_through_one_constraint() */


struct red_type	*ddd_project_through_one_constraint(d, vi, lb, ub)
     struct red_type	*d;
     int		vi, lb, ub;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

  ONE_CONSTRAINT_INDEX = vi;
  ONE_CONSTRAINT_UB = int_min(ub, VAR[vi].U.DISC.UB);
  ONE_CONSTRAINT_LB = int_max(lb, VAR[vi].U.DISC.LB);
  if (ONE_CONSTRAINT_LB > ONE_CONSTRAINT_UB) 
    return(NORM_FALSE); 
  
  result = rec_ddd_project_through_one_constraint(d);
  return(result);
}
/* ddd_project_through_one_constraint() */



struct red_type	*ddd_root_one_child(d, vi, value) 
	struct red_type	*d; 
	int		vi, value; 
{
  int	ci; 
  
  if (d->var_index != vi) { 
    fprintf(RED_OUT, "Error: the root var %1d:%s is incompatible with the operand vi %1d:%s.\n", 
	    d->var_index, VAR[d->var_index].NAME, vi, VAR[vi].NAME
	    ); 
    bk(" "); 
  }
  for (ci = 0; ci < d->u.ddd.child_count && value < d->u.ddd.arc[ci].lower_bound; ci++) ; 
  
  if (ci < d->u.ddd.child_count && value <= d->u.ddd.arc[ci].upper_bound) 
    return(d->u.ddd.arc[ci].child); 
  else 
    return(NORM_FALSE); 
}
  /* ddd_root_one_child() */  




/*************************************************************************************
 * The basic algorithm is as follows. 
 * Assume d = (i1 && d1) || .... || (in && dn).  
 * not d = ((not i1)||(not d1))&&...&&((not in)||(not dn))
 *       = ((not d1)&&...&&(not dn))||(not i1)||(not i2)||...||(not in).  
 */


/* Keep red untouched and make a new not red. */
struct red_type	*rec_complement(struct red_type *d) 
{
  int				ci, c1, c2, ub_numerator, ub_denominator, 
				lb, ub, tmp; 
  float				flb, fub; 
  double 			dflb, dfub; 
  struct red_type		*child, *acc, *result;
  struct ddd_child_type		*ic, *jc;
  struct ddd_child_link_type	*nic;
  struct hrd_exp_type		*converse_he;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE) {
    return(NORM_TRUE);
  }
  else if (d->var_index == TYPE_TRUE) {
    return(NORM_FALSE);
  }

  ce = cache1_check_result_key(OP_COMPLEMENT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
        rec_complement(d->u.bdd.zero_child), 
	rec_complement(d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD:
    result = NORM_FALSE; 
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    ci = d->u.crd.child_count-1; 
    acc = NORM_FALSE; 
    if (!c1) /* The result expression is like 0-c2. 
              * The upperbound must be <= 0 
              * if c2 is neither NEG_DELTA nor NEG_DELTAP. 
              */ {
      if (c2 == NEG_DELTA || c2 == NEG_DELTAP) {
        /* assume we have 0--delta << b && D ==> delta << b && D
         * complement -->  delta >> b+1 || ~D 
         *                -delta << -b-1 || ~D
         * 
         * case 1, if b <<-1, delta >> b+1 is a tautology.  
         *         we do not need to complement the child. 
         *         i.e., we need to construct nothing.  
         * case 2, if b >> 0, delta >> b+1 is meaningful.  
         *         we need to complement the child.  
         *         i.e., we need to construct delta>=0 || ~D.  
         */ 
        if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
          acc = rec_complement(d->u.crd.arc[ci].child); 
          ci--;  
        } 
        else 
          acc = NORM_NO_RESTRICTION; 
        for (; 
                ci >= 0 
             && acc != NORM_FALSE
             && d->u.crd.arc[ci].upper_bound >= 0; 
             ci--
             ) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
	  result = red_bop(OR, result, 
	    crd_one_constraint(acc, ZONE[c2][0], ub) /* acc && (c2-0<=ub) */ 
	  );
	  
          acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child));
        }
      }
      else {
        acc = crd_atom(ZONE[0][c2], 0);  
        for (; 
                ci >= 0 
             && acc != NORM_FALSE 
             && d->u.crd.arc[ci].upper_bound >=0; 
             ci--
             ) {
          acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child)); 
        }
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
	  if (ub >= 0) {
	    result = red_bop(OR, result, crd_one_constraint(acc, ZONE[c2][0], ub));
	  } 
          acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child));
        }
      } 
      result = red_bop(OR, result, acc); 
    } 
    else if (!c2) /* Th result expression is like 0-c1.  The upperbound must be <= 0 */ { 
      if (c1 == NEG_DELTA || c1 == NEG_DELTAP) { 
        /* assume we have -delta-0 << b && D ==> delta >> -b && D
         * complement --> we have 
         *           delta << -b-1 || ~D 
         *    ==> 0--delta << -b-1 || ~D
         * 
         * case 1, if b << -1, delta <= -b is meaningful.  
         *         we need to complement the child. 
         *         i.e., we need to construct 
         *               -delta >= b || ~D ==> 0--delta <= -b || ~D.  
         * case 2, if b >> 0, delta <= -b is a contradiction.  
         *         we only need to complement the child.  
         *         i.e., we need to construct ~D.  
         */ 
        acc = NORM_NO_RESTRICTION; 
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          if (d->u.crd.arc[ci].upper_bound < 0) {
            result = red_bop(OR, result, crd_one_constraint
	                     (acc, ZONE[0][c1], 
	                      -1 - d->u.crd.arc[ci].upper_bound
	                      ));  
          } 
          acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child));
        }
        result = red_bop(OR, result, acc);       
      }
      else {
        if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
          acc = rec_complement(d->u.crd.arc[ci].child); 
          ci--;  
        } 
        else 
          acc = NORM_NO_RESTRICTION; 
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
          if (ub <= 0) {
            result = red_bop(OR, result, crd_one_constraint(acc, ZONE[0][c1], ub));
	  } 
	  acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child));
        }
        result = red_bop(OR, result, crd_one_constraint(acc, ZONE[0][c1], 0));  
      }
    }
    else /* The result expression is like c2-c1.  No restrictions on upperbound. */ { 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
        acc = rec_complement(d->u.crd.arc[ci].child); 
        ci--;  
      } 
      else 
        acc = NORM_NO_RESTRICTION; 
      for (; ci >= 0 && acc != NORM_FALSE; ci--) {
        ub = -1 - d->u.crd.arc[ci].upper_bound;
	result = red_bop(OR, result, crd_one_constraint(acc, ZONE[c2][c1], ub));
	
        acc = red_bop(AND, acc, rec_complement(d->u.crd.arc[ci].child));
      }
      result = red_bop(OR, result, acc); 
    } 
    /*
    fprintf(RED_OUT, "\n==========================\nIn rec_complement(d=%1x)\n", d);
    red_print_graph(d);
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nIn the middle of rec_complement(result) for d=%1x\n", d);
    red_print_graph(result);
    fflush(RED_OUT);
    */
    break;

  case TYPE_HRD:
    result = NORM_FALSE; 
    ci = d->u.hrd.child_count-1; 
    converse_he = hrd_exp_converse(d->u.hrd.hrd_exp);
    ub_numerator = d->u.hrd.arc[ci].ub_numerator;
    if (ub_numerator == HYBRID_POS_INFINITY && d->u.hrd.arc[ci].ub_denominator == 1) {
      acc = rec_complement(d->u.hrd.arc[ci].child); 
      ci--;  
    } 
    else 
      acc = NORM_NO_RESTRICTION; 
    for (; 
            ci >= 0 
         && acc != NORM_FALSE 
         && (   d->u.hrd.arc[ci].ub_numerator > HYBRID_NEG_INFINITY+1 
             || d->u.hrd.arc[ci].ub_denominator > 1
             ); 
         ci--
         ) {
      ub_numerator = -1 - d->u.hrd.arc[ci].ub_numerator;
      result = red_bop(OR, result, hrd_one_constraint(acc, converse_he, 
		ub_numerator, d->u.hrd.arc[ci].ub_denominator
	      ));
      
      acc = red_bop(AND, acc, rec_complement(d->u.hrd.arc[ci].child));
    }
    result = red_bop(OR, result, acc); 
    /*
    fprintf(RED_OUT, "\n==========================\nIn rec_complement(d=%1x)\n", d);
    red_print_graph(d);
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nIn the middle of rec_complement(result) for d=%1x\n", d);
    red_print_graph(result);
    fflush(RED_OUT);
    */
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_complement(d->u.lazy.false_child), 
      rec_complement(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    fub = VAR[d->var_index].U.FLT.UB; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      if (fub > d->u.fdd.arc[ci].upper_bound) { 
	fchild_stack_push(NORM_NO_RESTRICTION, 
	  feps_plus(d->u.fdd.arc[ci].upper_bound), fub
	); 
      } 
      fchild_stack_push(
      	rec_complement(d->u.fdd.arc[ci].child),  
	d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound 
      ); 
      fub = feps_minus(d->u.fdd.arc[ci].lower_bound); 
    }
    if (fub >= VAR[d->var_index].U.FLT.LB) { 
      fchild_stack_push(NORM_NO_RESTRICTION, 
        VAR[d->var_index].U.FLT.LB, fub
      ); 
    } 
    result = fdd_new(d->var_index);
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    dfub = VAR[d->var_index].U.DBLE.UB; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      if (dfub > d->u.dfdd.arc[ci].upper_bound) { 
	dfchild_stack_push(NORM_NO_RESTRICTION, 
	  dfeps_plus(d->u.dfdd.arc[ci].upper_bound), dfub
	); 
      } 
      fchild_stack_push(
      	rec_complement(d->u.dfdd.arc[ci].child),  
	d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound 
      ); 
      dfub = dfeps_minus(d->u.dfdd.arc[ci].lower_bound); 
    }
    if (dfub >= VAR[d->var_index].U.DBLE.LB) { 
      dfchild_stack_push(NORM_NO_RESTRICTION, 
        VAR[d->var_index].U.DBLE.LB, dfub
      ); 
    } 
    result = dfdd_new(d->var_index);
    break; 

  default:
    child_stack_level_push();
    ub = VAR[d->var_index].U.DISC.UB; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      if (ub > d->u.ddd.arc[ci].upper_bound) { 
	ichild_stack_push(NORM_NO_RESTRICTION, 
	  d->u.ddd.arc[ci].upper_bound+1, ub
	); 
      } 
      ichild_stack_push(
      	rec_complement(d->u.ddd.arc[ci].child),  
	d->u.ddd.arc[ci].lower_bound, 
	d->u.ddd.arc[ci].upper_bound 
      ); 
      ub = d->u.ddd.arc[ci].lower_bound-1; 
    }
    if (ub >= VAR[d->var_index].U.DISC.LB) { 
      ichild_stack_push(NORM_NO_RESTRICTION, 
        VAR[d->var_index].U.DISC.LB, ub
      ); 
    } 
    result = ddd_new(d->var_index);
  }
/*
  fprintf(RED_OUT, "\n**********(new complement intermediate result)*************\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "--------------------------\n"); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
  /* rec_complement() */




struct red_type	*red_complement(d)
     struct red_type	*d;
{
  struct red_type	*result;

  /*
  fprintf(RED_OUT, "\nstarting a red_complement(d=%1x)----------------------------------------------\n", d);
  */
  result = rec_complement(d);
  /*
  fprintf(RED_OUT, "\nstopping a red_complement(d=%1x)+++++++++++++++++++++++++++++++++++++++++++++\n", d);
  */

  return(result);
}
/* red_complement() */







/*************************************************************************************
 * The basic algorithm is as follows. 
 * Assume d = (i1 && d1) || .... || (in && dn).  
 * not d = ((not i1)||(not d1))&&...&&((not in)||(not dn))
 *       = ((not d1)&&...&&(not dn))||(not i1)||(not i2)||...||(not in).  
 */


/* Keep red untouched and make a new not red. */
struct red_type	*rec_space_subtract(
  struct red_type *, 
  struct red_type *
); 

struct red_type *rec_space_subtract_slub_dlb(
  struct red_type	*s, 
  int			c1, 
  int			c2, 
  int			snlb, 
  struct red_type	*d
) {
  int			ci; 
  struct red_type	*result, *conj; 

  if (ZONE[c2][c1] == d->var_index) {
    result = s; 
    for (ci = d->u.crd.child_count-1; ci >=0 && result != NORM_FALSE; ci--) {
      if (d->u.crd.arc[ci].upper_bound + snlb < 0) 
        break; 
      else if (d->u.crd.arc[ci].upper_bound > CLOCK_POS_INFINITY) {
	conj = rec_space_subtract(s, d->u.crd.arc[ci].child);  
        conj = crd_one_constraint(conj, ZONE[c1][c2], 0); 
        conj = crd_one_constraint(conj, 
          d->var_index, d->u.crd.arc[ci].upper_bound
        ); 
        result = red_bop(AND, result, conj); 
      }
      else 
        result = red_bop(AND, result, red_bop(OR, 
          crd_atom(ZONE[c1][c2], -1 - d->u.crd.arc[ci].upper_bound), 
          crd_one_constraint(rec_space_subtract(
              s, d->u.crd.arc[ci].child 
            ), 
            d->var_index, d->u.crd.arc[ci].upper_bound
          ) 
        ) ); 
    } 
    return(result); 
  } 
  else 
    return(rec_space_subtract(s, d));   	
}
  /* rec_space_subtract_slub_dlb() */ 




struct red_type *rec_space_subtract_slub(
  struct red_type	*s, 
  int			c1, 
  int			c2, 
  int			snlb, 
  int			sub, 
  struct red_type	*d
) {
  int			ci; 
  struct red_type	*result; 

  if (ZONE[c1][c2] == d->var_index) {
    result = s; 
    for (ci = d->u.crd.child_count-1; ci >=0 && result != NORM_FALSE; ci--) {
      if (d->u.crd.arc[ci].upper_bound + sub < 0) 
        break; 
      else 
        result = red_bop(AND, result, red_bop(OR, 
          crd_atom(ZONE[c2][c1], -1-d->u.crd.arc[ci].upper_bound), 
          crd_one_constraint(rec_space_subtract_slub_dlb(
              s, c1, c2, snlb, d->u.crd.arc[ci].child
            ), 
            ZONE[c1][c2], d->u.crd.arc[ci].upper_bound
        ) ) ); 
    } 
    return(result); 
  } 
  else if (ZONE[c2][c1] == d->var_index) { 
    return(rec_space_subtract_slub_dlb(s, c1, c2, snlb, d));   	
  } 
  else 
    return(rec_space_subtract(s,d)); 
}
  /* rec_space_subtract_slub() */ 




struct red_type *rec_space_subtract_slb(
  struct red_type	*s, 
  int			c1, 
  int			c2, 
  int			snlb, 
  struct red_type	*d
) {
  int			ci; 
  struct red_type	*result; 
  
  if (s->var_index != ZONE[c2][c1]) 
    return(rec_space_subtract_slub(s, c1, c2, snlb, CLOCK_POS_INFINITY, d));
  else { 
    result = NORM_FALSE; 
    for (ci = 0; ci < s->u.crd.child_count; ci++) { 
      result = red_bop(OR, result, crd_one_constraint(
        rec_space_subtract_slub(
          s->u.crd.arc[ci].child, c1, c2, 
      	  snlb, s->u.crd.arc[ci].upper_bound, d
        ), 
        ZONE[c2][c1], s->u.crd.arc[ci].upper_bound
      ) ); 
    }
    return(result); 
  }
}
  /* rec_space_subtract_slb() */ 






struct red_type	*rec_space_subtract_right(s, d)
  struct red_type	*s, *d;
{
  int			ciy, lb, ub, c1, c2;
  struct red_type	*new_child;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(d->var_index, 
		   rec_space_subtract(s, d->u.bdd.zero_child), 
		   rec_space_subtract(s, d->u.bdd.one_child)
		   )
	   ); 
    break; 

  case TYPE_CDD:
    fprintf(RED_OUT, "\nERROR: we only use CDD as a representation.\n    Space subtraction are not to be used directly on CDDs.\n");
    fflush(RED_OUT); 
    exit(0); 

  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 < c2) 
      if (s->var_index == ZONE[c2][c1]) 
        return(rec_space_subtract_slb(s, c1, c2, 0, d)); 
      else 
        return(rec_space_subtract_slub(s, c1, c2, 0, CLOCK_POS_INFINITY, d)); 
    else 
      return(rec_space_subtract_slub_dlb(s, c2, c1, 0, d)); 
    break;

  case TYPE_HRD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_HDD:
    fprintf(RED_OUT, "\nWarning: hybrid inequality filter right subtraction is forbidden\n");
    fflush(RED_OUT);
    for (lb = 1; lb; );
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_space_subtract(s, d->u.lazy.false_child), 
      rec_space_subtract(s, d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    ) ); 
    break; 
    
  case TYPE_FLOAT: {
    float flb, fub; 
    
    child_stack_level_push();
    for (fub = VAR[d->var_index].U.FLT.UB, ciy = d->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (fub > d->u.fdd.arc[ciy].upper_bound)
	fchild_stack_push(s, 
	  feps_plus(d->u.fdd.arc[ciy].upper_bound), fub
	);

      new_child = rec_space_subtract(s, d->u.fdd.arc[ciy].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ciy].lower_bound,
	d->u.fdd.arc[ciy].upper_bound
      );
      fub = feps_minus(d->u.fdd.arc[ciy].lower_bound);
    }

    if (fub >= VAR[d->var_index].U.FLT.LB)
      fchild_stack_push(s, VAR[d->var_index].U.FLT.LB, fub);

    return(fdd_new(d->var_index));
    break; 
  }
  case TYPE_DOUBLE: {
    double dfub, dflb; 
    
    child_stack_level_push();
    for (dfub = VAR[d->var_index].U.DBLE.UB, ciy = d->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      if (dfub > d->u.dfdd.arc[ciy].upper_bound)
	dfchild_stack_push(s, 
	  dfeps_plus(d->u.dfdd.arc[ciy].upper_bound), dfub
	);

      new_child = rec_space_subtract(s, d->u.dfdd.arc[ciy].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ciy].lower_bound,
	d->u.dfdd.arc[ciy].upper_bound
      );
      dfub = dfeps_plus(d->u.dfdd.arc[ciy].lower_bound);
    }

    if (dfub >= VAR[d->var_index].U.DBLE.LB)
      dfchild_stack_push(s, VAR[d->var_index].U.DBLE.LB, dfub);

    return(dfdd_new(d->var_index));
    break; 
  }   
  default:
    child_stack_level_push();
    for (ub = VAR[d->var_index].U.DISC.UB, ciy = d->u.ddd.child_count-1; ciy >= 0; ciy--) {
      if (ub > d->u.ddd.arc[ciy].upper_bound)
	ichild_stack_push(s, d->u.ddd.arc[ciy].upper_bound+1, ub);

      new_child = rec_space_subtract(s, d->u.ddd.arc[ciy].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ciy].lower_bound,
	d->u.ddd.arc[ciy].upper_bound
      );
      ub = d->u.ddd.arc[ciy].lower_bound-1;
    }

    if (ub >= VAR[d->var_index].U.DISC.LB)
      ichild_stack_push(s, VAR[d->var_index].U.DISC.LB, ub);

    return(ddd_new(d->var_index));
  }
}
/* rec_space_subtract_right() */




struct red_type	*rec_space_subtract_left(s, d)
  struct red_type	*s, *d;
{
  int			cix, ciy, lb, ub;
  struct red_type	*new_child;

  switch (VAR[s->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return(bdd_new(s->var_index, 
		   rec_space_subtract(s->u.bdd.zero_child, d), 
		   rec_space_subtract(s->u.bdd.one_child, d)
		   )
	   ); 
    break; 
  case TYPE_CDD:
    fprintf(RED_OUT, "\nERROR: we only use CDD as a representation.\n    Space subtraction are not to be used directly on CDDs.\n");
    fflush(RED_OUT); 
    exit(0); 

  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality is encountered.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HDD:
    fprintf(RED_OUT, "\nError: a hybrid filter inequality is encountered.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = s->u.hrd.child_count-1; cix >= 0; cix--) {
      new_child = rec_space_subtract(s->u.hrd.arc[cix].child, d);
      hchild_stack_push(new_child, s->u.hrd.arc[cix].ub_numerator,
				 s->u.hrd.arc[cix].ub_denominator
				 );
    }
    return(hrd_new(s->var_index, s->u.hrd.hrd_exp));
  case TYPE_LAZY_EXP: 
    return(lazy_subtree(
      rec_space_subtract(s->u.lazy.false_child, d), 
      rec_space_subtract(s->u.lazy.true_child, d), 
      VAR[s->var_index].PROC_INDEX, 
      s->u.lazy.exp 
    ) ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = s->u.fdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_space_subtract(s->u.fdd.arc[cix].child, d);
      fchild_stack_push(new_child, s->u.fdd.arc[cix].lower_bound,
	 s->u.fdd.arc[cix].upper_bound
      );
    }
    return(fdd_new(s->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = s->u.dfdd.child_count-1; cix >= 0; cix--) {
      new_child = rec_space_subtract(s->u.dfdd.arc[cix].child, d);
      dfchild_stack_push(new_child, s->u.dfdd.arc[cix].lower_bound,
	 s->u.dfdd.arc[cix].upper_bound
      );
    }
    return(dfdd_new(s->var_index));
    break; 

  default:
    child_stack_level_push();
    for (cix = s->u.ddd.child_count-1; cix >= 0; cix--) {
      new_child = rec_space_subtract(s->u.ddd.arc[cix].child, d);
      ichild_stack_push(new_child, s->u.ddd.arc[cix].lower_bound,
	 s->u.ddd.arc[cix].upper_bound
      );
    }
    return(ddd_new(s->var_index));
  }
}
/* rec_space_subtract_left() */






struct red_type	*rec_space_subtract(s, d)
  struct red_type	*s, *d;
{
  int				ci, c1, c2, ub_numerator, ub_denominator, 
				b, lb, ub, tmp, cix, ciy; 
  float				flb, fub; 
  double 			dflb, dfub; 
  struct red_type		*child, *conj, *result, *acc;
  struct ddd_child_type		*ic, *jc;
  struct ddd_child_link_type	*nic;
  struct hrd_exp_type		*converse_he;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_FALSE) {
    return(NORM_TRUE);
  }
  else if (s == NORM_FALSE || d == NORM_TRUE) {
    return(NORM_FALSE);
  }

  ce = cache2_check_result_key(OP_SPACE_SUBTRACT, s, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (   VAR[s->var_index].TYPE != TYPE_CRD
      && s->var_index < d->var_index
      && s != NORM_NO_RESTRICTION 
      ) 
    return(ce->result = rec_space_subtract_left(s, d));
  else if (s->var_index > d->var_index || s == NORM_NO_RESTRICTION) {
    return(ce->result = rec_space_subtract_right(s, d)); 
  }
  switch (VAR[s->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(s->var_index, 
        rec_space_subtract(s->u.bdd.zero_child, d->u.bdd.zero_child), 
	rec_space_subtract(s->u.bdd.one_child, d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CDD:
    fprintf(RED_OUT, "\nERROR: we only use CDD as a representation.\n    Space subtraction are not to be used directly on CDDs.\n");
    fflush(RED_OUT); 
    exit(0); 

  case TYPE_CRD:
    c1 = VAR[s->var_index].U.CRD.CLOCK1;
    c2 = VAR[s->var_index].U.CRD.CLOCK2;
    result = NORM_FALSE; 
    if (c1 < c2) { 
      for (ci = 0; ci < s->u.crd.child_count; ci++) { 
      	result = red_bop(OR, result, crd_one_constraint( 
      	  rec_space_subtract_slb(s->u.crd.arc[ci].child, c1, c2, 
      	    s->u.crd.arc[ci].upper_bound, d
      	  ), 
      	  s->var_index, s->u.crd.arc[ci].upper_bound
      	) ); 
      } 
    } 
    else { 
      for (ci = 0; ci < s->u.crd.child_count; ci++) { 
      	if (c2 == 0) {
      	  conj = rec_space_subtract_slub(s->u.crd.arc[ci].child, c2, c1, 
      	    0, s->u.crd.arc[ci].upper_bound, d
      	  ); 
      	  conj = crd_one_constraint(conj, ZONE[c2][c1], 0);  
      	} 
      	else 
      	  conj = rec_space_subtract_slub(s->u.crd.arc[ci].child, c2, c1, 
      	    CLOCK_POS_INFINITY, s->u.crd.arc[ci].upper_bound, d
      	  ); 
      	result = red_bop(OR, result, crd_one_constraint(
      	  conj, s->var_index, s->u.crd.arc[ci].upper_bound 
      	) ); 
      } 
    } 
    return(result); 
    break;

  case TYPE_HRD:
    /*
    fprintf(RED_OUT, "\n==========================\nIn rec_space_subtract(d=%1x)\n", d);
    red_print_graph(d);
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nIn the middle of rec_space_subtract(result) for d=%1x\n", d);
    red_print_graph(result);
    fflush(RED_OUT);
    */
    break;
  case TYPE_LAZY_EXP: 
    if (b = ps_exp_comp(s->u.lazy.exp, d->u.lazy.exp)) {
      if (b < 0)
        return(ce->result = rec_space_subtract_left(s, d));
      else if (b > 0)
        return(ce->result = rec_space_subtract_right(s, d));
    }
    result = lazy_subtree(
      rec_space_subtract(s->u.lazy.false_child, d->u.lazy.false_child), 
      rec_space_subtract(s->u.lazy.true_child, d->u.lazy.true_child), 
      VAR[s->var_index].PROC_INDEX, 
      s->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(s, d, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_fchild(s, d, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && s->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= s->u.fdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && d->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= d->u.fdd.arc[ciy].upper_bound
	    )
	  conj = rec_space_subtract(
	    s->u.fdd.arc[cix].child, d->u.fdd.arc[ciy].child
	  );
	else
	  conj = s->u.fdd.arc[cix].child;

	fchild_stack_push(conj, flb, fub);
      }
    }
    result = fdd_new(s->var_index); 
    break; 
    
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(s, d, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_dfchild(s, d, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && s->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= s->u.dfdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && d->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= d->u.dfdd.arc[ciy].upper_bound
	    )
	  conj = rec_space_subtract(
	    s->u.dfdd.arc[cix].child, d->u.dfdd.arc[ciy].child
	  );
	else
	  conj = s->u.dfdd.arc[cix].child;

	dfchild_stack_push(conj, dflb, dfub);
      }
    }
    result = dfdd_new(s->var_index); 
    break; 
    
  default:
    child_stack_level_push();
    for (last_ichild(s, d, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(s, d, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && s->u.ddd.arc[cix].lower_bound <= lb && ub <= s->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && d->u.ddd.arc[ciy].lower_bound <= lb && ub <= d->u.ddd.arc[ciy].upper_bound)
	  conj = rec_space_subtract(
	    s->u.ddd.arc[cix].child, d->u.ddd.arc[ciy].child
	  );
	else
	  conj = s->u.ddd.arc[cix].child;

	ichild_stack_push(conj, lb, ub);
      }
    }
    result = ddd_new(s->var_index); 
  }
/*
  fprintf(RED_OUT, "\n**********(new complement intermediate result)*************\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "--------------------------\n"); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
  /* rec_space_subtract() */




struct red_type	*red_space_subtract(s, d)
     struct red_type	*s, *d;
{
  struct red_type	*result;

  /*
  fprintf(RED_OUT, "\nstarting a red_space_subtract(d=%1x)----------------------------------------------\n", d);
  */
  result = rec_space_subtract(s, d);
  /*
  fprintf(RED_OUT, "\nstopping a red_space_subtract(d=%1x)+++++++++++++++++++++++++++++++++++++++++++++\n", d);
  */

  return(result);
}
/* red_space_subtract() */




struct red_type	*rec_zone_complement(d)
  struct red_type	*d;
{
  int				ci, c1, c2, ub_numerator, ub_denominator, 
				lb, ub, tmp;
  struct red_type		*new_child, *acc, *result;
  struct ddd_child_type		*ic, *jc;
  struct ddd_child_link_type	*nic;
  struct hrd_exp_type		*converse_he;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE) {
    return(NORM_TRUE);
  }
  else if (d->var_index == TYPE_TRUE) { 
    return(NORM_FALSE);
  }

  ce = cache1_check_result_key(OP_ZONE_COMPLEMENT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    result = NORM_FALSE;
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    ci = d->u.crd.child_count-1; 
    if (!c1) /* The result expression is like 0-c2. 
              * The upperbound must be >= 0 if c2 is neither 
              * NEG_DELTA nor NEG_DELTAP. 
              */ {
      if (c2 == NEG_DELTA || c2 == NEG_DELTAP) {
        if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
          acc = rec_zone_complement(d->u.crd.arc[ci].child); 
          ci--;  
        } 
        else 
          acc = NORM_NO_RESTRICTION; 
        for (; ci >= 0 && acc != NORM_FALSE && d->u.crd.arc[ci].upper_bound >= 0; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
	  result = red_bop(OR, result, crd_one_constraint(acc, ZONE[c2][0], ub));
          acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child));
        }
      }
      else {
        acc = crd_atom(ZONE[0][c2], 0);  
        for (; 
                ci >= 0 
             && acc != NORM_FALSE 
             && d->u.crd.arc[ci].upper_bound >=0; 
             ci--
             ) {
          acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child)); 
        }
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
	  if (ub >= 0) 
	    result = red_bop(OR, result, crd_one_constraint(acc, ZONE[c2][0], ub));
          acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child));
        }
      } 
      result = red_bop(OR, result, acc); 
    } 
    else if (!c2) /* Th result expression is like c1-0.  The upperbound must be <= 0 */ { 
      if (c1 == NEG_DELTA || c1 == NEG_DELTAP) { 
        if (d->u.crd.arc[ci].upper_bound >= 0) { 
          acc = rec_zone_complement(d->u.crd.arc[ci].child); 
          ci--;  
        } 
        else 
          acc = NORM_NO_RESTRICTION; 
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
          if (ub >= 0) 
	    result = red_bop(OR, result, crd_one_constraint(acc, ZONE[0][c1], ub));
          acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child));
        }
        result = red_bop(OR, result, acc);       
      }
      else {
        if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
          acc = rec_zone_complement(d->u.crd.arc[ci].child); 
          ci--;  
        } 
        else 
          acc = NORM_NO_RESTRICTION; 
        for (; ci >= 0 && acc != NORM_FALSE; ci--) {
          ub = -1 - d->u.crd.arc[ci].upper_bound; 
          if (ub <= 0) 
	    result = red_bop(OR, result, crd_one_constraint(acc, ZONE[0][c1], ub));
          acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child));
        }
        result = red_bop(OR, result, crd_one_constraint(acc, ZONE[0][c1], 0));       
      }
    }
    else /* The result expression is like c2-c1.  No restrictions on upperbound. */ { 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
        acc = rec_zone_complement(d->u.crd.arc[ci].child); 
        ci--;  
      } 
      else 
        acc = NORM_NO_RESTRICTION; 
      for (; ci >= 0 && acc != NORM_FALSE; ci--) {
        ub = -1 - d->u.crd.arc[ci].upper_bound;
	result = red_bop(OR, result, crd_one_constraint(acc, ZONE[c2][c1], ub));
        acc = red_bop(AND, acc, rec_zone_complement(d->u.crd.arc[ci].child));
      }
      result = red_bop(OR, result, acc); 
    } 
    /*
    fprintf(RED_OUT, "\n==========================\nIn rec_zone_complement(d=%1x)\n", d);
    red_print_graph(d);
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nIn the middle of rec_zone_complement(result) for d=%1x\n", d);
    red_print_graph(result);
    fflush(RED_OUT);
    */
    break;

  case TYPE_HRD:
    result = NORM_FALSE;
    ci = d->u.hrd.child_count-1; 
    converse_he = hrd_exp_converse(d->u.hrd.hrd_exp);
    ub_numerator = d->u.hrd.arc[ci].ub_numerator;
    if (ub_numerator == HYBRID_POS_INFINITY && d->u.hrd.arc[ci].ub_denominator == 1) {
      acc = rec_zone_complement(d->u.hrd.arc[ci].child); 
      ci--;  
    } 
    else 
      acc = NORM_NO_RESTRICTION; 
    for (; 
            ci >= 0 
         && acc != NORM_FALSE 
         && (   d->u.hrd.arc[ci].ub_numerator > HYBRID_NEG_INFINITY+1 
             || d->u.hrd.arc[ci].ub_denominator > 1
             ); 
         ci--
         ) {
      ub_numerator = -1 - d->u.hrd.arc[ci].ub_numerator;
      result = red_bop(OR, result, 
		       hrd_one_constraint(acc, converse_he, 
					     ub_numerator, d->u.hrd.arc[ci].ub_denominator
					     )
		       );
      acc = red_bop(AND, acc, rec_zone_complement(d->u.hrd.arc[ci].child));
    }
    result = red_bop(OR, result, acc); 
    /*
    fprintf(RED_OUT, "\n==========================\nIn rec_zone_complement(d=%1x)\n", d);
    red_print_graph(d);
    fflush(RED_OUT);

    fprintf(RED_OUT, "\nIn the middle of rec_zone_complement(result) for d=%1x\n", d);
    red_print_graph(result);
    fflush(RED_OUT);
    */
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_zone_complement(d->u.fdd.arc[ci].child), 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
    }
    result = fdd_new(d->var_index);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(
        rec_zone_complement(d->u.dfdd.arc[ci].child),  
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
    }
    result = dfdd_new(d->var_index);
    break;

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ichild_stack_push(
        rec_zone_complement(d->u.ddd.arc[ci].child), d->var_index, 
	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
    }
    result = ddd_new(d->var_index);
  }
/*
  fprintf(RED_OUT, "\n**********(new complement intermediate result)*************\n"); 
  red_print_graph(d); 
  fprintf(RED_OUT, "--------------------------\n"); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
  /* rec_zone_complement() */




struct red_type	*zone_complement(d)
     struct red_type	*d;
{
  struct red_type	*result;

  /*
  fprintf(RED_OUT, "\nstarting a red_complement(d=%1x)----------------------------------------------\n", d);
  */
  result = rec_zone_complement(d);
  /*
  fprintf(RED_OUT, "\nstopping a red_complement(d=%1x)+++++++++++++++++++++++++++++++++++++++++++++\n", d);
  */

  return(result);
}
/* zone_complement() */







/*********************************************************************
 *  The following procedures are for the iterative removal of 
 *  states from a space.  
 *  It can be viewed as a speed-up technique of complementation. 
 */
int	count_subtract_path, path_start;  

int	PATH_DEPTH_LIMIT; 

int	rec_count_path_depth(d, depth) 
     struct red_type	*d; 
     int		depth; 
{
  int				ci, count; 
  struct cache4_hash_entry_type	*ce; 
  
  if (d == NORM_NO_RESTRICTION || depth >= PATH_DEPTH_LIMIT) 
    return(1); 
  
  ce = cache4_check_result_key(
    OP_COUNT_PATH_DEPTH, d, NULL, depth, PATH_DEPTH_LIMIT
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  count = 0; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      count = count + rec_count_path_depth(d->u.crd.arc[ci].child, depth+1);   
    } 
    break; 
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      count = count + rec_count_path_depth(d->u.fdd.arc[ci].child, depth+1); 
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      count = count + rec_count_path_depth(d->u.dfdd.arc[ci].child, depth+1); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      count = count + rec_count_path_depth(d->u.ddd.arc[ci].child, depth+1); 
    } 
  } 
  return((int) (ce->result = (struct red_type *) count)); 
}
  /* rec_count_path_depth() */ 




int	count_path_depth(d, limit) 
	struct red_type	*d; 
	int		limit; 
{ 
  PATH_DEPTH_LIMIT = limit; 
  
  limit = rec_count_path_depth(d, 0); 
  	
  return(limit); 
}
  /* count_path_depth() */ 
  
  
  
  
void	rec_subtract_path_fillin(d, depth, red_path) 
     struct red_type	*d, *red_path; 
     int		depth; 
{
  int			ci; 
  struct red_type	*cur; 
  
  if (d == NORM_NO_RESTRICTION || depth >= PATH_DEPTH_LIMIT) {
    cur = red_bop(AND, d, red_path); 
    for (ci = path_start; ci < RT_TOP; ci++) 
      if (cur == RT[ci]) 
        return; 
    RT[RT_TOP++] = cur; 
    return; 
  }

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      cur = crd_one_constraint(red_path, d->var_index, d->u.crd.arc[ci].upper_bound); 
      rec_subtract_path_fillin(d->u.crd.arc[ci].child, depth+1, cur);   
    } 
    break; 
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      cur = fdd_one_constraint(
        red_path, d->var_index, 
	d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      ); 
      rec_subtract_path_fillin(d->u.fdd.arc[ci].child, depth+1, cur); 
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      cur = dfdd_one_constraint(
        red_path, d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound
      ); 
      rec_subtract_path_fillin(d->u.dfdd.arc[ci].child, depth+1, cur); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      cur = ddd_one_constraint(
        red_path, d->var_index, 
	d->u.ddd.arc[ci].lower_bound, 
	d->u.ddd.arc[ci].upper_bound
      ); 
      rec_subtract_path_fillin(d->u.ddd.arc[ci].child, depth+1, cur); 
    } 
  } 
}
  /* rec_subtract_path_fillin() */ 




int	subtract_path_fillin(d, limit) 
	struct red_type	*d; 
	int		limit; 
{ 
  PATH_DEPTH_LIMIT = limit; 
  
  rec_subtract_path_fillin(d, 0, NORM_NO_RESTRICTION); 
  
  RT_TOP = path_start + count_subtract_path; 
  
  return(RT_TOP); 
}
  /* subtract_path_fillin() */ 
  


#ifdef RED_DEBUG_BISIM_MODE
int	count_subtract_iterative = 0; 
#endif 

struct red_type	*red_subtract_iterative(ineq, eq) 
	int	ineq, eq; 
{ 
  int	path_stop, i; 
  
  count_subtract_path = count_path_depth(RT[eq], 3); 
  path_start = RT_TOP; 
  RT_TOP = subtract_path_fillin(RT[eq], 3); 
  #ifdef RED_DEBUG_BISIM_MODE
  for (i = RT_TOP-1; i >= path_start; i--) { 
    fprintf(RED_OUT, "\nDecomposed RT[eq=%1d]=%x at RT[i=%1d]=%x:\n", 
      eq, (unsigned int) RT[eq], i, (unsigned int) RT[i]
    ); 
    red_print_graph(RT[i]); 
  } 
  #endif 
  for (; RT_TOP > path_start; RT_TOP--) { 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "\nTo subtract decomposed RT[eq=%1d]=%x at RT[i=%1d]=%x:\n", 
      eq, (unsigned int) RT[eq], RT_TOP-1, (unsigned int) RT[RT_TOP-1]
    ); 
    red_print_graph(RT[RT_TOP-1]); 
    #endif 
    
    RT[RT_TOP-1] = red_complement(RT[RT_TOP-1]); 
    #ifdef RED_DEBUG_BISIM_MODE
    ++count_subtract_iterative; 
    fprintf(RED_OUT, "subtract iterative I%1d, subtract %1d, after complementing an RT[%1d]:\n", 
      ITERATION_COUNT, count_subtract_iterative, RT_TOP-1
    ); 
    red_print_graph(RT[RT_TOP-1]); 
    #endif 
    
    RT[ineq] = red_bop(AND, RT[ineq], RT[RT_TOP-1]); 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "subtract iterative I%1d, subtract %1d, after subtracting from RT[ineq=%1d]:\n", 
      ITERATION_COUNT, count_subtract_iterative, ineq 
    ); 
    red_print_graph(RT[ineq]); 
    #endif 
    
    RT[ineq] = red_bop(AND, RT[ineq], RT[EC_INVARIANCE_WITH_ONLY_DIAGONAL]); 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "subtract iterative I%1d, subtract %1d, after invariancing with RT[ineq=%1d]:\n", 
      ITERATION_COUNT, count_subtract_iterative, ineq
    ); 
    red_print_graph(RT[ineq]); 
    #endif 
    
    RT[ineq] = red_tight_all_pairs(ineq); 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "subtract iterative I%1d, subtract %1d, after tightening with RT[ineq=%1d]:\n", 
      ITERATION_COUNT, count_subtract_iterative, ineq
    ); 
    red_print_graph(RT[ineq]); 
    #endif 
  } 
  return(RT[ineq]); 
}
  /* red_subtract_iterative() */  





/* Keep red untouched and make a new not red. */
int	check_clock_inequality_converse(dx, dy) 
	struct red_type	*dx, *dy; 
{ 
  if (   VAR[dx->var_index].TYPE == TYPE_CRD
      && VAR[dy->var_index].TYPE == TYPE_CRD
      && VAR[dx->var_index].U.CRD.CLOCK1 == VAR[dy->var_index].U.CRD.CLOCK2
      && VAR[dx->var_index].U.CRD.CLOCK2 == VAR[dy->var_index].U.CRD.CLOCK1
      ) 
    return(1); 
  else 
    return(0); 	
}
  /* check_clock_inequality_converse() */  
  
  



/*******************************
 *
 *  For INTERSECT, NORM_NO_RESTRICTION of clock inequalities is interpreted
 *	as (oo, oo) for both dx and dy.
 */


struct red_type	*rec_super_intersect_untimed(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*new_child, *result;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_SUPER_INTERSECT_UNTIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    ci = d->u.crd.child_count-1;
    if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY)
      new_child = rec_super_intersect_untimed(d->u.crd.arc[ci].child);
    else
      new_child = NORM_FALSE;
    result = new_child;
    break;

  case TYPE_HRD:
    ci = d->u.hrd.child_count-1;
    if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	&& d->u.hrd.arc[ci].ub_denominator == 1
	)
      new_child = rec_super_intersect_untimed(d->u.hrd.arc[ci].child);
    else
      new_child = NORM_FALSE;
    result = new_child;
    break; 
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_super_intersect_untimed(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }

    result = fdd_new(d->var_index);
    break; 
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_super_intersect_untimed(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index);
    break; 
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_super_intersect_untimed(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
				 d->u.ddd.arc[ci].upper_bound
				 );
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
  /* rec_super_intersect_untimed() */




struct red_type	*red_super_intersect_untimed(d)
     struct red_type	*d;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

  result = rec_super_intersect_untimed(d);
  return(result);
}
/* red_super_intersect_untimed() */



/*************************************************************************************
* red_super_intersect_self(dx, dy)
* dy is derived from dx purely.
* for each \eta in dx, \eta is in the result if \eta contains an \eta' in dy.
*/


struct red_type	*rec_super_intersect_self(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result, *unionx;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_FALSE || dy == NORM_FALSE)
    return(NORM_FALSE);
  else if (dx == NORM_NO_RESTRICTION)
    return(NORM_NO_RESTRICTION);

  ce = cache2_check_result_key(OP_SUPER_INTERSECT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dy == NORM_NO_RESTRICTION) {
    return(ce->result 
      = red_super_intersect_untimed(dx)
    );
  }

  if ((dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) || dy == NORM_NO_RESTRICTION) {
    if (VAR[dx->var_index].TYPE == TYPE_CRD) {
      struct crd_child_type	*bcx;

      bcx = &(dx->u.crd.arc[dx->u.crd.child_count - 1]);
      if (bcx->upper_bound == CLOCK_POS_INFINITY)
	result = rec_super_intersect_self(bcx->child, dy);
      else
	result = NORM_FALSE;
    }
    else if (VAR[dx->var_index].TYPE == TYPE_HRD) {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_super_intersect_self(hcx->child, dy);
      else
	result = NORM_FALSE;
    }
    else {
      struct ddd_child_type		*icx;

      child_stack_level_push();
        for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
        icx = &(dx->u.ddd.arc[cix]);
        new_child = rec_super_intersect_self(icx->child, dy);
        ichild_stack_push(new_child, icx->lower_bound, icx->upper_bound);
      }

      result = ddd_new(dx->var_index);
    }
    return(ce->result = result);
  }
  else if ((dy != NORM_NO_RESTRICTION && dx->var_index > dy->var_index) || dx == NORM_NO_RESTRICTION) {
    switch (VAR[dy->var_index].TYPE) {
    case TYPE_CRD:
      result = NORM_FALSE;
      for (ciy = dy->u.crd.child_count-1; ciy>=0; ciy--) {
        struct crd_child_type	*bcy;

        bcy = &(dy->u.crd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_self(dx, bcy->child));
      }
      break;
    case TYPE_HRD:
      result = NORM_FALSE;
      for (ciy = dy->u.hrd.child_count-1; ciy>=0; ciy--) {
        struct hrd_child_type	*hcy;

        hcy = &(dy->u.hrd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_self(dx, hcy->child));
      }
      break;
    case TYPE_FLOAT:
      child_stack_level_push();
      for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
        struct fdd_child_type	*fcy;

        fcy = &(dy->u.fdd.arc[ciy]);
        new_child = rec_super_intersect_self(dx, fcy->child);
        fchild_stack_push(new_child, fcy->lower_bound, fcy->upper_bound);
      }
      result = fdd_new(dy->var_index);
      break;
    case TYPE_DOUBLE:
      child_stack_level_push();
      for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
        struct dfdd_child_type	*dfcy;

        dfcy = &(dy->u.dfdd.arc[ciy]);
        new_child = rec_super_intersect_self(dx, dfcy->child);
        dfchild_stack_push(new_child, dfcy->lower_bound, dfcy->upper_bound);
      }
      result = dfdd_new(dy->var_index);
      break;
    default:
      child_stack_level_push();
      for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
        struct ddd_child_type	*icy;

        icy = &(dy->u.ddd.arc[ciy]);
        new_child = rec_super_intersect_self(dx, icy->child);
        ichild_stack_push(new_child, icy->lower_bound, icy->upper_bound);
      }
      result = ddd_new(dy->var_index);
    }
    return(ce->result = result);
  }
  else if (   dx->var_index == dy->var_index
	   && VAR[dx->var_index].TYPE == TYPE_HRD
           && (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp))
	   ) {
    if (b < 0) {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_super_intersect_self(hcx->child, dy);
      else
	result = NORM_FALSE;

      return(ce->result = result);
    }
    else if (b > 0) {
      result = NORM_FALSE;
      for (ciy = dy->u.hrd.child_count-1; ciy>=0; ciy--) {
        struct hrd_child_type	*hcy;

        hcy = &(dy->u.hrd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_self(dx, hcy->child));
      }

      return(ce->result = result);
    }
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    cix = dx->u.crd.child_count - 1;
    ciy = dy->u.crd.child_count - 1;
    result = NORM_FALSE;
    if (dx->u.crd.arc[cix].upper_bound == CLOCK_POS_INFINITY) {
      for (; ciy >= 0; ciy--) {
	result = red_bop(OR, result,
			 rec_super_intersect_self(dx->u.crd.arc[cix].child,
					     dy->u.crd.arc[ciy].child
					     )
			 );
      }
      cix--;
      ciy = dy->u.crd.child_count-1;
    }
    for (; cix >= 0 && ciy >= 0; ){
      if (dx->u.crd.arc[cix].upper_bound < dy->u.crd.arc[ciy].upper_bound)
	ciy--;
      else if (dx->u.crd.arc[cix].upper_bound > dy->u.crd.arc[ciy].upper_bound)
	cix--;
      else {
	new_child = rec_super_intersect_self(dx->u.crd.arc[cix].child, dy->u.crd.arc[ciy].child);
	bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
	cix--;
	ciy--;
      }
    }

    result = red_bop(OR, result, crd_new(dx->var_index));
    break;
  case TYPE_HRD:
    cix = dx->u.hrd.child_count - 1;
    result = NORM_FALSE;
    if (   dx->u.hrd.arc[cix].ub_numerator == HYBRID_POS_INFINITY
	&& dx->u.hrd.arc[cix].ub_denominator == 1
	) {
      for (ciy = dy->u.hrd.child_count - 1; ciy >= 0; ciy--) {
	result = red_bop(OR, result,
			 rec_super_intersect_self(dx->u.hrd.arc[cix].child,
					     dy->u.hrd.arc[ciy].child
					     )
			 );
      }
      cix--;
    }
    for (ciy = dy->u.hrd.child_count - 1;
	    ciy >= 0
	 && rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			  dx->u.hrd.arc[cix].ub_denominator,
			  dy->u.hrd.arc[ciy].ub_numerator,
			  dy->u.hrd.arc[ciy].ub_denominator
			  ) < 0;
	 ciy--
	 );
    for (unionx = NORM_FALSE; ciy >= 0; ciy--){
      for (;
	      cix >= 0
	   && (b = rational_comp(dx->u.hrd.arc[cix].ub_numerator,
				 dx->u.hrd.arc[cix].ub_denominator,
				 dy->u.hrd.arc[ciy].ub_numerator,
				 dy->u.hrd.arc[ciy].ub_denominator
				 )
	       ) > 0;
	   cix--
	   )
	unionx = red_bop(OR, dx->u.hrd.arc[cix].child, unionx);
      if (cix >= 0 && b == 0) {
        unionx = red_bop(OR, dx->u.hrd.arc[cix].child, unionx);
      }
      else
	cix++;
      new_child = rec_super_intersect_self(unionx, dy->u.hrd.arc[ciy].child);
      hchild_stack_push(new_child, dy->u.hrd.arc[ciy].ub_numerator,
				 dy->u.hrd.arc[ciy].ub_denominator
				 );
    }
    result = red_bop(OR, result,
		     hrd_new(dx->var_index, dx->u.hrd.hrd_exp)
		     );
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 && ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_super_intersect_self(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );
	  fchild_stack_push(new_child, flb, fub);
	}
    }

    result = fdd_new(dx->var_index);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 && ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_super_intersect_self(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );
	  dfchild_stack_push(new_child, flb, fub);
	}
    }

    result = dfdd_new(dx->var_index);
    break;
  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 && ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_super_intersect_self(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  ichild_stack_push(new_child, lb, ub);
	}
    }

    result = ddd_new(dx->var_index);
  }

  return(ce->result = result);
}
  /* rec_super_intersect_self() */


struct red_type	*red_super_intersect_self(dx, dy)
  struct red_type	*dx, *dy;
{
  if (dx == NORM_FALSE || dy == NORM_FALSE)
    return(NORM_FALSE);
  else if (dx == NORM_NO_RESTRICTION)
    return(dx);
  else {
    struct red_type	*result;

    result = rec_super_intersect_self(dx, dy);

    return(result);
  }
}
  /* red_super_intersect_self() */



/*************************************************************************************
* red_super_intersect_self(dx, dy)
* dy is derived independently of dx.
* usually, dy is derived from the complement of reachables.
* for each \eta in dx, \eta is in the result if \eta contains an \eta' in dy.
*/


struct red_type	*rec_super_intersect_external(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *result, *uniony;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_FALSE || dy == NORM_FALSE)
    return(NORM_FALSE);
  else if (dx == NORM_NO_RESTRICTION)
    return(NORM_NO_RESTRICTION);

  ce = cache2_check_result_key(OP_SUPER_INTERSECT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (dy == NORM_NO_RESTRICTION) {
    return(ce->result 
      = red_super_intersect_untimed(dx)
    );
  }

  if ((dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) || dy == NORM_NO_RESTRICTION) {
    switch (VAR[dx->var_index].TYPE) { 
    case TYPE_CRD: {
      struct crd_child_type	*bcx;

      bcx = &(dx->u.crd.arc[dx->u.crd.child_count - 1]);
      if (bcx->upper_bound == CLOCK_POS_INFINITY)
	result = rec_super_intersect_external(bcx->child, dy);
      else
	result = NORM_FALSE;
      break; 
    }
    case TYPE_HRD: {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_super_intersect_external(hcx->child, dy);
      else
	result = NORM_FALSE;
      break; 
    }
    case TYPE_FLOAT: {
      struct fdd_child_type		*fcx;

      child_stack_level_push();
      for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
        fcx = &(dx->u.fdd.arc[cix]);
        new_child = rec_super_intersect_external(fcx->child, dy);
        fchild_stack_push(new_child, fcx->lower_bound, fcx->upper_bound);
      }

      result = fdd_new(dx->var_index);
      break; 
    }
    case TYPE_DOUBLE: {
      struct dfdd_child_type		*dfcx;

      child_stack_level_push();
      for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
        dfcx = &(dx->u.dfdd.arc[cix]);
        new_child = rec_super_intersect_external(dfcx->child, dy);
        dfchild_stack_push(new_child, dfcx->lower_bound, dfcx->upper_bound);
      }

      result = dfdd_new(dx->var_index);
      break; 
    }
    default: {
      struct ddd_child_type		*icx;

      child_stack_level_push();
      for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
        icx = &(dx->u.ddd.arc[cix]);
        new_child = rec_super_intersect_external(icx->child, dy);
        ichild_stack_push(new_child, icx->lower_bound, icx->upper_bound);
      }

      result = ddd_new(dx->var_index);
      break; 
    } }
    return(ce->result = result);
  }
  else if ((dy != NORM_NO_RESTRICTION && dx->var_index > dy->var_index) || dx == NORM_NO_RESTRICTION) {
    switch (VAR[dy->var_index].TYPE) {
    case TYPE_CRD:
      result = NORM_FALSE;
      for (ciy = dy->u.crd.child_count-1; ciy>=0; ciy--) {
        struct crd_child_type	*bcy;

        bcy = &(dy->u.crd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_external(dx, bcy->child));
      }
      break;
    case TYPE_HRD:
      result = NORM_FALSE;
      for (ciy = dy->u.hrd.child_count-1; ciy>=0; ciy--) {
        struct hrd_child_type	*hcy;

        hcy = &(dy->u.hrd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_external(dx, hcy->child));
      }
      break;
    case TYPE_FLOAT:
      child_stack_level_push();
      for (ciy = dy->u.fdd.child_count-1; ciy >= 0; ciy--) {
        struct fdd_child_type	*fcy;

        fcy = &(dy->u.fdd.arc[ciy]);
        new_child = rec_super_intersect_external(dx, fcy->child);
        fchild_stack_push(new_child, fcy->lower_bound, fcy->upper_bound);
      }
      result = fdd_new(dy->var_index);
      break;
    case TYPE_DOUBLE:
      child_stack_level_push();
      for (ciy = dy->u.dfdd.child_count-1; ciy >= 0; ciy--) {
        struct dfdd_child_type	*dfcy;

        dfcy = &(dy->u.dfdd.arc[ciy]);
        new_child = rec_super_intersect_external(dx, dfcy->child);
        dfchild_stack_push(new_child, dfcy->lower_bound, dfcy->upper_bound);
      }
      result = dfdd_new(dy->var_index);
      break;
    default:
      child_stack_level_push();
      for (ciy = dy->u.ddd.child_count-1; ciy >= 0; ciy--) {
        struct ddd_child_type	*icy;

        icy = &(dy->u.ddd.arc[ciy]);
        new_child = rec_super_intersect_external(dx, icy->child);
        ichild_stack_push(new_child, icy->lower_bound, icy->upper_bound);
      }
      result = ddd_new(dy->var_index);
    }
    return(ce->result = result);
  }
  else if (   dx->var_index == dy->var_index
	   && VAR[dx->var_index].TYPE == TYPE_HRD
           && (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp))
	   ) {
    if (b < 0) {
      struct hrd_child_type	*hcx;

      hcx = &(dx->u.hrd.arc[dx->u.hrd.child_count - 1]);
      if (hcx->ub_numerator == HYBRID_POS_INFINITY && hcx->ub_denominator == 1)
	result = rec_super_intersect_external(hcx->child, dy);
      else
	result = NORM_FALSE;

      return(ce->result = result);
    }
    else if (b > 0) {
      result = NORM_FALSE;
      for (ciy = dy->u.hrd.child_count-1; ciy>=0; ciy--) {
        struct hrd_child_type	*hcy;

        hcy = &(dy->u.hrd.arc[ciy]);
	result = red_bop(OR, result, rec_super_intersect_external(dx, hcy->child));
      }

      return(ce->result = result);
    }
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    result = NORM_FALSE;
    for (cix = 0, ciy = 0, uniony = NORM_FALSE; cix < dx->u.crd.child_count; cix++) {
      for (;
	      ciy < dy->u.crd.child_count
	   && dx->u.crd.arc[cix].upper_bound >= dy->u.crd.arc[ciy].upper_bound;
	   ciy++
	   ) {
        uniony = red_bop(OR, uniony, dy->u.crd.arc[ciy].child);
      }
      new_child = rec_super_intersect_external(dx->u.crd.arc[cix].child, uniony);
      result = red_bop(OR, result,
		       crd_lone_subtree(new_child, dx->var_index,
					 dx->u.crd.arc[cix].upper_bound
					 )
		       );
    }
    break;

  case TYPE_HRD:
    result = NORM_FALSE;
    for (cix = 0, ciy = 0, uniony = NORM_FALSE; cix < dx->u.hrd.child_count; cix++) {
      for (;
	      ciy < dy->u.hrd.child_count
	   && rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			    dx->u.hrd.arc[cix].ub_denominator,
			    dy->u.hrd.arc[ciy].ub_numerator,
			    dy->u.hrd.arc[ciy].ub_denominator
			    ) >= 0;
	   ciy++
	   ) {
        uniony = red_bop(OR, uniony, dy->u.hrd.arc[ciy].child);
      }
      new_child = rec_super_intersect_external(dx->u.hrd.arc[cix].child, uniony);
      result = red_bop(OR, result,
		       hrd_lone_subtree(new_child, dx->var_index, dx->u.hrd.hrd_exp,
					   dx->u.hrd.arc[cix].ub_numerator,
					   dx->u.hrd.arc[cix].ub_denominator
					   )
		       );
    }
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 && ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_super_intersect_external(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );
	  fchild_stack_push(new_child, flb, fub);
	}
    }

    result = fdd_new(dx->var_index);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 && ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          )
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_super_intersect_external(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );
	  dfchild_stack_push(new_child, dflb, dfub);
	}
    }

    result = dfdd_new(dx->var_index);
    break;

  default:
    child_stack_level_push();
    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 && ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_super_intersect_external(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  ichild_stack_push(new_child, lb, ub);
	}
    }

    result = ddd_new(dx->var_index);
  }

  return(ce->result = result);
}
  /* rec_super_intersect_external() */


struct red_type	*red_super_intersect_external(dx, dy)
  struct red_type	*dx, *dy;
{
  if (dx == NORM_FALSE || dy == NORM_FALSE)
    return(NORM_FALSE);
  else if (dx == NORM_NO_RESTRICTION)
    return(dx);
  else {
    struct red_type	*result;

    result = rec_super_intersect_external(dx, dy);

    return(result);
  }
}
  /* red_super_intersect_external() */



void	bop_test()
{
  struct red_type	*result2, *dx, *dy;
  int			conj, result, dix;

/*
  RT[dix = RT_TOP++] = crd_atom(ZONE[1][2], -2);
  dy = crd_atom(ZONE[0][1], -3);
  fprintf(RED_OUT, "\n1:============================\nTest Restriction\n==========================\n");
  fprintf(RED_OUT, "dx:\n");
  red_print_graph(RT[dix]);
  fprintf(RED_OUT, "dy:\n");
  red_print_graph(dy);
  RT[result = RT_TOP++] = RT[dix];
  RT[result] = red_restrict_closure(result, dy);
  fprintf(RED_OUT, "result=dx restrict dy:\n");
  red_print_graph(RT[result]);

  RT[dix] = crd_atom(ZONE[0][1], -8);
  dy = crd_atom(ZONE[1][2], -12);
  fprintf(RED_OUT, "\n2:============================\nTest Restriction\n==========================\n");
  fprintf(RED_OUT, "dx:\n");
  red_print_graph(RT[dix]); 
  fprintf(RED_OUT, "dy:\n");
  red_print_graph(dy); 
  RT[conj = RT_TOP++] = RT[dix];
  RT[conj] = red_restrict_closure(conj, dy),
  RT[result] = red_bop(OR, RT[conj], RT[result]); 
  fprintf(RED_OUT, "conj=dx restrict dy:\n"); 
  red_print_graph(RT[conj]); 
  fprintf(RED_OUT, "result = conj union result:\n"); 
  red_print_graph(RT[result]); 

  RT[dix] = crd_atom(ZONE[1][0], -7);
  dy = crd_atom(ZONE[2][1], -5);
  fprintf(RED_OUT, "\n3:============================\nTest Restriction\n==========================\n");
  fprintf(RED_OUT, "dx:\n"); 
  red_print_graph(RT[dix]); 
  fprintf(RED_OUT, "dy:\n"); 
  red_print_graph(dy); 
   RT[conj] = RT[dix]; 
  RT[conj] = red_restrict_closure(dix, dy); 
  RT[result] = red_bop(OR, RT[conj], RT[result]); 
  fprintf(RED_OUT, "conj=dx restrict dy:\n"); 
  red_print_graph(RT[conj]); 
  fprintf(RED_OUT, "result = conj union result:\n"); 
  red_print_graph(RT[result]); 

  RT[dix] = crd_atom(ZONE[1][2], -6); 
  dy = crd_atom(ZONE[2][0], -9); 
  fprintf(RED_OUT, "\n4:============================\nTest Restriction\n==========================\n"); 
  fprintf(RED_OUT, "dx:\n"); 
  red_print_graph(RT[dix]); 
  fprintf(RED_OUT, "dy:\n");
  red_print_graph(dy);
  RT[conj] = RT[dix]; 
  RT[conj] = red_restrict_closure(dix, dy); 
  RT[result] = red_bop(OR, RT[conj], RT[result]);
  fprintf(RED_OUT, "conj=dx restrict dy:\n");
  red_print_graph(RT[conj]); 
  fprintf(RED_OUT, "result = conj union result:\n"); 
  red_print_graph(RT[result]); 

  RT_TOP = RT_TOP-3; 
  
  fflush(RED_OUT);
*/
  exit(0);


}
/* bop_test() */




/**************************************************************
*
*/

struct red_type		*rec_exclude_with_reduction();


struct red_type	*rec_exclude_right_with_reduction(dx, dy)
  struct red_type	*dx, *dy;
{
  int				ciy, lb, ub;
  float				flb, fub; 
  double			dflb, dfub; 
  struct red_type		*new_child, *new;
  struct crd_child_type		*bcy;
  struct hrd_child_type		*hcy;
  struct ddd_child_type		*icy;
  struct fdd_child_type		*fcy;
  struct dfdd_child_type	*dfcy;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_CRD:
    bcy = &(dy->u.crd.arc[dy->u.crd.child_count-1]);
    if (bcy->upper_bound == CLOCK_POS_INFINITY)
      return(rec_exclude_with_reduction(dx, bcy->child));
    else
      return(dx);

    break;

  case TYPE_HRD:
    hcy = &(dy->u.hrd.arc[dy->u.hrd.child_count-1]);
    if (hcy->ub_numerator == HYBRID_POS_INFINITY && hcy->ub_denominator == 1)
      return(rec_exclude_with_reduction(dx, hcy->child));
    else
      return(dx);

    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (fub = VAR[dy->var_index].U.FLT.UB, ciy = dy->u.fdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      fcy = &(dy->u.fdd.arc[ciy]);
      if (fub > fcy->upper_bound)
	fchild_stack_push(dx, feps_plus(fcy->upper_bound), fub);

      new_child = rec_exclude_with_reduction(dx, fcy->child);
      fchild_stack_push(new_child, fcy->lower_bound, fcy->upper_bound);
      fub = feps_minus(fcy->lower_bound);
    }

    if (fub >= VAR[dy->var_index].U.FLT.LB)
      fchild_stack_push(dx, VAR[dy->var_index].U.FLT.LB, fub);

    return(fdd_new(dy->var_index));
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (dfub = VAR[dy->var_index].U.DBLE.UB, ciy = dy->u.dfdd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      dfcy = &(dy->u.dfdd.arc[ciy]);
      if (dfub > dfcy->upper_bound)
	dfchild_stack_push(dx, dfeps_plus(dfcy->upper_bound), dfub);

      new_child = rec_exclude_with_reduction(dx, dfcy->child);
      dfchild_stack_push(new_child, dfcy->lower_bound, dfcy->upper_bound);
      dfub = dfeps_minus(dfcy->lower_bound);
    }

    if (dfub >= VAR[dy->var_index].U.DBLE.LB)
      dfchild_stack_push(dx, VAR[dy->var_index].U.DBLE.LB, fub);

    return(dfdd_new(dy->var_index));
    break;

  default:
    child_stack_level_push();
    for (ub = VAR[dy->var_index].U.DISC.UB, ciy = dy->u.ddd.child_count-1; 
         ciy >= 0; 
         ciy--
         ) {
      icy = &(dy->u.ddd.arc[ciy]);
      if (ub > icy->upper_bound)
	ichild_stack_push(dx, icy->upper_bound+1, ub);

      new_child = rec_exclude_with_reduction(dx, icy->child);
      ichild_stack_push(new_child, icy->lower_bound, icy->upper_bound);
      ub = icy->lower_bound-1;
    }

    if (ub >= VAR[dy->var_index].U.DISC.LB)
      ichild_stack_push(dx, VAR[dy->var_index].U.DISC.LB, ub);

    return(ddd_new(dy->var_index));
  }
}
/* rec_exclude_right_with_reduction() */





struct red_type	*rec_exclude_left_with_reduction(dx, dy)
  struct red_type	*dx, *dy;
{
  int				cix; 
  struct red_type		*new_child, *new;
  struct crd_child_type		*bcx;
  struct hrd_child_type		*hcx;
  struct ddd_child_type		*icx;
  struct fdd_child_type		*fcx;
  struct dfdd_child_type	*dfcx;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count-1; cix >= 0; cix--) {
      bcx = &(dx->u.crd.arc[cix]);
      new_child = rec_exclude_with_reduction(bcx->child, dy);
      bchild_stack_push(new_child, bcx->upper_bound);
    }
    return(crd_new(dx->var_index));

    break;
  case TYPE_HRD:
    child_stack_level_push();
    for (cix = dx->u.hrd.child_count-1; cix >= 0; cix--) {
      hcx = &(dx->u.hrd.arc[cix]);
      new_child = rec_exclude_with_reduction(hcx->child, dy);
      hchild_stack_push(new_child, hcx->ub_numerator, hcx->ub_denominator);
    }
    return(hrd_new(dx->var_index, dx->u.hrd.hrd_exp));

    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count-1; cix >= 0; cix--) {
      fcx = &(dx->u.fdd.arc[cix]);
      new_child = rec_exclude_with_reduction(fcx->child, dy);
      fchild_stack_push(new_child, fcx->upper_bound, fcx->upper_bound);
    }
    return(fdd_new(dx->var_index));
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count-1; cix >= 0; cix--) {
      dfcx = &(dx->u.dfdd.arc[cix]);
      new_child = rec_exclude_with_reduction(dfcx->child, dy);
      dfchild_stack_push(new_child, dfcx->upper_bound, dfcx->upper_bound);
    }
    return(dfdd_new(dx->var_index));
    break;
  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count-1; cix >= 0; cix--) {
      icx = &(dx->u.ddd.arc[cix]);
      new_child = rec_exclude_with_reduction(icx->child, dy);
      ichild_stack_push(new_child, icx->upper_bound, icx->upper_bound);
    }
    return(ddd_new(dx->var_index));
  }
}
/* rec_exclude_left_with_reduction() */






struct red_type	*rec_exclude_with_reduction(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, bx, by, lb, ub, cix, ciy;  
  struct red_type		*new_child;
  struct red_type		*dy_child;
  struct ddd_child_type		*icx, *icy;
  struct cache2_hash_entry_type	*ce; 

  #ifdef RED_DEBUG_REDBOP_MODE
  int 				local_top_level_child_stack;
  #endif 

  if (   dx == NORM_FALSE 
      || dy == NORM_NO_RESTRICTION 
      || dx == dy
      ) { 
    return(NORM_FALSE);
  }
  else if (dy == NORM_FALSE) 
    return(dx); 

  ce = cache2_check_result_key(OP_EXCLUDE_WITH_REDUCTION, dx, dy); 
  if (ce->result) { 
    return(ce->result); 
  } 

  if ((dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) || dy == NORM_NO_RESTRICTION)
    return(ce->result 
      = rec_exclude_left_with_reduction(dx, dy)
    );
  else if ((dy != NORM_NO_RESTRICTION && dy->var_index < dx->var_index) || dx == NORM_NO_RESTRICTION)
    return(ce->result
      = rec_exclude_right_with_reduction(dx, dy)
    );
  else if (   VAR[dx->var_index].TYPE == TYPE_HRD
           && (b = HRD_EXP_COMP(dx->u.hrd.hrd_exp, dy->u.hrd.hrd_exp))
	   ) {
    if (b < 0)
      return(ce->result
        = rec_exclude_left_with_reduction(dx, dy)
      );
    else
      return(ce->result
        = rec_exclude_right_with_reduction(dx, dy)
      );
  }

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    dy_child = NORM_FALSE;
    for (cix = dx->u.crd.child_count-1, ciy = dy->u.crd.child_count-1; cix >= 0; cix--) {
      for (; ciy >= 0 && dx->u.crd.arc[cix].upper_bound <= dy->u.crd.arc[ciy].upper_bound; ciy--)
	dy_child = red_bop(OR, dy_child, dy->u.crd.arc[ciy].child);
      if (dy_child != NORM_FALSE)
	new_child = rec_exclude_with_reduction(dx->u.crd.arc[cix].child, dy_child);
      else
	new_child = dx->u.crd.arc[cix].child;

      bchild_stack_push(new_child, dx->u.crd.arc[cix].upper_bound);
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    }  
    #endif 

    ce->result = crd_new(dx->var_index); 
    return(ce->result /* = crd_new(dx->var_index) */);

    break;

  case TYPE_HRD:
    child_stack_level_push(); 

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    dy_child = NORM_FALSE;
    for (cix = dx->u.hrd.child_count-1, ciy = dy->u.hrd.child_count-1; cix >= 0; cix--) {
      for (;
              ciy >= 0
           && rational_comp(dx->u.hrd.arc[cix].ub_numerator,
			    dx->u.hrd.arc[cix].ub_denominator,
			    dy->u.hrd.arc[ciy].ub_numerator,
			    dy->u.hrd.arc[ciy].ub_denominator
			    ) <= 0;
	   ciy--
	   )
	dy_child = red_bop(OR, dy_child, dy->u.hrd.arc[ciy].child);
      if (dy_child != NORM_FALSE)
	new_child = rec_exclude_with_reduction(dx->u.hrd.arc[cix].child, dy_child);
      else
	new_child = dx->u.hrd.arc[cix].child;

      hchild_stack_push(new_child, dx->u.hrd.arc[cix].ub_numerator,
 				 dx->u.hrd.arc[cix].ub_denominator
				 );
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    return(ce->result 
      = hrd_new(dx->var_index, dx->u.hrd.hrd_exp)
    );

    break;

  case TYPE_LAZY_EXP: 
    fprintf(RED_OUT, "\nlazy exp in rec_exclude_with_reduction()\n"); 
    bk(0); 
  case TYPE_FLOAT: {
    float flb, fub; 
    
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 || ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    )
	  new_child = rec_exclude_with_reduction(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );
	else
	  new_child = dx->u.fdd.arc[cix].child;
	fchild_stack_push(new_child, flb, fub);
      }
    }

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    return(ce->result 
      = fdd_new(dx->var_index)
    );
  }
  case TYPE_DOUBLE: {
    double dflb, dfub; 
    
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 || ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound
          ) {
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    )
	  new_child = rec_exclude_with_reduction(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );
	else
	  new_child = dx->u.dfdd.arc[cix].child;
	dfchild_stack_push(new_child, dflb, dfub);
      }
    }

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    return(ce->result = dfdd_new(dx->var_index));
  } 
  default:
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 || ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound) {
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound)
	  new_child = rec_exclude_with_reduction(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	else
	  new_child = dx->u.ddd.arc[cix].child;
	ichild_stack_push(new_child, lb, ub);
      }
    }

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    return(ce->result 
      = ddd_new(dx->var_index)
    );
  }
}
  /* rec_exclude_with_reduction() */




struct red_type	*red_exclude_with_reduction(dx, dy)
	struct red_type	*dx, *dy;
{
  struct red_type	*result;

  if (dx == NORM_FALSE || dy == NORM_FALSE)
    return(dx);

  result = rec_exclude_with_reduction(dx, dy);
  return(result);
}
/* red_exclude_with_reduction() */






#ifdef RED_DEBUG_REDBOP_MODE
int	count_subsume = 0; 
#endif 

struct red_type	*rec_subsume(d)
     struct red_type	*d;
{
  int				ci; 
  struct red_type		*new_child;
  struct cache1_hash_entry_type	*ce; 

  #ifdef RED_DEBUG_REDBOP_MODE
  int				count_local, local_top_level_child_stack;
  #endif 
  
  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE) {
    return(d);
  }

  ce = cache1_check_result_key(OP_SUBSUME, d); 
  if (ce->result) { 
    return(ce->result); 
  } 
  
  #ifdef RED_DEBUG_REDBOP_MODE
  count_subsume++; 
  count_local = count_subsume; 
  if (count_local == 3158) { 
    fprintf(RED_OUT, "Caught!\n"); 
    fflush(RED_OUT); 	
  } 
  #endif 
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    ce->result = bdd_new(d->var_index, 
      rec_subsume(d->u.bdd.zero_child), 
      rec_subsume(d->u.bdd.one_child)
    );
    return(ce->result); 
    break; 

  case TYPE_CRD:
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
      new_child = rec_subsume(d->u.crd.arc[ci].child); 
      if (new_child != NORM_FALSE) 
        bchild_stack_checkpush(new_child, d->u.crd.arc[ci].upper_bound);
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    ce->result = crd_new(d->var_index); 
/*
    if (count_subsume == 8) { 
      fprintf(RED_OUT, "\n=================\nEntering rec_subsume for:\n"); 
      red_print_graph(d); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "\nLeaving rec_subsume for CRD:\n"); 
      red_print_graph(ce->result); 	
    } 
*/
    return(ce->result /* = crd_new(dx->var_index) */);
    break;

  case TYPE_HRD:
    child_stack_level_push();

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subsume(d->u.hrd.arc[ci].child);
      if (new_child != NORM_FALSE) 
        hchild_stack_checkpush(new_child, d->u.hrd.arc[ci].ub_numerator,
 	  d->u.hrd.arc[ci].ub_denominator
	);
    }

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif 

    ce->result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
/*
    if (count_subsume == 8) { 
      fprintf(RED_OUT, "\n==================\nEntering rec_subsume for:\n"); 
      red_print_graph(d); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "\nLeaving rec_subsume for HRD:\n"); 
      red_print_graph(ce->result); 	
    } 
*/
    return(ce->result);
    break;

  case TYPE_LAZY_EXP: 
    ce->result = lazy_subtree(
      rec_subsume(d->u.lazy.false_child), 
      rec_subsume(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    );
    return(ce->result); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push(); 

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subsume(d->u.fdd.arc[ci].child);
      if (new_child != NORM_FALSE) 
	fchild_stack_push(new_child, 
	  d->u.fdd.arc[ci].lower_bound, 
	  d->u.fdd.arc[ci].upper_bound
	);
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif

    ce->result = fdd_new(d->var_index); 
/*
    if (count_subsume == 8) { 
      fprintf(RED_OUT, "\n===================\nEntering rec_subsume for:\n"); 
      red_print_graph(d); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "\nLeaving rec_subsume for DDD:\n"); 
      red_print_graph(ce->result); 	
    } 
*/
    return(ce->result);
  case TYPE_DOUBLE:
    child_stack_level_push(); 

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subsume(d->u.dfdd.arc[ci].child);
      if (new_child != NORM_FALSE) 
	dfchild_stack_push(new_child, 
	  d->u.dfdd.arc[ci].lower_bound, 
	  d->u.dfdd.arc[ci].upper_bound
	);
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif

    ce->result = dfdd_new(d->var_index); 
/*
    if (count_subsume == 8) { 
      fprintf(RED_OUT, "\n===================\nEntering rec_subsume for:\n"); 
      red_print_graph(d); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "\nLeaving rec_subsume for DDD:\n"); 
      red_print_graph(ce->result); 	
    } 
*/
    return(ce->result);
  default:
    child_stack_level_push(); 

    #ifdef RED_DEBUG_REDBOP_MODE
    local_top_level_child_stack = TOP_LEVEL_CHILD_STACK; 
    #endif 

    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subsume(d->u.ddd.arc[ci].child);
      if (new_child != NORM_FALSE) 
	ichild_stack_push(new_child, 
	  d->u.ddd.arc[ci].lower_bound, 
	  d->u.ddd.arc[ci].upper_bound
	);
    } 

    #ifdef RED_DEBUG_REDBOP_MODE
    if (local_top_level_child_stack != TOP_LEVEL_CHILD_STACK) { 
      fprintf(RED_OUT, "inconsistent top level child stack %1d-->%1d.\n", 
        local_top_level_child_stack
      ); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    #endif

    ce->result = ddd_new(d->var_index); 
/*
    if (count_subsume == 8) { 
      fprintf(RED_OUT, "\n===================\nEntering rec_subsume for:\n"); 
      red_print_graph(d); 
      fflush(RED_OUT); 
      fprintf(RED_OUT, "\nLeaving rec_subsume for DDD:\n"); 
      red_print_graph(ce->result); 	
    } 
*/
    return(ce->result);
  }
}
  /* rec_subsume() */




struct red_type	*red_subsume(d)
     struct red_type	*d;
{
  struct red_type	*result;
  int			w, old_size;

  if (d == NORM_FALSE)
    return(d);
/*
  fprintf(RED_OUT, 
    "\n==(Subsume %1d)=============================\nBefore subsumption\n", 
    ++count_subsume
  ); 
  red_print_graph(d); 
*/ 
  old_size = red_size(d, SIZE_SILENT, NULL, NULL);
  result = rec_subsume(d);
/*
  fprintf(RED_OUT, 
    "\n--(Subsume %1d)------------------\nAfter subsumption\n", 
    count_subsume
  ); 
  red_print_graph(d); 
*/  
  if (old_size <= red_size(result, SIZE_SILENT, NULL, NULL))
    return(d);
  else
    return(result);
}
/* red_subsume() */





struct red_type	*rec_ddd_one_project_constraint(d)
     struct red_type	*d;
{
  int				ci, ub, lb;
  struct red_type		*new_child;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ONE_CONSTRAINT_INDEX)
    return(d);
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_DDD_ONE_PROJECT_CONSTRAINT, d, 
    (struct hrd_exp_type *) ONE_CONSTRAINT_INDEX, 
    ONE_CONSTRAINT_UB, 
    ONE_CONSTRAINT_LB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_ddd_one_project_constraint(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    new_child = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_ddd_one_project_constraint(d->u.hrd.arc[ci].child);
      hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
    }
    new_child = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_ddd_one_constraint(d->u.fdd.arc[ci].child);
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
      new_child = rec_ddd_one_constraint(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child,
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound
      );
    } 
    new_child = dfdd_new(d->var_index);
    break;

  default:
    if (d->var_index == ONE_CONSTRAINT_INDEX) {
      new_child = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1;
	   ci >= 0 && d->u.ddd.arc[ci].upper_bound >= ONE_CONSTRAINT_LB;
	   ci--
	   ) {
	if (d->u.ddd.arc[ci].upper_bound <= ONE_CONSTRAINT_UB)
	  ub = d->u.ddd.arc[ci].upper_bound;
	else
	  ub = ONE_CONSTRAINT_UB;
	if (d->u.ddd.arc[ci].lower_bound >= ONE_CONSTRAINT_LB)
	  lb = d->u.ddd.arc[ci].lower_bound;
	else
	  lb = ONE_CONSTRAINT_LB;
	if (lb <= ub) {
	  new_child = red_bop(OR, new_child, d->u.ddd.arc[ci].child);
	}
      }
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	new_child = rec_ddd_one_constraint(d->u.ddd.arc[ci].child);
	ichild_stack_push(new_child,
      			  d->u.ddd.arc[ci].lower_bound,
      			  d->u.ddd.arc[ci].upper_bound
      			  );
      }
      new_child = ddd_new(d->var_index);
    }
  }
  return(ce->result = new_child);
}
  /* rec_ddd_one_project_constraint() */


struct red_type	*ddd_one_project_constraint(d, vi, lb, ub)
     struct red_type	*d;
     int		vi, lb, ub;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

  ONE_CONSTRAINT_INDEX = vi;
  ONE_CONSTRAINT_UB = ub;
  ONE_CONSTRAINT_LB = lb;
  result = rec_ddd_one_project_constraint(d);
  return(result);
}
/* ddd_one_project_constraint() */











/**************************************************************
*
*/


struct red_type	*red_through_all_invariance(w)
     int	w; 
{
  int	pi; 
 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    RT[w] = red_bop(AND, RT[w], RED_INVARIANCE[pi]); 
    if (RT[w] == NORM_FALSE)
      break; 
  } 
  return(RT[w]); 
}
/* red_through_all_invariance() */ 






/**************************************************************
*
*/

int			XVAR_TYPE, XVAR_PI, XVAR_OFFSET;
int			XCLOCK_INC, XVI_INC, XFI_INC, 
			XOFFSET_LB, XOFFSET_UB, XDI_INC, 
			XLB, XUB; 
float			XFLB, XFUB; 
double			XDFLB, XDFUB; 
struct hrd_exp_type	*XHEXP_INC;


int	XVI_LB, XVI_UB; 

struct red_type	*rec_variable_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, j;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (   (   d->var_index > XVI_UB 
          && VAR[XVI_LB].TYPE != TYPE_CLOCK 
          && VAR[XVI_LB].TYPE != TYPE_DENSE 
          && VAR[XVI_UB].TYPE != TYPE_CLOCK 
          && VAR[XVI_UB].TYPE != TYPE_DENSE
          ) 
      || d->var_index == TYPE_TRUE
      || d->var_index == TYPE_FALSE
      )
    return(d);

  ce = cache2_check_result_key(OP_VARIABLE_ELIMINATE, d, 
    (struct red_type *) (VARIABLE_COUNT * XVI_LB + XVI_UB) 
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

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   d->var_index >= XVI_LB
        && d->var_index <= XVI_UB
        ) {
      result = red_bop(OR, d->u.bdd.zero_child, d->u.bdd.one_child); 
    }
    else {
      result = bdd_new(d->var_index, 
        rec_variable_eliminate(d->u.bdd.zero_child), 
        rec_variable_eliminate(d->u.bdd.one_child)
      );
    } 
    break; 

  case TYPE_CRD:
    if (   (   d->var_index >= XVI_LB
            && d->var_index <= XVI_UB
            )
	|| (   CLOCK[VAR[d->var_index].U.CRD.CLOCK1] >= XVI_LB
	    && CLOCK[VAR[d->var_index].U.CRD.CLOCK1] <= XVI_UB
	    )
	|| (   CLOCK[VAR[d->var_index].U.CRD.CLOCK2] >= XVI_LB
	    && CLOCK[VAR[d->var_index].U.CRD.CLOCK2] <= XVI_UB
	)   ) {
      struct crd_child_type	*bc;
      
      result = NORM_FALSE; 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_variable_eliminate(bc->child);
	result = red_bop(OR, result, conj);
      }
    }
    else {
      struct crd_child_type	*bc;
      
      child_stack_level_push();
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_variable_eliminate(bc->child);
        bchild_stack_push(conj, bc->upper_bound);
      }
      result = crd_new(d->var_index);
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (   d->u.hrd.hrd_exp->hrd_term[ci].var_index >= XVI_LB
          && d->u.hrd.hrd_exp->hrd_term[ci].var_index <= XVI_UB
          )
        break;
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      struct hrd_child_type	*hc;
      
      result = NORM_FALSE; 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_variable_eliminate(hc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      struct hrd_child_type	*hc;
      
      child_stack_level_push();
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_variable_eliminate(hc->child);  
        hchild_stack_push(conj, hc->ub_numerator, hc->ub_denominator);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_LAZY_EXP: 
    result = red_lazy_project(
      rec_variable_eliminate(d->u.lazy.false_child), 
      rec_variable_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_MCHUNK, XVI_LB + XVI_UB*VARIABLE_COUNT 
    ); 
    break; 

  case TYPE_FLOAT:
    if (d->var_index >= XVI_LB && d->var_index <= XVI_UB) {
      struct fdd_child_type	*fc;

      result = NORM_FALSE; 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	fc = &(d->u.fdd.arc[ci]);
	result = red_bop(OR, result, rec_variable_eliminate(fc->child)); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct fdd_child_type	*fc;

      child_stack_level_push();
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	fc = &(d->u.fdd.arc[ci]);
	conj = rec_variable_eliminate(fc->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	fchild_stack_push(conj,
      	  fc->lower_bound,
      	  fc->upper_bound
      	);
      }
      result = fdd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break; 

  case TYPE_DOUBLE:
    if (d->var_index >= XVI_LB && d->var_index <= XVI_UB) {
      struct dfdd_child_type	*dfc;

      result = NORM_FALSE; 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	dfc = &(d->u.dfdd.arc[ci]);
	result = red_bop(OR, result, rec_variable_eliminate(dfc->child)); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct dfdd_child_type	*dfc;

      child_stack_level_push();
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	dfc = &(d->u.dfdd.arc[ci]);
	conj = rec_variable_eliminate(dfc->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	dfchild_stack_push(conj,
      	  dfc->lower_bound,
      	  dfc->upper_bound
      	);
      }
      result = dfdd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break; 

  default:
    if (d->var_index >= XVI_LB && d->var_index <= XVI_UB) {
      struct ddd_child_type	*ic;

      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]);
	result = red_bop(OR, result, rec_variable_eliminate(ic->child)); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct ddd_child_type	*ic;

      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]);
	conj = rec_variable_eliminate(ic->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	ichild_stack_push(conj,
      	  ic->lower_bound,
      	  ic->upper_bound
      	);
      }
      result = ddd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break;
  }
/*
  fprintf(RED_OUT, "var_elm(%1d, %x), new result=%x\n", XVI_INC, (unsigned int) d, (unsigned int) result); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
/* rec_variable_eliminate() */


struct red_type	*red_time_clock_eliminate(struct red_type *, int); 

struct red_type	*red_variable_eliminate(d, vi)
     struct red_type	*d;
     int		vi;
{
  struct red_type	*result;

  if (VAR[vi].TYPE == TYPE_CLOCK) { 
    result = red_time_clock_eliminate(
      d, VAR[vi].U.CLOCK.CLOCK_INDEX
    ); 
  } 
  else {
    XVI_LB = vi; 
    XVI_UB = vi; 

    result = rec_variable_eliminate(d);
  }
  return(result);
}
/* red_variable_eliminate() */



struct red_type	*red_multi_variables_eliminate(d, vix, viy)
     struct red_type	*d;
     int		vix, viy;
{
  struct red_type	*result;

  if (   (   VAR[vix].TYPE != TYPE_DISCRETE 
          && VAR[vix].TYPE != TYPE_FLOAT 
          && VAR[vix].TYPE != TYPE_DOUBLE 
          )
      || (   VAR[viy].TYPE != TYPE_DISCRETE
          && VAR[viy].TYPE != TYPE_FLOAT
          && VAR[viy].TYPE != TYPE_DOUBLE
          )
      ) {
    fprintf(RED_OUT, 
      "\nWarning: you cannot use red_multi_variables_eliminate() to \n"); 
    fprintf(RED_OUT, 
      "         eliminate non-discrete, non-float, and non-double.\n");
    fflush(RED_OUT);
    for (; 1; );
  }

  XVI_LB = vix; 
  XVI_UB = viy; 

  result = rec_variable_eliminate(d);

  return(result);
}
/* red_multi_variables_eliminate() */




struct red_type	*rec_variable_sim_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, j;
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

  ce = cache2_check_result_key(OP_VARIABLE_SIM_ELIMINATE, d, 
    (struct red_type *) XVI_INC
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

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && VAR[d->var_index].OFFSET == XVAR_OFFSET
        ) {
      result = red_bop(OR, d->u.bdd.zero_child, d->u.bdd.one_child); 
    }
    else {
      result = bdd_new(d->var_index, 
        rec_variable_sim_eliminate(d->u.bdd.zero_child), 
        rec_variable_sim_eliminate(d->u.bdd.one_child)
      );
    } 
    break; 

  case TYPE_CRD:
    if (   (   XVAR_TYPE == TYPE_CRD
            && VAR[d->var_index].OFFSET == XVAR_OFFSET
            )
        && (   XVAR_TYPE == TYPE_CLOCK
            && (   (   VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX 
                    && VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].OFFSET 
                       == XVAR_OFFSET
                    )
                || (   VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX 
                    && VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].OFFSET 
                       == XVAR_OFFSET
        )   )   )   ) {
      struct crd_child_type	*bc;
      
      result = NORM_FALSE; 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_variable_sim_eliminate(bc->child);
	result = red_bop(OR, result, conj);
      }
    }
    else {
      struct crd_child_type	*bc;
      
      child_stack_level_push();
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_variable_sim_eliminate(bc->child);
        bchild_stack_push(conj, bc->upper_bound);
      }
      result = crd_new(d->var_index);
    }
    break;
  case TYPE_HRD:
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE == XVAR_TYPE
          && VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].OFFSET == XVAR_OFFSET
          )
        break;
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      struct hrd_child_type	*hc;
      
      result = NORM_FALSE; 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_variable_sim_eliminate(hc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      struct hrd_child_type	*hc;
      
      child_stack_level_push();
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_variable_sim_eliminate(hc->child);  
        hchild_stack_push(conj, hc->ub_numerator, hc->ub_denominator);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_variable_sim_eliminate(d->u.lazy.false_child), 
      rec_variable_sim_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_VAR_SIM, XVAR_TYPE + (XVAR_OFFSET * 100000)
    ); 
    break; 

  case TYPE_FLOAT:
    if (   VAR[d->var_index].TYPE == XVAR_TYPE
        && VAR[d->var_index].OFFSET == XVAR_OFFSET
        ) {
      struct fdd_child_type	*fc;
      
      result = NORM_FALSE; 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	fc = &(d->u.fdd.arc[ci]);
	result = red_bop(OR, result, fc->child); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct fdd_child_type	*fc;

      child_stack_level_push();
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
	fc = &(d->u.fdd.arc[ci]);
	conj = rec_variable_sim_eliminate(fc->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	fchild_stack_push(conj,
      	  fc->lower_bound,
      	  fc->upper_bound
      	);
      }
      result = fdd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break; 

  case TYPE_DOUBLE:
    if (   VAR[d->var_index].TYPE == XVAR_TYPE
        && VAR[d->var_index].OFFSET == XVAR_OFFSET
        ) {
      struct dfdd_child_type	*dfc;

      result = NORM_FALSE; 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	dfc = &(d->u.dfdd.arc[ci]);
	result = red_bop(OR, result, dfc->child); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct dfdd_child_type	*dfc;

      child_stack_level_push();
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
	dfc = &(d->u.dfdd.arc[ci]);
	conj = rec_variable_sim_eliminate(dfc->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	dfchild_stack_push(conj,
      	  dfc->lower_bound,
      	  dfc->upper_bound
      	);
      }
      result = dfdd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break; 

  default:
    if (   VAR[d->var_index].TYPE == XVAR_TYPE
        && VAR[d->var_index].OFFSET == XVAR_OFFSET
        ) {
      struct ddd_child_type	*ic;

      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]);
	result = red_bop(OR, result, ic->child); 
        if (   result->var_index >= VARIABLE_COUNT 
            || result->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated variable index %1d\n", 
                  result->var_index
                  ); 
          bk(0); 
        }
      }
    }
    else {
      struct ddd_child_type	*ic;

      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
	ic = &(d->u.ddd.arc[ci]);
	conj = rec_variable_sim_eliminate(ic->child); 
        if (   conj->var_index >= VARIABLE_COUNT 
            || conj->var_index < 0
            ) {
          fprintf(RED_OUT, "A bad eliminated %1d'th child variable index %1d\n", 
                  ci, result->var_index
                  ); 
          bk(0); 
        }
	ichild_stack_push(conj,
      	  ic->lower_bound,
      	  ic->upper_bound
      	);
      }
      result = ddd_new(d->var_index);
      if (   result->var_index >= VARIABLE_COUNT 
          || result->var_index < 0
          ) {
        fprintf(RED_OUT, "A bad structured variable index %1d\n", 
                result->var_index
                ); 
        bk(0); 
      }
    }
    break;
  }
/*
  fprintf(RED_OUT, "var_elm(%1d, %x), new result=%x\n", XVI_INC, (unsigned int) d, (unsigned int) result); 
  red_print_graph(result); 
*/
  return(ce->result = result);
}
/* rec_variable_sim_eliminate() */


struct red_type	*red_time_clock_sim_eliminate(); 

struct red_type	*red_variable_sim_eliminate(
     struct red_type	*d, 
     int		vi
) {
  struct red_type	*result;

  if (VAR[vi].TYPE == TYPE_HRD) {
    fprintf(RED_OUT, "Warning: you cannot use red_variable_eliminate() to eliminate hybrid inequalities.\n");
    fflush(RED_OUT);
    for (; 1; );
  }
  else if (VAR[vi].TYPE == TYPE_CLOCK) { 
    #ifdef RED_DEBUG_REDBOP_MODE
    fprintf(RED_OUT, "Warning: usually we use red_time_clock_eliminate() to eliminate clocks.\n"); 
    fprintf(RED_OUT, "         We now direct it to red_time_clock_eliminate().\n"); 
    fflush(RED_OUT); 
    #endif 
    if (VAR[vi].PROC_INDEX == 0) 
      return(red_time_clock_eliminate(d, VAR[vi].U.CLOCK.CLOCK_INDEX)); 
    else 
      return(red_time_clock_sim_eliminate(d, VAR[vi].U.CLOCK.CLOCK_INDEX)); 
  } 
  if (VAR[vi].PROC_INDEX == 0) { 
    XVI_INC = vi; 
    result = rec_variable_eliminate(d); 
  } 
  else {
    XVAR_TYPE = VAR[vi].TYPE; 
    XVAR_OFFSET = VAR[vi].OFFSET; 
    result = rec_variable_sim_eliminate(d); 
  } 
  return(result); 
}
/* red_variable_sim_eliminate() */





struct red_type	*rec_assign_interval(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *td, *fd, *subresult, *filter;
  int				vi, fi, vi1, fi1, 
				vi2, fi2, lb, ub, ci;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(ddd_atom(XVI_INC, XLB, XUB));
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > XVI_INC)
    return(ddd_one_constraint(d, XVI_INC, XLB, XUB));

  ce = cache4_check_result_key(OP_ASSIGN_INTERVAL, d, 
    (struct hrd_exp_type *) XVI_INC, 
    XLB, 
    XUB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_assign_interval(d->u.bdd.zero_child), 
      rec_assign_interval(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_assign_interval(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_interval(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_interval(d->u.fdd.arc[ci].child);
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
      conj = rec_assign_interval(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(conj, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound 
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default: 
    if (d->var_index == XVI_INC) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.ddd.arc[ci].child);
      }
      result = ddd_lone_subtree(result, XVI_INC, XLB, XUB);
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_assign_interval(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, 
        		  d->u.ddd.arc[ci].lower_bound,
			  d->u.ddd.arc[ci].upper_bound 
			  );
      }
      result = ddd_new(d->var_index);
    }
  }
  return(ce->result = result);
}
/* rec_assign_interval() */



struct red_type	*red_assign_interval( 
  struct red_type	*d, 
  int			vi, 
  int			lb, 
  int			ub 
) {
  struct red_type	*result;

  XVI_INC = vi;
  XLB = lb; 
  XUB = ub; 

  result = rec_assign_interval(d);

  return(result);
}
/* red_assign_interval() */






struct red_type	*rec_assign_float_interval(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *td, *fd, 
				*subresult, *filter;
  int				vi, fi, vi1, fi1, 
				vi2, fi2, lb, ub, ci;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(fdd_atom(XVI_INC, XFLB, XFUB));
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > XVI_INC)
    return(fdd_one_constraint(d, XVI_INC, XFLB, XFUB));

  ce = cache4_check_result_key(OP_ASSIGN_INTERVAL, d, 
    (struct hrd_exp_type *) XVI_INC, 
    *((int *) &XFLB), 
    *((int *) &XFUB)
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_assign_float_interval(d->u.bdd.zero_child), 
      rec_assign_float_interval(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_assign_float_interval(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_float_interval(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    if (d->var_index == XVI_INC) {
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.fdd.arc[ci].child);
      }
      result = fdd_lone_subtree(result, XVI_INC, XFLB, XFUB);
    }
    else {
      child_stack_level_push();
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_assign_float_interval(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, 
          d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound 
        );
      }
      result = fdd_new(d->var_index);
    }   
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_float_interval(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(conj, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound 
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default: 
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_float_interval(d->u.ddd.arc[ci].child);
      ichild_stack_push(conj, 
        d->u.ddd.arc[ci].lower_bound,
	d->u.ddd.arc[ci].upper_bound 
      );
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
/* rec_assign_float_interval() */



struct red_type	*red_assign_float_interval( 
  struct red_type	*d, 
  int			vi,  
  float			lb, 
  float			ub 
) {
  struct red_type	*result;

  XVI_INC = vi;
  XFLB = lb; 
  XFUB = ub; 

  result = rec_assign_float_interval(d);

  return(result);
}
/* red_assign_float_interval() */



struct red_type	*rec_assign_double_interval(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *td, *fd, 
				*subresult, *filter;
  int				vi, fi, vi1, fi1, 
				vi2, fi2, lb, ub, ci;
  struct cache7_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(dfdd_atom(XVI_INC, XFLB, XFUB));
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > XVI_INC)
    return(dfdd_one_constraint(d, XVI_INC, XDFLB, XDFUB));

  fd = (struct red_type *) &XDFLB; 
  vi1 = ((int *) fd)[0]; 
  fi1 = ((int *) fd)[1]; 
  
  fd = (struct red_type *) &XDFUB; 
  vi2 = ((int *) fd)[0]; 
  fi2 = ((int *) fd)[1]; 
  
  ce = cache7_check_result_key(OP_ASSIGN_INTERVAL_DOUBLE, d, 
    (struct hrd_exp_type *) XVI_INC, vi1, fi1, 
    (struct hrd_exp_type *) vi2, fi2, 0 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_assign_double_interval(d->u.bdd.zero_child), 
      rec_assign_double_interval(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_assign_double_interval(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_double_interval(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_double_interval(d->u.fdd.arc[ci].child);
      fchild_stack_push(conj, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound 
      );
    }
    result = fdd_new(d->var_index);
    break; 
  case TYPE_DOUBLE: 
    if (d->var_index == XVI_INC) {
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.dfdd.arc[ci].child);
      }
      result = dfdd_lone_subtree(result, XVI_INC, XDFLB, XDFUB);
    }
    else {
      child_stack_level_push();
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_assign_double_interval(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, 
          d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound 
        );
      }
      result = dfdd_new(d->var_index);
    }   
    break; 
  default: 
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_double_interval(d->u.ddd.arc[ci].child);
      ichild_stack_push(conj, 
        d->u.ddd.arc[ci].lower_bound,
	d->u.ddd.arc[ci].upper_bound 
      );
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
/* rec_assign_double_interval() */



struct red_type	*red_assign_double_interval(
  struct red_type	*d, 
  int			vi,  
  double		lb, 
  double		ub 
) {
  struct red_type	*result;

  XVI_INC = vi;
  XDFLB = lb; 
  XDFUB = ub; 

  result = rec_assign_double_interval(d);

  return(result);
}
/* red_assign_double_interval() */






struct red_type	*rec_assign_bound(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(crd_atom(XVI_INC, XUB));
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > XVI_INC)
    return(crd_one_constraint(d, XVI_INC, XUB));

  ce = cache4_check_result_key(OP_ZONE_ASSIGN_BOUND, d, 
    (struct hrd_exp_type *) XVI_INC, XUB, 0
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_assign_bound(d->u.bdd.zero_child), 
      rec_assign_bound(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    if (d->var_index == XVI_INC) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.crd.arc[ci].child);
      }
      return(ce->result
        = crd_one_constraint(result, XVI_INC, XUB)
      );
    }
    else {
      child_stack_level_push();
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_assign_bound(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index); 
    }
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_bound(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_bound(d->u.fdd.arc[ci].child);
      fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_bound(d->u.dfdd.arc[ci].child);
      fchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default: 
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_assign_bound(d->u.ddd.arc[ci].child);
      ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
/* rec_assign_bound() */



struct red_type	*zone_assign_bound(d, vi, ub)
     struct red_type	*d;
     int		vi, ub;
{
  struct red_type	*result;

  if (VAR[vi].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError: a non clock inequality in zone_assign_bound() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  XVI_INC = vi;
  XUB = ub;

  result = rec_assign_bound(d);

  return(result);
}
/* zone_assign_bound() */




struct hrd_exp_type	*XHEXP_INC; 
int			XUB_NUM, XUB_DEN;


struct red_type	*rec_hybrid_assign_bound(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(hrd_atom(XVI_INC, XHEXP_INC, XUB_NUM, XUB_DEN));
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > XVI_INC)
    return(hrd_one_constraint(d, XHEXP_INC, XUB_NUM, XUB_DEN));

  ce = cache4_check_result_key(
    OP_HYBRID_ASSIGN_BOUND, d, 
    XHEXP_INC, XUB_NUM, XUB_DEN
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_hybrid_assign_bound(d->u.bdd.zero_child), 
      rec_hybrid_assign_bound(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_hybrid_assign_bound(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    if (d->var_index == XVI_INC && d->u.hrd.hrd_exp == XHEXP_INC) {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.hrd.arc[ci].child);
      }
      return(ce->result 
        = hrd_one_constraint(result, XHEXP_INC, XUB_NUM, XUB_DEN)
      ); 
    }
    else {
      child_stack_level_push();
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        conj = rec_hybrid_assign_bound(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_hybrid_assign_bound(d->u.fdd.arc[ci].child);
      fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
			d->u.fdd.arc[ci].upper_bound
			); 
    } 
    result = fdd_new(d->var_index);
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_hybrid_assign_bound(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
			d->u.dfdd.arc[ci].upper_bound
			); 
    } 
    result = dfdd_new(d->var_index);
    break; 
  default: 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_hybrid_assign_bound(d->u.ddd.arc[ci].child);
      ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			); 
    } 
    result = ddd_new(d->var_index);
  }
  return(ce->result = result);
}
/* rec_assign_bound() */



struct red_type	*hybrid_assign_bound(d, vi, hrd_exp, ub_numerator, ub_denominator)
     struct red_type		*d;
     int			vi, ub_numerator, ub_denominator;
     struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*result;

  if (VAR[vi].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError: a non clock inequality in zone_assign_bound() \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  XVI_INC = vi;
  XHEXP_INC = hrd_exp; 
  XUB_NUM = ub_numerator;
  XUB_DEN = ub_denominator;

   result = rec_hybrid_assign_bound(d);

  return(result);
}
/* hybrid_assign_bound() */





struct red_type *rec_type_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
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

  ce = cache2_check_result_key(OP_TYPE_ELIMINATE, 
    d, (struct red_type *) XVAR_TYPE
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (VAR[d->var_index].TYPE == XVAR_TYPE) {
      result = red_bop(OR, 
        rec_type_eliminate(d->u.bdd.zero_child), 
        rec_type_eliminate(d->u.bdd.one_child)
      ); 
    }
    else { 
      result = bdd_new(d->var_index, 
        rec_type_eliminate(d->u.bdd.zero_child), 
        rec_type_eliminate(d->u.bdd.one_child)
      );
    } 
    break; 
  case TYPE_CRD: 
    if (TYPE_CRD == XVAR_TYPE) {
      result = NORM_FALSE; 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_type_eliminate(d->u.crd.arc[ci].child)
        );
      } 
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_type_eliminate(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index); 
    }
    break; 
  case TYPE_HRD: 
    if (TYPE_HRD == XVAR_TYPE) {
      result = NORM_FALSE; 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, 
          result, rec_type_eliminate(d->u.hrd.arc[ci].child)
        );
      }
    } 
    else { 
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        conj = rec_type_eliminate(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, 
      	  d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = rec_type_eliminate(d->u.lazy.false_child); 
    conj = rec_type_eliminate(d->u.lazy.true_child); 
    if (TYPE_LAZY_EXP == XVAR_TYPE) {
      result = red_bop(OR, result, conj); 
    } 
    else { 
      result = red_lazy_project(result, conj, d, PROJECT_TYPE, XVAR_TYPE); 
    }  
    break; 

  case TYPE_FLOAT: 
    if (VAR[d->var_index].TYPE == XVAR_TYPE) {
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_type_eliminate(d->u.fdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci>=0; ci--) {
        conj = rec_type_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
			d->u.fdd.arc[ci].upper_bound
			);
      }
      result = fdd_new(d->var_index);
    } 
    break; 

  case TYPE_DOUBLE: 
    if (VAR[d->var_index].TYPE == XVAR_TYPE) {
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_type_eliminate(d->u.dfdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci>=0; ci--) {
        conj = rec_type_eliminate(d->u.dfdd.arc[ci].child);
        fchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
			d->u.dfdd.arc[ci].upper_bound
			);
      }
      result = dfdd_new(d->var_index);
    } 
    break; 

  default: 
    if (VAR[d->var_index].TYPE == XVAR_TYPE) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_type_eliminate(d->u.ddd.arc[ci].child));
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci>=0; ci--) {
        conj = rec_type_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
      }
      result = ddd_new(d->var_index);
    } 
  }
  return(ce->result = result);
}
/* rec_type_eliminate() */



struct red_type	*red_type_eliminate(d, type)
     struct red_type	*d;
     int		type; 
{
  struct red_type	*result;

  XVAR_TYPE = type;

  result = rec_type_eliminate(d);

  return(result);
}
/* red_type_eliminate() */







struct red_type *rec_pi_type_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_PI_TYPE_ELIMINATE, d, 
    NULL, 
    XVAR_TYPE, 
    XVAR_PI
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && VAR[d->var_index].PROC_INDEX == XVAR_PI
        ) {
      result = red_bop(OR, 
        rec_pi_type_eliminate(d->u.bdd.zero_child), 
        rec_pi_type_eliminate(d->u.bdd.one_child)
      ); 
    }
    else {
      result = bdd_new(d->var_index, 
        rec_pi_type_eliminate(d->u.bdd.zero_child), 
        rec_pi_type_eliminate(d->u.bdd.one_child)
      );
    }
    break; 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_pi_type_eliminate(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_pi_type_eliminate(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 

  case TYPE_FLOAT: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && VAR[d->var_index].PROC_INDEX == XVAR_PI
        ) {
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_pi_type_eliminate(d->u.fdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_pi_type_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
			  d->u.fdd.arc[ci].upper_bound);
      }
      result = fdd_new(d->var_index);
    }
    break; 

  case TYPE_DOUBLE: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && VAR[d->var_index].PROC_INDEX == XVAR_PI
        ) {
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_pi_type_eliminate(d->u.dfdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_pi_type_eliminate(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
			  d->u.dfdd.arc[ci].upper_bound);
      }
      result = dfdd_new(d->var_index);
    }
    break; 

  default: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && VAR[d->var_index].PROC_INDEX == XVAR_PI
        ) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_pi_type_eliminate(d->u.ddd.arc[ci].child));
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_pi_type_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			  d->u.ddd.arc[ci].upper_bound);
      }
      result = ddd_new(d->var_index);
    }
  }
  return(ce->result = result);
}
/* rec_pi_type_eliminate() */



struct red_type	*red_pi_type_eliminate(d, type, pi)
     struct red_type	*d; 
     int		type, pi; 
{
  struct red_type	*result;

  XVAR_TYPE = type;
  XVAR_PI = pi; 

  result = rec_pi_type_eliminate(d);

  return(result);
}
/* red_pi_type_eliminate() */



int	XVAR_ROLES; 

struct red_type *rec_role_type_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
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

  ce = cache2_check_result_key(OP_ROLE_TYPE_ELIMINATE, d,  
    (struct red_type *) (XVAR_TYPE * 8 + XVAR_ROLES)  
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && (PROCESS[VAR[d->var_index].PROC_INDEX].status & XVAR_ROLES) 
        ) {
      result = red_bop(OR, 
        rec_role_type_eliminate(d->u.bdd.zero_child), 
        rec_role_type_eliminate(d->u.bdd.one_child)
      ); 
    }
    else {
      result = bdd_new(d->var_index, 
        rec_role_type_eliminate(d->u.bdd.zero_child), 
        rec_role_type_eliminate(d->u.bdd.one_child)
      );
    }
    break; 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_role_type_eliminate(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_role_type_eliminate(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && (PROCESS[VAR[d->var_index].PROC_INDEX].status & XVAR_ROLES) 
        ) {
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_role_type_eliminate(d->u.fdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_role_type_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
			  d->u.fdd.arc[ci].upper_bound);
      }
      result = fdd_new(d->var_index);
    }
    break; 
  case TYPE_DOUBLE: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && (PROCESS[VAR[d->var_index].PROC_INDEX].status & XVAR_ROLES) 
        ) {
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_role_type_eliminate(d->u.dfdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_role_type_eliminate(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
			  d->u.dfdd.arc[ci].upper_bound);
      }
      result = dfdd_new(d->var_index);
    }
    break; 
  default: 
    if (   VAR[d->var_index].TYPE == XVAR_TYPE 
        && (PROCESS[VAR[d->var_index].PROC_INDEX].status & XVAR_ROLES) 
        ) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_role_type_eliminate(d->u.ddd.arc[ci].child));
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_role_type_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			  d->u.ddd.arc[ci].upper_bound);
      }
      result = ddd_new(d->var_index);
    }
  }
  return(ce->result = result);
}
/* rec_role_type_eliminate() */



struct red_type	*red_role_type_eliminate(d, type, flag_roles)
     struct red_type	*d; 
     int		type, flag_roles; 
{
  struct red_type	*result;

  XVAR_TYPE = type;
  XVAR_ROLES = flag_roles; 

  result = rec_role_type_eliminate(d);

  return(result);
}
/* red_role_type_eliminate() */





/* This procedure in evaluating the precondition of 
 * precondition-event-postcondition triples in state-event model-checking. 
 * The postcondition are specified with primed variables. 
 * To use the precondition evaluation procedure in REDLIB, 
 * we thus need to switch primed and umprimed variables. 
 *
 * The procedure is used in pair with red_lower_all_primed() in the following. 
 * After we have computed the precondition with those umprimed variables, 
 * we have to change the primed variables to umprimed and calculate the 
 * new diagram as a restriction of only umprimed variables. 
 * 
 * Note that for this procedure, we cannot use 
 * child_stack_level_push(), bchild_stack_push(), ichild_stack_push(), 
 * crd_new(), ddd_new() since we may change the variable ordering. 
 */ 
struct red_type *rec_switch_primed_and_umprimed(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, c1, c2, vi;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_SWITCH_PRIMED_AND_UMPRIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    result = NORM_FALSE; 
    c1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    if (c1) 
      if (VAR[c1].STATUS & FLAG_VAR_PRIMED) 
        c1 = VAR[VAR[c1].UMPRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c1 = VAR[VAR[c1].PRIMED_VI].U.CLOCK.CLOCK_INDEX; 
    c2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2]; 
    if (c2) 
      if (VAR[c2].STATUS & FLAG_VAR_PRIMED) 
        c2 = VAR[VAR[c2].UMPRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c2 = VAR[VAR[c2].PRIMED_VI].U.CLOCK.CLOCK_INDEX; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_switch_primed_and_umprimed(d->u.crd.arc[ci].child);
      result = red_bop(OR, result, 
        crd_one_constraint(conj, ZONE[c1][c2], 
          d->u.crd.arc[ci].upper_bound
      ) ); 
    }
    break; 
  case TYPE_HRD: 
    fprintf(RED_OUT, "Sorry that the primed-lowering operation has not\n"); 
    fprintf(RED_OUT, "been implemented for linear hybrid expressions.\n"); 
    fprintf(RED_OUT, "The reason is that this operation should only be \n"); 
    fprintf(RED_OUT, "used for tctl model-checking which has not been \n"); 
    fprintf(RED_OUT, "by RED for linear hybrid automata yet. \n"); 
    exit(0); 
  case TYPE_FLOAT:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    else 
      vi = VAR[vi].PRIMED_VI; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_switch_primed_and_umprimed(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, 
        fdd_one_constraint(conj, vi,  
	  d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  case TYPE_DOUBLE:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    else 
      vi = VAR[vi].PRIMED_VI; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_switch_primed_and_umprimed(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, 
        dfdd_one_constraint(conj, vi,  
	  d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  default:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    else 
      vi = VAR[vi].PRIMED_VI; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_switch_primed_and_umprimed(d->u.ddd.arc[ci].child);
      result = red_bop(OR, result, 
        ddd_one_constraint(conj, vi,  
	  d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound 
      ) );
    }
  }
  return(ce->result = result);
}
/* rec_switch_primed_and_umprimed() */



  
struct red_type	*red_switch_primed_and_umprimed(struct red_type	*d) { 
  struct red_type	*result;

  result = rec_switch_primed_and_umprimed(d);

  return(result);	
}
  /* red_switch_primed_and_umprimed() */ 
  
  



/* This procedure in evaluating the precondition of 
 * precondition-event-postcondition triples in state-event model-checking. 
 * The postcondition are specified with primed variables. 
 * To use the precondition evaluation procedure in REDLIB, 
 * we thus need to switch primed and umprimed variables. 
 *
 * The procedure is used in pair with red_switch_primed_and_umprimed() 
 * in the following. 
 * After we have computed the precondition with those umprimed variables, 
 * we have to change the primed variables to umprimed and calculate the 
 * new diagram as a restriction of only umprimed variables. 
 * 
 * Note that for this procedure, we cannot use 
 * child_stack_level_push(), bchild_stack_push(), ichild_stack_push(), 
 * crd_new(), ddd_new() since we may change the variable ordering. 
 */ 
struct red_type *rec_lower_all_primed(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, c1, c2, vi;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_LOWER_ALL_PRIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    result = NORM_FALSE; 
    c1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    if (c1) 
      if (VAR[c1].STATUS & FLAG_VAR_PRIMED) 
        c1 = VAR[VAR[c1].UMPRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c1 = VAR[c1].U.CLOCK.CLOCK_INDEX; 
    c2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2]; 
    if (c2) 
      if (VAR[c2].STATUS & FLAG_VAR_PRIMED) 
        c2 = VAR[VAR[c2].UMPRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c2 = VAR[c2].U.CLOCK.CLOCK_INDEX; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_lower_all_primed(d->u.crd.arc[ci].child);
      result = red_bop(OR , result, 
        crd_one_constraint(conj, ZONE[c1][c2], d->u.crd.arc[ci].upper_bound)
      );
    }
    break; 
  case TYPE_HRD: 
    fprintf(RED_OUT, "Sorry that the primed-lowering operation has not\n"); 
    fprintf(RED_OUT, "been implemented for linear hybrid expressions.\n"); 
    fprintf(RED_OUT, "The reason is that this operation should only be \n"); 
    fprintf(RED_OUT, "used for tctl model-checking which has not been \n"); 
    fprintf(RED_OUT, "by RED for linear hybrid automata yet. \n"); 
    exit(0); 
  case TYPE_FLOAT:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_lower_all_primed(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, 
        fdd_one_constraint(conj, vi, 
	  d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  case TYPE_DOUBLE:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_lower_all_primed(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, 
        dfdd_one_constraint(conj, vi, 
	  d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  default:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (VAR[vi].STATUS & FLAG_VAR_PRIMED) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_lower_all_primed(d->u.ddd.arc[ci].child);
      result = red_bop(OR, result, 
        ddd_one_constraint(conj, vi, 
	  d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound 
      ) );
    }
  }
  return(ce->result = result);
}
/* rec_lower_all_primed() */



struct red_type	*red_lower_all_primed(d) 
	struct red_type	*d; 
{ 
  struct red_type	*result;

  result = rec_lower_all_primed(d);

  return(result);
}
  /* red_lower_all_primed() */ 
  
  

struct red_type *rec_lift_all_umprimed(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, c1, c2, vi;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_LIFT_ALL_UMPRIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    result = NORM_FALSE; 
    c1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    if (c1) 
      if (!(VAR[c1].STATUS & FLAG_VAR_PRIMED)) 
        c1 = VAR[VAR[c1].PRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c1 = VAR[c1].U.CLOCK.CLOCK_INDEX; 
    c2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2]; 
    if (c2) 
      if (!(VAR[c2].STATUS & FLAG_VAR_PRIMED)) 
        c2 = VAR[VAR[c2].PRIMED_VI].U.CLOCK.CLOCK_INDEX; 
      else 
        c2 = VAR[c2].U.CLOCK.CLOCK_INDEX; 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      conj = rec_lift_all_umprimed(d->u.crd.arc[ci].child);
      result = red_bop(OR , result, 
        crd_one_constraint(conj, ZONE[c1][c2], d->u.crd.arc[ci].upper_bound)
      );
    }
    break; 
  case TYPE_HRD: 
    fprintf(RED_OUT, "Sorry that the primed-lowering operation has not\n"); 
    fprintf(RED_OUT, "been implemented for linear hybrid expressions.\n"); 
    fprintf(RED_OUT, "The reason is that this operation should only be \n"); 
    fprintf(RED_OUT, "used for tctl model-checking which has not been \n"); 
    fprintf(RED_OUT, "by RED for linear hybrid automata yet. \n"); 
    exit(0); 
  case TYPE_FLOAT:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_lift_all_umprimed(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, 
        fdd_one_constraint(conj, vi, 
	  d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  case TYPE_DOUBLE:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_lift_all_umprimed(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, 
        dfdd_one_constraint(conj, vi, 
	  d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound 
      ) );
    }
    break; 
  default:  
    result = NORM_FALSE; 
    vi = d->var_index; 
    if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) 
      vi = VAR[vi].UMPRIMED_VI; 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      conj = rec_lift_all_umprimed(d->u.ddd.arc[ci].child);
      result = red_bop(OR, result, 
        ddd_one_constraint(conj, vi, 
	  d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound 
      ) );
    }
  }
  return(ce->result = result);
}
/* rec_lift_all_umprimed() */



struct red_type	*red_lift_all_umprimed(d) 
	struct red_type	*d; 
{ 
  struct red_type	*result;

  result = rec_lift_all_umprimed(d);

  return(result);
}
  /* red_lift_all_umprimed() */ 
  
  

struct red_type *rec_local_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_LOCAL_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    if (   VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX
	|| VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX
	) { 
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_local_eliminate(d->u.crd.arc[ci].child));
      }
    } 
    else {
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_local_eliminate(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, 
          d->u.crd.arc[ci].upper_bound
        );
      }
      result = crd_new(d->var_index); 
    }
    break; 
  case TYPE_HRD: 
    if (d->u.hrd.hrd_exp->status & FLAG_LOCAL_HYBRID_VARIABLES) { 
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_local_eliminate(d->u.hrd.arc[ci].child));
      }
    } 
    else {
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        conj = rec_local_eliminate(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator 
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project(
      rec_local_eliminate(d->u.lazy.false_child), 
      rec_local_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_LOCAL, FLAG_XVI_LOCAL_ELIMINATE
    ); 
    break; 

  case TYPE_FLOAT: 
    if (VAR[d->var_index].PROC_INDEX) {
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_local_eliminate(d->u.fdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_local_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound
	);
      }
      result = fdd_new(d->var_index); 
    }
    break; 

  case TYPE_DOUBLE: 
    if (VAR[d->var_index].PROC_INDEX) {
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, 
          rec_local_eliminate(d->u.dfdd.arc[ci].child)
        );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_local_eliminate(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound
	);
      }
      result = dfdd_new(d->var_index); 
    }
    break; 

  default: 
    if (VAR[d->var_index].PROC_INDEX) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, rec_local_eliminate(d->u.ddd.arc[ci].child));
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_local_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			  d->u.ddd.arc[ci].upper_bound);
      }
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_local_eliminate() */



struct red_type	*red_local_eliminate(d)
  struct red_type	*d;
{
  struct red_type	*result;

  result = rec_local_eliminate(d);

  return(result);
}
/* red_local_eliminate() */






struct red_type	*rec_sync_place_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_SYNC_PLACE_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      struct crd_child_type	*bc;

      bc = &(d->u.crd.arc[ci]);
      conj = rec_sync_place_eliminate(bc->child);
      bchild_stack_push(conj, bc->upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      struct hrd_child_type	*hc;
      
      hc = &(d->u.hrd.arc[ci]);
      conj = rec_sync_place_eliminate(hc->child);
      hchild_stack_push(conj, hc->ub_numerator,
			hc->ub_denominator 
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      struct fdd_child_type	*fc;

      fc = &(d->u.fdd.arc[ci]);
      conj = rec_sync_place_eliminate(fc->child);
      fchild_stack_push(
        conj, fc->lower_bound, fc->upper_bound
      );
    }
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      struct dfdd_child_type	*dfc;

      dfc = &(d->u.dfdd.arc[ci]);
      conj = rec_sync_place_eliminate(dfc->child);
      dfchild_stack_push(
        conj, dfc->lower_bound, dfc->upper_bound
      );
    }
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    if (VAR[d->var_index].STATUS & FLAG_SYNC_PLACE) {
      struct ddd_child_type	*ic;

      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_sync_place_eliminate(ic->child);
        result = red_bop(OR, result, conj);
      }
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        struct ddd_child_type	*ic;

        ic = &(d->u.ddd.arc[ci]);
        conj = rec_sync_place_eliminate(ic->child);
        ichild_stack_push(
          conj, ic->lower_bound, ic->upper_bound
        );
      }
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_sync_place_eliminate() */




/* We have not taken care of inequalities like x = y */
struct red_type	*red_sync_place_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_sync_place_eliminate(d);

  return(result);
}
/* red_sync_place_eliminate() */





struct red_type	*rec_qsync_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_QSYNC_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    if (d->status & FLAG_RED_LAZY) { 
      result = NORM_FALSE;  
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.crd.arc[ci].child);
        result = red_bop(OR, result, 
          crd_one_constraint(conj, 
            d->var_index, d->u.crd.arc[ci].upper_bound
        ) );
      } 
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
      } 
      result = crd_new(d->var_index); 
    }
    break; 
  case TYPE_HRD: 
    if (d->status & FLAG_RED_LAZY) { 
      result = NORM_FALSE; 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.hrd.arc[ci].child);
        result = red_bop(OR, result, 
          hrd_one_constraint(conj, 
            d->u.hrd.hrd_exp, d->u.hrd.arc[ci].ub_numerator,
	    d->u.hrd.arc[ci].ub_denominator
	) );
      } 
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
      } 
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project(
      rec_qsync_eliminate(d->u.lazy.false_child), 
      rec_qsync_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_QSYNC, FLAG_XVI_QSYNC_ELIMINATE
    ); 
    break; 

  case TYPE_FLOAT: 
    if (d->status & FLAG_RED_LAZY) { 
      result = NORM_FALSE; 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.fdd.arc[ci].child);
        result = red_bop(OR, result, 
          fdd_one_constraint(conj, 
            d->var_index, 
            d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        ) );
      } 
    } 
    else { 
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, 
          d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
        );
      } 
      result = fdd_new(d->var_index); 
    }
    break; 

  case TYPE_DOUBLE: 
    if (d->status & FLAG_RED_LAZY) { 
      result = NORM_FALSE; 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.dfdd.arc[ci].child);
        result = red_bop(OR, result, 
          dfdd_one_constraint(conj, 
            d->var_index, 
            d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        ) );
      } 
    } 
    else { 
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, 
          d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
        );
      } 
      result = dfdd_new(d->var_index); 
    }
    break; 

  default: 
    if (   VAR[d->var_index].TYPE == TYPE_POINTER
        && VAR[d->var_index].PROC_INDEX 
        && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.ddd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else if (d->status & FLAG_RED_LAZY) { 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.ddd.arc[ci].child);
        result = red_bop(OR, result, 
          ddd_one_constraint(conj, 
            d->var_index, 
            d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
        ) );
      } 
    } 
    else { 
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_qsync_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, 
          d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
        );
      } 
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_qsync_eliminate() */




/* We have not taken care of inequalities like x = y */
struct red_type	*red_qsync_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_qsync_eliminate(d);

  return(result);
}
/* red_qsync_eliminate() */






struct red_type	*rec_pi_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_PI_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    ce->result = bdd_new(d->var_index, 
      rec_pi_eliminate(d->u.bdd.zero_child), 
      rec_pi_eliminate(d->u.bdd.one_child)
    );
    return(ce->result); 
    break; 

  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      struct crd_child_type	*bc;

      bc = &(d->u.crd.arc[ci]);
      conj = rec_pi_eliminate(bc->child);
      bchild_stack_push(conj, bc->upper_bound);
    } 
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      struct hrd_child_type	*hc;

      hc = &(d->u.hrd.arc[ci]);
      conj = rec_pi_eliminate(hc->child); 
      hchild_stack_push(conj, hc->ub_numerator,
			hc->ub_denominator 
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_pi_eliminate(d->u.lazy.false_child), 
      rec_pi_eliminate(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    ); 
    break; 

  case TYPE_FLOAT: {
    struct fdd_child_type	*fc;

    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fc = &(d->u.fdd.arc[ci]);
      conj = rec_pi_eliminate(fc->child);
      fchild_stack_push(conj, fc->lower_bound, fc->upper_bound);
    }
    result = fdd_new(d->var_index); 
    break; 
  }
  case TYPE_DOUBLE: {
    struct dfdd_child_type	*dfc;

    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfc = &(d->u.dfdd.arc[ci]);
      conj = rec_pi_eliminate(dfc->child);
      dfchild_stack_push(conj, dfc->lower_bound, dfc->upper_bound);
    }
    result = dfdd_new(d->var_index); 
    break; 
  }
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_XTION_INSTANCE
        || VAR[d->var_index].TYPE == TYPE_ACTION_INSTANCE
        ) {
      struct ddd_child_type	*ic;

      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_pi_eliminate(ic->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      struct ddd_child_type	*ic;

      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_pi_eliminate(ic->child);
        ichild_stack_push(conj, ic->lower_bound, ic->upper_bound);
      }
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_pi_eliminate() */




/* We have not taken care of inequalities like x = y */
struct red_type	*red_pi_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_pi_eliminate(d);

  return(result);
}
/* red_pi_eliminate() */





int	PI_LB_PROC, PI_UB_PROC; 

struct red_type	*rec_proc_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, cv1, cv2;
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

  ce = cache2_check_result_key(OP_PROC_ELIMINATE, d, 
    (struct red_type *) ((PROCESS_COUNT + 1)* PI_UB_PROC + PI_LB_PROC)
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    cv1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    cv2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2]; 
    if (   (   VAR[cv1].PROC_INDEX >= PI_LB_PROC
            && VAR[cv1].PROC_INDEX <= PI_UB_PROC
            )
        || (   VAR[cv2].PROC_INDEX >= PI_LB_PROC
            && VAR[cv2].PROC_INDEX <= PI_UB_PROC
            )
        ) { 
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.crd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound); 
      }
      result = crd_new(d->var_index); 
    }
    break; 
  case TYPE_HRD: 
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX 
             >= PI_LB_PROC
          && VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX 
             <= PI_UB_PROC
          ) 
        break; 
        
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.hrd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator 
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_proc_eliminate(d->u.lazy.false_child), 
      rec_proc_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_PROC, PI_UB_PROC * (PROCESS_COUNT+1) + PI_LB_PROC 
    ); 
    break; 

  case TYPE_FLOAT: 
    if (   VAR[d->var_index].PROC_INDEX >= PI_LB_PROC
	&& VAR[d->var_index].PROC_INDEX <= PI_UB_PROC
	) { 
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.fdd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound, 
          d->u.fdd.arc[ci].upper_bound
        );
      }
      result = fdd_new(d->var_index); 
    }
    break; 

  case TYPE_DOUBLE: 
    if (   VAR[d->var_index].PROC_INDEX >= PI_LB_PROC
	&& VAR[d->var_index].PROC_INDEX <= PI_UB_PROC
	) { 
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.dfdd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound, 
          d->u.dfdd.arc[ci].upper_bound
        );
      }
      result = dfdd_new(d->var_index); 
    }
    break; 

  default: 
    if (   (   VAR[d->var_index].TYPE != TYPE_DISCRETE
            || (!VAR[d->var_index].PROC_INDEX)
            || VAR[d->var_index].OFFSET != OFFSET_MODE
            ) 
        && VAR[d->var_index].PROC_INDEX >= PI_LB_PROC
	&& VAR[d->var_index].PROC_INDEX <= PI_UB_PROC
	) { 
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.ddd.arc[ci].child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_proc_eliminate(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound, 
          d->u.ddd.arc[ci].upper_bound
        );
      }
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_proc_eliminate() */



/* We have not taken care of inequalities like x = y */
struct red_type	*red_proc_eliminate(
  struct red_type	*d, 
  int			pi, 
  int			pj 
) {
  struct red_type	*result;

  PI_LB_PROC = pi; 
  PI_UB_PROC = pj; 
  
  result = rec_proc_eliminate(d);

  return(result);
}
/* red_proc_eliminate() */






int	PI_PEER; 

struct red_type	*rec_peer_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, cv1, cv2;
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

  ce = cache2_check_result_key(OP_PEER_ELIMINATE, d, 
    (struct red_type *) PI_PEER
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: {
    struct crd_child_type	*bc; 
    
    cv1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    cv2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2]; 
    if (   (VAR[cv1].PROC_INDEX && VAR[cv1].PROC_INDEX != PI_PEER)
        || (VAR[cv2].PROC_INDEX && VAR[cv2].PROC_INDEX != PI_PEER)
        ) { 
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        conj = rec_peer_eliminate(bc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else { 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        conj = rec_peer_eliminate(bc->child);
        bchild_stack_push(conj, bc->upper_bound); 
      }
      result = crd_new(d->var_index); 
    }
    break; 
  }
  case TYPE_HRD: {
    struct hrd_child_type	*hc;
    
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          && VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX != PI_PEER
          ) 
        break; 
        
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_peer_eliminate(hc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else { 
        child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        conj = rec_peer_eliminate(hc->child);
        hchild_stack_push(conj, hc->ub_numerator,
			  hc->ub_denominator 
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break; 
  }
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_peer_eliminate(d->u.lazy.false_child), 
      rec_peer_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_PEER, PI_PEER
    ); 
    break; 

  case TYPE_FLOAT: {
    struct fdd_child_type	*fc;

    if (   VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].PROC_INDEX != PI_PEER
	) { 
      result = NORM_FALSE;
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        fc = &(d->u.fdd.arc[ci]);
        conj = rec_peer_eliminate(fc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        fc = &(d->u.fdd.arc[ci]);
        conj = rec_peer_eliminate(fc->child);
        fchild_stack_push(conj, fc->lower_bound, 
          fc->upper_bound
        );
      }
      result = fdd_new(d->var_index); 
    }
    break; 
  }
  case TYPE_DOUBLE: {
    struct dfdd_child_type	*dfc;

    if (   VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].PROC_INDEX != PI_PEER
	) { 
      result = NORM_FALSE;
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        dfc = &(d->u.dfdd.arc[ci]);
        conj = rec_peer_eliminate(dfc->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        dfc = &(d->u.dfdd.arc[ci]);
        conj = rec_peer_eliminate(dfc->child);
        dfchild_stack_push(conj, dfc->lower_bound, 
          dfc->upper_bound
        );
      }
      result = dfdd_new(d->var_index); 
    }
    break; 
  }
  default: {
    struct ddd_child_type	*ic;

    if (   VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].PROC_INDEX != PI_PEER
	) { 
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_peer_eliminate(ic->child);
        result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_peer_eliminate(ic->child);
        ichild_stack_push(conj, ic->lower_bound, 
          ic->upper_bound
        );
      }
      result = ddd_new(d->var_index); 
    }
    break; 
  } }
  return(ce->result = result);
}
/* rec_peer_eliminate() */




/* We have not taken care of inequalities like x = y */
struct red_type	*red_peer_eliminate(d, pi)
     struct red_type	*d; 
     int		pi; 
{
  struct red_type	*result;

  PI_PEER = pi; 
  
  result = rec_peer_eliminate(d);

  return(result);
}
/* red_peer_eliminate() */






struct red_type	*rec_all_trigger(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, cv;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_ALL_TRIGGER, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: {
    struct ddd_child_type	*ic;
    int				pi;

    pi = VAR[d->var_index].PROC_INDEX;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);  
      conj = NORM_FALSE; 
      for (cv = ic->lower_bound; cv <= ic->upper_bound; cv++) 
        if (valid_mode_index(XTION[cv].src_mode_index)
            && (   cv > 0 
                || (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
                )
            ) 
          conj = red_bop(OR, conj, MODE[XTION[cv].src_mode_index].invariance[pi].red); 
        else 
          conj = NORM_NO_RESTRICTION; 
      conj = red_bop(AND, conj, rec_all_trigger(ic->child)); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  }
  case TYPE_CRD: {
    struct crd_child_type	*bc;

    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      conj = rec_all_trigger(bc->child);
      conj = crd_lone_subtree(conj, d->var_index, bc->upper_bound);

      result = red_bop(OR, result, conj);
    }
    break; 
  }
  case TYPE_HRD: {
    struct hrd_child_type	*hc;

    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      conj = rec_all_trigger(hc->child);
      conj = hrd_lone_subtree(conj, d->var_index, d->u.hrd.hrd_exp,
				 hc->ub_numerator, hc->ub_denominator
				 );

      result = red_bop(OR, result, conj);
    }
    break; 
  }
  case TYPE_FLOAT: {
    struct fdd_child_type	*fc;

    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fc = &(d->u.fdd.arc[ci]);
      conj = rec_all_trigger(fc->child);
      conj = fdd_lone_subtree(conj, d->var_index, 
        fc->lower_bound, fc->upper_bound
      );

      result = red_bop(OR, result, conj);
    }
    break; 
  }
  case TYPE_DOUBLE: {
    struct dfdd_child_type	*dfc;

    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfc = &(d->u.dfdd.arc[ci]);
      conj = rec_all_trigger(dfc->child);
      conj = dfdd_lone_subtree(conj, d->var_index, 
        dfc->lower_bound, dfc->upper_bound
      );

      result = red_bop(OR, result, conj);
    }
    break; 
  }
  default: {
    struct ddd_child_type	*ic;

    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = rec_all_trigger(ic->child);
      conj = ddd_lone_subtree(conj, d->var_index, ic->lower_bound, ic->upper_bound);

      result = red_bop(OR, result, conj);
    }
    break; 
  } }
  return(ce->result = result);
}
/* rec_all_trigger() */




/* We have not taken care of inequalities like x = y */
struct red_type	*red_all_trigger(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_all_trigger(d);

  return(result);
}
/* red_all_trigger() */



/* It is assumed that no clock's reading is TIMING_BOUND
 */
/*
int tia_count = 0; 
*/

struct a23tree_type	*tia_tree; 

int	rec_time_inactive(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct rec_type		*nrec, *rec;

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(TYPE_TRUE);
  else if (   VAR[d->var_index].TYPE == TYPE_CRD
	   || VAR[d->var_index].TYPE == TYPE_HRD
	   )
    return(TYPE_FALSE);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(rec, tia_tree, rec_comp, rec_free,
					rec_nop, rec_parent_set, rec_print
					); 
  if (rec != nrec) { 
    return((int) nrec->result); 
  }

  switch (VAR[d->var_index].TYPE) {
  case TYPE_LAZY_EXP: 
    if (d->u.lazy.exp->var_status & (FLAG_CLOCK | FLAG_DISCRETE)) 
      return((int) (rec->result = (struct red_type *) TYPE_FALSE)); 
    else 
      return((int) (rec->result = (struct red_type *) TYPE_TRUE));
    break; 

  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fc = &(d->u.fdd.arc[ci]);
/*
    fprintf(RED_OUT, "tia_count=%1d\n", ++tia_count); 
    fflush(RED_OUT); 
    for (; tia_count == 2; ) ; 
*/    
      if (!rec_time_inactive(fc->child))
        return((int) (rec->result
          = (struct red_type *) TYPE_FALSE
        ) );
    }
    break; 

  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfc = &(d->u.dfdd.arc[ci]);
/*
    fprintf(RED_OUT, "tia_count=%1d\n", ++tia_count); 
    fflush(RED_OUT); 
    for (; tia_count == 2; ) ; 
*/    
      if (!rec_time_inactive(dfc->child))
        return((int) (rec->result
          = (struct red_type *) TYPE_FALSE
        ) );
    }
    break; 

  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
/*
    fprintf(RED_OUT, "tia_count=%1d\n", ++tia_count); 
    fflush(RED_OUT); 
    for (; tia_count == 2; ) ; 
*/    
      if (!rec_time_inactive(ic->child))
        return((int) (rec->result
          = (struct red_type *) TYPE_FALSE
        ) );
    }
  }
  return((int) (rec->result = (struct red_type *) TYPE_TRUE));
}
/* rec_time_inactive() */



int	red_time_inactive(d)
     struct red_type	*d;
{
  int	result;

  init_23tree(&tia_tree);
  result = rec_time_inactive(d);
  free_entire_23tree(tia_tree, rec_free);

  return(result);
}
/* red_time_inactive() */







struct red_type	*rec_time_eliminate(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_TIME_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    result = NORM_FALSE;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
      result = red_bop(OR, result, rec_time_eliminate(d->u.crd.arc[ci].child));
    break; 
  case TYPE_HRD: 
    result = NORM_FALSE;
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
      result = red_bop(OR, result, rec_time_eliminate(d->u.hrd.arc[ci].child));
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_time_eliminate(d->u.lazy.false_child), 
      rec_time_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_TIME, FLAG_XVI_TIME_ELIMINATE
    ); 
    break; 

  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_time_eliminate(d->u.fdd.arc[ci].child),
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    } 
    result = fdd_new(d->var_index); 
    break; 

  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(
        rec_time_eliminate(d->u.dfdd.arc[ci].child),
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    } 
    result = dfdd_new(d->var_index); 
    break; 

  default: 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      ichild_stack_push(
        rec_time_eliminate(ic->child),
	ic->lower_bound, ic->upper_bound
      );
    } 
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result);
}
/* rec_time_eliminate() */



struct red_type	*red_time_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_time_eliminate(d);

  return(result);
}
/* red_time_eliminate() */





struct red_type	*rec_nonmodal_clock_eliminate(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct red_type		*result, *conj;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_NONMODAL_CLOCK_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    if (d->var_index == ZONE[0][MODAL_CLOCK] || d->var_index == ZONE[MODAL_CLOCK][0]) {
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      	conj = rec_nonmodal_clock_eliminate(d->u.crd.arc[ci].child);
        bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index); 
    }
    else {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
        result = red_bop(OR, result,
        		 rec_nonmodal_clock_eliminate(d->u.crd.arc[ci].child)
        		 );
    }
    break; 
  case TYPE_HRD: 
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1
	&& d->u.hrd.hrd_exp->hrd_term[0].var_index == CLOCK[MODAL_CLOCK]
	) {
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      	conj = rec_nonmodal_clock_eliminate(d->u.hrd.arc[ci].child);
        hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    else {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
        result = red_bop(OR, result,
        		 rec_nonmodal_clock_eliminate(d->u.hrd.arc[ci].child)
        		 );
    } 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fc = &(d->u.fdd.arc[ci]);
      fchild_stack_push(rec_nonmodal_clock_eliminate(fc->child),
			fc->lower_bound, fc->upper_bound
			);
    }
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfc = &(d->u.dfdd.arc[ci]);
      dfchild_stack_push(rec_nonmodal_clock_eliminate(dfc->child),
			dfc->lower_bound, dfc->upper_bound
			);
    }
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      ichild_stack_push(rec_nonmodal_clock_eliminate(ic->child),
			ic->lower_bound, ic->upper_bound
			);
    }
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result);
}
/* rec_nonmodal_clock_eliminate() */



struct red_type	*red_nonmodal_clock_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_nonmodal_clock_eliminate(d);

  return(result);
}
/* red_nonmodal_clock_eliminate() */





int	XCLOCK, XCLOCK_OFFSET; 

struct red_type	*rec_time_clock_eliminate(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct red_type		*result, *conj;
  struct cache2_hash_entry_type	*ce; 
  struct ps_exp_type		*lazy_exp; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_TIME_CLOCK_ELIMINATE, d, 
    (struct red_type *) XCLOCK
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (ce->result = bdd_new(d->var_index, 
	        rec_time_clock_eliminate(d->u.bdd.zero_child), 
	        rec_time_clock_eliminate(d->u.bdd.one_child)
	      )
	    ); 
    break; 
  case TYPE_CRD :
    if (XCLOCK == VAR[d->var_index].U.CRD.CLOCK2) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, 
			 rec_time_clock_eliminate(d->u.crd.arc[ci].child)
			 );
    }
    else if (XCLOCK == VAR[d->var_index].U.CRD.CLOCK1) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, 
			 rec_time_clock_eliminate(d->u.crd.arc[ci].child)
			 );
      if (   VAR[d->var_index].U.CRD.CLOCK2 != NEG_DELTA 
          && VAR[d->var_index].U.CRD.CLOCK2 != NEG_DELTAP
          ) 
        result = crd_one_constraint(result, 
          ZONE[0][VAR[d->var_index].U.CRD.CLOCK2], 0
        ); 
    }
    else {
      struct crd_child_type	*bc;

      result = NORM_FALSE; 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_time_clock_eliminate(bc->child); 
	if (   conj == NORM_NO_RESTRICTION 
	    || conj->var_index > d->var_index
	    ) 
	  bchild_stack_push(conj, bc->upper_bound);
	else {
	  conj = crd_one_constraint(conj, d->var_index, bc->upper_bound);
	  result = red_bop(OR, result, conj);
        }
      } 
      result = red_bop(OR, result, crd_new(d->var_index)); 
    }
    break;
  case TYPE_HRD :
    if (hrd_term_coeff_extract(d->u.hrd.hrd_exp, CLOCK[XCLOCK])) {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, rec_time_clock_eliminate(d->u.hrd.arc[ci].child));
    }
    else {
      struct hrd_child_type	*hc;

      result = NORM_FALSE; 
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) { 
	hc = &(d->u.hrd.arc[ci]); 
	conj = rec_time_clock_eliminate(hc->child); 
	if (   conj == NORM_NO_RESTRICTION
	    || conj->var_index > d->var_index
	    ) 
	  hchild_stack_push(conj, hc->ub_numerator, hc->ub_denominator); 
	else { 
	  conj = hrd_one_constraint(conj,
				   d->u.hrd.hrd_exp,
				   hc->ub_numerator, hc->ub_denominator
				   );
	  result = red_bop(OR, result, conj); 
	}
      }
      result = red_bop(OR, result, 
      		       hrd_new(d->var_index, d->u.hrd.hrd_exp)
      		       ); 
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project(
      rec_time_clock_eliminate(d->u.lazy.false_child), 
      rec_time_clock_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT, CLOCK[XCLOCK] 
    ); 
    break; 
  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fc = &(d->u.fdd.arc[ci]);
      conj = rec_time_clock_eliminate(fc->child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        fchild_stack_push(conj, fc->lower_bound, fc->upper_bound); 
      else { 
        conj = fdd_one_constraint(conj, d->var_index, 
				  fc->lower_bound, fc->upper_bound
				  );
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, fdd_new(d->var_index)); 
    break; 
  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfc = &(d->u.dfdd.arc[ci]);
      conj = rec_time_clock_eliminate(dfc->child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        dfchild_stack_push(conj, dfc->lower_bound, dfc->upper_bound); 
      else { 
        conj = fdd_one_constraint(conj, d->var_index, 
				  dfc->lower_bound, dfc->upper_bound
				  );
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, dfdd_new(d->var_index)); 
    break; 
  default: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = rec_time_clock_eliminate(ic->child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        ichild_stack_push(conj, ic->lower_bound, ic->upper_bound); 
      else { 
        conj = ddd_one_constraint(conj, d->var_index, 
				  ic->lower_bound, ic->upper_bound
				  );
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, ddd_new(d->var_index)); 
  }
  return(ce->result = result);
}
/* rec_time_clock_eliminate() */



struct red_type	*red_time_clock_eliminate(d, ci)
     struct red_type	*d; 
     int		ci; 
{
  struct red_type	*result;
  int			w; 

  XCLOCK = ci;
  RT[w = RT_TOP++] = d; 
  d = red_bypass_DOWNWARD(w, ci); 
  RT_TOP--; // w 
  result = rec_time_clock_eliminate(d);

  return(result);
}
/* red_time_clock_eliminate() */





struct red_type	*rec_time_clock_sim_eliminate(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct fdd_child_type		*fc;
  struct dfdd_child_type	*dfc;
  struct red_type		*result, *conj;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_TIME_CLOCK_SIM_ELIMINATE, d, 
    (struct red_type *) XCLOCK_OFFSET
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (ce->result = bdd_new(d->var_index, 
	        rec_time_clock_sim_eliminate(d->u.bdd.zero_child), 
	        rec_time_clock_sim_eliminate(d->u.bdd.one_child)
	      )
	    ); 
    break; 
  case TYPE_CRD :
    if (   VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX 
        && XCLOCK_OFFSET == VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].OFFSET
        ) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, 
			 rec_time_clock_sim_eliminate(d->u.crd.arc[ci].child)
			 );
    }
    else if (   VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX 
             && XCLOCK_OFFSET == VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].OFFSET
             ) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, 
	  rec_time_clock_sim_eliminate(d->u.crd.arc[ci].child)
	);
      if (   VAR[d->var_index].U.CRD.CLOCK2 != NEG_DELTA 
          && VAR[d->var_index].U.CRD.CLOCK2 != NEG_DELTAP
          ) 
        result = crd_one_constraint(result, 
          ZONE[0][VAR[d->var_index].U.CRD.CLOCK2], 0
        ); 
    }
    else {
      struct crd_child_type	*bc;

      result = NORM_FALSE; 
      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_time_clock_sim_eliminate(bc->child); 
	if (   conj == NORM_NO_RESTRICTION 
	    || conj->var_index > d->var_index
	    ) 
	  bchild_stack_push(conj, bc->upper_bound);
	else {
	  conj = crd_one_constraint(conj, d->var_index, bc->upper_bound);
	  result = red_bop(OR, result, conj);
        }
      } 
      result = red_bop(OR, result, crd_new(d->var_index)); 
    }
    break;
  case TYPE_HRD :
    for (ci = 0; ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++)
      if (   VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].TYPE == TYPE_CLOCK
          && VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX
          && VAR[d->u.hrd.hrd_exp->hrd_term[ci].var_index].OFFSET == XVAR_OFFSET
          )
        break;
    if (ci < (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)) {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, rec_time_clock_sim_eliminate(d->u.hrd.arc[ci].child));
    }
    else {
      struct hrd_child_type	*hc;

      result = NORM_FALSE; 
      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) { 
	hc = &(d->u.hrd.arc[ci]); 
	conj = rec_time_clock_sim_eliminate(hc->child); 
	if (   conj == NORM_NO_RESTRICTION
	    || conj->var_index > d->var_index
	    ) 
	  hchild_stack_push(conj, hc->ub_numerator, hc->ub_denominator); 
	else { 
	  conj = hrd_one_constraint(conj,
				   d->u.hrd.hrd_exp,
				   hc->ub_numerator, hc->ub_denominator
				   );
	  result = red_bop(OR, result, conj); 
	}
      }
      result = red_bop(OR, result, 
      		       hrd_new(d->var_index, d->u.hrd.hrd_exp)
      		       ); 
    }
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_time_clock_sim_eliminate(d->u.lazy.false_child), 
      rec_time_clock_sim_eliminate(d->u.lazy.true_child), 
      d, 
      PROJECT_CLOCK_SIM, XCLOCK_OFFSET 
    ); 
    break; 
  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_time_clock_sim_eliminate(d->u.fdd.arc[ci].child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound, 
          d->u.fdd.arc[ci].upper_bound
        ); 
      else { 
        conj = fdd_one_constraint(conj, d->var_index, 
	  d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, fdd_new(d->var_index)); 
    break; 
  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_time_clock_sim_eliminate(d->u.dfdd.arc[ci].child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound, 
          d->u.dfdd.arc[ci].upper_bound
        ); 
      else { 
        conj = dfdd_one_constraint(conj, d->var_index, 
	  d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, dfdd_new(d->var_index)); 
    break; 
  default: 
    result = NORM_FALSE; 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = rec_time_clock_sim_eliminate(ic->child);
      if (   conj == NORM_NO_RESTRICTION
          || conj->var_index > d->var_index 
          ) 
        ichild_stack_push(conj, ic->lower_bound, ic->upper_bound); 
      else { 
        conj = ddd_one_constraint(conj, d->var_index, 
				  ic->lower_bound, ic->upper_bound
				  );
        result = red_bop(OR, result, conj); 
      }
    }
    result = red_bop(OR, result, ddd_new(d->var_index)); 
  }
  return(ce->result = result);
}
/* rec_time_clock_sim_eliminate() */



struct red_type	*red_time_clock_sim_eliminate( 
     struct red_type	*d, 
     int		ci 
) {
  struct red_type	*result;

  if (VAR[CLOCK[ci]].PROC_INDEX) { 
    XCLOCK_OFFSET = VAR[CLOCK[ci]].OFFSET; 
    result = rec_time_clock_sim_eliminate(d); 
  }
  else {
    XCLOCK = ci;
    result = rec_time_clock_eliminate(d); 
  }
  return(result);
}
/* red_time_clock_sim_eliminate() */






struct a23tree_type	*abstract_lazy_tree; 

struct red_type	*rec_abstract_lazy(d)
     struct red_type	*d;
{
  int			ci;
  struct rec_type	*nrec, *rec;
  struct red_type	*result; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d); 

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, abstract_lazy_tree, 
    rec_comp, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  }

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_abstract_lazy(d->u.bdd.zero_child), 
      rec_abstract_lazy(d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD :
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bchild_stack_push(
        rec_abstract_lazy(d->u.crd.arc[ci].child), 
        d->u.crd.arc[ci].upper_bound
      );
    } 
    result = crd_new(d->var_index); 
    break;
  case TYPE_HRD :
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) { 
      hchild_stack_push(
        rec_abstract_lazy(d->u.hrd.arc[ci].child), 
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
      ); 
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_LAZY_EXP: 
    result = red_bop(OR, 
      rec_abstract_lazy(d->u.lazy.false_child), 
      rec_abstract_lazy(d->u.lazy.true_child)
    ); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_abstract_lazy(d->u.fdd.arc[ci].child), 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
    }
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(
        rec_abstract_lazy(d->u.dfdd.arc[ci].child), 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
    }
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ichild_stack_push(
        rec_abstract_lazy(d->u.ddd.arc[ci].child), 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
    }
    result = ddd_new(d->var_index); 
  } 
  return(rec->result = result);
}
  /* rec_abstract_lazy() */  




struct red_type	*red_abstract_lazy(
  struct red_type	*d 
) {
  init_23tree(&abstract_lazy_tree); 
  d = rec_abstract_lazy(d); 
  free_entire_23tree(abstract_lazy_tree, rec_free);
  
  return(d); 
}
  /* red_abstract_lazy() */ 





struct red_type	*rec_measure_time_clock(d, expected_vi)
     struct red_type	*d;
{
  int			ci;
  struct rec_type	*nrec, *rec;

  if (d->var_index == TYPE_TRUE || d->var_index > ZONE[XCLOCK][0]) { 
    if (expected_vi == ZONE[0][XCLOCK]) { 
      XOFFSET_LB = 0; 
      if (XCLOCK == TIME) 
        XOFFSET_UB = HYBRID_POS_INFINITY; 
      else 
        XOFFSET_UB = CLOCK_POS_INFINITY; 
    } 
    else { 
      if (XCLOCK == TIME) 
        XOFFSET_UB = HYBRID_POS_INFINITY; 
      else 
        XOFFSET_UB = CLOCK_POS_INFINITY; 
    } 
    return; 
  }

  rec = rec_new(d, (struct red_type *) expected_vi); 
  nrec = (struct rec_type *) 
    add_23tree(rec, tia_tree, rec_comp, rec_free,
	       rec_nop, rec_parent_set, rec_print
	       ); 
  if (rec != nrec) { 
    return; 
  }

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD : 
    if (   0 == VAR[d->var_index].U.CRD.CLOCK1 
        && XCLOCK == VAR[d->var_index].U.CRD.CLOCK2
        ) {
      ci = d->u.crd.child_count-1; 
      if (XOFFSET_LB + d->u.crd.arc[ci].upper_bound > 0) 
        XOFFSET_LB = -1 * d->u.crd.arc[ci].upper_bound; 
      for (; ci >= 0; ci--)
	rec_measure_time_clock(d->u.crd.arc[ci].child, ZONE[XCLOCK][0]);
    } 
    else if (   XCLOCK == VAR[d->var_index].U.CRD.CLOCK1
             && 0 == VAR[d->var_index].U.CRD.CLOCK2
             ) { 
      ci = d->u.crd.child_count-1; 
      if (XOFFSET_UB < d->u.crd.arc[ci].upper_bound) 
        XOFFSET_UB = d->u.crd.arc[ci].upper_bound; 
    }
    else {  
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	rec_measure_time_clock(d->u.crd.arc[ci].child, expected_vi); 
      } 
    }
    break;
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      rec_measure_time_clock(d->u.fdd.arc[ci].child, expected_vi);
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      rec_measure_time_clock(d->u.dfdd.arc[ci].child, expected_vi);
    } 
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      rec_measure_time_clock(d->u.ddd.arc[ci].child, expected_vi);
    } 
  }
  return;
}
/* rec_measure_time_clock() */



void	red_measure_time_clock(d, ci, lb_ptr, ub_ptr) 
  struct red_type	*d; 
  int			ci, *lb_ptr, *ub_ptr; 
{ 
  if (d == NORM_FALSE) { 
    fprintf(RED_OUT, "\n>> Time measurement in an empty space.\n"); 
    fprintf(RED_OUT, ">> Zero time bounds assumed.\n"); 
    fflush(RED_OUT); 
    *lb_ptr = *ub_ptr = 0; 
    return; 
//    bk(0); 	
  } 
  else if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
           == FLAG_SYSTEM_UNTIMED
           ) { 
    *lb_ptr = 0; 
    *ub_ptr = CLOCK_POS_INFINITY; 
    return;         	
  }
  XCLOCK = ci; 
  if (ci == TIME) 
    XOFFSET_LB = HYBRID_POS_INFINITY; 
  else 
    XOFFSET_LB = CLOCK_POS_INFINITY; 
  XOFFSET_UB = 0; 
  
  init_23tree(&tia_tree);
  rec_measure_time_clock(d, ZONE[0][ci]);
  free_entire_23tree(tia_tree, rec_free); 
  
  *lb_ptr = XOFFSET_LB; 
  *ub_ptr = XOFFSET_UB; 
}
  /* red_measure_time_clock() */ 
  
  



 
struct red_type	*rec_diagonal_eliminate(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_DIAGONAL_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD :
    if (VAR[d->var_index].U.CRD.CLOCK1 && VAR[d->var_index].U.CRD.CLOCK2) {
      result = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, rec_diagonal_eliminate(d->u.crd.arc[ci].child));
    }
    else {
      struct crd_child_type	*bc;

      child_stack_level_push(); 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	bchild_stack_push(rec_diagonal_eliminate(bc->child),
			  bc->upper_bound
			  );
      } 
      result = crd_new(d->var_index); 
    }
    break;
  case TYPE_HRD :
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1) {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--)
	result = red_bop(OR, result, rec_diagonal_eliminate(d->u.hrd.arc[ci].child));
    }
    else {
      struct hrd_child_type	*hc;

      child_stack_level_push(); 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	hc = &(d->u.hrd.arc[ci]);
	hchild_stack_push(rec_diagonal_eliminate(hc->child),
			  hc->ub_numerator, hc->ub_denominator
			  );
      } 
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break;
  case TYPE_FLOAT:
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(rec_diagonal_eliminate(d->u.fdd.arc[ci].child),
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index); 
    break;
  case TYPE_DOUBLE:
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_diagonal_eliminate(d->u.dfdd.arc[ci].child),
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index); 
    break;
  default:
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      ichild_stack_push(rec_diagonal_eliminate(ic->child),
			ic->lower_bound, ic->upper_bound
			);
    }
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result);
}
/* rec_diagonal_eliminate() */



struct red_type	*red_diagonal_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_diagonal_eliminate(d);

  return(result);
}
/* red_diagonal_eliminate() */




int	ZCI_REPLACER, ZCI_REPLACED, ZCI_RDISP;


struct red_type	*rec_time_clock_eliminate_replace(d)
     struct red_type	*d;
{
  int				ci, c1, c2, b;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct hrd_child_type		*hc;
  int				new_vi;
  struct hrd_exp_type		*newhe;
  struct cache4_hash_entry_type	*ce; 


  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_TIME_CLOCK_ELIMINATE_REPLACE, d, 
    (struct hrd_exp_type *) ZCI_REPLACED, 
    ZCI_REPLACER,
    ZCI_RDISP
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD :
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == ZCI_REPLACED) {
      struct crd_child_type	*bc; 

      if (c2 == ZCI_REPLACER) {
        for (ci = d->u.crd.child_count-1; ci>= 0; ci--) {
	  bc = &(d->u.crd.arc[ci]);
	  if (zone_ub_add(-1*ZCI_RDISP, bc->upper_bound) < 0)
	    break;
	  conj = rec_time_clock_eliminate_replace(bc->child);
	  result = red_bop(OR, result, conj);
        }
      }
      else {
        for (ci = d->u.crd.child_count-1; ci>= 0; ci--) {
	  bc = &(d->u.crd.arc[ci]); 
	  b = zone_ub_add(-1*ZCI_RDISP, bc->upper_bound); 
	  conj = rec_time_clock_eliminate_replace(bc->child); 
	  conj = crd_one_constraint(conj, ZONE[ZCI_REPLACER][c2], b); 
	  result = red_bop(OR, result, conj);
        }
      }
    }
    else if (c2 == ZCI_REPLACED) {
      struct crd_child_type	*bc;

      if (c1 == ZCI_REPLACER) {
        for (ci = d->u.crd.child_count-1; ci>= 0; ci--) {
	  bc = &(d->u.crd.arc[ci]);
	  if (zone_ub_add(ZCI_RDISP, bc->upper_bound) < 0)
	    break;
	  conj = rec_time_clock_eliminate_replace(bc->child);
	  result = red_bop(OR, result, conj);
	}
      }
      else {
        for (ci = d->u.crd.child_count-1; ci>= 0; ci--) {
	  bc = &(d->u.crd.arc[ci]);
	  b = zone_ub_add(ZCI_RDISP, bc->upper_bound);
	  conj = rec_time_clock_eliminate_replace(bc->child);
	  conj = crd_one_constraint(conj, ZONE[c1][ZCI_REPLACER], b);
	  result = red_bop(OR, result, conj);
	}
      }
    }
    else {
      struct crd_child_type	*bc;

      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	conj = rec_time_clock_eliminate_replace(bc->child);
	conj = crd_one_constraint(conj, d->var_index, bc->upper_bound);
	result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_HRD :
    fprintf(RED_OUT, "\nWarning: hybrid inequality is not allowed in this mode.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_time_clock_eliminate_replace(d->u.fdd.arc[ci].child);
      conj = fdd_one_constraint(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_time_clock_eliminate_replace(d->u.dfdd.arc[ci].child);
      conj = dfdd_one_constraint(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = rec_time_clock_eliminate_replace(ic->child);
      conj = ddd_one_constraint(conj, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result);
}
/* rec_time_clock_eliminate_replace() */



struct red_type	*red_time_clock_eliminate_replace(d, crd, crr, disp)
     struct red_type	*d;
     int		crd, crr, disp;
{
  struct red_type	*result;

  ZCI_REPLACED = crd;
  ZCI_REPLACER = crr;
  ZCI_RDISP = disp;

  result = rec_time_clock_eliminate_replace(d);

  return(result);
}
/* red_time_clock_eliminate_replace() */






int	XCLOCK;


struct red_type	*rec_time_clock_inc(d)
     struct red_type	*d;
{
  int				ci, b, coeff;
  int				offset, numerator, denominator;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_TIME_CLOCK_INC, d, 
    NULL, XCLOCK, XOFFSET_LB * CLOCK_POS_INFINITY + XOFFSET_UB 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD :
    child_stack_level_push(); 
    if (XCLOCK == VAR[d->var_index].U.CRD.CLOCK1) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	b = d->u.crd.arc[ci].upper_bound;
	b = zone_ub_add(b, XOFFSET_UB);
	bchild_stack_push(
	  rec_time_clock_eliminate(d->u.crd.arc[ci].child),
	  b 
	);
      }
    }
    else if (XCLOCK == VAR[d->var_index].U.CRD.CLOCK2) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	b = d->u.crd.arc[ci].upper_bound;
	b = zone_ub_add(b, -1*XOFFSET_LB);
	bchild_stack_push(
	  rec_time_clock_eliminate(d->u.crd.arc[ci].child), b
	);
      }
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bchild_stack_push(
	  rec_time_clock_eliminate(d->u.crd.arc[ci].child),
	  d->u.crd.arc[ci].upper_bound
	);
      }
    }
    result = crd_new(d->var_index); 
    break;
  case TYPE_HRD:
    child_stack_level_push(); 
    coeff = hrd_term_coeff_extract(d->u.hrd.hrd_exp, CLOCK[XCLOCK]);
    if (coeff >= 0) { 
      offset = XOFFSET_UB*coeff;
    }
    else 
      offset = -1*XOFFSET_LB*coeff;
    if (offset) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hybrid_ub_add(d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator,
		      offset, 1, &numerator, &denominator
		      );
        hchild_stack_push(rec_time_clock_eliminate(d->u.hrd.arc[ci].child),
			  numerator, denominator 
			  );
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hchild_stack_push(rec_time_clock_eliminate(d->u.hrd.arc[ci].child),
			  d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator 
			  );
      }
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break;
  case TYPE_FLOAT:
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(rec_time_clock_eliminate(d->u.fdd.arc[ci].child),
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index); 
    break;
  case TYPE_DOUBLE:
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_time_clock_eliminate(d->u.dfdd.arc[ci].child),
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index); 
    break;
  default:
    child_stack_level_push(); 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      ichild_stack_push(rec_time_clock_eliminate(ic->child),
			ic->lower_bound, ic->upper_bound
			);
    }
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result);
}
/* rec_time_clock_inc() */



struct red_type	*red_time_clock_inc(d, ci, offset_lb, offset_ub)
     struct red_type	*d;
{
  struct red_type	*result;

  XCLOCK = ci;
  XOFFSET_LB = offset_lb;
  XOFFSET_UB = offset_ub;

  result = rec_time_clock_inc(d);
  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED
      && offset_lb > 0
      )
    result = red_bop(AND, result, crd_atom(ZONE[0][ci], offset_lb)); 

  return(result); 
}
/* red_time_clock_inc() */ 






int	DETECT_TARGET_VI; 

int	rec_detect(d)
     struct red_type	*d; 
{
  int				ci; 
  struct ddd_child_type		*ic; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(TYPE_FALSE);
  else if (d->var_index == TYPE_FALSE) 
    return(TYPE_FALSE); 

  ce = cache2_check_result_key(
    OP_DETECT, d, 
    (struct red_type *) DETECT_TARGET_VI
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  if (d->var_index == DETECT_TARGET_VI) {
    fprintf(RED_OUT, "\nDetected d=%x with index %1d\n", (unsigned int) d, d->var_index); 
    return((int) (ce->result
      = (struct red_type *) TYPE_TRUE
    ) ); 
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      if (rec_detect(d->u.crd.arc[ci].child))
        return((int) (ce->result
          = (struct red_type *) TYPE_TRUE
        ) ); 
    }
    break; 
  case TYPE_HRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      if (rec_detect(d->u.hrd.arc[ci].child))
        return((int) (ce->result
          = (struct red_type *) TYPE_TRUE
        ) ); 
    }
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      if (rec_detect(d->u.fdd.arc[ci].child))
        return((int) (ce->result
          = (struct red_type *) TYPE_TRUE
        ) ); 
    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      if (rec_detect(d->u.dfdd.arc[ci].child))
        return((int) (ce->result
          = (struct red_type *) TYPE_TRUE
        ) ); 
    }
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      if (rec_detect(d->u.ddd.arc[ci].child))
        return((int) (ce->result
          = (struct red_type *) TYPE_TRUE
        ) ); 
    }
    break; 
  }
  return((int) (ce->result
           = (struct red_type *) TYPE_FALSE
         ) );
}
/* rec_detect() */


red_detect(d, vi)
  struct red_type	*d;
  int	vi;
{
  int	result;

  DETECT_TARGET_VI = vi;

  result = rec_detect(d);

  if (result) {
    fprintf(RED_OUT, "\nDetected vi=%1d at red %x:\n", vi, (unsigned int) d);
    red_print_graph(d);
    exit(0);
  }
}
/* red_detect() */









/***************************************************************************
 */

/* It is that along any path from top to bottom, there is
 *   a node with var_index = vi.
 * The procedure red_inc() won't work if there is a path in which no
 * node is with var_index = vi.
 */

struct red_type	*rec_inc(d)
     struct red_type	*d;
{
  int				lb, ub, ci;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (   d->var_index == TYPE_FALSE
      || d->var_index == TYPE_TRUE
      || d->var_index > XVI_INC
      ) 
    return(d); 

  ce = cache4_check_result_key(OP_INC, d, NULL, XVI_INC, 
    XOFFSET_LB * (VAR[XVI_INC].U.DISC.UB-VAR[XVI_INC].U.DISC.LB+1) + XOFFSET_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  if (d == NORM_NO_RESTRICTION || d->var_index > XVI_INC) {
    lb = VAR[XVI_INC].U.DISC.LB + XOFFSET_LB;
    ub = VAR[XVI_INC].U.DISC.UB + XOFFSET_UB;
    if (lb < VAR[XVI_INC].U.DISC.LB)
      lb = VAR[XVI_INC].U.DISC.LB;
    if (ub > VAR[XVI_INC].U.DISC.UB)
      ub = VAR[XVI_INC].U.DISC.UB;
    return(ce->result = ddd_lone_subtree(d, XVI_INC, lb, ub));
  }
  else switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_inc(d->u.bdd.zero_child), 
      rec_inc(d->u.bdd.one_child)
    ); 
    break; 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      bchild_stack_push(rec_inc(bc->child), bc->upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      hchild_stack_push(rec_inc(hc->child), 
			hc->ub_numerator, hc->ub_denominator 
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_inc(d->u.fdd.arc[ci].child), 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(
        rec_inc(d->u.dfdd.arc[ci].child), 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    child_stack_level_push(); 
    if (d->var_index == XVI_INC) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        lb = ic->lower_bound + XOFFSET_LB;
        ub = ic->upper_bound + XOFFSET_UB;

        if (lb < VAR[d->var_index].U.DISC.LB)
	  lb = VAR[d->var_index].U.DISC.LB;
        if (ub > VAR[d->var_index].U.DISC.UB)
	  ub = VAR[d->var_index].U.DISC.UB;

        if (lb <= ub)
	  ichild_stack_push(ic->child, lb, ub);
      }
    }
    else for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      ichild_stack_push(
        rec_inc(ic->child), ic->lower_bound, ic->upper_bound
      );
    }
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result);
}
/* rec_inc() */


struct red_type	*rec_inc_wide(d)
     struct red_type	*d;
{
  int				lb, ub, ci;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (   d->var_index == TYPE_FALSE
      || d->var_index == TYPE_TRUE
      || d->var_index > XVI_INC
      ) 
    return(d); 

  ce = cache4_check_result_key(OP_INC, d, NULL, XVI_INC, 
    XOFFSET_LB * (VAR[XVI_INC].U.DISC.UB-VAR[XVI_INC].U.DISC.LB+1) + XOFFSET_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      bchild_stack_push(rec_inc_wide(bc->child), bc->upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      hchild_stack_push(rec_inc_wide(hc->child), 
			hc->ub_numerator, hc->ub_denominator 
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_inc(d->u.fdd.arc[ci].child), 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(
        rec_inc(d->u.dfdd.arc[ci].child), 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    if (d->var_index == XVI_INC) {
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        lb = ic->lower_bound + XOFFSET_LB;
	ub = ic->upper_bound + XOFFSET_UB;

        if (lb < VAR[d->var_index].U.DISC.LB)
	  lb = VAR[d->var_index].U.DISC.LB;
        if (ub > VAR[d->var_index].U.DISC.UB)
	  ub = VAR[d->var_index].U.DISC.UB;

        if (lb <= ub)
	  result = red_bop(OR, result, 
	    ddd_one_constraint(ic->child, XVI_INC, lb, ub)
	  );
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        ichild_stack_push(
          rec_inc(ic->child), ic->lower_bound, ic->upper_bound
        );
      }
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_inc_wide() */


struct red_type	*red_inc(d, vi, offset_lb, offset_ub)
     struct red_type	*d;
     int		vi, offset_lb, offset_ub;
{
  struct red_type	*result;

  if (offset_lb > offset_ub) 
    return(NORM_FALSE); 

  XVI_INC = vi; 
  XOFFSET_LB = offset_lb;
  XOFFSET_UB = offset_ub; 
  if (ddd_one_constraint(d, vi, VAR[vi].U.DISC.UB - offset_ub+1, VAR[vi].U.DISC.UB)
    != NORM_FALSE
  ) {
    fprintf(RED_OUT, "\nWarning: Overflow on upper-bound increment by %1d on variable %s \n",
	    offset_ub, VAR[vi].NAME
	    );
    fprintf(RED_OUT, "\twith bound = %1d:%1d.\n", VAR[vi].U.DISC.LB, VAR[vi].U.DISC.UB);
    fflush(RED_OUT); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ddd_one_constraint(d, vi, VAR[vi].U.DISC.LB, VAR[vi].U.DISC.LB-offset_lb-1) 
    != NORM_FALSE
  ) {
    fprintf(RED_OUT, "\nWarning: Overflow on lower-bound increment by %1d on variable %s \n",
	    offset_lb, VAR[vi].NAME
	    ); 
    fprintf(RED_OUT, "\twith bounds = %1d.\n", VAR[vi].U.DISC.LB, VAR[vi].U.DISC.UB);
    fflush(RED_OUT); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(103); 
  }
  else 
    d = ddd_one_constraint(
      d, vi, VAR[vi].U.DISC.LB-offset_lb, VAR[vi].U.DISC.UB-offset_ub
    );

  if (offset_lb == offset_ub) 
    result = rec_inc(d); 
  else 
    result = rec_inc_wide(d); 

  return(result); 
}
/* red_inc() */ 





struct red_type	*red_inc_off(d, vi, offset_lb, offset_ub)
     struct red_type	*d; 
     int		vi, offset_lb, offset_ub; 
{
  struct red_type	*result; 

  if (offset_lb > offset_ub) 
    return(NORM_FALSE); 

  XVI_INC = vi; 
  XOFFSET_LB = offset_lb; 
  XOFFSET_UB = offset_ub; 
  
  if (offset_lb == offset_ub) 
    result = rec_inc(d); 
  else 
    result = rec_inc_wide(d); 

  return(result); 
}
/* red_inc_off() */ 






int	add_mod(vi, a, b)
     int	vi, a, b; 
{
  a = a+b; 

  return((a % (VAR[vi].U.DISC.UB+1)) + VAR[vi].U.DISC.LB); 
}
/* add_mod() */





struct red_type	*rec_inc_mod(d)
     struct red_type	*d;
{
  int				lb, ub, ci;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (   d->var_index == TYPE_FALSE
      || d->var_index == TYPE_TRUE
      || d->var_index > XVI_INC
      ) 
    return(d); 

  ce = cache4_check_result_key(OP_INC_MOD, d, NULL, XVI_INC, 
    XOFFSET_LB * (VAR[XVI_INC].U.DISC.UB-VAR[XVI_INC].U.DISC.LB+1) + XOFFSET_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      bchild_stack_push(rec_inc_mod(bc->child), 
        bc->upper_bound
      );
    } 
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      hchild_stack_push(rec_inc_mod(hc->child), 
			hc->ub_numerator, hc->ub_denominator
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(rec_inc_mod(d->u.fdd.arc[ci].child),
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound 
      );
    } 
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_inc_mod(d->u.dfdd.arc[ci].child),
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound 
      );
    } 
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    child_stack_level_push(); 
    if (d->var_index == XVI_INC) { 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);

        lb = add_mod(d->var_index, ic->lower_bound, XOFFSET_LB);
        ub = add_mod(d->var_index, ic->upper_bound, XOFFSET_UB);

        if (lb <= ub)
	  ichild_stack_push(ic->child, lb, ub);
        else { 
	  result = red_bop(OR, result, 
	  		   ddd_lone_subtree(ic->child, 
	  		     VAR[d->var_index].U.DISC.LB, ub
	  		   )); 
	  ichild_stack_push(ic->child, lb, VAR[d->var_index].U.DISC.UB);
        }
      } 
      result = red_bop(OR, result, ddd_new(d->var_index)); 
    }
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        ichild_stack_push(rec_inc_mod(ic->child),
			  ic->lower_bound, ic->upper_bound 
			  );
      } 
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_inc_mod() */





struct red_type	*rec_inc_mod_wide(d)
     struct red_type	*d;
{
  int				lb, ub, ci;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (   d->var_index == TYPE_FALSE
      || d->var_index == TYPE_TRUE
      || d->var_index > XVI_INC
      ) 
    return(d); 

  ce = cache4_check_result_key(OP_INC_MOD, d, NULL, XVI_INC, 
    XOFFSET_LB * (VAR[XVI_INC].U.DISC.UB-VAR[XVI_INC].U.DISC.LB+1) + XOFFSET_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    child_stack_level_push(); 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      bchild_stack_push(rec_inc_mod_wide(bc->child), 
        bc->upper_bound
      );
    } 
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push(); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      hchild_stack_push(rec_inc_mod_wide(hc->child), 
			hc->ub_numerator, hc->ub_denominator
			);
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    break; 
  case TYPE_FLOAT: 
    child_stack_level_push(); 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(rec_inc_mod_wide(d->u.fdd.arc[ci].child),
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound 
      );
    } 
    result = fdd_new(d->var_index); 
    break; 
  case TYPE_DOUBLE: 
    child_stack_level_push(); 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_inc_mod_wide(d->u.dfdd.arc[ci].child),
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound 
      );
    } 
    result = dfdd_new(d->var_index); 
    break; 
  default: 
    if (d->var_index == XVI_INC) { 
      result = NORM_FALSE; 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);

        lb = add_mod(d->var_index, ic->lower_bound, XOFFSET_LB);
        ub = add_mod(d->var_index, ic->upper_bound, XOFFSET_UB);

        if (lb <= ub)
	  result = red_bop(OR, 
	    result, 
	    ddd_one_constraint(ic->child, XVI_INC, lb, ub)
	  );
        else { 
	  result = red_bop(OR, result, ddd_lone_subtree(
	    ic->child, XVI_INC, lb, VAR[d->var_index].U.DISC.UB
	  ) );
	  result = red_bop(OR, result, ddd_lone_subtree(
	    ic->child, XVI_INC, VAR[d->var_index].U.DISC.LB, ub
	  ) ); 
        }
      } 
    }
    else {
      child_stack_level_push(); 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        ichild_stack_push(rec_inc_mod_wide(ic->child),
			  ic->lower_bound, ic->upper_bound 
			  );
      } 
      result = ddd_new(d->var_index); 
    }
  }
  return(ce->result = result);
}
/* rec_inc_mod_wide() */






struct red_type	*red_inc_mod(d, vi, offset_lb, offset_ub)
     struct red_type	*d;
     int		vi, offset_lb, offset_ub;
{
  struct red_type	*result; 

  if (offset_lb > offset_ub) 
    return(NORM_FALSE); 

  XVI_INC = vi; 
  XOFFSET_LB = offset_lb; 
  XOFFSET_UB = offset_ub; 
  
  if (offset_lb == offset_ub) 
    result = rec_inc_mod(d); 
  else 
    result = rec_inc_mod_wide(d); 

  return(result); 
}
/* red_inc_mod() */










/***************************************************************************
 */

/* It is that along any path from top to bottom, there is
 *   two nodes with var_index = vi, vj respectively.
 * The procedure red_inc() won't work if there is a path in which no
 * node is with var_index = vi.
 * It is also assumed taht vi < vj.
 */

int	XVI, XVJ;

struct red_type	*rec_switch_vi(d)
     struct red_type	*d;
{
  int				ci, nc1, nc2;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct hrd_exp_type		*rhrd_exp; 
  struct red_type		*result, *conj;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_SWITCH_VI, d, NULL, XVI, XVJ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (CLOCK[VAR[d->var_index].U.CRD.CLOCK1] == XVI) 
      nc1 = VAR[XVJ].U.CLOCK.CLOCK_INDEX; 
    else if (CLOCK[VAR[d->var_index].U.CRD.CLOCK1] == XVJ) 
      nc1 = VAR[XVI].U.CLOCK.CLOCK_INDEX; 
    else 
      nc1 = VAR[d->var_index].U.CRD.CLOCK1; 
    if (CLOCK[VAR[d->var_index].U.CRD.CLOCK2] == XVI) 
      nc2 = VAR[XVJ].U.CLOCK.CLOCK_INDEX; 
    else if (CLOCK[VAR[d->var_index].U.CRD.CLOCK2] == XVJ) 
      nc2 = VAR[XVI].U.CLOCK.CLOCK_INDEX; 
    else 
      nc2 = VAR[d->var_index].U.CRD.CLOCK2; 
      
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      conj = crd_one_constraint(rec_switch_vi(ic->child), 
        ZONE[nc1][nc2], bc->upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_HRD:
    rhrd_exp = hrd_exp_switch_vi(d->u.hrd.hrd_exp, XVI, XVJ); 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      conj = hrd_one_constraint(rec_switch_vi(hc->child), rhrd_exp,
	hc->ub_numerator, hc->ub_denominator
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    if (d->var_index == XVI) {
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result,
	  fdd_one_constraint(rec_switch_vi(d->u.fdd.arc[ci].child),
	    XVJ, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	) );
      }
    }
    else if (d->var_index == XVJ) {
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result,
	  fdd_one_constraint(d->u.fdd.arc[ci].child, XVI, 
	    d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
	) );
      }
    }
    else for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = fdd_one_constraint(rec_switch_vi(d->u.fdd.arc[ci].child),
	d->var_index, 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    if (d->var_index == XVI) {
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result,
	  dfdd_one_constraint(rec_switch_vi(d->u.dfdd.arc[ci].child),
	    XVJ, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	) );
      }
    }
    else if (d->var_index == XVJ) {
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result,
	  dfdd_one_constraint(d->u.dfdd.arc[ci].child, XVI, 
	    d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
	) );
      }
    }
    else for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = dfdd_one_constraint(rec_switch_vi(d->u.dfdd.arc[ci].child),
	d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (d->var_index == XVI) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        result = red_bop(OR, result,
		       ddd_one_constraint(rec_switch_vi(ic->child),
					       XVJ, ic->lower_bound, ic->upper_bound
					       )
		       );
      }
    }
    else if (d->var_index == XVJ) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        result = red_bop(OR, result,
		       ddd_one_constraint(ic->child, XVI, ic->lower_bound, ic->upper_bound)
		       );
      }
    }
    else for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      conj = ddd_one_constraint(rec_switch_vi(ic->child),
				     d->var_index, ic->lower_bound, ic->upper_bound
				     );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result);
}
/* rec_switch_vi() */ 





struct red_type	*red_switch_vi(d, vi, vj)
     struct red_type	*d; 
     int		vi, vj; 
{
  struct red_type	*result; 

  if (VAR[vi].TYPE != VAR[vj].TYPE) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal variable switch between incompatible types.\n"
    ); 
    fprintf(RED_OUT, "  %s and %s \n", VAR[vi].NAME, VAR[vj].NAME); 
    bk(0); 
  } 
  XVI = vi; 
  XVJ = vj; 
 
  result = rec_switch_vi(d);

  return(result); 
}
/* red_switch_vi() */ 




int	interval_intersect(lbx, ubx, lby, uby)
     int	lbx, ubx, lby, uby; 
{
  if (lbx > ubx)
    return(TYPE_FALSE);

  if (lby > uby) 
    return(TYPE_FALSE); 

  if (ubx < lby) 
    return(TYPE_FALSE);

  if (uby < lbx)
    return(TYPE_FALSE);

  return(TYPE_TRUE);
}
/* interval_intersect() */



int	XPI, XPJ;

struct red_type *rec_pi_permute(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *td, *fd, *subresult, *filter;
  int				vi, lb, ub, ci, cv1, cv2, c1, c2;
  struct hrd_exp_type		*he;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_PI_PERMUTE, d, NULL, XVI, XVJ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  if (VAR[d->var_index].TYPE == TYPE_CRD) {
    cv1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1];
    cv2 = CLOCK[VAR[d->var_index].U.CRD.CLOCK2];
    if (VAR[cv1].PROC_INDEX == XPI)
      c1 = VAR[
        variable_index[TYPE_CLOCK][XPJ][VAR[cv1].OFFSET]
      ].U.CLOCK.CLOCK_INDEX;
    else if (VAR[cv1].PROC_INDEX == XPJ)
      c1 = VAR[
        variable_index[TYPE_CLOCK][XPI][VAR[cv1].OFFSET]
      ].U.CLOCK.CLOCK_INDEX;
    else
      c1 = VAR[cv1].U.CLOCK.CLOCK_INDEX;

    if (VAR[cv2].PROC_INDEX == XPI)
      c2 = VAR[
        variable_index[TYPE_CLOCK][XPJ][VAR[cv2].OFFSET]
      ].U.CLOCK.CLOCK_INDEX;
    else if (VAR[cv2].PROC_INDEX == XPJ)
      c2 = VAR[
        variable_index[TYPE_CLOCK][XPI][VAR[cv2].OFFSET]
      ].U.CLOCK.CLOCK_INDEX;
    else
      c2 = VAR[cv2].U.CLOCK.CLOCK_INDEX;

    vi = ZONE[c1][c2];
  }
  else if (VAR[d->var_index].TYPE == TYPE_HRD) {
    he = hrd_exp_permute(d->u.hrd.hrd_exp, &vi, XPI, XPJ);
  }
  else if (VAR[d->var_index].PROC_INDEX ==  XPI) {
    vi = variable_index[VAR[d->var_index].TYPE][XPJ][VAR[d->var_index].OFFSET];
  }
  else if (VAR[d->var_index].PROC_INDEX ==  XPJ) {
    vi = variable_index[VAR[d->var_index].TYPE][XPI][VAR[d->var_index].OFFSET];
  }
  else
    vi = d->var_index;

  switch (VAR[vi].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      struct crd_child_type	*bc;

      bc = &(d->u.crd.arc[ci]);
      conj = rec_pi_permute(bc->child);
      conj = crd_one_constraint(conj, vi, bc->upper_bound);
      result = red_bop(OR, result, conj);
    }
    break; 
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      struct hrd_child_type	*hc;

      hc = &(d->u.hrd.arc[ci]);
      conj = rec_pi_permute(hc->child);
      conj = hrd_one_constraint(conj, he, hc->ub_numerator, hc->ub_denominator);
      result = red_bop(OR, result, conj);
    }
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      conj = rec_pi_permute(d->u.fdd.arc[ci].child);
      conj = fdd_one_constraint(conj, vi, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      conj = rec_pi_permute(d->u.dfdd.arc[ci].child);
      conj = dfdd_one_constraint(conj, vi, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
  default: 
    if (VAR[vi].TYPE == TYPE_POINTER) {
      struct ddd_child_type	*ic;

      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        subresult = rec_pi_permute(ic->child);
        if (interval_intersect(ic->lower_bound, ic->upper_bound, 0, XPI-1)) {
	  if (XPI-1 < ic->upper_bound)
	    ub = XPI-1;
	  else
	    ub = ic->upper_bound;
	  conj = ddd_one_constraint(subresult, vi, ic->lower_bound, ub);
	  result = red_bop(OR, result, conj);
        }

        if (interval_intersect(ic->lower_bound, ic->upper_bound, XPI, XPI)) {
	  conj = ddd_one_constraint(subresult, vi, XPJ, XPJ);
	  result = red_bop(OR, result, conj);
        }

        if (interval_intersect(ic->lower_bound, ic->upper_bound, XPI+1, XPJ-1)) {
	  if (XPI+1 > ic->lower_bound)
	    lb = XPI+1;
	  else
	    lb = ic->lower_bound;

	  if (XPJ-1 < ic->upper_bound)
	    ub = XPJ-1;
	  else
	    ub = ic->upper_bound;
	  conj = ddd_one_constraint(subresult, vi, lb, ub);
	  result = red_bop(OR, result, conj);
        }

        if (interval_intersect(ic->lower_bound, ic->upper_bound, XPJ, XPJ)) {
	  conj = ddd_one_constraint(subresult, vi, XPI, XPI);
	  result = red_bop(OR, result, conj);
        }

        if (   XPJ < VAR[vi].U.DISC.UB 
            && interval_intersect(
                 ic->lower_bound, ic->upper_bound, XPJ+1, VAR[vi].U.DISC.UB
            )  ) {
	  if (XPJ+1 > ic->lower_bound)
	    lb = XPJ+1;
	  else
	    lb = ic->lower_bound;

	  conj = ddd_one_constraint(subresult, vi, lb, ic->upper_bound);
	  result = red_bop(OR, result, conj);
        }
      }
    }
    else if (d->var_index == HF_PSTART_VI || d->var_index == HF_PSTOP_VI) {
      struct ddd_child_type	*ic;

      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        subresult = rec_pi_permute(ic->child);
        for (lb = ic->lower_bound; lb <= ic->upper_bound; lb++) {
	  if (VAR[CLOCK[lb]].PROC_INDEX == XPI)
	    ub = VAR[
	      variable_index[TYPE_CLOCK][XPJ][VAR[CLOCK[lb]].OFFSET]
	    ].U.CLOCK.CLOCK_INDEX;
	  else if (VAR[CLOCK[lb]].PROC_INDEX == XPJ)
	    ub = VAR[
	      variable_index[TYPE_CLOCK][XPI][VAR[CLOCK[lb]].OFFSET]
	    ].U.CLOCK.CLOCK_INDEX;
	  else
	    ub = lb;
	  conj = ddd_one_constraint(subresult, vi, ub, ub);
	  result = red_bop(OR, result, conj);
        }
      }
    }
    else {
      struct ddd_child_type	*ic;

      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        conj = rec_pi_permute(ic->child);
        conj = ddd_one_constraint(conj, vi, ic->lower_bound, ic->upper_bound);
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result);
}
/* rec_pi_permute() */




  /* It is assumed that pi < pj */
struct red_type	*red_pi_permute(d, pi, pj)
     struct red_type	*d;
     int		pi, pj;
{
  struct red_type	*result;

  if (pi < pj) {
    XPI = pi;
    XPJ = pj;
  }
  else {
    XPI = pj;
    XPJ = pi; 
  }
  result = rec_pi_permute(d);

  return(result);
}
/* red_pi_permute() */





int	count_order_check = 0; 

int	rec_order_check(d)
     struct red_type	*d;
{
  int				ci;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(TYPE_TRUE);

  ce = cache1_check_result_key(OP_ORDER_CHECK, d); 
  if (ce->result) {
    return((int) ce->result); 
  } 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      if (   (bc->child != NORM_NO_RESTRICTION && bc->child->var_index <= d->var_index)
	  || !rec_order_check(bc->child)
	  ) {
	fprintf(RED_OUT, "An out-of-order variable is found.\n");
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	bk(0);
      }
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      if (   (hc->child != NORM_NO_RESTRICTION && hc->child->var_index <= d->var_index)
	  || !rec_order_check(hc->child)
	  ) {
	fprintf(RED_OUT, "An out-of-order variable is found.\n");
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	bk(0);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      ++count_order_check; 
//      fprintf(RED_OUT, "count_order_check = %1d\n", ++count_order_check); 
      if (count_order_check == -1) 
        for (; count_order_check; ); 
      if (   (   d->u.fdd.arc[ci].child != NORM_NO_RESTRICTION 
              && d->u.fdd.arc[ci].child->var_index <= d->var_index
              )
	  || !rec_order_check(d->u.fdd.arc[ci].child)
	  ) {
	fprintf(RED_OUT, "An out-of-order variable is found for vi=%1d.\n", d->var_index); 
	red_print_graph(d->u.fdd.arc[ci].child); 
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
	bk(0); 
      }
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      ++count_order_check; 
//      fprintf(RED_OUT, "count_order_check = %1d\n", ++count_order_check); 
      if (count_order_check == -1) 
        for (; count_order_check; ); 
      if (   (   d->u.dfdd.arc[ci].child != NORM_NO_RESTRICTION 
              && d->u.dfdd.arc[ci].child->var_index <= d->var_index
              )
	  || !rec_order_check(d->u.dfdd.arc[ci].child)
	  ) {
	fprintf(RED_OUT, "An out-of-order variable is found for vi=%1d.\n", d->var_index); 
	red_print_graph(d->u.dfdd.arc[ci].child); 
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
	bk(0); 
      }
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      ++count_order_check; 
//      fprintf(RED_OUT, "count_order_check = %1d\n", ++count_order_check); 
      if (count_order_check == -1) 
        for (; count_order_check; ); 
      if (   (   ic->child != NORM_NO_RESTRICTION 
              && ic->child->var_index <= d->var_index
              )
	  || !rec_order_check(ic->child)
	  ) {
	fprintf(RED_OUT, "An out-of-order variable is found for vi=%1d.\n", d->var_index); 
	red_print_graph(ic->child); 
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
	bk(0); 
      }
    }
  }
  return((int) (ce->result
    = (struct red_type *) TYPE_TRUE
  ) );
}
/* rec_order_check() */




  /* It is assumed that pi < pj */ 
int	red_order_check(d) 
     struct red_type	*d; 
{
  int	result;

  result = rec_order_check(d); 

  return(result); 
}
/* red_order_check() */




struct red_type	*rec_CDD(d)
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

  ce = cache1_check_result_key(OP_CDD, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 <= c2) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        child = rec_CDD(bc->child);
        child = ddd_one_constraint(child, VAR[d->var_index].U.CRD.CORRESPONDING_CDD_VI,
        			 	CLOCK_NEG_INFINITY, bc->upper_bound
					);
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        child = rec_CDD(bc->child);
        child = ddd_one_constraint(child, VAR[ZONE[c2][c1]].U.CRD.CORRESPONDING_CDD_VI,
        			 	-1*bc->upper_bound, CLOCK_POS_INFINITY
					);
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_HRD:
    if (d->u.hrd.hrd_exp->hrd_term[0].coeff < 0) {
      for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        child = rec_CDD(hc->child);
        child = hdd_one_constraint(
        	child, VAR[d->var_index].U.HRD.CORRESPONDING_HDD_VI, d->u.hrd.hrd_exp,         				
        	 HYBRID_NEG_INFINITY, 1,
        	 d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
        	 );
		//printf("red_print_graph(result)\n");
		//red_print_graph(result);
		//printf("red_print_graph(child)\n");
		//red_print_graph(child);
				
        result = red_bop(OR, result, child);	
        //printf("red_print_graph(result)\n");
/*        red_print_graph(result);	
*/
      }
    }
    else {
      he = converse_hrd_exp(d->u.hrd.hrd_exp);
      for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        //fprintf(RED_OUT,"hc->child\n");
        //red_print_graph(hc->child);
        child = rec_CDD(hc->child);
        //fprintf(RED_OUT,"child\n");        
        //red_print_graph(child);
        child = hdd_one_constraint(child, 
          VAR[d->var_index].U.HRD.CORRESPONDING_HDD_VI, he,         				
          -1*d->u.hrd.arc[ci].ub_numerator,d->u.hrd.arc[ci].ub_denominator,
          HYBRID_POS_INFINITY,1
        );
        result = red_bop(OR, result, child);				
      }			
    }    
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_CDD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_CDD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_CDD(ic->child);
      child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_CDD() */




struct red_type	*red_CDD(d)
     struct red_type	*d;
{
/*
  print_cpu_time("Before red_cdd()");
*/
  struct red_type	*result;

  result = rec_CDD(d);
  /*
  print_cpu_time("After red_cdd()");
  */
  return(result);
}
/* red_CDD() */





struct red_type	*rec_bottom_ordering(d)
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

  ce = cache1_check_result_key(OP_BOTTOM_ORDERING, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_bottom_ordering(bc->child);
      child = crd_one_constraint(
        child, d->var_index, bc->upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_bottom_ordering(hc->child);
      child = hrd_one_constraint(
        child, d->u.hrd.hrd_exp,         				
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
    );
    //printf("red_print_graph(result)\n");
    //red_print_graph(result);
    //printf("red_print_graph(child)\n");
    //red_print_graph(child); 			
    result = red_bop(OR, result, child);	
        //printf("red_print_graph(result)\n");
/*        red_print_graph(result);	
*/
    }
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_bottom_ordering(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_bottom_ordering(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
    if (VAR[d->var_index].PROC_INDEX > 0) { 
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        ic = &(d->u.ddd.arc[ci]);
        child = rec_bottom_ordering(ic->child);
        child = ddd_one_constraint(
          child, VAR[d->var_index].U.DISC.AUX_VI_BOTTOM_ORDERING, 
          ic->lower_bound, ic->upper_bound
        );
        result = red_bop(OR, result, child);
      }
      break; 
    }
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_bottom_ordering(ic->child);
      child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_bottom_ordering() */


struct red_type	*red_bottom_ordering(struct red_type *d) { 
  struct red_type	*result; 
  
  result = rec_bottom_ordering(d); 
  return(result); 
} 
  /* red_bottom_ordering() */ 





struct red_type	*rec_back_to_original_ordering(d)
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

  ce = cache1_check_result_key(OP_BACK_TO_ORIGINAL_ORDERING, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_back_to_original_ordering(bc->child);
      child = crd_one_constraint(
        child, d->var_index, bc->upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_back_to_original_ordering(hc->child);
      child = hrd_one_constraint(
        child, d->u.hrd.hrd_exp,         				
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
    );
    //printf("red_print_graph(result)\n");
    //red_print_graph(result);
    //printf("red_print_graph(child)\n");
    //red_print_graph(child); 			
    result = red_bop(OR, result, child);	
        //printf("red_print_graph(result)\n");
/*        red_print_graph(result);	
*/
    }
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_back_to_original_ordering(ic->child);
      child = ddd_one_constraint(
        child, VAR[d->var_index].U.DISC.ORIG_VI_BOTTOM_ORDERING, 
        ic->lower_bound, ic->upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_back_to_original_ordering(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_back_to_original_ordering(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_back_to_original_ordering(ic->child);
      child = ddd_one_constraint(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_back_to_original_ordering() */


struct red_type	*red_back_to_original_ordering(struct red_type *d) { 
  struct red_type	*result; 
  
  result = rec_back_to_original_ordering(d); 
  return(result); 
} 
  /* red_back_to_original_ordering() */ 




rec_mode_zero_distance(d)
     struct red_type	*d;
{
  int				ci, di;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return;

// check this!!
  ce = cache1_check_result_key(OP_MODE_ZERO_DISTANCE, d); 
  if (ce->result) {
    return; 
  } 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      rec_mode_zero_distance(d->u.crd.arc[ci].child);
    }
    break; 
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_mode_zero_distance(d->u.hrd.arc[ci].child);
    }
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      rec_mode_zero_distance(d->u.fdd.arc[ci].child);
    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      rec_mode_zero_distance(d->u.dfdd.arc[ci].child);
    }
    break; 
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
	&& VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        for (di = d->u.ddd.arc[ci].lower_bound; di <= d->u.ddd.arc[ci].upper_bound; di++)
          MODE[di].distance = 0;
      }
    }
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        rec_mode_zero_distance(d->u.ddd.arc[ci].child);
      }
    }
  }
}
/* rec_mode_zero_distance() */



red_mode_distance(d)
     struct red_type	*d;
{
  int flag_change, xi, mi;

  for (mi = 0; mi < MODE_COUNT; mi++)
    MODE[mi].distance = 2*MODE_COUNT;

//check this
  cache1_clear(OP_MODE_ZERO_DISTANCE); 
  rec_mode_zero_distance(d);

//check this

  for (flag_change = 1; flag_change; ) {
    flag_change = 0;
    for (xi = 1; xi < XTION_COUNT; xi++) {
      if (   valid_mode_index(XTION[xi].src_mode_index)
          && valid_mode_index(XTION[xi].dst_mode_index)
          && MODE[XTION[xi].src_mode_index].distance 
             > MODE[XTION[xi].dst_mode_index].distance + 1
          ) {
      	flag_change = 1;
        MODE[XTION[xi].src_mode_index].distance = MODE[XTION[xi].dst_mode_index].distance + 1;
      }
    }
  }
}
/* red_mode_distance() */






void 	rec_check_abnormal_XTION_INSTANCE(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE) {
    return;
  }
  else if (d->var_index == TYPE_FALSE) {
    return;
  }

  ce = cache1_check_result_key(OP_CHECK_ABNORMAL_XTION_INSTANCE, d); 
  if (ce->result) {
    return; 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      rec_check_abnormal_XTION_INSTANCE(d->u.crd.arc[ci].child);
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_check_abnormal_XTION_INSTANCE(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      if (   d->u.ddd.arc[ci].lower_bound < d->u.ddd.arc[ci].upper_bound 
	  && d->u.ddd.arc[ci].upper_bound == 216
	  ) 
        bk("Gotcha!"); 
      rec_check_abnormal_XTION_INSTANCE(d->u.ddd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      rec_check_abnormal_XTION_INSTANCE(d->u.fdd.arc[ci].child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      rec_check_abnormal_XTION_INSTANCE(d->u.dfdd.arc[ci].child);
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      rec_check_abnormal_XTION_INSTANCE(d->u.ddd.arc[ci].child);
    }
    break;
  }

  ce->result = (struct red_type *) TYPE_TRUE;

  //printf("result %f\n",result);
  return;
}
/* rec_check_abnormal_XTION_INSTANCE() */



void 	red_check_abnormal_XTION_INSTANCE(d)
     struct red_type	*d;
{ 
  cache1_clear(OP_CHECK_ABNORMAL_XTION_INSTANCE); 
  rec_check_abnormal_XTION_INSTANCE(d);
} 
/* red_check_abnormal_XTION_INSTANCE() */






float 	rec_volume_CDD(d)
     struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  float				result;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE) {
    return 1.0;
  }
  else if (d->var_index == TYPE_FALSE) {
    return 0.0;
  }

  ce = cache1_check_result_key(OP_VOLUME_CDD, d); 
  if (ce->result) {
    return((float) (int) ce->result); 
  } 

  result = 0.0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    printf("warning : rec_volume_CDD() : TYPE_CRD should not appear in CDD\n");
    exit(0);
    break; 
  case TYPE_XTION_INSTANCE: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = result + ((float)(d->u.ddd.arc[ci].upper_bound - d->u.ddd.arc[ci].lower_bound + 1)
		/(float)(PROCESS[VAR[d->var_index].PROC_INDEX].firable_xtion_count))
		*rec_volume_CDD(d->u.ddd.arc[ci].child);
    }
    break; 
  case TYPE_HRD: 
	printf("warning : rec_volume_CDD() : TYPE_HRD should not appear in CDD\n");
	exit(0);
  case TYPE_HDD: 
    for (ci = 0; ci < d->u.hdd.child_count; ci++) {
      result = result
	     + ((( (  ((float)d->u.hdd.arc[ci].ub_numerator) + 1)
	            / ((float) d->u.hdd.arc[ci].ub_denominator)
		    )
		  -(  ((float)d->u.hdd.arc[ci].lb_numerator)
	            / ((float) d->u.hdd.arc[ci].lb_denominator)
		    )
		  )
		 /(((float) HYBRID_POS_INFINITY) - ((float) HYBRID_NEG_INFINITY) + 1)
		)
		*rec_volume_CDD(d->u.hdd.arc[ci].child);
    } 
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = result 
      + ((float)(d->u.fdd.arc[ci].upper_bound - d->u.fdd.arc[ci].lower_bound + 1)
      /(float)(VAR[d->var_index].U.FLT.UB - VAR[d->var_index].U.FLT.LB + 1))
	*rec_volume_CDD(d->u.fdd.arc[ci].child);

    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = result 
      + ((float)(d->u.dfdd.arc[ci].upper_bound - d->u.dfdd.arc[ci].lower_bound + 1)
      /(float)(VAR[d->var_index].U.DBLE.UB - VAR[d->var_index].U.DBLE.LB + 1))
	*rec_volume_CDD(d->u.dfdd.arc[ci].child);

    }
    break; 
  default: 
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
  	&& VAR[d->var_index].PROC_INDEX
  	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = result + ((float)(d->u.ddd.arc[ci].upper_bound - d->u.ddd.arc[ci].lower_bound + 1)
		/(float)(PROCESS[VAR[d->var_index].PROC_INDEX].reachable_mode_count))
		*rec_volume_CDD(d->u.ddd.arc[ci].child);
      }
    }
    else {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = result + ((float)(d->u.ddd.arc[ci].upper_bound - d->u.ddd.arc[ci].lower_bound + 1)
		/(float)(VAR[d->var_index].U.DISC.UB 
		  - VAR[d->var_index].U.DISC.LB + 1
		))
		*rec_volume_CDD(d->u.ddd.arc[ci].child);
      }
    }
  }

  ce->result = (struct red_type *) (int) result; 
  return(result);
}
/* rec_volume_CDD() */



float red_volume_CDD(d)
     struct red_type	*d;
{
  float	result;

  result = rec_volume_CDD(d);

  return(result);
}
/* red_volume_CDD() */






int	rec_trigger_xtion_count(d)
     struct red_type	*d;
{
  int				ci, result;
  struct ddd_child_type		*ic;
  struct red_type		*child;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(1);
  else if (d->var_index == TYPE_FALSE)
    return(0);

  ce = cache1_check_result_key(OP_TRIGGER_XTION_COUNT, d); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = 0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child = NORM_FALSE;
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      child = red_bop(OR, d->u.crd.arc[ci].child, child);
    }
    result = rec_trigger_xtion_count(child);
    break;
  case TYPE_HRD:
    child = NORM_FALSE;
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = red_bop(OR, d->u.hrd.arc[ci].child, child);
    }
    result = rec_trigger_xtion_count(child);
    break;
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = result +
		(d->u.ddd.arc[ci].upper_bound-d->u.ddd.arc[ci].lower_bound+1)
		*rec_trigger_xtion_count(d->u.ddd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    child = NORM_FALSE;
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = red_bop(OR, d->u.fdd.arc[ci].child, child);
    }
    result = rec_trigger_xtion_count(child);
    break;
  case TYPE_DOUBLE:
    child = NORM_FALSE;
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = red_bop(OR, d->u.dfdd.arc[ci].child, child);
    }
    result = rec_trigger_xtion_count(child);
    break;
  default:
    child = NORM_FALSE;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      child = red_bop(OR, d->u.ddd.arc[ci].child, child);
    }
    result = rec_trigger_xtion_count(child);
    break;
  }
  return((int) (ce->result 
    = (struct red_type *) result
  ) );
}
  /* rec_trigger_xtion_count() */



int	red_trigger_xtion_count(d)
     struct red_type	*d;
{
  int	result;

  result = rec_trigger_xtion_count(d);

  return(result);
}
/* red_trigger_xtion_count() */







int	rec_path_count(d)
     struct red_type	*d;
{
  int				ci, result;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(1);
  else if (d->var_index == TYPE_FALSE)
    return(0);

  ce = cache2_check_result_key(OP_PATH_THRESHOLD, d, 
    (struct red_type *) INT_MAX
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = 0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = result + rec_path_count(d->u.crd.arc->child);
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = result + rec_path_count(d->u.hrd.arc->child);
    }
    break;
  case TYPE_LAZY_EXP: 
    return(1); 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = result + rec_path_count(d->u.fdd.arc->child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = result + rec_path_count(d->u.dfdd.arc->child);
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = result + rec_path_count(d->u.ddd.arc->child);
    }
    break;
  }
  return((int) (ce->result 
    = (struct red_type *) result
  ) );
}
  /* rec_path_count() */



int	red_path_count(d)
     struct red_type	*d;
{
  int	result;

  result = rec_path_count(d);

  return(result);
}
/* red_path_count() */



int	THRESHOLD_PATH; 

int	rec_path_threshold(d)
     struct red_type	*d;
{
  int				ci, result;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(1);
  else if (d->var_index == TYPE_FALSE)
    return(0);

  ce = cache2_check_result_key(OP_PATH_THRESHOLD, 
    d, (struct red_type *) THRESHOLD_PATH
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = 0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; 
         ci >= 0 && result < THRESHOLD_PATH; 
         ci--
         ) {
      result = result + rec_path_threshold(d->u.crd.arc->child);
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; 
         ci >= 0 && result < THRESHOLD_PATH; 
         ci--
         ) {
      result = result + rec_path_threshold(d->u.hrd.arc->child);
    }
    break;
  case TYPE_LAZY_EXP: 
    return(1); 
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; 
         ci >= 0 && result < THRESHOLD_PATH; 
         ci--
         ) {
      result = result + rec_path_threshold(d->u.fdd.arc->child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; 
         ci >= 0 && result < THRESHOLD_PATH; 
         ci--
         ) {
      result = result + rec_path_threshold(d->u.dfdd.arc->child);
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; 
         ci >= 0 && result < THRESHOLD_PATH; 
         ci--
         ) {
      result = result + rec_path_threshold(d->u.ddd.arc->child);
    }
    break;
  }
  return((int) (ce->result 
    = (struct red_type *) result
  ) );
}
  /* rec_path_threshold() */



int	red_path_threshold(d, th)
     struct red_type	*d;
     int		th; 
{
  int	result; 
  
  THRESHOLD_PATH = th; 
  result = rec_path_threshold(d);
  if (result > th) 
    return(TYPE_TRUE); 
  else 
    return(TYPE_FALSE); 
}
/* red_path_threshold() */










int	rec_discrete_model_count(d, expected_vi)
     struct red_type	*d;
     int		expected_vi; 
{
  int				ci, result;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE) {
    result = 1; 
    for (ci = expected_vi; ci < VARIABLE_COUNT; ci++) { 
      if (   (   VAR[ci].TYPE == TYPE_DISCRETE 
              || VAR[ci].TYPE == TYPE_POINTER
              ) 
          && !(VAR[ci].STATUS & FLAG_VAR_PRIMED)
          ) 
        result = result * (VAR[ci].U.DISC.UB - VAR[ci].U.DISC.LB + 1);   
    } 
    fprintf(RED_OUT, "==[expected vi = %1d, result = %1d]=====\n", 
      expected_vi, result
    ); 
    red_print_graph(d); 
    return(result); 
  }
  else if (d->var_index == TYPE_FALSE)
    return(0); 

  ce = cache1_check_result_key(OP_DISCRETE_MODEL_COUNT, d); 
  if (ce->result) {
    fprintf(RED_OUT, "==[cached expected vi = %1d at %1d:%s, result = %1d]=====\n", 
      expected_vi, d->var_index, VAR[d->var_index].NAME, (int) ce->result
    ); 
    red_print_graph(d); 
    return((int) ce->result); 
  } 

  result = 0;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = result 
      + rec_discrete_model_count(
        d->u.crd.arc->child, d->var_index + 1
      );
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = result 
      + rec_discrete_model_count(
        d->u.hrd.arc[ci].child, d->var_index + 1
      );
    }
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = result 
      + rec_discrete_model_count(
        d->u.fdd.arc[ci].child, d->var_index + 1
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = result 
      + rec_discrete_model_count(
        d->u.dfdd.arc[ci].child, d->var_index + 1
      );
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = result 
      + (d->u.ddd.arc[ci].upper_bound - d->u.ddd.arc[ci].lower_bound+1)
        * rec_discrete_model_count(
            d->u.ddd.arc->child, d->var_index + 1
          ); 
    }
    for (ci = expected_vi; ci < d->var_index; ci++) { 
      if (   (   VAR[ci].TYPE == TYPE_DISCRETE 
              || VAR[ci].TYPE == TYPE_POINTER
              ) 
          && !(VAR[ci].STATUS & FLAG_VAR_PRIMED)
          ) 
        result = result * (VAR[ci].U.DISC.UB - VAR[ci].U.DISC.LB + 1);   
    } 
    return(result); 
    break;
  }
  fprintf(RED_OUT, "==[new expected vi = %1d at %1d:%s, result = %1d]=====\n", 
    expected_vi, d->var_index, VAR[d->var_index].NAME, (int) ce->result
  ); 
  red_print_graph(d); 
  return((int) (ce->result 
    = (struct red_type *) result
  ) );
}
  /* rec_discrete_model_count() */



int	red_discrete_model_count(d)
     struct red_type	*d;
{
  int	result;

  result = rec_discrete_model_count(d, INDEX_START_USER_VAR);

  return(result);
}
/* red_discrete_model_count() */



struct a23tree_type	*only_xi_tree; 

struct red_type	*rec_only_xi(d)
     struct red_type	*d;
{
  int			ci;
  struct ddd_child_type	*ic;
  struct red_type	*result;
  struct rec_type	*rec, *nrec; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(d);

  rec = rec_new(d, NORM_FALSE); 
  nrec = (struct rec_type *) add_23tree(
    rec, only_xi_tree, 
    rec_comp, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return(nrec->result); 
  }

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result, rec_only_xi(d->u.crd.arc[ci].child));
    }
    break;
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result, rec_only_xi(d->u.hrd.arc[ci].child));
    }
    break;
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result,
	ddd_lone_subtree(rec_only_xi(d->u.ddd.arc[ci].child),
	  d->var_index, 
	  d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ) );
    }
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result, rec_only_xi(d->u.fdd.arc[ci].child));
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result, rec_only_xi(d->u.dfdd.arc[ci].child));
    } 
    break;
  case TYPE_POINTER: 
    if (   VAR[d->var_index].PROC_INDEX
        && (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result,
	  ddd_lone_subtree(rec_only_xi(d->u.ddd.arc[ci].child),
	    d->var_index, 
	    d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
	) );
      }
      break; 	
    }
  
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = red_bop(OR, result, rec_only_xi(d->u.ddd.arc[ci].child));
    }
    break;
  }
  return(rec->result = result);
}
  /* rec_only_xi() */



struct red_type	*red_only_xi(d)
     struct red_type	*d;
{
  init_23tree(&only_xi_tree); 
  d = rec_only_xi(d);
  free_entire_23tree(only_xi_tree, rec_free); 

  return(d);
}
/* red_only_xi() */



int	VOC; 


int	rec_variable_occurrence_check(d)
     struct red_type	*d;
{
  int				ci, result;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == VOC)
    return(TYPE_TRUE);
  else if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(TYPE_FALSE);

  ce = cache2_check_result_key(OP_VARIABLE_OCCURRENCE_CHECK, d, 
    (struct red_type *) VOC
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = TYPE_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (CLOCK[VAR[d->var_index].U.CRD.CLOCK1] == VOC || CLOCK[VAR[d->var_index].U.CRD.CLOCK2] == VOC)
      result = TYPE_TRUE;
    else for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      if (rec_variable_occurrence_check(d->u.crd.arc[ci].child)) {
        result = TYPE_TRUE;
	break;
      }
    }
    break;
  case TYPE_HRD:
    for (ci = (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) - 1; ci >= 0; ci--)
      if (d->u.hrd.hrd_exp->hrd_term[ci].var_index == VOC)
        break;
    if (ci >= 0)
      result = TYPE_TRUE;
    else for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      if (rec_variable_occurrence_check(d->u.hrd.arc[ci].child)) {
        result = TYPE_TRUE;
	break;
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      if (rec_variable_occurrence_check(d->u.fdd.arc[ci].child)) {
        result = TYPE_TRUE;
	break;
      }
    }
    break;
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      if (rec_variable_occurrence_check(d->u.dfdd.arc[ci].child)) {
        result = TYPE_TRUE;
	break;
      }
    }
    break;
  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      if (rec_variable_occurrence_check(d->u.ddd.arc[ci].child)) {
        result = TYPE_TRUE;
	break;
      }
    }
    break;
  }
  return((int) (ce->result
    = (struct red_type *) result
  ) );
}
  /* rec_variable_occurrence_check() */



int	variable_occurrence_check(d, vi)
     struct red_type	*d;
     int		vi;
{
  int	result;

  VOC = vi;
  result = rec_variable_occurrence_check(d);

  return(result);
}
/* variable_occurrence_check() */







int 	VI_TRIGGER_TO_BE_ABSTRACTED;


int rec_trigger_to_be_abstracted(d)
	struct red_type	*d;
{
  int				ci;
  struct ddd_child_type		*ic;
  int				result;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) {
    return 1;
  }
  else if(d->var_index == VI_TRIGGER_TO_BE_ABSTRACTED) {
    return 0;
  }

  ce = cache2_check_result_key(OP_TRIGGER_TO_BE_ABSTRACTED, d, 
    (struct red_type *) VI_TRIGGER_TO_BE_ABSTRACTED
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  result = 1;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      result = rec_trigger_to_be_abstracted(d->u.crd.arc[ci].child);
	if(!result)
	  return 0;
    }
    break; 
  case TYPE_HRD: 
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      result = rec_trigger_to_be_abstracted(d->u.hrd.arc[ci].child);
	if(!result)
	  return 0;
    }
    break; 
  case TYPE_FLOAT: 
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      result = rec_trigger_to_be_abstracted(d->u.fdd.arc[ci].child);
	if(!result)
	  return 0;
    }
    break; 
  case TYPE_DOUBLE: 
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      result = rec_trigger_to_be_abstracted(d->u.dfdd.arc[ci].child);
	if(!result)
	  return 0;
    }
    break; 
  default: 
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      result = rec_trigger_to_be_abstracted(d->u.ddd.arc[ci].child);
	if(!result)
	  return 0;
    }
  }

  return((int) (ce->result 
    = (struct red_type *) result
  ) );
}

/*return false iff d contains var_index*/
int trigger_to_be_abstracted(d, var_index)
	struct red_type	*d;
	int	var_index;
{

  int	result;

  VI_TRIGGER_TO_BE_ABSTRACTED = var_index;
  result = rec_trigger_to_be_abstracted(d);

  return(result);
}






struct red_type	*rec_trigger_abstraction(d, pxi)
     struct red_type	*d;
     int		pxi;
{
  int				ci, cxi, epi, exi;
  struct ddd_child_type		*ic;
  struct red_type		*result, *child;
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE)
    return(d);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_TRIGGER_ABSTRACTION, d, 
    ((struct red_type *) pxi)
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  epi = pxi / XTION_COUNT;
  exi = pxi % XTION_COUNT;
  result = NORM_FALSE;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi],d->var_index)) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.crd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.crd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      		        crd_lone_subtree(child, d->var_index,
					  d->u.crd.arc[ci].upper_bound
					  )
		       );
      }
    }
    break;
  case TYPE_HRD:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi], d->var_index)) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.hrd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.hrd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      		        hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
					  d->u.hrd.arc[ci].ub_numerator,
					  d->u.hrd.arc[ci].ub_denominator
					  )
		       );
      }
    }
    break;
  
  case TYPE_HDD:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi],d->var_index)) {
      for (ci = 0; ci < d->u.hdd.child_count; ci++) {
        child = rec_trigger_abstraction(d->u.ddd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else{
      for (ci = 0; ci < d->u.hdd.child_count; ci++) {
        child = rec_trigger_abstraction(d->u.ddd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      	  hdd_lone_subtree(child, d->var_index, 
      	    d->u.hdd.hrd_exp,
	    d->u.hdd.arc[ci].lb_numerator,
	    d->u.hdd.arc[ci].lb_denominator, 
	    d->u.hdd.arc[ci].ub_numerator,
	    d->u.hdd.arc[ci].ub_denominator 
	) );
      }
    }
    break;
  case TYPE_XTION_INSTANCE:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      for (cxi = d->u.ddd.arc[ci].lower_bound;
           cxi <= d->u.ddd.arc[ci].upper_bound;
	         cxi++) {
        pxi = VAR[d->var_index].PROC_INDEX * XTION_COUNT + cxi;
	      child = rec_trigger_abstraction(d->u.ddd.arc[ci].child, pxi);
	      result = red_bop(OR, result,
                ddd_lone_subtree(child, d->var_index, cxi, cxi));
      }
    }
    break;
  case TYPE_FLOAT:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi],d->var_index)) {
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.fdd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else{
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.fdd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      	  fdd_lone_subtree(child,
	    d->var_index, d->u.fdd.arc[ci].lower_bound,
	    d->u.fdd.arc[ci].upper_bound
	) );
      }
    }
    break;
  case TYPE_DOUBLE:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi],d->var_index)) {
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.dfdd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else{
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.dfdd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      	  dfdd_lone_subtree(child,
	    d->var_index, d->u.dfdd.arc[ci].lower_bound,
	    d->u.dfdd.arc[ci].upper_bound
	) );
      }
    }
    break;
  default:
    if ((!epi) || trigger_to_be_abstracted(XTION[exi].red_trigger[epi],d->var_index)) {
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.ddd.arc[ci].child, pxi);
        result = red_bop(OR, result, child);
      }
    }
    else{
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        child = rec_trigger_abstraction(d->u.ddd.arc[ci].child, pxi);
        result = red_bop(OR, result,
      		        ddd_lone_subtree(child,
					      d->var_index, d->u.ddd.arc[ci].lower_bound,
					      d->u.ddd.arc[ci].upper_bound
					      )
			);
      }
    }
    break;
  }

  return (ce->result = result);
}




struct red_type	*red_trigger_abstraction(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_trigger_abstraction(d, 0);

  return(result);
}
/* red_trigger_abstraction */



int	*OMAP, *RMAP, *OMAP_BOTTOM, *OMAP_HALF_INTERLEAVING, *OMAP_FULL_INTERLEAVING; 





struct red_type	*rec_eliminate_magnitudes(d)
     struct red_type	*d;
{
  int				ci, cj, c1, c2;
  struct red_type		*child, *result, *gchild;
  struct hrd_exp_type		*he;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_ELIMINATE_MAGNITUDE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_eliminate_magnitudes(d->u.bdd.zero_child), 
      rec_eliminate_magnitudes(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0 || c1 > c2) {  
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        child = rec_eliminate_magnitudes(bc->child);
        result = red_bop(OR, result, child);
      }
    } 
    else { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
        bc = &(d->u.crd.arc[ci]);
      	child = bc->child; 
      	if (bc->upper_bound == CLOCK_POS_INFINITY) { 
          child = rec_eliminate_magnitudes(bc->child); 
          result = red_bop(OR, result, child); 
        }
        else switch (VAR[child->var_index].TYPE) { 
      	case TYPE_CRD: 
      	  if (VAR[child->var_index].U.CRD.CLOCK1 == c2 && VAR[child->var_index].U.CRD.CLOCK2 == c1) { 
      	    for (cj = child->u.crd.child_count-1; cj >= 0; cj--) { 
      	      gchild = child->u.crd.arc[cj].child; 
              gchild = rec_eliminate_magnitudes(gchild); 
      	      if (bc->upper_bound + child->u.crd.arc[cj].upper_bound == 0) { 
      	        gchild = crd_one_constraint(gchild, d->var_index, bc->upper_bound); 
      	        gchild = crd_one_constraint(gchild, child->var_index, 
					     child->u.crd.arc[cj].upper_bound
					     ); 
      	      } 
      	      result = red_bop(OR, result, gchild); 
      	    } 
      	    break; 
      	  } 
        default: 
          child = rec_eliminate_magnitudes(child); 
          result = red_bop(OR, result, child); 
        }
      }
    } 
    break;
  case TYPE_HRD:
    for(ci = d->u.hrd.child_count-1; ci>=0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_eliminate_magnitudes(hc->child);
      result = red_bop(OR, result, child); 
    } 
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_eliminate_magnitudes(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_eliminate_magnitudes(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  default:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_eliminate_magnitudes(ic->child);
      child = ddd_one_constraint
		(child, d->var_index, ic->lower_bound, ic->upper_bound);
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_eliminate_magnitudes() */  




struct red_type	*red_eliminate_magnitudes(d) 
	struct red_type	*d; 
{
  struct red_type	*result; 
  int			w; 
  
  if (!CLOCK_COUNT) 
    return(d); 

  RT[w = RT_TOP++] = d; 
  d = red_tight_all_pairs(w); 
  RT_TOP--; /* w */ 
  
  result = rec_eliminate_magnitudes(d); 
  
  return(result); 	
} 
  /* red_eliminate_magnitudes() */  
  
  
  


struct red_type	*rec_time_upperbounded(d, flag_ub)
     struct red_type	*d;
     int		flag_ub; 
{
  int				ci, c1, c2;
  struct red_type		*result, *child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    if (flag_ub) 
      return(d);
    else 
      return(NORM_FALSE); 

  ce = cache2_check_result_key(OP_TIME_UPPERBOUNDED, d, 
    (struct red_type *) flag_ub
  ); 

  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_time_upperbounded(d->u.bdd.zero_child, flag_ub), 
      rec_time_upperbounded(d->u.bdd.one_child, flag_ub)
    );
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if ((!flag_ub) && c1 && (!c2)) { 
      ci = d->u.crd.child_count-1; 
      if(d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) {
	child = rec_time_upperbounded(d->u.crd.arc[ci].child, flag_ub);
        child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child); 
	ci--; 
      }
      for (; ci >= 0; ci--) { 
	child = rec_time_upperbounded(d->u.crd.arc[ci].child, TYPE_TRUE);
        child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_time_upperbounded(d->u.crd.arc[ci].child, flag_ub);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_time_upperbounded(d->u.fdd.arc[ci].child, flag_ub);
      child = fdd_one_constraint(
        child, d->var_index, 
      	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_time_upperbounded(d->u.dfdd.arc[ci].child, flag_ub);
      child = dfdd_one_constraint(
        child, d->var_index, 
      	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_time_upperbounded(d->u.ddd.arc[ci].child, flag_ub);
      child = ddd_one_constraint(
        child, d->var_index, 
      	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
  }
  return(ce->result = result); 
}
  /* rec_time_upperbounded() */






struct red_type	*red_time_upperbounded(d)
     struct red_type	*d;
{
  if (!CLOCK_COUNT) 
    return(d); 

  d = rec_time_upperbounded(d, 0);
  return(d);
}
/* red_time_upperbounded() */ 




int	VI_PRESENCE; 

struct red_type	*rec_var_presence(d)
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
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_VAR_PRESENCE, 
    d, (struct red_type *) VI_PRESENCE
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (d->var_index == VI_PRESENCE) 
      result = d; 
    else 
      result = bdd_new(d->var_index, 
        rec_var_presence(d->u.bdd.zero_child), 
        rec_var_presence(d->u.bdd.one_child)
      );
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (CLOCK[c1] == VI_PRESENCE || CLOCK[c2] == VI_PRESENCE) {  
      ci = d->u.crd.child_count-1; 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
      	result = rec_var_presence(d->u.crd.arc[ci].child); 
        for (ci--; ci >= 0; ci--) 
          result = red_bop(OR, result, 
            crd_one_constraint(d->u.crd.arc[ci].child, d->var_index, 
              d->u.crd.arc[ci].upper_bound
          ) ); 
      } 
      else 
        result = d; 
    }
    else 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        bc = &(d->u.crd.arc[ci]);
        child = rec_var_presence(bc->child);
        result = red_bop(OR, result, 
          crd_one_constraint(child, d->var_index, 
            d->u.crd.arc[ci].upper_bound
        ) );
      }
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (i = 0; i < len; i++) {
      if (VI_PRESENCE == d->u.hrd.hrd_exp->hrd_term[i].var_index) 
        break;
    } 
    if (i < len) { 
      ci = d->u.hrd.child_count-1; 
      if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
          && d->u.hrd.arc[ci].ub_denominator == 1
          ) { 
       	result = rec_var_presence(d->u.hrd.arc[ci].child); 
        for (ci--; ci >= 0; ci--) 
          result = red_bop(OR, result, 
            hrd_one_constraint(d->u.hrd.arc[ci].child, 
              d->u.hrd.hrd_exp, 
              d->u.hrd.arc[ci].ub_numerator, 
              d->u.hrd.arc[ci].ub_denominator
          ) ); 
      } 
      else 
        result = d; 
    }
    else 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        hc = &(d->u.hrd.arc[ci]);
        child = rec_var_presence(hc->child);
        result = red_bop(OR, result, 
          hrd_one_constraint(child, d->u.hrd.hrd_exp, 
            d->u.hrd.arc[ci].ub_numerator, 
            d->u.hrd.arc[ci].ub_denominator
        ) );
      }
    break;
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_var_presence");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree( 
      rec_var_presence(d->u.lazy.false_child), 
      rec_var_presence(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    );
    break; 

    fprintf(RED_OUT, "\nError:\n"); 
    fflush(RED_OUT); 
    bk(0); 
    break; 

  case TYPE_FLOAT: 
    if (d->var_index == VI_PRESENCE) 
      result = d; 
    else if (   d->var_index > VI_PRESENCE 
             && VAR[VI_PRESENCE].TYPE != TYPE_CLOCK
             && VAR[VI_PRESENCE].TYPE != TYPE_DENSE 
             ) 
      result = NORM_FALSE; 
    else for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_var_presence(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 

  case TYPE_DOUBLE: 
    if (d->var_index == VI_PRESENCE) 
      result = d; 
    else if (   d->var_index > VI_PRESENCE 
             && VAR[VI_PRESENCE].TYPE != TYPE_CLOCK
             && VAR[VI_PRESENCE].TYPE != TYPE_DENSE 
             ) 
      result = NORM_FALSE; 
    else for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_var_presence(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 

  default: 
    if (d->var_index == VI_PRESENCE) 
      result = d; 
    else if (   d->var_index > VI_PRESENCE 
             && VAR[VI_PRESENCE].TYPE != TYPE_CLOCK
             && VAR[VI_PRESENCE].TYPE != TYPE_DENSE 
             ) 
      result = NORM_FALSE; 
    else for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      child = rec_var_presence(ic->child);
      child = ddd_one_constraint(
        child, d->var_index, ic->lower_bound, ic->upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_var_presence() */  




struct red_type	*red_var_presence(d, vi) 
  struct red_type	*d; 
  int	vi; 
{
  struct red_type	*result; 
  
  VI_PRESENCE = vi; 
  result = rec_var_presence(d); 
  
  return(result); 	
} 
  /* red_var_presence() */  



  
  


int	VI_ABSENCE; 

struct red_type	*rec_var_absence(d)
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

  ce = cache2_check_result_key(OP_VAR_ABSENCE, 
    d, (struct red_type *) VI_ABSENCE
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  if (   d->var_index > VI_ABSENCE
      && VAR[VI_ABSENCE].TYPE != TYPE_CLOCK
      && VAR[VI_ABSENCE].TYPE != TYPE_DENSE
      ) 
    result = d; 
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (d->var_index == VI_ABSENCE) 
      result = NORM_FALSE; 
    else 
      result = bdd_new(d->var_index, 
        rec_var_absence(d->u.bdd.zero_child), 
        rec_var_absence(d->u.bdd.one_child)
      );
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (CLOCK[c1] == VI_ABSENCE || CLOCK[c2] == VI_ABSENCE) {  
      ci = d->u.crd.child_count-1; 
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) { 
      	result = rec_var_absence(d->u.crd.arc[ci].child); 
      } 
    }
    else for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      bc = &(d->u.crd.arc[ci]);
      child = rec_var_absence(bc->child);
      result = red_bop(OR, result, 
        crd_one_constraint(child, d->var_index, 
          d->u.crd.arc[ci].upper_bound
      ) );
    }
    break;
  case TYPE_HRD:
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (i = 0; i < len; i++) {
      if (VI_ABSENCE == d->u.hrd.hrd_exp->hrd_term[i].var_index) 
        break;
    } 
    if (i < len) { 
      ci = d->u.hrd.child_count-1; 
      if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
          && d->u.hrd.arc[ci].ub_denominator == 1
          ) { 
       	result = rec_var_absence(d->u.hrd.arc[ci].child); 
      } 
    }
    else for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      hc = &(d->u.hrd.arc[ci]);
      child = rec_var_absence(hc->child);
      result = red_bop(OR, result, 
        hrd_one_constraint(child, d->u.hrd.hrd_exp, 
          d->u.hrd.arc[ci].ub_numerator, 
          d->u.hrd.arc[ci].ub_denominator
      ) );
    }
    break;
  case TYPE_HDD: 
    fprintf(RED_OUT,"ERROR in rec_var_absence");
    exit(0);
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_subtree( 
      rec_var_absence(d->u.lazy.false_child), 
      rec_var_absence(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    );
    break; 
    
    fprintf(RED_OUT,"ERROR in rec_cdd");
    exit(0);
    break;

  case TYPE_FLOAT: 
    if (d->var_index == VI_ABSENCE) 
      result = NORM_FALSE; 
    else for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_var_absence(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint( 
        child, d->var_index, d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  case TYPE_DOUBLE: 
    if (d->var_index == VI_ABSENCE) 
      result = NORM_FALSE; 
    else for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_var_absence(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint( 
        child, d->var_index, d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;

  default: 
    if (d->var_index == VI_ABSENCE) 
      result = NORM_FALSE; 
    else for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      child = rec_var_absence(ic->child);
      child = ddd_one_constraint(
        child, d->var_index, ic->lower_bound, ic->upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }

  return(ce->result = result);
}
  /* rec_var_absence() */  




struct red_type	*red_var_absence(d, vi) 
  struct red_type	*d; 
  int	vi; 
{
  struct red_type	*result; 
  
  VI_ABSENCE = vi; 
  result = rec_var_absence(d); 
  
  return(result); 	
} 
  /* red_var_absence() */  
  
  





int	rec_check_ooo(d, parent_vi, parent_hrdexp)
  struct red_type	*d; 
  int			parent_vi; 
  struct hrd_exp_type	*parent_hrdexp; 
{
  int	ci, result;

/*
  fprintf(RED_OUT, "count_mark_clocks = %1d\n", ++count_mark_clocks); 
  for (; count_mark_clocks == 119; ) ; 
*/
  if (d == NORM_NO_RESTRICTION) { 
    return(0);
  }
  else if (d == NORM_FALSE) {
    if (parent_vi >= 0) 
      return(1); 
    else 
      return(0);
  }
  else if (parent_vi > d->var_index) { 
    fprintf(RED_OUT, "\nvariable ooo with parent vi=%1d:%s-->vi=%1d:%s\n", 
      parent_vi, VAR[parent_vi].NAME, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    red_print_graph(d); 
    fflush(RED_OUT); 
    return(1); 
  } 
  else if (   parent_vi == d->var_index
           && VAR[d->var_index].TYPE == TYPE_HRD
           && HRD_EXP_COMP(parent_hrdexp, d->u.hrd.hrd_exp) >= 0
           ) { 
    fprintf(RED_OUT, "\nvariable ooo with HRD parent vi=%1d:%s-->vi=%1d:%s\n", 
      parent_vi, VAR[parent_vi].NAME, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fprintf(RED_OUT, "parent hrd exp:"); 
    hrd_exp_print(parent_hrdexp, 0); 
    fprintf(RED_OUT, "\nd hrd exp:"); 
    hrd_exp_print(d->u.hrd.hrd_exp, 0); 
    fprintf(RED_OUT, "\n"); 
    red_print_graph(d); 
    fflush(RED_OUT); 
    return(1); 
  } 
  else if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
           && d->result_stack->result
           ) { 
    return(0);
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD:
    return(
      rec_check_ooo(d->u.bdd.zero_child, d->var_index, NULL)
    | rec_check_ooo(d->u.bdd.one_child, d->var_index, NULL)
    ); 
    break; 
  case TYPE_CRD /* TYPE_CRD*/ : 
    result = 0; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      result = result 
      | rec_check_ooo(d->u.crd.arc[ci].child, d->var_index, NULL);
    }
    break;
  case TYPE_HRD /* TYPE_HRD*/ : 
    result = 0; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.hrd.arc[ci].child, d->var_index, d->u.hrd.hrd_exp);
    break;
    
  case TYPE_CDD /* TYPE_CDD*/ : 
    result = 0; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.ddd.arc[ci].child, d->var_index, NULL);
    break;
    
  case TYPE_HDD /* TYPE_HDD*/ :
    result = 0; 
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.hdd.arc[ci].child, d->var_index, NULL);
    break;    
  case TYPE_LAZY_EXP: 
    return(
      rec_check_ooo(d->u.lazy.false_child, d->var_index, NULL) 
    | rec_check_ooo(d->u.lazy.true_child, d->var_index, NULL)
    );  
    break; 

  case TYPE_FLOAT:
    result = 0; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.fdd.arc[ci].child, d->var_index, NULL);
    break; 

  case TYPE_DOUBLE:
    result = 0; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.dfdd.arc[ci].child, d->var_index, NULL);
    break; 

  default:
    result = 0; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      result = result 
      | rec_check_ooo(d->u.ddd.arc[ci].child, d->var_index, NULL);
  }
  return(result); 
}
  /* rec_check_ooo() */




int	red_check_ooo(d)
     struct red_type	*d;
{
  int	result; 
  
  if (d == NORM_FALSE) 
    return (1); 

  red_init_result(d); 
  result = rec_check_ooo(d, -1);
  red_clear_result(d); 
  
  if (result) 
    return(1); 
  else 
    return(0); 
}
/* red_check_ooo() */ 



red_test()
{
  int 			m1, m2, m3, m4, m5, zvi, b, t;
  struct red_type	*conj1, *conj2, *conj3, *result;

/*  bop_test();
*/

  conj1 = crd_atom(ZONE[0][1], -6);
  conj1 = crd_one_constraint(conj1, ZONE[1][3], -9);
  conj1 = crd_one_constraint(conj1, ZONE[2][1], 11);
  fprintf(RED_OUT, "\nconj1:\n");
  red_print_graph(conj1);

  conj2 = crd_atom(ZONE[0][2], -3);
  conj2 = crd_one_constraint(conj2, ZONE[2][1], 11);
  fprintf(RED_OUT, "\nconj2:\n");
  red_print_graph(conj2);

  result = red_bop(OR, conj1, conj2);
  fprintf(RED_OUT, "\nresult in CRD:\n");
  red_print_graph(result);

  conj3 = red_CDD(result);
  fprintf(RED_OUT, "\nresult in CDD:\n");
  red_print_graph(conj3);
  fflush(RED_OUT);

  exit(0);
}
/* red_test() */



