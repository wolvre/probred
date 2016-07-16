/*===================================================================
*
*       hashman.c
*
*/

#include <stdlib.h>
#include <string.h> 
#include <stdio.h>
#include <ctype.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
*/
#include "redparse.h" 
#include "redparse.e" 

#include "redbop.h" 
#include "redbop.e" 
#include "hybrid.e" 
#include "redbasics.h" 
#include "redbasics.e" 
#include "treeman.h" 
#include "treeman.e" 
#include "hashman.h"

extern int	det_si, det_ei, det_di; 
  
#define hash_target (0xb63f3b0) /* (0xad36650) */
#define red_target ((struct red_type *) (0xb63f3a0)) 

struct cache2_hash_entry_type	*hashtar; 


/* Primes for cache hash functions. */
#define DD_P1			12582917
#define DD_P2			4256249
#define DD_P3			741457
#define DD_P4			1618033999
#define	DD_P5			2750159

#define COUNT_HASH_PRIME	80 
int	HASH_PRIME[COUNT_HASH_PRIME]; 


struct red_type	*hash_t; 



struct hash_hrd_exp_type	
	HASH_SHARE_HRD_EXP[SIZE_HASH_SHARED_HRD_EXPS]; 

int	hashkey_shared_hrd_exp(he) 
	struct hrd_exp_type	*he; 
{
  int	key, ti, len; 
  
  len = he->status & MASK_HYBRID_LENGTH;
  key = he->hrd_term[0].var_index; 
  key = key * HASH_PRIME[0] + he->hrd_term[0].coeff; 
  for (ti = 1; ti < len; ti++) {
    key = key * HASH_PRIME[2*ti - 1] + he->hrd_term[ti].var_index; 
    key = key * HASH_PRIME[2*ti] + he->hrd_term[ti].coeff;
  }
  return((key >> LEHGTH_SHIFT_SHARED_HRD_EXPS) & MASK_HASH_SHARED_HRD_EXPS); 
}
  /* hashkey_shared_hrd_exp() */ 
  
  
	
struct hrd_exp_type	*hrd_exp_share(he) 
	struct hrd_exp_type	*he; 
{ 
  int					key; 
  struct hash_hrd_exp_link_type	*hs;

//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  key = hashkey_shared_hrd_exp(he); 
  if (HASH_SHARE_HRD_EXP[key].count) { 
    for (hs = HASH_SHARE_HRD_EXP[key].hrd_exp_list; 
         hs; 
         hs = hs->next_hash_hrd_exp_link
         ) { 
      if (!HRD_EXP_COMP(hs->hrd_exp, he))
        break; 
    } 
  }
  else 
    hs = NULL; 
  if (!hs) { 
    hs = (struct hash_hrd_exp_link_type *) 
       malloc(sizeof(struct hash_hrd_exp_link_type)); 
    hs->hrd_exp = he; 
    hs->next_hash_hrd_exp_link = HASH_SHARE_HRD_EXP[key].hrd_exp_list;
    HASH_SHARE_HRD_EXP[key].hrd_exp_list = hs;
    HASH_SHARE_HRD_EXP[key].count++; 
  } 
  else { 
    hrd_exp_free(he); 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(hs->hrd_exp); 
}
  /* hrd_exp_share() */ 
  
  
void 	hrd_exp_delete(he) 
	struct hrd_exp_type	*he; 
{ 
  int				key; 
  struct hash_hrd_exp_link_type	*hs, *phs, dummy_head;
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);    
  key = hashkey_shared_hrd_exp(he); 
  if (HASH_SHARE_HRD_EXP[key].count) { 
    dummy_head.next_hash_hrd_exp_link 
    = HASH_SHARE_HRD_EXP[key].hrd_exp_list; 
    for (phs = &dummy_head, hs = phs->next_hash_hrd_exp_link; 
         hs; 
         phs = hs, hs = hs->next_hash_hrd_exp_link
         ) { 
      if (!HRD_EXP_COMP(hs->hrd_exp, he))
        break; 
    } 
    if (!hs) { 
      fprintf(RED_OUT, "Error, something wrong, an already-deleted node is to be deleted again. \n"); 
      exit(0); 	
    } 
    else { 
      phs->next_hash_hrd_exp_link 
      = hs->next_hash_hrd_exp_link;
      free(hs); 
      HASH_SHARE_HRD_EXP[key].hrd_exp_list 
      = dummy_head.next_hash_hrd_exp_link;
    } 
  }
  else {
    fprintf(RED_OUT, "Error, something wrong, an already-deleted node is to be deleted again. \n"); 
    exit(0); 
  }
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* hrd_exp_delete() */ 
  
  
	


/********************************************************************
 *  We first have the following routines for the diagram sharing. 
 */
/* The hashkey for share diagram is calculated with the assumption 
 * that the childred of d has already been shared. 
 */

// int	count_red_share = 0; 

struct hash_share_type	HASH_SHARE[SIZE_HASH_SHARED_DIAGRAMS]; 
int			COUNT_HASH_SHARE_USED_ENTRIES = 0; 
int			COUNT_HASH_SHARE_REGISTERED_DIAGRAMS = 0; 
  
int	hashkey_diagram(d) 
	struct red_type	*d; 
{ 
  int		key, ci, *vp; 
  
  key = d->var_index; 
/*
  if (count_red_share == 9) { 
    fprintf(RED_OUT, "in hashkey_diagram, key=%1d, TOP_LEVEL_CHILD_STACK=%1d, TOP_CHILD_STACK=%1d\n", 
      key, TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK
    ); 	
  } 
*/
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_FALSE: 
  case TYPE_TRUE: 
    key = key * HASH_PRIME[0]; 
    break; 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    key = key * HASH_PRIME[18]; 
    key = (key + ((int) d->u.bdd.zero_child))*HASH_PRIME[19]; 
    key = (key + ((int) d->u.bdd.one_child))*HASH_PRIME[20]; 
    break;
  case TYPE_CRD: 
    key = key * HASH_PRIME[3];  
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      key = (key + d->u.crd.arc[ci].upper_bound) 
      * HASH_PRIME[(2*ci+4)%COUNT_HASH_PRIME]; 
      key = (key + ((int) d->u.crd.arc[ci].child))
      * HASH_PRIME[(2*ci+5)%COUNT_HASH_PRIME]; 
    }
    break; 
  case TYPE_HRD: 
    key = (key * HASH_PRIME[6] + ((int) d->u.hrd.hrd_exp))*HASH_PRIME[7];
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      key = (key + d->u.hrd.arc[ci].ub_numerator) 
      * HASH_PRIME[(3*ci+8)%COUNT_HASH_PRIME]; 
      key = (key + d->u.hrd.arc[ci].ub_denominator) 
      * HASH_PRIME[(3*ci+9)%COUNT_HASH_PRIME]; 
      key = (key + ((int) d->u.hrd.arc[ci].child)) 
      * HASH_PRIME[(3*ci+10)%COUNT_HASH_PRIME];
    }
    break; 
    
  case TYPE_HDD: 
    key = (key * HASH_PRIME[11] + ((int) d->u.hdd.hrd_exp)) * HASH_PRIME[12];
    for (ci = 0; ci < d->u.hdd.child_count; ci++) {
      key = (key + d->u.hdd.arc[ci].lb_numerator) 
      * HASH_PRIME[(5*ci+13)%COUNT_HASH_PRIME];   
      key = (key + d->u.hdd.arc[ci].lb_denominator) 
      * HASH_PRIME[(5*ci+14)%COUNT_HASH_PRIME];   
      key = (key + d->u.hdd.arc[ci].ub_numerator)
      * HASH_PRIME[(5*ci+15)%COUNT_HASH_PRIME];   
      key = (key + d->u.hdd.arc[ci].ub_denominator) 
      * HASH_PRIME[(5*ci+16)%COUNT_HASH_PRIME];   
      key = (key + ((int) d->u.hdd.arc[ci].child))
      * HASH_PRIME[(5*ci+17)%COUNT_HASH_PRIME]; 
    }
    break; 
    
  case TYPE_CDD: 
    key = key * HASH_PRIME[21]; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      key = (key + d->u.ddd.arc[ci].upper_bound) 
      * HASH_PRIME[(3*ci+22)%COUNT_HASH_PRIME];  
      key = (key + d->u.ddd.arc[ci].lower_bound) 
      * HASH_PRIME[(3*ci+23)%COUNT_HASH_PRIME];  
      key = (key + ((int) d->u.ddd.arc[ci].child))
      * HASH_PRIME[(3*ci+24)%COUNT_HASH_PRIME]; 
    }
    break; 

  case TYPE_LAZY_EXP:   
    key = key * HASH_PRIME[68]; 
    key = (key + ((int) d->u.lazy.false_child))*HASH_PRIME[69]; 
    key = (key + ((int) d->u.lazy.true_child))*HASH_PRIME[70]; 
    break; 

  case TYPE_FLOAT: 
    key = key * HASH_PRIME[69];  
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      vp = (int *) &(d->u.fdd.arc[ci].upper_bound);  
      key = (key + vp[0]) * HASH_PRIME[(3*ci+70)%COUNT_HASH_PRIME];  
      vp = (int *) &(d->u.fdd.arc[ci].lower_bound);  
      key = (key + vp[0]) * HASH_PRIME[(3*ci+71)%COUNT_HASH_PRIME];  

      key = (key + ((int) d->u.fdd.arc[ci].child))
      * HASH_PRIME[(3*ci+72)%COUNT_HASH_PRIME]; 
    }
    break; 

  case TYPE_DOUBLE: 
    key = key * HASH_PRIME[73];  
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      vp = (int *) &(d->u.dfdd.arc[ci].upper_bound);  
      key = (key + vp[0]) * HASH_PRIME[(5*ci+74)%COUNT_HASH_PRIME];  
      key = (key + vp[1]) * HASH_PRIME[(5*ci+75)%COUNT_HASH_PRIME];  

      vp = (int *) &(d->u.fdd.arc[ci].lower_bound);  
      key = (key + vp[0]) * HASH_PRIME[(5*ci+76)%COUNT_HASH_PRIME];  
      key = (key + vp[1]) * HASH_PRIME[(5*ci+77)%COUNT_HASH_PRIME];  

      key = (key + ((int) d->u.dfdd.arc[ci].child))
      * HASH_PRIME[(5*ci+78)%COUNT_HASH_PRIME]; 
    }
    break; 

  default: 
    key = key * HASH_PRIME[25];  
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      key = (key + d->u.ddd.arc[ci].upper_bound) 
      * HASH_PRIME[(3*ci+26)%COUNT_HASH_PRIME];  
      key = (key + d->u.ddd.arc[ci].lower_bound) 
      * HASH_PRIME[(3*ci+27)%COUNT_HASH_PRIME];  
      key = (key + ((int) d->u.ddd.arc[ci].child))
      * HASH_PRIME[(3*ci+28)%COUNT_HASH_PRIME]; 
    }
    break; 
  } 
  
  key = (key >> LEHGTH_SHIFT_SHARED_DIAGRAMS) & MASK_HASH_SHARED_DIAGRAMS;
  return(key); 
}
  /* hashkey_diagram() */ 
  
  
 

// Note that unless d is shared, we are not going update 
// the reference counts of its children and subexpressions. 
struct red_type	*red_share(d) 
	struct red_type	*d; 
{ 
  int				key, kk; 
  struct hash_red_link_type	*hs;
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  // First get the key.
//  ++count_red_share; 
//  for (; count_red_share == -1; ); 
  key = hashkey_diagram(d); 
//  fprintf(RED_OUT, "count_red_share = %1d, key in red_share = %1d:\n", 
//    count_red_share, key
//  ); 
//  red_print_graph(d); 
  // check if it is not used. 
  if (HASH_SHARE[key].count) { 
  // could be used. 
    for (hs = HASH_SHARE[key].shared_list; 
         hs; 
         hs = hs->next_hash_red_link
         ) { 
      if (!red_comp(hs->diagram, d))
      // It is used. 
        break; 
    } 
  }
  else {
  // not used!
    hs = NULL; // to signal it is not used. 
    COUNT_HASH_SHARE_USED_ENTRIES++; 
  }
  // If it is not used, then we should insert it to the shared list.   
  if (!hs) { 
    int	ci; 

    hs = (struct hash_red_link_type *) 
       malloc(sizeof(struct hash_red_link_type)); 
    hs->diagram = d; 
    hs->next_hash_red_link = HASH_SHARE[key].shared_list;
    HASH_SHARE[key].shared_list = hs; 
    HASH_SHARE[key].count++; 
    COUNT_HASH_SHARE_REGISTERED_DIAGRAMS++;

    // We need to update the lazy bit. 
    switch (VAR[d->var_index].TYPE) { 
    case TYPE_FALSE: 
    case TYPE_TRUE: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      break; 

    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
      d->status = d->status 
      | (  (d->u.bdd.one_child->status | d->u.bdd.zero_child->status) 
         & FLAG_RED_LAZY 
         ); 
      break; 

    case TYPE_LAZY_EXP: 
      d->status = d->status | FLAG_RED_LAZY; 
      break; 

    case TYPE_CRD: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) 
        d->status = d->status 
        | (d->u.crd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 
    case TYPE_HRD: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) 
        d->status = d->status 
        | (d->u.hrd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 
    
    case TYPE_HDD: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.hdd.child_count; ci++) 
        d->status = d->status 
        | (d->u.hdd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 

    case TYPE_FLOAT: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.fdd.child_count; ci++) 
        d->status = d->status 
        | (d->u.fdd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 

    case TYPE_DOUBLE: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.dfdd.child_count; ci++) 
        d->status = d->status 
        | (d->u.dfdd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 

    case TYPE_CDD: 
    default: 
      d->status = d->status & ~FLAG_RED_LAZY; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) 
        d->status = d->status 
        | (d->u.ddd.arc[ci].child->status & FLAG_RED_LAZY); 
      break; 
    } 
   
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
    return (d); 
  } 
  else { 
  // Otherwise, we should discard it.  
    switch (VAR[d->var_index].TYPE) { 
    case TYPE_FALSE: 
    case TYPE_TRUE: 
    case TYPE_BDD: 
    case TYPE_SYNCHRONIZER: 
    case TYPE_LAZY_EXP: 
      free(d); 
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 
    case TYPE_CRD: 
      free(d->u.crd.arc); 
      free(d); 
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(hs->diagram); 
      break; 
    case TYPE_HRD: 
      free(d->u.hrd.arc); 
      free(d); 
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 
    
    case TYPE_HDD: 
      free(d->u.hdd.arc); 
      free(d); 
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 

    case TYPE_FLOAT: 
/*
      fprintf(RED_OUT, "=======(red_share duplicate)==============\n"); 
      red_print_graph(d); 
*/
      free(d->u.fdd.arc); 
      free(d); 
/*
      fprintf(RED_OUT, "-------------------------\n"); 
      red_print_graph(hs->diagram); 
*/
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 
    case TYPE_DOUBLE: 
/*
      fprintf(RED_OUT, "=======(red_share duplicate)==============\n"); 
      red_print_graph(d); 
*/
      free(d->u.dfdd.arc); 
      free(d); 
/*
      fprintf(RED_OUT, "-------------------------\n"); 
      red_print_graph(hs->diagram); 
*/
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 
    case TYPE_CDD: 
    default: 
/*
      fprintf(RED_OUT, "=======(red_share duplicate)==============\n"); 
      red_print_graph(d); 
*/
      free(d->u.ddd.arc); 
      free(d); 
/*
      fprintf(RED_OUT, "-------------------------\n"); 
      red_print_graph(hs->diagram); 
*/
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return (hs->diagram); 
    } 
  } 
}
  /* red_share() */ 



// This is to assume that d has already been shared. 
//
void 	hash_red_delete(d) 
	struct red_type	*d; 
{ 
  int				key; 
  struct hash_red_link_type	*hs, *phs, dummy_head;
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  key = hashkey_diagram(d); 
  if (HASH_SHARE[key].count) { 
    dummy_head.next_hash_red_link = HASH_SHARE[key].shared_list; 
    for (phs = &dummy_head, hs = phs->next_hash_red_link; 
         hs; 
         phs = hs, hs = hs->next_hash_red_link
         ) { 
      if (hs->diagram == d) 
        break; 
    } 
    if (!hs) { 
      fprintf(RED_OUT, "Error, something wrong, an unshared node is to be unshared again. \n"); 
      exit(0); 	
    } 

    phs->next_hash_red_link = hs->next_hash_red_link;
    free(hs); 
    HASH_SHARE[key].shared_list = dummy_head.next_hash_red_link; 
    red_free(d);  
  }
  else {
    fprintf(RED_OUT, "Error, something wrong, an already-deleted node is to be deleted again. \n"); 
    exit(0); 
  }
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* hash_share_daigram_delete() */ 
  
  




/* Note that now red_free is implicit in red_deref_internal() and 
 * red_deref_external(). 
 */






  


 
/**********************************************************************
 *  The following procedures are for the caching of diagram manipulation. 
 */



struct cache1_hash_type		*HASH_CACHE1; 

struct cache2_hash_type		*HASH_CACHE2; 
struct cache4_hash_type		*HASH_CACHE4; 
struct cache7_hash_type		*HASH_CACHE7; 
struct cache10_hash_type	*HASH_CACHE10; 
struct cache13_hash_type	*HASH_CACHE13; 

inline int	cache1_hashkey(op, d) 
	int		op; 
	struct red_type	*d; 
{ 
  int	t; 
  
  t = (op*HASH_PRIME[1] + (int) d) * HASH_PRIME[2]; 
  return (t >> LENGTH_SHIFT_CACHE1) & MASK_HASH_CACHE1; 
} 
  /* cache1_hashkey() */ 

  
  
int	COUNT_HASH_CACHE1 = 0, 
	COUNT_HASH_CACHE2 = 0, 
	COUNT_HASH_CACHE4 = 0, 
	COUNT_HASH_CACHE7 = 0, 
	COUNT_HASH_CACHE10 = 0, 
	COUNT_HASH_CACHE13 = 0; 

int	count_query_cache1 = 1, 
	count_query_cache1_acc_length = 0; 
int	count_query_cache2 = 1, 
	count_query_cache2_acc_length = 0; 
int	count_query_cache4 = 1, 
	count_query_cache4_acc_length = 0; 
int	count_query_cache7 = 1, 
	count_query_cache7_acc_length = 0; 
int	count_query_cache10 = 1, 
	count_query_cache10_acc_length = 0; 
int	count_query_cache13 = 1, 
	count_query_cache13_acc_length = 0; 
  

extern int	count_tapairs; 

void 	fpca1() { 
  free(HASH_CACHE2[551715].cache->next_cache2_hash_entry->result); 	
}
  /* fpca1() */ 
  
   
 
void	ppca1() { 
  if (HASH_CACHE2[551715].cache) { 
    fprintf(RED_OUT, "HASH_CACHE2[551715].cache->op=%1d, d1=%x, d2=%x, result->var_index=%1d!\n", 
      HASH_CACHE2[551715].cache->op, 
      (unsigned int) HASH_CACHE2[551715].cache->d1, 
      (unsigned int) HASH_CACHE2[551715].cache->d2, 
      HASH_CACHE2[551715].cache->result->var_index
    ); 
    if (HASH_CACHE2[551715].cache->next_cache2_hash_entry) { 
      fprintf(RED_OUT, "HASH_CACHE1[551715].cache->next_cache2_hash_entry->op=%1d, d1=%x, d2=%x, result->var_index=%1d!\n", 
        HASH_CACHE2[551715].cache->next_cache2_hash_entry->op, 
        (unsigned int) HASH_CACHE2[551715].cache->next_cache2_hash_entry->d1, 
        (unsigned int) HASH_CACHE2[551715].cache->next_cache2_hash_entry->d2, 
        HASH_CACHE2[551715].cache->next_cache2_hash_entry->result->var_index 
      ); 
    }
    fflush(RED_OUT); 	
  } 
  else { 
    fprintf(RED_OUT, "HASH_CACHE2[551715] no cached entry yet!\n"); 
    fflush(RED_OUT); 	
  } 
}
  /* ppca1() */ 
  
  
 

struct cache1_hash_entry_type	
  *cache1_check_result_key(op, d) 
	int		op; // master time-stamp of the procedure
	struct red_type	*d; 
{
  int				key; 
  struct cache1_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 

  count_query_cache1++; 
/*
  fprintf(RED_OUT, "count_query_cache1=%1d\n", count_query_cache1); 
  print_cpu_time("In cache1 query"); 
*/
  key = cache1_hashkey(op, d); 
  pce = &dummy_ce; 
  dummy_ce.next_cache1_hash_entry = ce = HASH_CACHE1[key].cache; 
  for (count_query_cache1_acc_length++; ce; count_query_cache1_acc_length++) { 
    if (   ce->op < op 
        || (ce->op == op && ce->d < d) 
        ) { 
      pce = ce; 
      ce = ce->next_cache1_hash_entry;
    } 
    else if (ce->op == op && ce->d == d) {
/*
      print_cpu_time("exit cache1 query with cached result"); 
*/
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE1[key].count_entry_used++; 

  ce = (struct cache1_hash_entry_type *) 
    malloc(sizeof(struct cache1_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->result = NULL; 
  ce->next_cache1_hash_entry = pce->next_cache1_hash_entry; 
  pce->next_cache1_hash_entry = ce;
  
  COUNT_HASH_CACHE1++; 
  HASH_CACHE1[key].cache = dummy_ce.next_cache1_hash_entry; 
/*  
  print_cpu_time("exit cache1 query new"); 
*/
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache1_check_result_key() */ 


int	count_c1cl = 0; 

void	cache1_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache1_hash_entry_type	*ce, *pce, dummy_ce; 
  int				i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
    dummy_ce.next_cache1_hash_entry = HASH_CACHE1[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE1[i].cache; 
    for (; ce; ) {
/*
      fprintf(RED_OUT, "count_c1cl=%1d, i=%1d, oplb=%1d, opub=%1d, ce=%x, ce->op=%1d\n", 
        count_c1cl, i, oplb, opub, ce, ce->op
      ); 
      if (count_c1cl == -1) {
      	for(; count_c1cl; ); 
      } 
      count_c1cl++; 
*/
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache1_hash_entry = ce->next_cache1_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache1_hash_entry; 
      	HASH_CACHE1[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache1_hash_entry; 
      } 
    }
    HASH_CACHE1[i].cache = dummy_ce.next_cache1_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache1_clear() */  



  
  

/**********************************************************************
 * Cache function for 2 arguments. 
 */
inline int	cache2_hashkey(op, d1, d2) 
  int			op; 
  struct red_type	*d1, *d2; 
{ 
  int	t; 
  
  t = (op*HASH_PRIME[3] + (int) d1 ) * HASH_PRIME[4]; 
  t = (t + (int) d2) * HASH_PRIME[5]; 
  
  return ((t >> LEHGTH_SHIFT_CACHE2) & MASK_HASH_CACHE2); 
}
  /* cache2_hashkey() */ 
   


struct cache2_hash_entry_type	
  *cache2_check_result_key(op, d1, d2) 
	int		op; // master time-stamp of the procedure
	struct red_type	*d1, *d2; 
{
  int				key; 
  struct cache2_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 

  count_query_cache2++; 
  key = cache2_hashkey(op, d1, d2); 
  pce = &dummy_ce; 
  dummy_ce.next_cache2_hash_entry = ce = HASH_CACHE2[key].cache; 
  for (count_query_cache2_acc_length++; ce; count_query_cache2_acc_length++) { 
    if (   ce->op < op 
        || (   ce->op == op 
            && (   ce->d1 < d1 
                || (ce->d1 == d1 && ce->d2 < d2)
                ) 
            ) 
        ) { 
      pce = ce; 
      ce = ce->next_cache2_hash_entry;
    } 
    else if (ce->op == op && ce->d1 == d1 && ce->d2 == d2) {
/*
      fprintf(RED_OUT, "cache checking, already in at (%1d,%1d,%x,%x).\n", 
              key, j, ce, ce->result
              ); 
*/
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE2[key].count_entry_used++; 
  
  ce = (struct cache2_hash_entry_type *) 
    malloc(sizeof(struct cache2_hash_entry_type)); 
  #if RED_DEBUG_HASH_MODE 
  if (ce <= hashtar && ce+1 > hashtar) { 
    fprintf(RED_OUT, "hash target found %x\n", hash_target); 	
  } 
  #endif 
  
  ce->op = op; 
  ce->d1 = d1; 
  ce->d2 = d2; 
  ce->result = NULL; 
  ce->next_cache2_hash_entry = pce->next_cache2_hash_entry; 
  pce->next_cache2_hash_entry = ce;
  
  COUNT_HASH_CACHE2++; 
  HASH_CACHE2[key].cache = dummy_ce.next_cache2_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache2_check_result_key() */ 


struct cache2_hash_entry_type 
  *cache2_check_result_key_symmetric(op, d1, d2) 
	int		op; // master time-stamp of the procedure
	struct red_type	*d1, *d2; 
{
  int				key; 
  struct cache2_hash_entry_type	dummy_ce, *pce, *ce; 
  struct red_type		*t; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
  count_query_cache2++; 
  if (d1 > d2) {
    t = d1; d1 = d2; d2 = t; 
  } 
  key = cache2_hashkey(op, d1, d2); 
//  key = proc_cache1_hashkey(d); 
  pce = &dummy_ce; 
  dummy_ce.next_cache2_hash_entry = ce = HASH_CACHE2[key].cache; 
  for (count_query_cache2_acc_length++; ce; count_query_cache2_acc_length++) { 
    if (   ce->op < op 
        || (   ce->op == op 
            && (   ce->d1 < d1 
                || (ce->d1 == d1 && ce->d2 < d2)
                ) 
            ) 
        ) { 
      pce = ce; 
      ce = ce->next_cache2_hash_entry;
    } 
    else if (ce->op == op && ce->d1 == d1 && ce->d2 == d2) {
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE2[key].count_entry_used++; 
  
  ce = (struct cache2_hash_entry_type *) 
    malloc(sizeof(struct cache2_hash_entry_type)); 
  ce->op = op; 
  ce->d1 = d1; 
  ce->d2 = d2; 
  ce->result = NULL; 
  ce->next_cache2_hash_entry = pce->next_cache2_hash_entry; 
  pce->next_cache2_hash_entry = ce;
  
  COUNT_HASH_CACHE2++; 
  HASH_CACHE2[key].cache = dummy_ce.next_cache2_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache2_check_result_key_symmetric() */ 





void	cache2_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache2_hash_entry_type	*ce, *pce, dummy_ce; 
  int				i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
    dummy_ce.next_cache2_hash_entry = HASH_CACHE2[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE2[i].cache; 
    for (; ce; ) 
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache2_hash_entry = ce->next_cache2_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache2_hash_entry; 
      	HASH_CACHE2[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache2_hash_entry; 
      } 
    HASH_CACHE2[i].cache = dummy_ce.next_cache2_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache2_clear() */  




/**********************************************************************
 * Cache function for 4 arguments. 
 */
inline int	cache4_hashkey(op, d, hr, bn, bd) 
	int			op; // master time-stamp of the procedure
	struct red_type		*d; 
	struct hrd_exp_type	*hr; 
	int			bn, bd;  
{
  int	t; 
  
  t = op * HASH_PRIME[3] + (int)d; 
  t = t * HASH_PRIME[4] + (int) hr;
  t = t * HASH_PRIME[5] + (int) bn; 
  t = t * HASH_PRIME[6] + (int) bd; 
  t = (t >> LEHGTH_SHIFT_CACHE4) & MASK_HASH_CACHE4;  

  return (t); 
}
  /* cache4_hashkey() */ 



inline	int	cache4_comp(ce, op, d, hr0, bn0, bd0) 
	struct cache4_hash_entry_type	*ce; 
	int				op, bn0, bd0; 
	struct red_type			*d; 
	struct hrd_exp_type		*hr0; 
{ 
  int	comp; 
  
  if (comp = (ce->op - op)) 
    return(comp); 
  else if (comp = ((int) ce->d) - ((int) d)) 
    return(comp); 
  else if (comp = ((int) ce->hr0) - ((int) hr0))  
    return(comp); 
  else if (comp = ce->bn0 - bn0) 
    return(comp); 
  else 
    return(ce->bd0 - bd0); 
}
  /* cache4_comp() */ 
  
  
  

struct cache4_hash_entry_type	
  *cache4_check_result_key(op, d, hr0, bn0, bd0) 
	int			op; // master time-stamp of the procedure
	struct red_type		*d; 
	struct hrd_exp_type	*hr0; 
	int			bn0, bd0;  
{
  int				key, comp; 
  struct cache4_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
  count_query_cache4++; 
  key = cache4_hashkey(op, d, hr0, bn0, bd0); 
/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_query_cache4=%1d, key=%1d", 
      count_query_cache4, key
    ); 
  } 
*/
  pce = &dummy_ce; 
  dummy_ce.next_cache4_hash_entry = ce = HASH_CACHE4[key].cache; 
  for (count_query_cache4_acc_length++; ce; count_query_cache4_acc_length++) { 
    comp = cache4_comp(ce, op, d, hr0, bn0, bd0); 
    if (comp < 0) { 
      pce = ce; 
      ce = ce->next_cache4_hash_entry;
    } 
    else if (comp == 0) {
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE4[key].count_entry_used++; 
  
  ce = (struct cache4_hash_entry_type *) 
    malloc(sizeof(struct cache4_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->hr0 = hr0; 
  ce->bn0 = bn0; 
  ce->bd0 = bd0; 
  ce->result = NULL; 
  ce->next_cache4_hash_entry = pce->next_cache4_hash_entry; 
  pce->next_cache4_hash_entry = ce;
  
  COUNT_HASH_CACHE4++; 
  HASH_CACHE4[key].cache = dummy_ce.next_cache4_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache4_check_result_key() */ 



	
struct cache4_hash_entry_type	
  *cache4_check_result_key_symmetric(op, d, hr0, bn0, bd0) 
	int			op; // master time-stamp of the procedure
	struct red_type		*d; 
	struct hrd_exp_type	*hr0; 
	int			bn0, bd0;  
{
  int				key, comp, t; 
  struct cache4_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
  count_query_cache4++; 
  if (   ((char *) d) > ((char *) hr0) 
      || (   ((char *) d) == ((char *) hr0)
          && bn0 > bd0
          ) 
      ) {
    t = (int)d; d = (struct red_type *)hr0; hr0 = (struct hrd_exp_type *)t;     
    t = bn0; bn0 = bd0; bd0 = t; 
  } 
  key = cache4_hashkey(op, d, hr0, bn0, bd0); 

  pce = &dummy_ce; 
  dummy_ce.next_cache4_hash_entry = ce = HASH_CACHE4[key].cache; 
  for (count_query_cache4_acc_length++; ce; count_query_cache4_acc_length++) { 
    comp = cache4_comp(ce, op, d, hr0, bn0, bd0); 
    if (comp < 0) { 
      pce = ce; 
      ce = ce->next_cache4_hash_entry;
    } 
    else if (comp == 0) {
//      update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE4[key].count_entry_used++; 
  
  ce = (struct cache4_hash_entry_type *) 
    malloc(sizeof(struct cache4_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->hr0 = hr0; 
  ce->bn0 = bn0; 
  ce->bd0 = bd0; 
  ce->result = NULL; 
  ce->next_cache4_hash_entry = pce->next_cache4_hash_entry; 
  pce->next_cache4_hash_entry = ce;
  
  COUNT_HASH_CACHE4++; 
  HASH_CACHE4[key].cache = dummy_ce.next_cache4_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache4_check_result_key_symmetric() */ 

	

void	cache4_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache4_hash_entry_type	*ce, *pce, dummy_ce; 
  int				i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE4; i++) { 
    dummy_ce.next_cache4_hash_entry = HASH_CACHE4[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE4[i].cache; 
    for (; ce; ) 
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache4_hash_entry = ce->next_cache4_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache4_hash_entry; 
      	HASH_CACHE4[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache4_hash_entry; 
      } 
    HASH_CACHE4[i].cache = dummy_ce.next_cache4_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache4_clear() */  




/**********************************************************************
 * Cache function for 7 arguments. 
 */
inline int	cache7_hashkey(op, d, hr0, bn0, bd0, hr1, bn1, bd1) 
	int			op; // master time-stamp of the procedure
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1; 
	int			bn0, bd0, bn1, bd1;  
{
  int	t; 
  
  t = op * HASH_PRIME[3] + (int)d; 
  t = t * HASH_PRIME[4] + (int) hr0;
  t = t * HASH_PRIME[5] + (int) bn0; 
  t = t * HASH_PRIME[6] + (int) bd0; 
  t = t * HASH_PRIME[7] + (int) hr1;
  t = t * HASH_PRIME[8] + (int) bn1; 
  t = t * HASH_PRIME[9] + (int) bd1; 
  t = (t >> LEHGTH_SHIFT_CACHE7) & MASK_HASH_CACHE7;  

  return (t); 
}
  /* cache7_hashkey() */ 



inline	int	cache7_comp(ce, op, d, hr0, bn0, bd0, hr1, bn1, bd1) 
	struct cache7_hash_entry_type	*ce; 
	int				op, bn0, bd0, bn1, bd1; 
	struct red_type			*d; 
	struct hrd_exp_type		*hr0, *hr1; 
{ 
  int	comp; 
  
  if (comp = (ce->op - op)) 
    return(comp); 
  else if (comp = ((int) ce->d) - ((int) d)) 
    return(comp); 
  else if (comp = ((int) ce->hr0) - ((int) hr0))  
    return(comp); 
  else if (comp = ce->bn0 - bn0) 
    return(comp); 
  else if (comp = ce->bd0 - bd0) 
    return(comp); 
  else if (comp = ((int) ce->hr1) - ((int) hr1))  
    return(comp); 
  else if (comp = ce->bn1 - bn1) 
    return(comp); 
  else 
    return(ce->bd1 - bd1); 
}
  /* cache7_comp() */ 
  
  
  

struct cache7_hash_entry_type	
  *cache7_check_result_key(op, d, hr0, bn0, bd0, hr1, bn1, bd1) 
	int			op, bn0, bd0, bn1, bd1; 
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1; 
{
  int				key, comp; 
  struct cache7_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
/*
  count_query_cache7++;  
  fprintf(RED_OUT, "\ncache7_check %1d, op=%1d\n", count_query_cache7, op); 
  fprintf(RED_OUT, "d=%x\n", d); 
  fprintf(RED_OUT, "hr0=%x\n", hr0); 
  fprintf(RED_OUT, "bn0=%1d\n", bn0); 
  fprintf(RED_OUT, "bd0=%1d\n", bd0); 
  fprintf(RED_OUT, "hr1=%x\n", hr1); 
  fprintf(RED_OUT, "bn1=%1d\n", bn1); 
  fprintf(RED_OUT, "bd1=%1d\n", bd1); 
*/  
  key = cache7_hashkey(op, d, hr0, bn0, bd0, hr1, bn1, bd1); 

  pce = &dummy_ce; 
  dummy_ce.next_cache7_hash_entry = ce = HASH_CACHE7[key].cache; 
  for (count_query_cache7_acc_length++; ce; count_query_cache7_acc_length++) { 
    comp = cache7_comp(ce, op, d, hr0, bn0, bd0, hr1, bn1, bd1); 
    if (comp < 0) { 
      pce = ce; 
      ce = ce->next_cache7_hash_entry;
    } 
    else if (comp == 0) {
    //  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE7[key].count_entry_used++; 
  
  ce = (struct cache7_hash_entry_type *) 
    malloc(sizeof(struct cache7_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->hr0 = hr0; 
  ce->bn0 = bn0; 
  ce->bd0 = bd0; 
  ce->hr1 = hr1; 
  ce->bn1 = bn1; 
  ce->bd1 = bd1; 
  ce->result = NULL; 
  ce->next_cache7_hash_entry = pce->next_cache7_hash_entry; 
  pce->next_cache7_hash_entry = ce;
  
  COUNT_HASH_CACHE7++; 
  HASH_CACHE7[key].cache = dummy_ce.next_cache7_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache7_check_result_key() */ 

	

void	cache7_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache7_hash_entry_type	*ce, *pce, dummy_ce; 
  int				i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE7; i++) { 
    dummy_ce.next_cache7_hash_entry = HASH_CACHE7[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE7[i].cache; 
    for (; ce; ) 
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache7_hash_entry = ce->next_cache7_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache7_hash_entry; 
      	HASH_CACHE7[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache7_hash_entry; 
      } 
    HASH_CACHE7[i].cache = dummy_ce.next_cache7_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache7_clear() */  





/**********************************************************************
 * Cache function for 10 arguments. 
 */
inline int	cache10_hashkey(
  op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2
) 
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2;  
{
  int	t; 
  
  t = op * HASH_PRIME[3] + (int)d; 
  t = t * HASH_PRIME[4] + (int) hr0;
  t = t * HASH_PRIME[5] + (int) bn0; 
  t = t * HASH_PRIME[6] + (int) bd0; 
  t = t * HASH_PRIME[7] + (int) hr1;
  t = t * HASH_PRIME[8] + (int) bn1; 
  t = t * HASH_PRIME[9] + (int) bd1; 
  t = t * HASH_PRIME[10] + (int) hr2;
  t = t * HASH_PRIME[11] + (int) bn2; 
  t = t * HASH_PRIME[12] + (int) bd2; 
  t = (t >> LEHGTH_SHIFT_CACHE10) & MASK_HASH_CACHE10;  

  return (t); 
}
  /* cache10_hashkey() */ 



inline	int	cache10_comp(
  ce, 
  op, d, 
  hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2
) 
	struct cache10_hash_entry_type	*ce; 
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2;  
{ 
  int	comp; 
  
  if (comp = (ce->op - op)) 
    return(comp); 
  else if (comp = ((int) ce->d) - ((int) d)) 
    return(comp); 
  else if (comp = ((int) ce->hr0) - ((int) hr0))  
    return(comp); 
  else if (comp = ce->bn0 - bn0) 
    return(comp); 
  else if (comp = ce->bd0 - bd0) 
    return(comp); 
  else if (comp = ((int) ce->hr1) - ((int) hr1))  
    return(comp); 
  else if (comp = ce->bn1 - bn1) 
    return(comp); 
  else if (comp = ce->bd1 - bd1) 
    return(comp); 
  else if (comp = ((int) ce->hr2) - ((int) hr2))  
    return(comp); 
  else if (comp = ce->bn2 - bn2) 
    return(comp); 
  else 
    return(ce->bd2 - bd2); 
}
  /* cache10_comp() */ 
  
  
  

struct cache10_hash_entry_type	
  *cache10_check_result_key(
  op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2
)  
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2;  
{
  int					key, comp; 
  struct cache10_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
  count_query_cache10++; 
  key = cache10_hashkey(op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2); 

  pce = &dummy_ce; 
  dummy_ce.next_cache10_hash_entry = ce = HASH_CACHE10[key].cache; 
  for (count_query_cache10_acc_length++; ce; count_query_cache10_acc_length++) { 
    comp = cache10_comp(
      ce, op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2
    ); 
    if (comp < 0) { 
      pce = ce; 
      ce = ce->next_cache10_hash_entry;
    } 
    else if (comp == 0) {
    //  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE10[key].count_entry_used++; 
  
  ce = (struct cache10_hash_entry_type *) 
    malloc(sizeof(struct cache10_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->hr0 = hr0; 
  ce->bn0 = bn0; 
  ce->bd0 = bd0; 
  ce->hr1 = hr1; 
  ce->bn1 = bn1; 
  ce->bd1 = bd1; 
  ce->hr2 = hr2; 
  ce->bn2 = bn2; 
  ce->bd2 = bd2; 
  ce->result = NULL; 
  ce->next_cache10_hash_entry = pce->next_cache10_hash_entry; 
  pce->next_cache10_hash_entry = ce;
  
  COUNT_HASH_CACHE10++; 
  HASH_CACHE10[key].cache = dummy_ce.next_cache10_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache10_check_result_key() */ 

	


void	cache10_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache10_hash_entry_type	*ce, *pce, dummy_ce; 
  int				i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE10; i++) { 
    dummy_ce.next_cache10_hash_entry = HASH_CACHE10[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE10[i].cache; 
    for (; ce; ) 
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache10_hash_entry = ce->next_cache10_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache10_hash_entry; 
      	HASH_CACHE10[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache10_hash_entry; 
      } 
    HASH_CACHE10[i].cache = dummy_ce.next_cache10_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache10_clear() */  



/**********************************************************************
 * Cache function for 13 arguments. 
 */
inline int	cache13_hashkey(
  op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2, hr3, bn3, bd3
) 
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2, *hr3; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2, bn3, bd3;  
{
  int	t; 
  
  t = op * HASH_PRIME[3] + (int)d; 
  t = t * HASH_PRIME[4] + (int) hr0;
  t = t * HASH_PRIME[5] + (int) bn0; 
  t = t * HASH_PRIME[6] + (int) bd0; 
  t = t * HASH_PRIME[7] + (int) hr1;
  t = t * HASH_PRIME[8] + (int) bn1; 
  t = t * HASH_PRIME[9] + (int) bd1; 
  t = t * HASH_PRIME[10] + (int) hr2;
  t = t * HASH_PRIME[11] + (int) bn2; 
  t = t * HASH_PRIME[12] + (int) bd2; 
  t = t * HASH_PRIME[13] + (int) hr3;
  t = t * HASH_PRIME[14] + (int) bn3; 
  t = t * HASH_PRIME[15] + (int) bd3; 
  t = (t >> LEHGTH_SHIFT_CACHE13) & MASK_HASH_CACHE13;  

  return (t); 
}
  /* cache13_hashkey() */ 



inline	int	cache13_comp(
  ce, 
  op, d, 
  hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2, hr3, bn3, bd3
) 
	struct cache13_hash_entry_type	*ce; 
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2, *hr3; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2, bn3, bd3;  
{ 
  int	comp; 
  
  if (comp = (ce->op - op)) 
    return(comp); 
  else if (comp = ((int) ce->d) - ((int) d)) 
    return(comp); 
  else if (comp = ((int) ce->hr0) - ((int) hr0))  
    return(comp); 
  else if (comp = ce->bn0 - bn0) 
    return(comp); 
  else if (comp = ce->bd0 - bd0) 
    return(comp); 
  else if (comp = ((int) ce->hr1) - ((int) hr1))  
    return(comp); 
  else if (comp = ce->bn1 - bn1) 
    return(comp); 
  else if (comp = ce->bd1 - bd1) 
    return(comp); 
  else if (comp = ((int) ce->hr2) - ((int) hr2))  
    return(comp); 
  else if (comp = ce->bn2 - bn2) 
    return(comp); 
  else if (comp = ce->bd2 - bd2) 
    return(comp); 
  else if (comp = ((int) ce->hr3) - ((int) hr3))  
    return(comp); 
  else if (comp = ce->bn3 - bn3) 
    return(comp); 
  else 
    return(ce->bd3 - bd3); 
}
  /* cache13_comp() */ 
  
  
  

struct cache13_hash_entry_type	
  *cache13_check_result_key(
  op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2, hr3, bn3, bd3
)  
	struct red_type		*d; 
	struct hrd_exp_type	*hr0, *hr1, *hr2, *hr3; 
	int			op, bn0, bd0, bn1, bd1, bn2, bd2, bn3, bd3;  
{
  int					key, comp; 
  struct cache13_hash_entry_type	dummy_ce, *pce, *ce; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  if (op == -1) 
    bk(0); 
  count_query_cache13++; 
  key = cache13_hashkey(op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2); 

  pce = &dummy_ce; 
  dummy_ce.next_cache13_hash_entry = ce = HASH_CACHE13[key].cache; 
  for (count_query_cache13_acc_length++; ce; count_query_cache13_acc_length++) { 
    comp = cache13_comp(
      ce, op, d, hr0, bn0, bd0, hr1, bn1, bd1, hr2, bn2, bd2
    ); 
    if (comp < 0) { 
      pce = ce; 
      ce = ce->next_cache13_hash_entry;
    } 
    else if (comp == 0) {
    //  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
      return(ce); 
    }
    else 
      break; 
  } 
  HASH_CACHE13[key].count_entry_used++; 
  
  ce = (struct cache13_hash_entry_type *) 
    malloc(sizeof(struct cache13_hash_entry_type)); 
  ce->op = op; 
  ce->d = d; 
  ce->hr0 = hr0; 
  ce->bn0 = bn0; 
  ce->bd0 = bd0; 
  ce->hr1 = hr1; 
  ce->bn1 = bn1; 
  ce->bd1 = bd1; 
  ce->hr2 = hr2; 
  ce->bn2 = bn2; 
  ce->bd2 = bd2; 
  ce->hr3 = hr3; 
  ce->bn3 = bn3; 
  ce->bd3 = bd3; 
  ce->result = NULL; 
  ce->next_cache13_hash_entry = pce->next_cache13_hash_entry; 
  pce->next_cache13_hash_entry = ce;
  
  COUNT_HASH_CACHE13++; 
  HASH_CACHE13[key].cache = dummy_ce.next_cache13_hash_entry; 
  
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
  return(ce); 
}
  /* cache13_check_result_key() */ 

	

void	cache13_clear(oplb, opub) 
	int	oplb, opub; 
{ 
  struct cache13_hash_entry_type	*ce, *pce, dummy_ce; 
  int					i; 
  
//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  for (i = 0; i < SIZE_HASH_CACHE13; i++) { 
    dummy_ce.next_cache13_hash_entry = HASH_CACHE13[i].cache; 
    pce = &dummy_ce; 
    ce = HASH_CACHE13[i].cache; 
    for (; ce; ) 
      if (oplb <= ce->op && ce->op <= opub) { 
      	pce->next_cache13_hash_entry = ce->next_cache13_hash_entry; 
      	free(ce); 
      	ce = pce->next_cache13_hash_entry; 
      	HASH_CACHE13[i].count_entry_used--; 
      }
      else { 
      	pce = ce; 
      	ce = pce->next_cache13_hash_entry; 
      } 
    HASH_CACHE13[i].cache = dummy_ce.next_cache13_hash_entry; 
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
}
  /* cache13_clear() */  




/*********************************************************
 *  The following procedure are for the initialization of hashman. 
 */
void	thash() { 
  struct red_type	*t; 
  
  t = (struct red_type *) hash_target; 
  fprintf(RED_OUT, "printing target %x:\n", (unsigned int) t); 
  red_print_graph(t); 
}
  /* thash() */ 
  
  

struct cache2_hash_entry_type *hash_tmp; 

void	init_hash_management() { 
  int	i, j; 

//  reset_acc_time(FLAG_ACC_HASH_TIME);   
  hash_tmp = (struct cache2_hash_entry_type *) 
  malloc(sizeof(struct cache2_hash_entry_type)); 
  hashtar = (struct cache2_hash_entry_type *) 
  // hash_tmp; 
  hash_target  ; 
/*
  hashtar->u.crd.child_count = 0; 
*/  
  HASH_PRIME[0] = 12582917; 
  HASH_PRIME[1] = 4256249; 
  HASH_PRIME[2] = 741457; 
  HASH_PRIME[3] = 1618033999; 
  HASH_PRIME[4] = 2750159; 
  HASH_PRIME[5] = 32452867; 
  HASH_PRIME[6] = 35926307;     
  HASH_PRIME[7] = 67867979; 
  HASH_PRIME[8] = 71480051; 
  HASH_PRIME[9] = 2750161; 
  HASH_PRIME[10] = 5800079;     
  HASH_PRIME[11] = 35926309; 
  HASH_PRIME[12] = 39410867; 
  HASH_PRIME[13] = 71480063; 
  HASH_PRIME[14] = 75103493; 
  HASH_PRIME[15] = 5800139; 
  HASH_PRIME[16] = 8960453; 
  HASH_PRIME[17] = 39410869; 
  HASH_PRIME[18] = 42920191;
  HASH_PRIME[19] = 75103543; 
  HASH_PRIME[20] = 78736451; 
  HASH_PRIME[21] = 8960467; 
  HASH_PRIME[22] = 12195257; 
  HASH_PRIME[23] = 42920209; 
  HASH_PRIME[24] = 46441207; 
  HASH_PRIME[25] = 78736487; 
  HASH_PRIME[26] = 82376219; 
  HASH_PRIME[27] = 12195263; 
  HASH_PRIME[28] = 15485863; 
  HASH_PRIME[29] = 46441223; 
  HASH_PRIME[30] = 49979687; 
  HASH_PRIME[31] = 82376243; 
  HASH_PRIME[32] = 86028121; 
  HASH_PRIME[33] = 15485867; 
  HASH_PRIME[34] = 18815231;     
  HASH_PRIME[35] = 49979693; 
  HASH_PRIME[36] = 53533511;     
  HASH_PRIME[37] = 86028157; 
  HASH_PRIME[38] = 89687683; 
  HASH_PRIME[39] = 18815249;
  HASH_PRIME[40] = 22182343;  
  HASH_PRIME[41] = 53533523;
  HASH_PRIME[42] = 57099299;
  HASH_PRIME[43] = 89687693;
  HASH_PRIME[44] = 93354673; 
  HASH_PRIME[45] = 22182379; 
  HASH_PRIME[46] = 25582153; 
  HASH_PRIME[47] = 57099349; 
  HASH_PRIME[48] = 60678089; 
  HASH_PRIME[49] = 93354689; 
  HASH_PRIME[50] = 97026233; 
  HASH_PRIME[51] = 25582163; 
  HASH_PRIME[52] = 29005541; 
  HASH_PRIME[53] = 60678109; 
  HASH_PRIME[54] = 64268779; 
  HASH_PRIME[55] = 97026263; 
  HASH_PRIME[56] = 100711433; 
  HASH_PRIME[57] = 29005549; 
  HASH_PRIME[58] = 32452843; 
  HASH_PRIME[59] = 64268783; 
  HASH_PRIME[60] = 67867967; 

  HASH_PRIME[61] = 104395301; 
  HASH_PRIME[62] = 104395303;
  HASH_PRIME[63] = 122949823; 
  HASH_PRIME[64] = 122949829; 
  HASH_PRIME[65] = 141650939; 
  HASH_PRIME[66] = 141650963; 
  HASH_PRIME[67] = 160481183; 
  HASH_PRIME[68] = 160481219; 
  HASH_PRIME[69] = 179424673; 
  HASH_PRIME[70] = 179424691; 
  HASH_PRIME[71] = 198491317; 
  HASH_PRIME[72] = 198491329; 
  HASH_PRIME[73] = 217645177; 
  HASH_PRIME[74] = 217645199; 
  HASH_PRIME[75] = 236887691; 
  HASH_PRIME[76] = 236887699; 
  HASH_PRIME[77] = 256203161; 
  HASH_PRIME[78] = 256203221; 
  HASH_PRIME[79] = 275604541; 

  
  for (i = 0; i < SIZE_HASH_SHARED_HRD_EXPS; i++) { 
    HASH_SHARE_HRD_EXP[i].count = 0; 
    HASH_SHARE_HRD_EXP[i].hrd_exp_list = NULL; 
  }
  
  for (i = 0; i < SIZE_HASH_SHARED_DIAGRAMS; i++) { 
    HASH_SHARE[i].count = 0; 
    HASH_SHARE[i].shared_list = NULL; 
  } 
  
  HASH_CACHE1 = (struct cache1_hash_type *) 
    malloc(SIZE_HASH_CACHE1 * sizeof(struct cache1_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
    HASH_CACHE1[i].cache = NULL; 
    HASH_CACHE1[i].count_entry_used = 0; 	
  } 
  HASH_CACHE2 = (struct cache2_hash_type *) 
    malloc(SIZE_HASH_CACHE2 * sizeof(struct cache2_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
    HASH_CACHE2[i].cache = NULL; 	
    HASH_CACHE2[i].count_entry_used = 0; 	
  } 
  
  HASH_CACHE4 = (struct cache4_hash_type *) 
    malloc(SIZE_HASH_CACHE4 * sizeof(struct cache4_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE4; i++) { 
    HASH_CACHE4[i].cache = NULL; 
    HASH_CACHE4[i].count_entry_used = 0; 	
  } 
  HASH_CACHE7 = (struct cache7_hash_type *) 
    malloc(SIZE_HASH_CACHE7 * sizeof(struct cache7_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE7; i++) { 
    HASH_CACHE7[i].cache = NULL; 	
    HASH_CACHE7[i].count_entry_used = 0; 	
  } 
  
  HASH_CACHE10 = (struct cache10_hash_type *) 
    malloc(SIZE_HASH_CACHE10 * sizeof(struct cache10_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE10; i++) { 
    HASH_CACHE10[i].cache = NULL; 
    HASH_CACHE10[i].count_entry_used = 0; 	
  } 
  HASH_CACHE13 = (struct cache13_hash_type *) 
    malloc(SIZE_HASH_CACHE13 * sizeof(struct cache13_hash_type)); 
  for (i = 0; i < SIZE_HASH_CACHE13; i++) { 
    HASH_CACHE13[i].cache = NULL; 
    HASH_CACHE13[i].count_entry_used = 0; 	
  } 
//  update_acc_time(FLAG_ACC_HASH_TIME, FLAG_ACC_SILENT);    
} 
  /* init_hash_management() */ 
  





int	MASK_GC_SESSION; 

void	rec_check_mark(d)
     struct red_type	*d;
{
  int	ci;

  if (!(d->status & (MASK_GC_SESSION | FLAG_GC_STABLE) & MASK_GC)) {
    bk(0); 
    return; 
  }
  red_gc_mark_count++;
  d->status = d->status | MASK_GC_SESSION;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    rec_check_mark(d->u.bdd.zero_child); 
    rec_check_mark(d->u.bdd.one_child); 
    break; 
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_check_mark(d->u.crd.arc[ci].child);
    break;
  case TYPE_CDD:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_check_mark(d->u.ddd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_check_mark(d->u.hrd.arc[ci].child);
    break;
  case TYPE_HDD:
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      rec_check_mark(d->u.hdd.arc[ci].child);
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_check_mark(d->u.fdd.arc[ci].child);
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_check_mark(d->u.dfdd.arc[ci].child);
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_check_mark(d->u.ddd.arc[ci].child);
  }
}
/* rec_check_mark() */


int	count_check_mark = 0; 
void	check_mark(d, mask)
     struct red_type	*d;
     int		mask; 
{
  if (!d) 
    return; 
  ++count_check_mark; 
  if (count_check_mark == -1) {
    fprintf(RED_OUT, "\nTarget hit!\n"); 
    for (; count_check_mark == -1; ) ; 
  }
  MASK_GC_SESSION = mask; 
  rec_check_mark(d); 
}
  /* check_mark() */ 





void	rec_mark(d)
     struct red_type	*d;
{
  int	ci;

  if (   d == NULL 
      || (d->status & (FLAG_GC_STABLE | MASK_GC_SESSION))
      || d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return; 
    
  red_gc_mark_count++;
  d->status = d->status | MASK_GC_SESSION;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    rec_mark(d->u.bdd.zero_child); 
    rec_mark(d->u.bdd.one_child); 
    break; 
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_mark(d->u.crd.arc[ci].child);
    break;
  case TYPE_CDD:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_mark(d->u.ddd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_mark(d->u.hrd.arc[ci].child);
    break;
  case TYPE_HDD:
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      rec_mark(d->u.hdd.arc[ci].child);
    break;
  case TYPE_LAZY_EXP: 
    rec_ps_exp_mark(d->u.lazy.exp); 
    rec_mark(d->u.lazy.false_child); 
    rec_mark(d->u.lazy.true_child); 
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_mark(d->u.fdd.arc[ci].child);
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_mark(d->u.dfdd.arc[ci].child);
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_mark(d->u.ddd.arc[ci].child);
  }
}
/* rec_mark() */



void	red_mark(d, mask)
     struct red_type	*d;
     int		mask; 
{
  int	old_mask; 
  
  old_mask = MASK_GC_SESSION; 
  MASK_GC_SESSION = mask; 
  rec_mark(d); 
  MASK_GC_SESSION = old_mask; 
}
  /* red_mark() */ 



rec_ps_exp_mark(psub)
     struct ps_exp_type	*psub;
{
  int				lvi, rvi, lci, i;
  struct ps_bunit_type		*pbu;
  struct ps_exp_type		*newsub;
  struct red_type		*childred;
  struct ps_fairness_link_type	*fl;
/*
  fprintf(RED_OUT, "entering rec_ps_exp_mark() for type %1d\n", psub->type); 
  pcform(psub); 
*/

  switch(psub->type) {
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_CONSTANT :
    return; 
    
  case TYPE_DISCRETE: 
  case TYPE_CLOCK: 
  case TYPE_POINTER: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_BDD: 
    rec_ps_exp_mark(psub->u.atom.exp_base_proc_index); 
    return; 
    
  case IMPLY :
  case FORALL : 
  case EXISTS : 
    fprintf(RED_OUT, "\nBug: This types should already have been eliminated.\n"); 
    bk(); 
    
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    rec_ps_exp_mark(psub->u.exp); 
    break; 

  case EQ : 
  case NEQ : 
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    rec_ps_exp_mark(psub->u.ineq.offset); 
    for (i = 0; i < psub->u.ineq.term_count; i++) {
      rec_ps_exp_mark(psub->u.ineq.term[i].coeff); 
      rec_ps_exp_mark(psub->u.ineq.term[i].operand); 
    }
    break; 
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
    rec_ps_exp_mark(psub->u.arith.lhs_exp);
    rec_ps_exp_mark(psub->u.arith.rhs_exp);
    return; 
    
  case ARITH_CONDITIONAL: 
    rec_ps_exp_mark(psub->u.arith_cond.cond);
    rec_ps_exp_mark(psub->u.arith_cond.if_exp);
    rec_ps_exp_mark(psub->u.arith_cond.else_exp);
    break; 
    
  case TYPE_INLINE_CALL: 
    rec_ps_exp_mark(psub->u.inline_call.instantiated_exp);
    break; 
    
  case AND :
  case OR :
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) {
      rec_ps_exp_mark(pbu->subexp); 
    }
    break; 
  case NOT : 
    rec_ps_exp_mark(psub->u.bexp.blist->subexp); 
    break; 
  case RESET: 
    rec_ps_exp_mark(psub->u.reset.child);
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
    rec_ps_exp_mark(psub->u.mexp.dest_child); 
    rec_ps_exp_mark(psub->u.mexp.path_child); 
    if (psub->u.mexp.event_restriction) 
      rec_ps_exp_mark(psub->u.mexp.event_restriction); 
    rec_ps_exp_mark(psub->u.mexp.time_restriction); 
    if (psub->u.mexp.strong_fairness_count) 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_ps_exp_mark(fl->fairness); 
        red_mark(fl->red_fairness, FLAG_GC_STABLE);
      }
    if (psub->u.mexp.weak_fairness_count) 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_ps_exp_mark(fl->fairness); 
        red_mark(fl->red_fairness, FLAG_GC_STABLE); 
      }
    break; 

  case TYPE_GAME_SIM: 
    if (psub->u.mexp.strong_fairness_count) 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_ps_exp_mark(fl->fairness); 
        red_mark(fl->red_fairness, FLAG_GC_STABLE);
      }
    if (psub->u.mexp.weak_fairness_count) 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      	rec_ps_exp_mark(fl->fairness); 
        red_mark(fl->red_fairness, FLAG_GC_STABLE); 
      }
    break; 

  case LINEAR_EVENT: 
    rec_ps_exp_mark(psub->u.eexp.precond_exp); 
    rec_ps_exp_mark(psub->u.eexp.postcond_exp); 
    if (psub->u.eexp.event_exp) 
      rec_ps_exp_mark(psub->u.eexp.event_exp); 
    red_mark(psub->u.eexp.red_sync_bulk_from_event_exp); 
    red_mark(psub->u.eexp.red_game_sync_bulk_from_event_exp); 
    red_mark(psub->u.eexp.red_precond); 
    red_mark(psub->u.eexp.red_postcond); 
    break; 
  case RED: 
    red_mark(psub->u.rpred.red, FLAG_GC_STABLE); 
    if (psub->u.rpred.red != psub->u.rpred.original_red) {
      red_mark(psub->u.rpred.original_red, FLAG_GC_STABLE); 
    }     
    break; 


  default:
    fprintf(RED_OUT, 
      "\nError 7: unrecognized condition operator %1d in rec_ps_exp_mark().\n", 
      psub->type
    );
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n"); 
    bk(); 
  }
}
/* rec_ps_exp_mark() */ 



void	ps_exp_mark(
  struct ps_exp_type	*psub, 
  int			mask
) {
  int	old_mask; 
  
  old_mask = MASK_GC_SESSION; 
  rec_ps_exp_mark(psub); 
  MASK_GC_SESSION = old_mask; 
}
  /* ps_exp_mark() */




void	rec_unmark(d)
     struct red_type	*d;
{
  int	ci;

  if (   d == NULL  
      || (!(d->status & MASK_GC_SESSION)) 
      || d == NORM_NO_RESTRICTION
      || d == NORM_FALSE 
      )
    return; 
    
  red_gc_mark_count++;
  d->status = d->status & ~MASK_GC_SESSION;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    rec_unmark(d->u.bdd.zero_child); 
    rec_unmark(d->u.bdd.one_child); 
    break; 
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_unmark(d->u.crd.arc[ci].child);
    break;
  case TYPE_CDD:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_unmark(d->u.ddd.arc[ci].child);
    break;
  case TYPE_HRD:
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_unmark(d->u.hrd.arc[ci].child);
    break;
  case TYPE_HDD:
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      rec_unmark(d->u.hdd.arc[ci].child);
    break;
  case TYPE_LAZY_EXP: 
    rec_unmark(d->u.lazy.false_child); 
    rec_unmark(d->u.lazy.true_child); 
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_unmark(d->u.fdd.arc[ci].child);
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_unmark(d->u.dfdd.arc[ci].child);
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_unmark(d->u.ddd.arc[ci].child);
  }
}
/* rec_unmark() */



void	red_unmark(d, mask)
     struct red_type	*d;
     int		mask; 
{
  MASK_GC_SESSION = mask; 
  rec_unmark(d); 
}
  /* red_unmark() */ 






int	count_unmark_all = 0; 

void	red_unmark_all(mask) 
	int	mask; 
{ 
  int				i; 
  struct hash_red_link_type	*hrl; 
  
  for (i = 0; i < SIZE_HASH_SHARED_DIAGRAMS; i++) { 
    for (hrl = HASH_SHARE[i].shared_list; 
         hrl; 
         hrl = hrl->next_hash_red_link
         ) { 
/*
      fprintf(RED_OUT, "count_unmark_all = %1d\n", ++count_unmark_all); 
      if (count_unmark_all == 146) 
        bk(0); 
*/
      hrl->diagram->status = hrl->diagram->status & ~mask;
    } 
  } 
}
  /* red_unmark_all() */  


inline int	cache1_active(
  struct cache1_hash_entry_type	*c1 
) {   
  switch (c1->op) { 
// fxp.c 
  case OP_GET_PROCESS_FIRABLE_XTIONS: 
  case OP_GET_ALL_FIRABLE_XTIONS: 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_LOOKAHEAD_COLLECTIVE: 
  case OP_COLLECT_PROOF_OBLIGATIONS: 
  case OP_HYBRID_COLLECT_ALL_PRIMED: 
// redbop.c 
  case OP_QUERY_SIZE: 
  case OP_SIZE_SPACE: 
  case OP_ORDER_CHECK: 
  case OP_MODE_ZERO_DISTANCE: 
  case OP_CHECK_ABNORMAL_XTION_INSTANCE: 
  case OP_VOLUME_CDD: 
  case OP_TRIGGER_XTION_COUNT: 
  case OP_PATH_COUNT: 
  case OP_DISCRETE_MODEL_COUNT: 
// redparse.c
  case OP_SPEC_PROCESS: 
  case OP_PARTY_COUNT:  
  case OP_EVENT_PATH_EVALUATE: 
  case OP_BIG_TIMING_CONSTANT_IN_CRD: 
// zone.c 
  case OP_INVARIANCE_DISCONTINUITY: 
  /* when only d1 is of red_type. 
   * That is, the result is not of red_type. 
   */ 
    return(c1->d->status & MASK_GC); 
    break; 

// access_analysis.c, 
  case OP_DSCR_SPEC_WRITE_SYNCHRONIZATIONS:
// bisim.c, 
  case OP_GAME_ELIMINATE_GLOBAL_WRITE:
// fxp.c, 
  case OP_ELIMINATE_ALL_QFD_SYNC:
  case OP_EXTRACT_NO_UPPERBOUND:
// hybrid.c
  case OP_HYBRID_ELIMINATE_RELATIVE:
  case OP_HYBRID_ELIMINATE_SIMPLE_NEGATIVE_CYCLES: 
  case OP_HYBRID_CONSTANT_REPLACE: 
  case OP_HYBRID_RELATIVE_ELIMINATE:
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_LOOKAHEAD: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_CHECK_LONG: 
  case OP_HYBRID_EXTRACT_LONG: 
  case OP_HYBRID_PROOF_OBLIGATION: 
  case OP_HYBRID_ABSTRACT_PRECISION: 
  case OP_HYBRID_ABSTRACT_MAGNITUDE: 
  case OP_HYBRID_PARAMETER_EXTRACT: 
  case OP_HYBRID_REMOVE_ALL_DISCRETES: 
// inactive.c 
  case OP_ACTIVE_VARIABLE_GLOBAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_CLOCK_SUPPORT_EXTRACT: 
  case OP_ACTIVE_GLOBAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_UNTIMED_EXTRACT: 
// mtred.c
  case OP_MT_ABS: 
  case OP_MT_ABSTRACT: 
// redbop.c
  case OP_UNTIMED_SUBTRACT: 
  case OP_COMPLEMENT: 
  case OP_ZONE_COMPLEMENT:
  case OP_SUPER_INTERSECT_UNTIMED: 
  case OP_SWITCH_PRIMED_AND_UMPRIMED: 
  case OP_LIFT_ALL_UMPRIMED: 
  case OP_LOWER_ALL_PRIMED: 
  case OP_LOCAL_ELIMINATE: 
  case OP_SYNC_PLACE_ELIMINATE:
  case OP_QSYNC_ELIMINATE:
  case OP_PI_ELIMINATE:
  case OP_ALL_TRIGGER:
  case OP_TIME_ELIMINATE:
  case OP_NONMODAL_CLOCK_ELIMINATE:
  case OP_DIAGONAL_ELIMINATE:
  case OP_CDD:
  case OP_BOTTOM_ORDERING: 
  case OP_BACK_TO_ORIGINAL_ORDERING: 
  case OP_ELIMINATE_MAGNITUDE:
// redparse.c
  case OP_IDENTIFY_UNIQUE_ZONE:
  case OP_ADD_NECESSARY_LOWERBOUND: 
  case OP_ADD_SYNC_PROC_HOLDERS: 
  case OP_REMOVE_INTRIGGERABLE_SYNC_XTIONS: 
  case OP_ELIMINATE_SIMPLE_QFD_SYNC: 
// zapprox.c
  case OP_HULL_FILTER: 
  case OP_ONE_CONVEX_HULL: 
// zone.c
  case OP_PATH_ELIMINATE: 
  case OP_CLOCK_UPPER_EXTEND: 
  case OP_CLOCK_UPPER_DELTAP: 
  case OP_CLOCK_LOWER_EXTEND: 
  case OP_CLOCK_LOWER_DELTAP: 
  case OP_CLOCK_NOXTIVE_LOWER_EXTEND: 
  case OP_ELIMINATE_SIMPLE_NEGATIVE_CYCLES: 
  case OP_TIGHT_MAGNITUDES_DOWNWARD_THROUGH_MAGNITUDES: 
  case OP_TIGHT_DIFFERENCES_DOWNWRAD_THROUGH_MAGNITUDES: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDES_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUDANCY_DOWNWARD: 
  case OP_SUBSUME: 
  case OP_ZONE_SUBSUME: 
  case OP_CHECK_DISCONTINUITY_LOW_PRECISION: 
  case OP_CHECK_TIME_DISCONTINUITY: 
  case OP_DISCRETE_STACK_EXTRACT: 
  case OP_REDUCE_EQ:  
  case OP_MERGE_ZONES: 

  case OP_TIME_PATH_ASSUMED_CONVEXITY_ALL:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_SPEC:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_MODL:  

  case OP_TIME_PATH_FULL_FORMULATION_ALL:   
  case OP_TIME_PATH_FULL_FORMULATION_SPEC:   
  case OP_TIME_PATH_FULL_FORMULATION_MODL:   
/*
  case OP_TIME_PATH_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_SHARED_CONCAVITY_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_MODL: 
/*
  case OP_TIME_PATH_SPLIT_CONVEXITIES_ALL:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_SPEC:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_MODL:  

  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_MODL: 
/*
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
/*
  case OP_TIME_PATH_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_EASY_CONCAVITY_MODL:  

  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_MODL:  
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_MODL:  
//  when both d1 and result are of red_type. 
    return(
       (c1->d->status & MASK_GC) 
    && (   c1->result == NULL // This means that the result is still in computation.
        || (c1->result->status & MASK_GC)
    )   ); 
    break; 
  default: 
    fprintf(RED_OUT, "unexpected op %1d in cache1_active()\n", c1->op); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}
  /* cache1_active() */  
  
  
void	cache1_hash_entry_mark(c1) 
	struct cache1_hash_entry_type	*c1; 
{   
  switch (c1->op) { 
// fxp.c 
  case OP_GET_PROCESS_FIRABLE_XTIONS: 
  case OP_GET_ALL_FIRABLE_XTIONS: 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_2REDUNDANCY_LOOKAHEAD_COLLECTIVE: 
  case OP_COLLECT_PROOF_OBLIGATIONS: 
  case OP_HYBRID_COLLECT_ALL_PRIMED: 
// redbop.c 
  case OP_QUERY_SIZE: 
  case OP_SIZE_SPACE: 
  case OP_ORDER_CHECK: 
  case OP_MODE_ZERO_DISTANCE: 
  case OP_CHECK_ABNORMAL_XTION_INSTANCE: 
  case OP_VOLUME_CDD: 
  case OP_TRIGGER_XTION_COUNT: 
  case OP_PATH_COUNT: 
  case OP_DISCRETE_MODEL_COUNT: 
// redparse.c
  case OP_SPEC_PROCESS: 
  case OP_PARTY_COUNT:  
  case OP_EVENT_PATH_EVALUATE: 
  case OP_BIG_TIMING_CONSTANT_IN_CRD: 
// zone.c 
  case OP_INVARIANCE_DISCONTINUITY: 
  /* when only d1 is of red_type. 
   */ 
    red_mark(c1->d, FLAG_GC_USER_STACK); 
    break; 
// access_analysis.c, 
  case OP_DSCR_SPEC_WRITE_SYNCHRONIZATIONS:
// bisim.c, 
  case OP_GAME_ELIMINATE_GLOBAL_WRITE:
// fxp.c, 
  case OP_ELIMINATE_ALL_QFD_SYNC:
  case OP_EXTRACT_NO_UPPERBOUND:
// hybrid.c
  case OP_HYBRID_ELIMINATE_RELATIVE:
  case OP_HYBRID_ELIMINATE_SIMPLE_NEGATIVE_CYCLES:
  case OP_HYBRID_CONSTANT_REPLACE:
  case OP_HYBRID_RELATIVE_ELIMINATE:
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_DOWNWARD:
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_DOWNWARD:
  case OP_HYBRID_ELIMINATE_REDUNDANCY_DOWNWARD_FOR_PRIMED:
  case OP_HYBRID_ELIMINATE_REDUNDANCY_LOOKAHEAD:
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_FOR_PRIMED:
  case OP_HYBRID_CHECK_LONG: 
  case OP_HYBRID_EXTRACT_LONG: 
  case OP_HYBRID_PROOF_OBLIGATION: 
  case OP_HYBRID_ABSTRACT_PRECISION: 
  case OP_HYBRID_ABSTRACT_MAGNITUDE: 
  case OP_HYBRID_PARAMETER_EXTRACT: 
  case OP_HYBRID_REMOVE_ALL_DISCRETES: 
// inactive.c 
  case OP_ACTIVE_VARIABLE_GLOBAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_CLOCK_SUPPORT_EXTRACT: 
  case OP_ACTIVE_GLOBAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_UNTIMED_EXTRACT:
// mtred.c
  case OP_MT_ABS: 
  case OP_MT_ABSTRACT: 
// redbop.c
  case OP_UNTIMED_SUBTRACT:
  case OP_COMPLEMENT:
  case OP_ZONE_COMPLEMENT:
  case OP_SUPER_INTERSECT_UNTIMED:
  case OP_SWITCH_PRIMED_AND_UMPRIMED: 
  case OP_LIFT_ALL_UMPRIMED: 
  case OP_LOWER_ALL_PRIMED:
  case OP_LOCAL_ELIMINATE:
  case OP_SYNC_PLACE_ELIMINATE:
  case OP_QSYNC_ELIMINATE:
  case OP_PI_ELIMINATE:
  case OP_ALL_TRIGGER:
  case OP_TIME_ELIMINATE:
  case OP_NONMODAL_CLOCK_ELIMINATE:
  case OP_DIAGONAL_ELIMINATE:
  case OP_CDD:
  case OP_BOTTOM_ORDERING: 
  case OP_BACK_TO_ORIGINAL_ORDERING: 
  case OP_ELIMINATE_MAGNITUDE:
// redparse.c
  case OP_IDENTIFY_UNIQUE_ZONE:
  case OP_ADD_NECESSARY_LOWERBOUND: 
  case OP_ADD_SYNC_PROC_HOLDERS: 
  case OP_REMOVE_INTRIGGERABLE_SYNC_XTIONS: 
  case OP_ELIMINATE_SIMPLE_QFD_SYNC: 
// zapprox.c
  case OP_HULL_FILTER: 
  case OP_ONE_CONVEX_HULL: 
// zone.c
  case OP_PATH_ELIMINATE: 
  case OP_CLOCK_UPPER_EXTEND: 
  case OP_CLOCK_UPPER_DELTAP: 
  case OP_CLOCK_LOWER_EXTEND: 
  case OP_CLOCK_LOWER_DELTAP: 
  case OP_CLOCK_NOXTIVE_LOWER_EXTEND: 
  case OP_ELIMINATE_SIMPLE_NEGATIVE_CYCLES: 
  case OP_TIGHT_MAGNITUDES_DOWNWARD_THROUGH_MAGNITUDES: 
  case OP_TIGHT_DIFFERENCES_DOWNWRAD_THROUGH_MAGNITUDES: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDES_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUDANCY_DOWNWARD: 
  case OP_SUBSUME: 
  case OP_ZONE_SUBSUME: 
  case OP_CHECK_DISCONTINUITY_LOW_PRECISION: 
  case OP_CHECK_TIME_DISCONTINUITY: 
  case OP_DISCRETE_STACK_EXTRACT: 
  case OP_REDUCE_EQ:  
  case OP_MERGE_ZONES: 

  case OP_TIME_PATH_ASSUMED_CONVEXITY_ALL:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_SPEC:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_MODL:  

  case OP_TIME_PATH_FULL_FORMULATION_ALL:   
  case OP_TIME_PATH_FULL_FORMULATION_SPEC:   
  case OP_TIME_PATH_FULL_FORMULATION_MODL:   
/*
  case OP_TIME_PATH_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_SHARED_CONCAVITY_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_MODL: 

/*
  case OP_TIME_PATH_SPLIT_CONVEXITIES_ALL:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_SPEC:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_MODL:  

  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_MODL: 
/*
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
/*
  case OP_TIME_PATH_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_EASY_CONCAVITY_MODL:  

  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_MODL:  
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_MODL:  
// when both d1 and result are of red_type. 
    red_mark(c1->d, FLAG_GC_USER_STACK); 
    red_mark(c1->result, FLAG_GC_USER_STACK); 
    break; 

  default: 
    fprintf(RED_OUT, "unexpected operator %1d in cache1_hash_entry_mark()\n", 
      c1->op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}
  /* cache1_hash_entry_mark() */  
  
  
  
inline int	cache2_active( 
  struct cache2_hash_entry_type	*c2 
) {   
  switch (c2->op) { 
/* d=(op,d,d) */ 
// mtred.c
  case OP_MT_MULTIPLY: 
  case OP_MT_MATRIX_MULTIPLY_MATCH: 
// redbop.c
  case AND: 
  case OR: 
  case INTERSECT: 
  case EXCLUDE: 
  case SUBTRACT: 
  case EXTRACT: 
  case OP_ZONE_SUBTRACT: 
  case OP_SPACE_SUBTRACT: 
  case OP_SUPER_INTERSECT: 
  case OP_EXCLUDE_WITH_REDUCTION: 
// redparse.c 
  case OP_ADD_EVENT_COUNTS_FROM_XTIONS: 
// zapprox.c
  case OP_UNION_FILTER: 
// zone.c 
  case OP_ZONE_INTERSECT: 
  case OP_TIME_PROGRESS_ALL:
  case OP_TIME_PROGRESS_SPEC:
  case OP_TIME_PROGRESS_MODL:
  /* when d1, d2, and result are of red_type. 
   */ 
    return (
       (c2->d1->status & MASK_GC) 
    && (   c2->result == NULL // This means that the result is still in computation.
        || (   (c2->d2->status & MASK_GC) 
            && (c2->result->status & MASK_GC)
    )   )   ); 

/* void (op,d,d) */ 
// inactive.c
  case OP_CHECK_NOT_TYPE_III: 
// zapprox.c 
  case OP_ZONE_CONVEX_HULL: 
  /* when d1 and d2 are of red_type. 
   */ 
    return((c2->d1->status & MASK_GC) && (c2->d2->status & MASK_GC)); 

/* d=(op,d,i) */ 
// access_analysis.c 
  case OP_ELIMINATE_SINGLE_PARTY: 
// action.c 
  case OP_CHANGE_LHS_TO_VIVALUE: 
// bisim.c 
  case OP_ELIMINATE_ILLEGAL_DESCRIPTION_SPECIFICATION_READ_WRITES: 
  case OP_GAME_AUTO_PARTY: 
  case OP_GAME_ELIMINATE_ROLES: 
  case OP_GAME_EXTRACT_ROLE_UNBOUNDED:   
// fxp.c 
  case OP_ELIMINATE_PROC_QFD_SYNC: 
// hybrid.c 
  case OP_HYBRID_ADD_PRIMED_CONSTRAINTS: 
  case OP_HYBRID_ELIMINATE: 
  case OP_HYBRID_BYPASS_DOWNWARD: 
  case OP_HYBRID_BYPASS_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_GIVEN_PRIMED_REPLACE: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD: 
  case OP_HYBRID_DELTA_EXPRESSION_INACTIVE_CHANGE_BACK: 
// inactive.c
  case OP_ACTIVE_GLOBAL_LOCAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_VARIABLE_SUPPORT_EXTRACT: 
  case OP_ELIMINATE_PEERS:  
// redbasics.c
  case OP_ROLE_DEADLOCK: 
  case OP_ROLE_SIMPLE_ZENO: 
  case OP_CONJUNCT_ROLE_PRECONDITION: 
// redbop.c
  case OP_VARIABLE_ELIMINATE: 
  case OP_VARIABLE_SIM_ELIMINATE:
  case OP_TIME_CLOCK_SIM_ELIMINATE: 
  case OP_TYPE_ELIMINATE: 
  case OP_PROC_ELIMINATE: 
  case OP_PEER_ELIMINATE: 
  case OP_TIME_CLOCK_ELIMINATE: 
  case OP_TRIGGER_ABSTRACTION: 
  case OP_TIME_UPPERBOUNDED: 
  case OP_VAR_ABSENCE: 
  case OP_VAR_PRESENCE: 
  case OP_ROLE_TYPE_ELIMINATE: 
// redparse.c
  case OP_REPLACE_SYNC_PROC_HOLDERS: 

// redstream.c 
  case OP_HEAP_FREE: 
  
// redsymmetry.c
  case OP_ZONE_ONE_PAIR_REVERSE: 
  case OP_CLOCK_DEPENDENT: 
// zapprox.c 
  case OP_ABSTRACTION_GAME_BASED_INSIG: 
  case OP_ABSTRACTON_GAME_BASED_INSIG_DISCRETE: 
  case OP_ABSTRACTON_GAME_BASED_INSIG_TIME: 
  case OP_ABSTRACTION_GAME_BASED_INSIG_MAGNITUDE: 
  case OP_ABS_GAME: 
// zone.c 
  case OP_BYPASS_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_DOWNWARD: 
  case OP_TIME_PROGRESS_BY_AMOUNT: 
  case OP_LUB_EXTRAPOLATE: 
  case OP_LUB_EXTRAPOLATE_GIVEN_RIGHT: 
  case OP_REDUCE_EQ_REMOVE_CLOCK: 
// redgame.c
  case OP_ADD_ROLE_EVENTS: 
  case OP_INEQ_UNIVERSE_LONG_DEST_WITH_UAPPROX: 

  /* when d1 and result are of red_type. 
   */ 
    return(
       (c2->d1->status & MASK_GC) 
    && (   c2->result == NULL // This means that the result is still in computation.
        || (c2->result->status & MASK_GC)
    )   ); 

/* d=(op,i,i) */ 
// redgame.c
  case OP_ROLE_FAIRNESS_BCK: 

  /* when only result is of red_type. 
   */ 
    return(
       c2->result == NULL // This means that the result is still in computation.
    || (c2->result->status & MASK_GC)
    ); 
    break; 

/* i=(op,d,i) */ 
// bisim.c 
//  case OP_ROLE_IN_RED: 
// hybrid.c 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE: 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_DOWNWARD_COLLECTIVE: 
// inactive.c
//  case OP_TIMED_INVARIANCE_BOUNDS: 
//  case OP_VARIABLE_ACTIVE: 
// redbop.c
//  case OP_DETECT: 
//  case OP_VARIABLE_OCCURRENCE_CHECK: 
//  case OP_TRIGGER_TO_BE_ABSTRACTED: 
//  case OP_PATH_THRESHOLD: 
// exp.c 
//  case OP_VI_IN_EXP_POSSIBLY:
//  case OP_MCHUNK_IN_EXP: 
//  case OP_VI_SIM_IN_EXP:
//  case OP_CLOCK_SIM_IN_EXP:
//  case OP_TYPE_IN_EXP: 
//  case OP_TIME_IN_EXP: 
//  case OP_QSYNC_IN_EXP: 
//  case OP_CLOCK_IN_EXP: 
//  case OP_PEER_IN_EXP: 
//  case OP_LOCAL_IN_EXP: 
//  case OP_PROC_AND_GLOBAL_IN_EXP: 
  default: 
  /* when only d1 is of red_type. 
   */ 
    return(c2->d1->status & MASK_GC); 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache2_active()\n", 
//      c2->op
//    ); 
//    fflush(RED_OUT); 
//    exit(0); 
  } 
} 
  /* cache2_active() */  




void	cache2_hash_entry_mark(c2) 
	struct cache2_hash_entry_type	*c2; 
{   
  switch (c2->op) { 
// mtred.c
  case OP_MT_MULTIPLY: 
  case OP_MT_MATRIX_MULTIPLY_MATCH: 
// redbop.c
  case AND: 
  case OR: 
  case INTERSECT: 
  case EXCLUDE: 
  case SUBTRACT: 
  case EXTRACT: 
  case OP_ZONE_SUBTRACT: 
  case OP_SPACE_SUBTRACT: 
  case OP_SUPER_INTERSECT: 
  case OP_EXCLUDE_WITH_REDUCTION: 
// redparse.c 
  case OP_ADD_EVENT_COUNTS_FROM_XTIONS: 
// zapprox.c
  case OP_UNION_FILTER: 
// zone.c 
  case OP_ZONE_INTERSECT: 
  case OP_TIME_PROGRESS_ALL:
  case OP_TIME_PROGRESS_SPEC:
  case OP_TIME_PROGRESS_MODL:

  case OP_TIME_PATH_ASSUMED_CONVEXITY_ALL:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_SPEC:  
  case OP_TIME_PATH_ASSUMED_CONVEXITY_MODL:  

  case OP_TIME_PATH_FULL_FORMULATION_ALL:   
  case OP_TIME_PATH_FULL_FORMULATION_SPEC:   
  case OP_TIME_PATH_FULL_FORMULATION_MODL:   
/*
  case OP_TIME_PATH_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_SHARED_CONCAVITY_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_MODL: 
/*
  case OP_TIME_PATH_SPLIT_CONVEXITIES_ALL:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_SPEC:  
  case OP_TIME_PATH_SPLIT_CONVEXITIES_MODL:  
  
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_MODL: 
/*
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_ALL: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_SPEC: 
  case OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_MODL: 
*/
/* 
  case OP_TIME_PATH_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_EASY_CONCAVITY_MODL:  

  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_SHARED_EASY_CONCAVITY_MODL:  
*/
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_ALL:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_SPEC:  
  case OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_MODL:  
  /* when d1, d2, and result are of red_type. 
   */ 
    red_mark(c2->d1, FLAG_GC_USER_STACK); 
    red_mark(c2->d2, FLAG_GC_USER_STACK); 
    red_mark(c2->result, FLAG_GC_USER_STACK); 
    break; 

// inactive.c
  case OP_CHECK_NOT_TYPE_III: 
// zapprox.c 
  case OP_ZONE_CONVEX_HULL: 
  /* when d1 and d2 are of red_type. 
   */ 
    red_mark(c2->d1, FLAG_GC_USER_STACK); 
    red_mark(c2->d2, FLAG_GC_USER_STACK); 
    break; 
    
// access_analysis.c 
  case OP_ELIMINATE_SINGLE_PARTY: 
// action.c 
  case OP_CHANGE_LHS_TO_VIVALUE: 
// bisim.c 
  case OP_ELIMINATE_ILLEGAL_DESCRIPTION_SPECIFICATION_READ_WRITES: 
  case OP_GAME_AUTO_PARTY: 
  case OP_GAME_ELIMINATE_ROLES: 
  case OP_GAME_EXTRACT_ROLE_UNBOUNDED:   
// fxp.c 
  case OP_ELIMINATE_PROC_QFD_SYNC: 
// hybrid.c 
  case OP_HYBRID_ADD_PRIMED_CONSTRAINTS: 
  case OP_HYBRID_ELIMINATE: 
  case OP_HYBRID_BYPASS_DOWNWARD: 
  case OP_HYBRID_BYPASS_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_GIVEN_PRIMED_REPLACE: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD: 
  case OP_HYBRID_DELTA_EXPRESSION_INACTIVE_CHANGE_BACK: 
// inactive.c
  case OP_ACTIVE_GLOBAL_LOCAL_UNTIMED_EXTRACT: 
  case OP_ACTIVE_VARIABLE_SUPPORT_EXTRACT: 
  case OP_ELIMINATE_PEERS:  
// redbasics.c
  case OP_ROLE_DEADLOCK: 
  case OP_ROLE_SIMPLE_ZENO: 
  case OP_CONJUNCT_ROLE_PRECONDITION: 
// redbop.c
  case OP_VARIABLE_ELIMINATE: 
  case OP_VARIABLE_SIM_ELIMINATE:
  case OP_TIME_CLOCK_SIM_ELIMINATE: 
  case OP_TYPE_ELIMINATE: 
  case OP_PROC_ELIMINATE: 
  case OP_PEER_ELIMINATE: 
  case OP_TIME_CLOCK_ELIMINATE: 
  case OP_TRIGGER_ABSTRACTION: 
  case OP_TIME_UPPERBOUNDED: 
  case OP_VAR_ABSENCE: 
  case OP_VAR_PRESENCE: 
  case OP_ROLE_TYPE_ELIMINATE: 
// redparse.c
  case OP_REPLACE_SYNC_PROC_HOLDERS: 
// redstream.c 
  case OP_HEAP_FREE: 
  
// redsymmetry.c
  case OP_ZONE_ONE_PAIR_REVERSE: 
  case OP_CLOCK_DEPENDENT: 
// zapprox.c 
  case OP_ABSTRACTION_GAME_BASED_INSIG: 
  case OP_ABSTRACTON_GAME_BASED_INSIG_DISCRETE: 
  case OP_ABSTRACTON_GAME_BASED_INSIG_TIME: 
  case OP_ABSTRACTION_GAME_BASED_INSIG_MAGNITUDE: 
  case OP_ABS_GAME: 
// zone.c 
  case OP_BYPASS_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_DOWNWARD: 
  case OP_TIME_PROGRESS_BY_AMOUNT: 
  case OP_LUB_EXTRAPOLATE: 
  case OP_LUB_EXTRAPOLATE_GIVEN_RIGHT: 
  case OP_REDUCE_EQ_REMOVE_CLOCK: 
// redgame.c
  case OP_ADD_ROLE_EVENTS: 
  case OP_INEQ_UNIVERSE_LONG_DEST_WITH_UAPPROX: 
  /* when d1 and result are of red_type. 
   */ 
    red_mark(c2->d1, FLAG_GC_USER_STACK); 
    red_mark(c2->result, FLAG_GC_USER_STACK); 
    break; 

// redgame.c
  case OP_ROLE_FAIRNESS_BCK: 
  /* when only result is of red_type. 
   */ 
    red_mark(c2->result, FLAG_GC_USER_STACK); 
    break; 

// bisim.c 
//  case OP_ROLE_IN_RED: 
// hybrid.c 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE: 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_DOWNWARD_COLLECTIVE: 
// inactive.c
//  case OP_TIMED_INVARIANCE_BOUNDS: 
//  case OP_VARIABLE_ACTIVE: 
// redbop.c
//  case OP_DETECT: 
//  case OP_VARIABLE_OCCURRENCE_CHECK: 
//  case OP_TRIGGER_TO_BE_ABSTRACTED: 
//  case OP_PATH_THRESHOLD: 
// exp.c 
//  case OP_VI_IN_EXP_POSSIBLY:
//  case OP_MCHUNK_IN_EXP: 
//  case OP_VI_SIM_IN_EXP:
//  case OP_CLOCK_SIM_IN_EXP:
//  case OP_TYPE_IN_EXP: 
//  case OP_TIME_IN_EXP: 
//  case OP_QSYNC_IN_EXP: 
//  case OP_CLOCK_IN_EXP: 
//  case OP_PEER_IN_EXP: 
//  case OP_LOCAL_IN_EXP: 
//  case OP_PROC_AND_GLOBAL_IN_EXP: 
  default: 
  /* when only d1 is of red_type. 
   */ 
    red_mark(c2->d1, FLAG_GC_USER_STACK); 
    break; 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache2_hash_entry_mark()\n", 
//      c2->op
//    ); 
//    fflush(RED_OUT); 
//    exit(0); 
//
  }
}
  /* cache2_hash_entry_mark() */  
  
  
  
  
inline int	cache4_active(c) 
	struct cache4_hash_entry_type	*c; 
{   
  switch (c->op) { 
  // hybrid.c 
  case OP_HYBRID_DELTA_EXTEND: 
  case OP_HYBRID_DELTA_TRANSITIVITY_FOR_UMPRIMED_VARIABLES: 
  case OP_HYBRID_DELTA_EXPRESSION: 
  // mtred.c
  case OP_MT_ADD: 
  case OP_MT_MATRIX_MULTIPLY: 
  /* when d1, d2, and result are of red_type. 
   */ 
    return (
       (c->d->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (   (((struct red_type *) c->hr0)->status & MASK_GC) 
            && (c->result->status & MASK_GC)
    )   )   ); 

// access_analysis.c 
  case OP_FILTER_ROLE_WRITES: 
// action.c 
  case OP_TIME_CLOCK_MAGNITUDE_INC: 
  case OP_CLOCK_ASSIGN_BCK: 
  // bisim.c
  case OP_GAME_ROLE_NULLIFY:
  case OP_GAME_ELIMINATE_TYPE_ROLES: 
  case OP_ELIMINATE_ROLE_AND_SINGLE_PLANT:
  // hybrid.c
  case OP_HYBRID_EXTRACT_LOWERHALF: 
  case OP_HYBRID_EXTRACT_UPPERHALF: 
  case OP_HYBRID_SUBTRACT_UPPERHALF:
  case OP_HYBRID_SPECIFIC_CONSTANT_REPLACE: 
  case OP_HYBRID_REPLACE: 
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_LOOKAHEAD: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_EXTRACT_BOUND_REDUNDANCY_COLLECTIVE: 
  case OP_HYBRID_PROOF_OBLIGATION_GIVENX: 
  
  // mtred.c
  case OP_MT_THRESHOLD: 
  case OP_MT_APPLY_CONST: 
  case OP_MT_MATRIX_MULTIPLY_TAIL: 
  // redbop.c
  case OP_DDD_ONE_CONSTRAINT: 
  case OP_DDD_PROJECT_THROUGH_ONE_CONSTRAINT: 
  case OP_DDD_ONE_PROJECT_CONSTRAINT: 
  case OP_ASSIGN_INTERVAL: 
  case OP_ZONE_ASSIGN_BOUND: 
  case OP_HYBRID_ASSIGN_BOUND: 
  case OP_PI_TYPE_ELIMINATE: 
  case OP_TIME_CLOCK_ELIMINATE_REPLACE: 
  case OP_TIME_CLOCK_INC: 
  case OP_INC: 
  case OP_INC_MOD: 
  case OP_SWITCH_VI: 
  case OP_PI_PERMUTE: 
  
  // redstream.c 
  case OP_STREAM_INPUT_FROM_BUFFER:
  case OP_STREAM_OUTPUT_TO_BUFFER: 
  case OP_HEAP_MALLOC:  

  // redsymmetry.c
  case OP_SYMMETRY_POINTER_FIXPOINT_ONLINE_FANOUT_ONEPAIR: 
  // zone.c
  case OP_EXTRACT_INTERVAL: 
  case OP_SUBTRACT_INTERVAL: 
  case OP_BYPASS_DOWNWARD_MATCHING_LEFT: 
  case OP_BYPASS_DOWNWARD_MATCHING_RIGHT: 
  case OP_BYPASS_GIVEN_LEFT_DOWNWARD: 
  case OP_BYPASS_GIVEN_RIGHT_DOWNWARD: 
  case OP_TIGHT_MAGNITUDES_FROM_ZERO_DOWNWARD: 
  case OP_TIGHT_MAGNITUDES_TO_ZERO_DOWNWARD: 
  case OP_TIGHT_DIFFERENCES_FROM_ZERO_DOWNWARD: 
  case OP_TIGHT_DIFFERENCES_TO_ZERO_DOWNWARD: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_FROM_ZERO_DOWNWARD: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_TO_ZERO_DOWNWARD: 
  case OP_ELIMINATE_ONE_GROUP_MAGNITUDE_REDUNDANCY_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_RIGHT_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_LEFT_DOWNWARD: 
  case OP_PUSH_BIG_TIMING_CONSTANT: 
  
  // redgame.c
  case OP_GAME_FORCED_ONE_STRONG_FAIRNESS: 

    return(
       (c->d->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (c->result->status & MASK_GC)
    )   ); 

// access_analysis.c
//  case OP_REGISTER_RED_READ: 
// bisim.c 
//  case OP_COUNT_PATH_DEPTH: 
// hybrid.c
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE: 
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED:
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_LOOKAHEAD_COLLECTIVE:
// mtred.c
//  case OP_MT_MINMAX: 
// redparse.c
//  case OP_SYNC_PARTY_COUNT: 
  default: 
    return(c->d->status & MASK_GC); 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache4_active()\n", 
//      c->op
//    ); 
//    fflush(RED_OUT); 
//    exit(0); 
  }
}
  /* cache4_active() */  




void	cache4_hash_entry_mark(c) 
	struct cache4_hash_entry_type	*c; 
{   
  switch (c->op) { 
  // hybrid.c 
  case OP_HYBRID_DELTA_EXTEND: 
  case OP_HYBRID_DELTA_TRANSITIVITY_FOR_UMPRIMED_VARIABLES: 
  case OP_HYBRID_DELTA_EXPRESSION: 
  // mtred.c
  case OP_MT_ADD: 
  case OP_MT_MATRIX_MULTIPLY: 
  /* when d1, d2, and result are of red_type. 
   */ 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    red_mark((struct red_type *) c->hr0, FLAG_GC_USER_STACK); 
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 

/* d=(op,d,i,i,i) */ 
// access_analysis.c 
  case OP_FILTER_ROLE_WRITES: 
// action.c 
  case OP_TIME_CLOCK_MAGNITUDE_INC: 
  case OP_CLOCK_ASSIGN_BCK: 
  // bisim.c
  case OP_GAME_ROLE_NULLIFY:
  case OP_GAME_ELIMINATE_TYPE_ROLES: 
  case OP_ELIMINATE_ROLE_AND_SINGLE_PLANT:
  // hybrid.c
  case OP_HYBRID_EXTRACT_LOWERHALF: 
  case OP_HYBRID_EXTRACT_UPPERHALF: 
  case OP_HYBRID_SUBTRACT_UPPERHALF:
  case OP_HYBRID_SPECIFIC_CONSTANT_REPLACE: 
  case OP_HYBRID_REPLACE: 
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_LOOKAHEAD: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_EXTRACT_BOUND_REDUNDANCY_COLLECTIVE: 
  case OP_HYBRID_PROOF_OBLIGATION_GIVENX: 
  
  // mtred.c
  case OP_MT_THRESHOLD: 
  case OP_MT_APPLY_CONST: 
  case OP_MT_MATRIX_MULTIPLY_TAIL: 
  // redbop.c
  case OP_DDD_ONE_CONSTRAINT: 
  case OP_DDD_PROJECT_THROUGH_ONE_CONSTRAINT: 
  case OP_DDD_ONE_PROJECT_CONSTRAINT: 
  case OP_ASSIGN_INTERVAL: 
  case OP_ZONE_ASSIGN_BOUND: 
  case OP_HYBRID_ASSIGN_BOUND: 
  case OP_PI_TYPE_ELIMINATE: 
  case OP_TIME_CLOCK_ELIMINATE_REPLACE: 
  case OP_TIME_CLOCK_INC: 
  case OP_INC: 
  case OP_INC_MOD: 
  case OP_SWITCH_VI: 
  case OP_PI_PERMUTE: 
  
  // redstream.c 
  case OP_STREAM_INPUT_FROM_BUFFER:
  case OP_STREAM_OUTPUT_TO_BUFFER: 
  case OP_HEAP_MALLOC:  

  // redsymmetry.c
  case OP_SYMMETRY_POINTER_FIXPOINT_ONLINE_FANOUT_ONEPAIR: 
  // zone.c
  case OP_EXTRACT_INTERVAL: 
  case OP_SUBTRACT_INTERVAL: 
  case OP_BYPASS_DOWNWARD_MATCHING_LEFT: 
  case OP_BYPASS_DOWNWARD_MATCHING_RIGHT: 
  case OP_BYPASS_GIVEN_LEFT_DOWNWARD: 
  case OP_BYPASS_GIVEN_RIGHT_DOWNWARD: 
  case OP_TIGHT_MAGNITUDES_FROM_ZERO_DOWNWARD: 
  case OP_TIGHT_MAGNITUDES_TO_ZERO_DOWNWARD: 
  case OP_TIGHT_DIFFERENCES_FROM_ZERO_DOWNWARD: 
  case OP_TIGHT_DIFFERENCES_TO_ZERO_DOWNWARD: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_FROM_ZERO_DOWNWARD: 
  case OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_TO_ZERO_DOWNWARD: 
  case OP_ELIMINATE_ONE_GROUP_MAGNITUDE_REDUNDANCY_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_RIGHT_DOWNWARD: 
  case OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_LEFT_DOWNWARD: 
  case OP_PUSH_BIG_TIMING_CONSTANT: 
  // redgame.c
  case OP_GAME_FORCED_ONE_STRONG_FAIRNESS: 

    red_mark(c->d, FLAG_GC_USER_STACK); 
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 

// access_analysis.c
//  case OP_REGISTER_RED_READ: 
// bisim.c 
//  case OP_COUNT_PATH_DEPTH: 
// hybrid.c
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE: 
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED: 
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED:
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_LOOKAHEAD_COLLECTIVE:
// mtred.c
//  case OP_MT_MINMAX: 
// redparse.c
//  case OP_SYNC_PARTY_COUNT: 
  default: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    break; 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache4_hash_entry_mark()\n", 
//      c->op
//    ); 
//    fflush(RED_OUT); 
//    exit(0); 
  }
}
  /* cache4_hash_entry_mark() */  
  
  
  
  

  
  
  
inline int	cache7_active(
  struct cache7_hash_entry_type	*c  
) {   
  switch (c->op) { 
// action.c 
  case OP_EFFECT_SIMPLE: 
// hybrid.c 
  case OP_HYBRID_BYPASS_GIVEN_DOWNWARD: 
  case OP_HYBRID_BYPASS_GIVEN_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENXY_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXY_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXZ_LOOKAHEAD:
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD:
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_FOR_PRIMED:
  case OP_HDD_ONE_CONSTRAINT_ASCENDING:
// redbop.c
  case OP_ASSIGN_INTERVAL_DOUBLE: 
  case OP_DDD_ONE_CONSTRAINT_DOUBLE: 
    return(
       (c->d->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (c->result->status & MASK_GC)
    )   ); 
    
  // redgame.c
  case OP_INEQ_UNIVERSE_SYNC_ITERATIVE: 
    return(
       (c->d->status & MASK_GC) 
    && (((struct red_type *) c->hr0)->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (c->result->status & MASK_GC)
    )   ); 
  case OP_INEQ_UNIVERSE: 
    return(
       (c->d->status & MASK_GC) 
    && (((struct red_type *) c->hr0)->status & MASK_GC) 
    && (((struct red_type *) c->bn0)->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (c->result->status & MASK_GC)
    )   ); 
// hybrid.c
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE_FOR_PRIMED:
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXZ_LOOKAHEAD_COLLECTIVE:
  default: 
    return(c->d->status & MASK_GC); 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache7_active()\n", 
//      c->op
//     ); 
//    fflush(RED_OUT); 
//    exit(0); 
  }
}
  /* cache7_active() */  




 void	cache7_hash_entry_mark(c) 
	struct cache7_hash_entry_type	*c; 
{   
  switch (c->op) { 
// action.c 
  case OP_EFFECT_SIMPLE: 
// hybrid.c 
  case OP_HYBRID_BYPASS_GIVEN_DOWNWARD: 
  case OP_HYBRID_BYPASS_GIVEN_DOWNWARD_FOR_PRIMED: 
  case OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENXY_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXY_DOWNWARD: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXZ_LOOKAHEAD:
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD:
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_FOR_PRIMED:
  case OP_HDD_ONE_CONSTRAINT_ASCENDING:
// redbop.c
  case OP_ASSIGN_INTERVAL_DOUBLE: 
  case OP_DDD_ONE_CONSTRAINT_DOUBLE: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 
    
  // redgame.c
  case OP_INEQ_UNIVERSE_SYNC_ITERATIVE: 
    red_mark(c->d, FLAG_GC_USER_STACK);  
    red_mark((struct red_type *) c->hr0, FLAG_GC_USER_STACK);  
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 
  case OP_INEQ_UNIVERSE: 
    red_mark(c->d, FLAG_GC_USER_STACK);  
    red_mark((struct red_type *) c->hr0, FLAG_GC_USER_STACK);  
    red_mark((struct red_type *) c->bn0, FLAG_GC_USER_STACK);  
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 
    
// hybrid.c
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE_FOR_PRIMED:
//  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE:
//  case OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXZ_LOOKAHEAD_COLLECTIVE:
  default: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    break; 
//  default: 
//    fprintf(RED_OUT, "unexpected operator %1d in cache7_hash_entry_mark()\n", 
//      c->op
//    ); 
//    fflush(RED_OUT); 
//    exit(0); 
  }
}
  /* cache7_hash_entry_mark() */  
  
  
  
  

  
  
  
int	cache10_active(  
  struct cache10_hash_entry_type	*c
) {   
  switch (c->op) { 
// hybrid.c
  case OP_HYBRID_TIME_CROSS_GIVEN: 
  /* when d1, d2, and result are of red_type. 
   */ 
    return (
       (c->d->status & MASK_GC) 
    && (   c->result == NULL // This means that the result is still in computation.
        || (   (((struct red_type *) c->hr1)->status  & MASK_GC)
            && (c->result->status & MASK_GC)
    )   )   ); 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD: 
    return(c->result->status & MASK_GC); 
// exp.c 
  case OP_EXTRACT_VARIABLE_VALUES: 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE: 
    return(c->d->status & MASK_GC); 
  default: 
    fprintf(RED_OUT, "unexpected operator %1d in cache10_active()\n", 
      c->op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* cache10_active() */  




 void	cache10_hash_entry_mark(c) 
	struct cache10_hash_entry_type	*c; 
{   
  switch (c->op) { 
// hybrid.c 
  case OP_HYBRID_TIME_CROSS_GIVEN: 
  /* when d1, d2, and result are of red_type. 
   */ 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    red_mark((struct red_type *) c->hr1, FLAG_GC_USER_STACK); 
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    red_mark(c->result, FLAG_GC_USER_STACK); 
    break; 
// exp.c 
  case OP_EXTRACT_VARIABLE_VALUES: 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    break; 
  default: 
    fprintf(RED_OUT, "unexpected operator %1d in cache10_hash_entry_mark()\n", 
      c->op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* cache10_hash_entry_mark() */  
  
  
  
  

  
  
  
inline int	cache13_active(
  struct cache13_hash_entry_type	*c
) {   
  switch (c->op) { 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZU_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_TARGET_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_COLLECTIVE: 
    return(c->d->status & MASK_GC); 
  default: 
    fprintf(RED_OUT, "unexpected operator %1d in cache13_active()\n", 
      c->op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* cache13_active() */  




 void	cache13_hash_entry_mark(c) 
	struct cache13_hash_entry_type	*c; 
{   
  switch (c->op) { 
// hybrid.c 
  case OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZU_DOWNWARD_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_TARGET_COLLECTIVE: 
  case OP_HYBRID_ELIMINATE_REDUNDANCY_COLLECTIVE: 
    red_mark(c->d, FLAG_GC_USER_STACK); 
    break; 
  default: 
    fprintf(RED_OUT, "unexpected operator %1d in cache13_hash_entry_mark()\n", 
      c->op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
}
  /* cache13_hash_entry_mark() */  
  
  
  
struct token_protection_type
  *TOKEN_PROTECTION_LIST = NULL, 
  *USER_TOKEN_PROTECTION_LIST = NULL; 


int	get_a_new_gc_token(tplist_ptr) 
  struct token_protection_type	**tplist_ptr; 
{
  struct token_protection_type	*tp, dummy_tp, *ptp, *ntp; 

  dummy_tp.token = -1; 
  dummy_tp.next_token_protection = *tplist_ptr; 
  for (ptp = &dummy_tp, tp = *tplist_ptr; 
       tp && ptp->token + 1 == tp->token; 
       ptp = tp, tp = tp->next_token_protection
       ) ; 
  ntp = (struct token_protection_type *) 
    malloc(sizeof(struct token_protection_type)); 
  ntp->next_token_protection = tp; 
  ptp->next_token_protection = ntp; 
  *tplist_ptr = dummy_tp.next_token_protection; 
  
  ntp->token = ptp->token + 1; 
  ntp->protection_list = NULL; 
  
  return(ntp->token); 
}
  /* get_a_new_gc_token() */ 
  
  
void	release_gc_token(token, tplist_ptr) 
  int				token; 
  struct token_protection_type	**tplist_ptr; 
{ 
  struct token_protection_type	*tp, dummy_tp, *ptp; 
  
  dummy_tp.next_token_protection = *tplist_ptr; 
  for (ptp = &dummy_tp, tp = *tplist_ptr; 
       tp && tp->token < token; 
       ptp = tp, tp = tp->next_token_protection
       ); 
       
  if (tp && tp->token == token) {
    ptp->next_token_protection = tp->next_token_protection; 
    free_red_list(tp->protection_list); 
    free(tp); 
    tp = ptp->next_token_protection; 
    *tplist_ptr = dummy_tp.next_token_protection; 
  } 
} 
  /* release_gc_token() */  

  
  
void	protect_from_gc_with_token(d, token, tplist) 
  struct red_type		*d; 
  int				token; 
  struct token_protection_type	*tplist; 
{ 
  struct token_protection_type	*tp; 
  struct red_link_type		*rl; 
  
  for (tp = tplist; 
       tp && tp->token < token; 
       tp = tp->next_token_protection
       ) ; 
       
  if (tp && tp->token == token) { 
    rl = (struct red_link_type *) malloc(sizeof(struct red_link_type)); 
    rl->result = d; 
    rl->next_red_link = tp->protection_list; 
    tp->protection_list = rl; 
  } 
  else { 
    fprintf(RED_OUT, 
      "\nError: an unrecognized garbage collection token %1d.\n", 
      token
    );
    fflush(RED_OUT); 
    bk(0);  	
  } 
} 
  /* protect_from_gc_with_token() */ 
  
  
  
int	count_gc_hash = 0; 

// garbage_collect_from_red_alloc(flag_stage) 
garbage_collect(flag_stage) 
     int	flag_stage;
{
  int				i, cur_mem, tmp_flag, half, j;
  struct dfs_stack_type		*dfs; 
  struct hash_red_link_type	*hrl, *phrl, dummy_hrl; 
  struct token_protection_type	*tp; 
  
/*
  print_cpu_time("GC at RT_DYNAMIC=%d, RT_TOP=%d,", 
    RT_DYNAMIC, RT_TOP
  ); 
  fprintf(RED_OUT, 
    "count_query_cache1_acc_length/count_query_cache1=%1d/%1d\n", 
    count_query_cache1_acc_length, count_query_cache1
  ); 
  fprintf(RED_OUT, 
    "count_query_cache2_acc_length/count_query_cache2=%1d/%1d\n", 
    count_query_cache2_acc_length, count_query_cache2
  ); 
  fprintf(RED_OUT, 
    "count_query_cache4_acc_length/count_query_cache4=%1d/%1d\n", 
    count_query_cache4_acc_length, count_query_cache4
  ); 
  fprintf(RED_OUT, 
    "count_query_cache7_acc_length/count_query_cache7=%1d/%1d\n", 
    count_query_cache7_acc_length, count_query_cache7
  ); 
  fprintf(RED_OUT, 
    "count_query_cache10_acc_length/count_query_cache10=%1d/%1d\n", 
    count_query_cache10_acc_length, count_query_cache10
  ); 
  fprintf(RED_OUT, 
    "count_query_cache13_acc_length/count_query_cache13=%1d/%1d\n", 
    count_query_cache13_acc_length, count_query_cache13
  ); 
*/
  if (   count_query_cache1_acc_length/count_query_cache1 < 2
      && count_query_cache2_acc_length/count_query_cache2 < 2
      && count_query_cache4_acc_length/count_query_cache4 < 2
      && count_query_cache7_acc_length/count_query_cache7 < 2
      && count_query_cache10_acc_length/count_query_cache10 < 2
      && count_query_cache13_acc_length/count_query_cache13 < 2
      ) { 
/*
    fprintf(RED_OUT, " not necessary!\n"); 
*/
    return;  	
  } 
/*
  fprintf(RED_OUT, " started\n"); 
*/
  switch (flag_stage & MASK_GC_REPORT) { 
  case FLAG_GC_REPORT: 
    fprintf(RED_OUT, "====================================================================================\n");
    break; 
  }
  cur_mem = report_23tree_management(FLAG_GC_SILENT);
  cur_mem
    = cur_mem
    + GARBAGE_OVERHEAD
    + red_count*sizeof(struct red_type)
    + ichild_count*sizeof(struct ddd_child_type)
    + bchild_count*sizeof(struct crd_child_type)
    + rec_count*sizeof(struct rec_type) + drec_count * sizeof(struct double_rec_type);

  if (cur_mem > MAX_MEM)
    MAX_MEM = cur_mem;

  switch (flag_stage & MASK_GC_REPORT) { 
  case FLAG_GC_REPORT: 
    fprintf(RED_OUT, "Max memory used in bytes so far: %1d\n", MAX_MEM);
    fprintf(RED_OUT, "Current memory used in bytes so far: %1d\n", cur_mem);
    fprintf(RED_OUT, "Starting garbage collection at RT_TOP= %1d; red:%1d, ic:%1d, bc:%1d, rec:%1d, drec:%1d. \n",
	    RT_TOP, red_count, ichild_count, bchild_count, rec_count, drec_count
	    );
    break; 
  }

  red_gc_all_count = 0;
  red_gc_mark_count = 0;
  red_gc_unmarked_count = 0;

    /*
    if (op == GARBAGE_COUNTER_EXAMPLE)
      MASK_CLEAR = MASK_REACHABLE | MASK_XTION | MASK_COUNTER_PATH;
    else
    */
/*
  print_cpu_time("GC: before unmarking all RED."); 
*/
/*
  if (ITERATE_SXI == 49 && ITERATE_PI == 1 && ITERATE_XI == 6) { 
    fprintf(RED_OUT, "\nGC (sxi %1d,p%1d,x%1d), before unmarking all\n", 
      ITERATE_SXI, ITERATE_PI, ITERATE_XI
    ); 
    fflush(RED_OUT); 
  } 
*/
  red_unmark_all(
    FLAG_GC_SYSTEM_STACK 
  | FLAG_GC_USER_STACK 
  | FLAG_GC_WHILE_GFP 
  | FLAG_GC_TEMP
  ); 
/*
  print_cpu_time("GC: after unmarking all RED."); 
  process_23tree(red_tree, red_count_clear);

  for (i = 0; i < RT_DYNAMIC; i++) { 
    if (i >= INDEX_GAME_START && i <= INDEX_GAME_STOP) 
      check_mark(RT[i], FLAG_GC_BISIM); 
    else 
      check_mark(RT[i], FLAG_GC_STABLE); 
  } 

  print_cpu_time("after checking mark\n"); 
*/
/*
  if (ITERATE_SXI == 49 && ITERATE_PI == 1 && ITERATE_XI == 6) { 
    fprintf(RED_OUT, "\nGC (sxi %1d,p%1d,x%1d), before marking RT\n", 
      ITERATE_SXI, ITERATE_PI, ITERATE_XI
    ); 
    fflush(RED_OUT); 
  } 
*/
  for (i = RT_DYNAMIC; i < RT_TOP; i++) {
/*      
    fprintf(RED_OUT, "ec_g = %1d, gbg_c = %1d, red_mark(RT[i=%1d]=%1d)\n", 
	    count_ec_g, ++count_gbg_c, i, RT[i]
	    ); 
    red_print_graph(RT[i]); 
    fflush(RED_OUT); 
*/
    red_mark(RT[i], FLAG_GC_SYSTEM_STACK);
  }
    /*
    if (op == GARBAGE_COUNTER_EXAMPLE) {
      MASK_MARK = MASK_COUNTER_PATH;
      for (i = 0; i <= COUNTER_PATH_TOP; i++)
	red_mark(COUNTER_PATH[i]);
    }
    */
/*
  if (ITERATE_SXI == 49 && ITERATE_PI == 1 && ITERATE_XI == 6) { 
    fprintf(RED_OUT, "\nGC (sxi %1d,p%1d,x%1d), before marking TOKENS\n", 
      ITERATE_SXI, ITERATE_PI, ITERATE_XI
    ); 
    fflush(RED_OUT); 
  } 
*/
  for (tp = TOKEN_PROTECTION_LIST; tp; tp = tp->next_token_protection) { 
    struct red_link_type	*rl; 
    
    for (rl = tp->protection_list; rl; rl = rl->next_red_link) { 
      red_mark(rl->result, FLAG_GC_SYSTEM_STACK);
    } 	
  } 
/*
  if (ITERATE_SXI == 49 && ITERATE_PI == 1 && ITERATE_XI == 6) { 
    fprintf(RED_OUT, "\nGC (sxi %1d,p%1d,x%1d), before marking user Tokens\n", 
      ITERATE_SXI, ITERATE_PI, ITERATE_XI
    ); 
    fflush(RED_OUT); 
  } 
*/
  for (tp = USER_TOKEN_PROTECTION_LIST; tp; tp = tp->next_token_protection) { 
    struct red_link_type	*rl; 
    
    for (rl = tp->protection_list; rl; rl = rl->next_red_link) { 
      red_mark(rl->result, FLAG_GC_USER_STACK);
    } 	
  } 
/*
  print_cpu_time("GC: after marking all RTs."); 
  fprintf(RED_OUT, "RT from %1d to %1d\n", INDEX_BOTTOM_OF_RUNTIME_STACK, RT_TOP); 
*/
/*
  if (ITERATE_SXI == 49 && ITERATE_PI == 1 && ITERATE_XI == 6) { 
    fprintf(RED_OUT, "\nGC (sxi %1d,p%1d,x%1d), before marking DFS STACK\n", 
      ITERATE_SXI, ITERATE_PI, ITERATE_XI
    ); 
    fflush(RED_OUT); 
  } 
*/
  for (dfs = DFS_STACK_TOP; dfs; dfs = dfs->next_dfs_stack){
/*
    fprintf(RED_OUT, "%1d, ", i++); 
*/
    red_mark(dfs->sync_xtion_red, FLAG_GC_SYSTEM_STACK);
  }
/*
  print_cpu_time("GC: after marking the whole DFS_STACK."); 
*/ 
  for (i = 0; i < USER_TOP; i++) { 
    red_mark(RED_USER_STACK[i], FLAG_GC_USER_STACK); 	
  } 
/*
  print_cpu_time("GC: after marking the whole USER STACK."); 
  fprintf(RED_OUT, "USER STACK up to %1d\n", USER_TOP); 
*/
  /*
  if (op == GARBAGE_REPORT) {
    fprintf(RED_OUT, "\nwith mask reachable = %x; xtion = %x\n",
	    MASK_REACHABLE, MASK_XTION
	    );
    fflush(RED_OUT);
  }
  */ 
  if (count_query_cache1_acc_length/count_query_cache1 < 2) {
    struct cache1_hash_entry_type	*c; 
    for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
      for (c = HASH_CACHE1[i].cache; c; c = c->next_cache1_hash_entry) { 
        cache1_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache1_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache1 = 1; 
    count_query_cache1_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
      if (HASH_CACHE1[i].count_entry_used <= 2) {
        for (c = HASH_CACHE1[i].cache; c; c = c->next_cache1_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
          cache1_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE1[i].count_entry_used / 2; 
      dummy_c.next_cache1_hash_entry = HASH_CACHE1[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE1[i].cache, j = 1; c; j++) { 
        if (cache1_active(c) || half == j || j == 2*half) { 
          cache1_hash_entry_mark(c); 
	  pc->next_cache1_hash_entry = c; 
          c = c->next_cache1_hash_entry;
        }
        else { 
          pc->next_cache1_hash_entry = c->next_cache1_hash_entry; 
/*
          if (c->d == red_target || c->result == red_target) { 
            fprintf(RED_OUT, "hey, count_gc_hash=%1d, target unmarked at cache1\n", ++count_gc_hash); 
            fflush(RED_OUT); 	
          } 
*/
          free(c); 
          c = pc->next_cache1_hash_entry; 
          HASH_CACHE1[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE1[i].cache = dummy_c.next_cache1_hash_entry; 
    } 
  }
/*
  fprintf(RED_OUT, "garbage checking %1d cache2 entries.\n", SIZE_HASH_CACHE2); 
  fprintf(RED_OUT, "garbage checking i=%1d\n", 811398); 
  print_cpu_time("GC: after 1."); 
*/
  if (count_query_cache2_acc_length/count_query_cache2 < 2) {
    struct cache2_hash_entry_type	*c; 

    for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
      for (c = HASH_CACHE2[i].cache; c; c = c->next_cache2_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
        cache2_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache2_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache2 = 1; 
    count_query_cache2_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
      if (HASH_CACHE2[i].count_entry_used <= 2) { 
        for (c = HASH_CACHE2[i].cache; c; c = c->next_cache2_hash_entry) { 
      	  cache2_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE2[i].count_entry_used / 2; 
      dummy_c.next_cache2_hash_entry = HASH_CACHE2[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE2[i].cache, j = 1; c; j++) { 
      /* when d1, d2, and result are of red_type. 
       */ 
        if (cache2_active(c) || half == j || j == 2*half) { 
      	  cache2_hash_entry_mark(c); 
	  pc->next_cache2_hash_entry = c; 
          c = c->next_cache2_hash_entry;
        }
        else { 
          pc->next_cache2_hash_entry = c->next_cache2_hash_entry; 
/*
          if (   c->d1 == red_target 
              || c->d2 == red_target
              || c->result == red_target
              ) { 
            fprintf(RED_OUT, "hey, count_gc_hash=%1d, target unmarked at cache2\n", ++count_gc_hash); 
            fflush(RED_OUT); 	
          } 
*/
          free(c); 
          c = pc->next_cache2_hash_entry; 
          HASH_CACHE2[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE2[i].cache = dummy_c.next_cache2_hash_entry; 
    }
  } 
  if (count_query_cache4_acc_length/count_query_cache4 < 2) {
    struct cache4_hash_entry_type	*c; 

    for (i = 0; i < SIZE_HASH_CACHE4; i++) { 
      for (c = HASH_CACHE4[i].cache; c; c = c->next_cache4_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
        cache4_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache4_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache4 = 1; 
    count_query_cache4_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE4; i++) { 
      if (HASH_CACHE4[i].count_entry_used <= 2) { 
        for (c = HASH_CACHE4[i].cache; c; c = c->next_cache4_hash_entry) { 
      	  cache4_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE4[i].count_entry_used / 2; 
      dummy_c.next_cache4_hash_entry = HASH_CACHE4[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE4[i].cache, j = 1; c; j++) { 
      /* when d1, d2, and result are of red_type. 
       */ 
        if (cache4_active(c) || half == j || j == 2*half) { 
      	  cache4_hash_entry_mark(c); 
	  pc->next_cache4_hash_entry = c; 
          c = c->next_cache4_hash_entry;
        }
        else { 
          pc->next_cache4_hash_entry = c->next_cache4_hash_entry; 
/*
          if (   c->d == red_target 
              || ((struct red_type *) c->hr0)  == red_target
              || c->result == red_target
              ) { 
            fprintf(RED_OUT, "hey, count_gc_hash=%1d, target unmarked at cache4\n", ++count_gc_hash); 
            fflush(RED_OUT); 	
          } 
*/
          free(c); 
          c = pc->next_cache4_hash_entry; 
          HASH_CACHE4[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE4[i].cache = dummy_c.next_cache4_hash_entry; 
    }
  } 
  if (count_query_cache7_acc_length/count_query_cache7 < 2) {
    struct cache7_hash_entry_type	*c; 

    for (i = 0; i < SIZE_HASH_CACHE7; i++) { 
      for (c = HASH_CACHE7[i].cache; c; c = c->next_cache7_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
        cache7_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache7_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache7 = 1; 
    count_query_cache7_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE7; i++) { 
      if (HASH_CACHE7[i].count_entry_used <= 2) { 
        for (c = HASH_CACHE7[i].cache; c; c = c->next_cache7_hash_entry) { 
      	  cache7_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE7[i].count_entry_used / 2; 
      dummy_c.next_cache7_hash_entry = HASH_CACHE7[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE7[i].cache, j = 1; c; j++) { 
      /* when d1, d2, and result are of red_type. 
       */ 
        if (cache7_active(c) || half == j || j == 2*half) { 
      	  cache7_hash_entry_mark(c); 
	  pc->next_cache7_hash_entry = c; 
          c = c->next_cache7_hash_entry;
        }
        else { 
          pc->next_cache7_hash_entry = c->next_cache7_hash_entry; 
          free(c); 
          c = pc->next_cache7_hash_entry; 
          HASH_CACHE7[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE7[i].cache = dummy_c.next_cache7_hash_entry; 
    }
  } 
  if (count_query_cache10_acc_length/count_query_cache10 < 2) {
    struct cache10_hash_entry_type	*c; 

    for (i = 0; i < SIZE_HASH_CACHE10; i++) { 
      for (c = HASH_CACHE10[i].cache; c; c = c->next_cache10_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
        cache10_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache10_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache10 = 1; 
    count_query_cache10_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE10; i++) { 
      if (HASH_CACHE10[i].count_entry_used <= 2) { 
        for (c = HASH_CACHE10[i].cache; c; c = c->next_cache10_hash_entry) { 
      	  cache10_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE10[i].count_entry_used / 2; 
      dummy_c.next_cache10_hash_entry = HASH_CACHE10[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE10[i].cache, j = 1; c; j++) { 
      /* when d1, d2, and result are of red_type. 
       */ 
        if (cache10_active(c) || half == j || j == 2*half) { 
      	  cache10_hash_entry_mark(c); 
	  pc->next_cache10_hash_entry = c; 
          c = c->next_cache10_hash_entry;
        }
        else { 
          pc->next_cache10_hash_entry = c->next_cache10_hash_entry; 
          free(c); 
          c = pc->next_cache10_hash_entry; 
          HASH_CACHE10[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE10[i].cache = dummy_c.next_cache10_hash_entry; 
    }
  } 
  if (count_query_cache13_acc_length/count_query_cache13 < 2) {
    struct cache13_hash_entry_type	*c; 

    for (i = 0; i < SIZE_HASH_CACHE13; i++) { 
      for (c = HASH_CACHE13[i].cache; c; c = c->next_cache13_hash_entry) { 
/*
        fprintf(RED_OUT, "count_gc_hash=%1d, i=%1d\n", ++count_gc_hash, i); 
        for (; count_gc_hash == -1; ); 
*/
        cache13_hash_entry_mark(c); 
      } 
    }  
  }
  else { 
    struct cache13_hash_entry_type	*pc, *c, dummy_c; 

    count_query_cache13 = 1; 
    count_query_cache13_acc_length = 0; 
    for (i = 0; i < SIZE_HASH_CACHE13; i++) { 
      if (HASH_CACHE13[i].count_entry_used <= 2) { 
        for (c = HASH_CACHE13[i].cache; c; c = c->next_cache13_hash_entry) { 
      	  cache13_hash_entry_mark(c); 
        } 
        continue; 
      }  
      half = HASH_CACHE13[i].count_entry_used / 2; 
      dummy_c.next_cache13_hash_entry = HASH_CACHE13[i].cache; 
      pc = &dummy_c; 
      for (c = HASH_CACHE13[i].cache, j = 1; c; j++) { 
      /* when d1, d2, and result are of red_type. 
       */ 
        if (cache13_active(c) || half == j || j == 2*half) { 
      	  cache13_hash_entry_mark(c); 
	  pc->next_cache13_hash_entry = c; 
          c = c->next_cache13_hash_entry;
        }
        else { 
          pc->next_cache13_hash_entry = c->next_cache13_hash_entry; 
          free(c); 
          c = pc->next_cache13_hash_entry; 
          HASH_CACHE13[i].count_entry_used--; 
        }  
      } 
      HASH_CACHE13[i].cache = dummy_c.next_cache13_hash_entry; 
    }
  } 
  for (i = 0; i < SIZE_HASH_SHARED_DIAGRAMS; i++) { 
    dummy_hrl.next_hash_red_link = HASH_SHARE[i].shared_list; 
    phrl = & dummy_hrl; 
    for (j = 0, hrl = HASH_SHARE[i].shared_list; 
         hrl; 
         j++
         ) { 
      if (!(hrl->diagram->status)) { 
      	HASH_SHARE[i].count--; 
/*
      	fprintf(RED_OUT, 
      		"hash %1d(%1d): diagram %x with status %1x freed in garbage-collection.\n", 
      		i, j, hrl->diagram, hrl->diagram->status
      		); 
*/
/*
        if (hrl->diagram == red_target) { 
          int flag; 
          
          fprintf(RED_OUT, "target %x freed!\n", hrl->diagram); 
          fflush(RED_OUT); 
//          for (flag = 1; flag; ) ; 
        } 
*/
        
      	red_free(hrl->diagram); 
      	hrl = hrl->next_hash_red_link; 
      	free(phrl->next_hash_red_link); 
      	phrl->next_hash_red_link = hrl; 
      } 
      else { 
      	phrl = hrl; 
      	hrl = hrl->next_hash_red_link; 
      } 
    }
    HASH_SHARE[i].shared_list = dummy_hrl.next_hash_red_link; 
  }
/*
  print_cpu_time("GC: after garbage collecting the whole red tree."); 
*/
  cur_mem = report_23tree_management(FLAG_GC_SILENT);
  cur_mem
    = cur_mem
    + GARBAGE_OVERHEAD
    + red_count*sizeof(struct red_type)
    + ichild_count*sizeof(struct ddd_child_type)
    + bchild_count*sizeof(struct crd_child_type)
    + rec_count*sizeof(struct rec_type)
    + drec_count * sizeof(struct double_rec_type);
  switch (flag_stage & MASK_GC_REPORT) { 
  case FLAG_GC_REPORT: 
    /*    fprintf(RED_OUT, "\nEnd of garbage collection. gc_all=%1d, gc_mark=%1d, gc_unmark=%1d\n",
	    red_gc_all_count, red_gc_mark_count, red_gc_unmarked_count
	    );
    */
    fprintf(RED_OUT, "Total current memory used = %1d\n", cur_mem);
    fprintf(RED_OUT, "End of garbage collection red:%1d, ic:%1d, bc:%1d, rec:%1d, drec:%1d. \n",
	    red_count, ichild_count, bchild_count, rec_count, drec_count
	    );
    break; 
  }
}
  /* garbage_collector_from_red_alloc() */


garbage_collect_tmp(int flag_stage) {
// garbage_collect(int flag_stage) {
}
  /* garbage_collect() */ 

  
int	report_hash_management(flag_gc)
	int	flag_gc; 
{ 
  return(0); 
}
  /* report_hash_mansgement() */ 
  
  



void	print_hash_share() { 
  int				i, cur_mem, tmp_flag;
  struct hash_red_link_type	*hrl; 

  fprintf(RED_OUT, "\n==<HASH SHARE>==========================================\n"); 
  fprintf(RED_OUT, "%1d entries in HASH_SHARE table\n", 
	  SIZE_HASH_SHARED_DIAGRAMS
	  ); 
	  
  for (i = 0; i < SIZE_HASH_SHARED_DIAGRAMS; i++) { 
    hrl = HASH_SHARE[i].shared_list; 
    if (!hrl) { 
      continue; 
    }
    
    fprintf(RED_OUT, "[%1d]", i); 
    for (; hrl; hrl = hrl->next_hash_red_link) { 
      fprintf(RED_OUT, "-->%1d:%x", hrl->diagram->status, (unsigned int) hrl->diagram); 
    }
    fprintf(RED_OUT, "\n"); 
  }
}
  /* print_hash_share() */  




void	print_hash_share_diagrams() { 
  int				i, cur_mem, tmp_flag;
  struct hash_red_link_type	*hrl; 

  fprintf(RED_OUT, "\n==<HASH SHARE>==========================================\n"); 
  fprintf(RED_OUT, "%1d entries in HASH_SHARE table\n", 
	  SIZE_HASH_SHARED_DIAGRAMS
	  ); 
	  
  for (i = 0; i < SIZE_HASH_SHARED_DIAGRAMS; i++) { 
    hrl = HASH_SHARE[i].shared_list; 
    if (!hrl) { 
      continue; 
    }
    
    fprintf(RED_OUT, "[%1d]", i); 
    for (; hrl; hrl = hrl->next_hash_red_link) { 
      fprintf(RED_OUT, "-->%1d:%x", hrl->diagram->status, (unsigned int) hrl->diagram); 
    }
    fprintf(RED_OUT, "\n"); 
    for (hrl = HASH_SHARE[i].shared_list; 
         hrl; 
         hrl = hrl->next_hash_red_link
         ) { 
      fprintf(RED_OUT, "----{%1d:%x}-----------------------------\n", 
	      hrl->diagram->status, (unsigned int) hrl->diagram
	      );
      red_print_graph(hrl->diagram); 
    }
    fprintf(RED_OUT, "\n"); 
  }
}
  /* print_hash_share_diagrams() */  



#define	FLAG_PRINT_CACHE_TOP		-1

#define	FLAG_PRINT_CACHE_ALL		1
#define	FLAG_PRINT_CACHE_PRESENT	0

#define	FLAG_PRINT_CACHE_DIAGRAMS	1
#define	FLAG_PRINT_CACHE_SIMPLE		0

void	print_cache1(flag_print_cache_diagrams) 
	int	flag_print_cache_diagrams; 
{ 
  int				i, flag_head; 
  struct cache1_hash_entry_type	*ce; 
  
  fprintf(RED_OUT, "\n====[print_cache1]======================\n"); 
  
  switch (flag_print_cache_diagrams) { 
  case FLAG_PRINT_CACHE_SIMPLE: 
    for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
      flag_head = 1; 
      for (ce = HASH_CACHE1[i].cache; 
           ce; 
           ce = ce->next_cache1_hash_entry
      	   ) { 
     	if (flag_head) {
      	  fprintf(RED_OUT, "[%1d]", i);  
      	  flag_head = 0; 
      	} 
        fprintf(RED_OUT, "-->(%1d:%x:%x)", ce->op, (unsigned int) ce->d, (unsigned int) ce->result); 
      } 
      if (!flag_head)
        fprintf(RED_OUT, "\n");  
    }
    break; 
  case FLAG_PRINT_CACHE_DIAGRAMS: 
    for (i = 0; i < SIZE_HASH_CACHE1; i++) { 
      for (ce = HASH_CACHE1[i].cache, flag_head = 0; 
      	   ce; 
      	   ce = ce->next_cache1_hash_entry, flag_head++
      	   ) { 
        fprintf(RED_OUT, 
                "======[%1d:%1d.%1d.d]====================\n", 
                ce->op, i, flag_head
                ); 
        red_print_graph(ce->d);  
        fprintf(RED_OUT, 
                "------[%1d:%1d.%1d.result]---------------\n", 
                ce->op, i, flag_head
                ); 
        red_print_graph(ce->result); 
      } 
    }
    break; 
  } 
} 
  /* print_cache1() */ 


  
  
  
void	print_cache2(flag_print_cache_diagrams) 
	int	flag_print_cache_diagrams; 
{ 
  int				i, flag_head; 
  struct cache2_hash_entry_type	*ce; 
  
  fprintf(RED_OUT, "\n====[print_cache2]======================\n"); 
  
  switch (flag_print_cache_diagrams) { 
  case FLAG_PRINT_CACHE_SIMPLE: 
    for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
      flag_head = 1; 
      for (ce = HASH_CACHE2[i].cache; 
      	   ce; 
      	   ce = ce->next_cache2_hash_entry
      	   ) { 
        if (flag_head) {
      	  fprintf(RED_OUT, "[%1d]", i);  
      	  flag_head = 0; 
      	} 
        fprintf(RED_OUT, "-->(%1d:%x:%x:%x)", ce->op, (unsigned int) ce->d1, (unsigned int) ce->d2, (unsigned int) ce->result); 
      }
    } 
    if (!flag_head)
      fprintf(RED_OUT, "\n");  
    break; 
  case FLAG_PRINT_CACHE_DIAGRAMS: 
    for (i = 0; i < SIZE_HASH_CACHE2; i++) { 
      for (ce = HASH_CACHE2[i].cache, flag_head = 0; 
           ce; 
      	   ce = ce->next_cache2_hash_entry, flag_head++
      	   ) { 
        fprintf(RED_OUT, 
                "======[%1d:%1d.%1d.d1]====================\n", 
                ce->op, i, flag_head
                ); 
        red_print_graph(ce->d1);  
        fprintf(RED_OUT, 
                "------[%1d:%1d.%1d.d2]---------------\n", 
                ce->op, i, flag_head
                ); 
        red_print_graph(ce->d2);  
        fprintf(RED_OUT, 
                "------[%1d:%1d.%1d.result]---------------\n", 
                ce->op, i, flag_head
                ); 
        red_print_graph(ce->result); 
      } 
    }
    break; 
  } 
} 
  /* print_cache2() */ 

void	reset_hash_diagram_status() {
  int				key; 
  struct hash_red_link_type	*sdl; 
  
  for (key = 0; key < SIZE_HASH_SHARED_DIAGRAMS; key++) { 
    for (sdl = HASH_SHARE[key].shared_list; 
      sdl; 
      sdl = sdl->next_hash_red_link
    ) {
      sdl->diagram->status = sdl->diagram->status & FLAG_GC_USER_STACK; 
    } 
  } 
}
  /* reset_hash_diagram_status() */ 
  
  


void	release_all_hash_tables() {
  int				key; 
  struct hash_hrd_exp_link_type	*hs, *hs_tmp;
  struct hash_red_link_type	*sdl, *sdl_tmp; 

  for (key = 0; key < SIZE_HASH_SHARED_HRD_EXPS; key++) { 
    for (hs = HASH_SHARE_HRD_EXP[key].hrd_exp_list; 
      hs; 
      hs_tmp = hs, hs = hs->next_hash_hrd_exp_link, free(hs_tmp) 
    ) { 
      hrd_exp_free(hs->hrd_exp); 
    }
  } 

  /* free all caches of type 1. 
   */
  if (HASH_CACHE1) { 
    for (key = 0; key < SIZE_HASH_CACHE1; key++) { 
      struct cache1_hash_entry_type	*c1, *c1_tmp; 
    
      for (c1 = HASH_CACHE1[key].cache; 
        c1; 
        c1_tmp = c1, c1 = c1->next_cache1_hash_entry, free(c1_tmp)
      ) ; 
    } 
    free(HASH_CACHE1); 
    HASH_CACHE1 = NULL; 
  } 
  
  /* free all caches of type 2. 
   */
  if (HASH_CACHE2) { 
    for (key = 0; key < SIZE_HASH_CACHE2; key++) { 
      struct cache2_hash_entry_type	*c2, *c2_tmp; 
    
      for (c2 = HASH_CACHE2[key].cache; 
        c2; 
        c2_tmp = c2, c2 = c2->next_cache2_hash_entry, free(c2_tmp)
      ) ; 
    } 
    free(HASH_CACHE2); 
    HASH_CACHE2 = NULL; 
  }
  
  /* free all caches of type 4. 
   */
  if (HASH_CACHE4) { 
    for (key = 0; key < SIZE_HASH_CACHE4; key++) { 
      struct cache4_hash_entry_type	*c4, *c4_tmp; 
    
      for (c4 = HASH_CACHE4[key].cache; 
        c4; 
        c4_tmp = c4, c4 = c4->next_cache4_hash_entry, free(c4_tmp)
      ) ; 
    } 
    free(HASH_CACHE4); 
    HASH_CACHE4 = NULL; 
  }
  
  /* free all caches of type 7. 
   */
  if (HASH_CACHE7) { 
    for (key = 0; key < SIZE_HASH_CACHE7; key++) { 
      struct cache7_hash_entry_type	*c7, *c7_tmp; 
    
      for (c7 = HASH_CACHE7[key].cache; 
        c7; 
        c7_tmp = c7, c7 = c7->next_cache7_hash_entry, free(c7_tmp)
      ) ; 
    } 
    free(HASH_CACHE7); 
    HASH_CACHE7 = NULL; 
  } 
  
  /* free all caches of type 10. 
   */
  if (HASH_CACHE10) { 
    for (key = 0; key < SIZE_HASH_CACHE10; key++) { 
      struct cache10_hash_entry_type	*c10, *c10_tmp; 
    
      for (c10 = HASH_CACHE10[key].cache; 
        c10; 
        c10_tmp = c10, c10 = c10->next_cache10_hash_entry, free(c10_tmp)
      ) ; 
    } 
    free(HASH_CACHE10); 
    HASH_CACHE10 = NULL; 
  }
  
  /* free all caches of type 13. 
   */
  if (HASH_CACHE13) { 
    for (key = 0; key < SIZE_HASH_CACHE13; key++) { 
      struct cache13_hash_entry_type	*c13, *c13_tmp; 
    
      for (c13 = HASH_CACHE13[key].cache; 
        c13; 
        c13_tmp = c13, c13 = c13->next_cache13_hash_entry, free(c13_tmp)
      ) ; 
    } 
    free(HASH_CACHE13); 
    HASH_CACHE13 = NULL; 
  }

  for (key = 0; key < SIZE_HASH_SHARED_DIAGRAMS; key++) { 
    for (sdl = HASH_SHARE[key].shared_list; 
      sdl; 
      sdl_tmp = sdl, sdl = sdl->next_hash_red_link, free(sdl_tmp) 
    ) {
      switch (VAR[sdl->diagram->var_index].TYPE) { 
      case TYPE_CRD: 
        free(sdl->diagram->u.crd.arc); 
        break; 
      case TYPE_HRD: 
        free(sdl->diagram->u.hrd.arc); 
        break; 
      case TYPE_HDD: 
        free(sdl->diagram->u.hdd.arc); 
        break; 
      case TYPE_BDD: 
      case TYPE_SYNCHRONIZER: 
      case TYPE_FALSE: 
      case TYPE_TRUE: 
      case TYPE_LAZY_EXP: 
        break; 
      case TYPE_FLOAT: 
        free(sdl->diagram->u.fdd.arc); 
        break; 
      case TYPE_DOUBLE: 
        free(sdl->diagram->u.dfdd.arc); 
        break; 
      default: 
        free(sdl->diagram->u.ddd.arc); 
        break; 
      } 
      free(sdl->diagram); 
    } 
  } 
}
  /* release_all_hash_tables() */ 
  
  

  
void	test_hashman() { 
  int	v1, v2, v3, v4, d1, d2, d3, sc, gc; 
  
  sc = 0; gc = 0; 
  v1 = variable_index[TYPE_DISCRETE][0][0]; 
  v2 = variable_index[TYPE_DISCRETE][0][1]; 
  v3 = variable_index[TYPE_DISCRETE][0][3]; 
  v4 = variable_index[TYPE_DISCRETE][0][4]; 
  RT[d1 = RT_TOP++] = ddd_atom(v3, 0, 0); 
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 
  
  garbage_collect(FLAG_GC_SILENT); 
  gc++; 
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 

  RT[d2 = RT_TOP++] = ddd_one_constraint(RT[d1], v1, 0, 0); 
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 

  RT[d3 = RT_TOP++] = ddd_atom(v2, 1, 1); 
  RT[d3] = red_bop(AND, RT[d3], RT[d2]); 
  
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 
  
  garbage_collect(FLAG_GC_SILENT); 
  gc++; 
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 
  
  RT_TOP--; // d3 
  garbage_collect(FLAG_GC_SILENT); 
  gc++; 
  fprintf(RED_OUT, 
	  "\n>>>>>>testing hashman, step %1d: after the %1d GC\n", 
          ++sc, gc
          ); 
  print_hash_share_diagrams(); 
  
  exit(0); 
}
  /* test_hashman() */ 






