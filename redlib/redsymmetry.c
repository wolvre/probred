#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>



#include "redbasics.h"
#include "redbasics.e"

#include "vindex.e"

#include "redbop.h"
#include "redbop.e"

#include "zone.h"  
#include "zone.e"

#include "redparse.h"
#include "redparse.e"

#include "hashman.h" 
#include "hashman.e" 

#define	SYMMETRY_P1	1
#define	SYMMETRY_P2	2

struct red_type
  ***PROCESS_REVERSE, ***PROCESS_EQUAL,
  ***DSC_EQUAL, ***DSC_REVERSE,
  ***POINTER_LOCAL_FANOUT_EQUAL, ***POINTER_LOCAL_FANOUT_REVERSE,
  ***POINTER_LOCAL_FANIN_EQUAL, ***POINTER_LOCAL_FANIN_REVERSE,
  ***POINTER_GLOBAL_EQUAL, ***POINTER_GLOBAL_REVERSE;

int	SWITCH_PI, SWITCH_PJ;



struct red_type	*dsc_equal_basic(pi, pj) 
	int	pi, pj; 
{ 
  struct red_type	*result, *conj; 
  int			imi, mi, offset, vi, vj, value; 
  
  result = NORM_NO_RESTRICTION;
  for (offset = 0; offset < LOCAL_COUNT[TYPE_DISCRETE]; offset++) {
    vi = variable_index[TYPE_DISCRETE][pi][offset];
    if (VAR[vi].STATUS & FLAG_SYNC_PLACE) 
      continue; 
    vj = variable_index[TYPE_DISCRETE][pj][offset];
    conj = NORM_FALSE;
    for (value = VAR[vi].U.DISC.LB; value <= VAR[vi].U.DISC.UB; value++) {
      conj = red_bop(OR, conj, ddd_one_constraint(
        ddd_atom(vj, value, value), 
        vi, value, value
      ) ); 
    }
    result = red_bop(AND, conj, result); 
  }
  return(result); 
} 
  /* dsc_equal_basic() */ 
  
  

struct red_type	*dsc_reverse_basic(pi, pj) 
	int	pi, pj; 
{ 
  struct red_type	*result, *prev_equal, *conj; 
  int			imi, mi, offset, vi, vj, value; 
  
  result = NORM_FALSE;
  prev_equal = NORM_NO_RESTRICTION;
  for (offset = 0; offset < LOCAL_COUNT[TYPE_DISCRETE]; offset++) {
    vi = variable_index[TYPE_DISCRETE][pi][offset];
    if (VAR[vi].STATUS & FLAG_SYNC_PLACE) 
      continue; 
    vj = variable_index[TYPE_DISCRETE][pj][offset];

    conj = NORM_FALSE;
    for (value = VAR[vi].U.DISC.UB; value > VAR[vi].U.DISC.LB; value--) {
      conj = red_bop(OR, conj,
		     red_bop(AND, ddd_atom(vj, VAR[vi].U.DISC.LB, value-1),
			     ddd_atom(vi, value, value)
			     )
		     );
    }

    result = red_bop(OR, result, red_bop(AND, conj, prev_equal));

    conj = NORM_FALSE;
    for (value = VAR[vi].U.DISC.LB; value <= VAR[vi].U.DISC.UB; value++) {
      conj = red_bop(OR, conj,
		     red_bop(AND, ddd_atom(vj, value, value),
			     ddd_atom(vi, value, value)
			     )
		     );
    }

    prev_equal = red_bop(AND, conj, prev_equal);
  }
  return(result); 
}
  /* dsc_reverse_basic() */ 
  
  
  


/****************************************************************************
 *
 *  for option d
 *  Recursively called by red_clock_reverse() and red_discrete_clock_pointer()
 */


/* condition for the true root of pj in pi to PROCESS_COUNT
 * 1. vo[pj] all point to pi,.., INFINITY, for some vos.
 * 2. no pk, except pj, points to pj through local pointers
 */
struct red_type *red_true_root(pi, pj)
     int	pi, pj;
{
  struct red_type	*true_root, *equal, *conj;
  int			pk, vo, vi, vj, vh, vk;

  if (PROCESS[pi].group_process_index != PROCESS[pj].group_process_index) 
    return(NORM_FALSE); 
    
  true_root = NORM_FALSE;
  for (vo = 0; vo < LOCAL_COUNT[TYPE_POINTER]; vo++) {
    vi = variable_index[TYPE_POINTER][pj][vo]; 
    if (vi == FLAG_NO_USE || (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC)) 
      continue; 
    true_root = red_bop(OR, true_root, ddd_atom(vi, pi, PROCESS_COUNT));
  }
  for (pk = pi; pk <= PROCESS_COUNT; pk++) {
    if (pk != pj) {
      for (vo = 0; vo < LOCAL_COUNT[TYPE_POINTER]; vo++) {
	vk = variable_index[TYPE_POINTER][pk][vo]; 
	if (vk == FLAG_NO_USE || (VAR[vk].STATUS & FLAG_QUANTIFIED_SYNC)) 
	  continue; 
	true_root = red_bop(SUBTRACT, true_root, ddd_atom(vk, pj, pj));
      }
    }
  }

  equal = NORM_NO_RESTRICTION;
  for (vo = 0; vo < LOCAL_COUNT[TYPE_POINTER]; vo++) {
    conj = NORM_FALSE;
    vi = variable_index[TYPE_POINTER][pi][vo]; 
    if (vi == FLAG_NO_USE || (VAR[vi].STATUS & FLAG_QUANTIFIED_SYNC)) 
      continue; 
    vj = variable_index[TYPE_POINTER][pj][vo]; 
    conj = red_bop(AND, ddd_atom(vi, 0, 0), ddd_atom(vj, 0, 0));
    conj = red_bop(OR, conj,
		   red_bop(AND, ddd_atom(vi, pi, pi), ddd_atom(vj, pj, pj))
		   );
    conj = red_bop(OR, conj,
		   red_bop(AND, ddd_atom(vi, pj, pj), ddd_atom(vj, pi, pi))
		   );
    equal = red_bop(AND, equal, conj);
  }
  equal = red_bop(AND, equal, DSC_REVERSE[pi][pj]);

  true_root = red_bop(OR, true_root, equal);

  return(true_root);
}
/* red_true_root() */



struct red_type	*red_first_pred(pi, pj)
     int	pi, pj;
{
  struct red_type	*disj, *conj;
  int			ik, pk, ih, ph, vh, vk, vjk;

  /* case 2: pj is the first successor in [pi, PROCESS_COUNT].
   */
  if (pi > 1) {
    disj = NORM_FALSE;
    for (ik = 0; ik < LOCAL_COUNT[TYPE_POINTER]; ik++) {
      for (pk = pi; pk <= PROCESS_COUNT; pk++) {
	vk = variable_index[TYPE_POINTER][pk][ik]; 
	vjk = variable_index[TYPE_POINTER][pj][ik]; 
	if (   vk == FLAG_NO_USE 
	    || (VAR[vk].STATUS & FLAG_QUANTIFIED_SYNC) 
	    || vjk == FLAG_NO_USE
	    || (VAR[vjk].STATUS & FLAG_QUANTIFIED_SYNC) 
	    ) 
	  continue; 
	conj = NORM_TRUE;
	for (ih = 0; ih < ik; ih++)
	  for (ph = pi; ph <= PROCESS_COUNT; ph++) { 
	    vh = variable_index[TYPE_POINTER][ph][ih]; 
	    if (vh == FLAG_NO_USE || (VAR[vh].STATUS & FLAG_QUANTIFIED_SYNC))
	      continue; 
	    conj = red_bop(AND, conj,
			   red_bop(OR,
				   ddd_atom(vh, pi, PROCESS_COUNT),
				   ddd_atom(vk, 0, 0)
				   )
			   ); 
	  }
	  
	for (ph = pi; ph < pj; ph++) { 
	  vh = variable_index[TYPE_POINTER][ph][ik]; 
	  if (vh == FLAG_NO_USE || (VAR[vh].STATUS & FLAG_QUANTIFIED_SYNC)) 
	    continue; 
		
	  conj = red_bop(AND, conj,
			 red_bop(OR,
				 ddd_atom(vh, pi, PROCESS_COUNT),
				 ddd_atom(vh, 0, 0)
				 )
			 );
	}
	conj = ddd_one_constraint(conj, vjk, 1, pi-1);

	disj = red_bop(OR, conj, disj);
      }
    }
  }

  conj = NORM_TRUE;
  for (ih = 0; ih < LOCAL_COUNT[TYPE_POINTER]; ih++)
    for (ph = pi; ph <= PROCESS_COUNT; ph++) {
      vh = variable_index[TYPE_POINTER][ph][ih]; 
      if (vh == FLAG_NO_USE || (VAR[vh].STATUS & FLAG_QUANTIFIED_SYNC)) 
        continue; 
        
      conj = red_bop(AND, conj,
		     red_bop(OR,
			     ddd_atom(vh, pi, PROCESS_COUNT),
			     ddd_atom(vh, 0, 0)
			     )
		     );
    }
  conj = red_bop(AND, conj, red_true_root(pi, pj));

  if (pi > 1)
    return(red_bop(OR, disj, conj));
  else
    return(conj);
}
/* red_first_pred() */




struct red_type	*red_no_succ(pi)
     int	pi;
{
  struct red_type	*conj;
  int			pk, ik, vk;

  conj = NORM_TRUE;
  for (pk = 1; pk < pi; pk++) {
    for (ik = 0; ik < LOCAL_COUNT[TYPE_POINTER]; ik++) {
      vk = variable_index[TYPE_POINTER][pk][ik]; 
      if (vk == FLAG_NO_USE || (VAR[vk].STATUS & FLAG_QUANTIFIED_SYNC)) 
        continue; 
      conj = ddd_one_constraint(conj, vk, 0, pi-1);
    }
  }
  return(conj);
}
/* red_no_succ() */






struct red_type	*red_first_succ(pi, pj)
     int	pi, pj;
{
  struct red_type	*disj, *conj;
  int			pk, ph, ik, ih, vk, vh, vkh;

  if (PROCESS[pi].group_process_index != PROCESS[pj].group_process_index) 
    return(NORM_FALSE); 
    
  /* case 2: pj is the first successor in [pi, PROCESS_COUNT]
   */
  disj = NORM_FALSE;
  for (pk = 1; pk < pi; pk++) {
    for (ik = 0; ik < LOCAL_COUNT[TYPE_POINTER]; ik++) {
      vk = variable_index[TYPE_POINTER][pk][ik]; 
      if (vk == FLAG_NO_USE || (VAR[vk].STATUS & FLAG_QUANTIFIED_SYNC)) 
        continue; 
        
      conj = NORM_TRUE;
      for (ph = pk+1; ph < pi; ph++)
	for (ih = 0; ih < LOCAL_COUNT[TYPE_POINTER]; ih++) {
	  vh = variable_index[TYPE_POINTER][ph][ih];  
	  if (vh == FLAG_NO_USE || (VAR[vh].STATUS & FLAG_QUANTIFIED_SYNC)) 
	    continue; 
	    
	  conj = ddd_one_constraint(conj, vh, 0, pi-1);
	}
      for (ih = ik+1; ih < LOCAL_COUNT[TYPE_POINTER]; ih++) {     	  
      	vkh = variable_index[TYPE_POINTER][pk][ih]; 
      	if (vkh == FLAG_NO_USE || (VAR[vkh].STATUS & FLAG_QUANTIFIED_SYNC)) 
      	  continue; 
	conj = ddd_one_constraint(conj, vh, 0, pi-1);
      } 
      conj = ddd_one_constraint(conj, vk, pj, pj);

      disj = red_bop(OR, conj, disj);
    }
  }


  /* case 1: there is no succ to [pi, PROCESS_COUNT]
   */
  conj = red_bop(AND, red_first_pred(pi, pj), red_no_succ(pi));

  disj = red_bop(OR, conj, disj);
  return(disj);
}
/* red_first_succ() */



struct red_type	*red_global_root_reverse(pi, pj)
     int	pi, pj;
{
  struct red_type	*disj, *conj;
  int			vo, vop;

  if (PROCESS[pi].group_process_index != PROCESS[pj].group_process_index) 
    return(NORM_FALSE); 
    
  disj = NORM_FALSE;
  for (vo = 0; vo < GLOBAL_COUNT[TYPE_POINTER]; vo++) {
    conj = ddd_atom(variable_index[TYPE_POINTER][0][vo], pj, pj);
    for (vop = 0; vop < vo; vop++) {
      conj = red_bop(AND, conj,
		     ddd_atom(variable_index[TYPE_POINTER][0][vop], 0, pi-1)
		     );
    }
    disj = red_bop(OR, disj, conj);
  }

  conj = red_first_succ(pi, pj);
  if (conj != NORM_FALSE) { 
    for (vo = 0; vo < GLOBAL_COUNT[TYPE_POINTER]; vo++) {
      conj = ddd_one_constraint
	  (conj, variable_index[TYPE_POINTER][0][vo], 0, pi-1);
    }

    disj = red_bop(OR, disj, conj);
  }
  return(disj);
}
/* red_global_root_reverse() */




struct red_type	*dsc_general_reverse_basic(pi, pj) 
	int	pi, pj; 
{
  struct red_type	*result; 
  
  result = red_global_root_reverse(pi, pj); 
  result = red_bop(AND, result, DSC_EQUAL[pi][pj]); 
  result = red_bop(OR, result, DSC_REVERSE[pi][pj]); 
  return(result); 
} 
  /* dsc_general_reverse_basic() */ 
  
  
  
parse_symmetry_template(sym_ptr, sym_proc)
  struct red_type	****sym_ptr, *((*sym_proc)()); 
{
  struct red_type	*result, *conj;
  int			pi, pj, ph, pk, vi, vj, offset, value;

  *sym_ptr = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    (*sym_ptr)[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (pj = 1; pj <= PROCESS_COUNT; pj++) { 
      (*sym_ptr)[pi][pj] = NULL; 	
    } 
  } 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) { 
      if ((*sym_ptr)[pi][pj]) { 
      /* already processed */ 
        continue; 
      } 
      else if (PROCESS[pi].group_process_index != PROCESS[pj].group_process_index) { 
      /* Not in the same equivalence class */ 
	(*sym_ptr)[pi][pj] = NORM_FALSE; 
	(*sym_ptr)[pj][pi] = NORM_FALSE; 
	continue; 
      } 
      else if (PROCESS[pj].group_process_index == pi) { 
      	/* (pi, pj) is the first pair in the equivalence class.  
      	 * So we calculate and copy it to all pairs in this class. 
      	 */ 
      	(*sym_ptr)[pi][pj] = sym_proc(pi, pj); 
        red_mark((*sym_ptr)[pi][pj], FLAG_GC_STABLE);
        
        for (ph = pi; ph <= PROCESS_COUNT; ph++) { 
          for (pk = pi; pk <= PROCESS_COUNT; pk++) { 
            if (ph == pk) 
              (*sym_ptr)[ph][ph] = NORM_NO_RESTRICTION; 
            else if (   (ph == pi && pk == pj) 
		     || PROCESS[ph].group_process_index != pi
		     || PROCESS[pk].group_process_index != pi
		     ) 
	      continue; 
	    else if (pi == ph) { 
	      if (pj == pk) 
	        continue; 
	      else 
		(*sym_ptr)[pi][pk] = red_pi_permute((*sym_ptr)[pi][pj], pk, pj);
	    } 
	    else if (pj == pk)
	      (*sym_ptr)[ph][pj] = red_pi_permute((*sym_ptr)[pi][pj], ph, pi);
	    else if (pi == pk && pj == ph)
	      (*sym_ptr)[pj][pi] = red_pi_permute((*sym_ptr)[pi][pj], pj, pi);
	    else if (pk == pi) {
	      (*sym_ptr)[ph][pi] = red_pi_permute((*sym_ptr)[pi][pj], pi, ph);
	      (*sym_ptr)[ph][pi] = red_pi_permute((*sym_ptr)[ph][pi], pj, pk);
	    }
	    else {
	      (*sym_ptr)[ph][pk] = red_pi_permute((*sym_ptr)[pi][pj], pj, pk);
	      (*sym_ptr)[ph][pk] = red_pi_permute((*sym_ptr)[ph][pk], pi, ph);
	    }
	    red_mark((*sym_ptr)[ph][pk], FLAG_GC_STABLE);
          } 	
        } 
      }	
    } 
  } 

  fprintf(RED_OUT, "\n**** symmetry template *********************\n");
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) 
      if (pi != pj) {
        fprintf(RED_OUT, "(*sym_ptr)[%1d][%1d]:\n", pi, pj);
        red_print_graph((*sym_ptr)[pi][pj]);
      }
  fflush(RED_OUT);
}
/* parse_symmetry_template() */






parse_symmetry_dsc_equal() { 
  fprintf(RED_OUT, "\nShould be obsolete!\n"); 
  fflush(RED_OUT); 
  exit(0);
} 
  /* parse_symmetry_dsc_equal() */ 



parse_symmetry_dsc_reverse()
{
  struct red_type	*result, *conj, *prev_equal;
  int			pi, pj, vi, vj, offset, value;
/*
  test_alloc();
*/
  DSC_REVERSE = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    DSC_REVERSE[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;

  result = NORM_FALSE;
  prev_equal = NORM_NO_RESTRICTION;
  for (offset = 0; offset < LOCAL_COUNT[TYPE_DISCRETE]; offset++) {

    vi = variable_index[TYPE_DISCRETE][SYMMETRY_P1][offset];
    vj = variable_index[TYPE_DISCRETE][SYMMETRY_P2][offset];
    if (VAR[vi].STATUS & FLAG_SYNC_PLACE) 
      continue; 

    conj = NORM_FALSE;
    for (value = VAR[vi].U.DISC.UB; value > VAR[vi].U.DISC.LB; value--) {
      conj = red_bop(OR, conj,
		     red_bop(AND, ddd_atom(vj, VAR[vi].U.DISC.LB, value-1),
			     ddd_atom(vi, value, value)
			     )
		     );
    }

    result = red_bop(OR, result, red_bop(AND, conj, prev_equal));

    conj = NORM_FALSE;
    for (value = VAR[vi].U.DISC.LB; value <= VAR[vi].U.DISC.UB; value++) {
      conj = red_bop(OR, conj,
		     red_bop(AND, ddd_atom(vj, value, value),
			     ddd_atom(vi, value, value)
			     )
		     );
    }

    prev_equal = red_bop(AND, conj, prev_equal);
  }
  DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2] = result;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      if (pi == pj)
        DSC_REVERSE[pi][pj] = NORM_FALSE;
      else if (pi == SYMMETRY_P1)
        if (pj == SYMMETRY_P2) {
	  red_mark(DSC_REVERSE[pi][pj], FLAG_GC_STABLE);
	  continue;
	}
	else
	  DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
      else if (pj == SYMMETRY_P2)
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
      else if (pi == SYMMETRY_P2 && pj == SYMMETRY_P1)
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2], pj, pi);
      else if (pj == SYMMETRY_P1) {
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[pi][pj], SYMMETRY_P2, pj);
      }
      else {
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
	DSC_REVERSE[pi][pj] = red_pi_permute(DSC_REVERSE[pi][pj], SYMMETRY_P1, pi);
      }
      red_mark(DSC_REVERSE[pi][pj], FLAG_GC_STABLE);
    }

  fprintf(RED_OUT, "\n**** DSC_REVERSEs *********************\n");
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      fprintf(RED_OUT, "DSC_REVERSE[%1d][%1d]:\n", pi, pj);
      red_print_graph(DSC_REVERSE[pi][pj]);
    }
  fflush(RED_OUT);
}
/* parse_symmetry_dsc_reverse() */




parse_symmetry_pointer_global_equal()
{
  struct red_type	*result, *conj;
  int			pi, pj, gvi, offset, value;

  POINTER_GLOBAL_EQUAL = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_GLOBAL_EQUAL[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  result = NORM_NO_RESTRICTION;
  for (offset = 0; offset < GLOBAL_COUNT[TYPE_POINTER]; offset++) {

    gvi = variable_index[TYPE_POINTER][0][offset];
    conj = red_bop(AND,
		   red_complement(ddd_atom(gvi, SYMMETRY_P1, SYMMETRY_P1)),
		   red_complement(ddd_atom(gvi, SYMMETRY_P2, SYMMETRY_P2))
		   );

    result = red_bop(AND, conj, result);
  }
  MASK_MARK = FLAG_GC_STABLE;
  POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2] = result;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      if (pi == pj)
        POINTER_GLOBAL_EQUAL[pi][pj] = NORM_NO_RESTRICTION;
      else if (pi == SYMMETRY_P1)
        if (pj == SYMMETRY_P2) {
	  red_mark(POINTER_GLOBAL_EQUAL[pi][pj], FLAG_GC_STABLE);
	  continue;
	}
	else
	  POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
      else if (pj == SYMMETRY_P2)
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
      else if (pi == SYMMETRY_P2 && pj == SYMMETRY_P1)
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2], pj, pi);
      else if (pj == SYMMETRY_P1) {
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[pi][pj], SYMMETRY_P2, pj);
      }
      else {
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
	POINTER_GLOBAL_EQUAL[pi][pj] = red_pi_permute(POINTER_GLOBAL_EQUAL[pi][pj], SYMMETRY_P1, pi);
      }
      red_mark(POINTER_GLOBAL_EQUAL[pi][pj], FLAG_GC_STABLE);
    }

  fprintf(RED_OUT, "\n**** POINTER_GLOBAL_EQUALs *********************\n");
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      fprintf(RED_OUT, "POINTER_GLOBAL_EQUAL[%1d][%1d]:\n", pi, pj);
      red_print_graph(POINTER_GLOBAL_EQUAL[pi][pj]);
    }
  fflush(RED_OUT);
}
/* parse_symmetry_pointer_global_equal() */







parse_symmetry_pointer_global_reverse()
{
  struct red_type	*result, *conj, *prev_equal;
  int			pi, pj, gvi, offset, value;

  POINTER_GLOBAL_REVERSE = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_GLOBAL_REVERSE[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;

  result = NORM_FALSE;
  prev_equal = NORM_NO_RESTRICTION;
  for (offset = 0; offset < GLOBAL_COUNT[TYPE_POINTER]; offset++) {

    gvi = variable_index[TYPE_POINTER][0][offset];
    result = red_bop(OR, result,
		     red_bop(AND, ddd_atom(gvi, SYMMETRY_P2, SYMMETRY_P2), prev_equal)
		     );

    conj = red_bop(AND,
		   red_complement(ddd_atom(gvi, SYMMETRY_P1, SYMMETRY_P1)),
		   red_complement(ddd_atom(gvi, SYMMETRY_P2, SYMMETRY_P2))
		   );
    prev_equal = red_bop(AND, conj, prev_equal);
  }
  MASK_MARK = FLAG_GC_STABLE;
  POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2] = result;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      if (pi == pj)
        POINTER_GLOBAL_REVERSE[pi][pj] = NORM_FALSE;
      else if (pi == SYMMETRY_P1)
        if (pj == SYMMETRY_P2) {
	  red_mark(POINTER_GLOBAL_REVERSE[pi][pj], FLAG_GC_STABLE);
	  continue;
	}
	else
	  POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
      else if (pj == SYMMETRY_P2)
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
      else if (pi == SYMMETRY_P2 && pj == SYMMETRY_P1)
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2], pj, pi);
      else if (pj == SYMMETRY_P1) {
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[pi][pj], SYMMETRY_P2, pj);
      }
      else {
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
	POINTER_GLOBAL_REVERSE[pi][pj] = red_pi_permute(POINTER_GLOBAL_REVERSE[pi][pj], SYMMETRY_P1, pi);
      }
      red_mark(POINTER_GLOBAL_REVERSE[pi][pj], FLAG_GC_STABLE);
    }

  fprintf(RED_OUT, "\n**** POINTER_GLOBAL_REVERSEs *********************\n");
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      fprintf(RED_OUT, "POINTER_GLOBAL_REVERSE[%1d][%1d]:\n", pi, pj);
      red_print_graph(POINTER_GLOBAL_REVERSE[pi][pj]);
    }
  fflush(RED_OUT);
}
/* parse_symmetry_pointer_global_reverse() */






/****************************************************************************
 *
 *  for option d
 *  Recursively called by red_clock_reverse() and red_discrete_clock_pointer()
 */
struct red_type	*red_global_pointer_reverse(w, vo)
     int	vo;
{
  struct red_type	*conj, *result, *filter, *subresult;
  int			cv, fv, vi, vj, fi, fj;

  if (vo >= GLOBAL_COUNT[TYPE_POINTER])
    return(NORM_FALSE);
  else {
    vi = variable_index[TYPE_POINTER][0][vo];
    RT[w] = red_global_pointer_reverse(vo+1);
    conj = red_complement(red_bop(OR, ddd_atom(vi, SWITCH_PJ, SWITCH_PJ),
				 ddd_atom(vi, SWITCH_PI, SWITCH_PI)
				 )
			  );
    RT[w] = red_bop(AND, conj, RT[w]);
    RT[w] = red_bop(OR, RT[w], ddd_atom(vi, SWITCH_PJ, SWITCH_PJ));
    return(RT[w]);
  }
}
/* red_global_pointer_reverse() */







struct red_type	*red_clock_reverse(W, vo)
     int	vo;
{
  int			ci, cj, vi, vj;

  if (vo >= LOCAL_COUNT[TYPE_CLOCK])
    return(red_global_pointer_reverse(W, 0));
  else {
    vi = variable_index[TYPE_CLOCK][SWITCH_PI][vo];
    vj = variable_index[TYPE_CLOCK][SWITCH_PJ][vo];
    ci = VAR[vi].U.CLOCK.CLOCK_INDEX;
    cj = VAR[vj].U.CLOCK.CLOCK_INDEX;

    RT[W] = red_clock_reverse(W, vo+1);
    if (ci < cj) {
      RT[W] = ddd_one_constraint(RT[W], 1+ZONE[ci][cj], 0, 0);
      RT[W] = red_bop(OR, RT[W], ddd_atom(1+ZONE[ci][cj], CLOCK_NEG_INFINITY, -1));
    }
    else {
      RT[W] = ddd_one_constraint(RT[W], 1+ZONE[cj][ci], 0, 0);
      RT[W] = red_bop(OR, RT[W], ddd_atom(1+ZONE[cj][ci], 1, CLOCK_POS_INFINITY));
    }

    garbage_collect(FLAG_GC_REPORT);

    return(RT[W]);
  }
}
/* red_clock_reverse() */







struct red_type	*red_discrete_clock_reverse(W, vo)
     int	W, vo;
{
  struct red_type	*conj;
  int			cv, vi, vj, in, sub;

  if (vo >= LOCAL_COUNT[TYPE_DISCRETE])
    return(red_clock_reverse(W, 0));
  else {
    vi = variable_index[TYPE_DISCRETE][SWITCH_PI][vo];
    vj = variable_index[TYPE_DISCRETE][SWITCH_PJ][vo];

    RT[W] = red_discrete_clock_reverse(W, vo+1);
    conj = NORM_FALSE;
    for (cv = VAR[vi].U.DISC.LB; cv <= VAR[vi].U.DISC.UB; cv++) {
      conj = red_bop(OR, conj,
		     red_bop(AND, ddd_atom(vi, cv, cv),
			     ddd_atom(vj, cv, cv)
			     )
		     );
    }
    RT[W] = red_bop(AND, RT[W], conj);

    for (cv = VAR[vi].U.DISC.LB+1; cv <= VAR[vi].U.DISC.UB; cv++)
      RT[W] = red_bop(OR, RT[W],
		      red_bop(AND, ddd_atom(vj, 0, cv-1),
			      ddd_atom(vi, cv, cv)
			      )
		      );

    garbage_collect(FLAG_GC_REPORT);

    return(RT[W]);
  }
}
/* red_discrete_clock_reverse() */




parse_symmetry_pointer_onestep_offline()
{
  int pi, pj;

  parse_symmetry_dsc_reverse();

  PROCESS_REVERSE = ((struct red_type ***)
		     malloc(PROCESS_COUNT*sizeof(struct red_type **))
		     ) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    PROCESS_REVERSE[pi] = ((struct red_type **) malloc((PROCESS_COUNT)*sizeof(struct red_type *))) - 1;

    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      PROCESS_REVERSE[pi][pj] = red_global_root_reverse(pi, pj);

      MASK_MARK = FLAG_GC_STABLE;
      red_mark(PROCESS_REVERSE[pi][pj], FLAG_GC_STABLE);

      garbage_collect(FLAG_GC_REPORT);

	fprintf(RED_OUT, "\nred_reverse[pi=%1d][pj=%1d]:\n", pi, pj);
	red_print_graph(PROCESS_REVERSE[pi][pj]);

    }
  }

/*
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    PROCESS_REVERSE[pi] = ((struct red_type **) malloc((PROCESS_COUNT)*sizeof(struct red_type *))) - 1;
  }
  PROCESS_REVERSE[SYMMETRY_P1][SYMMETRY_P2] = red_global_root_reverse(SYMMETRY_P1, SYMMETRY_P2);

  MASK_MARK = FLAG_GC_STABLE;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      if (pi != SYMMETRY_P1 && pj != SYMMETRY_P2) {
        PROCESS_REVERSE[pi][pj]
        = red_pi_permute(PROCESS_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
        if (pi != SYMMETRY_P1)
          PROCESS_REVERSE[pi][pj]
          = red_pi_permute(PROCESS_REVERSE[pi][pj], SYMMETRY_P1, pi);
      }
      red_mark(PROCESS_REVERSE[pi][pj], FLAG_GC_STABLE);
*/
/*
	fprintf(RED_OUT, "\nred_reverse[pi=%1d][pj=%1d]:\n", pi, pj);
	red_print_graph(PROCESS_REVERSE[pi][pj]);
*/
/*
    }
*/
}
  /* parse_symmetry_pointer_onestep_offline() */




/**************************************************************************
 *  This is used for links of all lengths with fixpoint
 *
 * This is used with the assumption that pointer_local_fanout_equal is true.
 */
parse_symmetry_pointer_local_fanin_equal()
{
  int			pi, pj, flag_change, ov, pk, ph, count;
  struct red_type	*result;

  POINTER_LOCAL_FANIN_EQUAL = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_LOCAL_FANIN_EQUAL[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++)
      if (pi == pj)
        POINTER_LOCAL_FANIN_EQUAL[pi][pj] = NORM_NO_RESTRICTION;
      else
        POINTER_LOCAL_FANIN_EQUAL[pi][pj]
        = red_bop(AND, POINTER_GLOBAL_EQUAL[pi][pj], DSC_EQUAL[pi][pj]);

  for (count = 0, flag_change = TYPE_TRUE; flag_change; count++) {
    flag_change = TYPE_FALSE;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
        if (pi == pj)
	  continue;

        result = NORM_FALSE;
        for (ov = 0; ov < LOCAL_COUNT[TYPE_POINTER]; ov++) {
	  for (pk = 1; pk <= PROCESS_COUNT; pk++)
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      result = red_bop(OR, result,
			       red_bop(AND,
				       POINTER_LOCAL_FANIN_EQUAL[pk][ph],
				       red_bop(AND,
					       ddd_atom(variable_index[TYPE_POINTER][pk][ov], pi, pi),
					       ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj)
					       )
				       )
			        );
	}
	if (result != POINTER_LOCAL_FANIN_EQUAL[pi][pj]) {
	  flag_change = TYPE_TRUE;
	  POINTER_LOCAL_FANIN_EQUAL[pi][pj] = result;
	}
      }
    }
    fprintf(RED_OUT, "\n**(count=%1d)************************\n", count);
    for (pi = 1; pi <= PROCESS_COUNT; pi++)
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
	fprintf(RED_OUT, "POINTER_LOCAL_FANIN_EQUAL[%1d][%1d]:\n", pi, pj);
	red_print_graph(POINTER_LOCAL_FANIN_EQUAL[pi][pj]);
      }
    fflush(RED_OUT);
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++)
      red_mark(POINTER_LOCAL_FANIN_EQUAL[pi][pj], FLAG_GC_STABLE);
 }
  /* parse_symmetry_pointer_local_fanin_equal() */




/* This is used with the assumption that pointer_local_fanout_equal is true. */
parse_symmetry_pointer_local_fanin_reverse()
{
  int			pi, pj, flag_change, ov, pk, ph, count;
  struct red_type	*result, *prev_equal, *subresult,
			*new_kh_reverse_instance, *new_hk_reverse_instance;

  POINTER_LOCAL_FANIN_REVERSE = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_LOCAL_FANIN_REVERSE[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++)
      if (pi == pj)
        POINTER_LOCAL_FANIN_REVERSE[pi][pj] = NORM_FALSE;
      else
	POINTER_LOCAL_FANIN_REVERSE[pi][pj]
        = red_bop(OR, POINTER_GLOBAL_REVERSE[pi][pj],
		red_bop(AND, POINTER_GLOBAL_EQUAL[pi][pj], DSC_REVERSE[pi][pj])
		);

  /* a pi, pj is reversed iff either
   * 1. the global or discrete of pi and pj are reversed
   * 2. pi-v->pk pj-v->ph and pk ph are reversed, and for all v' < v, pi and pj are equal.
   */
  for (count = 0, flag_change = TYPE_TRUE; flag_change; count++) {
    flag_change = TYPE_FALSE;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
        if (pi == pj)
	  continue;

        result = NORM_FALSE;
	prev_equal = NORM_NO_RESTRICTION;
        for (ov = 0; ov < LOCAL_COUNT[TYPE_POINTER]; ov++) {
	  subresult = NORM_NO_RESTRICTION;
	  for (pk = 1; pk <= PROCESS_COUNT; pk++) {
	    subresult = red_bop(AND, prev_equal,
				ddd_atom(variable_index[TYPE_POINTER][pk][ov], pi, pi)
				);
	    /* For all ph, either vo[ph] is NULL or
				  ph points to pj implies ph is reverse with pk.
	    */
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      if (pk != ph) {
	        subresult = red_bop(AND, subresult,
				    red_bop(OR,
					    red_complement(ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj)),
					    POINTER_LOCAL_FANIN_REVERSE[pk][ph]
					    )
				    );
	      }
	  }

	  result = red_bop(OR, result, subresult);

	  /* update the previous_equal in the following way.
	   * pi and pj are fanin equal w.r.t. local pointer ov iff
	     1. if pk->pi and reverse with pj, then either forall ph, ph->pj ==> ph reverse with pi
	     2. vice versa
	   */
	  new_kh_reverse_instance = NORM_FALSE;
	  for (pk = 1; pk <= PROCESS_COUNT; pk++) {
	    subresult = NORM_NO_RESTRICTION;
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      subresult = red_bop(AND, subresult,
				  red_complement(ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj))
				  );
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      if (pk != ph)
	        subresult = red_bop(OR, subresult,
				  red_bop(AND,
					  POINTER_LOCAL_FANIN_REVERSE[pk][ph],
					  ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj)
					  )
				  );
	    subresult = red_bop(AND, subresult,
				ddd_atom(variable_index[TYPE_POINTER][pk][ov], pi, pi)
				);
	    new_kh_reverse_instance = red_bop(OR, new_kh_reverse_instance, subresult);
	  }
	  new_hk_reverse_instance = NORM_FALSE;
	  for (ph = 1; ph <= PROCESS_COUNT; ph++) {
	    subresult = NORM_NO_RESTRICTION;
	    for (pk = 1; pk <= PROCESS_COUNT; pk++)
	      subresult = red_bop(AND, subresult,
				  red_complement(ddd_atom(variable_index[TYPE_POINTER][pk][ov], pi, pi))
				  );
	    for (pk = 1; pk <= PROCESS_COUNT; pk++)
	      if (pk != ph)
	        subresult = red_bop(OR, subresult,
				    red_bop(AND,
					    POINTER_LOCAL_FANIN_REVERSE[ph][pk],
					    ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj)
					    )
				    );
	    subresult = red_bop(AND, subresult,
				ddd_atom(variable_index[TYPE_POINTER][ph][ov], pj, pj)
				);
	    new_hk_reverse_instance = red_bop(OR, new_hk_reverse_instance, subresult);
	  }
	  prev_equal = red_bop(AND, prev_equal,
			       red_bop(AND,
				       red_bop(OR, new_kh_reverse_instance,
					       red_complement(new_hk_reverse_instance)
					       ),
				       red_bop(OR, new_hk_reverse_instance,
					       red_complement(new_kh_reverse_instance)
					       )
				       )
			       );
	}
	result = red_bop(OR, POINTER_LOCAL_FANIN_REVERSE[pi][pj],
			 red_bop(AND, result,
				 red_bop(AND,
					 red_complement(POINTER_LOCAL_FANIN_REVERSE[pi][pj]),
					 red_complement(POINTER_LOCAL_FANIN_REVERSE[pj][pi])
					 )
				 )
			 );
        if (result != POINTER_LOCAL_FANIN_REVERSE[pi][pj]) {
	  flag_change = TYPE_TRUE;
	  POINTER_LOCAL_FANIN_REVERSE[pi][pj] = result;
	}
      }
    }
/*
    fprintf(RED_OUT, "\n**(count=%1d)************************\n", count);
    for (pi = 1; pi <= PROCESS_COUNT; pi++)
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
	fprintf(RED_OUT, "POINTER_LOCAL_FANIN_REVERSE[%1d][%1d]:\n", pi, pj);
	red_print_graph(POINTER_LOCAL_FANIN_REVERSE[pi][pj]);
      }
    fflush(RED_OUT);
*/
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++)
      red_mark(POINTER_LOCAL_FANIN_REVERSE[pi][pj], FLAG_GC_STABLE);
}
  /* parse_symmetry_pointer_local_fanin_REVERSE() */




parse_symmetry_pointer_local_fanout_equal()
{
  int			pi, pj, flag_change, ov, pk, ph;
  struct red_type	*result;

  POINTER_LOCAL_FANOUT_EQUAL = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_LOCAL_FANOUT_EQUAL[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++)
      if (pi == pj)
        POINTER_LOCAL_FANOUT_EQUAL[pi][pj] = NORM_NO_RESTRICTION;
      else if (   (pi == SYMMETRY_P2 && pj != SYMMETRY_P1)
	       || (pi != SYMMETRY_P2 && pj == SYMMETRY_P1)
	       ) {
        POINTER_LOCAL_FANOUT_EQUAL[pi][pj] = NORM_FALSE;
      }
      else {
        POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
        = red_bop(AND, POINTER_GLOBAL_EQUAL[pi][pj], DSC_EQUAL[pi][pj]);
      }
  for (flag_change = TYPE_TRUE; flag_change; ) {
    flag_change = TYPE_FALSE;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
        if (pi == pj)
	  continue;

        result = NORM_FALSE;
        for (ov = 0; ov < LOCAL_COUNT[TYPE_POINTER]; ov++) {
          for (pk = 0; pk <= PROCESS_COUNT; pk++)
	    result = red_bop(OR, result,
			     red_bop(AND,
				     ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
				     ddd_atom(variable_index[TYPE_POINTER][pj][ov], pk, pk)
				     )
			     );
	  for (pk = 1; pk <= PROCESS_COUNT; pk++)
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      result = red_bop(OR, result,
			       red_bop(AND,
				       POINTER_LOCAL_FANOUT_EQUAL[pk][ph],
				       red_bop(AND,
					       ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
					       ddd_atom(variable_index[TYPE_POINTER][pj][ov], ph, ph)
					       )
				       )
			       );
	}
	if (result != POINTER_LOCAL_FANOUT_EQUAL[pi][pj]) {
	  flag_change = TYPE_TRUE;
	  POINTER_LOCAL_FANOUT_EQUAL[pi][pj] = result;
	}
      }
    }
  }
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      if (pi == SYMMETRY_P2 && pj == SYMMETRY_P1)
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[SYMMETRY_P1][SYMMETRY_P2], pi, pj);
      else if (pi == SYMMETRY_P1) {
        if (pj != SYMMETRY_P2)
	  POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	  = red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
      }
      else if (pj == SYMMETRY_P2) {
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
      }
      else if (pj == SYMMETRY_P1) {
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[pi][pj], SYMMETRY_P2, pj);
      }
      else {
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_LOCAL_FANOUT_EQUAL[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_EQUAL[pi][pj], SYMMETRY_P2, pj);
      }
      red_mark(POINTER_LOCAL_FANOUT_EQUAL[pi][pj], FLAG_GC_STABLE);
    }
}
  /* parse_symmetry_pointer_local_fanout_equal() */




parse_symmetry_pointer_local_fanout_reverse()
{
  int			pi, pj, flag_change, ov, pk, ph, count;
  struct red_type	*result, *prev_equal, *new_equal;

  POINTER_LOCAL_FANOUT_REVERSE = ((struct red_type ***) malloc(PROCESS_COUNT * sizeof(struct red_type **))) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    POINTER_LOCAL_FANOUT_REVERSE[pi] = ((struct red_type **)
			malloc(PROCESS_COUNT * sizeof(struct red_type *))
			) - 1;
  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      POINTER_LOCAL_FANOUT_REVERSE[pi][pj] = NORM_FALSE;
      if (pi != pj) {
        if (pi != SYMMETRY_P2 && pj == SYMMETRY_P1)
          POINTER_LOCAL_FANOUT_REVERSE[pi][pj] = NORM_NO_RESTRICTION;

	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_bop(AND, DSC_EQUAL[pi][pj], POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
        = red_bop(OR, DSC_REVERSE[pi][pj], POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);

	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
        = red_bop(AND, POINTER_GLOBAL_EQUAL[pi][pj], POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
        = red_bop(OR, POINTER_GLOBAL_REVERSE[pi][pj], POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);
      }
    }
  for (count = 0, flag_change = TYPE_TRUE; flag_change; count++) {
    flag_change = TYPE_FALSE;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
        result = NORM_FALSE;
	prev_equal = NORM_NO_RESTRICTION;
        for (ov = 0; ov < LOCAL_COUNT[TYPE_POINTER]; ov++) {
	  for (pk = 1; pk <= PROCESS_COUNT; pk++)
	    result = red_bop(OR, result,
			     red_bop(AND,
				     ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
				     ddd_atom(variable_index[TYPE_POINTER][pj][ov], 0, 0)
				     )
			     );
	  for (pk = 1; pk <= PROCESS_COUNT; pk++)
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      result = red_bop(OR, result,
			       red_bop(AND,
				       red_bop(AND,
					       POINTER_LOCAL_FANOUT_REVERSE[pk][ph],
					       prev_equal
					       ),
				       red_bop(AND,
					       ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
					       ddd_atom(variable_index[TYPE_POINTER][pj][ov], ph, ph)
					       )
				       )
			       );
	  new_equal = NORM_FALSE;
	  for (pk = 0; pk <= PROCESS_COUNT; pk++)
	    new_equal = red_bop(OR, new_equal,
				red_bop(AND,
					ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
					ddd_atom(variable_index[TYPE_POINTER][pj][ov], pk, pk)
					)
				);
	  for (pk = 1; pk <= PROCESS_COUNT; pk++)
	    for (ph = 1; ph <= PROCESS_COUNT; ph++)
	      new_equal = red_bop(OR, new_equal,
				  red_bop(AND, POINTER_LOCAL_FANOUT_EQUAL[pk][ph],
					  red_bop(AND,
						  ddd_atom(variable_index[TYPE_POINTER][pi][ov], pk, pk),
						  ddd_atom(variable_index[TYPE_POINTER][pj][ov], ph, ph)
						  )
					  )
				  );
	  prev_equal = red_bop(AND, prev_equal, new_equal);
	}
	result = red_bop(OR, POINTER_LOCAL_FANOUT_REVERSE[pi][pj],
			 red_bop(AND, result,
				 red_bop(AND,
					 red_complement(POINTER_LOCAL_FANOUT_REVERSE[pi][pj]),
					 red_complement(POINTER_LOCAL_FANOUT_REVERSE[pj][pi])
					 )
				 )
			 );
	if (result != POINTER_LOCAL_FANOUT_REVERSE[pi][pj]) {
	  flag_change = TYPE_TRUE;
	  POINTER_LOCAL_FANOUT_REVERSE[pi][pj] = result;
	}
      }
    }
/*
    fprintf(RED_OUT, "\n**(count=%1d)************************\n", count);
    for (pi = 1; pi <= PROCESS_COUNT; pi++)
      for (pj = 1; pj <= PROCESS_COUNT; pj++) {
	fprintf(RED_OUT, "POINTER_LOCAL_FANOUT_REVERSE[%1d][%1d]:\n", pi, pj);
	red_print_graph(POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);
      }
    fflush(RED_OUT);
*/
  }

  for (pi = 1; pi <= PROCESS_COUNT; pi++)
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      if (pi == SYMMETRY_P2 && pj == SYMMETRY_P1)
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[SYMMETRY_P1][SYMMETRY_P2], pi, pj);
      else if (pi == SYMMETRY_P1) {
        if (pj != SYMMETRY_P2)
	  POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	  = red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P2, pj);
      }
      else if (pj == SYMMETRY_P2) {
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
      }
      else if (pj == SYMMETRY_P1) {
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[pi][pj], SYMMETRY_P2, pj);
      }
      else {
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[SYMMETRY_P1][SYMMETRY_P2], SYMMETRY_P1, pi);
	POINTER_LOCAL_FANOUT_REVERSE[pi][pj]
	= red_pi_permute(POINTER_LOCAL_FANOUT_REVERSE[pi][pj], SYMMETRY_P2, pj);
      }
      red_mark(POINTER_LOCAL_FANOUT_REVERSE[pi][pj], FLAG_GC_STABLE);
    }
}
  /* parse_symmetry_pointer_local_fanout_REVERSE() */







struct red_type	*red_symmetry_pointer_reverse_fixpoint_fanout_offline(pi, pj)
     int	pi, pj;
{
  struct red_type	*result;

  result = DSC_REVERSE[pi][pj];

  result = red_bop(AND, result, POINTER_LOCAL_FANIN_EQUAL[pi][pj]);
  result = red_bop(OR, result, POINTER_LOCAL_FANIN_REVERSE[pi][pj]);

  result = red_bop(AND, result, POINTER_LOCAL_FANOUT_EQUAL[pi][pj]);
  result = red_bop(OR, result, POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);

  result = red_bop(AND, result, POINTER_GLOBAL_EQUAL[pi][pj]);
  result = red_bop(OR, result, POINTER_GLOBAL_REVERSE[pi][pj]);

  return(result);
}
/* red_symmetry_pointer_reverse_fixpoint_fanout_offline() */



parse_symmetry_pointer_fixpoint_offline()
{
  int			pi, pj;


  parse_symmetry_dsc_equal();
  parse_symmetry_dsc_reverse();

  parse_symmetry_pointer_global_equal();
  parse_symmetry_pointer_global_reverse();

  parse_symmetry_pointer_local_fanin_equal();
  parse_symmetry_pointer_local_fanin_reverse();

  parse_symmetry_pointer_local_fanout_equal();
  parse_symmetry_pointer_local_fanout_reverse();

  PROCESS_REVERSE = ((struct red_type ***)
		     malloc(PROCESS_COUNT*sizeof(struct red_type **))
		     ) - 1;

  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    PROCESS_REVERSE[pi] = ((struct red_type **) malloc((PROCESS_COUNT)*sizeof(struct red_type *))) - 1;

    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      PROCESS_REVERSE[pi][pj] = red_symmetry_pointer_reverse_fixpoint_fanout_offline(pi, pj);

      red_mark(PROCESS_REVERSE[pi][pj], FLAG_GC_STABLE);

      garbage_collect(FLAG_GC_REPORT);
    }
  }

  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    for (pj = 1; pj <= PROCESS_COUNT; pj++) {
      MASK_MARK = FLAG_GC_STABLE;
      red_unmark(DSC_EQUAL[pi][pj]);
      red_unmark(DSC_REVERSE[pi][pj]);
      red_unmark(POINTER_LOCAL_FANOUT_EQUAL[pi][pj]);
      red_unmark(POINTER_LOCAL_FANOUT_REVERSE[pi][pj]);
      red_unmark(POINTER_LOCAL_FANIN_EQUAL[pi][pj]);
      red_unmark(POINTER_LOCAL_FANIN_REVERSE[pi][pj]);
      red_unmark(POINTER_GLOBAL_EQUAL[pi][pj]);
      red_unmark(POINTER_GLOBAL_REVERSE[pi][pj]);
    }
    free(DSC_REVERSE[pi] + 1);
    free(DSC_EQUAL[pi] + 1);
    free(POINTER_LOCAL_FANOUT_EQUAL[pi] + 1);
    free(POINTER_LOCAL_FANOUT_REVERSE[pi] + 1);
    free(POINTER_LOCAL_FANIN_EQUAL[pi] + 1);
    free(POINTER_LOCAL_FANIN_REVERSE[pi] + 1);
    free(POINTER_GLOBAL_EQUAL[pi] + 1);
    free(POINTER_GLOBAL_REVERSE[pi] + 1);
  }
  free(DSC_EQUAL + 1);
  free(DSC_REVERSE + 1);

  free(POINTER_LOCAL_FANOUT_EQUAL + 1);
  free(POINTER_LOCAL_FANOUT_REVERSE + 1);

  free(POINTER_LOCAL_FANIN_EQUAL + 1);
  free(POINTER_LOCAL_FANIN_REVERSE + 1);

  free(POINTER_GLOBAL_EQUAL + 1);
  free(POINTER_GLOBAL_REVERSE + 1);
}
  /* parse_symmetry_pointer_fixpoint_offline() */



/************************************************************
*
*  Routines for the initialization of pointer-symmetry with fixpoint fanout checking.
*  Note that the arrays of DSC_EQUAL, DSC_REVERSE, POINTER_GLOBAL_EQUAL,
*  and POINTER_GLOBAL_REVERSE are not released after the initialization
*  since they are needed in the online symmetry reduction.
*/
parse_symmetry_pointer_fixpoint_online()
{
  int			pi, pj;

  parse_symmetry_dsc_equal();
  parse_symmetry_dsc_reverse();

  parse_symmetry_pointer_global_equal();
  parse_symmetry_pointer_global_reverse();
}
  /* parse_symmetry_pointer_fixpoint_online() */





/****************************************************************************
 *
 *  for option v
 *  Recursively called by itself.
 */

struct red_type	*red_zone_reverse(offset)
     int	offset;
{
  struct red_type	*conj, *filter, *subresult;
  int			vi, zij, vj, zji, value;

  if (offset >= LOCAL_COUNT[TYPE_CLOCK])
    return(NORM_TRUE);

  vi = variable_index[TYPE_CLOCK][SWITCH_PI][offset];
  vj = variable_index[TYPE_CLOCK][SWITCH_PJ][offset];

  zij = ZONE[VAR[vi].U.CLOCK.CLOCK_INDEX][VAR[vj].U.CLOCK.CLOCK_INDEX];
  zji = ZONE[VAR[vj].U.CLOCK.CLOCK_INDEX][VAR[vi].U.CLOCK.CLOCK_INDEX];

  subresult = NORM_FALSE;
  for (value = CLOCK_NEG_INFINITY; value < CLOCK_POS_INFINITY; value++) {
    subresult = red_bop(OR, subresult,
			red_bop(AND, ddd_atom(1+zji, value, value),
				ddd_atom(1+zij, value+1, VAR[vi].U.DISC.UB)
				)
			);
  }

  conj = NORM_FALSE;
  for (value = 0; value <= CLOCK_POS_INFINITY; value++) {
    conj = red_bop(OR, conj,
		   red_bop(AND, ddd_atom(1+zij, value, value),
			   ddd_atom(1+zji, value, value)
			   )
		   );
  }

  conj = red_bop(AND, red_zone_reverse(offset+1), conj);

  subresult = red_bop(OR, conj, subresult);
  return(subresult);
}
/* red_zone_reverse() */



struct red_type	*red_reverse(offset)
     int	offset;
{
  struct red_type	*conj, *child, *subresult;
  int			vi, vj, value;

  if (offset >= LOCAL_COUNT[TYPE_DISCRETE])
    return(NORM_FALSE);

  vi = variable_index[TYPE_DISCRETE][SWITCH_PI][offset];
  vj = variable_index[TYPE_DISCRETE][SWITCH_PJ][offset];

  child = red_reverse(offset+1);

  subresult = NORM_FALSE;
  for (value = VAR[vi].U.DISC.LB; value < VAR[vi].U.DISC.UB; value++) {
    subresult = red_bop(OR, subresult,
			red_bop(AND, ddd_atom(vj, value, value),
				ddd_atom(vi, value+1, VAR[vi].U.DISC.UB)
				)
			);
  }

  conj = NORM_FALSE;
  for (value = VAR[vi].U.DISC.LB; value <= VAR[vi].U.DISC.UB; value++) {
    conj = red_bop(OR, conj,
		   red_bop(AND, ddd_atom(vj, value, value),
			   ddd_atom(vi, value, value)
			   )
		   );
  }

  conj = red_bop(AND, child, conj);

  subresult = red_bop(OR, conj, subresult);
  return(subresult);
}
/* red_reverse() */



parse_symmetry_state_offline()
{
  parse_symmetry_dsc_equal();
  PROCESS_REVERSE = ((struct red_type ***)
		     malloc(PROCESS_COUNT*sizeof(struct red_type **))
		     ) - 1;

  PROCESS_EQUAL = ((struct red_type ***)
		   malloc(PROCESS_COUNT*sizeof(struct red_type **))
		   ) - 1;

  for (SWITCH_PI = 1; SWITCH_PI < PROCESS_COUNT; SWITCH_PI++) {
    PROCESS_REVERSE[SWITCH_PI]
    = ((struct red_type **)
       malloc((PROCESS_COUNT)*sizeof(struct red_type *))
       ) - 1 - SWITCH_PI;
    PROCESS_EQUAL[SWITCH_PI]
    = ((struct red_type **)
       malloc((PROCESS_COUNT)*sizeof(struct red_type *))
       ) - 1 - SWITCH_PI;

    for (SWITCH_PJ = SWITCH_PI+1; SWITCH_PJ <= PROCESS_COUNT; SWITCH_PJ++) {
      PROCESS_REVERSE[SWITCH_PI][SWITCH_PJ] = red_reverse(0);
      PROCESS_EQUAL[SWITCH_PI][SWITCH_PJ] = DSC_EQUAL[SWITCH_PI][SWITCH_PJ];

      red_mark(PROCESS_REVERSE[SWITCH_PI][SWITCH_PJ], FLAG_GC_STABLE);
      red_mark(PROCESS_EQUAL[SWITCH_PI][SWITCH_PJ], FLAG_GC_STABLE);
/*
	fprintf(RED_OUT, "\nred_reverse[SWITCH_PI=%1d][SWITCH_PJ=%1d]:\n", SWITCH_PI, SWITCH_PJ);
	red_print_graph(PROCESS_REVERSE[SWITCH_PI][SWITCH_PJ]);
*/
      garbage_collect(FLAG_GC_SILENT);
    }
  }
}
  /* parse_symmetry_state_offline() */





parse_symmetry_discrete_general()
{
  fprintf(RED_OUT, ">> Calculating DSC_EQUAL \n"); 
  parse_symmetry_template(&DSC_EQUAL, dsc_equal_basic);
  fprintf(RED_OUT, ">> Calculating DSC_REVERSE \n"); 
  parse_symmetry_template(&DSC_REVERSE, dsc_reverse_basic);
  fprintf(RED_OUT, ">> Calculating DSC_GENERAL_REVERSE \n"); 
  parse_symmetry_template(&PROCESS_REVERSE, dsc_general_reverse_basic); 
}
  /* parse_symmetry_discrete_general() */







parse_symmetry()
{
  int			w, pi, pj;

/*
  print_cpu_time("** Entering parse_symmetry() **");
*/
  switch (GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY) {
  case FLAG_SYMMETRY_POINTER_FIXPOINT_OFFLINE:
    parse_symmetry_pointer_fixpoint_offline();
    break;
  case FLAG_SYMMETRY_POINTER_FIXPOINT_ONLINE:
    parse_symmetry_pointer_fixpoint_online();
    break;
  case FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE:
    parse_symmetry_pointer_onestep_offline();
    break;
  case FLAG_SYMMETRY_ZONE:
  case FLAG_SYMMETRY_STATE:
    parse_symmetry_state_offline();
    break;
  case FLAG_SYMMETRY_DISCRETE_GENERAL: 
    parse_symmetry_discrete_general(); 
    break; 
  }
/*
  print_cpu_time("** Leaving parse_symmetry **");
*/
}
/* parse_symmetry() */












/*************************************************************************
 *
 *  Symmetry
 */

reduce_symmetry_offline(w)
     int	w;
{
  int			flag_symmetry, pi, pj, dsc_boundary, dsc_oo;
  struct red_type	*cond;

  /*
  fprintf(RED_OUT, "\n=============================================\nBefore symmetry!\n");
  red_print_graph(RT[w]);
  probe(PROBE_PRERISK, "\nBefore symmetry probe\n", RT[NEW]);
  flag_symmetry = FALSE;
  */
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) { 
      if (PROCESS[pi].group_process_index != PROCESS[pj].group_process_index) 
      	continue; 
      RT[dsc_oo = RT_TOP++] = red_bop(EXTRACT, RT[w], PROCESS_REVERSE[pi][pj]);
      if (RT[dsc_oo] != NORM_FALSE) {
	/*
	flag_symmetry = TRUE;
	*/
	fprintf(RED_OUT, "\n---------------------------------------\nBefore symmetry reduction on pi=%1d, pj =%1d:\n",
		pi, pj
		);
	red_print_graph(RT[dsc_oo]);

	RT[w] = red_bop(EXCLUDE, RT[w], RT[dsc_oo]);
	RT[dsc_oo] = red_pi_permute(RT[dsc_oo], pi, pj);

	fprintf(RED_OUT, "\n\nAfter symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj);
	red_print_graph(RT[dsc_oo]);

	RT[w] = red_bop(OR, RT[w], RT[dsc_oo]); 
      } 
      RT_TOP--;
      garbage_collect(FLAG_GC_SILENT);
    }
  }
  /*
  probe(PROBE_PRERISK, "\nAfter symmetry probe\n", RT[w]);
  if (flag_symmetry) {
    fprintf(RED_OUT, "\n=================================\nSymmetry successful!\n");
    red_print_graph(RT[w]);
  }
  */
}
/* reduce_symmetry_offline() */




/*******************************************************
*
* online symmetry reduction for pointer data-structure
*/
int	SYMMETRY_RESULT;

int	TS_SYMMETRY_POINTER_FIXPOINT_ONLINE_FANOUT_ONEPAIR; 

struct red_type	*rec_symmetry_pointer_fixpoint_online_fanout_onepair(d, pi, pj)
     struct red_type	*d;
     int		pi, pj;
{
  int		       		vi, vj, ph, pk, ov;
  struct red_type		*reverse, *equal, *conj, *nonreverse, *subresult;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_SYMMETRY_POINTER_FIXPOINT_ONLINE_FANOUT_ONEPAIR, 
    d, NULL, pi, pj
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  else 
    return(d); 
    
  /* extract the reverse, nonreverse w.r.t. discrete variables. */
  reverse = red_bop(EXTRACT, d, DSC_REVERSE[pi][pj]);
  if (reverse != NORM_FALSE) {
    d = red_bop(EXCLUDE, d, reverse);
    reverse = red_pi_permute(reverse, SWITCH_PI, SWITCH_PJ);
    RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
  }
  nonreverse = red_bop(EXTRACT, d, DSC_REVERSE[pj][pi]);
  if (nonreverse != NORM_FALSE) {
    d = red_bop(EXCLUDE, d, nonreverse);
    RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], nonreverse);
  }
  if (d == NORM_FALSE)
    return(ce->result = NORM_FALSE);

  /* extract the reverse, nonreverse w.r.t. pointer global variables. */
  reverse = red_bop(EXTRACT, d, POINTER_GLOBAL_REVERSE[pi][pj]);
  if (reverse != NORM_FALSE) {
    d = red_bop(EXCLUDE, d, reverse);
    reverse = red_pi_permute(reverse, SWITCH_PI, SWITCH_PJ);
    RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
  }
  nonreverse = red_bop(EXTRACT, d, POINTER_GLOBAL_REVERSE[pj][pi]);
  if (nonreverse != NORM_FALSE) {
    d = red_bop(EXCLUDE, d, nonreverse);
    RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], nonreverse);
  }
  if (d == NORM_FALSE)
    return(ce->result = NORM_FALSE);

  for (ov = 0; d != NORM_FALSE && ov < LOCAL_COUNT[TYPE_POINTER]; ov++) {
    /* reverse:
       vo[pi] != NULL && vo[pj] == NULL
       vo[pj] == SWITCH_PJ && vo[pi] != SWITCH_PI && vo[pi] != NULL
       vo[pj] == SWITCH_PI && vo[pi] != SWITCH_PI && vo[pi] != SWITCH_PJ && vo[pi] != NULL
       vo[pj] != SWITCH_PJ && vo[pi] != SWITCH_PI && vo[pi] != SWITCH_PJ && vo[pi] != SWITCH_PI
         && vo[pj] != NULL && vo[pi] != NULL
         && rec(vo[pi], vo[pj])
     */
    /* vo[pi] != NULL && vo[pj] == NULL */
    vi = variable_index[TYPE_POINTER][pi][ov];
    vj = variable_index[TYPE_POINTER][pj][ov];
    reverse = ddd_one_constraint(d, vi, 1, PROCESS_COUNT);
    reverse = ddd_one_constraint(reverse, vj, 0, 0);
    if (reverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, reverse);
      reverse = red_pi_permute(reverse, SWITCH_PI, SWITCH_PJ);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
    }
    nonreverse = ddd_one_constraint(d, vi, 1, PROCESS_COUNT);
    nonreverse = ddd_one_constraint(nonreverse, vj, 0, 0);
    if (nonreverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, nonreverse);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], nonreverse);
    }

    if (d == NORM_FALSE)
      return(ce->result = NORM_FALSE);

    /* vo[pj] == SWITCH_PJ && vo[pi] != SWITCH_PI && vo[pi] != NULL */
    reverse = ddd_one_constraint(d, vj, SWITCH_PJ, SWITCH_PJ);
    reverse = ddd_one_constraint(reverse, vi, 1, PROCESS_COUNT);
    reverse = red_bop(SUBTRACT, reverse, ddd_atom(vi, SWITCH_PI, SWITCH_PI));
    if (reverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, reverse);
      reverse = red_pi_permute(reverse, SWITCH_PI, SWITCH_PJ);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
    }
    nonreverse = ddd_one_constraint(d, vi, SWITCH_PI, SWITCH_PI);
    nonreverse = ddd_one_constraint(nonreverse, vj, 1, PROCESS_COUNT);
    nonreverse = red_bop(SUBTRACT, nonreverse, ddd_atom(vj, SWITCH_PJ, SWITCH_PJ));
    if (nonreverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, nonreverse);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], nonreverse);
    }
    if (d == NORM_FALSE)
      return(ce->result = NORM_FALSE);

    /* vo[pj] == SWITCH_PI && vo[pi] != SWITCH_PI && vo[pi] != SWITCH_PJ && vo[pi] != NULL */
    reverse = ddd_one_constraint(d, vj, SWITCH_PI, SWITCH_PI);
    reverse = ddd_one_constraint(reverse, vi, 1, PROCESS_COUNT);
    reverse = red_bop(SUBTRACT, reverse, ddd_atom(vi, SWITCH_PI, SWITCH_PI));
    reverse = red_bop(SUBTRACT, reverse, ddd_atom(vi, SWITCH_PJ, SWITCH_PJ));
    if (reverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, reverse);
      reverse = red_pi_permute(reverse, SWITCH_PI, SWITCH_PJ);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
    }
    nonreverse = ddd_one_constraint(d, vi, SWITCH_PJ, SWITCH_PJ);
    nonreverse = ddd_one_constraint(nonreverse, vj, 1, PROCESS_COUNT);
    nonreverse = red_bop(SUBTRACT, nonreverse, ddd_atom(vj, SWITCH_PI, SWITCH_PI));
    nonreverse = red_bop(SUBTRACT, nonreverse, ddd_atom(vj, SWITCH_PJ, SWITCH_PJ));
    if (reverse != NORM_FALSE) {
      d = red_bop(EXCLUDE, d, reverse);
      RT[SYMMETRY_RESULT] = red_bop(OR, RT[SYMMETRY_RESULT], reverse);
    }
    if (d == NORM_FALSE)
      return(ce->result = NORM_FALSE);

    /* vo[pj] != SWITCH_PJ && vo[pi] != SWITCH_PI && vo[pi] != SWITCH_PJ && vo[pi] != SWITCH_PI
         && vo[pj] != NULL && vo[pi] != NULL
         && rec(vo[pi], vo[pj])
    */
    subresult = ddd_one_constraint(d, vi, 0, 0);
    subresult = ddd_one_constraint(subresult, vj, 0, 0);
    for (ph = 1; ph <= PROCESS_COUNT; ph++) {
      if (ph != SWITCH_PI && ph != SWITCH_PJ) {
        conj = ddd_one_constraint(d, vi, ph, ph);
	if (conj == NORM_FALSE)
	  continue;
        for (pk = 1; conj != NORM_FALSE && pk <= PROCESS_COUNT; pk++) {
	  if (pk != SWITCH_PI && pk != SWITCH_PJ && pk != ph) {
	    equal = ddd_one_constraint(conj, vj, pk, pk);
	    equal = rec_symmetry_pointer_fixpoint_online_fanout_onepair(equal, ph, pk);
	    subresult = red_bop(OR, subresult, equal);
	  }
	}
      }
    }
    d = subresult;
  }
  return(ce->result = d);
}
  /* rec_symmetry_pointer_fixpoint_online_fanout_onepair() */






struct red_type	*red_symmetry_pointer_fixpoint_online_fanout_onepair(w, pi, pj)
     int	w, pi, pj;
{
  struct red_type	*equal_fixpoint;

  SWITCH_PI = pi;
  SWITCH_PJ = pj;

  RT[SYMMETRY_RESULT = RT_TOP++] = NORM_FALSE;
  equal_fixpoint = rec_symmetry_pointer_fixpoint_online_fanout_onepair(RT[w], pi, pj);

  equal_fixpoint = red_bop(OR, RT[SYMMETRY_RESULT], equal_fixpoint);
  RT_TOP--; /* SYMMETRY_RESULT */
  return(equal_fixpoint);
}
/* red_symmetry_pointer_fixpoint_online_fanout_onepair() */


reduce_symmetry_pointer_fixpoint_online(w)
     int	w;
{
  int			flag_symmetry, pi, pj, dsc_boundary, dsc_oo;
  struct red_type	*cond;

  /*
  fprintf(RED_OUT, "\n=============================================\nBefore symmetry!\n");
  red_print_graph(RT[w]);
  probe(PROBE_PRERISK, "\nBefore symmetry probe\n", RT[NEW]);
  flag_symmetry = FALSE;
  */
  for (pi = 1; pi < PROCESS_COUNT; pi++)
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      RT[w] = red_symmetry_pointer_fixpoint_online_fanout_onepair(w, pi, pj);
      garbage_collect(FLAG_GC_SILENT);
    }

  /*
  probe(PROBE_PRERISK, "\nAfter symmetry probe\n", RT[w]);
  if (flag_symmetry) {
    fprintf(RED_OUT, "\n=================================\nSymmetry successful!\n");
    red_print_graph(RT[w]);
  }
  */
}
/* reduce_symmetry_pointer_fixpoint_online() */




/* This symmetry is based on the first local clocks.
*/
#define	VISITED		1
#define NOT_VISITED	0

int	ZCI, ZCJ, ZCI_LB, ZCI_UB, ZCIJ_LB, FLAG_ZCJ_LB, FLAG_ZCJ_UB; 
int	TS_ZONE_ONE_PAIR_REVERSE; 


struct red_type	*rec_zone_one_pair_reverse(d)
     struct red_type	*d;
{
  int		       		ci, cj;
  struct red_type		*result;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(NORM_FALSE); 

  result = NORM_FALSE; 
  if (VAR[d->var_index].TYPE != TYPE_CRD) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, NULL); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      result = red_bop(OR, result,
		       ddd_lone_subtree(rec_zone_one_pair_reverse(d->u.ddd.arc[ci].child),
					d->var_index, d->u.ddd.arc[ci].upper_bound, d->u.ddd.arc[ci].upper_bound
					)
		       );
    return(ce->result = result); 
  }  
  else if (d->var_index < ZONE[0][ZCI]) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, NULL); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      result = red_bop(OR, result,
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
					 d->var_index, d->u.crd.arc[ci].upper_bound
					 )
		       );
    return(ce->result = result); 
  }
  else if (d->var_index == ZONE[0][ZCI]) { 
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, NULL); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      ZCI_LB = d->u.crd.arc[ci].upper_bound;
      result = red_bop(OR, result, 
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
					 d->var_index, d->u.crd.arc[ci].upper_bound
					 )
		       ); 
    }
    ZCI_LB = CLOCK_POS_INFINITY; 

    return(ce->result = result); 
  }
  else if (d->var_index == ZONE[ZCI][0]) {
    ce = cache2_check_result_key(
      OP_ZONE_ONE_PAIR_REVERSE, d, (struct red_type *) ZCI_LB
    ); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      ZCI_UB = d->u.crd.arc[ci].upper_bound; 
      result = red_bop(OR, result,
        crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
			 d->var_index, d->u.crd.arc[ci].upper_bound
			 )
      );
    }
    ZCI_UB = CLOCK_POS_INFINITY;

    return(ce->result = result);
  }
  else if (d->var_index < ZONE[0][ZCJ]) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, 
      (struct red_type *) ((2*CLOCK_POS_INFINITY * ZCI_UB) + ZCI_LB)
    ); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      result = red_bop(OR, result,
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
					 d->var_index, d->u.crd.arc[ci].upper_bound
					 )
		       );
    return(ce->result = result); 
  }
  else if (d->var_index == ZONE[0][ZCJ]) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, 
      (struct red_type *) ((2*CLOCK_POS_INFINITY * ZCI_UB) + ZCI_LB)
    ); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (cj = d->u.crd.child_count-1; cj >= 0 && d->u.crd.arc[cj].upper_bound > ZCI_LB; cj--)
      result = red_bop(OR, result, 
		       crd_lone_subtree(d->u.crd.arc[cj].child,
					 d->var_index, d->u.crd.arc[cj].upper_bound
					 )
		       );

    FLAG_ZCJ_LB = VISITED; 
    if (cj >= 0 && d->u.crd.arc[cj].upper_bound == ZCI_LB) {
      result = red_bop(OR, result,
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[cj].child),
					 d->var_index, d->u.crd.arc[cj].upper_bound
					 )
		       ); 
    }
    FLAG_ZCJ_LB = NOT_VISITED; 
    return(ce->result = result);
  } 
  else if /* d->var_index > ZONE[0][ZCJ]*/ (FLAG_ZCJ_LB == NOT_VISITED && ZCI_LB < CLOCK_POS_INFINITY) {
    return(d);
  }
  else if (d->var_index == ZONE[ZCJ][0]) { 
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, 
      (struct red_type *) ZCI_UB
    ); 
    if (ce->result) {
      return(ce->result); 
    } 
    
    for (cj = 0; cj < d->u.crd.child_count && d->u.crd.arc[cj].upper_bound < ZCI_UB; cj++) 
      result = red_bop(OR, result,
		       crd_lone_subtree(d->u.crd.arc[cj].child,
      					 d->var_index, d->u.crd.arc[cj].upper_bound
					 )
		       ); 

    FLAG_ZCJ_UB = VISITED;
    if (cj < d->u.crd.child_count && d->u.crd.arc[cj].upper_bound == ZCI_UB) {
      result = red_bop(OR, result,
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[cj].child),
					 d->var_index, d->u.crd.arc[cj].upper_bound
					 )
		       ); 
    }
    FLAG_ZCJ_UB = NOT_VISITED; 
    return(ce->result = result);       
  } 
  else if /* d->var_index > ZONE[ZCJ][0] */ (FLAG_ZCJ_UB == NOT_VISITED && ZCI_UB < CLOCK_POS_INFINITY) 
    return(NORM_FALSE);
  else if (d->var_index < ZONE[ZCI][ZCJ]) { 
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, NULL); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      result = red_bop(OR, result, 
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
					 d->var_index, d->u.crd.arc[ci].upper_bound
					 )
		       ); 
    return(ce->result = result);     
  } 
  else if (d->var_index == ZONE[ZCI][ZCJ]) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, d, NULL); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      ZCIJ_LB = d->u.crd.arc[ci].upper_bound; 
      result = red_bop(OR, result, 
		       crd_lone_subtree(rec_zone_one_pair_reverse(d->u.crd.arc[ci].child),
					 d->var_index, d->u.crd.arc[ci].upper_bound
					 )
		       ); 
    }
    
    ZCIJ_LB = CLOCK_POS_INFINITY; 
    return(ce->result = result); 
  }
  else if (d->var_index == ZONE[ZCJ][ZCI]) {
    ce = cache2_check_result_key(OP_ZONE_ONE_PAIR_REVERSE, 
      d, (struct red_type *) ZCIJ_LB
    ); 
    if (ce->result) {
      return(ce->result); 
    } 

    for (cj = 0; cj < d->u.crd.child_count && d->u.crd.arc[cj].upper_bound < ZCIJ_LB; cj++) 
      result = red_bop(OR, result,
		       crd_lone_subtree(d->u.crd.arc[cj].child,
					 d->var_index, d->u.crd.arc[cj].upper_bound
					 )
		       ); 
    return(ce->result = result); 	
  } 
  else /* d->var_index > ZONE[ZCJ][ZCI] */ { 
    return(NORM_FALSE); 
  } 
}
  /* rec_zone_one_pair_reverse() */






red_zone_symmetry(w)
     int	w;
{
  int			pi, pj;
  struct red_type	*reverse;

  for (pi = 1; pi < PROCESS_COUNT; pi++)
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      ZCI = VAR[variable_index[TYPE_CLOCK][pi][0]].U.CLOCK.CLOCK_INDEX;
      ZCJ = VAR[variable_index[TYPE_CLOCK][pj][0]].U.CLOCK.CLOCK_INDEX;
      ZCI_LB = ZCI_UB = ZCIJ_LB = CLOCK_POS_INFINITY;
      FLAG_ZCJ_LB = FLAG_ZCJ_UB = NOT_VISITED;

      cache2_clear(OP_ZONE_ONE_PAIR_REVERSE); 
      reverse = rec_zone_one_pair_reverse(RT[w]);

      if (reverse != NORM_FALSE) {
	/*
	fprintf(RED_OUT, "\n---------------------------------------\nBefore symmetry reduction on pi=%1d, pj =%1d:\n",
		pi, pj
		);
	red_print_graph(reverse);
	*/
	RT[w] = red_bop(EXCLUDE, RT[w], reverse);
	reverse = red_pi_permute(reverse, pi, pj);
	/*
	fprintf(RED_OUT, "\n\nAfter symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj);
	red_print_graph(reverse);
	*/
	RT[w] = red_bop(OR, RT[w], reverse);
      }
      garbage_collect(FLAG_GC_SILENT);
    }

}
/* red_zone_symmetry() */



reduce_zone_symmetry(w)
     int	w;
{
  int			pi, pj, dsc_oo;
  struct red_type	*reverse;
  /*
  fprintf(RED_OUT, "\nSymmetry request!\n");
  red_print_graph(RT[w]);
  */
  for (pi = 1; pi < PROCESS_COUNT; pi++)
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      RT[dsc_oo = RT_TOP++] = red_bop(EXTRACT, RT[w], PROCESS_REVERSE[pi][pj]);
      if (RT[dsc_oo] != NORM_FALSE) {
	RT[w] = red_bop(EXCLUDE, RT[w], RT[dsc_oo]);
	/*
	fprintf(RED_OUT, "\n---------------------------------------\nBefore dsc symmetry reduction on pi=%1d, pj =%1d:\n",
		pi, pj
		);
	red_print_graph(RT[dsc_oo]);
	*/
	RT[dsc_oo] = red_pi_permute(RT[dsc_oo], pi, pj);
	/*
	  fprintf(RED_OUT, "\n\nAfter dsc symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj);
	red_print_graph(RT[dsc_oo]);
	*/
      }

      if (LOCAL_COUNT[TYPE_CLOCK]) {
	reverse = red_bop(EXTRACT, RT[w], PROCESS_EQUAL[pi][pj]);
	if (reverse != NORM_FALSE) {

	  ZCI = VAR[variable_index[TYPE_CLOCK][pi][0]].U.CLOCK.CLOCK_INDEX;
	  ZCJ = VAR[variable_index[TYPE_CLOCK][pj][0]].U.CLOCK.CLOCK_INDEX;
	  ZCI_LB = ZCI_UB = ZCIJ_LB = CLOCK_POS_INFINITY;
	  FLAG_ZCJ_LB = FLAG_ZCJ_UB = NOT_VISITED;

          cache2_clear(OP_ZONE_ONE_PAIR_REVERSE); 
	  reverse = rec_zone_one_pair_reverse(reverse);
	  if (reverse != NORM_FALSE) {
	    /*
	    fprintf(RED_OUT, "\n-------------------------------------\nBefore zone symmetry reduction on pi=%1d, pj =%1d:\n",
		    pi, pj
		    );
	    red_print_graph(reverse);
	    */
	    RT[w] = red_bop(EXCLUDE, RT[w], reverse);
	    reverse = red_pi_permute(reverse, pi, pj);
	    /*
	    fprintf(RED_OUT, "\n\nAfter zone symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj);
	    red_print_graph(reverse);
	    */
	    RT[w] = red_bop(OR, RT[w], reverse);
	  }
	  garbage_collect(FLAG_GC_SILENT);
	}
      }
      RT[w] = red_bop(OR, RT[w], RT[dsc_oo]);
      RT_TOP--; /* dsc_oo */

      garbage_collect(FLAG_GC_SILENT);
    }
  /*
  fprintf(RED_OUT, "\n********************************************************\nSymmetry successful!\n");
  red_print_graph(RT[w]);
  */

}
/* reduce_zone_symmetry() */




int	SYMCI; 

struct red_type	*rec_clock_dependent(d)
     struct red_type	*d; 
{
  struct red_type		*conj, *result;
  int				ci; 
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic; 
  struct cache2_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) 
    return(NORM_FALSE);

  ce = cache2_check_result_key(
    OP_CLOCK_DEPENDENT, d, (struct red_type *) SYMCI
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD:  
    if (   VAR[d->var_index].U.CRD.CLOCK1 == SYMCI 
        || VAR[d->var_index].U.CRD.CLOCK2 == SYMCI
        ) 
      return(ce->result = d); 

    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      conj = rec_clock_dependent(bc->child); 
      conj = red_bop(AND, conj, crd_atom(d->var_index, bc->upper_bound)); 
      result = red_bop(OR, result, conj);
    }
    break; 
  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = rec_clock_dependent(d->u.fdd.arc[ci].child); 
      conj = fdd_one_constraint(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break;
  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = rec_clock_dependent(d->u.dfdd.arc[ci].child); 
      conj = dfdd_one_constraint(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, conj); 
    }
    break;
  default: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      ic = &(d->u.ddd.arc[ci]); 
      conj = rec_clock_dependent(ic->child); 
      conj = red_bop(AND, conj, 
      		     ddd_atom(d->var_index, ic->lower_bound, ic->upper_bound)
      		     ); 
      result = red_bop(OR, result, conj); 
    }
    break;
  }
  return(ce->result = result); 
}
/* rec_order_check() */




  /* It is assumed that pi < pj */ 
struct red_type	*red_clock_dependent(d, ci) 
     struct red_type	*d; 
     int		ci; 
{
  struct red_type	*result; 

  SYMCI = ci;
  result = rec_clock_dependent(d); 

  return(result);
}
/* red_clock_dependent() */




reduce_state_symmetry(w)
	int	w;
{
  int			pi, pj, lci, lcj, vi, vj, ci, cj, result;
  struct red_type	*reverse, *ci_dependent, *cj_dependent, *both_dependent;

  fprintf(RED_OUT, "\n**(I=%1d)******************************************\n",
	  ITERATION_COUNT
	  );
  fprintf(RED_OUT, "Symmetry request!\n");
  red_print_graph(RT[w]);

  for (pi = 1; pi < PROCESS_COUNT; pi++) {
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      RT[result = RT_TOP++] = NORM_FALSE;
      reverse = red_bop(EXTRACT, RT[w], PROCESS_REVERSE[pi][pj]);
      if (reverse != NORM_FALSE) {
	RT[w] = red_bop(EXCLUDE, RT[w], reverse);
	/*
	fprintf(RED_OUT, "\n---------------------------------------\nBefore dsc symmetry reduction on pi=%1d, pj =%1d:\n",
		pi, pj
		);
	red_print_graph(RT[dsc_oo]);
	*/
	reverse = red_pi_permute(reverse, pi, pj);
	/*
	  fprintf(RED_OUT, "\n\nAfter dsc symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj);
	red_print_graph(RT[dsc_oo]);
	*/
	RT[result] = red_bop(OR, RT[result], reverse);
      }

      if (!LOCAL_COUNT[TYPE_CLOCK]) {
      	RT[w] = red_bop(OR, RT[w], RT[result]);
      	RT_TOP--;
      	continue;
      }

      reverse = red_bop(EXTRACT, RT[w], PROCESS_EQUAL[pi][pj]);
      if (reverse == NORM_FALSE) {
      	RT[w] = red_bop(OR, RT[w], RT[result]);
      	RT_TOP--;
      	continue;
      }

      RT[w] = red_bop(EXCLUDE, RT[w], reverse);
      RT[result] = red_bop(OR, RT[result], RT[w]);
      RT[w] = reverse;

      for (lci = 0; lci < LOCAL_COUNT[TYPE_CLOCK]; lci++) {
      	vi = variable_index[TYPE_CLOCK][pi][lci];
      	ci = VAR[vi].U.CLOCK.CLOCK_INDEX;
	for (lcj = 0; lcj < LOCAL_COUNT[TYPE_CLOCK]; lcj++) {
	  ci_dependent = red_clock_dependent(RT[w], ci);

      	  vj = variable_index[TYPE_CLOCK][pj][lcj];
      	  cj = VAR[vj].U.CLOCK.CLOCK_INDEX;
	  cj_dependent = red_clock_dependent(RT[w], cj);

	  RT[w] = red_bop(EXCLUDE, RT[w], ci_dependent);
	  RT[w] = red_bop(EXCLUDE, RT[w], cj_dependent);

	  RT[result] = red_bop(OR, RT[result],
	  		       red_bop(EXCLUDE, ci_dependent,
	  			       cj_dependent
	  			       )
	  		       );
	  RT[result] = red_bop(OR, RT[result],
	  		       red_pi_permute(red_bop(EXCLUDE, cj_dependent,
	  		       			      ci_dependent
	  		       			      ),
	  		       		      pi, pj
	  		       		      )
	  		       );

	  both_dependent = red_bop(INTERSECT, ci_dependent, cj_dependent);
	  RT[result] = red_bop(OR, RT[result],
	  		       red_bop(AND, both_dependent,
	  		    	       crd_atom(ZONE[ci][cj], 0)
	  			       )
	  		       );
	  RT[result] = red_bop(OR, RT[result],
	  		       red_pi_permute(red_bop(AND, both_dependent,
	  		    			      crd_atom(ZONE[cj][ci], 0)
	  		    			      ),
	  		    		      pi, pj
	  		    		      )
	  		       );
      	}
      }
      RT[w] = red_bop(OR, RT[w], RT[result]);
      RT_TOP--; /* result */

      garbage_collect(FLAG_GC_SILENT);
    }
  }

  fprintf(RED_OUT, "\n********************************************************\n");
  fprintf(RED_OUT, "Symmetry successful!\n");
  red_print_graph(RT[w]);

}
/* reduce_state_symmetry() */






reduce_state_total_symmetry(w)
	int	w;
{
  int			pi, pj, lci, lcj, vi, vj, ci, cj, result;
  struct red_type	*reverse, *ci_dependent, *cj_dependent, *both_dependent;

  fprintf(RED_OUT, "\n**(I=%1d)******************************************\n",
	  ITERATION_COUNT
	  );
  fprintf(RED_OUT, "Symmetry request!\n");
  red_print_graph(RT[w]);

  for (pi = 1; pi < PROCESS_COUNT; pi++) {
    for (pj = pi+1; pj <= PROCESS_COUNT; pj++) {
      RT[result = RT_TOP++] = NORM_FALSE;
      reverse = red_bop(EXTRACT, RT[w], PROCESS_REVERSE[pi][pj]); 
      if (reverse != NORM_FALSE) { 
	RT[w] = red_bop(EXCLUDE, RT[w], reverse); 
	/* 
	fprintf(RED_OUT, "\n---------------------------------------\nBefore dsc symmetry reduction on pi=%1d, pj =%1d:\n", 
		pi, pj
		); 
	red_print_graph(RT[dsc_oo]); 
	*/
	reverse = red_pi_permute(reverse, pi, pj); 
	/* 
	  fprintf(RED_OUT, "\n\nAfter dsc symmetry reduction on pi=%1d, pj =%1d:\n", pi, pj); 
	red_print_graph(RT[dsc_oo]); 
	*/ 
	RT[result] = red_bop(OR, RT[result], reverse); 
      } 
      
      if (!LOCAL_COUNT[TYPE_CLOCK]) {
      	RT[w] = red_bop(OR, RT[w], RT[result]); 
      	RT_TOP--; 
      	continue; 
      } 
      
      reverse = red_bop(EXTRACT, RT[w], PROCESS_EQUAL[pi][pj]); 
      if (reverse == NORM_FALSE) {
      	RT[w] = red_bop(OR, RT[w], RT[result]); 
      	RT_TOP--;
      	continue; 	
      } 
      
      RT[w] = red_bop(EXCLUDE, RT[w], reverse); 
      RT[result] = red_bop(OR, RT[result], RT[w]);
      RT[w] = reverse; 
      
      for (lci = 0; lci < LOCAL_COUNT[TYPE_CLOCK]; lci++) { 
      	vi = variable_index[TYPE_CLOCK][pi][lci]; 
      	ci = VAR[vi].U.CLOCK.CLOCK_INDEX; 
	for (lcj = 0; lcj < LOCAL_COUNT[TYPE_CLOCK]; lcj++) { 
	  ci_dependent = red_clock_dependent(RT[w], ci); 
	  
      	  vj = variable_index[TYPE_CLOCK][pj][lcj];
      	  cj = VAR[vj].U.CLOCK.CLOCK_INDEX; 
	  cj_dependent = red_clock_dependent(RT[w], cj); 

	  RT[w] = red_bop(EXCLUDE, RT[w], ci_dependent); 
	  RT[w] = red_bop(EXCLUDE, RT[w], cj_dependent); 
	  
	  RT[result] = red_bop(OR, RT[result], 
	  		       red_bop(EXCLUDE, ci_dependent, 
	  			       cj_dependent
	  			       )
	  		       ); 
	  RT[result] = red_bop(OR, RT[result], 
	  		       red_pi_permute(red_bop(EXCLUDE, cj_dependent, 
	  		       			      ci_dependent
	  		       			      ), 
	  		       		      pi, pj
	  		       		      )
	  		       ); 
	  		       
	  both_dependent = red_bop(INTERSECT, ci_dependent, cj_dependent); 
	  RT[result] = red_bop(OR, RT[result], 
	  		       red_bop(AND, both_dependent, 
	  		    	       crd_atom(ZONE[ci][cj], -1)
	  			       )
	  		       ); 	
	  RT[result] = red_bop(OR, RT[result], 
	  		       red_pi_permute(red_bop(AND, both_dependent, 
	  		    			      crd_atom(ZONE[cj][ci], -1) 
	  		    			      ), 
	  		    		      pi, pj
	  		    		      )
	  		       );
	  RT[w] = red_bop(OR, RT[w], 
	  		  red_bop(AND, both_dependent, 
	  		  	  red_bop(AND, 
	  		  	  	  crd_atom(ZONE[ci][cj], 0), 
	  		  	  	  crd_atom(ZONE[cj][ci], 0)
	  		  	  	  ) 
	  		  	  )
	  		  ); 
      	}
      } 
      RT[w] = red_bop(OR, RT[w], RT[result]);
      RT_TOP--; /* result */

      garbage_collect(FLAG_GC_SILENT);
    }
  }

  fprintf(RED_OUT, "\n********************************************************\n");
  fprintf(RED_OUT, "Symmetry successful!\n");
  red_print_graph(RT[w]);

}
/* reduce_state_symmetry() */




void	reduce_symmetry(w)
	int	w;
{
  switch (GSTATUS[INDEX_SYMMETRY] & MASK_SYMMETRY) {
  case FLAG_SYMMETRY_POINTER_FIXPOINT_OFFLINE:
  case FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE:
  case FLAG_SYMMETRY_DISCRETE_GENERAL: 
    reduce_symmetry_offline(w);
    break;
  case FLAG_SYMMETRY_POINTER_FIXPOINT_ONLINE:
    reduce_symmetry_pointer_fixpoint_online(w);
    break;
  case FLAG_SYMMETRY_ZONE:
    reduce_zone_symmetry(w);
    /*
      print_cpu_time("after zone symmetry");
      red_print_graph(RT[path]);
    */
    break;
  case FLAG_SYMMETRY_STATE:
    reduce_state_symmetry(w);
	  /*
	  print_cpu_time("after zone symmetry");
	  red_print_graph(RT[path]);
	  */
    break;
  }
}
  /* reduce_symmetry() */


