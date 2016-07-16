#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include "redbasics.h"
#include "redbasics.e"

#include "redstring.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "vindex.e"

#include "redbop.h"
#include "redbop.e"

#include "zone.h"  
#include "zone.e" 
#include "zapprox.e"

#include "redparse.h" 
#include "redparse.e"

#include "exp.e" 

#include "fxp.h"
#include "fxp.e"

#include "action.e"

#include "pointer.e" 

#include "redsymmetry.e" 

#include "inactive.e"

#include "hybrid.e"


struct red_type	**COUNTER_PATH; 
int		COUNTER_PATH_TOP = -1, COUNTER_PATH_LIMIT = 99; 

int	*pia, *xia; 

void	init_counter_example_management() { 
  COUNTER_PATH_LIMIT = 99; 
  COUNTER_PATH_TOP = -1; 
  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
    int	i;

    COUNTER_PATH = (struct red_type **) 
      malloc((COUNTER_PATH_LIMIT+1)*sizeof(struct red_type *)); 
    for (i = 0; i <= COUNTER_PATH_LIMIT; i++)
      COUNTER_PATH[i] = NULL; 
      
    pia = (int *) malloc(PROCESS_COUNT * sizeof(int));
    xia = (int *) malloc(PROCESS_COUNT * sizeof(int));
  }
  else { 
    pia = NULL; 
    xia = NULL; 	
  } 
}
/* init_counter_example_management() */ 



void	conditional_init_counter_example_management() { 
  if (   (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE)
      && !pia
      ) {
    int	i;

    COUNTER_PATH_LIMIT = 99; 
    COUNTER_PATH_TOP = -1; 
    COUNTER_PATH = (struct red_type **) 
      malloc((COUNTER_PATH_LIMIT+1)*sizeof(struct red_type *)); 
    for (i = 0; i <= COUNTER_PATH_LIMIT; i++)
      COUNTER_PATH[i] = NULL; 
      
    pia = (int *) malloc(PROCESS_COUNT * sizeof(int));
    xia = (int *) malloc(PROCESS_COUNT * sizeof(int));
  }
}
/* conditional_init_counter_example_management() */ 



void	free_counter_example_record() { 
  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) {
    int	i;

    for (i = 0; i <= COUNTER_PATH_TOP; i++)
      COUNTER_PATH[i] = NULL; 
    COUNTER_PATH_TOP = -1; 
    free(pia); 
    free(xia); 
    pia = NULL; 
    xia = NULL; 
  }
}
/* free_counter_example_record() */ 



void	print_counter_example(goal_name, cl) 
	char					*goal_name; 
	struct counter_example_node_type	*cl; 
{ 
  int	cs, // index to the current stage 
	pti; // index to the party in exit sync transitions. 
  
  if (cl == NULL) {
    fprintf(RED_OUT, "\n========================\nNull counter example! \n");
    return; 
  }
  
  fprintf(RED_OUT, "\n========================\nCounter example: \n");
  for (cs = 0; 
       cl->next_counter_example_node; 
       cs++, cl = cl->next_counter_example_node
       ) {
    int	pti; // index to the party in exit sync transitions. 
  
    fprintf(RED_OUT, "--------------------\nState %1d:\n", cs);
    red_print_line_break(cl->prestate);
    fprintf(RED_OUT, "\n---------------\n  |\n");
    fflush(RED_OUT);
    for (pti = 0; pti < cl->exit_sync_xtion_party_count; pti++) {
      fprintf(RED_OUT, "  | pi=%1d,xi=%1d:", 
        cl->exit_sync_xtion_party[pti].proc, 
        cl->exit_sync_xtion_party[pti].xtion  
      );
      print_xtion_line(
        cl->exit_sync_xtion_party[pti].xtion, 
        cl->exit_sync_xtion_party[pti].proc
      );
      fprintf(RED_OUT, "\n");
    }
    fprintf(RED_OUT, "  |\n  |\n  V\n");
    fflush(RED_OUT);
  }

  fprintf(RED_OUT, "--------------------\nState %1d, the %s state:\n", 
    cs, goal_name
  ); 
  red_print_line_break(cl->prestate);

  fprintf(RED_OUT, "\n\n");
  fflush(RED_OUT);
}
  /* print_counter_example() */ 
  
  


// It is assumed that the event and state order in array counter 
// is already in forward temporal order. 
struct counter_example_node_type	*construct_counter_example( 
  struct path_xtion_type	*counter 
) { 
  struct counter_example_node_type	*cl, dummy_cl, *tail_cl; 
  int					current_stage, pos; 

  dummy_cl.next_counter_example_node = NULL; 
  tail_cl = &dummy_cl; 
  for (current_stage = 0; 
       current_stage < COUNTER_PATH_TOP; 
       current_stage++
       ) {
    int	pti, pi, xi, total_statements; 

    cl = (struct counter_example_node_type *) 
      malloc(sizeof(struct counter_example_node_type)); 
    tail_cl->next_counter_example_node = cl; 
    tail_cl = cl; 
    
    cl->prestate = counter[current_stage].prestate; 
    cl->exit_sync_xtion_party_count = counter[current_stage].party_count; 
    cl->exit_sync_xtion_party = (struct counter_example_party_type *) 
      malloc(cl->exit_sync_xtion_party_count
             *sizeof(struct counter_example_party_type)
             ); 
    for (pti = 0; pti < counter[current_stage].party_count; pti++) { 
      cl->exit_sync_xtion_party[pti].xtion 
      = counter[current_stage].xi[pti]; 
      cl->exit_sync_xtion_party[pti].proc 
      = counter[current_stage].pi[pti]; 
    }
    
    /* Now construct the string for the sync xtion. 
     * First, we construct the string for the conjunction of the triggering 
     * conditions of the party transitions. 
     */ 
    pos = 0; 
    sprintf(&(sbuf[pos]), "when (("); 
    pos = pos+7; 
/*
    fprintf(RED_OUT, "\nIn construct counter:\n"); 
    fprintf(RED_OUT, "counter[current_stage=%1d].xi=%x, [0]=%1d\n", 
      current_stage, counter[current_stage].xi, 
      counter[current_stage].xi[0]
    ); 
    fprintf(RED_OUT, "counter[current_stage=%1d].pi=%x, [0]=%1d\n", 
      current_stage, counter[current_stage].pi, 
      counter[current_stage].pi[0]
    ); 
    fflush(RED_OUT); 
*/
    xi = counter[current_stage].xi[0]; 
    pi = counter[current_stage].pi[0]; 
/*
    flag_debug_string_diagram = 1; 
    pos = rec_string_diagram(XTION[xi].red_trigger[pi], pos); 
*/
    pos = rec_string_parse_subformula(
      XTION[xi].parse_xtion->trigger_exp, pos, NULL
    );
    for (pti = 1; pti < counter[current_stage].party_count; pti++) { 
      xi = counter[current_stage].xi[pti]; 
      pi = counter[current_stage].pi[pti]; 
      sprintf(&(sbuf[pos]), ")&&("); pos = pos + 4; 
/*
      pos = rec_string_diagram(XTION[xi].red_trigger[pi], pos); 
*/
      pos = rec_string_parse_subformula(
        XTION[xi].parse_xtion->trigger_exp, pos, NULL
      );
    }
    sprintf(&(sbuf[pos]), ")) may "); 
    // Second, we construct the string for the actions. 
    pos = pos + 7; 
    for (pti = 0; pti < counter[current_stage].party_count; pti++) { 
      xi = counter[current_stage].xi[pti]; 
      pi = counter[current_stage].pi[pti]; 
      PI_STRING = pi; 
      PI_LENGTH = intlen(pi); 
      pos = rec_string_statement(XTION[xi].statement, pos); 
    }
    sbuf[pos] = '\0'; 
    cl->exit_sync_xtion_string = malloc(pos + 1); 
    sprintf(cl->exit_sync_xtion_string, "%s", sbuf); 
  } 
  cl = (struct counter_example_node_type *) 
    malloc(sizeof(struct counter_example_node_type)); 
  cl->exit_sync_xtion_party_count = 0; 
  cl->exit_sync_xtion_party = NULL; 
  cl->exit_sync_xtion_string = NULL; 
  cl->prestate = counter[COUNTER_PATH_TOP].prestate; 
  tail_cl->next_counter_example_node = cl; 
  cl->next_counter_example_node = NULL; 
  return(dummy_cl.next_counter_example_node); 
}
  /* construct_counter_example() */ 
  
  
  
  
void	add_counter_path( 
  struct red_type	*d, 
  int			it
) { 
  if (it == COUNTER_PATH_LIMIT) { 
    struct red_type	**new_counter_path;
    int			i;

    new_counter_path = (struct red_type **) malloc((COUNTER_PATH_LIMIT+100)*sizeof(struct red_type *));
    for (i = 0; i < COUNTER_PATH_LIMIT; i++)
      new_counter_path[i] = COUNTER_PATH[i];
    for (; i< COUNTER_PATH_LIMIT+100; i++)
      new_counter_path[i] = NULL;
    COUNTER_PATH_LIMIT = COUNTER_PATH_LIMIT+100;
    free(COUNTER_PATH);
    COUNTER_PATH = new_counter_path;
  }

  if (it > COUNTER_PATH_TOP) 
    COUNTER_PATH_TOP = it; 
  COUNTER_PATH[it] = d;
  red_mark(d, FLAG_GC_STABLE);
}
/* add_counter_path() */


  
struct red_type	*locate_one_instance(
     struct red_type		*d, 
     struct path_xtion_type	*counter, 
     int			current_stage
) {
  struct index_pair_link_type	*pixil, *pixi_list;
  struct red_type		*result;
  int				ci, pc;
  /*
  fprintf(RED_OUT, "\nIn locate an instance() with d:\n");
  red_print_graph(d);
  */
  if (d == NORM_FALSE)
    return(d);

  pc = 0;
  result = NORM_NO_RESTRICTION;
  pixi_list = NULL;

  for (; d != NORM_NO_RESTRICTION; ) {
    switch (VAR[d->var_index].TYPE) {
    case TYPE_XTION_INSTANCE:
      ci = d->u.ddd.child_count-1;
      if (d->u.ddd.arc[ci].upper_bound) {
	pc++;
	pixi_list = add_index_pair(pixi_list, VAR[d->var_index].PROC_INDEX, 
				   d->u.ddd.arc[ci].upper_bound
				   );
      }
      d = d->u.ddd.arc[d->u.ddd.child_count-1].child;
      break;
    case TYPE_CRD:
      ci = d->u.crd.child_count-1;
      result = crd_one_constraint(
      	result, d->var_index, d->u.crd.arc[ci].upper_bound
      );
      d = d->u.crd.arc[d->u.crd.child_count-1].child;
      break;
    case TYPE_HRD:
      ci = d->u.hrd.child_count-1;
      result = hrd_one_constraint(result, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      d = d->u.hrd.arc[d->u.hrd.child_count-1].child;
      break; 
    case TYPE_FLOAT: 
      ci = d->u.fdd.child_count-1;
      result = fdd_one_constraint(result, 
        d->var_index, 
        d->u.fdd.arc[ci].upper_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      d = d->u.fdd.arc[d->u.fdd.child_count-1].child;
      break; 
    case TYPE_DOUBLE: 
      ci = d->u.dfdd.child_count-1;
      result = dfdd_one_constraint(result, 
        d->var_index, 
        d->u.dfdd.arc[ci].upper_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      d = d->u.dfdd.arc[d->u.dfdd.child_count-1].child;
      break; 
    default: 
      ci = d->u.ddd.child_count-1;
      result = ddd_one_constraint(result, 
        d->var_index, 
        d->u.ddd.arc[ci].upper_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      d = d->u.ddd.arc[d->u.ddd.child_count-1].child;
    }
  }

  if (pc) {
    counter[current_stage].party_count = pc;
    counter[current_stage].pi = (int *) malloc(pc * sizeof(int));
    counter[current_stage].xi = (int *) malloc(pc * sizeof(int));
    for (ci = 0, pixil = pixi_list; pixil; ci++, pixil = pixil->next_index_pair_link) {
      counter[current_stage].pi[ci] = pixil->index1;
      counter[current_stage].xi[ci] = pixil->index2;
    }
  }

  free_index_pair_list(pixi_list);

  return(result);
}
/* locate_one_instance() */ 






int	locate_one_weakest_precondition_sync_ITERATIVE( 
  struct path_xtion_type	*counter,   
  int				current_stage 
) {
  int	sxi, xi, pi, i, ai, ci, api, flag, ipi; 

  /*
    flag_activeness = FLAG_CLOCK_UNKNOWN; 
  */

  for (sxi = 1; sxi < SYNC_XTION_COUNT; sxi++) {
    int cur_sxi;

    RT[cur_sxi = RT_TOP++] = counter[current_stage+1].prestate;
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) {
      int pi;

      /* Since the null xtion is not generated, we start from 0. */
      pi = SYNC_XTION[sxi].party[ipi].proc;
      xi = SYNC_XTION[sxi].party[ipi].xtion; 
      /*
      fprintf(RED_OUT, "\n=========================================\nIteration %1d, before xtion xi = %1d; pi = %1d; at RT_TOP = %1d\n",
	      ITERATION_COUNT, xi, pi, RT_TOP
	      );
      */
      /*
      fprintf(RED_OUT, "ITERATION %1d, before reverse actions , xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi);
      print_cpu_time("before reverse actions");
      red_print_graph(RT[cur_pi]);
      */
      RT[cur_sxi] = red_statement_bck(
        cur_sxi, pi, SYNC_XTION[sxi].party[ipi].statement, 
        GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
        FLAG_ACTION_DELAYED_EVAL 
      );
      /*
      fprintf(RED_OUT, "ITERATION %1d, After reverse actions, xi=%1d, pi=%1d:\n", ITERATION_COUNT, xi, pi);
      print_cpu_time("after reverse actions");
      red_print_graph(RT[cur_pi]);
      */
      if (RT[cur_sxi] == NORM_FALSE) {
        continue;
      }
    }
    if (RT[cur_sxi] == NORM_FALSE) {
      RT_TOP--; // cur_sxi 
      continue;
    }
    RT[cur_sxi] = red_delayed_eval(SYNC_XTION[sxi].red_trigger,
      PROC_GLOBAL, 
      RT[cur_sxi]
    );
    if (RT[cur_sxi] == NORM_FALSE) {
      RT_TOP--; // cur_sxi
      continue;
    }

    /*
      fprintf(RED_OUT, "ITERATION %1d, after reverse triggering, xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi);
      print_cpu_time("after reverse triggering");
      red_print_graph(RT[cur_pi]);
     */
    RT[cur_sxi] = red_eliminate_all_qfd_sync(RT[cur_sxi]); 
    RT[cur_sxi] = red_bop(AND, RT[cur_sxi], RT[REFINED_GLOBAL_INVARIANCE]);
    RT[cur_sxi] = inactive_variable_eliminate(cur_sxi);
    /*
    fprintf(RED_OUT, "ITERATION %1d, after all global inactive elimination, xi=%1d\n", ITERATION_COUNT, xi);
    print_cpu_time("after a global inactive elimination");
    red_print_graph(RT[cur_sxi]);
    */

    if (CLOCK_COUNT > 1) {
      RT[cur_sxi] = red_game_time_progress_bck(
        NULL, cur_sxi, 
        REFINED_GLOBAL_INVARIANCE, MASK_GAME_ROLES, 
        TYPE_TRUE 
      );
      /*
	fprintf(RED_OUT, "ITERATION %1d, after all hull saturation, xi=%1d\n", ITERATION_COUNT, xi);
	print_cpu_time("after all hull saturation");
	red_print_graph(RT[cur_sxi]);
	*/
      RT[cur_sxi] = red_bop(AND, RT[cur_sxi], RT[REFINED_GLOBAL_INVARIANCE]);
      /*
	fprintf(RED_OUT, "ITERATION %1d, after last all global invariancing, xi=%1d\n", ITERATION_COUNT, xi);
	print_cpu_time("after last global invariancing");
	red_print_graph(RT[cur_sxi]);
       */
    }
    RT[cur_sxi] = red_abs_game(RT[cur_sxi], GSTATUS[INDEX_APPROX]); 
    RT[cur_sxi] = red_bop(AND, RT[cur_sxi], COUNTER_PATH[current_stage]);
    RT[cur_sxi] = red_subsume(RT[cur_sxi]);

    reduce_symmetry(cur_sxi);

    if (CLOCK_COUNT > 1) {
      RT[cur_sxi] = red_hull_normalize(cur_sxi);
    }
    if (RT[cur_sxi] != NORM_FALSE) {
// In locate_one_weakest_precondition(counter, current_stage) 
      counter[current_stage].prestate 
      = locate_one_instance(RT[cur_sxi], counter, current_stage);
      RT_TOP--; // cur_sxi
      red_mark(counter[current_stage].prestate, FLAG_GC_STABLE);

/*
      fprintf(RED_OUT, "\n==[pi=%1d,xi=%1d]=============\n", pi, xi); 
      red_print_graph(COUNTER_PATH[current_stage]); 
*/
      counter[current_stage].party_count = SYNC_XTION[sxi].party_count; 
      counter[current_stage].pi 
      = (int *) malloc(SYNC_XTION[sxi].party_count * sizeof(int)); 
      counter[current_stage].xi 
      = (int *) malloc(SYNC_XTION[sxi].party_count * sizeof(int)); 

      for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) {
        counter[current_stage].pi[ipi] = SYNC_XTION[sxi].party[ipi].proc;
        counter[current_stage].xi[ipi] = SYNC_XTION[sxi].party[ipi].xtion; 
      }

      return(TYPE_TRUE);
    }

    RT_TOP--; // cur_sxi 
    garbage_collect(FLAG_GC_SILENT);
  }

  /*
    probe(PROBE_PRERISK3, "test the risk after saturation", RT[cur_xi]);
  */
  /*
    print_cpu_time("Leaving sync_bulk_xtion()");
  */
  return(TYPE_FALSE); 
}
/* locate_one_weakest_precondition_sync_ITERATIVE() */







locate_one_weakest_precondition_sync_bulk(counter, current_stage)
     struct path_xtion_type	*counter;
     int			current_stage;
{
  int	cur_mi, explore, urgent, pi, flag, cur_pi, fxi, ci, xi, cur_xi, ai, ixi;

  /*
  print_cpu_time("Entering sync_bulk_xtion()"); 
  report_red_management();
  */
  counter[current_stage].party_count = 0;

  RT[explore = RT_TOP++] 
  = red_bop(AND, counter[current_stage+1].prestate,
  	    RT[XI_SYNC_BULK_WITH_POSTCONDITION]
  	    );
  /*
  firable_xtion = (int *) malloc((XTION_COUNT+1)*sizeof(int));
  */
  get_all_firable_xtions(explore, MASK_GAME_ROLES);
  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;
/*
    get_firable_xtions(pi, explore);
*/
    for (ixi = 0;
            current_firable_xtion[pi][ixi] != -1
         && ixi < PROCESS[pi].firable_xtion_count;
         ixi++
         ) {
      xi = current_firable_xtion[pi][ixi];
      RT[cur_xi = RT_TOP++] = red_bop(EXTRACT, RT[explore], ddd_atom(fxi, xi, xi));

      /*
      fprintf(RED_OUT, "==========================================================================\n");
      fprintf(RED_OUT, "IITERATIN %1d, before reverse action, xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi);
      print_cpu_time("before reverse action");
      red_print_graph(RT[cur_xi]);
      fflush(RED_OUT);
      */
      if (RT[cur_xi] == NORM_FALSE) {
        RT_TOP--;
        continue;
      }

      if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) )
          || (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC)
          ) 
        RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi);

      if (xi) {
        RT[cur_xi] = red_statement_bck(
          cur_xi, pi, XTION[xi].statement, 
          GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
          FLAG_ACTION_DELAYED_EVAL  
        ); 
	/*
	print_cpu_time("after reverse action"); 
	red_print_graph(RT[cur_xi]);
	fflush(RED_OUT); 
	*/
        if (RT[cur_xi] == NORM_FALSE) {
          RT_TOP--; // cur_xi 
          continue;
        }
        if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                  & FLAG_BULK_TRIGGER_ACTION_INTERFERE
                ) ) 
            || (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
            ) {
          if (valid_mode_index(XTION[xi].src_mode_index)) 
            RT[cur_xi] = red_bop(AND, RT[cur_xi], 
                                 MODE[XTION[xi].src_mode_index].invariance[pi].red
                                 );
          RT[cur_xi] = red_bop(AND, RT[cur_xi], XTION[xi].red_trigger[pi]); 
	  /*
	  fprintf(RED_OUT, "I:%1d, after reverse triggering local invariance, xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi); 
	  print_cpu_time("after reverse triggering and local invariance"); 
	  red_print_graph(RT[cur_xi]); 
	  fflush(RED_OUT); 
	  */
          RT[cur_xi] = process_inactive_variable_eliminate(cur_xi, pi);

	  /*
	  fprintf(RED_OUT, "I:%1d, after local inactive elimination, xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi);
	  print_cpu_time("after local inactive elimination"); 
	    probe(PROBE_RISK1, "after local inactive eliminations", RT[cur_xi]); 
	  red_print_graph(RT[cur_xi]); 
	  fflush(RED_OUT);
	  */
        }
      }

      RT[cur_pi] = red_bop(OR, RT[cur_xi], RT[cur_pi]); 
      RT[cur_pi] = red_subsume(RT[cur_pi]);

      /*
      fprintf(RED_OUT, "\nITERATION %1d, after final union, xi=%1d, pi=%1d\n", ITERATION_COUNT, xi, pi); 
      print_cpu_time("after final union"); 
	probe(PROBE_RISK1, "after final union", RT[cur_pi]); 
      red_print_graph(RT[cur_xi]); 
      fflush(RED_OUT); 
      */

      RT_TOP--; // cur_xi 
      if (RT[cur_xi] != NORM_FALSE) {
        RT[cur_pi] = RT[cur_xi]; 
        if (xi) { 
          pia[counter[current_stage].party_count] = pi; 
          xia[counter[current_stage].party_count] = xi; 
          counter[current_stage].party_count++; 
        }
        break; 
      }
      garbage_collect(FLAG_GC_SILENT); 
    }

    RT[explore] = RT[cur_pi]; 
    RT_TOP--; /* cur_pi */ 
  }
  /*
  free(firable_xtion);
  */
  /*
  fprintf(RED_OUT, "After bulk execution\n");
  report_red_management();
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  if (   (  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
          & FLAG_BULK_TRIGGER_ACTION_INTERFERE
          ) 
      || (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)
      ) { 
    RT[explore] = red_bop(AND, RT[explore], RT[XI_SYNC_BULK_WITH_TRIGGERS]);
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
    RT[explore] = red_eliminate_all_qfd_sync(RT[explore]); 
    RT[explore] = inactive_variable_eliminate(explore);
  }
  reduce_symmetry(explore);
  /*
  fprintf(RED_OUT, "I:%1d, after first global invariancing\n", ITERATION_COUNT);
  print_cpu_time("after first global invariancing");
  probe(PROBE_PRERISK, "after first global invariancing", RT[explore]);
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */

  if (CLOCK_COUNT > 1) {
    RT[explore] = red_game_time_progress_bck(
      NULL, explore, REFINED_GLOBAL_INVARIANCE, MASK_GAME_ROLES, 
      TYPE_TRUE   
    );
    /*
      fprintf(RED_OUT, "I:%1d, after bck saturating\n", ITERATION_COUNT);
      print_cpu_time("after bck saturating");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
    */
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
    /*
      fprintf(RED_OUT, "I:%1d, after 2nd global invariancing\n", ITERATION_COUNT);
      print_cpu_time("after 2nd global invariancing");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
    */
  }

  RT[explore] = red_abs_game(RT[explore], GSTATUS[INDEX_APPROX]); 
  RT[explore] = red_bop(AND, RT[explore], COUNTER_PATH[current_stage]);
  /*
  fprintf(RED_OUT, "I:%1d, after path filtering\n", ITERATION_COUNT);
  print_cpu_time("after path filtering");
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  RT[explore] = red_subsume(RT[explore]);

  /*
  fprintf(RED_OUT, "\nITERATION %1d, after exact hulling \n", ITERATION_COUNT);
  print_cpu_time("after exact hulling");
  probe(PROBE_PRERISK, "after exact hulling", RT[explore]);
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */

  if (CLOCK_COUNT > 1) {
    RT[explore] = red_hull_normalize(explore);
  }

  /*
  print_cpu_time("Leaving sync_bulk_xtion()");
  probe(PROBE_PRERISK, "Leaving sync bulk xtion", RT[explore]);
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */

// In locate_one_weakest_precondition_sync_bulk(counter, current_stage)
// In locate_one_instance, the choices of transitions are recorded 
// as a side-effect if there are TYPE_XTION_INSTANCE variables in 
// RT[explore].  
  counter[current_stage].prestate 
  = locate_one_instance(RT[explore], counter, current_stage); 
  red_mark(counter[current_stage].prestate, FLAG_GC_STABLE);
  RT_TOP--; /* explore */
  garbage_collect(FLAG_GC_SILENT);
}
/* locate_one_weakest_precondition_sync_bulk() */








struct counter_example_node_type
	*generate_counter_example_fwd()
{
  struct path_xtion_type		*counter;
  int					old_iterate_sxi, 
					old_iterate_pi, 
					old_iterate_xi, 
					current_stage, 
  					explore, explore_sync;
  struct counter_example_node_type	*cl, *nc; 

  old_iterate_sxi = ITERATE_SXI; 
  old_iterate_xi = ITERATE_XI; 
  old_iterate_pi = ITERATE_PI; 
  
  if (!pia) {
    pia = (int *) malloc(PROCESS_COUNT * sizeof(int));
    xia = (int *) malloc(PROCESS_COUNT * sizeof(int));
  }

  if (CLOCK_COUNT > 1) {
    RT[explore = RT_TOP++] = COUNTER_PATH[COUNTER_PATH_TOP];
    RT[explore] = red_game_time_progress_bck(
      NULL, 
      explore, REFINED_GLOBAL_INVARIANCE, MASK_GAME_ROLES, 
      TYPE_TRUE   
    );
    /*
      fprintf(RED_OUT, "I:%1d, after bck saturating\n", ITERATION_COUNT);
      print_cpu_time("after bck saturating");
      red_print_graph(RT[explore]);
      fflush(RED_OUT); 
    */
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
    /*
      fprintf(RED_OUT, "I:%1d, after 2nd global invariancing\n", ITERATION_COUNT);
      print_cpu_time("after 2nd global invariancing");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
    */
    COUNTER_PATH[COUNTER_PATH_TOP] = RT[explore];
    red_mark(COUNTER_PATH[COUNTER_PATH_TOP], FLAG_GC_STABLE);
    RT_TOP--; // explore
  }

  counter = (struct path_xtion_type *) 
    malloc((COUNTER_PATH_TOP+1)*sizeof(struct path_xtion_type));

  fprintf(RED_OUT, "\n*********Generating counter example of %1d steps.\n", 
    COUNTER_PATH_TOP
  ); 
  counter[COUNTER_PATH_TOP].prestate = COUNTER_PATH[COUNTER_PATH_TOP]; 
  counter[COUNTER_PATH_TOP].party_count = 0; 
  counter[COUNTER_PATH_TOP].pi = NULL; 
  counter[COUNTER_PATH_TOP].xi = NULL; 
  for (current_stage = COUNTER_PATH_TOP-1; 
       current_stage >= 0; 
       current_stage--
       ) {
    counter[current_stage].party_count = 0; 
    counter[current_stage].pi = NULL; 
    counter[current_stage].xi = NULL; 
    if (   (!locate_one_weakest_precondition_sync_ITERATIVE(
              counter, current_stage
            ) )
        && !(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
        ) {
      locate_one_weakest_precondition_sync_bulk(counter, current_stage);
    } 
  } 
  
  cl = construct_counter_example(counter); 
   
  for (current_stage = 0; 
       current_stage < COUNTER_PATH_TOP; 
       current_stage++
       ) {
    free(counter[current_stage].xi); 
    free(counter[current_stage].pi); 
  } 
  free(counter); 
  
  ITERATE_SXI = old_iterate_sxi; 
  ITERATE_XI = old_iterate_xi; 
  ITERATE_PI = old_iterate_pi; 
  
  return(cl); 
}
/* generate_counter_example_fwd() */ 









/*****************************************************************
 *
 */




void	locate_one_strongest_postcondition_sync_bulk(counter, current_stage)
     struct path_xtion_type	*counter;
     int			current_stage;
{
  int	explore, cur_xi, cur_pi, cur_mi, urgent, pi,   
  	mpi, mi, ci, ai, xi, api, fpi, fxi, flag;
  /*
  print_cpu_time("Entering sync_bulk_xtion()");
  report_red_management();
  */

  RT[explore = RT_TOP++] = red_bop(AND, 
    counter[current_stage].prestate,
    RT[XI_SYNC_BULK_WITH_TRIGGERS]
  );
  if (RT[explore] == NORM_FALSE) {
    fprintf(RED_OUT, "\nThere is something wrong!\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 

  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];
    RT[cur_pi = RT_TOP++] = NORM_FALSE;
    for (ci = 0; ci < PROCESS[pi].firable_xtion_count; ci++) {

      xi = PROCESS[pi].firable_xtion[ci];
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(
        RT[explore], fxi, xi, xi 
      );

      if (RT[cur_xi] == NORM_FALSE) {
	RT_TOP--;
	continue;
      }
/*
      fprintf(RED_OUT, "sync bulk %1d, (pi=%1d, xi=%1d):\n", 
        current_stage, pi, xi
      ); 
*/
      RT[cur_xi] = red_bop(AND, RT[cur_xi], XTION[xi].red_trigger[pi]);
      if (RT[cur_xi] == NORM_FALSE) {
      	RT_TOP--; 
      	continue; 
      } 
      if (xi) {
	RT[cur_xi] = red_statement_fwd(cur_xi, pi, XTION[xi].statement, 
	  GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
          FLAG_ACTION_DELAYED_EVAL 
	);
        if (XTION[xi].status & FLAG_XTION_QUANTIFIED_SYNC) 
          RT[cur_xi] = red_eliminate_proc_qfd_sync(RT[cur_xi], pi); 

	if (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
	      & FLAG_BULK_TRIGGER_ACTION_INTERFERE
	    ) ) {
	  if (valid_mode_index(XTION[xi].dst_mode_index))
	    RT[cur_xi] = red_bop(AND, RT[cur_xi],
	      MODE[XTION[xi].dst_mode_index].invariance[pi].red
	    );
	  RT[cur_xi] = process_inactive_variable_eliminate(cur_xi, pi);
	}
      }
      RT[cur_pi] = red_bop(OR, RT[cur_pi], RT[cur_xi]); 
      RT_TOP--; // cur_xi 
      garbage_collect(FLAG_GC_SILENT);
    }

    RT[explore] = RT[cur_pi]; 
    RT_TOP--; // cur_pi 
  }
  /*
  fprintf(RED_OUT, "After bulk execution\n");
  report_red_management();
  */
  if (  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
      & FLAG_BULK_TRIGGER_ACTION_INTERFERE
      ) {
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
    RT[explore] = inactive_variable_eliminate(explore);
    /*
      fprintf(RED_OUT, "I=%1d", ITERATION_COUNT);
      print_cpu_time("after eliminating inactives");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
      probe(PROBE_PRERISK3, "test the risk after eliminating inactives", RT[cur_xi]);
    */
  }

  reduce_symmetry(explore);
  if (CLOCK_COUNT + DENSE_COUNT > 1) {
    RT[explore] = red_time_progress_fwd(
      explore, REFINED_GLOBAL_INVARIANCE
    );
    /*
    print_cpu_time("after the saturation()");
      fprintf(RED_OUT, "After bulk saturation\n");
      report_red_management();
    */
/* 
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
*/
    /*
    print_cpu_time("before the globally invariancing()");
      fprintf(RED_OUT, "After bulk saturation\n");
      report_red_management();
    */
  }
  RT[explore] = red_abs_game(RT[explore], GSTATUS[INDEX_APPROX]); 
/*  
  fprintf(RED_OUT, 
    "\ncounter %1d sync bulk, after abs, RT[explore]:\n", 
    current_stage
  ); 
  red_print_graph(RT[explore]); 
*/
  RT[explore] = red_bop(AND, RT[explore], 
    COUNTER_PATH[COUNTER_PATH_TOP - current_stage-1]
  );
/*
  fprintf(RED_OUT, 
    "\ncounter %1d sync bulk, after constraining, RT[explore]:\n", 
    current_stage
  ); 
  red_print_graph(RT[explore]); 
*/
  if (RT[explore] == NORM_FALSE) {
    fprintf(RED_OUT, "\nThere is something wrong!\n"); 
    fprintf(RED_OUT, 
      "The post-condition is excluded from the fwd trace at step %1d!\n", 
      current_stage+1   
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 

  reduce_symmetry(explore);

  if (CLOCK_COUNT + DENSE_COUNT > 1) {
    RT[explore] = red_hull_normalize(explore);
    /*
      fprintf(RED_OUT, "I=%1d", ITERATION_COUNT);
      print_cpu_time("after red_hulling()");
      fprintf(RED_OUT, "After bulk red hulling\n");
      report_red_management();
    */
  }
/* 
  fprintf(RED_OUT, "\nStage %1d: right before locating an instance with RT[explore=%1d]:\n", current_stage, explore);
  red_print_graph(RT[explore]);
*/ 
// In locate_one_strongest_postcondition_sync_bulk(counter, current_stage)
// In locate_one_instance, the choices of transitions are recorded 
// as a side-effect if there are TYPE_XTION_INSTANCE variables in 
// RT[explore].  
  counter[current_stage+1].prestate 
  = locate_one_instance(RT[explore], counter, current_stage); 
/*
  fprintf(RED_OUT, "\nStage %1d: after locating an instance:\n", current_stage);
  red_print_graph(counter[current_stage+1].prestate);
*/
  red_mark(counter[current_stage+1].prestate, FLAG_GC_STABLE);
  RT_TOP--; // explore 
/*
  fprintf(RED_OUT, "\n=========\ncounter[current_stage=%1d].pi=%x, size %1d\n", 
    current_stage, counter[current_stage].pi, 
    counter[current_stage].party_count
  ); 
  fprintf(RED_OUT, "counter[current_stage=%1d].xi=%x, size %1d\n", 
    current_stage, counter[current_stage].xi, 
    counter[current_stage].party_count
  ); 
*/
/*
  fprintf(RED_OUT, "\nCOUNTER_PATH[%1d]:\n", 
    COUNTER_PATH_TOP - current_stage-1
  );
  red_print_graph(COUNTER_PATH[COUNTER_PATH_TOP - current_stage-1]);
*/

  /*
  probe(PROBE_PRERISK2, "test the risk after red-hulling the sync bulk execution", RT[explore]);
  */
//  fflush(RED_OUT);

  /*
    print_cpu_time("after saturation");
    red_print_graph(RT[cur_xi]);
    probe(PROBE_PRERISK3, "test the risk after saturation", RT[cur_xi]);
  print_cpu_time("Leaving sync_bulk_xtion()");
  */
  garbage_collect(FLAG_GC_SILENT);
}
/* locate_one_strongest_postcondition_sync_bulk() */






int	locate_one_strongest_postcondition_sync_ITERATIVE(
  struct path_xtion_type	*counter, 
  int				current_stage
) {
  int			explore, sxi, urgent, ipi, ci, ai, api, 
			fpi, fxi, flag;
  struct red_type	*conj;
  /*
  print_cpu_time("Entering sync_bulk_xtion()");
  report_red_management();
  */
  for (ITERATE_SXI = 0; ITERATE_SXI < SYNC_XTION_COUNT; ITERATE_SXI++) {
/*
    switch (GLOBAL_STATUS & MASK_NORMALITY) {
    case FLAG_NORM_CLOSURE:
      RT[sxi = RT_TOP++] = red_restrict_closure(explore, SYNC_XTION[ITERATE_SXI].red_post);
      break;
    case FLAG_NORM_CLOSURE_EQ:
      RT[sxi = RT_TOP++] = RT[explore];
      RT[sxi] = red_restrict_closure_eq(sxi, SYNC_XTION[ITERATE_SXI].red_post);
      break;
    default:
      RT[sxi = RT_TOP++] = red_bop(AND, RT[explore], SYNC_XTION[ITERATE_SXI].red_post);
      break;
    }

    fprintf(RED_OUT, "\nRT_TOP=%1d, explore = %1d\n", RT_TOP, explore);
    red_print_graph(RT[explore]);
    red_print_graph(SYNC_XTION[ITERATE_SXI].red_trigger);
*/
    RT[sxi = RT_TOP++] = red_delayed_eval( 
      SYNC_XTION[ITERATE_SXI].red_trigger, 
      PROC_GLOBAL, 
      counter[current_stage].prestate
    );
/*
    print_sync_xtion(ITERATE_SXI);
    fprintf(RED_OUT, "RT_TOP=%1d, explore = %1d, sxi = %1d, RESULT_STACK_HEIGHT=%1d, flag_red_management=%1d\n",
	    RT_TOP, explore, sxi, RESULT_STACK_HEIGHT, flag_red_management
	    );
    fflush(RED_OUT);
    red_print_graph(RT[sxi]);
    fflush(RED_OUT);
    print_cpu_time("after global xi restrictions in sync ENUMERATIVE");
    report_red_management();
*/
    if (RT[sxi] == NORM_FALSE) {
      RT_TOP--;
      continue;
    }
/*
  red_print_graph(RT[explore]);
*/

    for (ipi = 0; ipi < SYNC_XTION[ITERATE_SXI].party_count; ipi++) {
      ITERATE_XI = SYNC_XTION[ITERATE_SXI].party[ipi].xtion;
      ITERATE_PI = SYNC_XTION[ITERATE_SXI].party[ipi].proc;
      if (RT[sxi] != NORM_FALSE) {
        if (ITERATE_XI) {
          RT[sxi] = red_statement_fwd(
            sxi, ITERATE_PI, 
            SYNC_XTION[ITERATE_SXI].party[ipi].statement, 
            /* XTION[ITERATE_XI].statement */
            GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX, 
            FLAG_ACTION_DELAYED_EVAL 
          );
          if (XTION[ITERATE_XI].status & FLAG_XTION_QUANTIFIED_SYNC) {
            RT[sxi] = red_eliminate_proc_qfd_sync(RT[sxi], ITERATE_PI); 
          }
          if (!(  SYNC_XTION[ITERATE_SXI].status 
                & FLAG_XTION_FWD_ACTION_INV_INTERFERE
              ) ) {
            if (valid_mode_index(XTION[ITERATE_XI].dst_mode_index))
              RT[sxi] = red_delayed_eval(
                MODE[
                  XTION[ITERATE_XI].dst_mode_index
                ].invariance[ITERATE_PI].red, 
                ITERATE_PI, 
                RT[sxi] 
              );
            RT[sxi] = process_inactive_variable_eliminate(sxi, ITERATE_PI);
          }
        }
/*
	fprintf(RED_OUT, "\n===Counter stage %1d; pi=%1d; xi=%1d;====================================\n",
		current_stage, pi, xi
		);
	print_xtion_line(xi, pi);
	fprintf(RED_OUT, "\n");
	print_cpu_time("after xtion");
	red_print_graph(RT[cur_xi]);
	fflush(RED_OUT);
*/
      }
      garbage_collect(FLAG_GC_SILENT);
    }

  /*
  fprintf(RED_OUT, "After bulk execution\n");
  report_red_management();
  */
    RT[sxi] = red_abs_game(RT[sxi], GSTATUS[INDEX_APPROX]); 
    if (  SYNC_XTION[ITERATE_SXI].status 
        & FLAG_XTION_FWD_ACTION_INV_INTERFERE
        ) {
      RT[sxi] = red_bop(AND, RT[sxi], RT[REFINED_GLOBAL_INVARIANCE]);
      RT[sxi] = inactive_variable_eliminate(sxi);
    /*
      fprintf(RED_OUT, "I=%1d", ITERATION_COUNT);
      print_cpu_time("after eliminating inactives");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
      probe(PROBE_PRERISK3, "test the risk after eliminating inactives", RT[cur_xi]);
    */
    }

    reduce_symmetry(sxi);
    if (CLOCK_COUNT + DENSE_COUNT > 1) {
      RT[sxi] = red_time_progress_fwd(sxi, REFINED_GLOBAL_INVARIANCE);
    /*
    print_cpu_time("after the saturation()");
      fprintf(RED_OUT, "After bulk saturation\n");
      report_red_management();
    */
/*
      RT[sxi] = red_bop(AND, RT[sxi], RT[REFINED_GLOBAL_INVARIANCE]);
*/
    /*
    print_cpu_time("before the globally invariancing()");
      fprintf(RED_OUT, "After bulk saturation\n");
      report_red_management();
    */
    }
    RT[sxi] = red_abs_game(RT[sxi], GSTATUS[INDEX_APPROX]); 
    RT[sxi] = red_bop(AND, RT[sxi], 
      COUNTER_PATH[COUNTER_PATH_TOP - current_stage-1]
    );
    reduce_symmetry(sxi);
    if (CLOCK_COUNT + DENSE_COUNT > 1) {
      RT[sxi] = red_hull_normalize(sxi);
      /*
        fprintf(RED_OUT, "I=%1d", ITERATION_COUNT);
        print_cpu_time("after red_hulling()");
        fprintf(RED_OUT, "After bulk red hulling\n");
        report_red_management();
      */
    }
    /*
    red_print_graph(RT[explore]);
    fprintf(RED_OUT, "\nStage %1d: right before locating an instance with RT[explore=%1d]:\n", current_stage, explore);
    red_print_graph(RT[explore]);
    */

// In locate_one_strongest_postcondition_sync_ITERATIVE(counter, current_stage)
    if ((conj = locate_one_instance(RT[sxi], counter, current_stage)) 
        != NORM_FALSE
        ) {
      counter[current_stage+1].prestate = conj;
      counter[current_stage].party_count = SYNC_XTION[ITERATE_SXI].party_count;
      counter[current_stage].pi = (int *) malloc(SYNC_XTION[ITERATE_SXI].party_count * sizeof(int));
      counter[current_stage].xi = (int *) malloc(SYNC_XTION[ITERATE_SXI].party_count * sizeof(int));
/*
      fprintf(RED_OUT, "\n*******\n"); 
      fprintf(RED_OUT, "current_stage %1d: ", current_stage); 
*/
      for (ipi = 0; ipi < SYNC_XTION[ITERATE_SXI].party_count; ipi++) {
        counter[current_stage].pi[ipi] = SYNC_XTION[ITERATE_SXI].party[ipi].proc;
        counter[current_stage].xi[ipi] = SYNC_XTION[ITERATE_SXI].party[ipi].xtion;
/*
        fprintf(RED_OUT, "(p%1d,x%1d) ", 
          counter[current_stage].pi[ipi], 
          counter[current_stage].xi[ipi]
        ); 
*/
      }
/*
      fprintf(RED_OUT, "\n"); 
      fprintf(RED_OUT, "counter[current_stage+1=%1d].prestate:\n", 
        current_stage+1
      ); 
      red_print_graph(counter[current_stage+1].prestate); 
*/
      red_mark(counter[current_stage+1].prestate, 
        FLAG_GC_STABLE
      );
/*
      fprintf(RED_OUT, "\nCOUNTER_PATH[%1d]:\n", 
        COUNTER_PATH_TOP - current_stage-1);
      red_print_graph(COUNTER_PATH[COUNTER_PATH_TOP - current_stage-1]);
*/
      RT_TOP--; // sxi 
      return(TYPE_TRUE);
    }
    else
      RT_TOP--; /* sxi */

  /*
  probe(PROBE_PRERISK2, "test the risk after red-hulling the sync bulk execution", RT[explore]);
  */
    fflush(RED_OUT);

  /*
    print_cpu_time("after saturation");
    red_print_graph(RT[cur_xi]);
    probe(PROBE_PRERISK3, "test the risk after saturation", RT[cur_xi]);
  print_cpu_time("Leaving sync_bulk_xtion()");
  */
    garbage_collect(FLAG_GC_SILENT);
  }
  return(TYPE_FALSE);
}
/* locate_one_strongest_postcondition_sync_ITERATIVE() */






struct counter_example_node_type
	*generate_counter_example_bck()
{
  struct path_xtion_type		*counter;
  int					i, old_iterate_sxi, 
					old_iterate_pi, 
					old_iterate_xi, 
					current_stage, explore, 
					explore_sync;
  struct counter_example_node_type	*cl; 
  
  old_iterate_sxi = ITERATE_SXI; 
  old_iterate_xi = ITERATE_XI; 
  old_iterate_pi = ITERATE_PI; 
  
  if (!pia) {
    pia = (int *) malloc(PROCESS_COUNT * sizeof(int));
    xia = (int *) malloc(PROCESS_COUNT * sizeof(int));
  }
  
  if (CLOCK_COUNT + DENSE_COUNT > 1) {
    RT[explore = RT_TOP++] = COUNTER_PATH[COUNTER_PATH_TOP];
    RT[explore] = red_time_progress_fwd(
      explore, 
      REFINED_GLOBAL_INVARIANCE
    );
    /*
      fprintf(RED_OUT, "I:%1d, after bck saturating\n", ITERATION_COUNT);
      print_cpu_time("after bck saturating");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
    */
/*
    RT[explore] = red_bop(AND, RT[explore], RT[REFINED_GLOBAL_INVARIANCE]);
*/
    /*
      fprintf(RED_OUT, "I:%1d, after 2nd global invariancing\n", ITERATION_COUNT);
      print_cpu_time("after 2nd global invariancing");
      red_print_graph(RT[explore]);
      fflush(RED_OUT);
    */
    COUNTER_PATH[COUNTER_PATH_TOP] = RT[explore];
    red_mark(COUNTER_PATH[COUNTER_PATH_TOP], FLAG_GC_STABLE);
    RT_TOP--; // explore 
  }

  counter = (struct path_xtion_type *) 
    malloc((COUNTER_PATH_TOP+1)*sizeof(struct path_xtion_type));

  // Note that in counter array, the events and states are recorded 
  // in temporal order.  
  // That is, 
  counter[0].prestate = COUNTER_PATH[COUNTER_PATH_TOP]; 
  for (current_stage = 0; current_stage < COUNTER_PATH_TOP; current_stage++) {
      /*
      */
      fprintf(RED_OUT, 
        "\n==[COUNTER %1d, counter[%1d].prestate]===================\n", 
        current_stage, current_stage
      );
      red_print_graph(counter[current_stage].prestate);

    counter[current_stage].party_count = 0; 
    counter[current_stage].pi = NULL; 
    counter[current_stage].xi = NULL; 
//    fprintf(RED_OUT, "\n>> %1d, before locating post:\n", current_stage); 
    if (   !locate_one_strongest_postcondition_sync_ITERATIVE(
             counter, current_stage
           )
      	&& !(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_NO_SYNCHRONIZERS)
	) {
      locate_one_strongest_postcondition_sync_bulk(counter, current_stage);
    } 
    for (i = 0; i < counter[current_stage].party_count; i++) { 
      fprintf(RED_OUT, "(pi=%1d, xi=%1d):\n>> ", 
        counter[current_stage].pi[i], counter[current_stage].xi[i]
      ); 
      print_xtion_line(
        counter[current_stage].xi[i], counter[current_stage].pi[i]
      );
      fprintf(RED_OUT, "\n"); 
    } 
    fprintf(RED_OUT, "\nTo post condition in:\n"); 
    red_print_graph(COUNTER_PATH[COUNTER_PATH_TOP - current_stage - 1]); 
  } 
  counter[COUNTER_PATH_TOP].party_count = 0; 
  counter[COUNTER_PATH_TOP].pi = NULL; 
  counter[COUNTER_PATH_TOP].xi = NULL; 

  cl = construct_counter_example(counter); 

  for (current_stage = 0; 
       current_stage < COUNTER_PATH_TOP; 
       current_stage++
       ) {
    free(counter[current_stage].xi); 
    free(counter[current_stage].pi); 
  }
  free(counter); 
    
  ITERATE_SXI = old_iterate_sxi; 
  ITERATE_XI = old_iterate_xi; 
  ITERATE_PI = old_iterate_pi; 
  
  return(cl); 
}
/* generate_counter_example_bck() */




