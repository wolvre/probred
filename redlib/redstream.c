#include <stdlib.h>
#include <stdio.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
*/
#include <limits.h> 

#include "redbasics.h"
#include "redbasics.e"

#include "fxp.h" 

#include "treeman.h" 
#include "treeman.e" 

#include "redbop.h"
#include "redbop.e"

#include "redparse.h"
#include "redparse.e"

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "action.e"

#include "hybrid.e" 

#include "redlib.h" 
#include "redlib.e" 


#define	SIZE_STREAM_CHUNK	100 


/************************************************************
 *  Stream operations
 *  In the long run, we need to implement the idea of file pointer 
 *  for each computation trace.  
 */
struct red_type	*red_set_sync_bulk(
  struct red_type	*d, 
  int			pi, 
  int			xi
) { 
  d = ddd_one_constraint(d, 
    variable_index[TYPE_XTION_INSTANCE][pi][0], xi, xi
  ); 
  return(d); 
} 
  /* red_set_sync_bulk() */ 
  



int	red_exp_sync_bulk(
  struct red_type	*d, 
  int			pi, 
  struct ps_exp_type	*exp
) {
  struct red_type	*red_value; 
  int			ci, value; 
  
  red_value = red_delayed_exp_value(exp, pi, d); 
  ci = rand() % red_value->u.ddd.child_count; 
  d = red_bop(AND, d, red_value->u.ddd.arc[ci].child); 
  value = rand() % (
    red_value->u.ddd.arc[ci].upper_bound 
  - red_value->u.ddd.arc[ci].lower_bound 
  + 1
  ); 
  value = value + red_value->u.ddd.arc[ci].lower_bound; 
  return(value); 
}
  /* red_exp_sync_bulk() */ 









  




/***************************************************************
 *  The following procedures are for the modeling of streams.  
 */


struct red_type	*red_open_stream(
  struct red_type	*d, 
  int			vi_stream, 
  int			direction  
) {
  struct red_type	*conj; 
  
  if (   vi_stream < 0 
      || vi_stream >= VARIABLE_COUNT
      ) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d to open.\n", 
      vi_stream
    ); 
    bk(0); 
  } 
  else if (VAR[vi_stream].TYPE != TYPE_STREAM) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d:%s to open.\n", 
      vi_stream, VAR[vi_stream].NAME
    ); 
    bk(0); 
  }
  
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, 
    FLAG_STREAM_NOT_OPENED+1, INT_MAX
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: STREAM %s already opened in the following states.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 
  switch (direction) { 
  case FLAG_STREAM_INPUT: 
    d = red_assign_interval(d, VAR[vi_stream].U.STRM.DIRECTION_VI, 
      FLAG_STREAM_INPUT, FLAG_STREAM_INPUT
    ); 
    VAR[vi_stream].U.STRM.FILE_STREAM = fopen(VAR[vi_stream].NAME, "r"); 
    break; 
  case FLAG_STREAM_OUTPUT: 
    d = red_assign_interval(d, VAR[vi_stream].U.STRM.DIRECTION_VI, 
      FLAG_STREAM_OUTPUT, FLAG_STREAM_OUTPUT
    ); 
    VAR[vi_stream].U.STRM.FILE_STREAM = fopen(VAR[vi_stream].NAME, "w"); 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal stream open mode: %1d\n", 
      direction 
    ); 
    bk(0); 
  }
  d = red_assign_interval(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, -1, -1); 
  if (VAR[vi_stream].U.STRM.SIZE_BUFFER == 0) { 
    VAR[vi_stream].U.STRM.SIZE_BUFFER = SIZE_STREAM_CHUNK; 
    VAR[vi_stream].U.STRM.SIZE_DATA = 0; 
    VAR[vi_stream].U.STRM.BUFFER = (int *) 
      malloc(SIZE_STREAM_CHUNK * sizeof(int)); 
    switch (direction) { 
    case FLAG_STREAM_INPUT: 
      VAR[vi_stream].U.STRM.FILE_STREAM = fopen(VAR[vi_stream].NAME, "r"); 
      break; 
    case FLAG_STREAM_OUTPUT: 
      VAR[vi_stream].U.STRM.FILE_STREAM = fopen(VAR[vi_stream].NAME, "w"); 
      break; 
    }
  } 
  return(d); 
}
  /* red_open_stream() */  
  



struct red_type	*red_close_stream(
  struct red_type	*d, 
  int			vi_stream
) { 
  struct red_type	*conj; 
  
  if (vi_stream < 0 || vi_stream >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d to close.\n", 
      vi_stream
    ); 
    bk(0); 
  } 
  else if (VAR[vi_stream].TYPE != TYPE_STREAM) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d:%s to close.\n", 
      vi_stream, VAR[vi_stream].NAME
    ); 
    bk(0); 
  } 
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, 
    FLAG_STREAM_NOT_OPENED, FLAG_STREAM_NOT_OPENED
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: STREAM %s already closed in the following states.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 
  d = red_variable_eliminate(d, VAR[vi_stream].U.STRM.DIRECTION_VI);  
  d = red_assign_interval(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, 
    FLAG_STREAM_NOT_OPENED, FLAG_STREAM_NOT_OPENED
  ); 

  return(d); 
} 
  /* red_close_stream() */ 



struct red_type	*red_close_all_streams(
  struct red_type	*d
) { 
  int			vi, i; 
  struct red_type	*conj; 
  
  for (i = 0; i < GLOBAL_COUNT[TYPE_STREAM]; i++) { 
    vi = variable_index[TYPE_STREAM][0][i]; 
    d = red_variable_eliminate(d, VAR[vi].U.STRM.DIRECTION_VI);  
    d = red_assign_interval(d, VAR[vi].U.STRM.HEAD_POS_VI, 
      FLAG_STREAM_NOT_OPENED, FLAG_STREAM_NOT_OPENED
    ); 
  } 
  return(d); 
} 
  /* red_close_all_streams() */ 






int	STREAM_OP_LHS_VI, STREAM_OP_STREAM_VI, STREAM_OP_VALUE; 

struct red_type	*rec_stream_input_from_buffer(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				i, ci, j, newpos;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
      || d->var_index > VAR[STREAM_OP_STREAM_VI].U.STRM.HEAD_POS_VI
      ) {
    fprintf(RED_OUT, "\nERROR: unknown status of stream %s.\n", 
      VAR[STREAM_OP_STREAM_VI].NAME
    ); 
    bk(0); 
  }
  ce = cache4_check_result_key(OP_STREAM_INPUT_FROM_BUFFER, d, 
    (struct hrd_exp_type *) STREAM_OP_LHS_VI, STREAM_OP_STREAM_VI, 0
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_stream_input_from_buffer(d->u.bdd.zero_child), 
      rec_stream_input_from_buffer(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_stream_input_from_buffer(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_stream_input_from_buffer(d->u.hrd.arc[ci].child);
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
      conj = rec_stream_input_from_buffer(d->u.fdd.arc[ci].child);
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
      conj = rec_stream_input_from_buffer(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(conj, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound 
      );
    }
    result = fdd_new(d->var_index);
    break; 
  default: 
    if (d->var_index == STREAM_OP_LHS_VI) {
      result = NORM_FALSE;
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        result = red_bop(OR, result, d->u.ddd.arc[ci].child);
      }
    }
    else if (d->var_index == VAR[STREAM_OP_STREAM_VI].U.STRM.HEAD_POS_VI) {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	for (i = d->u.ddd.arc[ci].lower_bound; 
      	     i <= d->u.ddd.arc[ci].upper_bound; 
      	     i++
      	     ) { 
      	  newpos = i+1; 
      	  if (newpos >= VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER) { 
            int	*new_buf, pos; 
    
            new_buf = (int *) 
              malloc(2*VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER*sizeof(int)); 
            for (pos = 0; pos < VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER; pos++) { 
              new_buf[pos] = VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[pos]; 
            } 
            free(VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER); 
            VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER = new_buf; 
            VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER 
            = 2*VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER; 
      	  } 
      	  for (j = VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA; 
      	       j <= newpos; 
      	       j++
      	       ) { 
            if (fscanf(VAR[STREAM_OP_STREAM_VI].U.STRM.FILE_STREAM, "%d", 
                  &(VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[j]) 
                )!= 1) {
              fprintf(RED_OUT, "\nERROR: stream %s data reading failure\n", 
                VAR[STREAM_OP_STREAM_VI].NAME
              ); 
              exit(0); 
            }
      	  } 
      	  if (VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA <= newpos) 
            VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA = newpos+1; 
          conj = red_assign_interval(d->u.ddd.arc[ci].child, 
            STREAM_OP_LHS_VI, 
            VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[newpos], 
            VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[newpos]
          ); 
          conj = ddd_one_constraint(conj, d->var_index, newpos, newpos); 
            
          result = red_bop(OR, result, conj);
        } 
      }
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_stream_input_from_buffer(d->u.ddd.arc[ci].child);
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
/* rec_stream_input_from_buffer() */






struct red_type	*red_get_stream_input(
  struct red_type	*d, 
  int			lhs_vi, 
  int			vi_stream
) { 
  struct red_type	*conj; 
  int			value; 
  
  if (red_query_var_attribute(vi_stream, RED_VAR_STREAM_ORDERED)) {
    STREAM_OP_LHS_VI = lhs_vi; 
    STREAM_OP_STREAM_VI = vi_stream; 
    d = rec_stream_input_from_buffer(d); 
  } 
  else {
    if (fscanf(VAR[vi_stream].U.STRM.FILE_STREAM, "%d", &value) != 1) { 
      fprintf(RED_OUT, "\nERROR: stream %s data reading failure\n", 
        VAR[vi_stream].NAME
      ); 
      exit(0); 
    }
    d = red_assign_interval(d, lhs_vi, value, value); 
  } 

  return(d); 
}
  /* red_get_stream_input() */ 





struct red_type	*red_postcondition_stream_input_sync_bulk(
  struct red_type	*d, 
  int			pi,
  int			xi, 
  int			soi  
) { 
  int			ri, vi, ci, pj, vi_stream; 
  struct ps_exp_type	*dest_exp; 
  struct red_type	*red_addr, *result, *conj; 
  
  vi_stream = XTION[xi].stream_operation[soi].stream; 
  if (vi_stream < 0 || vi_stream >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d to read.\n", 
      vi_stream
    ); 
    bk(0); 
  } 
  else if (VAR[vi_stream].TYPE != TYPE_STREAM) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d:%s to read.\n", 
      vi_stream, VAR[vi_stream].NAME
    ); 
    bk(0); 
  } 
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, 
    FLAG_STREAM_NOT_OPENED, FLAG_STREAM_NOT_OPENED
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: STREAM %s not opened in the following states.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.DIRECTION_VI, 
    FLAG_STREAM_OUTPUT, FLAG_STREAM_OUTPUT
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: output STREAM %s illegally for input.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 

  dest_exp = XTION[xi].stream_operation[soi].var; 
  red_addr = red_delayed_operand_indirection(dest_exp, pi, d); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_addr->u.ddd.child_count; ci++) { 
    for (vi = red_addr->u.ddd.arc[ci].lower_bound; 
         vi <= red_addr->u.ddd.arc[ci].upper_bound; 
         vi++
           ) { 
      result = red_bop(OR, result, 
        red_get_stream_input(
          /* red_bop(AND, d, */
          red_addr->u.ddd.arc[ci].child
          /* )*/ , 
          vi, vi_stream
        ) 
      ); 
    } 
  } 
  return(result); 
} 
  /* red_postcondition_stream_input_sync_bulk() */ 
  


struct red_type	*rec_stream_output_to_buffer(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *td, *fd, *subresult, *filter;
  int				i, ci, newpos;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (   d->var_index == TYPE_TRUE 
      || d->var_index == TYPE_FALSE
      || d->var_index > VAR[STREAM_OP_STREAM_VI].U.STRM.HEAD_POS_VI
      ) {
    fprintf(RED_OUT, "\nERROR: unknown status of stream %s.\n", 
      VAR[STREAM_OP_STREAM_VI].NAME
    ); 
    bk(0); 
  }
  ce = cache4_check_result_key(OP_STREAM_OUTPUT_TO_BUFFER, d, 
    (struct hrd_exp_type *) STREAM_OP_STREAM_VI, STREAM_OP_VALUE, 0
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_stream_output_to_buffer(d->u.bdd.zero_child), 
      rec_stream_output_to_buffer(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_stream_output_to_buffer(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_stream_output_to_buffer(d->u.hrd.arc[ci].child);
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
      conj = rec_stream_output_to_buffer(d->u.fdd.arc[ci].child);
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
      conj = rec_stream_output_to_buffer(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(conj, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound 
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default: 
    if (d->var_index == VAR[STREAM_OP_STREAM_VI].U.STRM.HEAD_POS_VI) {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	for (i = d->u.ddd.arc[ci].lower_bound; 
      	     i <= d->u.ddd.arc[ci].upper_bound; 
      	     i++
      	     ) { 
      	  newpos = i+1; 
          if (   red_query_var_attribute(
                   STREAM_OP_STREAM_VI, RED_VAR_STREAM_ORDERED
                 )
              && newpos >= VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER
              ) { 
            int	*new_buf, pos; 
    
            new_buf = (int *) 
              malloc(2*VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER*sizeof(int)); 
            for (pos = 0; pos < VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER; pos++) { 
              new_buf[pos] = VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[pos]; 
            } 
            free(VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER); 
            VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER = new_buf; 
            VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER 
            = 2*VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_BUFFER; 
      	  } 
      	  if (newpos >= VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA) { 
      	    if (newpos > VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA) {
      	      fprintf(RED_OUT, 
      	        "\nERROR: stream head position %1d bigger than data size %1d.\n", 
      	        newpos, VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA
      	      ); 
      	      bk(0); 
      	    } 
      	    VAR[STREAM_OP_STREAM_VI].U.STRM.SIZE_DATA++; 
      	    fprintf(VAR[STREAM_OP_STREAM_VI].U.STRM.FILE_STREAM, 
      	      " %1d", STREAM_OP_VALUE
      	    ); 
            if (red_query_var_attribute(
                  STREAM_OP_STREAM_VI, RED_VAR_STREAM_ORDERED
                ) ) { 
              VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[newpos] = STREAM_OP_VALUE; 
            } 
      	  } 
      	  else if (   red_query_var_attribute(
      	                STREAM_OP_STREAM_VI, RED_VAR_STREAM_ORDERED
      	              )
      	           && VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[newpos] 
      	              != STREAM_OP_VALUE
      	           ) { 
            fprintf(RED_OUT, 
              "\nERROR: Different values %1d, %1d written to data %1d of stream %s.\n", 
              STREAM_OP_VALUE, 
              VAR[STREAM_OP_STREAM_VI].U.STRM.BUFFER[newpos], 
              newpos, VAR[STREAM_OP_STREAM_VI].NAME
            ); 
            bk(0); 
      	  }
          conj = ddd_one_constraint(d->u.ddd.arc[ci].child, 
            d->var_index, newpos, newpos
          ); 
          result = red_bop(OR, result, conj); 
        } 
      }
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_stream_output_to_buffer(d->u.ddd.arc[ci].child);
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
/* rec_stream_output_to_buffer() */




struct red_type	*red_put_stream_output(
  struct red_type	*d, 
  int			vi_stream, 
  int			value
) { 
  STREAM_OP_STREAM_VI = vi_stream; 
  STREAM_OP_VALUE = value; 
  d = rec_stream_output_to_buffer(d); 
  return(d); 
}
  /* red_put_stream_output() */ 



struct red_type	*red_postcondition_stream_output_sync_bulk(
  struct red_type	*d, 
  int			pi,
  int			xi, 
  int			soi  
) { 
  int			ri, value, ci, pj, vi_stream; 
  struct ps_exp_type	*dest_exp; 
  struct red_type	*conj, *red_value, *result; 
  
  vi_stream = XTION[xi].stream_operation[soi].stream; 
  if (vi_stream < 0 || vi_stream >= VARIABLE_COUNT) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d to read.\n", 
      vi_stream
    ); 
    bk(0); 
  } 
  else if (VAR[vi_stream].TYPE != TYPE_STREAM) {
    fprintf(RED_OUT, "\nERROR: Illegal stream variable id %1d:%s to read.\n", 
      vi_stream, VAR[vi_stream].NAME
    ); 
    bk(0); 
  } 
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.HEAD_POS_VI, 
    FLAG_STREAM_NOT_OPENED, FLAG_STREAM_NOT_OPENED
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: STREAM %s not opened in the following states.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 
  conj = ddd_one_constraint(d, VAR[vi_stream].U.STRM.DIRECTION_VI, 
    FLAG_STREAM_OUTPUT, FLAG_STREAM_OUTPUT
  ); 
  if (conj != NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR: output STREAM %s illegally for input.\n", 
      VAR[vi_stream].NAME
    ); 
    red_print_graph(conj); 
    bk(0); 
  } 

  red_value = red_delayed_exp_value(
    XTION[xi].stream_operation[soi].value_exp, pi, d
  ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_value->u.ddd.child_count; ci++) { 
    for (value = red_value->u.ddd.arc[ci].lower_bound; 
         value <= red_value->u.ddd.arc[ci].upper_bound; 
         value++
         ) { 
      result = red_bop(OR, result, 
        red_put_stream_output(red_value->u.ddd.arc[ci].child, 
          vi_stream, value 
        ) 
      ); 
    } 
  } 
  return(result); 
} 
  /* red_postcondition_stream_output_sync_bulk() */ 
  


int	HEAP_RQ_DEST, HEAP_RQ_SIZE; 

struct red_type	*rec_heap_malloc(d, tvi)
     struct red_type	*d;
     int		tvi; 
{
  struct red_type		*result, *conj, *td, *fd, *subresult, *filter;
  int				i, ci, newpos;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_HEAP_MALLOC, d, 
    (struct hrd_exp_type *) HEAP_RQ_DEST, HEAP_RQ_SIZE, tvi 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_heap_malloc(d->u.bdd.zero_child, tvi), 
      rec_heap_malloc(d->u.bdd.one_child, tvi)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_heap_malloc(d->u.crd.arc[ci].child, tvi);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_heap_malloc(d->u.hrd.arc[ci].child, tvi);
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
      conj = rec_heap_malloc(d->u.fdd.arc[ci].child, tvi);
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
      conj = rec_heap_malloc(d->u.dfdd.arc[ci].child, tvi);
      dfchild_stack_push(conj, 
        d->u.dfdd.arc[ci].lower_bound,
        d->u.dfdd.arc[ci].upper_bound 
      );
    }
    result = dfdd_new(d->var_index);
    break; 
  default: 
    if (d->var_index == tvi) {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	for (i = d->u.ddd.arc[ci].lower_bound; 
      	     i <= d->u.ddd.arc[ci].upper_bound; 
      	     i++
      	     ) { 
      	  if (i > 0) { 
      	    conj = rec_heap_malloc(d->u.ddd.arc[ci].child, tvi + 2*i); 
      	    conj = ddd_one_constraint(conj, tvi, i, i); 
      	    result = red_bop(OR, result, conj); 
      	  } 
      	  else if (i < 0) { 
      	    if (i + HEAP_RQ_SIZE <= 0) { 
      	      conj = d->u.ddd.arc[ci].child; 
      	      if (i + HEAP_RQ_SIZE < 0) { 
      	      	conj = red_assign_interval(conj, 
      	      	  tvi + 2 * HEAP_RQ_SIZE, 
      	      	  i+HEAP_RQ_SIZE, i+HEAP_RQ_SIZE
      	      	); 
      	      } 
      	      conj = ddd_one_constraint(
      	        conj, tvi, HEAP_RQ_SIZE, HEAP_RQ_SIZE
      	      ); 
      	      result = red_bop(OR, result, conj); 
      	    } 
      	    else { 
      	      conj = rec_heap_malloc(d->u.ddd.arc[ci].child, tvi - 2*i); 
      	      conj = ddd_one_constraint(conj, tvi, i, i); 
      	      result = red_bop(OR, result, conj); 
      	    } 	
      	  } 
      	  else { 
      	    conj = rec_heap_malloc(d->u.ddd.arc[ci].child, tvi); 
      	    conj = ddd_one_constraint(conj, tvi, i, i); 
      	    result = red_bop(OR, result, conj); 
      	  } 
        } 
      }
    }
    else {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_heap_malloc(d->u.ddd.arc[ci].child, tvi);
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
   /* rec_heap_malloc() */








struct red_type	*red_malloc_from_exp_sync_bulk(
  struct red_type	*d, 
  int			pi,
  int			xi, 
  int			soi 
) { 
  int			vi, ci, cj, size; 
  struct red_type	*red_size, *red_addr, *red_dest, *result, *conj; 
  
  red_size = red_delayed_exp_value(
    XTION[xi].stream_operation[soi].value_exp, pi, d
  );  
  
  red_dest = red_delayed_operand_indirection(
    XTION[xi].stream_operation[soi].var, pi, d
  ); 
  result = NORM_FALSE; 
  for (ci = 0; ci < red_dest->u.ddd.child_count; ci++) { 
    for (vi = red_dest->u.ddd.arc[ci].lower_bound; 
         vi <= red_dest->u.ddd.arc[ci].upper_bound; 
         vi++
         ) { 
      HEAP_RQ_DEST = vi; 
      for (cj = 0; cj < red_size->u.ddd.child_count; cj++) { 
      	for (size = red_size->u.ddd.arc[cj].lower_bound; 
      	     size <= red_size->u.ddd.arc[cj].upper_bound; 
      	     size++
      	     ) { 
          HEAP_RQ_SIZE = size; 
          conj = red_bop(AND, red_dest->u.ddd.arc[ci].child, 
            red_size->u.ddd.arc[cj].child
          ); 
          conj = rec_heap_malloc(conj, MEMORY_START_VI+1); 
          result = red_bop(OR, result, conj); 
    } } }
  } 
  return(result); 
} 
  /* red_malloc_from_exp_sync_bulk() */ 
  



struct red_type	*red_free_heap(
  struct red_type	*d, 
  int 			addr
) {
  int			ci, cj, mid; 
  struct red_type	*result, *child; 
  
  if (RT[INDEX_MALLOC_SPACE] == NORM_FALSE) { 
    fprintf(RED_OUT, 
      "\nERROR, Illegal free operation on unalloc'd space 0x%x.\n", 
      addr
    );
    fflush(RED_OUT); 
    bk(0); 
  }
  ci = 0; 
  cj = RT[INDEX_MALLOC_SPACE]->u.ddd.child_count-1;
  for (; ci <= cj; ) { 
    mid = (ci+cj)/2; 
    if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].lower_bound == addr) { 
      child = RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].child; 
      d = red_multi_variables_eliminate(d, 
        addr, addr + child->u.ddd.arc[0].lower_bound - 1
      ); 
      RT[INDEX_MALLOC_SPACE] = red_bop(SUBTRACT, 
        RT[INDEX_MALLOC_SPACE], ddd_atom(LHS_PI, addr, addr)
      ); 
      return (d); 
    } 
    else if (RT[INDEX_MALLOC_SPACE]->u.ddd.arc[mid].lower_bound < addr) {
      ci = mid+1; 
    } 
    else { 
      cj = mid-1; 
    } 
  } 
  fprintf(RED_OUT, 
    "\nERROR, Illegal free operation on unalloc'd space %x.\n", 
    addr
  );
  fflush(RED_OUT); 
  bk(0); 
  return; 
}
  /* red_free_heap() */ 




struct red_type	*rec_heap_free(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj, *sd, *gchild;
  int				i, ci, cj, j, k, ck, newpos;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index > HEAP_RQ_DEST+1) {
    fprintf(RED_OUT, 
      "\nERROR: Trying to free in the middle %1d of a block.\n", 
      HEAP_RQ_DEST
    ); 
    bk(0); 
  }
  else if (d->var_index == TYPE_FALSE) { 
    return(NORM_FALSE); 
  } 

  ce = cache2_check_result_key(OP_HEAP_FREE, d, 
    (struct red_type *) HEAP_RQ_DEST  
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    result = bdd_new(d->var_index, 
      rec_heap_free(d->u.bdd.zero_child), 
      rec_heap_free(d->u.bdd.one_child)
    );
    break; 
  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
      conj = rec_heap_free(d->u.crd.arc[ci].child);
      bchild_stack_push(conj, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index); 
    break; 
  case TYPE_HRD: 
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      conj = rec_heap_free(d->u.hrd.arc[ci].child);
      hchild_stack_push(conj, 
	d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
    } 
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break; 
  case TYPE_FLOAT: 
    if (d->var_index < HEAP_RQ_DEST) {
      child_stack_level_push();
      for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
        conj = rec_heap_free(d->u.fdd.arc[ci].child);
        fchild_stack_push(conj, 
          d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound 
	);
      }
      result = fdd_new(d->var_index);
    }
    else { 
      fprintf(RED_OUT, "\nERROR, something fishy here. \n"); 
      fprintf(RED_OUT, 
        "       We should not reaced a deep memory variable %1d:%s\n", 
        d->var_index, VAR[d->var_index].NAME
      ); 
      bk(0); 
    } 
    break; 
  case TYPE_DOUBLE: 
    if (d->var_index < HEAP_RQ_DEST) {
      child_stack_level_push();
      for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
        conj = rec_heap_free(d->u.dfdd.arc[ci].child);
        dfchild_stack_push(conj, 
          d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound 
	);
      }
      result = dfdd_new(d->var_index);
    }
    else { 
      fprintf(RED_OUT, "\nERROR, something fishy here. \n"); 
      fprintf(RED_OUT, 
        "       We should not reaced a deep memory variable %1d:%s\n", 
        d->var_index, VAR[d->var_index].NAME
      ); 
      bk(0); 
    } 
    break; 
  default: 
    if (d->var_index < HEAP_RQ_DEST) {
      child_stack_level_push();
      for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
        conj = rec_heap_free(d->u.ddd.arc[ci].child);
        ichild_stack_push(conj, 
          d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound 
	);
      }
      result = ddd_new(d->var_index);
    }
    else if (d->var_index == HEAP_RQ_DEST) {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
        result = red_bop(OR, result, rec_heap_free(d->u.ddd.arc[ci].child)); 
      } 
    }
    else if (d->var_index == HEAP_RQ_DEST+1) {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	for (i = d->u.ddd.arc[ci].lower_bound; 
      	     i <= d->u.ddd.arc[ci].upper_bound; 
      	     i++
      	     ) { 
      	  if (i < 0) { 
      	    fprintf(RED_OUT, "\nERROR: Trying to free already free'd %1d\n", HEAP_RQ_DEST); 
      	    bk(0); 
      	  } 
      	  else if (i == 0) { 
      	    fprintf(RED_OUT, "\nERROR: Trying to free %1d in the middle of a block\n", HEAP_RQ_DEST); 
      	    fprintf(RED_OUT, "       This should only happen when memory is zero size.\n"); 
      	    bk(0); 
      	  } 
      	  else { 
      	    newpos = d->var_index-1+2*i; 
      	    conj = red_multi_variables_eliminate(d->u.ddd.arc[ci].child, 
      	      d->var_index, newpos-1
      	    ); 
      	    if (conj->var_index <= TYPE_TRUE) {
      	      result = red_bop(OR, result, 
      	        ddd_atom(d->var_index, -1 * i, -1 * i)
      	      ); 
      	    }
      	    else if (conj->var_index == newpos) { 
      	      for (cj = 0; cj < conj->u.ddd.child_count; cj++) { 
      	      	gchild = conj->u.ddd.arc[cj].child; 
      	      	for (ck = 0; ck < gchild->u.ddd.child_count; ck++) { 
      	      	  if (gchild->u.ddd.arc[ck].lower_bound > 0) { 
      	      	    sd = ddd_one_constraint(
      	      	      ddd_one_constraint(gchild->u.ddd.arc[ck].child, 
      	      	        newpos+1, 
      	      	        gchild->u.ddd.arc[ck].lower_bound, 
      	      	        gchild->u.ddd.arc[ck].upper_bound
      	      	      ), 
      	      	      newpos, 
      	      	      conj->u.ddd.arc[cj].lower_bound, 
      	      	      conj->u.ddd.arc[cj].upper_bound
      	      	    ); 
      	      	    sd = ddd_one_constraint(sd, d->var_index, -1*i, -1*i); 
      	      	    result = red_bop(OR, result, sd);  
      	      	  }
      	      	  else if (gchild->u.ddd.arc[ck].upper_bound < 0) { 
      	      	    sd = ddd_one_constraint(
      	      	      gchild->u.ddd.arc[ck].child, 
      	      	      d->var_index, 
      	      	      gchild->u.ddd.arc[ck].lower_bound - i, 
      	      	      gchild->u.ddd.arc[ck].upper_bound -i 
      	      	    );  
      	      	    result = red_bop(OR, result, sd); 
      	      	  } 
      	      	  else { 
      	      	    fprintf(RED_OUT, "\nERROR, something fishy!\n"); 
      	      	    bk(0); 
      	      	  } 
      	      	} 
      	      } 
      	    }
      	    else if (conj->var_index == newpos+1) { 
      	      for (cj = 0; cj < conj->u.ddd.child_count; cj++) { 
      	        if (conj->u.ddd.arc[cj].lower_bound > 0) { 
      	          sd = ddd_one_constraint(
      	            ddd_one_constraint(conj->u.ddd.arc[cj].child, 
      	              conj->var_index, 
      	              conj->u.ddd.arc[cj].lower_bound, 
      	              conj->u.ddd.arc[cj].upper_bound
      	            ), 
      	            d->var_index, -1*i, -1*i
      	          ); 
      	          result = red_bop(OR, result, sd);  
      	        }
      	        else if (conj->u.ddd.arc[cj].upper_bound < 0) { 
      	          sd = ddd_one_constraint(
      	            conj->u.ddd.arc[cj].child, 
      	            d->var_index, 
      	            conj->u.ddd.arc[cj].lower_bound - i, 
      	            conj->u.ddd.arc[cj].upper_bound -i 
      	          );  
      	          result = red_bop(OR, result, sd); 
      	        } 
      	        else { 
      	          fprintf(RED_OUT, "\nERROR, something fishy!\n"); 
      	          bk(0); 
      	        } 
      	      } 	
      	    }
      	    else { 
      	      fprintf(RED_OUT, "\nERROR, something fishy here. \n"); 
      	      fprintf(RED_OUT, "       somehow the next block is missing.\n"); 
      	      bk(0); 
      	    } 
      	  }
        } 
      }
    }
    else { 
      fprintf(RED_OUT, "\nERROR, something fishy here. \n"); 
      fprintf(RED_OUT, 
        "       We should not reaced a deep memory variable %1d:%s\n", 
        d->var_index, VAR[d->var_index].NAME
      ); 
      bk(0); 
    } 
  }
  return(ce->result = result);
}
   /* rec_heap_free() */






struct red_type	*red_free_from_exp_sync_bulk(
  struct red_type	*d, 
  int			pi,
  int			xi, 
  int			soi 
) { 
  int			vi, ci; 
  struct red_type	*red_dest, *result, *conj; 
  
  red_dest = red_delayed_exp_value(
    XTION[xi].stream_operation[soi].value_exp, pi, d
  );
  result = NORM_FALSE; 
  for (ci = 0; ci < red_dest->u.ddd.child_count; ci++) { 
    for (vi = red_dest->u.ddd.arc[ci].lower_bound; 
         vi <= red_dest->u.ddd.arc[ci].upper_bound; 
         vi++
         ) { 
      HEAP_RQ_DEST = vi; 
      conj = rec_heap_free(d); 
      result = red_bop(OR, result, conj); 
    } 
  } 

  return(result); 
} 
  /* red_free_from_exp_sync_bulk() */ 



struct red_type	*red_postcondition_stream(
  struct red_type	*d, 
  int			pi, 
  int			xi
) { 
  int	soi, value; 
  char	*sname; 
  
  for (soi = 0; 
    soi < red_query_xtion_attribute(xi, RED_XTION_STREAM_OP_COUNT); 
    soi++
  ) { 
    switch (red_query_xtion_stream_operation(xi, soi)) {
    case RED_XTION_STREAM_OPEN_INPUT: 
      d = red_open_stream(d, 
        XTION[xi].stream_operation[soi].stream, 
        FLAG_STREAM_INPUT
      ); 
      break; 
    case RED_XTION_STREAM_OPEN_OUTPUT: 
      d = red_open_stream(d, 
        XTION[xi].stream_operation[soi].stream, 
        FLAG_STREAM_OUTPUT
      ); 
      break; 
    case RED_XTION_STREAM_CLOSE:
      d = red_close_stream(d, XTION[xi].stream_operation[soi].stream); 
      break; 
    case RED_XTION_STREAM_INPUT: 
      d = red_postcondition_stream_input_sync_bulk(d, pi, xi, soi);  
      break; 
    case RED_XTION_STREAM_OUTPUT: 
      d = red_postcondition_stream_output_sync_bulk(d, pi, xi, soi); 
      break; 
    case RED_XTION_MALLOC: 
      d = red_malloc_from_exp_sync_bulk(d, pi, xi, soi); 
      break; 
    case RED_XTION_FREE: 
      d = red_free_from_exp_sync_bulk(d, pi, xi, soi); 
      break; 
  } } 
  return(d); 
}
  /* red_postcondition_stream() */ 
  
  
  






