/**********************************************************************
 *
 *	Hull form
 *
 *	2002/08/17 strategy for closure near-equivalence form:
 *	
 *	1. red_hull_inactive
 *	2. red_restrict_closure_eq
 *		a. with strict assumption of closure eq form
 *		   and magnitude 2nd constraints
 *		b. find the representatives and translate 
 *		   to equivalent magnitude constraints 
 *		c. merge equivalence classes
 *		d. postprocessing at normalization step 
 *		   we choose to sacrifice the precision in this regard, 
 *	3. saturate
 *		a. red_hull_inactive
 *		b. crd_one_constraint
 *		c. crd_one_constraint_closure 
 * 	4. assignment 
 *		a. combine red_hull_inactive, crd_one_constraint, and 
 *		   red_
 
 
	2007/10/14 We have temporarily disabled the funciton 
	of red_push_big_timing_constant(). 
	The procedure works to push all clock upper-bounds greater than 
	the biggest timing constant that will be used by the corresponding 
	clock according to the operation modes. 
	At this moment, it is only used if no backward analysis will be 
	used.  
	Thus it may not affect the performance in general since 
	in most cases, we don't work on forward analysis alone. 
	But I suspect that a special benchmarks might be affected, like 
	Leader or Pathos. 
	But I am not sure. 
	In the future, we may extend and reinstall this procedures in 
	both forward and backward analysis. 
	But this could be challenging since it may affect our 
	interpretation of CLOCK_POS_INFINITY and CLOCK_NEG_INFINITY. 
	The new interpretation of the two constants can then 
	affect the meaning of many other procedures. 
	So we need be careful in this issue. 
 */

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

#include "redparse.h"
#include "exp.e" 

#include "redbop.h"
#include "redbop.e"

#include "zone.h" 

#include "hybrid.e"

#include "redsymmetry.e"

#include "inactive.e"
#include "redparse.e"

#include "treeman.h" 
#include "treeman.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "bisim.e" 


#define	DETOUR_FIXED	-2 
#define	DETOUR_TERMINAL	-1 

extern int	count_subtract_iterative; 
int		count_zk = 0; 
int 	count_tpb = 0; 

int 	bchild_count, bchild_link_count; 

int		HF_PSTART_CI, HF_PSTOP_CI, 
		HF_PUB, HF_PLB, HF_PSTART, HF_PSTOP; 
int		HF_CSTART_CI, HF_CSTOP_CI, HF_PBOUND; 

struct red_type	*RED_INVARIANCE_DISCONTINUITY, *RED_INVARIANCE_CONTINUITY; 


struct index_link_type	***ZONE_CONSTANT; 

int	*flag_clock; 

#if defined(RED_REGRESS_CHECKING) || defined(RED_DEBUG_ZONE_MODE_TIME_MEASURE)
double	start_time_progress, 
	acc_time_time_progress = 0.0, 
        acc_time_overhead_time_progress = 0.0, 
        acc_time_overhead_split_convexities = 0.0, 
        acc_time_overhead_shared_concavities = 0.0, 
        acc_time_overhead_easy_concavities = 0.0, 
        acc_time_normalization = 0.0; 
int	count_time_progress_bck = 0, 
	count_split_convexity = 0, 
	count_assumed_convexity = 0, 
	count_full_formulation = 0, 
	count_easy_concavity = 0,  
	count_shared_concavity = 0; 
#endif 


        
// The following structure is purely used to record the path components for 
// time-progress operations.  
// Since we don't want to interfere with stack RT, 
// zone.c keeps a little stack of its own. 
// The diagrams maintained by this structures are to be protected 
// by tokens so as to be module-independent with hashman.c.  

/* 
int	*flag_progress, *flag_new_progress, 
	BYPASS_LARGE_BOUND; 
*/

struct red_type	*(*RED_BYPASS_BCK)(), *(*RED_BYPASS_FWD)(); 



#define	TEST_COUNT	-1
int	cross_count; 

int	ttop, testm[100]; 


#if defined(RED_REGRESS_CHECKING) || defined(RED_DEBUG_ZONE_MODE_TIME_MEASURE)
void 	print_time_progress_overhead_statistics(
  char 		*f, 
  ... 
) { 
  char		*real_f; 
  va_list	args; 
  double	tmp_time_progress; 
  
  string_var(real_f, NULL, NULL, f, args);  
  
  tmp_time_progress = red_user_time();
  fprintf(RED_OUT, "\nTIME PROGRESS: %s\n", real_f); 
  fprintf(RED_OUT, "acc %.6fs, overhead %.6fs[", 
    acc_time_time_progress + tmp_time_progress - start_time_progress, 
    acc_time_overhead_time_progress 
  );   
  fprintf(RED_OUT, 
    "split %.6fs, sh. concavities %.6fs, ez. concavities %.6fs]\n ", 
    acc_time_overhead_split_convexities, 
    acc_time_overhead_shared_concavities,  
    acc_time_overhead_easy_concavities 
  );   
  /*
  fprintf(RED_OUT, "[SHARED:%1d; DATA:%1d; STACK:%1d]%%%%\n", usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
  */
  fflush(RED_OUT); 
}
  /* print_time_progress_overhead_statistics() */ 





void	update_time_progress_overhead_statistics(
  double	time_time_progress, 
  double	time_overhead_time_progress, 
  double	time_overhead_split_convexities, 
  double	time_overhead_shared_concavities, 
  double	time_overhead_easy_concavities, 
  char 		*f, 
  ... 
) {
  char			*real_f; 
  va_list		args; 
  
  acc_time_time_progress = acc_time_time_progress + time_time_progress;  
  acc_time_overhead_time_progress 
  = acc_time_overhead_time_progress + time_overhead_time_progress;  
  acc_time_overhead_split_convexities  
  = acc_time_overhead_split_convexities + time_overhead_split_convexities; 
  acc_time_overhead_shared_concavities 
  = acc_time_overhead_shared_concavities + time_overhead_shared_concavities; 
  acc_time_overhead_easy_concavities 
  = acc_time_overhead_easy_concavities + time_overhead_easy_concavities; 
  
  string_var(real_f, NULL, NULL, f, args);  
  
  fprintf(RED_OUT, "\nTIME PROGRESS: %s\n", real_f); 
  fprintf(RED_OUT, "acc %.6fs, overhead %.6fs[", 
    acc_time_time_progress, 
    acc_time_overhead_time_progress 
  );   
  fprintf(RED_OUT, 
    "split %.6fs, sh. concavities %.6fs, ez. concavities %.6fs]\n ", 
    acc_time_overhead_split_convexities, 
    acc_time_overhead_shared_concavities,  
    acc_time_overhead_easy_concavities 
  );   
  /*
  fprintf(RED_OUT, "[SHARED:%1d; DATA:%1d; STACK:%1d]%%%%\n", usage.ru_ixrss, usage.ru_idrss, usage.ru_isrss);
  */
  fflush(RED_OUT); 
}
  /* update_time_progress_overhead_statistics() */ 



void 	print_time_progress_statistics(
  char 	*f, 
  ... 
) { 
  char		*real_f; 
  va_list	args; 
  double	tmp_time_progress; 
  
  string_var(real_f, NULL, NULL, f, args);  
  
  fprintf(RED_OUT, "\nTIME PROGRESS: %s\n", real_f); 
  fprintf(RED_OUT, "Total time: %.6fs; total time progress time: %.6fs.\n", 
    red_user_time(), acc_time_time_progress
  ); 
  fprintf(RED_OUT, "# time progres:      %1d\n", count_time_progress_bck); 
  fprintf(RED_OUT, "# assumed convexity: %1d\n", count_assumed_convexity); 
  fprintf(RED_OUT, "# full formulation:  %1d\n", count_full_formulation); 
  fprintf(RED_OUT, "# shared concavity:  %1d\n", count_shared_concavity); 
  fprintf(RED_OUT, "# split convexity:   %1d\n", count_split_convexity); 
  fprintf(RED_OUT, "# easy concavity:    %1d\n", count_easy_concavity); 
  fflush(RED_OUT);  
}
  /* print_time_progress_statistics() */ 




void	update_time_progress_statistics(int time_op) {
  if (count_time_progress_bck == 0) 
    fprintf(RED_OUT, "\n0000>>");  

  count_time_progress_bck++; 
  acc_time_time_progress = acc_time_time_progress 
  + red_user_time() - start_time_progress;  
  switch (time_op) { 
  case FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY: 
    count_assumed_convexity++;  
    if (count_time_progress_bck % 10) 
      fprintf(RED_OUT, "c"); 
    else if (count_time_progress_bck % 50)
      fprintf(RED_OUT, "C"); 
    else 
      fprintf(RED_OUT, "C\n%4d>>", count_time_progress_bck);  
    break;  

  case FLAG_TIME_PROGRESS_FULL_FORMULATION:  
    count_full_formulation++;  
    if (count_time_progress_bck % 10) 
      fprintf(RED_OUT, "f"); 
    else if (count_time_progress_bck % 50)
      fprintf(RED_OUT, "F"); 
    else 
      fprintf(RED_OUT, "F\n%4d>>", count_time_progress_bck);  
    break; 
    
  case FLAG_TIME_PROGRESS_SHARED_CONCAVITY: 
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    count_shared_concavity++; 
    if (count_time_progress_bck % 10) 
      fprintf(RED_OUT, "h"); 
    else if (count_time_progress_bck % 50)
      fprintf(RED_OUT, "H"); 
    else 
      fprintf(RED_OUT, "H\n%4d>>", count_time_progress_bck);  
    break; 

  case FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES:  
  case FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 	
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 
  case FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 
    count_split_convexity++;  
    if (count_time_progress_bck % 10) 
      fprintf(RED_OUT, "s"); 
    else if (count_time_progress_bck % 50)
      fprintf(RED_OUT, "S"); 
    else 
      fprintf(RED_OUT, "S\n%4d>>", count_time_progress_bck);  
    break; 

  case FLAG_TIME_PROGRESS_EASY_CONCAVITY:  
  case FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY:  
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY:  
    count_easy_concavity++; 
    if (count_time_progress_bck % 10) 
      fprintf(RED_OUT, "e"); 
    else if (count_time_progress_bck % 50)
      fprintf(RED_OUT, "E"); 
    else 
      fprintf(RED_OUT, "E\n%4d>>", count_time_progress_bck);  
    break; 
  default: 
    fprintf(RED_OUT, "\nError: Illegal time progress operation %1d.\n", 
      time_op
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  fflush(RED_OUT); 
}
  /* update_time_progress_statistics() */ 
#endif 



void	print_testm() 
{
  int	i; 

  for (i = 0; i < ttop; i++) 
    fprintf(RED_OUT, "m[%1d]=%1d; ", i, testm[i]); 
  fprintf(RED_OUT, "\n"); 
}
/* print_testm() */ 




struct zone_xaction_type {
  int	var_index, clock1, clock2, upper_bound; 
}; 

int				**ZONE_RECORD;

char	string_ub[20]; 
char	*string_zone_ub(b) 
	int	b; 
{ 
  if (b == CLOCK_POS_INFINITY) { 
    return("<oo"); 	
  } 
  else if (b == CLOCK_NEG_INFINITY) { 
    return("<-oo"); 	
  } 
  else if (b < CLOCK_NEG_INFINITY || b > CLOCK_POS_INFINITY) 
    fprintf(RED_OUT, "Warning, an out of range infinity %1d.\n", b); 
  else if (b % 2) { 
    sprintf(string_ub, "<%1d", (b+1)/2); 
    return(string_ub); 
  } 
  else { 
    sprintf(string_ub, "<=%1d", b/2); 
    return(string_ub); 	
  } 
}
  /* string_zone_ub() */ 
  
  
  

int	zone_ub_add(d1, d2)
     int	d1, d2;
{
  int	s;

  if (d1 == CLOCK_POS_INFINITY || d2 == CLOCK_POS_INFINITY)
    return(CLOCK_POS_INFINITY);

  if ((d1 % 2) && (d2 % 2))
    s = d1 + d2 + 1;
  else
    s = d1 + d2;

  if (s >= CLOCK_POS_INFINITY)
    return(CLOCK_POS_INFINITY);
  else if (s <= CLOCK_NEG_INFINITY)
    return(CLOCK_NEG_INFINITY);
  else
    return(s);
}
/* zone_ub_add() */


  
  
  
//081215 CHANGE
int	zone_ub_add_unbounded(d1, d2)
     int	d1, // d1 is unbounded
     		d2; // d2 is bounded by CLOCK_POS_INFINITY 
{
  int	s;

  if ((d1 % 2) && (d2 % 2))
    s = d1 + d2 + 1;
  else
    s = d1 + d2;

  return(s);
}
/* zone_ub_add_unbounded() */





/* When this routine returns -oo, then the difference is not decided and should not
 * be used to eliminate redundant inequalities.
 */
zone_ub_subtract(d1, d2)
	int	d1, d2;
{
  int	s;

  if (d1 == CLOCK_POS_INFINITY)
/*
    if (d2 <= 0)
*/
      return (CLOCK_POS_INFINITY);
/*
    else if (CLOCK_POS_INFINITY)
      return(CLOCK_NEG_INFINITY);
    else if (d2 % 2)
      return(d1-d2 - 1);
    else
      return(d1 - d2 - 2);
*/
  else if (d2 == CLOCK_NEG_INFINITY)
/*
    if (d1 >= 0)
*/
      return(CLOCK_POS_INFINITY);
/*
    else if (d1 == CLOCK_NEG_INFINITY)
      return(CLOCK_NEG_INFINITY);
    else if (d1 % 2)
      return(d1 - d2 - 1);
    else
      return(d1-d2);
*/
  /*
  else if (d1 == CLOCK_POS_INFINITY) {
    fprintf(RED_OUT, "\nHow comes ? \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    for (; 1; );
    exit(0);
  }
  */
  s = d1-d2;

  if (s >= CLOCK_POS_INFINITY)
    return(CLOCK_POS_INFINITY-1);
  else if (s <= CLOCK_NEG_INFINITY)
    return(CLOCK_NEG_INFINITY);
  else
    return(s);
}
/* zone_ub_subtract() */


int	old_zone_lb_subtract(d1, d2)
     int	d1, d2;
{
  int	s;

  if (d1 == CLOCK_NEG_INFINITY || d2 == CLOCK_POS_INFINITY)
    return(CLOCK_NEG_INFINITY);

  if ((d1 % 2) && (d2 % 2))
    s = d1 - d2 - 2;
  else
    s = d1 - d2;

  if (s >= CLOCK_POS_INFINITY)
    return(CLOCK_POS_INFINITY);
  else if (s <= CLOCK_NEG_INFINITY)
    return(CLOCK_NEG_INFINITY);
  else
    return(s);
}
/* old_zone_lb_subtract() */




int	zone_lb_subtract(d1, d2)
     int	d1, d2;
{
  int	s;

  if (d1 == CLOCK_NEG_INFINITY || d2 == CLOCK_POS_INFINITY)
    return(CLOCK_NEG_INFINITY);
  /*
  else if (d1 == CLOCK_POS_INFINITY) {
    fprintf(RED_OUT, "\nHow comes ? \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    for (; 1; );
    exit(0); 
  } 
  */
  if (d1 % 2) 
    if (d2 % 2)
      s = d1 - d2 - 2; 
    else 
      s = d1 - d2 - 1; 
  else 
    if (d2 % 2) 
      s = d1 - d2 - 1; 
    else 
      s = d1 - d2; 

  if (s >= CLOCK_POS_INFINITY)
    return(CLOCK_POS_INFINITY); 
  else if (s <= CLOCK_NEG_INFINITY)
    return(CLOCK_NEG_INFINITY); 
  else
    return(s); 
}
/* zone_lb_subtract() */ 




struct red_type	*red_clock_exclusion(vi, ci, cj) 
     int	vi, ci, cj;
{
  int			tmp; 
  struct red_type	*result; 

  if (ci > cj) {
    tmp = ci; 
    ci = cj;
    cj = tmp; 
  }

  if (ci == 0) {
    result = NORM_FALSE; 
  }
  else 
    result = ddd_atom(vi, 0, ci-1); 

  if (ci+1 < cj) {
    result = red_bop(OR, result, ddd_atom(vi, ci+1, cj-1));
  }

  if (cj < CLOCK_COUNT-1)
    result = red_bop(OR, result, ddd_atom(vi, cj+1, CLOCK_COUNT-1));

  return(result);
}
/* red_clock_exclusion() */





old_filter_minimal_not_equivalences()
{
  int 	ci, cj;
  struct red_type	*subresult;

  FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE = (struct red_type ***) malloc(CLOCK_COUNT*sizeof(struct red_type **));
  FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE = (struct red_type ***) malloc(CLOCK_COUNT*sizeof(struct red_type **));

  for (ci = 0; ci < CLOCK_COUNT; ci++) {
    FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci] = (struct red_type **) malloc(CLOCK_COUNT*sizeof(struct red_type *));
    FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci]
      = (struct red_type **) malloc(CLOCK_COUNT*sizeof(struct red_type *));

    for (cj = 0; cj < CLOCK_COUNT; cj++) {
      if (ci == cj) {
	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj] = NULL;
	FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj] = NULL;
	continue;
      }

      /********************************************************************************************
       * First, the negative cases used when v(ci) >= v(cj).
       */
      /* case 1: there is a ck, v(ck)=v(ci)+d with d>0 */
      FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	= red_bop(AND,
		  red_bop(AND,
			  ddd_atom(HF_PSTART_VI, ci, ci),
			  red_clock_exclusion(HF_PSTOP_VI, ci, cj)
			  ),
		  red_bop(AND,
			  ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
			  ddd_atom(VI_VALUE, CLOCK_NEG_INFINITY, -1)
			  )
		  );

      /* case 2: there is a ck, v(ck)+d=v(cj) with d>0 */
      FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	= red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		  red_bop(AND,
			  red_bop(AND,
				  red_clock_exclusion(HF_PSTART_VI, ci, cj),
				  ddd_atom(HF_PSTOP_VI, cj, cj)
				  ),
			  red_bop(AND,
				  ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
				  ddd_atom(VI_VALUE, CLOCK_NEG_INFINITY, -1)
				  )
			  )
		  );

      /* case 3: c(vi)=v(cj) */
      if (ci < cj) {
	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	  = red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		    red_bop(AND,
			    red_bop(AND,
				    ddd_atom(HF_PSTART_VI, ci, ci),
				    ddd_atom(HF_PSTOP_VI, cj, cj)
				    ),
			    ddd_atom(VI_VALUE, 0, 0)
			    )
		    );
      }

      /* case 4: there is a ck > ci, v(ck)=v(ci) */
      if (ci < CLOCK_COUNT-1) {
	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	  = red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		    red_bop(AND,
			    red_bop(AND,
				    ddd_atom(HF_PSTART_VI, ci, ci),
				    ddd_atom(HF_PSTOP_VI, ci+1, CLOCK_COUNT-1)
				    ),
			    red_bop(AND,
				    ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
				    ddd_atom(VI_VALUE, 0, 0)
				    )
			    )
		    );
      }

      /* case 5: there is a ck < cj, v(ck)=v(cj) */
      if (cj > 0) {
	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	  = red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		    red_bop(AND,
			    red_bop(AND,
				    ddd_atom(HF_PSTART_VI, cj, cj),
				    ddd_atom(HF_PSTOP_VI, 0, cj-1)
				    ),
			    red_bop(AND,
				    ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
				    ddd_atom(VI_VALUE, 0, 0)
				    )
			    )
		    );
      }

      red_mark(FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj], FLAG_GC_STABLE);
      /*
      fprintf(RED_OUT, "FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci=%1d][cj=%1d]", ci, cj);
      red_print_graph(FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]);
      */

      /********************************************************************************************
       * Second, the positive case is used when v(ci) < v(cj)
       */
      /* case 1: v*/
      if (ci < CLOCK_COUNT-1)
	FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj]
	  = red_bop(AND,
		    red_bop(AND,
			    ddd_atom(HF_PSTART_VI, ci, ci),
			    ddd_atom(HF_PSTOP_VI, ci+1, CLOCK_COUNT-1)
			    ),
		    red_bop(AND,
			    ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
			    ddd_atom(VI_VALUE, 0, 0)
			    )
		    );
      else
	FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj] = NORM_FALSE;

      if (cj > 0)
	FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj]
	  = red_bop(OR, FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj],
		    red_bop(AND,
			    red_bop(AND,
				    ddd_atom(HF_PSTART_VI, 0, cj-1),
				    ddd_atom(HF_PSTOP_VI, cj, cj)
				    ),
			    red_bop(AND,
				    ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE),
				    ddd_atom(VI_VALUE, 0, 0)
				    )
			    )
		    );

      red_mark(FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj], FLAG_GC_STABLE);
      /*
      fprintf(RED_OUT, "FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci=%1d][cj=%1d]: \n", ci, cj);
      red_print_graph(FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj]);
      */
      garbage_collect(FLAG_GC_SILENT);
    }
  }
}
/* old_filter_minimal_not_equivalences() */






filter_reduced_not_equivalences()
{
  int 	ci, cj;
  struct red_type	*subresult;

  FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE = (struct red_type ***) malloc(CLOCK_COUNT*sizeof(struct red_type **));
  FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE = (struct red_type ***) malloc(CLOCK_COUNT*sizeof(struct red_type **));

  for (ci = 0; ci < CLOCK_COUNT; ci++) {
    FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci] = (struct red_type **) malloc(CLOCK_COUNT*sizeof(struct red_type *));
    FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci]
      = (struct red_type **) malloc(CLOCK_COUNT*sizeof(struct red_type *));

    for (cj = 0; cj < CLOCK_COUNT; cj++) {
      if (ci == cj) {
	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj] = NULL;
	FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj] = NULL;
	continue;
      }
      else if (ci > cj) {
        FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj] = NORM_NO_RESTRICTION;
        FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj] = NORM_FALSE;
	if (ci < CLOCK_COUNT-1)
	  FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	    = red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		      red_bop(AND, ddd_atom(HF_PSTART_VI, ci, ci),
			      ddd_atom(HF_PSTOP_VI, ci+1, CLOCK_COUNT-1)
			      )
		      );
	if (cj > 0)
	  FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	    = red_bop(OR, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		      red_bop(AND, ddd_atom(HF_PSTART_VI, 0, cj-1),
			      ddd_atom(HF_PSTOP_VI, cj, cj)
			      )
		      );

	FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]
	  = red_bop(AND, FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj],
		    ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE)
		    );

        red_mark(FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj], FLAG_GC_STABLE);
        /*
        fprintf(RED_OUT, "FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci=%1d][cj=%1d]", ci, cj);
        red_print_graph(FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj]);
        */
      }
      /********************************************************************************************
       * Second, the positive case is used when v(ci) < v(cj)
       */
      /* case 1: v*/
      else {
        FILTER_NOT_DIRECT_NEGATIVE_EQUIVALENCE[ci][cj] = NORM_NO_RESTRICTION;
        FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj] = ddd_atom(VI_OP, TYPE_FALSE, TYPE_FALSE);
	if (ci+1 < cj)
	  FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj]
	    = red_bop(OR, FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj],
		      red_bop(AND,
		      	      red_bop(AND,
				      ddd_atom(HF_PSTART_VI, ci, ci),
				      ddd_atom(HF_PSTOP_VI, ci+1, cj-1)
				      ),
			      ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE)
			      )
		      );

        red_mark(FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj], FLAG_GC_STABLE);
      }
      /*
      fprintf(RED_OUT, "FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci=%1d][cj=%1d]: \n", ci, cj);
      red_print_graph(FILTER_NOT_DIRECT_POSITIVE_EQUIVALENCE[ci][cj]);
      */
      garbage_collect(FLAG_GC_SILENT);
    }
  }
}
/* filter_reduced_not_equivalences() */






filter_reduced_not_nonzero_transitivities()
{
  int	ci;

  FILTER_NOT_NONZERO_XTIVE_LEFT = (struct red_type **) malloc(CLOCK_COUNT * sizeof(struct red_type *));
  FILTER_NOT_NONZERO_XTIVE_RIGHT = (struct red_type **) malloc(CLOCK_COUNT * sizeof(struct red_type *));

  for (ci = 0; ci < CLOCK_COUNT; ci++) {
    if (ci == 0)
      FILTER_NOT_NONZERO_XTIVE_LEFT[ci] = NORM_FALSE;
    else
      FILTER_NOT_NONZERO_XTIVE_LEFT[ci] = red_bop(AND, ddd_atom(HF_PSTART_VI, 0, ci-1),
						  red_bop(AND,
							  ddd_atom(HF_PSTOP_VI, ci, ci),
							  ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE)
							  )
						  );
    if (ci == CLOCK_COUNT-1)
      FILTER_NOT_NONZERO_XTIVE_RIGHT[ci] = NORM_FALSE;
    else
      FILTER_NOT_NONZERO_XTIVE_RIGHT[ci] = red_bop(AND, ddd_atom(HF_PSTART_VI, ci, ci),
						   red_bop(AND,
							   ddd_atom(HF_PSTOP_VI, ci+1, CLOCK_COUNT-1),
							   ddd_atom(VI_OP, TYPE_TRUE, TYPE_TRUE)
							   )
						   );
    red_mark(FILTER_NOT_NONZERO_XTIVE_LEFT[ci], FLAG_GC_STABLE);
    red_mark(FILTER_NOT_NONZERO_XTIVE_RIGHT[ci], FLAG_GC_STABLE);
    /*
    fprintf(RED_OUT, "\nFILTER_NOT_NONZERO_XTIVE_LEFT[ci=%1d]\n", ci);
    red_print_graph(FILTER_NOT_NONZERO_XTIVE_LEFT[ci]);
    fprintf(RED_OUT, "\nFILTER_NOT_NONZERO_XTIVE_RIGHT[ci=%1d]\n", ci);
    red_print_graph(FILTER_NOT_NONZERO_XTIVE_RIGHT[ci]);
    */
    garbage_collect(FLAG_GC_SILENT);
  }
}
/* filter_reduced_not_nonzero_transitivities() */







/* This routine is only called when d is of type clock inequality with clock1 < clock2. 
 * The routine only eliminate negatives between the first two layers. 
 */
struct red_type	*red_simple_cycle_eliminate(d)
     struct red_type	*d; 
{
  struct red_type	*conj; 
  int			ci, cj, lb; 
  struct crd_child_type	*bic, *bjc; 

  child_stack_level_push(); 
  for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
    bic = &(d->u.crd.arc[ci]); 
    if (   bic->child == NORM_TRUE 
        || bic->child->var_index > VAR[d->var_index].U.CRD.CONVERSE_CRD_VI
        ) 
      conj = bic->child; 
    else { 
      child_stack_level_push(); 
      for (cj = bic->child->u.crd.child_count - 1; cj >= 0; cj--) { 
	bjc = &(bic->child->u.crd.arc[cj]);
	lb = zone_ub_add(bic->upper_bound, bjc->upper_bound); 
	if (lb < 0) 
	  break; 
	
	bchild_stack_push(bjc->child, bjc->upper_bound); 
      }
      
      conj = crd_new(bic->child->var_index); 
    }
    
    if (conj == NORM_FALSE) 
      continue; 

    bchild_stack_push(conj, bic->upper_bound); 
  } 
  
/*
  if (child_count == 0) {
    child_stack_level_pop(); 
    conj = NORM_FALSE; 
  }
  else if (   child_count == 1 
           && CHILD_STACK[TOP_CHILD_STACK].ub == CLOCK_POS_INFINITY
           ) {
    conj = CHILD_STACK[TOP_CHILD_STACK].d;
    child_stack_pop(); 
    child_stack_level_pop(); 
  }
  else
*/  
  conj = crd_new(d->var_index);
  return(conj);
}
/* red_simple_cycle_eliminate() */




struct red_type		*rec_zone_intersect();


struct red_type	*rec_zone_intersect_right(dx, dy)
  struct red_type	*dx, *dy;
{
  int			child_count, ciy, lb, ub;
  struct red_type	*new_child, *conj;
  struct crd_child_type	*bcy;
  char			*cstack;
  struct ddd_child_type	*icy;

  switch (VAR[dy->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ciy = dy->u.crd.child_count - 1; ciy >= 0; ciy--) {
      bcy = &(dy->u.crd.arc[ciy]);
      new_child = rec_zone_intersect(dx, bcy->child);

      if (new_child == NORM_FALSE)
	continue;

      bchild_stack_insert(new_child, bcy->upper_bound);
    }

/*
    if (child_count == 0) {
      child_stack_level_pop(); 
      return(NORM_FALSE);
    }
    else if (   child_count == 1 
             && CHILD_STACK[TOP_CHILD_STACK].ub == CLOCK_POS_INFINITY
             ) {
      child_stack_pop(); 
      child_stack_level_pop(); 
      return(new_child);
    }
    else {
*/      new_child = crd_new(dy->var_index);
      if (VAR[dy->var_index].U.CRD.CLOCK1 < VAR[dy->var_index].U.CRD.CLOCK2) {
        new_child = red_simple_cycle_eliminate(new_child);
      }
      return(new_child);
/*
    }
*/
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ciy = dy->u.fdd.child_count - 1; ciy >= 0; ciy--) {
      new_child = rec_zone_intersect(dx, dy->u.fdd.arc[ciy].child);

      if (new_child == NORM_FALSE)
	continue;

      fchild_stack_push(new_child, dy->u.fdd.arc[ciy].lower_bound, 
        dy->u.fdd.arc[ciy].upper_bound
      );
    }

    conj = fdd_new(dy->var_index);
    return(conj);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ciy = dy->u.dfdd.child_count - 1; ciy >= 0; ciy--) {
      new_child = rec_zone_intersect(dx, dy->u.dfdd.arc[ciy].child);

      if (new_child == NORM_FALSE)
	continue;

      dfchild_stack_push(new_child, dy->u.dfdd.arc[ciy].lower_bound, 
        dy->u.dfdd.arc[ciy].upper_bound
      );
    }

    conj = dfdd_new(dy->var_index);
    return(conj);
    break;

  default:
    child_stack_level_push();
    for (ciy = dy->u.ddd.child_count - 1; ciy >= 0; ciy--) {
      icy = &(dy->u.ddd.arc[ciy]);
      new_child = rec_zone_intersect(dx, icy->child);

      if (new_child == NORM_FALSE)
	continue;

      ichild_stack_push(new_child, icy->lower_bound, icy->upper_bound);
    }

/*
    if (child_count == 0) {
      child_stack_level_pop(); 
      return(NORM_FALSE);
    }
    else if (child_count == 1
	&& CHILD_STACK[TOP_CHILD_STACK].lb == VAR[dy->var_index].LB
	&& CHILD_STACK[TOP_CHILD_STACK].ub == VAR[dy->var_index].U.DISC.UB
	) {
      child_stack_level_pop();
      child_stack_pop(); 
      return(new_child);
    }
    else {
*/
      conj = ddd_new(dy->var_index);
      return(conj);
/*
    }
*/
  }
}
/* rec_zone_intersect_right() */







struct red_type	*rec_zone_intersect_left(dx, dy)
  struct red_type	*dx, *dy;
{
  int			cix, lb, ub;
  struct red_type	*new_child, *conj;
  struct crd_child_type	*bcx;
  char			*cstack;
  struct ddd_child_type	*icx;

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count - 1; cix >= 0; cix--) {
      bcx = &(dx->u.crd.arc[cix]);
      new_child = rec_zone_intersect(bcx->child, dy);

      if (new_child == NORM_FALSE)
	continue;

      bchild_stack_insert(new_child, bcx->upper_bound);
    }

/*
    if (child_count == 0) {
      child_stack_level_pop(); 
      return(NORM_FALSE);
    }
    else if (   child_count == 1 
             && CHILD_STACK[TOP_CHILD_STACK].ub == CLOCK_POS_INFINITY
             ) {
      child_stack_level_pop();
      child_stack_pop(); 
      return(new_child);
    }
    else {
*/
      new_child = crd_new(dx->var_index);
      if (VAR[dx->var_index].U.CRD.CLOCK1 < VAR[dx->var_index].U.CRD.CLOCK2) {
        new_child = red_simple_cycle_eliminate(new_child);
      }
      return(new_child);
/*
    }
*/
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (cix = dx->u.fdd.child_count - 1; cix >= 0; cix--) {
      new_child = rec_zone_intersect(dx->u.fdd.arc[cix].child, dy);

      if (new_child == NORM_FALSE)
	continue;

      fchild_stack_push(new_child, 
        dx->u.fdd.arc[cix].lower_bound, dx->u.fdd.arc[cix].upper_bound
      );
    }

    conj = fdd_new(dx->var_index);
    return(conj);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (cix = dx->u.dfdd.child_count - 1; cix >= 0; cix--) {
      new_child = rec_zone_intersect(dx->u.dfdd.arc[cix].child, dy);

      if (new_child == NORM_FALSE)
	continue;

      fchild_stack_push(new_child, 
        dx->u.dfdd.arc[cix].lower_bound, dx->u.dfdd.arc[cix].upper_bound
      );
    }

    conj = dfdd_new(dx->var_index);
    return(conj);
    break;
  default:
    child_stack_level_push();
    for (cix = dx->u.ddd.child_count - 1; cix >= 0; cix--) {
      icx = &(dx->u.ddd.arc[cix]);
      new_child = rec_zone_intersect(icx->child, dy);

      if (new_child == NORM_FALSE)
	continue;

      ichild_stack_push(new_child, icx->lower_bound, icx->upper_bound);
    }

    conj = ddd_new(dx->var_index);
    return(conj);
  }
}
/* red_zone_intersect_left() */






int	TS_ZONE_INTERSECT; 

struct red_type	*rec_zone_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  int				b, lb, ub, cix, ciy;
  struct red_type		*new_child;
  struct crd_child_type		*bcx, *bcy;
  struct ddd_child_type		*icx, *icy;
  struct cache2_hash_entry_type	*ce; 

  if (dx == NORM_NO_RESTRICTION && dy == NORM_NO_RESTRICTION)
    return(NORM_NO_RESTRICTION);

  ce = cache2_check_result_key(OP_ZONE_INTERSECT, dx, dy); 
  if (ce->result) {
    return(ce->result); 
  } 

  if ((dx != NORM_NO_RESTRICTION && dx->var_index < dy->var_index) || dy == NORM_NO_RESTRICTION)
    return(ce->result = rec_zone_intersect_left(dx, dy));
  else if ((dy != NORM_NO_RESTRICTION && dx->var_index > dy->var_index) || dx == NORM_NO_RESTRICTION)
    return(ce->result = rec_zone_intersect_right(dx, dy));

  switch (VAR[dx->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (cix = dx->u.crd.child_count - 1; cix >= 0; cix--) {
      bcx = &(dx->u.crd.arc[cix]);
      for (ciy = dy->u.crd.child_count - 1; ciy >= 0; ciy--) {
	bcy = &(dy->u.crd.arc[ciy]);
	new_child = rec_zone_intersect(bcx->child, bcy->child);

	if (new_child == NORM_FALSE)
	  continue;

	if (bcx->upper_bound < bcy->upper_bound)
	  b = bcx->upper_bound;
	else
	  b = bcy->upper_bound;

	bchild_stack_insert(new_child, b);
      }
    }

/*
    if (child_count == 0) {
      child_stack_level_pop(); 
      return(ce->result = NORM_FALSE); 
    }
    else if (   child_count == 1 
             && CHILD_STACK[TOP_CHILD_STACK].ub == CLOCK_POS_INFINITY
             ) {
      child_stack_pop(); 
      child_stack_level_pop();  
      return(ce->result = new_child);
    }
    else {
*/
      ce->result = crd_new(dx->var_index);
      if (VAR[dx->var_index].U.CRD.CLOCK1 < VAR[dx->var_index].U.CRD.CLOCK2) {
        ce->result = red_simple_cycle_eliminate(ce->result);
      }
      return(ce->result);
/*
    }
*/
    break;

  case TYPE_FLOAT: {
    float	flb, fub; 
    
    child_stack_level_push();

    for (last_fchild(dx, dy, &cix, &ciy, &flb, &fub);
	 cix >= 0 && ciy >= 0;
	 advance_fchild(dx, dy, &cix, &ciy, &flb, &fub)
	 ){
      if (   cix >= 0 
          && dx->u.fdd.arc[cix].lower_bound <= flb 
          && fub <= dx->u.fdd.arc[cix].upper_bound)
	if (   ciy >= 0 
	    && dy->u.fdd.arc[ciy].lower_bound <= flb 
	    && fub <= dy->u.fdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_zone_intersect(
	    dx->u.fdd.arc[cix].child, dy->u.fdd.arc[ciy].child
	  );
	  fchild_stack_push(new_child, flb, fub);
	}
    }

    return(ce->result = fdd_new(dx->var_index));
    break;
  }
  case TYPE_DOUBLE: {
    double	dflb, dfub; 
    
    child_stack_level_push();

    for (last_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub);
	 cix >= 0 && ciy >= 0;
	 advance_dfchild(dx, dy, &cix, &ciy, &dflb, &dfub)
	 ){
      if (   cix >= 0 
          && dx->u.dfdd.arc[cix].lower_bound <= dflb 
          && dfub <= dx->u.dfdd.arc[cix].upper_bound)
	if (   ciy >= 0 
	    && dy->u.dfdd.arc[ciy].lower_bound <= dflb 
	    && dfub <= dy->u.dfdd.arc[ciy].upper_bound
	    ) {
	  new_child = rec_zone_intersect(
	    dx->u.dfdd.arc[cix].child, dy->u.dfdd.arc[ciy].child
	  );
	  dfchild_stack_push(new_child, dflb, dfub);
	}
    }

    return(ce->result = dfdd_new(dx->var_index));
    break;
  }
  default:
    child_stack_level_push();

    for (last_ichild(dx, dy, &cix, &ciy, &lb, &ub);
	 cix >= 0 && ciy >= 0;
	 advance_ichild(dx, dy, &cix, &ciy, &lb, &ub)
	 ){
      if (cix >= 0 && dx->u.ddd.arc[cix].lower_bound <= lb && ub <= dx->u.ddd.arc[cix].upper_bound)
	if (ciy >= 0 && dy->u.ddd.arc[ciy].lower_bound <= lb && ub <= dy->u.ddd.arc[ciy].upper_bound) {
	  new_child = rec_zone_intersect(dx->u.ddd.arc[cix].child, dy->u.ddd.arc[ciy].child);
	  ichild_stack_push(new_child, lb, ub);
	}
    }

    return(ce->result = ddd_new(dx->var_index));
  }
}
  /* rec_zone_intersect() */




struct red_type	*zone_intersect(dx, dy)
     struct red_type	*dx, *dy;
{
  struct red_type	*result;
  int			w;

  /*
  if (dx->var_index == TYPE_FALSE && dx != NORM_FALSE) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (dx->var_index == TYPE_TRUE && dx != NORM_TRUE) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  if (dy->var_index == TYPE_FALSE && dy != NORM_FALSE) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (dy->var_index == TYPE_TRUE && dy != NORM_TRUE) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  result = rec_zone_intersect(dx, dy);

  return(result);
}
/* zone_intersect() */






/*************************************************************************************
*
*/
int	XVI, XFI, XVJ, XBI, XBJ, XTYPE, XLB, XUB;
int	XLAST_BIT, XPI, XPJ;







/*****************************************************************************************
 *
 */
int	HFI_IN, HFI_W;

struct red_type	*red_track_pbound(w, pstart, pstop, veq)
     int	w, pstart, pstop, veq;
{
  struct red_type	*d, *sum;
  int			ci;

  d = RT[w];
  if (d->var_index == HF_PSTART_VI) {
    for (ci = 0; ci < d->u.ddd.child_count && pstart > d->u.ddd.arc[ci].upper_bound; ci++) ;

    if (ci >= d->u.ddd.child_count || pstart < d->u.ddd.arc[ci].lower_bound)
      return(NORM_FALSE);
    else
      d = d->u.ddd.arc[ci].child;
  }

  if (d->var_index == HF_PSTOP_VI) {
    for (ci = 0; ci < d->u.ddd.child_count && pstop > d->u.ddd.arc[ci].upper_bound; ci++) ;

    if (ci >= d->u.ddd.child_count || pstop < d->u.ddd.arc[ci].lower_bound)
      return(NORM_FALSE);
    else
      d = d->u.ddd.arc[ci].child;
  }

  if (d->var_index == VI_OP) {
    if (veq == DONT_CARE) {
      sum = NORM_FALSE;
      for (ci = 0; ci < d->u.ddd.child_count; ci++)
	sum = red_bop(OR, sum, d->u.ddd.arc[ci].child);
      return(sum);
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count && veq > d->u.ddd.arc[ci].upper_bound; ci++) ;

      if (ci >= d->u.ddd.child_count || veq < d->u.ddd.arc[ci].lower_bound)
	return(NORM_FALSE);
      else
	return(d->u.ddd.arc[ci].child);
    }
  }
  else if (d == NORM_FALSE || d== NORM_TRUE)
    return(d);
  else {
    fprintf(RED_OUT, "\nHow comes ? \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    for (; 1; ); 
    exit(0); 
  }
}
/* red_track_pbound() */ 






struct red_type	*red_track_pveq(w, pstart, pstop)
     int	w, pstart, pstop; 
{
  struct red_type	*d, *sum; 
  int			ci; 

  d = RT[w]; 
  if (d->var_index == HF_PSTART_VI) {
    for (ci = 0; ci < d->u.ddd.child_count && pstart > d->u.ddd.arc[ci].upper_bound; ci++) ; 

    if (ci >= d->u.ddd.child_count || pstart < d->u.ddd.arc[ci].lower_bound) 
      return(NORM_FALSE);
    else 
      d = d->u.ddd.arc[ci].child; 
  }

  if (d->var_index == HF_PSTOP_VI) {
    for (ci = 0; ci < d->u.ddd.child_count && pstop > d->u.ddd.arc[ci].upper_bound; ci++) ; 

    if (ci >= d->u.ddd.child_count || pstop < d->u.ddd.arc[ci].lower_bound)
      return(NORM_FALSE); 
    else 
      d = d->u.ddd.arc[ci].child; 
  }

  return(d); 
}
/* red_track_pveq() */ 










int	TS_PATH_ELIMINATE; 

struct red_type	*rec_path_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				vi, lb, ub, ci;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index > VI_VALUE)
    return(d);
  else if (d->var_index == TYPE_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_PATH_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      conj = crd_atom(d->var_index, bc->upper_bound);
      conj = red_bop(AND, conj, rec_path_eliminate(bc->child));
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = fdd_atom(d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      conj = red_bop(AND, conj, rec_path_eliminate(d->u.fdd.arc[ci].child));
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = dfdd_atom(d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      conj = red_bop(AND, conj, rec_path_eliminate(d->u.dfdd.arc[ci].child));
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (   d->var_index == HF_PSTART_VI || d->var_index == HF_PSTOP_VI
	   || d->var_index == VI_OP || d->var_index == VI_VALUE
	   ) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++)
	result = red_bop(OR, result, rec_path_eliminate(d->u.ddd.arc[ci].child));
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	ic = &(d->u.ddd.arc[ci]);
	conj = ddd_atom(d->var_index, ic->lower_bound, ic->upper_bound);
	conj = red_bop(AND, conj, rec_path_eliminate(ic->child));
	result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_path_eliminate() */






struct red_type	*red_path_eliminate(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_path_eliminate(d);

  return(result);
}
/* red_path_eliminate() */







int	ZF_VI, ZF_VJ, ZF_B, ZF_LB, ZF_UB;



struct red_type	*rec_extract_interval(d)
  struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index == TYPE_TRUE || d->var_index > ZF_VI)
    if (ZF_UB == CLOCK_POS_INFINITY)
      return(d);
    else
      return(NORM_FALSE);

  ce = cache4_check_result_key(OP_EXTRACT_INTERVAL, d, 
    (struct hrd_exp_type *) ZF_VI, ZF_LB, ZF_UB 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    if (d->var_index == ZF_VI) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	if (ZF_LB <= bc->upper_bound && bc->upper_bound <= ZF_UB)
	  bchild_stack_push(bc->child, bc->upper_bound);
      }
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	new_child = rec_extract_interval(bc->child);
	bchild_stack_push(new_child, bc->upper_bound);
      }
    }
    return(ce->result 
      = crd_new(d->var_index)
    );

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_extract_interval(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }

    return(ce->result = fdd_new(d->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_extract_interval(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }

    return(ce->result = dfdd_new(d->var_index));
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      new_child = rec_extract_interval(ic->child);
      ichild_stack_push(new_child, ic->lower_bound, ic->upper_bound);
    }

    return(
      ce->result 
        = ddd_new(d->var_index)
    );
  }
}
/* rec_extract_interval() */





struct red_type	*zone_extract_interval(d, ineq_vi, lb, ub)
     struct red_type	*d;
     int		ineq_vi, lb, ub;
{
  struct red_type	*result;

  if (VAR[ineq_vi].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError: a non-clock_inequality in zone_extract_interval()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0); 
    exit(0);
  }
  ZF_VI = ineq_vi;
  ZF_LB = lb;
  ZF_UB = ub;

  result = rec_extract_interval(d);

  return(result);
}
/* zone_extract_interval() */




int 	TS_SUBTRACT_INTERVAL; 

struct red_type	*rec_subtract_interval(d)
  struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index == TYPE_TRUE || d->var_index > ZF_VI)
    if (ZF_UB == CLOCK_POS_INFINITY)
      return(NORM_FALSE);
    else
      return(d);

  ce = cache4_check_result_key(OP_SUBTRACT_INTERVAL, d, 
    (struct hrd_exp_type *) ZF_VI, 
    ZF_LB,  
    ZF_UB
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->var_index == ZF_VI) {
      child_stack_level_push();
      new_child = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	if (ZF_LB > bc->upper_bound || bc->upper_bound > ZF_UB)
	  bchild_stack_push(bc->child, bc->upper_bound);
      }
      return(
        ce->result
          = crd_new(d->var_index)
      );
    }
    else {
      child_stack_level_push();
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	new_child = rec_subtract_interval(bc->child);
	bchild_stack_push(new_child, bc->upper_bound);
      }
      return(ce->result
        = crd_new(d->var_index)
      );
    }
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subtract_interval(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }

    return(ce->result
      = fdd_new(d->var_index)
    );
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_subtract_interval(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }

    return(ce->result
      = dfdd_new(d->var_index)
    );
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      new_child = rec_subtract_interval(ic->child);
      ichild_stack_push(new_child, ic->lower_bound, ic->upper_bound);
    }

    return(ce->result
      = ddd_new(d->var_index)
    );
  }
}
/* rec_subtract_interval() */





struct red_type	*zone_subtract_interval(d, ineq_vi, lb, ub)
     struct red_type	*d;
     int		ineq_vi, lb, ub;
{
  struct red_type	*result; 
  
  if (VAR[ineq_vi].TYPE != TYPE_CRD) { 
    fprintf(RED_OUT, "\nError: a non-clock_inequality in zone_subtract_interval()\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    bk(0); 
    exit(0); 
  } 
  ZF_VI = ineq_vi; 
  ZF_LB = lb; 
  ZF_UB = ub; 

  result = rec_subtract_interval(d); 
  
  return(result); 
}
/* zone_subtract_interval() */






/*******************************************************************************************
 *
 * Routines for the evaluation of forward time progress when path condition 
 * is time-convex.  
 */


struct red_type	*rec_clock_upper_extend(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  struct ddd_child_type		*ic;
  int				ci, c1, c2;
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

  ce = cache1_check_result_key(OP_CLOCK_UPPER_EXTEND, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (   (   c1 > 0 
            && c1 != DELTA && c1 != DELTAP 
            && c1 != NEG_DELTA && c1 != NEG_DELTAP
            )
        && (   c2 == 0 
            || c2 == DELTA || c2 == DELTAP 
            || c2 == NEG_DELTA || c2 == NEG_DELTAP
        )   ) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = rec_clock_upper_extend(d->u.crd.arc[ci].child);
	result = red_bop(OR, result, conj);
    } }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_one_constraint(
	  rec_clock_upper_extend(d->u.crd.arc[ci].child), 
	  d->var_index, d->u.crd.arc[ci].upper_bound
	);
	result = red_bop(OR, result, conj);
    } }
    break;
  case TYPE_HRD:
    fprintf(RED_OUT, "\nError: this should have been taken care of with hybrid_time_progress_fwd().\n");
    for (; 1; );
    exit(0);
    break;
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_clock_upper_extend(d->u.lazy.false_child), 
      rec_clock_upper_extend(d->u.lazy.true_child), 
      d, 
      PROJECT_CLOCK_UPPER_EXTEND, 
      FLAG_XVI_CLOCK_UPPER_EXTEND
    ); 
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_clock_upper_extend(d->u.fdd.arc[ci].child), 
	d->var_index, 
	d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_clock_upper_extend(d->u.dfdd.arc[ci].child), 
	d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_one_constraint(
        rec_clock_upper_extend(d->u.ddd.arc[ci].child), 
	d->var_index, 
	d->u.ddd.arc[ci].lower_bound, 
	d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_clock_upper_extend() */



struct red_type	*red_clock_upper_extend(
  struct red_type	*d
) {
  struct red_type	*result;

  result = rec_clock_upper_extend(d);

  return(result); 
}
/* red_clock_upper_extend() */ 




/*******************************************************************************************
 *
 * Routines for the evaluation of forward time progress when path condition 
 * is time-convex.  
 */



struct red_type	*rec_clock_upper_deltap(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  struct ddd_child_type		*ic;
  int				ci, c1, c2;
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

  ce = cache1_check_result_key(OP_CLOCK_UPPER_DELTAP, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (   c1 == DELTA || c1 == DELTAP || c1 == NEG_DELTA || c1 == NEG_DELTAP
        || c2 == DELTA || c2 == DELTAP || c2 == NEG_DELTA || c2 == NEG_DELTAP
        ) { 
      fprintf(RED_OUT, 
        "\nError: unexpected delta clocks %s in red_clock_upper_deltap().\n", 
        VAR[d->var_index].NAME 
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else if (c1 > 0 && c2 == 0) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_one_constraint( 
	  rec_clock_upper_deltap(d->u.crd.arc[ci].child), 
	  ZONE[c1][DELTAP], d->u.crd.arc[ci].upper_bound 
	);
	result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_one_constraint
		(rec_clock_upper_deltap(d->u.crd.arc[ci].child), 
		 d->var_index, d->u.crd.arc[ci].upper_bound
		 );
	result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_HRD:
    fprintf(RED_OUT, "\nError: this should have been taken care of with hybrid_time_progress_fwd().\n");
    for (; 1; );
    exit(0);
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_clock_upper_deltap(d->u.fdd.arc[ci].child), 
	d->var_index, d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_clock_upper_deltap(d->u.dfdd.arc[ci].child), 
	d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_one_constraint(
        rec_clock_upper_deltap(d->u.ddd.arc[ci].child), 
	d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result);
}
/* rec_clock_upper_deltap() */



struct red_type	*red_clock_upper_deltap(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_clock_upper_deltap(d);

  return(result); 
}
/* red_clock_upper_deltap() */ 







/*******************************************************************************************
 *
 * Routines for the evaluation of backward time progress when path condition 
 * is time-convex.  
 */
struct red_type	*rec_clock_lower_extend(d) 
     struct red_type	*d; 
{
  struct red_type		*result, *conj; 
  struct ddd_child_type		*ic; 
  int				ci, c1, c2; 
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

  ce = cache1_check_result_key(OP_CLOCK_LOWER_EXTEND, d); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (   c1 == 0 
            || c1 == DELTA || c1 == DELTAP 
            || c1 == NEG_DELTA || c1 == NEG_DELTAP
        )
        && (   c2 > 0 
            && c2 != DELTA && c2 != DELTAP 
            && c2 != NEG_DELTA && c2 != NEG_DELTAP
        )   ) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = rec_clock_lower_extend(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, conj); 
      }
    } 
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_one_constraint(
	  rec_clock_lower_extend(d->u.crd.arc[ci].child), 
	  d->var_index, d->u.crd.arc[ci].upper_bound
	); 
	result = red_bop(OR, result, conj); 
      }
    } 
    break; 

  case TYPE_HRD:
    fprintf(RED_OUT, "\nError: This should have been taken care of\n"); 
    fprintf(RED_OUT, "       by hybrid_time_progress_bck().\n");
    for (; 1; );
    exit(0);
    break; 
  case TYPE_LAZY_EXP: 
    result = red_lazy_project( 
      rec_clock_lower_extend(d->u.lazy.false_child), 
      rec_clock_lower_extend(d->u.lazy.true_child), 
      d, 
      PROJECT_CLOCK_LOWER_EXTEND, 
      FLAG_XVI_CLOCK_LOWER_EXTEND
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_atom(d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_lower_extend(d->u.fdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_atom(d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_lower_extend(d->u.dfdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound); 
      conj = red_bop(AND, conj, rec_clock_lower_extend(d->u.ddd.arc[ci].child)); 
      result = red_bop(OR, result, conj); 
    }
  }
  return(ce->result = result); 
}
/* rec_clock_lower_extend() */ 



struct red_type	*red_clock_lower_extend(
  struct red_type	*d 
) {
  struct red_type	*result; 
  
  result = rec_clock_lower_extend(d); 

  return(result); 
}
/* red_clock_lower_extend() */ 







/*******************************************************************************************
 *
 * Routines for the evaluation of backward time progress when path condition 
 * is time-convex.  
 */


struct red_type	*rec_clock_lower_deltap(d) 
     struct red_type	*d; 
{
  struct red_type		*result, *conj; 
  struct ddd_child_type		*ic; 
  int				ci, c1, c2; 
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

  ce = cache1_check_result_key(OP_CLOCK_LOWER_DELTAP, d); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   c1 == DELTA || c1 == DELTAP || c1 == NEG_DELTA || c1 == NEG_DELTAP
        || c2 == DELTA || c2 == DELTAP || c2 == NEG_DELTA || c2 == NEG_DELTAP
        ) { 
      fprintf(RED_OUT, 
        "\nError: unexpected delta clocks %s in red_clock_lower_deltap().\n", 
        VAR[d->var_index].NAME 
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else if (c1 > 0 && c2 == 0) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_one_constraint(
	  rec_clock_lower_deltap(d->u.crd.arc[ci].child), 
	  ZONE[c1][NEG_DELTAP], d->u.crd.arc[ci].upper_bound
	); 
	result = red_bop(OR, result, conj); 
      } 
      result = red_bop(AND, result, crd_atom(d->var_index, 0)); 
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = rec_clock_lower_deltap(d->u.crd.arc[ci].child); 
	conj = crd_one_constraint(conj, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, conj); 
      }
    } 
    break; 

  case TYPE_HRD:
    fprintf(RED_OUT, "\nError: This should have been taken care of\n"); 
    fprintf(RED_OUT, "       by hybrid_time_progress_bck().\n");
    for (; 1; );
    exit(0);
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_atom(d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_lower_deltap(d->u.fdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_atom(d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_lower_deltap(d->u.dfdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound); 
      conj = red_bop(AND, conj, rec_clock_lower_deltap(d->u.ddd.arc[ci].child)); 
      result = red_bop(OR, result, conj); 
    }
  }
  return(ce->result = result); 
}
/* rec_clock_lower_deltap() */ 



struct red_type	*red_clock_lower_deltap(d) 
     struct red_type	*d; 
{
  struct red_type	*result; 
  
  result = rec_clock_lower_deltap(d); 

  return(result); 
}
/* red_clock_lower_deltap() */ 




struct red_type	*rec_clock_noxtive_lower_extend(d)
     struct red_type	*d; 
{
  struct red_type		*result, *conj; 
  struct ddd_child_type		*ic; 
  int				ci, c1, c2; 
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

  ce = cache1_check_result_key(OP_CLOCK_NOXTIVE_LOWER_EXTEND, d); 
  if (ce->result) {
    return(ce->result); 
  } 
  
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0 && c2 > 0) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = rec_clock_noxtive_lower_extend(d->u.crd.arc[ci].child); 
	result = red_bop(OR, result, conj); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	conj = crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound);
	conj = red_bop(AND, conj, rec_clock_noxtive_lower_extend(d->u.crd.arc[ci].child)); 
	result = red_bop(OR, result, conj); 
      }
    } 
    break; 

  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_atom(d->var_index, d->u.fdd.arc[ci].lower_bound, 
        d->u.fdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_noxtive_lower_extend(d->u.fdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_atom(d->var_index, d->u.dfdd.arc[ci].lower_bound, 
        d->u.dfdd.arc[ci].upper_bound
      ); 
      conj = red_bop(AND, conj, 
        rec_clock_noxtive_lower_extend(d->u.dfdd.arc[ci].child)
      ); 
      result = red_bop(OR, result, conj); 
    }
    break; 

  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound); 
      conj = red_bop(AND, conj, rec_clock_noxtive_lower_extend(d->u.ddd.arc[ci].child)); 
      result = red_bop(OR, result, conj); 
    }
  }
  return(ce->result = result); 
}
/* rec_clock_noxtive_lower_extend() */ 



struct red_type	*red_clock_noxtive_lower_extend(d) 
     struct red_type	*d; 
{
  struct red_type	*result; 

  result = rec_clock_noxtive_lower_extend(d);

  return(result); 
}
/* red_clock_noxtive_lower_extend() */ 


/*********************************************************************
 */

int		TX_V1, TX_V2, TX_VIJ, TX_LB, TX_UB, TX_LCI, TX_RCI; 
struct red_type	*TX_W, *TX_D1; 



struct red_type	*rec_eliminate_simple_negative_cycles(d) 
     struct red_type	*d; 
{
  int				b, ci;
  struct red_type		*child;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  ce = cache1_check_result_key(OP_ELIMINATE_SIMPLE_NEGATIVE_CYCLES, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    if (VAR[d->var_index].U.CRD.CLOCK1 < VAR[d->var_index].U.CRD.CLOCK2) {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	if (bc->upper_bound < CLOCK_POS_INFINITY) {
/*
	  fprintf(RED_OUT, "vi=%1d:%s, \n", 
	  	  d->var_index, VAR[d->var_index].NAME 
	  	  ); 
	  fflush(RED_OUT); 
	  fprintf(RED_OUT, "converse=%1d:\n", 
	  	  VAR[d->var_index].CONVERSE_CRD_INDEX
	  	  ); 
	  fflush(RED_OUT); 
	  fprintf(RED_OUT, "%s\n", 
	  	  VAR[VAR[d->var_index].CONVERSE_CRD_INDEX].NAME
	  	  ); 
	  fflush(RED_OUT); 
*/
	  child = zone_extract_interval(bc->child,
	    VAR[d->var_index].U.CRD.CONVERSE_CRD_VI,
	    -bc->upper_bound,
	    CLOCK_POS_INFINITY
	  );
	}
	else
	  child = bc->child;

	child = rec_eliminate_simple_negative_cycles(child);
	bchild_stack_push(child, bc->upper_bound);
      }
    }
    else {
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	bc = &(d->u.crd.arc[ci]);
	child = rec_eliminate_simple_negative_cycles(bc->child);
	bchild_stack_push(child, bc->upper_bound);
      }
    }
    return(ce->result 
      = crd_new(d->var_index)
    );

  case TYPE_LAZY_EXP: 
    ce->result = lazy_subtree(
      rec_eliminate_simple_negative_cycles(d->u.lazy.false_child), 
      rec_eliminate_simple_negative_cycles(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp 
    ); 
    return(ce->result); 
    break; 
    
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_eliminate_simple_negative_cycles(d->u.fdd.arc[ci].child);
      fchild_stack_push(child, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
    }

    return(ce->result = fdd_new(d->var_index));
    break; 
    
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_eliminate_simple_negative_cycles(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(child, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
    }

    return(ce->result = dfdd_new(d->var_index));
    break; 
    
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]);
      child = rec_eliminate_simple_negative_cycles(ic->child);
      ichild_stack_push(child, ic->lower_bound, ic->upper_bound);
    }

    return(ce->result
      = ddd_new(d->var_index)
    );

  }
}
  /* rec_eliminate_simple_negative_cycles() */





struct red_type	*red_eliminate_simple_negative_cycles(w) 
     int	w; 
{
  struct red_type	*result; 
  
  if (RT[w] == NORM_FALSE || RT[w] == NORM_NO_RESTRICTION) 
    return(RT[w]); 

  result = rec_eliminate_simple_negative_cycles(RT[w]); 
  
  return(RT[w] = result);   
}
/* red_eliminate_simple_negative_cycles() */ 









/*************************************************************************
 * BYPASS with iterative downward matching techniques 
 */
  
  
int	ZX, ZY, ZXY_BOUND; 

struct red_type	*rec_bypass_DOWNWARD_MATCHING_left(d) 
     struct red_type	*d;
{
  int				b, b1, b2, ci, cj, c1, c2, cmax, old_bound, old_c1_bound, old_c2_bound; 
  struct red_type		*result, *child, *new_record, *conj; 
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    return(d); 
  
  ce = cache4_check_result_key(OP_BYPASS_DOWNWARD_MATCHING_LEFT, 
    d, (struct hrd_exp_type *) ZX, ZY, ZXY_BOUND 
    ); 
  if (ce->result) {
    return(ce->result); 
  } 
  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (d->var_index < ZONE[ZX][ZY]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	child = rec_bypass_DOWNWARD_MATCHING_left(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
	result = red_bop(OR, result, child); 
      }
    }
    else if (d->var_index == ZONE[ZX][ZY]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	ZXY_BOUND = d->u.crd.arc[ci].upper_bound; 
	child = rec_bypass_DOWNWARD_MATCHING_left(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound));
	result = red_bop(OR, result, child); 
      }
      ZXY_BOUND = CLOCK_POS_INFINITY; 
    }
    else if (c1 == ZY) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	b = zone_ub_add(ZXY_BOUND, d->u.crd.arc[ci].upper_bound); 
	if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) 
	  child = rec_bypass_DOWNWARD_MATCHING_left(d->u.crd.arc[ci].child); 
	else if (b < 0 && (ZX == c2 || c2 == 0)) 
	  return(ce->result = result); 
	else {
	  child = crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound); 
	  if (b < CLOCK_POS_INFINITY) 
	    child = red_bop(AND, child, crd_atom(ZONE[ZX][c2], b)); 
	  child = red_bop(AND, child, rec_bypass_DOWNWARD_MATCHING_left(d->u.crd.arc[ci].child)); 
	}
	result = red_bop(OR, result, child); 
      }	
    }
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	child = rec_bypass_DOWNWARD_MATCHING_left(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
	result = red_bop(OR, result, child); 
      }
    }
    break; 
  case TYPE_FLOAT:  
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_left(d->u.fdd.arc[ci].child); 
      child = red_bop(AND, child,
	fdd_atom(d->var_index, d->u.fdd.arc[ci].lower_bound, 
	  d->u.fdd.arc[ci].upper_bound
	)
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE:  
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_left(d->u.dfdd.arc[ci].child); 
      child = red_bop(AND, child,
	dfdd_atom(d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	  d->u.dfdd.arc[ci].upper_bound
	)
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default:  
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_left(d->u.ddd.arc[ci].child); 
      child = red_bop(AND, child,
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, 
			       d->u.ddd.arc[ci].upper_bound
			       )
		      ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_bypass_DOWNWARD_MATCHING_left() */ 





struct red_type	*rec_bypass_DOWNWARD_MATCHING_right(d) 
     struct red_type	*d; 
{
  int				b, b1, b2, ci, cj, c1, c2, 
  				cmax, old_bound, old_c1_bound, old_c2_bound; 
  struct red_type		*result, *child, *new_record, *conj; 
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    return(d); 
  
  ce = cache4_check_result_key(OP_BYPASS_DOWNWARD_MATCHING_RIGHT, 
    d, (struct hrd_exp_type *) ZX, ZY, ZXY_BOUND
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (d->var_index < ZONE[ZX][ZY]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	child = rec_bypass_DOWNWARD_MATCHING_right(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
	result = red_bop(OR, result, child); 
      }
    }
    else if (d->var_index == ZONE[ZX][ZY]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	ZXY_BOUND = d->u.crd.arc[ci].upper_bound; 
	child = rec_bypass_DOWNWARD_MATCHING_right(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
	result = red_bop(OR, result, child); 
      }
      ZXY_BOUND = CLOCK_POS_INFINITY; 
    }
    else if (c2 == ZX) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
	b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZXY_BOUND); 
	if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) 
	  child = rec_bypass_DOWNWARD_MATCHING_right(d->u.crd.arc[ci].child); 
	else if (b < 0 && (c1 == ZY || ZY == 0)) 
	  return(ce->result = result); 
	else {
	  child = crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound); 
	  if (b < CLOCK_POS_INFINITY) 
	    child = red_bop(AND, child, crd_atom(ZONE[c1][ZY], b));
	  child = red_bop(AND, child, rec_bypass_DOWNWARD_MATCHING_right(d->u.crd.arc[ci].child)); 
	}
	result = red_bop(OR, result, child); 
      }	
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	child = rec_bypass_DOWNWARD_MATCHING_right(d->u.crd.arc[ci].child); 
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)); 
	result = red_bop(OR, result, child); 
      }
    }
    break; 
  case TYPE_FLOAT:  
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_right(d->u.fdd.arc[ci].child); 
      child = red_bop(AND, child, 
	fdd_atom(d->var_index, d->u.fdd.arc[ci].lower_bound, 
	  d->u.fdd.arc[ci].upper_bound
	)
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE:  
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_right(d->u.dfdd.arc[ci].child); 
      child = red_bop(AND, child, 
	dfdd_atom(d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	  d->u.dfdd.arc[ci].upper_bound
	)
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default:  
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_bypass_DOWNWARD_MATCHING_right(d->u.ddd.arc[ci].child); 
      child = red_bop(AND, child, 
	ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, 
	  d->u.ddd.arc[ci].upper_bound
	)
      ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_bypass_DOWNWARD_MATCHING_right() */ 





struct red_type	*red_bypass_DOWNWARD_MATCHING(w, clhs)
     int	w; 
{
  /* 
  fprintf(RED_OUT, "\nOn entering red_bypass_DOWNWARD_MATCHING with clhs=%1d at RT[w]:\n", clhs); 
  red_print_graph(RT[w]); 
  */ 
  ZXY_BOUND = CLOCK_POS_INFINITY; 
  ZX = clhs; 
  for (ZY = 0; ZY < CLOCK_COUNT; ZY++) 
    if (clhs != ZY) { 
      /* 
      fprintf(RED_OUT, "\n\n----------------------------------------------------\n"); 
      fprintf(RED_OUT, "Before bypass DOWNWARD_MATCHING right with (?)->(ZX=%1d)->(ZY=%1d);\n", ZX, ZY); 
      probe(PROBE_RISK, "*->zx->zy BEFORE", RT[w]); 
      red_print_graph(RT[w]); 
      */ 
      RT[w] = rec_bypass_DOWNWARD_MATCHING_right(RT[w]); 
          garbage_collect(FLAG_GC_SILENT); 
      /* 
      fprintf(RED_OUT, "\nAfter bypass DOWNWARD_MATCHING right with (?)->(ZX=%1d)->(ZY=%1d);\n", ZX, ZY); 
      probe(PROBE_RISK, "*->zx->zy AFTER", RT[w]); 
      red_print_graph(RT[w]); 
      */ 
    }
  ZY = clhs; 
  for (ZX = 0; ZX < CLOCK_COUNT; ZX++) 
    if (ZX != clhs) { 
      /* 
      fprintf(RED_OUT, "\n\n----------------------------------------------------\n");
      fprintf(RED_OUT, "Before bypass DOWNWARD_MATCHING left with (ZX=%1d)->(ZY=%1d)->(?);\n", ZX, ZY); 
      probe(PROBE_RISK, "zx->zy->* BEFORE", RT[w]); 
      red_print_graph(RT[w]); 
      */ 
      RT[w] = rec_bypass_DOWNWARD_MATCHING_left(RT[w]); 
          garbage_collect(FLAG_GC_SILENT); 
      /* 
      fprintf(RED_OUT, "\nAfter bypass DOWNWARD_MATCHING left with (ZX=%1d)->(ZY=%1d)->(?);\n", ZX, ZY); 
      probe(PROBE_RISK, "zx->zy->* AFTER", RT[w]); 
      red_print_graph(RT[w]); 
      */ 
    }
  /* 
  fprintf(RED_OUT, "\nOn leaving new red_bypass with clhs=%1d at RT[w]:\n", clhs); 
  red_print_graph(RT[w]); 
  */ 
  return(RT[w]); 
}
/* red_bypass_DOWNWARD_MATCHING() */ 






/******************************************************************
 * magnitude maintenance with downward split techniques 
 */
#define RBSTOP	-1 // 155  
int	count_tapairs = 0; 
int	count_rbdownward = 0; 

extern struct cache2_hash_entry_type	*hashtar; 

#define tashbound 470002

void thash_byd() { 
  if (count_tapairs > -1 /*< tashbound*/) 
    return; 
  fprintf(RED_OUT, "count_tapairs=%1d, op=%1d, d1=%x, d2=%x, result=%x\n", 
    count_tapairs, hashtar->op, (unsigned int) hashtar->d1, (unsigned int) hashtar->d2, (unsigned int) hashtar->result
  ); 
  fflush(RED_OUT); 
} 
  /* thash_byd() */ 




int	ZL_DOWNWARD, ZM_DOWNWARD, ZR_DOWNWARD, ZB_DOWNWARD;
// int	count_bypass_DW = 0; 
/*
int	count_sh_bypass_downward, 
	count_sh_bypass_left_downward, 
	count_sh_bypass_right_downward; 
int	count_bpD = 0; 
*/


// int	count_bpcl = 0; 

struct red_type	*rec_bypass_given_left_DOWNWARD(d) 
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (   d == NORM_FALSE
      || d == NORM_NO_RESTRICTION 
      || d->var_index > ZONE[ZM_DOWNWARD][CLOCK_COUNT-1]
      )
    return(d);
/*
    fprintf(RED_OUT, "\nrec bypass gL dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == 2090) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT); 
*/
  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass given left downward.\n", 
      count_tapairs
    ); 
  #endif 
  
//  print_cpu_time(">>bypass check L %1d", ++count_bpcl); 
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_BYPASS_GIVEN_LEFT_DOWNWARD, d, 
    (struct hrd_exp_type *) ZL_DOWNWARD, ZM_DOWNWARD, ZB_DOWNWARD
  ); 
//  print_cpu_time("<<bypass check L %1d", count_bpcl); 
  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
/*
    count_sh_bypass_left_downward++;  
    if (count_bpD == 5) { 
      fprintf(RED_OUT, "%1d:L%1d:ZL=%1d:%1d:%s,ZM=%1d:%1d:%s,ZB=%1d\n", 
        count_bpD, count_sh_bypass_left_downward, 
        ZL_DOWNWARD, CLOCK[ZL_DOWNWARD], VAR[CLOCK[ZL_DOWNWARD]].NAME, 
        ZM_DOWNWARD, CLOCK[ZM_DOWNWARD], VAR[CLOCK[ZM_DOWNWARD]].NAME, 
        ZB_DOWNWARD
      ); 
    } 
*/
    return(ce->result); 
  } 
#endif 
/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "left, count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  }
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
		    rec_bypass_given_left_DOWNWARD(d->u.bdd.zero_child), 
		    rec_bypass_given_left_DOWNWARD(d->u.bdd.one_child)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 != ZM_DOWNWARD) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    else if (c2 == ZL_DOWNWARD) {
      // This is a cycle of two difference constraints.  
      // So we need to check if there is any inconsistency.  
      if (ZL_DOWNWARD == TIME) {
        for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD
	  );
	  if (b < 0) {
	    break;
	  }
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        } 
      }
      else { 
        for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        } 
      } 
    }
    else switch (ZL_DOWNWARD) {
    case 0: 
      switch (c2) { 
      case TIME: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound
	  );
	  // This gives us a consraint like -c2<=b or -c2<b.  
	  if (b > 0) { 
	  // This gives us a constraint like -c2<=|b| or -c2<|b|.  
          // This gives us a constraint like -c2<=|b| or -c2<|b|.  
	    b = 0;
	  }
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(
	      child, d->var_index, d->u.crd.arc[ci].upper_bound
	    ),
	    ZONE[ZL_DOWNWARD][c2], b
	  ); 
	  result = red_bop(OR, result, child);
	}
        break; 
      
      case NEG_DELTA: 
      case NEG_DELTAP: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  // This gives us a consraint like -c2<=b or -c2<b.  
	  if (b < 0) { 
	  // This gives us a constraint like -c2<=-|b| or -c2<-|b|.  
	    // This gives us a constraint like delta<=-|b| or delta'<-|b|.  
	    break;  
	  }
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(
	      child, d->var_index, d->u.crd.arc[ci].upper_bound
	    ),
	    ZONE[ZL_DOWNWARD][c2], b
	  ); 
	  result = red_bop(OR, result, child);
	}
	break; 
	
      default: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  // This gives us a consraint like -c2<=b or -c2<b.  
	  if (b > 0) { 
	  // This gives us a constraint like -c2<=|b| or -c2<|b|.  
          // This gives us a constraint like -c2<=|b| or -c2<|b|.  
	    b = 0;
	  }
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(
	      child, d->var_index, d->u.crd.arc[ci].upper_bound
	    ),
	    ZONE[ZL_DOWNWARD][c2], b
	  ); 
	  result = red_bop(OR, result, child);
	}
      }
      break; 
      
    case TIME: // Since ZL_DOWNWARD != c2, we know that c2 != TIME. 
      for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	b = zone_ub_add_unbounded(
	  ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound
	);
	if (c2 == 0) { 
	// This gives us a consraint like ZL<=b or ZL<b.  
	  if (b < 0) {
	  // This gives us a constriant like ZL<=-|b| or ZL<-|b|. 
          // This gives us a constriant like ZL<=-|b| or ZL<-|b|. 
	    break;
	  } 
	} 
	child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(
	  crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  ),
	  ZONE[ZL_DOWNWARD][c2], b
	); 
	result = red_bop(OR, result, child);
      }
      break; 
      
    default: 
      switch (c2) { 
      case TIME: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(
	      child, d->var_index, d->u.crd.arc[ci].upper_bound
	    ),
	    ZONE[ZL_DOWNWARD][c2], b
	  ); 
	  result = red_bop(OR, result, child);
	}
        break; 
      case 0: 
        switch (ZL_DOWNWARD) { 
        case NEG_DELTA: 
        case NEG_DELTAP: 
          for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	    b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	    // This gives us a consraint like ZL<=b or ZL<b.  
	    if (b > 0) { 
	    // This gives us a constriant like ZL<=|b| or ZL<|b|. 
	      // This gives us a constriant like -delta<=|b| or -delta'<|b|.
	      b = 0;  
	    }  
	    child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	    child = crd_one_constraint(
	      crd_one_constraint(
	        child, d->var_index, d->u.crd.arc[ci].upper_bound
	      ),
	      ZONE[ZL_DOWNWARD][c2], b
	    ); 
	    result = red_bop(OR, result, child);
	  }
	  break; 
	default: 
          for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	    b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	    // This gives us a consraint like ZL<=b or ZL<b.  
	    if (b < 0) {
	    // This gives us a constriant like ZL<=-|b| or ZL<-|b|. 
	      break;
	    } 
	    child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	    child = crd_one_constraint(
	      crd_one_constraint(
	        child, d->var_index, d->u.crd.arc[ci].upper_bound
	      ),
	      ZONE[ZL_DOWNWARD][c2], b
	    ); 
	    result = red_bop(OR, result, child);
	  }
	}
        break; 
      default: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  child = rec_bypass_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(
	      child, d->var_index, d->u.crd.arc[ci].upper_bound
	    ),
	    ZONE[ZL_DOWNWARD][c2], b
	  ); 
	  result = red_bop(OR, result, child);
	}
	break; 
      }
      break; 
    }
    break;

  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_bypass_given_left_DOWNWARD(d->u.lazy.false_child), 
      rec_bypass_given_left_DOWNWARD(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_bypass_given_left_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index,
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_bypass_given_left_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index,
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_bypass_given_left_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
      	      (child, d->var_index,
	       d->u.ddd.arc[ci].lower_bound,
	       d->u.ddd.arc[ci].upper_bound
	       );
      result = red_bop(OR, result, child);
    }
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_given_left_DOWNWARD(%s-%s%s) for input:\n", 
      VAR[CLOCK[ZL_DOWNWARD]].NAME, 
      VAR[CLOCK[ZM_DOWNWARD]].NAME, 
      string_zone_ub(ZB_DOWNWARD) 
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_given_left_DOWNWARD(%s-%s%s) for result:\n", 
      VAR[CLOCK[ZL_DOWNWARD]].NAME, 
      VAR[CLOCK[ZM_DOWNWARD]].NAME, 
      string_zone_ub(ZB_DOWNWARD) 
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_bypass_given_left_DOWNWARD() */





int	count_bpcr = 0; 


struct red_type	*rec_bypass_given_right_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (   d == NORM_FALSE
      || d == NORM_NO_RESTRICTION 
      || d->var_index > ZONE[CLOCK_COUNT-1][ZM_DOWNWARD]
      )
    return(d);
/*
    fprintf(RED_OUT, "\nrec bypass gR dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT); 
*/
  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass given right downward.\n", 
      count_tapairs
    ); 
  #endif 
  
//  print_cpu_time(">>bypass check R %1d", ++count_bpcr); 
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_BYPASS_GIVEN_RIGHT_DOWNWARD, d, 
    (struct hrd_exp_type *) ZM_DOWNWARD, ZR_DOWNWARD, ZB_DOWNWARD
  ); 
//  print_cpu_time("<<bypass check R %1d", count_bpcr); 
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
/*
    count_sh_bypass_right_downward++;  
    if (count_bpD == 5) { 
      fprintf(RED_OUT, "%1d:R%1d:ZM=%1d:%1d:%s,ZR=%1d:%1d:%s,ZB=%1d\n", 
        count_bpD, count_sh_bypass_right_downward, 
        ZM_DOWNWARD, CLOCK[ZM_DOWNWARD], VAR[CLOCK[ZM_DOWNWARD]].NAME, 
        ZR_DOWNWARD, CLOCK[ZR_DOWNWARD], VAR[CLOCK[ZR_DOWNWARD]].NAME, 
        ZB_DOWNWARD
      ); 
    } 
*/
    return(ce->result); 
  } 
#endif 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "right, count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
		    rec_bypass_given_right_DOWNWARD(d->u.bdd.zero_child), 
		    rec_bypass_given_right_DOWNWARD(d->u.bdd.one_child)
		    )
	    ); 
    break; 
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c2 != ZM_DOWNWARD) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    else if (c1 == ZR_DOWNWARD) {
      // This is a cycle of two difference constraints.  
      // So we need to check if there is any inconsistency.  
      if (ZR_DOWNWARD == TIME) 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD
	  ); 
	  if (b < 0) {
	    break;
	  }
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      else 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
    }
    else switch (ZR_DOWNWARD) { 
    case 0: 
/*This is a bug that was found on 2008/5/11. 
 *****************************************
In rec_BYPASS_given_right_DOWNWARD(x[1]-0<10) for input:
 (0)V=332:(-delta-x[1]);(8aa02e8)40;IC=1;<=0:8aa0288;
   (1)V=334:(x[1]--delta);(8aa0288)40;IC=1;<10:8a8d678;
     (2)V=342:(x[1]-MODAL_CLOCK);(8a8d678)40;IC=1;<10:TRUE;
In rec_BYPASS_given_right_DOWNWARD(x[1]-0<10) for result:
 (0), FALSE
*/
      switch (c1) { 
      case TIME: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD
	  );
	  // a new constraint like c1<b or c1<=b 
          if (b < 0) { 
	    // This gives us a constraint like c1<-|b| or c1<=-|b| 
	    break;
	  } 

	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	    ZONE[c1][ZR_DOWNWARD], b
	  );
	  result = red_bop(OR, result, child);
	}
        break; 
      case NEG_DELTA: 
      case NEG_DELTAP: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  // a new constraint like c1<b or c1<=b 
          if (b >= 0) { 
	    // This gives us a constraint like -delta<|b| or -delta'<=|b|.  
	    b = 0; 
	  } 

	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  else
	    child = crd_one_constraint(
	      crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	      ZONE[c1][ZR_DOWNWARD], b
	    );
	  result = red_bop(OR, result, child);
	}
	break; 
      default: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  // a new constraint like c1<b or c1<=b 
          if (b < 0) { 
            break;
	  } 

	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  else
	    child = crd_one_constraint(
	      crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	      ZONE[c1][ZR_DOWNWARD], b
	    );
	  result = red_bop(OR, result, child);
	}
	break; 
      }
      break; 
    case TIME: // Since c1 != ZR_DOWNWARD, we know that c1 != TIME
      switch (c1) { 
      case 0: 
        for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD
	  );
	  if (b > 0) {
	    // This gives us a constraint like -ZR<|b| or -ZR<=|b|
	    b = 0; 
	  }
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	    ZONE[c1][ZR_DOWNWARD], b
	  );
	  result = red_bop(OR, result, child);
        }
        break; 
      default: 
        for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(
	    d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD
	  );
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(
	    crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	    ZONE[c1][ZR_DOWNWARD], b
	  );
	  result = red_bop(OR, result, child);
        }
        break; 
      } 
      break; 
    default: /* ZR_DOWNWARD != 0 && ZR_DOWNWARD != TIME */ 
      switch (c1) { 
      case 0:  
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b > 0) {
	    // This gives us a constraint like -ZR<|b| or -ZR<=|b|
	    b = 0; 
	  }
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  else
	    child = crd_one_constraint(
	      crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	      ZONE[c1][ZR_DOWNWARD], b
	    );
	  result = red_bop(OR, result, child);
	}
        break; 
      case TIME: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add_unbounded(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
          child = crd_one_constraint(
	    crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	    ZONE[c1][ZR_DOWNWARD], b
	  );
	  result = red_bop(OR, result, child);
	}
        break; 
      default: 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  child = rec_bypass_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  else
	    child = crd_one_constraint(
	      crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound),
	      ZONE[c1][ZR_DOWNWARD], b
	    );
	  result = red_bop(OR, result, child);
	}
	break; 
      }
      break; 
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_bypass_given_right_DOWNWARD(d->u.lazy.false_child), 
      rec_bypass_given_right_DOWNWARD(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
    
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_bypass_given_right_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_bypass_given_right_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
    
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_bypass_given_right_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
      		(child, d->var_index, d->u.ddd.arc[ci].lower_bound,
		 d->u.ddd.arc[ci].upper_bound
		 );
      result = red_bop(OR, result, child);
    }
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_given_right_DOWNWARD(%s-%s%s) for input:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME, 
      VAR[CLOCK[ZR_DOWNWARD]].NAME, 
      string_zone_ub(ZB_DOWNWARD) 
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_given_right_DOWNWARD(%s-%s%s) for result:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME, 
      VAR[CLOCK[ZR_DOWNWARD]].NAME, 
      string_zone_ub(ZB_DOWNWARD) 
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_bypass_given_right_DOWNWARD() */



// int	count_bpc = 0; 

struct red_type	*rec_bypass_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2, old_bound, old_c1_bound, old_c2_bound;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

/*
  fprintf(RED_OUT, "\nbpc %1d\n", ++count_bpc); 
  fflush(RED_OUT); 
*/
  
  if (   d == NORM_FALSE 
      || d == NORM_NO_RESTRICTION
      || (d->var_index > ZONE[ZM_DOWNWARD][CLOCK_COUNT-1])
      )
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 
  
  ce = cache2_check_result_key(OP_BYPASS_DOWNWARD, d, 
    (struct red_type *) ZM_DOWNWARD
  ); 
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
		    rec_bypass_DOWNWARD(d->u.bdd.zero_child), 
		    rec_bypass_DOWNWARD(d->u.bdd.one_child)
		    )
	    ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT); 
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == ZM_DOWNWARD) {
      if (c2 == ZM_DOWNWARD) {
	fprintf(RED_OUT, "\nError: how come this happen ? \n");
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	exit(0);
      }
      else {
	for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	  child = rec_bypass_DOWNWARD(d->u.crd.arc[ci].child);
	  if (   d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY
	      || VAR[d->var_index].U.CRD.CLOCK1 == TIME
	      ) {
	    ZR_DOWNWARD = c2;
	    ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	    red_init_result(child); 
#endif 
	    grown_child = rec_bypass_given_right_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	    red_clear_result(child); 
#endif 
	    child = grown_child;
	  }
/*
	  if (count_bpD == 5) 
	    print_cpu_time("before crd"); 
*/
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
/*
	  if (count_bpD == 5) 
	    print_cpu_time("before or"); 
*/
	  result = red_bop(OR, result, child); 
/*
	  if (count_bpD == 5) 
	    print_cpu_time("after or"); 
*/
	}
	ZB_DOWNWARD = CLOCK_POS_INFINITY;
      }
    }
    else {
      if (c2 == ZM_DOWNWARD) {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_bypass_DOWNWARD(d->u.crd.arc[ci].child);
	  if (   d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY
	      || VAR[d->var_index].U.CRD.CLOCK1 == TIME
	      ) {
	    ZL_DOWNWARD = c1;
	    ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	    red_init_result(child); 
#endif 
	    grown_child = rec_bypass_given_left_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	    red_clear_result(child); 
#endif 
	    child = grown_child;
	  }
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
	ZB_DOWNWARD = CLOCK_POS_INFINITY;
      }
      else {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_bypass_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_bypass_DOWNWARD(d->u.lazy.false_child), 
      rec_bypass_DOWNWARD(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
      	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_bypass_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
      	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_bypass_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
      		(child, d->var_index, 
      		 d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
		 ); 
      result = red_bop(OR, result, child); 
    } 
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for input:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for result:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
  return(ce->result = result); 
}
  /* rec_BYPASS_DOWNWARD() */







struct red_type	*red_bypass_DOWNWARD(w, ci)
     int	w, ci;
{
  struct red_type	*result;
  
  if (RT[w] == NORM_FALSE || RT[w] == NORM_NO_RESTRICTION) 
    return(RT[w]); 
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */
/*
  print_cpu_time("\nIT%1d, SXI%1d>> bpD %1d: %1d:%1d:%s", 
    ITERATION_COUNT, ITERATE_SXI, ++count_bpD, 
    ci, CLOCK[ci], VAR[CLOCK[ci]].NAME
  ); 
  if (count_bpD == 5) { 
    red_print_graph(RT[w]); 	
  } 
*/

/*
  if (   (GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_BRANCHING_BISIM_CHECKING 
      || (GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_BRANCHING_SIM_CHECKING
      ) { 
    fprintf(RED_OUT, "Be careful, we need to change this procedure\n"); 
    fprintf(RED_OUT, "before we can use it for simulation checking.\n"); 
    fflush(RED_OUT); 
    exit(0); 
  } 
*/
//081225 CHANGE
  if (ci == TIME) { 
//    fprintf(RED_OUT, "\nWARNING: Attempt to bypass clock TIME skipped.\n"); 
//    fflush(RED_OUT); 
    return(RT[w]); 
//     bk(0); 	
  } 
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[w] = hybrid_bypass_DOWNWARD(w, CLOCK[ci]); 
  }
  else { 
    ZM_DOWNWARD = ci;

    result = rec_bypass_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
  } 
/*
  if (   count_subtract_iterative == 7 
      && ZM_DOWNWARD == 16 
      ) { 
    fprintf(RED_OUT, "\n=== count_subtract_iterative:7, ZM_DOWNWARD:16, red_bypass_DOWNWARD() with output ===\n");
    red_print_graph(RT[w]); 
  }  
*/
/*
  print_cpu_time("\nIT%1d, SXI%1d<< bpD %1d, sh%1d, shL%1d, shR%1d\n", 
    ITERATION_COUNT, ITERATE_SXI, count_bpD, 
    count_sh_bypass_downward, 
    count_sh_bypass_left_downward, 
    count_sh_bypass_right_downward   
  ); 
  if (count_bpD == 5) { 
    red_print_graph(RT[w]); 	
  } 
*/
  return(RT[w]);
}
/* red_bypass_DOWNWARD() */ 





/********************************************************************************
*   procedures for efficient closure form calculation.
*/



struct red_type	*rec_tight_magnitudes_from_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[ZM_DOWNWARD][CLOCK_COUNT-1]) 
    return(d); 
  
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_TIGHT_MAGNITUDES_FROM_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:  
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == ZM_DOWNWARD) { 
      if (!c2) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) { 
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD); 
	  if (b < 0) {
	    break;  
	  } 
	  child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child); 
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	  result = red_bop(OR, result, child); 
	}
      }
      else if (c2 == NEG_DELTA || c2 == NEG_DELTAP) { 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) { 
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound); 
	  child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child); 
	  child = crd_one_constraint
	  	  (crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound), 
		   ZONE[0][c2], b
		   ); 
	  result = red_bop(OR, result, child); 
	}
      } 
      else { 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) { 
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound); 
	  if (b > 0) {
	    b = 0; 
	  } 
	  child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child); 
	  child = crd_one_constraint
	  	  (crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound), 
		   ZONE[0][c2], b
		   ); 
	  result = red_bop(OR, result, child); 
	}
      } 
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
	child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child);
    }
    break;
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_magnitudes_from_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(child, d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
		      ); 
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_tight_magnitudes_from_zero_DOWNWARD() */





struct red_type	*rec_tight_magnitudes_to_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[CLOCK_COUNT-1][ZM_DOWNWARD]) 
    return(d);

#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_TIGHT_MAGNITUDES_TO_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c2 == ZM_DOWNWARD) {
      if (!c1) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
      else if (c2 == NEG_DELTA || c2 == NEG_DELTAP) { 
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) { 
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	  else
	    child = crd_one_constraint
	    	    (crd_one_constraint(child,	d->var_index, d->u.crd.arc[ci].upper_bound),
		     ZONE[c1][0], b
		     );
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) { 
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	  else
	    child = crd_one_constraint
	    	    (crd_one_constraint(child,	d->var_index, d->u.crd.arc[ci].upper_bound),
		     ZONE[c1][0], b
		     );
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break; 
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.fdd.arc[ci].child);
      child = red_bop(AND, child,
	fdd_atom(d->var_index, d->u.fdd.arc[ci].lower_bound, 
	  d->u.fdd.arc[ci].upper_bound
	)
      );
      result = red_bop(OR, result, child);
    }
    break; 
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = red_bop(AND, child,
	dfdd_atom(d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	  d->u.dfdd.arc[ci].upper_bound
	)
      );
      result = red_bop(OR, result, child);
    }
    break; 
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_magnitudes_to_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = red_bop(AND, child,
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, 
			       d->u.ddd.arc[ci].upper_bound
			       )
		      );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_tight_magnitudes_to_zero_DOWNWARD() */




// int	count_tight_magnitudes_DOWNWARD_through_magnitudes = 0; 

struct red_type	*rec_tight_magnitudes_DOWNWARD_through_magnitudes(d)
     struct red_type	*d;
{
  int				ci, c1, c2;
  struct red_type		*result, *child, *grown_child;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE
      || d->var_index > ZONE[CLOCK_COUNT-1][0]
      )
    return(d);

  ce = cache1_check_result_key(
    OP_TIGHT_MAGNITUDES_DOWNWARD_THROUGH_MAGNITUDES, d
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (!c1) {
      if (!c2) {
	fprintf(RED_OUT, "\nError: how come this happen ? \n");
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	exit(0);
      }
      else {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);

	  ZM_DOWNWARD = c2;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_tight_magnitudes_from_zero_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  ZB_DOWNWARD = CLOCK_POS_INFINITY;
	
	  child = crd_one_constraint(
	    grown_child,
	    d->var_index, d->u.crd.arc[ci].upper_bound
	  );
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      if (!c2) {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);

	  ZM_DOWNWARD = c1;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_tight_magnitudes_to_zero_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  ZB_DOWNWARD = CLOCK_POS_INFINITY;
	
	  child = crd_one_constraint(grown_child,
	  		  d->var_index, d->u.crd.arc[ci].upper_bound
	  		  );
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
    }
    break;
  case TYPE_FLOAT:
/* 
    fprintf(RED_OUT, "\nrec tight magnitudes DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_magnitudes_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound 
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
/* 
    fprintf(RED_OUT, "\nrec tight magnitudes DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_magnitudes_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound 
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
/* 
    fprintf(RED_OUT, "\nrec tight magnitudes DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_magnitudes_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_magnitudes_DOWNWARD_through_magnitudes(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(child,
				      d->var_index, d->u.ddd.arc[ci].lower_bound,
			       	      d->u.ddd.arc[ci].upper_bound 
				      );
      result = red_bop(OR, result, child);
    }
  } 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_NORMALIZE
    fprintf(RED_OUT, "\nrec_tight_magnitudes_DOWNWARD_through_magnitudes() with d:\n"); 
    red_print_graph(d); 
    fprintf(RED_OUT, "result: \n"); 
    red_print_graph(result); 
    #endif 
  #endif 

  return(ce->result = result); 
}
  /* rec_tight_magnitudes_DOWNWARD_through_magnitudes() */





struct red_type	*rec_tight_differences_from_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[CLOCK_COUNT-1][0])
    return(d);

#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_TIGHT_DIFFERENCES_FROM_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (!c2) {
      if (c1 == ZM_DOWNWARD) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_tight_differences_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  child = rec_tight_differences_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  child = crd_one_constraint(child, ZONE[c1][ZM_DOWNWARD], b);
/*
	  child = red_bop(AND, child,
			  red_bop(AND,
			  	  crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound),
				  crd_atom(ZONE[c1][ZM_DOWNWARD], b)
				  )
			  );
*/
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_tight_differences_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_differences_from_zero_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child,
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_differences_from_zero_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child,
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_differences_from_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(child,
		      		d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
		      );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_tight_differences_from_zero_DOWNWARD() */






struct red_type	*rec_tight_differences_to_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, ci, c1, c2;
  struct red_type		*result, *child;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[0][CLOCK_COUNT-1])
    return(d);

#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(OP_TIGHT_DIFFERENCES_TO_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (!c1) {
      if (c2 == ZM_DOWNWARD) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_tight_differences_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  child = rec_tight_differences_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b == CLOCK_POS_INFINITY)
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  else {
	    child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	    child = crd_one_constraint(child, ZONE[ZM_DOWNWARD][c2], b);
/*
	    child = red_bop(AND, child,
			    red_bop(AND, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound),
				    crd_atom(ZONE[ZM_DOWNWARD][c2], b)
				    )
			    );
*/
	  }
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_tight_differences_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_differences_to_zero_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound 
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_differences_to_zero_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound 
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_differences_to_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(child,
		      		d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
		      );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_tight_differences_to_zero_DOWNWARD() */





// int	count_tight_differences_DOWNWARD_through_magnitudes = 0; 

struct red_type	*rec_tight_differences_DOWNWARD_through_magnitudes(d)
     struct red_type	*d;
{
  int				ci, c1, c2;
  struct red_type		*result, *child, *grown_child;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE  
      || d->var_index > ZONE[CLOCK_COUNT-1][0]
      )
    return(d);

  ce = cache1_check_result_key(OP_TIGHT_DIFFERENCES_DOWNWRAD_THROUGH_MAGNITUDES, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (!c1) {
      if (!c2) {
	fprintf(RED_OUT, "\nError: how come this happen ? \n");
	for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
	exit(0);
      }
      else {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_differences_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);

	  ZM_DOWNWARD = c2;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_tight_differences_from_zero_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  ZB_DOWNWARD = CLOCK_POS_INFINITY;
	
	  child = crd_one_constraint(grown_child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      if (!c2) {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_differences_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);

	  ZM_DOWNWARD = c1;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_tight_differences_to_zero_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  ZB_DOWNWARD = CLOCK_POS_INFINITY;
	
	  child = crd_one_constraint(grown_child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = 0; ci < d->u.crd.child_count; ci++) {
	  child = rec_tight_differences_DOWNWARD_through_magnitudes(d->u.crd.arc[ci].child);
	  child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
	}
      }
    }
    break;
  case TYPE_FLOAT:
/*
    fprintf(RED_OUT, "\nrec tight differences DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_differences_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_tight_differences_DOWNWARD_through_magnitudes(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
/*
    fprintf(RED_OUT, "\nrec tight differences DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_differences_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_tight_differences_DOWNWARD_through_magnitudes(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
/*
    fprintf(RED_OUT, "\nrec tight differences DOWNWARD through magnitudes %1d, %1d:%s\n", 
      ++count_tight_differences_DOWNWARD_through_magnitudes, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_tight_differences_DOWNWARD_through_magnitudes(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(child,
		      		d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
		      );
      result = red_bop(OR, result, child);
    }
  }
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_NORMALIZE
    fprintf(RED_OUT, "\nrec_tight_differences_DOWNWARD_through_magnitudes() with d:\n"); 
    red_print_graph(d); 
    fprintf(RED_OUT, "result: \n"); 
    red_print_graph(result); 
    #endif 
  #endif 
  return(ce->result = result); 
}
  /* rec_tight_differences_DOWNWARD_through_magnitudes() */







struct red_type	*rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2;
  struct red_type		*result, *child, *new_record;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[ZM_DOWNWARD][CLOCK_COUNT-1])
    return(d);

  ce = cache4_check_result_key(
    OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_FROM_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == ZM_DOWNWARD) {
      if (!c2) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  if (b > 0) {
	    b = 0;
	  }
	  child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  child = red_bop(AND, child,crd_atom(ZONE[0][c2], b));
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound));
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = red_bop(AND, child,
	fdd_atom(d->var_index, d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound
	)
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = red_bop(AND, child, 
	dfdd_atom(d->var_index, d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound
	)
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = red_bop(AND, child,
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
			       )
		      );
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_inactive_clock_tight_magnitudes_from_zero_DOWNWARD() */







struct red_type	*rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2, 
  				old_bound, old_c1_bound, old_c2_bound;
  struct red_type		*result, *child, *new_record;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[CLOCK_COUNT-1][ZM_DOWNWARD])
    return(d);

  ce = cache4_check_result_key(
    OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_TO_ZERO_DOWNWARD, d, 
    NULL, 
    ZM_DOWNWARD, 
    ZB_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c2 == ZM_DOWNWARD) {
      if (!c1) {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  result = red_bop(OR, result, child);
	}
      }
      else {
	for (ci = d->u.crd.child_count - 1; ci >= 0; ci--) {
	  b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD);
	  if (b < 0) {
	    break;
	  }
	  child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	  if (b < CLOCK_POS_INFINITY)
	    child = red_bop(AND, child, crd_atom(ZONE[c1][0], b));
	  result = red_bop(OR, result, child);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(d->u.crd.arc[ci].child);
	child = red_bop(AND, child, crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound));
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD(d->u.ddd.arc[ci].child);
      child = red_bop(AND, child,
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
			       )
		      );
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_inactive_clock_tight_magnitudes_to_zero_DOWNWARD() */







struct red_type	*rec_inactive_clock_tight_magnitudes_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2, old_bound, old_c1_bound, old_c2_bound;
  struct red_type		*result, *child, *grown_child;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[ZM_DOWNWARD][0])
    return(d);

  ce = cache1_check_result_key(
    OP_INACTIVE_CLOCK_TIGHT_MAGNITUDES_DOWNWARD, d
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->var_index == ZONE[0][ZM_DOWNWARD]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_inactive_clock_tight_magnitudes_DOWNWARD(d->u.crd.arc[ci].child);
	ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
	grown_child = rec_tight_magnitudes_from_zero_DOWNWARD(child);
	result = red_bop(OR, result, grown_child);
      }
      ZB_DOWNWARD = CLOCK_POS_INFINITY;
    }
    else if (d->var_index == ZONE[ZM_DOWNWARD][0]) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_inactive_clock_tight_magnitudes_DOWNWARD(d->u.crd.arc[ci].child);
	ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
	grown_child = rec_tight_magnitudes_to_zero_DOWNWARD(child);
	result = red_bop(OR, result, grown_child);
      }
      ZB_DOWNWARD = CLOCK_POS_INFINITY;
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_inactive_clock_tight_magnitudes_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_inactive_clock_tight_magnitudes_DOWNWARD(d->u.ddd.arc[ci].child);
      child = red_bop(AND, child,
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound,
			       d->u.ddd.arc[ci].upper_bound
			       )
		      );
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_inactive_clock_tight_magnitudes_DOWNWARD() */






struct red_type	*red_hull_inactive(w, clhs)
     int	w, clhs;
{
  struct red_type	*result;

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_UNTIMED) 
    return(RT[w]); 
    
  /*
  switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
  case FLAG_NORM_ZONE_CLOSURE: 
  // FLAG_NORM_CLOSURE is here with the assumption
  // that only magnitude constraints are used.
  //
    ZM_DOWNWARD = clhs;
    result = rec_inactive_clock_tight_magnitudes_DOWNWARD(RT[w]);
    RT[w] = red_time_clock_eliminate(result, clhs);
    break;
  default:
*/
    if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)
      RT[w] = RED_BYPASS_BCK(w, clhs);
    else
      RT[w] = RED_BYPASS_FWD(w, clhs);
    RT[w] = red_time_clock_eliminate(RT[w], clhs); 
/*
    break;
  }
*/
  return(RT[w]);
}
/* red_hull_inactive() */







/*****************************************************************************
 * eliminate magnitude redundancy with filter techniques
 */
int		flag_total_progress,
		VW, VGROW, VEND, VNEW_GROW, VEXAM_UPPER, VEXAM_LOWER,
		VGROW_WEIGHT, VLEFT, VRIGHT;
struct red_type	*RED_GROW;




void	bchild_stack_unionpush(d, ub)
     struct red_type	*d;
     int		ub; 
{
  int	i; 
  
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

  if (d == NORM_FALSE) 
    return; 

  for (i = TOP_CHILD_STACK; 
       i >= 0 && CHILD_STACK[i].level == TOP_LEVEL_CHILD_STACK; 
       i--
       ) 
    if (d == CHILD_STACK[i].d) 
      return;

  if (   TOP_CHILD_STACK >= 0 
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK
      && CHILD_STACK[TOP_CHILD_STACK].u.crd.ub == ub
      ) { 
    CHILD_STACK[TOP_CHILD_STACK].d 
    = red_bop(OR, CHILD_STACK[TOP_CHILD_STACK].d, d); 
  }
  else { 
    child_stack_epush(); 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
    CHILD_STACK[TOP_CHILD_STACK].u.crd.ub = ub; 
  }
}
/* bchild_stack_unionpush() */ 




void	red_test_redundancy(d, s) 
     struct red_type	*d; 
     char		*s; 
{
  struct red_type	*filter; 

  if (ITERATION_COUNT == 3
      && (    (testm[0] == 0
	       && testm[1] == 2
	       && testm[2] == 2
	       && testm[3] == 1
	       && testm[4] == 1
	       && testm[5] == 1
	       )
	  || (testm[0] == 5
	      && testm[1] == 2
	      && testm[2] == 2
	      && testm[3] == 1
	      && testm[4] == 1
	      && testm[5] == 2
	      ) 
	  )
      ) {
    fprintf(RED_OUT, "\n%s\n", s); 
    red_print_graph(d); 
    fflush(RED_OUT); 
  }
}
/* red_test_filter() */ 





void	red_test_filter(d, s) 
     struct red_type	*d; 
     char		*s; 
{
  struct red_type	*filter; 

  if (ITERATION_COUNT == 3) {
    filter = NORM_NO_RESTRICTION; 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_POINTER][0][0], 5, 5)); 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][1][0], 2, 2)); 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][2][0], 2, 2)); 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][3][0], 1, 1)); 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][4][0], 1, 1)); 
    filter = red_bop(AND, filter, ddd_atom(variable_index[TYPE_DISCRETE][5][0], 2, 2)); 
    
    filter = red_bop(AND, d, filter); 
    fprintf(RED_OUT, "\n%s\n", s); 
    red_print_graph(filter); 
    fflush(RED_OUT); 
  }
}
/* red_test_filter() */ 











/*****************************************************************************
 * eliminate magnitude redundancy with record array techniques
 */



struct red_type	*rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d) 
     struct red_type	*d; 
{
  int				b, b1, b2, ci, c1, c2; 
  struct red_type		*result, *child, *child2, *filter; 
  struct cache4_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION 
      || (d->var_index > ZONE[CLOCK_COUNT-1][ZL_DOWNWARD] && d->var_index > ZONE[ZR_DOWNWARD][CLOCK_COUNT-1])
      ) 
    return(d); 
  
  ce = cache4_check_result_key(
    OP_ELIMINATE_ONE_GROUP_MAGNITUDE_REDUNDANCY_DOWNWARD, d, 
    (struct hrd_exp_type *) ZL_DOWNWARD, 
    ZR_DOWNWARD, 
    ZB_DOWNWARD    
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:  
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0 || c2 == 0) {
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, child); 
      } 
    }      
    else if (c1 == ZR_DOWNWARD) { 
      if (c2 == ZL_DOWNWARD) { 
	for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound); 
	  if (b < 0)
	    break; 
	  else {
	    child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	    child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	    result = red_bop(OR, result, child); 
	  }
	} 
      }
      else { 
	for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound); 
	  if (b < 0 && c2 == 0)
	    break; 
	  else if (ZL_DOWNWARD == 0 && b > 0) 
	    child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	  else { 
	    child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	    if (d->var_index < ZONE[ZL_DOWNWARD][c2]) {
	      child2 = zone_extract_interval(child, ZONE[ZL_DOWNWARD][c2], b, CLOCK_POS_INFINITY); 
	      child = zone_subtract_interval(child, ZONE[ZL_DOWNWARD][c2], b, CLOCK_POS_INFINITY); 
	      child2 = red_variable_eliminate(child2, ZONE[ZL_DOWNWARD][c2]); 
	      child = red_bop(OR, child, child2); 
	    } 
	  }
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	  result = red_bop(OR, result, child); 
	} 
      }
    }
    else if (c2 == ZL_DOWNWARD) { 
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	b = zone_ub_add(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD); 
	if (b < 0 && ZR_DOWNWARD == 0)
	  break; 
	else if (c1 == 0 && b > 0) 
	  child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	else { 
	  child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	  if (d->var_index < ZONE[c1][ZR_DOWNWARD]) {
	    child2 = zone_extract_interval(child, ZONE[c1][ZR_DOWNWARD], b, CLOCK_POS_INFINITY); 
	    child = zone_subtract_interval(child, ZONE[c1][ZR_DOWNWARD], b, CLOCK_POS_INFINITY); 
	    child2 = red_variable_eliminate(child2, ZONE[c1][ZR_DOWNWARD]); 
	    child = red_bop(OR, child, child2); 
	  } 
	}
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, child); 
      } 
    }
    else if (c1 == ZL_DOWNWARD) { 
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	if (d->var_index < ZONE[ZR_DOWNWARD][c2] && d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY) {
	  b = zone_lb_subtract(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD); 
	  if (b > CLOCK_NEG_INFINITY) { 
	    child2 = zone_extract_interval(child, ZONE[ZR_DOWNWARD][c2], CLOCK_NEG_INFINITY, b); 
	    child = zone_subtract_interval(child, ZONE[ZR_DOWNWARD][c2], CLOCK_NEG_INFINITY, b);
	    child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	    child = red_bop(OR, child, child2); 
	  }
	  else 
	    child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	}
	else 
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, child); 
      }       
    } 
    else if (c2 == ZR_DOWNWARD) { 
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	if (d->var_index < ZONE[c1][ZL_DOWNWARD]) {
	  b = zone_lb_subtract(d->u.crd.arc[ci].upper_bound, ZB_DOWNWARD); 
	  if (b > CLOCK_NEG_INFINITY && d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY) { 
	    child2 = zone_extract_interval(child, ZONE[c1][ZL_DOWNWARD], CLOCK_NEG_INFINITY, b); 
	    child = zone_subtract_interval(child, ZONE[c1][ZL_DOWNWARD], CLOCK_NEG_INFINITY, b);
	    child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	    child = red_bop(OR, child, child2); 
	  }
	  else 
	    child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	}
	else 
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, child); 
      }       
    }
    else {
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) { 
	child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child); 
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
	result = red_bop(OR, result, child); 
      } 
    }      
    break; 
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(
        d->u.fdd.arc[ci].child 
      ); 
      child = fdd_lone_subtree(child, d->var_index, 
      	d->u.fdd.arc[ci].lower_bound, 
      	d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(
        d->u.dfdd.arc[ci].child 
      ); 
      child = dfdd_lone_subtree(child, d->var_index, 
      	d->u.dfdd.arc[ci].lower_bound, 
      	d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(d->u.ddd.arc[ci].child); 
      child = ddd_lone_subtree(child, d->var_index, 
      			       d->u.ddd.arc[ci].lower_bound, 
      			       d->u.ddd.arc[ci].upper_bound
			       ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_eliminate_one_group_magnitude_redundancy_DOWNWARD() */ 





struct red_type	*rec_eliminate_magnitude_redundancy_DOWNWARD(d) 
     struct red_type	*d; 
{
  int				b, b1, b2, ci, c1, c2, old_bound, old_c1_bound, old_c2_bound; 
  struct red_type		*result, *child, *grown_child; 
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    return(d); 
  
  ce = cache1_check_result_key(OP_ELIMINATE_MAGNITUDE_REDUDANCY_DOWNWARD, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:  
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      child = rec_eliminate_magnitude_redundancy_DOWNWARD(d->u.crd.arc[ci].child);   
      ZL_DOWNWARD = c1; 
      ZR_DOWNWARD = c2; 
      ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound; 
      grown_child = rec_eliminate_one_group_magnitude_redundancy_DOWNWARD(child); 
    
      child = red_bop(AND, grown_child, 
      		      crd_atom(d->var_index, d->u.crd.arc[ci].upper_bound)
      		      ); 
      result = red_bop(OR, result, child); 
    }
    break; 
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundancy_DOWNWARD(
        d->u.fdd.arc[ci].child
      ); 
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundancy_DOWNWARD(
        d->u.dfdd.arc[ci].child
      ); 
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundancy_DOWNWARD(d->u.ddd.arc[ci].child); 
      child = red_bop(AND, child, 
		      ddd_atom(d->var_index, d->u.ddd.arc[ci].lower_bound, 
			       d->u.ddd.arc[ci].upper_bound
			       )
		      ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_eliminate_magnitude_redundancy_DOWNWARD() */ 




struct red_type	*red_eliminate_magnitude_redundancy_DOWNWARD(w)
     int	w; 
{
  int	i; 
  struct red_type	*result; 

  /* 
  print_cpu_time("Entering red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */  
  result = rec_eliminate_magnitude_redundancy_DOWNWARD(RT[w]); 
  RT[w] = result; 
  garbage_collect(FLAG_GC_SILENT); 
  /* 
  print_cpu_time("Leaving red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */ 
  return(RT[w]); 
}
/* red_eliminate_magnitude_redundancy_DOWNWARD() */ 








/************************************************************
 * normal form with closure techniques
 */

#define	FLAG_CLOCK_POS	1
#define	FLAG_CLOCK_NEG	2 

int	*flag_clock; 

void	rec_mark_clocks(d)
     struct red_type	*d; 
{
  int	ci, len, vi;

/*
  fprintf(RED_OUT, "count_mark_clocks = %1d\n", ++count_mark_clocks); 
  for (; count_mark_clocks == 119; ) ; 
*/
  if (   d == NORM_NO_RESTRICTION 
      || d == NORM_FALSE 
      ) { 
    return;
  } 
  else if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) 
    if (d->result_stack->result) {
      return; 
    } 
    else {
      d->result_stack->result = NORM_NO_RESTRICTION; 
    }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD:
    rec_mark_clocks(d->u.bdd.zero_child); 
    rec_mark_clocks(d->u.bdd.one_child); 
    break; 
  case TYPE_CRD /* TYPE_CRD*/ : 
    flag_clock[VAR[d->var_index].U.CRD.CLOCK1] 
    = flag_clock[VAR[d->var_index].U.CRD.CLOCK1] | FLAG_CLOCK_POS; 
    flag_clock[VAR[d->var_index].U.CRD.CLOCK2] 
    = flag_clock[VAR[d->var_index].U.CRD.CLOCK2] | FLAG_CLOCK_NEG;  
    for (ci = 0; ci < d->u.crd.child_count; ci++)
      rec_mark_clocks(d->u.crd.arc[ci].child);
    break;
  case TYPE_HRD /* TYPE_HRD*/ :
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      vi = d->u.hrd.hrd_exp->hrd_term[ci].var_index;
      if (VAR[vi].TYPE == TYPE_CLOCK) 
        if (d->u.hrd.hrd_exp->hrd_term[ci].coeff > 0) 
          flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] 
          = flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] | FLAG_CLOCK_POS;
        else 
          flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] 
          = flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] | FLAG_CLOCK_NEG;
    } 
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_mark_clocks(d->u.hrd.arc[ci].child);
    break;
    
  case TYPE_CDD /* TYPE_CDD*/ : 
    flag_clock[VAR[d->var_index].U.CDD.CLOCK1] 
    = flag_clock[VAR[d->var_index].U.CDD.CLOCK1] | FLAG_CLOCK_POS; 
    flag_clock[VAR[d->var_index].U.CDD.CLOCK2] 
    = flag_clock[VAR[d->var_index].U.CDD.CLOCK2] | FLAG_CLOCK_NEG;  
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_mark_clocks(d->u.ddd.arc[ci].child);
    break;
    
  case TYPE_HDD /* TYPE_HDD*/ :
    len = d->u.hdd.hrd_exp->status & MASK_HYBRID_LENGTH;
    for (ci = 0; ci < len; ci++) {
      vi = d->u.hdd.hrd_exp->hrd_term[ci].var_index;
      if (VAR[vi].TYPE == TYPE_CLOCK) 
        if (d->u.hrd.hrd_exp->hrd_term[ci].coeff > 0) 
          flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] 
          = flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] | FLAG_CLOCK_POS;
        else 
          flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] 
          = flag_clock[VAR[vi].U.CLOCK.CLOCK_INDEX] | FLAG_CLOCK_NEG;
    }
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      rec_mark_clocks(d->u.hdd.arc[ci].child);

    break;    
  case TYPE_LAZY_EXP: 
    rec_mark_clocks(d->u.lazy.false_child);  
    rec_mark_clocks(d->u.lazy.true_child);  
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_mark_clocks(d->u.fdd.arc[ci].child);
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_mark_clocks(d->u.dfdd.arc[ci].child);
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_mark_clocks(d->u.ddd.arc[ci].child);
  }
}
  /* rec_mark_clocks() */




void	red_mark_clocks(d)
     struct red_type	*d;
{
  int	i; 
  
  if (!CLOCK_COUNT) 
    return; 

  for (i = 0; i < CLOCK_COUNT; i++) { 
    flag_clock[i] = 0; 
  }
  red_init_result(d); 
  rec_mark_clocks(d);
  red_clear_result(); 
//081225 CHANGE
  flag_clock[TIME] = 0; 
}
/* red_mark_clocks() */ 


struct red_type	*red_tight_all_pairs(w)
     int	w;
{
  int	zi, zj, zk, arc1, weight1, arc2, weight2, b; 
  /*
  fprintf(RED_OUT, "\n=====(tight start)================================================================\n");
  fprintf(RED_OUT, "RED size at the start of red_tight() at iteration %1d\n", ITERATION_COUNT);
  print_cpu_time("In tight");
  red_size(RT[w], SIZE_REPORT, NULL, NULL);
  red_print_graph(RT[w]);
  */
  if (!CLOCK_COUNT) 
    return(RT[w]); 

  red_mark_clocks(RT[w]); 
  
  if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) {
    for (zk = 0; zk < CLOCK_COUNT; zk++) {
      if (flag_clock[zk] == (FLAG_CLOCK_POS | FLAG_CLOCK_NEG)) { 
	#ifdef RED_DEBUG_ZONE_MODE_NORMALIZE
        fprintf(RED_OUT, 
          "\n-----(bypass bck start for zk: %1d:%s)-------------\n", 
          zk, VAR[CLOCK[zk]].NAME
        );
        red_print_graph(RT[w]); 
        #endif 
      /* 
      fprintf(RED_OUT, "RED size at the start of red_tight() iteration at iteration %1d\n", ITERATION_COUNT);
      print_cpu_time("In tight iteations");
      red_size(RT[w], SIZE_REPORT, NULL, NULL);
      red_print_graph(RT[w]);
      */
        RT[w] = RED_BYPASS_BCK(w, zk); 
	#ifdef RED_DEBUG_ZONE_MODE_NORMALIZE
        fprintf(RED_OUT, 
          "\n-----(after bypass for zk: %1d:%s)-------------\n", 
          zk, VAR[CLOCK[zk]].NAME
        );
        red_print_graph(RT[w]); 
        #endif 
/*
      if (count_tpb == 43) { 
        fprintf(RED_OUT, "after pivoting on clock %1d:%s\n", 
          zk, VAR[CLOCK[zk]].NAME
        ); 
        red_test_bisim(RT[w], "after pivoting on clock zk"); 
      } 
      fprintf(RED_OUT, "count_tapairs=%1d, after bypassing at zk=%1d\n", 
        count_tapairs, zk
      ); 
      ppca1(); 
*/
        garbage_collect(FLAG_GC_SILENT);
/*
      if (count_subtract_iterative == 7) { 
        fprintf(RED_OUT, "I%1d, subtract %1d, zone bck pivoting on ci=%1d:vi=%1d:%s RT[w=%1d]:\n", 
          ITERATION_COUNT, count_subtract_iterative, zk, CLOCK[zk], 
          VAR[CLOCK[zk]].NAME, w
        ); 
        red_print_graph(RT[w]); 
      }
*/
/*
      fprintf(RED_OUT, "RED size at the start of red_tight() iteration at iteration %1d\n", ITERATION_COUNT);
      print_cpu_time("In tight iterations");
      red_size(RT[w], SIZE_REPORT, NULL, NULL);
      */
      } 
    }
  } 
  else {
    for (zk = 0; zk < CLOCK_COUNT; zk++) 
      if (flag_clock[zk]) {
        RT[w] = RED_BYPASS_FWD(w, zk);
        garbage_collect(FLAG_GC_SILENT);
/*
      if (count_subtract_iterative == 7) { 
        fprintf(RED_OUT, "I%1d, subtract %1d, zone fwd pivoting on ci=%1d:vi=%1d:%s RT[w=%1d]:\n", 
          ITERATION_COUNT, count_subtract_iterative, zk, CLOCK[zk], 
          VAR[CLOCK[zk]].NAME, w
        ); 
        red_print_graph(RT[w]); 
      } 
*/
      }
  }
  /*
  fprintf(RED_OUT, "\n=====(tight end)================================================================\n");
  fprintf(RED_OUT, "RED size at the end of red_tight() at iteration %1d\n", ITERATION_COUNT);
  print_cpu_time("In tight");
  red_size(RT[w], SIZE_REPORT, NULL, NULL);
  red_print_graph(RT[w]);
  */
  RT[w] = red_subsume(RT[w]); 
  return(RT[w]);
}
/* red_tight_all_pairs() */








struct red_type	*red_tight_DOWNWARD_through_magnitudes(w)
     int	w;
{
  int	zi, zj, zk, arc1, weight1, arc2, weight2, b;
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\n=====(tight start)================================================================\n");
  fprintf(RED_OUT, "RED size at the start of red_tight() at iteration %1d\n", ITERATION_COUNT);
  print_cpu_time("In tight");
  red_size(RT[w], SIZE_REPORT, NULL, NULL);
  red_print_graph(RT[w]);
  */
  ZB_DOWNWARD = CLOCK_POS_INFINITY;
  result = rec_tight_magnitudes_DOWNWARD_through_magnitudes(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);

  ZB_DOWNWARD = CLOCK_POS_INFINITY;
  result = rec_tight_differences_DOWNWARD_through_magnitudes(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\n=====(tight end)================================================================\n");
  fprintf(RED_OUT, "RED size at the end of red_tight() at iteration %1d\n", ITERATION_COUNT);
  print_cpu_time("In tight");
  red_size(RT[w], SIZE_REPORT, NULL, NULL);
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* red_tight_DOWNWARD_through_magnitudes() */





/****************************************************************************
*  Procedures that remove redundant difference inequalities deduced from magnitude inequalities.
*/
int	ZONE_PIVOT; 

struct red_type	*rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2;
  struct red_type		*result, *child, *child2, *filter;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[CLOCK_COUNT-1][0])
    return(d); 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(
    OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_RIGHT_DOWNWARD, d, 
    (struct hrd_exp_type *) ZONE_PIVOT, 
    ZR_DOWNWARD, 
    ZB_DOWNWARD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c2 == ZONE_PIVOT && c1 > ZONE_PIVOT)
      if (c1 == ZR_DOWNWARD) {
        for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  if (b < 0)
	    break;
	  child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        }
      }
      else {
        for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	  child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  if (b < CLOCK_POS_INFINITY) {
	    child2 = zone_extract_interval(child, ZONE[c1][ZR_DOWNWARD], b, CLOCK_POS_INFINITY);
	    child = zone_subtract_interval(child, ZONE[c1][ZR_DOWNWARD], b, CLOCK_POS_INFINITY);
	    child2 = red_variable_eliminate(child2, ZONE[c1][ZR_DOWNWARD]);
	    child = red_bop(OR, child, child2);
	  }
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        }
      }
    else
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index,
      	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index,
      	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree(child, d->var_index,
      	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD() */









struct red_type	*rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2;
  struct red_type		*result, *child, *child2, *filter;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  struct cache4_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[0][CLOCK_COUNT-1])
    return(d);

#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  ce = cache4_check_result_key(
    OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_LEFT_DOWNWARD, d, 
    (struct hrd_exp_type *) ZONE_PIVOT, 
    ZL_DOWNWARD, 
    ZB_DOWNWARD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == ZONE_PIVOT && c2 > ZONE_PIVOT)
      if (c2 == ZL_DOWNWARD) {
        for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  if (b < 0)
	    break;
	  child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        }
      }
      else {
        for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	  child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	  b = zone_ub_add(ZB_DOWNWARD, d->u.crd.arc[ci].upper_bound);
	  if (b < CLOCK_POS_INFINITY) {
	    child2 = zone_extract_interval(child, ZONE[ZL_DOWNWARD][c2], b, CLOCK_POS_INFINITY);
	    child = zone_subtract_interval(child, ZONE[ZL_DOWNWARD][c2], b, CLOCK_POS_INFINITY);
	    child2 = red_variable_eliminate(child2, ZONE[ZL_DOWNWARD][c2]);
	    child = red_bop(OR, child, child2);
	  }
	  child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	  result = red_bop(OR, result, child);
        }
      }
    else {
      for (ci = d->u.crd.child_count-1; ci>=0; ci--) {
	child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index,
      	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index,
      	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree(child, d->var_index,
      			       d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
			       );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE4 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD() */





struct red_type	*rec_eliminate_magnitude_redundant_differences_DOWNWARD(d)
     struct red_type	*d;
{
  int				b, b1, b2, ci, c1, c2;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(
    OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_DOWNWARD, d, 
    (struct red_type *) ZONE_PIVOT
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 == ZONE_PIVOT && c2 > ZONE_PIVOT) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(d->u.crd.arc[ci].child);
	if (d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY) {
	  ZR_DOWNWARD = c2;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_eliminate_magnitude_redundant_differences_given_right_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  child = crd_lone_subtree(grown_child, d->var_index, d->u.crd.arc[ci].upper_bound);
	}
	result = red_bop(OR, result, child);
      }
    }
    else if (c2 == ZONE_PIVOT && c1 > ZONE_PIVOT) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(d->u.crd.arc[ci].child);
	if (d->u.crd.arc[ci].upper_bound < CLOCK_POS_INFINITY) {
	  ZL_DOWNWARD = c1;
	  ZB_DOWNWARD = d->u.crd.arc[ci].upper_bound;
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_init_result(child); 
#endif 
	  grown_child = rec_eliminate_magnitude_redundant_differences_given_left_DOWNWARD(child);
#if RED_MECH_CACHE4 == RED_MECH_CACHE_STACK 
	  red_clear_result(child); 
#endif 
	  child = crd_lone_subtree(grown_child, d->var_index, d->u.crd.arc[ci].upper_bound);
	}
	result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(d->u.crd.arc[ci].child);
	child = crd_lone_subtree(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_subtree(
      rec_eliminate_magnitude_redundant_differences_DOWNWARD(
        d->u.lazy.false_child
      ), 
      rec_eliminate_magnitude_redundant_differences_DOWNWARD(
        d->u.lazy.true_child
      ), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 
  
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break; 
  
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_eliminate_magnitude_redundant_differences_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_eliminate_magnitude_redundant_differences_DOWNWARD() */






struct red_type	*red_grow_DOWNWARD(w)
     int	w;
{
  int	old;
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */
  for (RT[old = RT_TOP++] = RT[w], VW = w; TYPE_TRUE; RT[old] = RT[w]) {
    result = rec_tight_magnitudes_DOWNWARD_through_magnitudes(RT[w]);
    RT[w] = result; 
    garbage_collect(FLAG_GC_SILENT); 

    if (RT[old] == RT[w]) 
      break; 
  } 
  RT_TOP--; 
  
  #ifdef RED_DEBUG_ZONE_MODE
  #ifdef RED_DEBUG_ZONE_MODE_NORMALIZE
  fprintf(RED_OUT, "\nred_grow() between the loop and differences\n"); 
  red_print_graph(RT[w]); 
  #endif 
  #endif 
  
  ZB_DOWNWARD = CLOCK_POS_INFINITY;
  result = rec_tight_differences_DOWNWARD_through_magnitudes(RT[w]);
  RT[w] = result;
  /* 
  fprintf(RED_OUT, "\nred_grow() with output:\n"); 
  red_print_graph(RT[w]); 
  */ 
  return(RT[w]); 
}
/* red_grow_DOWNWARD() */ 









/* Eliminate those inequality constraints according to the biggest timing constants that are
 * important for the current mode.
 */
int	BTC_VMI, BTC_CI;


struct red_type	*rec_push_big_timing_constant(d, mi)
     struct red_type	*d;
     int		mi;
{
  int				ci;
  struct red_type		*result;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d->var_index > ZONE[0][BTC_CI])
    return(d);
  ce = cache4_check_result_key(OP_PUSH_BIG_TIMING_CONSTANT, d, 
    (struct hrd_exp_type *) mi,
    BTC_VMI, 
    BTC_CI
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->var_index == ZONE[0][BTC_CI] && mi >= 0) {
      for (ci = 0;
              ci < d->u.crd.child_count 
           && d->u.crd.arc[ci].upper_bound + MODE[mi].bound[BTC_CI] <= 0;
           ci++
           ) {
        result = red_bop(OR, result, red_time_clock_eliminate(d->u.crd.arc[ci].child, BTC_CI));
      }
      result = crd_lone_subtree(result, d->var_index, CLOCK_NEG_INFINITY);
      for (; ci < d->u.crd.child_count; ci++) {
        result = red_bop(OR, result,
                         crd_lone_subtree
                         (d->u.crd.arc[ci].child, d->var_index,
         	         	      d->u.crd.arc[ci].upper_bound
                          )
                         );
      }
    } 
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        result = red_bop(OR, result,
                         crd_lone_subtree
                         (rec_push_big_timing_constant
                          (d->u.crd.arc[ci].child, mi),
                          d->var_index, d->u.crd.arc[ci].upper_bound
                          )
                         );
      }
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      result = red_bop(OR, result, fdd_one_constraint(
        rec_push_big_timing_constant(d->u.fdd.arc[ci].child, mi),
        d->var_index, d->u.fdd.arc[ci].lower_bound, 
        d->u.fdd.arc[ci].upper_bound
      ) );
    }
    break; 
    
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      result = red_bop(OR, result, dfdd_one_constraint(
        rec_push_big_timing_constant(d->u.dfdd.arc[ci].child, mi),
        d->var_index, d->u.dfdd.arc[ci].lower_bound, 
        d->u.dfdd.arc[ci].upper_bound
      ) );
    }
    break; 
    
  default:
    if (d->var_index == BTC_VMI) {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
          result = red_bop(OR, result,
                           ddd_one_constraint
                           (rec_push_big_timing_constant
                            (d->u.ddd.arc[ci].child, mi),
                             d->var_index, mi, mi
                            )
                           );
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        result = red_bop(OR, result,
                         ddd_one_constraint
                         (rec_push_big_timing_constant
                          (d->u.ddd.arc[ci].child, mi),
                          d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
                          )
                         );
      }
    }
  }
  return(ce->result = result); 
}
  /* rec_push_big_timing_constant() */





struct red_type	*red_push_big_timing_constant(w)
	int	w;
{
  int			pi, lci;
  struct red_type	*result;

  for (pi = 1; pi <= PROCESS_COUNT; pi++) {
    BTC_VMI = variable_index[TYPE_DISCRETE][pi][OFFSET_MODE];
    for (lci = 0; lci < LOCAL_COUNT[TYPE_CLOCK]; lci++) {
      BTC_CI = VAR[variable_index[TYPE_CLOCK][pi][lci]].U.CLOCK.CLOCK_INDEX;
      RT[w] = rec_push_big_timing_constant(RT[w], -1);
      garbage_collect(FLAG_GC_SILENT);
    }
  }
  return(RT[w]);
}
/* red_push_big_timing_constant() */





/******************************************************************
 *  The following procedures are for lb/ub reduction from UPPAAL. 
 */ 
struct clock_lub_type { 
  int	gub_max, glb_max, gmax, *ub_max, *lb_max, *max; 	
}; 


struct clock_lub_type	*clock_lub; 

struct a23tree_type	*clock_lub_tree; 

void	rec_get_clock_lubs(
  struct red_type	*d, 
  int			pi, 
  int			mi 
) { 
  int			ci, xi, nmi, npi, c1, c2;
  struct rec_type	*rec, *nrec; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  rec = rec_new(d, (struct red_type *) (pi * MODE_COUNT + mi)); 
  nrec = (struct rec_type *) add_23tree(
    rec, clock_lub_tree, rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) { 
    return; 
  } 

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_XTION_INSTANCE: 
    npi = VAR[d->var_index].PROC_INDEX; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      for (xi = d->u.ddd.arc[ci].lower_bound; 
        xi <= d->u.ddd.arc[ci].upper_bound; 
        xi++ 
      ) { 
        if (!xi) 
          continue; 
        nmi = XTION[xi].src_mode_index; 
        if (nmi >= 0 && nmi < MODE_COUNT) {
          rec_get_clock_lubs(XTION[xi].red_trigger[npi], npi, nmi); 
          rec_get_clock_lubs(MODE[nmi].invariance[npi].red, npi, nmi);
          rec_get_clock_lubs(d->u.ddd.arc[ci].child, npi, nmi);
        } 
        else for (nmi = 0; nmi < MODE_COUNT; nmi++) { 
          rec_get_clock_lubs(XTION[xi].red_trigger[npi], npi, nmi);
          rec_get_clock_lubs(MODE[nmi].invariance[npi].red, npi, nmi);
          rec_get_clock_lubs(d->u.ddd.arc[ci].child, npi, nmi);
    } } }
    break; 

  case TYPE_BDD:
    rec_get_clock_lubs(d->u.bdd.zero_child, pi, mi); 
    rec_get_clock_lubs(d->u.bdd.one_child, pi, mi); 
    break; 
  case TYPE_CRD /* TYPE_CRD*/ : 
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (!c1) {
      if (VAR[CLOCK[c2]].PROC_INDEX == pi) { 
      	if (clock_lub[c2].lb_max[mi] + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].lb_max[mi] = -1 * d->u.crd.arc[0].upper_bound; 
      	if (clock_lub[c2].glb_max + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].glb_max = -1 * d->u.crd.arc[0].upper_bound; 

      	if (clock_lub[c2].max[mi] + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].max[mi] = -1 * d->u.crd.arc[0].upper_bound; 
      	if (clock_lub[c2].gmax + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].gmax = -1 * d->u.crd.arc[0].upper_bound; 
      }
      else for (nmi = 0; nmi < MODE_COUNT; nmi++) { 
      	if (clock_lub[c2].lb_max[nmi] + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].lb_max[nmi] = -1 * d->u.crd.arc[0].upper_bound; 
      	if (clock_lub[c2].glb_max + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].glb_max = -1 * d->u.crd.arc[0].upper_bound; 

      	if (clock_lub[c2].max[nmi] + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].max[nmi] = -1 * d->u.crd.arc[0].upper_bound; 
      	if (clock_lub[c2].gmax + d->u.crd.arc[0].upper_bound < 0) 
      	  clock_lub[c2].gmax = -1 * d->u.crd.arc[0].upper_bound; 
      } 
    }
    else if (!c2) { 
      ci = d->u.crd.child_count-1; 
      if (VAR[CLOCK[c1]].PROC_INDEX == pi) { 
      	if (clock_lub[c1].ub_max[mi] - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].ub_max[mi] = d->u.crd.arc[ci].upper_bound; 
      	if (clock_lub[c1].gub_max - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].gub_max = d->u.crd.arc[ci].upper_bound; 

      	if (clock_lub[c1].max[mi] - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].max[mi] = d->u.crd.arc[ci].upper_bound; 
      	if (clock_lub[c1].gmax - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].gmax = d->u.crd.arc[ci].upper_bound; 
      }
      else for (nmi = 0; nmi < MODE_COUNT; nmi++) { 
      	if (clock_lub[c1].ub_max[nmi] - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].ub_max[nmi] = d->u.crd.arc[ci].upper_bound; 
      	if (clock_lub[c1].gub_max - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].gub_max = d->u.crd.arc[ci].upper_bound; 

      	if (clock_lub[c1].max[nmi] - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].max[nmi] = d->u.crd.arc[ci].upper_bound; 
      	if (clock_lub[c1].gmax - d->u.crd.arc[ci].upper_bound < 0) 
      	  clock_lub[c1].gmax = d->u.crd.arc[ci].upper_bound; 
      } 
    }
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      rec_get_clock_lubs(d->u.crd.arc[ci].child, pi, mi);
    }
    break;
  case TYPE_HRD /* TYPE_HRD*/ : 
    for (ci = 0; ci < d->u.hrd.child_count; ci++)
      rec_get_clock_lubs(d->u.hrd.arc[ci].child, pi, mi);
    break;
    
  case TYPE_CDD /* TYPE_CDD*/ : 
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_get_clock_lubs(d->u.ddd.arc[ci].child, pi, mi);
    break;
    
  case TYPE_HDD /* TYPE_HDD*/ :
    for (ci = 0; ci < d->u.hdd.child_count; ci++)
      rec_get_clock_lubs(d->u.hdd.arc[ci].child, pi, mi);
    break;    
  case TYPE_LAZY_EXP: 
    rec_get_clock_lubs(d->u.lazy.false_child, pi, mi);  
    rec_get_clock_lubs(d->u.lazy.true_child, pi, mi);  
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++)
      rec_get_clock_lubs(d->u.fdd.arc[ci].child, pi, mi);
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++)
      rec_get_clock_lubs(d->u.dfdd.arc[ci].child, pi, mi);
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++)
      rec_get_clock_lubs(d->u.ddd.arc[ci].child, pi, mi);
  }
  return; 
}
  /* rec_get_clock_lubs() */ 


inline void	get_clock_lubs(
  struct red_type	*d, 
  int			pi, 
  int			mi 
) { 
  init_23tree(&clock_lub_tree); 
  rec_get_clock_lubs(d, pi, mi); 
  free_entire_23tree(clock_lub_tree, rec_free); 	
}
  /* get_clock_lubs() */ 



int	check_clock_reset(
  struct statement_type	*st, 
  int			pi, 
  int			ci
) {
  int	i, vi; 
  
  if (!st) 
    return(0); 
    
  switch (st->op) { 
  case ST_IF: 
    if (   check_clock_reset(st->u.branch.if_statement, pi, ci)
        && check_clock_reset(st->u.branch.else_statement, pi, ci)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    return(TYPE_FALSE);   
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      if (check_clock_reset(st->u.seq.statement[i], pi, ci)) 
        return(TYPE_TRUE); 
    } 
    return(TYPE_FALSE); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
    return(TYPE_FALSE); 
    break; 
  case ASSIGN_CLOCK_CONSTANT: 
    vi = st->u.act.lhs->u.atom.var_index; 
    vi = variable_index[TYPE_CLOCK][pi][VAR[vi].OFFSET]; 
    if (vi == CLOCK[ci]) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  default: 
    return(TYPE_FALSE); 
  } 
}
  /* check_clock_reset() */ 





void	clock_lubs_xtivity_closure() {
  int	ci, pi, flag_change, ixi, xi, src, dst; 
  
  for (ci = 0; ci < CLOCK_COUNT; ci++) { 
    pi = VAR[CLOCK[ci]].PROC_INDEX; 
    if (!pi) 
      continue; 
    for (flag_change = TYPE_TRUE; flag_change; ) { 
      flag_change = TYPE_FALSE; 
      for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) { 
      	xi = PROCESS[pi].firable_xtion[ixi]; 
        if (xi == 0 || check_clock_reset(XTION[xi].statement, pi, ci)) 
          continue; 
        src = XTION[xi].src_mode_index; 
        dst = XTION[xi].dst_mode_index; 
        if (   src != dst 
            && src >= 0 && src < MODE_COUNT 
            && dst >= 0 && dst < MODE_COUNT
            ) {
          if (clock_lub[ci].lb_max[src] < clock_lub[ci].lb_max[dst]) { 
            flag_change = TYPE_TRUE; 
            clock_lub[ci].lb_max[src] = clock_lub[ci].lb_max[dst]; 
          } 

          if (clock_lub[ci].ub_max[src] < clock_lub[ci].ub_max[dst]) { 
            flag_change = TYPE_TRUE; 
            clock_lub[ci].ub_max[src] = clock_lub[ci].ub_max[dst]; 
          } 

          if (clock_lub[ci].max[src] < clock_lub[ci].max[dst]) { 
            flag_change = TYPE_TRUE; 
            clock_lub[ci].max[src] = clock_lub[ci].max[dst]; 
          } 
  } } } }
}
  /* clock_lubs_xtivity_closure() */ 




void	analyze_clock_lubs() { 
  int	ci, mi, ipi, pi, sxi, xi; 
  
  clock_lub = (struct clock_lub_type *) 
    malloc(CLOCK_COUNT * sizeof(struct clock_lub_type)); 
  for (ci = 0; ci < CLOCK_COUNT; ci++) { 
    clock_lub[ci].glb_max = CLOCK_NEG_INFINITY; 	
    clock_lub[ci].gub_max = CLOCK_NEG_INFINITY; 	
    clock_lub[ci].gmax = CLOCK_NEG_INFINITY; 

    clock_lub[ci].lb_max = (int *) malloc(MODE_COUNT * sizeof(int)); 	
    clock_lub[ci].ub_max = (int *) malloc(MODE_COUNT * sizeof(int)); 	
    clock_lub[ci].max = (int *) malloc(MODE_COUNT * sizeof(int)); 
    for (mi = 0; mi < MODE_COUNT; mi++) { 
      clock_lub[ci].lb_max[mi] = CLOCK_NEG_INFINITY; 
      clock_lub[ci].ub_max[mi] = CLOCK_NEG_INFINITY; 
      clock_lub[ci].max[mi] = CLOCK_NEG_INFINITY; 
    } 
  } 
  
  for (mi = 0; mi < MODE_COUNT; mi++) { 
    for (ipi = 0; ipi < MODE[mi].process_count; ipi++) { 
      get_clock_lubs( 
        MODE[mi].invariance[MODE[mi].process[ipi]].red, 
        MODE[mi].process[ipi], mi
      ); 
  } }
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) { 
      xi = SYNC_XTION[sxi].party[ipi].xtion; 
      pi = SYNC_XTION[sxi].party[ipi].proc; 
      if (   XTION[xi].src_mode_index >= 0 
          && XTION[xi].src_mode_index < MODE_COUNT
          ) { 
      	get_clock_lubs(XTION[xi].red_trigger[pi], 
      	  pi, 
      	  XTION[xi].src_mode_index 
      	); 
      } 
      else for (mi = 0; mi < MODE_COUNT; mi++) { 
      	get_clock_lubs(XTION[xi].red_trigger[pi], 
      	  pi, 
      	  mi 
      	);
      } 
    } 	
  } 
  get_clock_lubs(RT[XI_SYNC_BULK], -1, -1); 
  
/*
  fprintf(RED_OUT, "\n<< Local clock bounds>> \n"); 
  for (ci = 0; ci < CLOCK_COUNT; ci++) { 
    fprintf(RED_OUT, "CLOCK %1d:%s bound analysis: \n", 
      ci, VAR[CLOCK[ci]].NAME
    ); 
    for (mi = 0; mi < MODE_COUNT; mi++) { 
      fprintf(RED_OUT, "  %1d:%s: lb_max=%1d, ub_max=%1d, max=%1d\n", 
        mi, MODE[mi].name, 
        clock_lub[ci].lb_max[mi], 
        clock_lub[ci].ub_max[mi], 
        clock_lub[ci].max[mi]
      ); 
    } 
    fprintf(RED_OUT, "\n"); 
  } 
  fflush(RED_OUT); 
*/
  clock_lubs_xtivity_closure(); 
} 
  /* analyze_clock_lubs() */ 




int
	MVI_LUB_EX_GIVEN_RIGHT, 
	MI_LUB_EX_GIVEN_RIGHT, 
	CLOCK_LUB_EX_GIVEN_RIGHT, 
	UB_LUB_EX_GIVEN_RIGHT; 

struct red_type	*rec_lub_extrapolate_given_right(
  struct red_type	*d
) { 
  int				ci, c1, c2, key;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  key = MVI_LUB_EX_GIVEN_RIGHT * MODE_COUNT + MI_LUB_EX_GIVEN_RIGHT; 
  key = CLOCK_COUNT * key + CLOCK_LUB_EX_GIVEN_RIGHT; 
  key = (2*CLOCK_POS_INFINITY + 1) * key + UB_LUB_EX_GIVEN_RIGHT; 
  ce = cache2_check_result_key(OP_LUB_EXTRAPOLATE_GIVEN_RIGHT, d, 
    (struct red_type *) key
  ); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_lub_extrapolate_given_right(d->u.bdd.zero_child), 
      rec_lub_extrapolate_given_right(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT); 
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (   VAR[CLOCK[c1]].PROC_INDEX
        && VAR[MVI_LUB_EX_GIVEN_RIGHT].PROC_INDEX 
           == VAR[CLOCK[c1]].PROC_INDEX
        ) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_lub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c1].lb_max[MI_LUB_EX_GIVEN_RIGHT] 
	    - d->u.crd.arc[ci].upper_bound 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else if (c1 == CLOCK_LUB_EX_GIVEN_RIGHT) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_lub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c1].lb_max[MI_LUB_EX_GIVEN_RIGHT] 
	    + UB_LUB_EX_GIVEN_RIGHT 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else if (c1 && c2 == CLOCK_LUB_EX_GIVEN_RIGHT) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_lub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c2].ub_max[MI_LUB_EX_GIVEN_RIGHT] 
	    + UB_LUB_EX_GIVEN_RIGHT 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_lub_extrapolate_given_right(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_lub_extrapolate_given_right(d->u.lazy.false_child), 
      rec_lub_extrapolate_given_right(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_lub_extrapolate_given_right(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_lub_extrapolate_given_right(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_lub_extrapolate_given_right(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(
        child, d->var_index, 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for input:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for result:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
  return(ce->result = result); 
}
  /* rec_lub_extrapolate_given_right() */



inline struct red_type	*red_lub_extrapolate_given_right(
  struct red_type	*d, 
  int			mvi, 
  int			mi, 
  int			c, 
  int			ub
) { 
  MVI_LUB_EX_GIVEN_RIGHT = mvi;  
  MI_LUB_EX_GIVEN_RIGHT = mi; 
  CLOCK_LUB_EX_GIVEN_RIGHT = c; 
  UB_LUB_EX_GIVEN_RIGHT = ub; 
  return(rec_lub_extrapolate_given_right(d)); 
}
  /* red_lub_extrapolate_given_right() */ 



struct red_type	*rec_lub_extrapolate(
  struct red_type	*d, 
  int			mvi, 
  int			mi
) { 
  int				ci, c1, c2, nmi;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 
/*
  if (count_bpD == 5) 
    print_cpu_time(">>bypass check %1d", ++count_bpc); 
*/
  ce = cache2_check_result_key(OP_LUB_EXTRAPOLATE, d, 
    (struct red_type *) (mvi * MODE_COUNT + mi)
  ); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_lub_extrapolate(d->u.bdd.zero_child, mvi, mi), 
      rec_lub_extrapolate(d->u.bdd.one_child, mvi, mi)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT);
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (   (!c1) 
        && VAR[CLOCK[c2]].PROC_INDEX
        && VAR[mvi].PROC_INDEX == VAR[CLOCK[c2]].PROC_INDEX
        ) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	child = rec_lub_extrapolate(d->u.crd.arc[ci].child, mvi, mi);
        child = red_lub_extrapolate_given_right(
          child, mvi, mi, c2, d->u.crd.arc[ci].upper_bound
        ); 
	if (d->u.crd.arc[ci].upper_bound + clock_lub[c2].ub_max[mi] < 0) 
	  child = crd_one_constraint(
	    child, d->var_index, -1 - clock_lub[c2].ub_max[mi]
	  );
	else 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_lub_extrapolate(d->u.crd.arc[ci].child, mvi, mi);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_lub_extrapolate(d->u.lazy.false_child, mvi, mi), 
      rec_lub_extrapolate(d->u.lazy.true_child, mvi, mi), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_lub_extrapolate(d->u.fdd.arc[ci].child, mvi, mi);
      child = fdd_one_constraint(child, d->var_index, 
      	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_lub_extrapolate(d->u.dfdd.arc[ci].child, mvi, mi);
      child = dfdd_one_constraint(child, d->var_index, 
      	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  default:
    if (VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX
        && VAR[d->var_index].OFFSET == OFFSET_MODE
        ) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	for (nmi = d->u.ddd.arc[ci].lower_bound; 
      	     nmi <= d->u.ddd.arc[ci].upper_bound; 
      	     nmi++
      	     ) { 
          child = rec_lub_extrapolate(
            d->u.ddd.arc[ci].child, d->var_index, nmi 
          );
          child = ddd_one_constraint(child, d->var_index, nmi, nmi); 
          result = red_bop(OR, result, child); 
    } } }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        child = rec_lub_extrapolate(d->u.ddd.arc[ci].child, mvi, mi);
        child = ddd_one_constraint(
          child, d->var_index, 
      	  d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
	); 
        result = red_bop(OR, result, child); 
    } }
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for input:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for result:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
  return(ce->result = result); 
}
  /* rec_lub_extrapolate() */



struct red_type	*rec_glub_extrapolate_given_right(
  struct red_type	*d
) { 
  int				ci, c1, c2, key;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  key = 0 * MODE_COUNT + 0; 
  key = CLOCK_COUNT * key + CLOCK_LUB_EX_GIVEN_RIGHT; 
  key = (2*CLOCK_POS_INFINITY + 1) * key + UB_LUB_EX_GIVEN_RIGHT; 
  ce = cache2_check_result_key(OP_LUB_EXTRAPOLATE_GIVEN_RIGHT, d, 
    (struct red_type *) key
  ); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_glub_extrapolate_given_right(d->u.bdd.zero_child), 
      rec_glub_extrapolate_given_right(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT); 
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (VAR[CLOCK[c1]].PROC_INDEX) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_glub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c1].glb_max 
	    - d->u.crd.arc[ci].upper_bound 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else if (c1 == CLOCK_LUB_EX_GIVEN_RIGHT) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_glub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c1].glb_max 
	    + UB_LUB_EX_GIVEN_RIGHT 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else if (c1 && c2 == CLOCK_LUB_EX_GIVEN_RIGHT) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
        child = rec_glub_extrapolate_given_right(d->u.crd.arc[ci].child); 
	if (clock_lub[c2].gub_max 
	    + UB_LUB_EX_GIVEN_RIGHT 
	    >= 0
	    ) 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_glub_extrapolate_given_right(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_glub_extrapolate_given_right(d->u.lazy.false_child), 
      rec_glub_extrapolate_given_right(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_glub_extrapolate_given_right(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_glub_extrapolate_given_right(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_glub_extrapolate_given_right(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(
        child, d->var_index, 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    }
  }
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_BYPASS 
    fprintf(RED_OUT, "\n\n*****************************************\n"); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for input:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(d); 
    fprintf(RED_OUT, "In rec_BYPASS_DOWNWARD(%s) for result:\n", 
      VAR[CLOCK[ZM_DOWNWARD]].NAME
    ); 
    red_print_graph(result); 
    #endif 
  #endif 
  return(ce->result = result); 
}
  /* rec_glub_extrapolate_given_right() */



inline struct red_type	*red_glub_extrapolate_given_right(
  struct red_type	*d, 
  int			c, 
  int			ub
) { 
  CLOCK_LUB_EX_GIVEN_RIGHT = c; 
  UB_LUB_EX_GIVEN_RIGHT = ub; 
  return(rec_glub_extrapolate_given_right(d)); 
}
  /* red_glub_extrapolate_given_right() */ 



struct red_type	*rec_glub_extrapolate(
  struct red_type	*d
) { 
  int				ci, c1, c2;
  struct red_type		*result, *child, *grown_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 
/*
  if (count_bpD == 5) 
    print_cpu_time(">>bypass check %1d", ++count_bpc); 
*/
  ce = cache2_check_result_key(OP_LUB_EXTRAPOLATE, d, 0); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_glub_extrapolate(d->u.bdd.zero_child), 
      rec_glub_extrapolate(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT);
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if ((!c1) && VAR[CLOCK[c2]].PROC_INDEX) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	child = rec_glub_extrapolate(d->u.crd.arc[ci].child);
        child = red_glub_extrapolate_given_right(
          child, c2, d->u.crd.arc[ci].upper_bound
        ); 
	if (d->u.crd.arc[ci].upper_bound + clock_lub[c2].gub_max < 0) 
	  child = crd_one_constraint(
	    child, d->var_index, -1 - clock_lub[c2].gub_max
	  );
	else 
	  child = crd_one_constraint(
	    child, d->var_index, d->u.crd.arc[ci].upper_bound
	  );
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
	child = rec_glub_extrapolate(d->u.crd.arc[ci].child);
	child = crd_one_constraint(child, 
	  d->var_index, d->u.crd.arc[ci].upper_bound
	);
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_glub_extrapolate(d->u.lazy.false_child), 
      rec_glub_extrapolate(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_glub_extrapolate(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index, 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_glub_extrapolate(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_glub_extrapolate(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(
        child, d->var_index, 
	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
  }
  return(ce->result = result); 
}
  /* rec_glub_extrapolate() */







struct red_type	*red_lub_extrapolate(
  struct red_type	*d
) {
  struct red_type	*result;
  
  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION) 
    return(d); 
  switch (GSTATUS[INDEX_LUB_EXTRAPOLATION] & MASK_LUB_EXTRAPOLATION) { 
  case FLAG_GLUB_EXTRAPOLATION: 
    result = rec_glub_extrapolate(d);
    break; 
  case FLAG_LUB_EXTRAPOLATION: 
    result = rec_lub_extrapolate(d, 0, 0);
    break; 
  }
  return(result);
}
/* red_lub_extrapolate() */ 



int	CLOCK_REDUCE_EQ_REMOVE; 

struct red_type	*rec_reduce_eq_remove_clock(
  struct red_type	*d
) { 
  int				ci, c1, c2;
  struct red_type		*result, *child, *subresult;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 
/*
  if (count_bpD == 5) 
    print_cpu_time(">>bypass check %1d", ++count_bpc); 
*/
  ce = cache2_check_result_key(OP_REDUCE_EQ_REMOVE_CLOCK, d, 
    (struct red_type *) CLOCK_REDUCE_EQ_REMOVE
  ); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_reduce_eq_remove_clock(d->u.bdd.zero_child), 
      rec_reduce_eq_remove_clock(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT);
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    result = NORM_FALSE; 
    if (c1 == CLOCK_REDUCE_EQ_REMOVE || c2 == CLOCK_REDUCE_EQ_REMOVE) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        result = red_bop(OR, result, 
      	  rec_reduce_eq_remove_clock(d->u.crd.arc[ci].child)
      	); 
    } }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	result = red_bop(OR, result, crd_one_constraint(
      	  rec_reduce_eq_remove_clock(d->u.crd.arc[ci].child), 
      	  d->var_index, d->u.crd.arc[ci].upper_bound
      	) ); 
      } 
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_reduce_eq_remove_clock(d->u.lazy.false_child), 
      rec_reduce_eq_remove_clock(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_reduce_eq_remove_clock(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index, 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_reduce_eq_remove_clock(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index, 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_reduce_eq_remove_clock(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint(
        child, d->var_index, 
	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
  }
  return(ce->result = result); 
}
  /* rec_reduce_eq_remove_clock() */




struct red_type	*red_reduce_eq_remove_clock(
  struct red_type	*d, 
  int			c2
) { 
  CLOCK_REDUCE_EQ_REMOVE = c2; 
  return(rec_reduce_eq_remove_clock(d)); 
} 
  /* red_reduce_eq_remove_clock() */ 




struct red_type	*rec_reduce_eq(
  struct red_type	*d
) { 
  int				ci, cj, ck, c1, c2;
  struct red_type		*result, *child, *subresult;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 
/*
  if (count_bpD == 5) 
    print_cpu_time(">>bypass check %1d", ++count_bpc); 
*/
  ce = cache1_check_result_key(OP_REDUCE_EQ, d); 
/*
  if (count_bpD == 5) 
    print_cpu_time("<<bypass check %1d", count_bpc); 
*/  
  #ifdef RED_DEBUG_ZONE_MODE
  thash_byd(); 
  fflush(RED_OUT); 
  for (; count_tapairs == -1 /*470121*/; ) ; 
  #endif 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

/*
  if (count_tapairs == 7425) {
    fprintf(RED_OUT, "count_rbdownward=%1d\n", count_rbdownward); 
    fflush(RED_OUT); 
    if (++count_rbdownward == RBSTOP) { 
//      fpca1(); 
      for (c1 = count_rbdownward; c1 == RBSTOP; ); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_reduce_eq(d->u.bdd.zero_child), 
      rec_reduce_eq(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
/*
    fprintf(RED_OUT, "\nrec bypass dw %1d.\n", ++count_bypass_DW); 
    if (count_bypass_DW == -1) { 
      fprintf(RED_OUT, "\nCaught!\n"); 
    } 
    fflush(RED_OUT);
*/
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    result = NORM_FALSE; 
    if (c1 < c2) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
      	child = d->u.crd.arc[ci].child; 
      	if (   (d->u.crd.arc[ci].upper_bound % 2)
      	    || (child->var_index != ZONE[c2][c1])
      	    ) {
      	  result = red_bop(OR, result, crd_one_constraint(
      	    rec_reduce_eq(child), 
      	    d->var_index, d->u.crd.arc[ci].upper_bound
      	  ) ); 
      	  continue; 
      	}
      	subresult = NORM_FALSE; 
      	for (cj = 0; cj < child->u.crd.child_count; cj++) 
      	  if (d->u.crd.arc[ci].upper_bound 
      	      + child->u.crd.arc[cj].upper_bound == 0
      	      ) { 
      	    subresult = red_reduce_eq_remove_clock(
      	      child->u.crd.arc[cj].child, c2
      	    ); 
      	    break; 
      	  } 
      	if (subresult == NORM_FALSE) { 
      	  subresult = rec_reduce_eq(child); 
      	} 
      	else { 
      	  subresult = crd_one_constraint(rec_reduce_eq(subresult), 
      	    ZONE[c2][c1], child->u.crd.arc[cj].upper_bound
      	  ); 
      	  for (ck = 0; ck < child->u.crd.child_count; ck++) { 
      	    if (ck != cj) {
       	      subresult = red_bop(OR, subresult, 
      	        crd_one_constraint(rec_reduce_eq(child->u.crd.arc[ck].child), 
      	          child->var_index, child->u.crd.arc[ck].upper_bound
      	      ) ); 
      	} } }
      	result = red_bop(OR, result, crd_one_constraint(
      	  subresult, d->var_index, d->u.crd.arc[ci].upper_bound
      	) ); 
      } 
    }
    else {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	result = red_bop(OR, result, crd_one_constraint(
      	  rec_reduce_eq(d->u.crd.arc[ci].child), 
      	  d->var_index, d->u.crd.arc[ci].upper_bound
      	) ); 
      } 
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_reduce_eq(d->u.lazy.false_child), 
      rec_reduce_eq(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(rec_reduce_eq(d->u.fdd.arc[ci].child), 
	d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
    } 
    result = fdd_new(d->var_index); 
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_reduce_eq(d->u.dfdd.arc[ci].child), 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
    } 
    result = dfdd_new(d->var_index); 
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) { 
      ichild_stack_push(rec_reduce_eq(d->u.ddd.arc[ci].child), 
	d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
    } 
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result); 
}
  /* rec_reduce_eq() */



struct red_type	*red_reduce_eq(struct red_type *d) { 
  return(rec_reduce_eq(d)); 
}
  /* red_reduce_eq() */ 







int	size_ch = 0, flag_ch, *size_gch, *flag_gch, **gch_ub; 
struct red_type	***gch; 

void	initialize_gch() { 
  int	ci; 
  
  flag_ch = TYPE_FALSE; 
  size_ch = 4; 
  gch = (struct red_type ***) malloc(size_ch * sizeof(struct red_type **)); 
  gch_ub = (int **) malloc(size_ch * sizeof(int *)); 
  flag_gch = (int *) malloc(size_ch * sizeof(int)); 
  size_gch = (int *) malloc(size_ch * sizeof(int)); 
  for (ci = 0; ci < size_ch; ci++) { 
    size_gch[ci] = 4; 
    flag_gch[ci] = TYPE_FALSE; 
    gch[ci] = (struct red_type **) 
      malloc(size_gch[ci]*sizeof(struct red_type *)); 	
    gch_ub[ci] = (int *) malloc(size_gch[ci]*sizeof(int)); 	
  } 
}
  /* initialize_gch() */ 




void	update_gch(struct red_type *d) { 
  struct red_type	*child, ***ngch; 
  int			c1, c2, ci, *size_ngch, **ngch_ub; 
  
  if (VAR[d->var_index].TYPE != TYPE_CRD) 
    return; 
  c1 = VAR[d->var_index].U.CRD.CLOCK1; 
  c2 = VAR[d->var_index].U.CRD.CLOCK2; 
  if (c1 > c2) 
    return; 
      
  if (size_ch < d->u.crd.child_count) { 
    ngch = (struct red_type ***) 
      malloc(2*d->u.crd.child_count*sizeof(struct red_type **)); 
    ngch_ub = (int **) malloc(2*d->u.crd.child_count*sizeof(int *)); 
    size_ngch = (int *) malloc(2*d->u.crd.child_count * sizeof(int)); 
    flag_gch = (int *) malloc(2*d->u.crd.child_count * sizeof(int)); 
    for (ci = 0; ci < size_ch; ci++) {
      ngch[ci] = gch[ci]; 
      ngch_ub[ci] = gch_ub[ci]; 
      size_ngch[ci] = size_gch[ci]; 
    } 
    for (; ci < 2*d->u.crd.child_count; ci++) { 
      ngch[ci] = (struct red_type **) malloc(4*sizeof(struct red_type *)); 
      ngch_ub[ci] = (int *) malloc(4*sizeof(int)); 
      size_ngch[ci] = 4; 
    } 
    free(gch); 
    free(size_gch); 
    
    size_ch = 2*d->u.crd.child_count; 
    gch = ngch; 
    size_gch = size_ngch; 
    gch_ub = ngch_ub; 
  } 
  for (ci = 0; ci < d->u.crd.child_count; ci++) { 
    child = d->u.crd.arc[ci].child; 
    if (   child->var_index != ZONE[c2][c1]
        || size_gch[ci] >= child->u.crd.child_count
        ) 
      continue; 
    free(gch[ci]); 
    free(gch_ub[ci]); 
    size_gch[ci] = 2*child->u.crd.child_count; 
    gch[ci] = (struct red_type **) 
      malloc(size_gch[ci] * sizeof(struct red_type *)); 
    gch_ub[ci] = (int *) malloc(size_gch[ci] * sizeof(int)); 
  } 
}
  /* update_gch() */ 




struct red_type	*rec_merge_zones(
  struct red_type	*d
) { 
  int				ci, cj, cip, cjp, c1, c2;
  struct red_type		*result, *child, *childp, *subresult;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  #ifdef RED_DEBUG_ZONE_MODE
  if (++count_tapairs <= -1 /*>= tashbound*/) 
    fprintf(RED_OUT, "count_tapairs=%1d, in bypass downward.\n", 
      count_tapairs
    ); 
  #endif 

  ce = cache1_check_result_key(OP_MERGE_ZONES, d); 
  
  if (ce->result) {
//    count_sh_bypass_downward++;  
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    return (bdd_new(d->var_index, 
      rec_merge_zones(d->u.bdd.zero_child), 
      rec_merge_zones(d->u.bdd.one_child)
    ) ); 
    break; 
  case TYPE_CRD:
    child_stack_level_push();
    c1 = VAR[d->var_index].U.CRD.CLOCK1;
    c2 = VAR[d->var_index].U.CRD.CLOCK2;
    if (c1 || c1 > c2) { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
      	bchild_stack_push( 
      	  rec_merge_zones(d->u.crd.arc[ci].child), 
      	  d->u.crd.arc[ci].upper_bound
      	); 
      }
      result = crd_new(d->var_index); 
    }
    else { 
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) { 
        bchild_stack_push( 
          rec_merge_zones(d->u.crd.arc[ci].child), 
          d->u.crd.arc[ci].upper_bound
        );  
      } 
      d = crd_new(d->var_index); 
      update_gch(d); 
      flag_ch = TYPE_FALSE; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) {
        child = d->u.crd.arc[ci].child; 
        flag_gch[ci] = TYPE_FALSE; 
        if (child->var_index != ZONE[c2][c1]) 
          continue; 
        for (cj = 0; cj < child->u.crd.child_count; cj++) {
          gch[ci][cj] = child->u.crd.arc[cj].child; 
          gch_ub[ci][cj] = child->u.crd.arc[cj].upper_bound; 
        }
      }
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	child = d->u.crd.arc[ci].child; 
      	if (child->var_index != ZONE[c2][c1]) 
      	  continue; 
        for (cip = ci+1; cip < d->u.crd.child_count; cip++) { 
          childp = d->u.crd.arc[cip].child; 
          if (childp->var_index != ZONE[c2][c1]) 
            continue; 
          for (cjp = childp->u.crd.child_count-1; cjp>=0; cjp--) { 
            if (gch_ub[cip][cjp] + d->u.crd.arc[ci].upper_bound < -1) 
              break; 
            for (cj = 0; cj < child->u.crd.child_count; cj++) { 
              if (gch[ci][cj] == gch[cip][cjp]) {
              	flag_ch = TYPE_TRUE; 
              	flag_gch[ci] = TYPE_TRUE; 
                gch[ci][cj] = NORM_FALSE; 
                if (gch_ub[cip][cjp] < gch_ub[ci][cj]) {
                  flag_gch[cip] = TYPE_TRUE; 
                  gch_ub[cip][cjp] = gch_ub[ci][cj]; 
                }
                gch_ub[ci][cj] = 0;  
              }
            } 
          }  
      } }
      if (!flag_ch) { 
      	return(d);  
      } 
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	child = d->u.crd.arc[ci].child; 
      	if (!flag_gch[ci]) {
      	  result = red_bop(OR, result, crd_one_constraint( 
      	    child, d->var_index, d->u.crd.arc[ci].upper_bound
      	  ) ); 
      	}
      	else { 
      	  subresult = NORM_FALSE; 
      	  for (cj = 0; cj < child->u.crd.child_count; cj++) { 
      	    if (gch[ci][cj] != NORM_FALSE) {
      	      subresult = red_bop(OR, subresult, crd_one_constraint(
      	        gch[ci][cj], child->var_index, gch_ub[ci][cj]
      	      ) ); 
            } 
          }
          if (subresult != NORM_FALSE) { 
      	    result = red_bop(OR, result, crd_one_constraint( 
      	      subresult, d->var_index, d->u.crd.arc[ci].upper_bound
      	    ) ); 
          } 
        }
      }
    }
    break;
  case TYPE_LAZY_EXP: 
    result = lazy_2_cases(
      rec_merge_zones(d->u.lazy.false_child), 
      rec_merge_zones(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      fchild_stack_push(
        rec_merge_zones(d->u.fdd.arc[ci].child), 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
    } 
    result = fdd_new(d->var_index); 
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      dfchild_stack_push(rec_merge_zones(d->u.dfdd.arc[ci].child), 
	d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
    } 
    result = dfdd_new(d->var_index); 
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ichild_stack_push(rec_merge_zones(d->u.ddd.arc[ci].child), 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      ); 
    } 
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result); 
}
  /* rec_merge_zones() */



struct red_type	*red_merge_zones(struct red_type *d) { 
  return(rec_merge_zones(d)); 
}
  /* red_merge_zones() */ 






  
int	count_hull_normalize = 0; 

struct red_type	*red_hull_normalize(w)
     int	w;
{
  int 			filter;
  struct red_type	*result; 

  /*
  print_cpu_time("Into hull normalization");
  */ 
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED: 
    return(RT[w]); 
  case FLAG_SYSTEM_HYBRID: 
    return(hybrid_normalize(w));
  }
  switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
  case FLAG_NORM_ZONE_NONE:
    break;
    /*
  case FLAG_NORM_MAGNITUDE_WITH_TABLE_LOOKUP:
    RT[w] = red_hull_magnitude_with_table_lookup(w);
    break;
    */
  case FLAG_NORM_ZONE_CLOSURE:
    RT[w] = red_eliminate_simple_negative_cycles(w); 
    RT[w] = red_tight_all_pairs(w);
/*
    fprintf(RED_OUT, "\nI%1d: inside normalization\n", ITERATION_COUNT);
    red_print_graph(RT[w]);
*/
    break;
  case FLAG_NORM_ZONE_CLOSURE_EQ:
    RT[w] = red_tight_all_pairs(w);
    RT[w] = red_eliminate_simple_negative_cycles(w); 
    RT[w] = red_reduce_eq(RT[w]); 
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_magnitude_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = red_merge_zones(result); 
    garbage_collect(FLAG_GC_SILENT);
    break; 
  case FLAG_NORM_ZONE_CLOSURE_REDUCTION:
    for (RT[filter = RT_TOP++] = RT[w], RT[w] = NORM_FALSE; RT[filter] != RT[w]; ) {
      RT[w] = RT[filter];
      RT[filter] = red_tight_DOWNWARD_through_magnitudes(filter);
      garbage_collect(FLAG_GC_SILENT);
    }
    RT_TOP--; /* filter */

    RT[w] = red_eliminate_simple_negative_cycles(w); 
    RT[w] = red_subsume(RT[w]);
/*
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_difference_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);

    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_difference_redundant_differences_MIDDLE(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
*/
    ZONE_PIVOT = 0;
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_magnitude_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
/*
*/
    break;
  case FLAG_NORM_ZONE_MAGNITUDE_REDUCTION:
    /*
       fprintf(RED_OUT, "\n==========================================================================\n");
       fprintf(RED_OUT, "ITERATION %1d: Entering red_magnitude_form()\n", ITERATION_COUNT);
       print_cpu_time("Entering red_magnitude_form()");
       red_size(RT[w], SIZE_REPORT, NULL, NULL);
       red_print_graph(RT[w]);
    */

    RT[w] = red_grow_DOWNWARD(w);
    /*
    RT[w] = red_grow_ARRAY(w);
       RT[w] = red_grow_DOWNWARD_MATCHING(w);
       RT[w] = red_grow_DOWNWARD(w);
    */


       /*
	 fprintf(RED_OUT, "\nITERATION %1d: after growth()\n", ITERATION_COUNT);
	 print_cpu_time("after growth()");
	 red_size(RT[w], SIZE_REPORT, NULL, NULL);
	 red_print_graph(RT[w]);
       */
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_magnitude_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
    /*
       fprintf(RED_OUT, "\nITERATION %1d: Leaving red_magnitude_form()\n", ITERATION_COUNT);
       print_cpu_time("Leaving red_magnitude_form()");
       red_size(RT[w], SIZE_REPORT, NULL, NULL);
       red_print_graph(RT[w]);
    */
    break;
  case	FLAG_NORM_ZONE_MAGNITUDE: 
    /*
       fprintf(RED_OUT, "\n==========================================================================\n");
       fprintf(RED_OUT, "ITERATION %1d: Entering red_magnitude_form()\n", ITERATION_COUNT);
       print_cpu_time("Entering red_magnitude_form()");
       red_size(RT[w], SIZE_REPORT, NULL, NULL);
       red_print_graph(RT[w]);
    */
    RT[w] = red_grow_DOWNWARD(w);
    /*
       fprintf(RED_OUT, "\nITERATION %1d: Leaving red_magnitude_form()\n", ITERATION_COUNT);
       print_cpu_time("Leaving red_magnitude_form()");
       red_size(RT[w], SIZE_REPORT, NULL, NULL);
       red_print_graph(RT[w]);
    */
    break; 
  case FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE: 
    RT[w] = red_grow_DOWNWARD(w);
    /*
    RT[w] = red_grow_ARRAY(w);
       RT[w] = red_grow_DOWNWARD_MATCHING(w);
       RT[w] = red_grow_DOWNWARD(w);
    */


       /*
	 fprintf(RED_OUT, "\nITERATION %1d: after growth()\n", ITERATION_COUNT);
	 print_cpu_time("after growth()");
	 red_size(RT[w], SIZE_REPORT, NULL, NULL);
	 red_print_graph(RT[w]);
       */
/*
    result = rec_tight_magnitudes_DOWNWARD_through_magnitudes(RT[w]);
    RT[w] = result; 
*/
    garbage_collect(FLAG_GC_SILENT); 
    RT[w] = red_eliminate_simple_negative_cycles(w); 
    break; 
  }
  /*
  print_cpu_time("Out of hull normalization");
  fprintf(RED_OUT, "\n");
  */ 
  if (GSTATUS[INDEX_LUB_EXTRAPOLATION] & FLAG_LUB_EXTRAPOLATION) { 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) { 
    case TASK_RISK: 
    case TASK_GOAL: 
    case TASK_SAFETY: 
    case TASK_ZENO: 
    case TASK_DEADLOCK: 
      RT[w] = red_lub_extrapolate(RT[w]); 
  } }
  RT[w] = red_subsume(RT[w]); 
  return(RT[w]); 
}
/* red_hull_normalize() */



struct red_type	*red_hull_test_emptiness(w)
     int	w;
{
  int 			filter;
  struct red_type	*result;
  /*
  print_cpu_time("Into hull normalization");
  */
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID)
    return(hybrid_normalize(w));
  else switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
  case FLAG_NORM_ZONE_NONE:
    for (RT[filter = RT_TOP++] = RT[w], RT[w] = NORM_FALSE; RT[filter] != RT[w]; ) {
      RT[w] = RT[filter];
      RT[filter] = red_tight_all_pairs(filter);
    }
    RT_TOP--; /* filter */
    break;
  case FLAG_NORM_ZONE_CLOSURE:
    RT[w] = red_tight_DOWNWARD_through_magnitudes(w);
/*
    fprintf(RED_OUT, "\nI%1d: inside normalization\n", ITERATION_COUNT);
    red_print_graph(RT[w]);
*/
    break;
  case FLAG_NORM_ZONE_CLOSURE_REDUCTION:
    for (RT[filter = RT_TOP++] = RT[w], RT[w] = NORM_FALSE; RT[filter] != RT[w]; ) {
      RT[w] = RT[filter];
      RT[filter] = red_tight_DOWNWARD_through_magnitudes(filter);
      garbage_collect(FLAG_GC_SILENT);
    }
    RT_TOP--; /* filter */

    RT[w] = red_subsume(RT[w]);

/*
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_difference_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);

    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_difference_redundant_differences_MIDDLE(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
*/
    ZONE_PIVOT = 0;
    ZB_DOWNWARD = CLOCK_POS_INFINITY;
    result = rec_eliminate_magnitude_redundant_differences_DOWNWARD(RT[w]);
    RT[w] = result;
    garbage_collect(FLAG_GC_SILENT);
/*
*/
    break;
  }
  /*
  print_cpu_time("Out of hull normalization");
  fprintf(RED_OUT, "\n");
  */
  return(RT[w]);
}
/* red_hull_test_emptiness() */



// int	count_zs = 0; 
// int	count_zsubsume = 0; 

struct red_type	*rec_zone_subsume(d)
     struct red_type	*d;
{
  int				b, lb, ub, ci, czs;
  struct red_type		*new_child;
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

/*
  czs = ++count_zs; 
  for (; czs == 109; ) ; 
*/
  ce = cache1_check_result_key(OP_ZONE_SUBSUME, d); 
  if (ce->result) { 
/*
    fprintf(RED_OUT, "count_zs = %1d, cached\ninput d:\n", czs); 
    red_print_graph(d); 
    fprintf(RED_OUT, "output d:\n"); 
    red_print_graph(ce->result); 
*/    
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    ce->result = bdd_new(d->var_index, 
      rec_zone_subsume(d->u.bdd.zero_child), 
      rec_zone_subsume(d->u.bdd.one_child)
    ); 
    return(ce->result); 
    break; 

  case TYPE_CRD: 
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_zone_subsume(d->u.crd.arc[ci].child);
      bchild_stack_checkpush(new_child, d->u.crd.arc[ci].upper_bound);
    }

    ce->result = crd_new(d->var_index);
/*
    fprintf(RED_OUT, "count_zs = %1d, crd newed\ninput d:\n", czs); 
    red_print_graph(d); 
    fprintf(RED_OUT, "output d:\n"); 
    red_print_graph(ce->result); 
*/
    return(ce->result); 
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_zone_subsume(d->u.hrd.arc[ci].child);
      hchild_stack_checkpush(new_child, 
			     d->u.hrd.arc[ci].ub_numerator,
			     d->u.hrd.arc[ci].ub_denominator
			     );
    }

    return(ce->result = hrd_new(d->var_index, d->u.hrd.hrd_exp));
    break;

  case TYPE_LAZY_EXP: 
    ce->result = lazy_subtree(
      rec_zone_subsume(d->u.lazy.false_child), 
      rec_zone_subsume(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    return(ce->result); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_zone_subsume(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }
    ce->result = fdd_new(d->var_index);
/*
    fprintf(RED_OUT, "count_zs = %1d, ddd newed\ninput d:\n", czs); 
    red_print_graph(d); 
    fprintf(RED_OUT, "output d:\n"); 
    red_print_graph(ce->result); 
*/
    return(ce->result); 
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_zone_subsume(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }
    ce->result = dfdd_new(d->var_index);
/*
    fprintf(RED_OUT, "count_zs = %1d, ddd newed\ninput d:\n", czs); 
    red_print_graph(d); 
    fprintf(RED_OUT, "output d:\n"); 
    red_print_graph(ce->result); 
*/
    return(ce->result); 
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_zone_subsume(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
				 d->u.ddd.arc[ci].upper_bound
				 );
    }
    ce->result = ddd_new(d->var_index);
/*
    fprintf(RED_OUT, "count_zs = %1d, ddd newed\ninput d:\n", czs); 
    red_print_graph(d); 
    fprintf(RED_OUT, "output d:\n"); 
    red_print_graph(ce->result); 
*/
    return(ce->result); 
  }
}
  /* rec_zone_subsume() */




struct red_type	*red_zone_subsume(d)
     struct red_type	*d;
{
  struct red_type	*result;
  int			old_size;

  if (d == NORM_FALSE)
    return(d);
/*
  fprintf(RED_OUT, 
    "** count_zsubsume = %1d, Entering red_zone_subsume(%x) ****\n", 
    ++count_zsubsume, d 
  ); 
  for (; count_zsubsume ==  692; ); 
*/  
  result = rec_zone_subsume(d);
  return(result);
}
/* red_zone_subsume() */





/**********************************************************************
 *  The following declarations are for the efficient detection of 
 *  easy time-concavities. 
 */
#define	diagonal_index	index1 
#define clk_index	index1
#define diagonal_ub	index2	
#define clk_lb		index2
#define clk_ub		index3  

struct easy_concavity_analysis_type { 
  int				status; 
#define	FLAG_NONTRIVIAL_UB	1
#define	FLAG_NONTRIVIAL_LB	2 

  struct red_type		*easy_convexity, 
				*easy_concavity; 
  struct index_pair_link_type	*shared_diagonal_list;  
  struct index_triple_link_type	*lb_ub_list; 
}; 

struct easy_concavity_arc_type { 
  int					status; 
#define	MASK_AUGMENTED_DIAGONAL_OR_UB_LB	3 
#define	FLAG_NO_AUGMENTATION			0
#define	FLAG_AUGMENTED_DIAGONAL			1
#define	FLAG_AUGMENTED_LB_UB			2 

  struct index_pair_link_type		*augmented_shared_diagonal_list, 
  					*wdg; 
  struct index_triple_link_type		*augmented_lb_ub_list; 
  struct easy_concavity_analysis_type	*child_result; 
}; 


struct easy_concavity_arc_type 	*easy_concavity; 
int				easy_concavity_top=-1; 
int				easy_concavity_limit = 1000; 

inline int	push_easy_concavity_lb_ub(clock_index, lb, ub, result) 
  int					clock_index, lb, ub; 
  struct easy_concavity_analysis_type	*result; 
{ 
  ++easy_concavity_top; 
/*
  fprintf(RED_OUT, "\nEntering push easy concavity lb-ub at %1d\n", 
    easy_concavity_top
  ); 
*/
  if (easy_concavity_limit == easy_concavity_top) { 
  /* If the stack is over the limit, we need to expand it at runtime. */
    struct easy_concavity_arc_type	*nstack; 
    int					i; 
    
    nstack = (struct easy_concavity_arc_type *) 
      malloc(easy_concavity_limit * 2 * 
        sizeof(struct easy_concavity_arc_type)
      ); 
    for (i=0; i < easy_concavity_limit; i++) { 
      nstack[i] = easy_concavity[i]; 
    } 
    free(easy_concavity); 
    easy_concavity = nstack; 
    easy_concavity_limit = easy_concavity_limit * 2; 
    for (; i < easy_concavity_limit; i++) { 
      easy_concavity[i].status = 0; 
      easy_concavity[i].augmented_lb_ub_list = NULL; 
      easy_concavity[i].augmented_shared_diagonal_list = NULL; 
      easy_concavity[i].child_result = NULL; 
    } 
  } 
  easy_concavity[easy_concavity_top].child_result = result; 
  if (   lb <= VAR[CLOCK[clock_index]].U.CLOCK.LB 
      && ub >= VAR[CLOCK[clock_index]].U.CLOCK.UB
      ) { 
  /* Note that in this easy concavity process, 
   * we use VAR[CLOCK[clock_index]].LB and VAR[CLOCK[clock_index]].U.CLOCK.UB 
   * to record the bounds collected in a diagram. 
   * They are no longer the initial values set by varible_fillin().  
   */ 
    easy_concavity[easy_concavity_top].status 
      = (  easy_concavity[easy_concavity_top].status 
         & ~MASK_AUGMENTED_DIAGONAL_OR_UB_LB
         ) 
      | FLAG_NO_AUGMENTATION; 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list 
    = result->lb_ub_list;
    easy_concavity[easy_concavity_top].augmented_shared_diagonal_list 
    = result->shared_diagonal_list;
    return(easy_concavity_top); 
  }
  easy_concavity[easy_concavity_top].status 
  = (  easy_concavity[easy_concavity_top].status 
     & ~MASK_AUGMENTED_DIAGONAL_OR_UB_LB
     ) 
    | FLAG_AUGMENTED_LB_UB; 
  easy_concavity[easy_concavity_top].augmented_lb_ub_list 
    = (struct index_triple_link_type *) 
    malloc(sizeof(struct index_triple_link_type)); 
  easy_concavity[easy_concavity_top]
    .augmented_lb_ub_list->next_index_triple_link 
    = result->lb_ub_list; 
  easy_concavity[easy_concavity_top]
    .augmented_lb_ub_list->clk_index = clock_index; 
  if (lb <= VAR[CLOCK[clock_index]].U.CLOCK.LB) 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list->clk_lb = 0; 
  else 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list->clk_lb = lb; 
  if (ub >= VAR[CLOCK[clock_index]].U.CLOCK.UB) 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list->clk_ub 
      = CLOCK_POS_INFINITY; 
  else 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list->clk_ub = ub; 
  easy_concavity[easy_concavity_top]
    .augmented_shared_diagonal_list = result->shared_diagonal_list; 

  return(easy_concavity_top); 
}
  /* push_easy_concavity_lb_ub() */ 


inline int	push_easy_concavity_diagonal(diagonal_index, ub, result) 
  int					diagonal_index, ub; 
  struct easy_concavity_analysis_type	*result; 
{ 
  ++easy_concavity_top; 
/* 
  fprintf(RED_OUT, "\nEntering push easy concavity diagonal at %1d\n", 
    easy_concavity_top
  ); 
*/
  if (easy_concavity_limit == easy_concavity_top) { 
  /* If the stack is over the limit, we need to expand it at runtime. */
    struct easy_concavity_arc_type	*nstack; 
    int					i; 
    
    nstack = (struct easy_concavity_arc_type *) 
      malloc(easy_concavity_limit * 2 * 
        sizeof(struct easy_concavity_arc_type)
      ); 
    for (i=0; i < easy_concavity_limit; i++) { 
      nstack[i] = easy_concavity[i]; 
    } 
    free(easy_concavity); 
    easy_concavity = nstack; 
    easy_concavity_limit = easy_concavity_limit * 2; 
    for (; i < easy_concavity_limit; i++) { 
      easy_concavity[i].status = 0; 
      easy_concavity[i].augmented_lb_ub_list = NULL; 
      easy_concavity[i].augmented_shared_diagonal_list = NULL; 
      easy_concavity[i].child_result = NULL; 
    } 
  } 
  easy_concavity[easy_concavity_top].child_result = result; 
  if (ub >= CLOCK_POS_INFINITY) {
    easy_concavity[easy_concavity_top].status 
      = (  easy_concavity[easy_concavity_top].status 
         & ~MASK_AUGMENTED_DIAGONAL_OR_UB_LB
         ) 
      | FLAG_NO_AUGMENTATION; 
    easy_concavity[easy_concavity_top].augmented_lb_ub_list 
    = result->lb_ub_list;
    easy_concavity[easy_concavity_top]
    .augmented_shared_diagonal_list = result->shared_diagonal_list;
    return(easy_concavity_top); 
  }
  easy_concavity[easy_concavity_top].status 
  = (  easy_concavity[easy_concavity_top].status 
     & ~MASK_AUGMENTED_DIAGONAL_OR_UB_LB
     ) 
    | FLAG_AUGMENTED_DIAGONAL; 
  easy_concavity[easy_concavity_top].augmented_lb_ub_list 
  = result->lb_ub_list;
  easy_concavity[easy_concavity_top].augmented_shared_diagonal_list 
  = (struct index_pair_link_type *) 
    malloc(sizeof(struct index_pair_link_type)); 
  easy_concavity[easy_concavity_top].augmented_shared_diagonal_list->next_index_pair_link 
  = result->shared_diagonal_list; 
  easy_concavity[easy_concavity_top].augmented_shared_diagonal_list->diagonal_index 
  = diagonal_index; 
  easy_concavity[easy_concavity_top].augmented_shared_diagonal_list->diagonal_ub 
  = ub; 
  return(easy_concavity_top); 
}
  /* push_easy_concavity_diagonal() */ 




inline void	pop_easy_concavity() { 
  switch (easy_concavity[easy_concavity_top].status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) {
  case FLAG_AUGMENTED_LB_UB: 
    free(easy_concavity[easy_concavity_top].augmented_lb_ub_list); 
    break; 
  case FLAG_AUGMENTED_DIAGONAL: 
    free(easy_concavity[easy_concavity_top].augmented_shared_diagonal_list); 
    break; 
  } 
  easy_concavity_top--; 
}
  /* pop_easy_concavity() */ 


inline void 	chunk_pop_easy_concavity(int i) { 
  int	ci; 
  
  if (i >= -1 && i < easy_concavity_top) { 
    for (ci = easy_concavity_top; ci > i; ci--) { 
      switch (easy_concavity[ci].status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) {
      case FLAG_AUGMENTED_LB_UB: 
        free(easy_concavity[ci].augmented_lb_ub_list); 
        break; 
      case FLAG_AUGMENTED_DIAGONAL: 
        free(easy_concavity[ci].augmented_shared_diagonal_list); 
        break; 
      } 
    } 
    easy_concavity_top = i; 
  } 
  else { 
    fprintf(RED_OUT, "Error: illegal chunk_pop stack frame %1d with top=%1d.\n", 
      i, easy_concavity_top
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
}
  /* chunk_pop_easy_concavity() */ 




struct a23tree_type	*easy_concavity_bound_tree; 

inline void	fill_in_chunk_clock_bounds(
  int	expected_clock_index, 
  int	stop_clock_index
) {
  int	ci; 
  
  if (expected_clock_index < 0) 
    for (ci = -1*expected_clock_index; ci < stop_clock_index; ci++) { 
      VAR[CLOCK[ci]].U.CLOCK.LB = 0; 
      VAR[CLOCK[ci]].U.CLOCK.UB = CLOCK_POS_INFINITY; 
    } 
  else { 
    VAR[CLOCK[expected_clock_index]].U.CLOCK.UB = CLOCK_POS_INFINITY; 
    for (ci = expected_clock_index+1; ci < stop_clock_index; ci++) { 
      VAR[CLOCK[ci]].U.CLOCK.LB = 0; 
      VAR[CLOCK[ci]].U.CLOCK.UB = CLOCK_POS_INFINITY; 
    } 
  } 
}
  /* fill_in_chunk_clock_bounds() */  
  
  
  
  
int	rec_comp_path_bounds(r1, r2) 
  struct rec_type	*r1, *r2; 
{ 
  if (r1->redx < r2->redx)   
    return(-1); 
  else if (r1->redx > r2->redx) 
    return(1); 
  else if (r1->redy < r2->redy) 
    return(-1); 
  else 
    return(0); 
} 
  /* rec_comp_path_bounds() */ 
  
  
  
  
void	rec_collect_all_path_clock_bounds(
  struct red_type 	*d, 
  int			expected_clock_index
) { 
  int					ci, cj, c1, c2; 
  struct hrd_exp_type			*he;
  struct crd_child_type			*bc;
  struct hrd_child_type			*hc;
  struct ddd_child_type			*ic;
  struct rec_type			*nrec, *rec;
    
  if (d == NORM_FALSE) 
    return; 

  rec = rec_new(d, expected_clock_index); 
  nrec = (struct rec_type *) add_23tree(
    rec, easy_concavity_bound_tree, 
    rec_comp_path_bounds, rec_free, 
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return; 
  }
  else if (d == NORM_NO_RESTRICTION) { 
    fill_in_chunk_clock_bounds(expected_clock_index, CLOCK_COUNT); 
    return; 
  } 
  
  switch (VAR[d->var_index].TYPE) { 
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0) { 
      fill_in_chunk_clock_bounds(expected_clock_index, c2);  
      if (d->u.crd.arc[d->u.crd.child_count-1].upper_bound
          + VAR[CLOCK[c2]].U.CLOCK.LB > 0
          ) 
        VAR[CLOCK[c2]].U.CLOCK.LB = -1 * d->u.crd.arc[d->u.crd.child_count-1].upper_bound; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	rec_collect_all_path_clock_bounds(d->u.crd.arc[ci].child, c2); 
      } 
    } 
    else if (c2 == 0) { 
      fill_in_chunk_clock_bounds(expected_clock_index, c1); 
      if (d->u.crd.arc[d->u.crd.child_count-1].upper_bound 
            > VAR[CLOCK[c2]].U.CLOCK.UB
          ) 
        VAR[CLOCK[c1]].U.CLOCK.UB = d->u.crd.arc[d->u.crd.child_count-1].upper_bound; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	rec_collect_all_path_clock_bounds(d->u.crd.arc[ci].child, -1*(c1+1)); 
      } 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	rec_collect_all_path_clock_bounds(
      	  d->u.crd.arc[ci].child, expected_clock_index 
      	); 
      } 
    } 
    break; 
  default: 
    fprintf(RED_OUT, 
      "Error: Unexpected data types in collect_all_path_clock_bounds()!\n"  
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
} 
  /* rec_collect_all_path_clock_bounds() */ 
  
  
  

inline void	collect_all_path_clock_bounds(struct red_type *d) { 
  int	i; 
  
  for (i = 0; i < CLOCK_COUNT; i++) { 
    VAR[CLOCK[i]].U.CLOCK.UB = CLOCK_NEG_INFINITY; 
    VAR[CLOCK[i]].U.CLOCK.LB = CLOCK_POS_INFINITY; 
  } 
  init_23tree(&easy_concavity_bound_tree); 
  rec_collect_all_path_clock_bounds(d, -1/* for lowerbound */); 
  free_entire_23tree(easy_concavity_bound_tree, rec_free);
} 
  /* collect_all_path_clock_bounds() */ 
  
  
  


inline struct index_triple_link_type	*merge_lb_ub_lists(
  struct index_triple_link_type	*list1, 
  struct index_triple_link_type	*list2
) { 
  struct index_triple_link_type	dummy_head, *p, *c, *n; 
  if (list2 == NULL) 
    return(list1); 
    
  dummy_head.next_index_triple_link = list1; 
  p = &dummy_head; 
  n = list1; 
  for (; n != NULL && list2 != NULL; ) { 
    if (n->clk_index < list2->clk_index) {
      p = n; 
      n = n->next_index_triple_link; 
    } 
    else if (n->clk_index == list2->clk_index) { 
      if (n->clk_ub > list2->clk_ub) 
        n->clk_ub = list2->clk_ub; 
      if (n->clk_lb < list2->clk_lb) 
        n->clk_lb = list2->clk_lb; 
      p = n; 
      n = n->next_index_triple_link; 
      list2 = list2->next_index_triple_link; 
    } 
    else { 
      c = (struct index_triple_link_type *) 
        malloc(sizeof(struct index_triple_link_type)); 
      c->clk_index = list2->clk_index; 
      c->clk_ub = list2->clk_ub; 
      c->clk_lb = list2->clk_lb; 
      p->next_index_triple_link = c; 
      c->next_index_triple_link = n; 
      p = c; 
      list2 = list2->next_index_triple_link; 
    } 
  } 
  for (; list2 != NULL; list2 = list2->next_index_triple_link) { 
    c = (struct index_triple_link_type *) 
      malloc(sizeof(struct index_triple_link_type)); 
    c->clk_index = list2->clk_index; 
    c->clk_ub = list2->clk_ub; 
    c->clk_lb = list2->clk_lb; 
    p->next_index_triple_link = c; 
    p = c; 
  } 
  p->next_index_triple_link = NULL; 
  
  return(dummy_head.next_index_triple_link); 
} 
  /* merge_lb_ub_lists() */ 
  
  


inline void	fill_in_concavity_analysis(
  struct easy_concavity_analysis_type	*result, 
  int					child_start, 
  int					child_stop
) {
  int				ci, flag, md_index, md_ub, count_min; 
  struct index_pair_link_type	dummy_head, *tail, *nd; 
  
  result->lb_ub_list = NULL; 
  result->status = 0; 
  for (ci = child_start; ci <= child_stop; ci++) { 
    result->status = result->status | easy_concavity[ci].child_result->status; 
    result->lb_ub_list = merge_lb_ub_lists(
      result->lb_ub_list, easy_concavity[ci].augmented_lb_ub_list
    ); 
    easy_concavity[ci].wdg 
    = easy_concavity[ci].augmented_shared_diagonal_list; 
    
    switch (easy_concavity[ci].status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) { 
    case FLAG_AUGMENTED_LB_UB: 
      if (easy_concavity[ci].augmented_lb_ub_list->clk_lb > 0) 
        result->status = result->status | FLAG_NONTRIVIAL_LB; 
      if (easy_concavity[ci].augmented_lb_ub_list->clk_ub < CLOCK_POS_INFINITY) 
        result->status = result->status | FLAG_NONTRIVIAL_UB; 
      break; 
    }
  }
  
  tail = &dummy_head; 
  for (flag = TYPE_TRUE; flag; ) { 
    /* First find the minimum diagonal in this round. */ 
    md_index = VARIABLE_COUNT; 
    md_ub = CLOCK_NEG_INFINITY; 
    count_min = 1; 
    for (ci = child_start; ci <= child_stop; ci++) { 
    /* Then we scan through the heads of all children's diagonal lists 
     * for the next . 
     */
      if (easy_concavity[ci].wdg == NULL) { 
      /* There is a child without any more shared diagonals. 
       * This implies that there is no possibility of more shared diagonals 
       * among the children.  
       */
      	tail->next_index_pair_link = NULL; 
      	result->shared_diagonal_list = dummy_head.next_index_pair_link; 
      	return; 
      }
      else if (md_index > easy_concavity[ci].wdg->diagonal_index) { 
        md_index = easy_concavity[ci].wdg->diagonal_index; 
        md_ub = easy_concavity[ci].wdg->diagonal_ub; 
        count_min = 1; 
      } 
      else if (md_index == easy_concavity[ci].wdg->diagonal_index) { 
      	count_min++;  
        if (md_ub < easy_concavity[ci].wdg->diagonal_ub) 
          md_ub = easy_concavity[ci].wdg->diagonal_ub; 
      } 
    } 
    if (   count_min == child_stop-child_start+1
        && md_ub != CLOCK_POS_INFINITY
        ) { 
      nd = (struct index_pair_link_type *) 
      	malloc(sizeof(struct index_pair_link_type)); 
      nd->diagonal_index = md_index; 
      nd->diagonal_ub = md_ub; 
      tail->next_index_pair_link = nd; 
      tail = nd; 
    } 
    for (ci = child_start; ci <= child_stop; ci++) { 
      if (easy_concavity[ci].wdg->diagonal_index == md_index) {
      	easy_concavity[ci].wdg 
      	= easy_concavity[ci].wdg->next_index_pair_link; 
      } 
    }
  }
}
  /* fill_in_concavity_analysis() */ 
  
  


inline int	check_diagonal_conflict(
  int				cub, 
  int				ub, 
  int				clb, 
  int				lb, 
  struct index_pair_link_type	*dlist1, 
  struct index_pair_link_type	*dlist2
) {
  int				dgi1, dgi2, comp; 
  struct index_pair_link_type	*dg1, *dg2; 

  for (dg1 = dlist1, dg2 = dlist2; 
       dg1 != NULL && dg2 != NULL; 
       ) { 
    dgi1 = dlist1->diagonal_index; 
    dgi2 = dlist2->diagonal_index; 
    if (   VAR[dgi1].U.CRD.CLOCK1 == VAR[dgi2].U.CRD.CLOCK2
        && VAR[dgi1].U.CRD.CLOCK2 == VAR[dgi2].U.CRD.CLOCK1
        ) { 
      if ((comp = dg1->diagonal_ub + dg2->diagonal_ub) < 0) { 
      	return(TYPE_TRUE); 
      } 
      else if (comp == 0) { 
      	if (clb == 0 || cub == 0) 
      	  continue; 
      	else if (   clb == VAR[dgi1].U.CRD.CLOCK1 
      	         && cub == VAR[dgi1].U.CRD.CLOCK2 
      	         && ub - lb + dg1->diagonal_ub < 0 
      	         ) 
      	  return(TYPE_TRUE); 
      	else if (   clb == VAR[dgi2].U.CRD.CLOCK1 
      	         && cub == VAR[dgi2].U.CRD.CLOCK2 
      	         && ub - lb + dg1->diagonal_ub < 0 
      	         ) 
      	  return(TYPE_TRUE); 
      } 
    } 
    if (dgi1 <= dgi2) 
      dg1 = dg1->next_index_pair_link; 
    else 
      dg2 = dg2->next_index_pair_link; 
  } 
  return(TYPE_FALSE); 
}
  /* check_diagonal_conflict() */ 






inline int	easy_concavity_check(int child_start, int child_stop) {
  int				ci, cj; 
  struct index_triple_link_type	*clb, *cub; 
  
  /* How should preceed ? 
   * In the following, we have four cases and each with 
   * some conditions for easy-concavity. 
   * We check if there are such ch1, ch2, and gc. 
   * If there is, then the whole d is easy-concave.  
   * Otherwise, the whole d is partitioned to easy-concave and 
   * easy-convex. 
   * 
   * A major challenge is the conflicting diagonals. 
   * We may have x-y <= c and -x+y<=-c.  
   * If x-y=c is true, then only one of x and y can participate in 
   * the other conditions.  
   */ 
  /* We check if there is any concavity between two children. 
   */ 
  for (ci = child_start; ci <= child_stop; ci++) { 
    if (easy_concavity[ci].child_result->status & FLAG_NONTRIVIAL_LB) { 
      for (cj = child_start; cj <= child_stop; cj++) { 
        if (ci == cj) 
          continue; 
        if (easy_concavity[cj].child_result->status & FLAG_NONTRIVIAL_UB) {
          for (clb = easy_concavity[ci].augmented_lb_ub_list; 
               clb; 
               clb = clb->next_index_triple_link 
               ) { 
            if (clb->clk_lb <= VAR[CLOCK[clb->clk_index]].U.CLOCK.LB) 
              continue; 
              
            for (cub = easy_concavity[cj].augmented_lb_ub_list; 
                 cub; 
                 cub = cub->next_index_triple_link 
                 ) { 
              if (cub->clk_ub >= VAR[CLOCK[cub->clk_index]].U.CLOCK.UB) 
                continue; 
              if (!check_diagonal_conflict( 
      	            cub->clk_index, cub->clk_ub, 
      	            clb->clk_index, clb->clk_lb, 
      	            easy_concavity[ci].augmented_shared_diagonal_list, 
      	            easy_concavity[cj].augmented_shared_diagonal_list 
      	          ) ) 
      	        return(TYPE_TRUE); 
      	    }
      	  } 
      	}
      	else if (   (easy_concavity[cj].status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) 
      	             == FLAG_AUGMENTED_LB_UB 
      	         && (cub = easy_concavity[cj].augmented_lb_ub_list)->clk_ub 
      	            < CLOCK_POS_INFINITY
      	         ) { 
          for (clb = easy_concavity[ci].augmented_lb_ub_list; 
               clb; 
               clb = clb->next_index_triple_link
               ) { 
            if (clb->clk_lb <= 0) 
              continue; 
              
            if (!check_diagonal_conflict( 
      	          cub->clk_index, cub->clk_ub, 
      	          clb->clk_index, clb->clk_lb, 
      	          easy_concavity[ci].augmented_shared_diagonal_list, 
      	          easy_concavity[cj].augmented_shared_diagonal_list 
      	        ) ) 
      	      return(TYPE_TRUE); 
      	  }       	  	
      	} 
      }
    }
    else if (   (easy_concavity[ci].status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) 
                 == FLAG_AUGMENTED_LB_UB 
      	     && (clb=easy_concavity[ci].augmented_lb_ub_list)->clk_lb < 0
      	     ) { 
      for (cj = child_start; cj <= child_stop; cj++) { 
        if (ci == cj) 
          continue; 
        if (easy_concavity[cj].child_result->status & FLAG_NONTRIVIAL_UB) {
          for (cub = easy_concavity[cj].augmented_lb_ub_list; 
               cub; 
               cub = cub->next_index_triple_link 
               ) { 
            if (cub->clk_ub < CLOCK_POS_INFINITY) 
              continue; 
            if (!check_diagonal_conflict( 
      	          cub->clk_index, cub->clk_ub, 
      	          clb->clk_index, clb->clk_lb, 
      	          easy_concavity[ci].augmented_shared_diagonal_list, 
      	          easy_concavity[cj].augmented_shared_diagonal_list 
      	        ) ) 
      	      return(TYPE_TRUE); 
      	  } 
      	}
      	else if (   (easy_concavity[cj].child_result->status & MASK_AUGMENTED_DIAGONAL_OR_UB_LB) 
      	             == FLAG_AUGMENTED_LB_UB 
      	         && (cub = easy_concavity[cj].augmented_lb_ub_list)->clk_ub 
      	            < CLOCK_POS_INFINITY
      	         ) { 
          if (!check_diagonal_conflict( 
      	        cub->clk_index, cub->clk_ub, 
      	        clb->clk_index, clb->clk_lb, 
      	        easy_concavity[ci].augmented_shared_diagonal_list, 
      	        easy_concavity[cj].augmented_shared_diagonal_list 
      	      ) ) 
      	    return(TYPE_TRUE); 
      	} 
      }    	
    }  
  }
  return(TYPE_FALSE); 
}
  /* easy_concavity_check() */ 
  
  

inline void	split_convexities_concavities(
  struct easy_concavity_analysis_type	*result, 
  struct red_type			*d, 
  int					child_start, 
  int					child_stop
) {
  int			c1, c2, ci, cj; 
  struct red_type	*ch, *ecave, *evex, *gecave, *gevex; 
  
  c1 = VAR[d->var_index].U.CRD.CLOCK1; 
  c2 = VAR[d->var_index].U.CRD.CLOCK2; 
  for (; child_start <= child_stop;) { 
    /* We first collect all the lb and ub and the shared diagonal bounds 
     * of the children. 
     * We push all such result in stack easy_concavity[].  
     */ 
    if (c1 == 0) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	ch = d->u.crd.arc[ci].child; 
      	if (   VAR[ch->var_index].TYPE == TYPE_CRD
      	    && VAR[ch->var_index].U.CRD.CLOCK1 == c2 
      	    && VAR[ch->var_index].U.CRD.CLOCK2 == c1
      	    ) { 
      	  ecave = NORM_FALSE; 
      	  evex = NORM_FALSE;  
      	  for (cj = 0; cj < ch->u.crd.child_count; cj++, child_start++) { 
            gecave = crd_one_constraint(
              easy_concavity[child_start].child_result->easy_concavity, 
              ch->var_index, 
              ch->u.crd.arc[cj].upper_bound
            ); 
            ecave = red_bop(OR, ecave, gecave); 
            gevex = crd_one_constraint(
              easy_concavity[child_start].child_result->easy_convexity, 
              ch->var_index, 
              ch->u.crd.arc[cj].upper_bound
            ); 
            evex = red_bop(OR, evex, gevex); 
          }
          ecave = crd_one_constraint(ecave, 
            d->var_index, 
            d->u.crd.arc[ci].upper_bound
          ); 
          result->easy_concavity = red_bop(OR, result->easy_concavity, ecave); 
          evex = crd_one_constraint(evex, 
            d->var_index, 
            d->u.crd.arc[ci].upper_bound
          ); 
          result->easy_convexity = red_bop(OR, result->easy_convexity, evex); 
      	} 
      	else { 
          ecave = crd_one_constraint(
          easy_concavity[child_start].child_result->easy_concavity, 
            d->var_index, 
            d->u.crd.arc[ci].upper_bound
          ); 
          result->easy_concavity = red_bop(OR, result->easy_concavity, ecave); 
          evex = crd_one_constraint(
            easy_concavity[child_start].child_result->easy_convexity, 
            d->var_index, 
            d->u.crd.arc[ci].upper_bound
          ); 
          result->easy_convexity = red_bop(OR, result->easy_convexity, evex); 
          child_start++; 
      	} 
      } 
    }
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        ecave = crd_one_constraint(
        easy_concavity[child_start].child_result->easy_concavity, 
          d->var_index, 
          d->u.crd.arc[ci].upper_bound
        ); 
        result->easy_concavity = red_bop(OR, result->easy_concavity, ecave); 
        evex = crd_one_constraint(
          easy_concavity[child_start].child_result->easy_convexity, 
          d->var_index, 
          d->u.crd.arc[ci].upper_bound
        ); 
        result->easy_convexity = red_bop(OR, result->easy_convexity, evex); 
        child_start++; 
      } 
    } 
  }    	
}
  /* split_convexities_concavities() */  




void	rec_easy_concavity_analysis_free(r) 
  struct rec_type	*r; 
{ 
  struct index_pair_link_type		*p1, *p2; 
  struct index_triple_link_type		*t1, *t2; 
  struct easy_concavity_analysis_type	*e; 

  rec_count--;

/*
  if (test_rec) {
    fprintf(RED_OUT, "??????????rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "----------rec=%1x freed with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, rec->redx, rec->redy
	    );
    fflush(RED_OUT);
    test_rec = NULL;
  }
*/
  if (rec_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  e = (struct easy_concavity_analysis_type *) r->result; 
  for (t1 = e->lb_ub_list; t1; ) { 
    t2 = t1; 
    t1 = t1->next_index_triple_link; 
    free(t2); 	
  } 
  for (p1 = e->shared_diagonal_list; p1; ) { 
    p2 = p1; 
    p1 = p1->next_index_pair_link; 
    free(p2); 	
  } 
  free(e); 
  free(r); 
} 
  /* rec_easy_concavity_analysis_free() */ 
  
  


struct a23tree_type	*easy_concavity_tree; 

struct easy_concavity_analysis_type	*rec_easy_concavity_analysis(
     struct red_type	*d, 
     int 		parent_type
) {
  int					ci, cj, c1, c2, vi; 
  int					child_start, child_stop; 
  struct red_type			*evex, *ecave, *ch;
  struct hrd_exp_type			*he;
  struct crd_child_type			*bc;
  struct hrd_child_type			*hc;
  struct ddd_child_type			*ic;
  struct rec_type			*nrec, *rec;
  struct easy_concavity_analysis_type	*child, *result; 

  rec = rec_new(d, (struct red_type *) parent_type); 
  nrec = (struct rec_type *) add_23tree(
    rec, easy_concavity_tree, 
    rec_comp, rec_free,
    rec_nop, rec_parent_set, rec_print
  ); 
  if (rec != nrec) { 
    return((struct easy_concavity_analysis_type *) nrec->result); 
  }

  result = (struct easy_concavity_analysis_type *) 
    malloc(sizeof(struct easy_concavity_analysis_type));
  result->status = 0; 
  result->shared_diagonal_list = NULL; 
  result->lb_ub_list = NULL;
  if (d == NORM_NO_RESTRICTION) { 
    result->easy_convexity = NORM_NO_RESTRICTION;  
    result->easy_concavity = NORM_FALSE; 
    result->shared_diagonal_list = NULL;  
    result->lb_ub_list = NULL; 
    rec->result = (struct red_type *) result; 
    return(result); 
  } 
  else if (d == NORM_FALSE) {
    result->easy_convexity = NORM_FALSE;  
    result->easy_concavity = NORM_FALSE; 
    result->shared_diagonal_list = NULL;  
    result->lb_ub_list = NULL; 
    rec->result = (struct red_type *) result; 
    return(result); 
  }

  result->easy_convexity = NORM_FALSE;  
  result->easy_concavity = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    if (parent_type == TYPE_DISCRETE) { 
      collect_all_path_clock_bounds(d); 
    } 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    child_start = easy_concavity_top+1;  
    /* We first collect all the lb and ub and the shared diagonal bounds 
     * of the children. 
     * We push all such result in stack easy_concavity[].  
     */ 
    if (c1 == 0) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      	ch = d->u.crd.arc[ci].child; 
      	if (   VAR[ch->var_index].TYPE == TYPE_CRD
      	    && VAR[ch->var_index].U.CRD.CLOCK1 == c2 
      	    && VAR[ch->var_index].U.CRD.CLOCK2 == c1
      	    ) { 
      	  for (cj = 0; cj < ch->u.crd.child_count; cj++) { 
/*
      	    fprintf(RED_OUT, 
      	      "\n****[%1d:%1d:%s, two level]*************************************\n", 
      	      CLOCK[c2], c2, VAR[CLOCK[c2]].NAME 
      	    ); 
      	    fprintf(RED_OUT, 
      	      "To push easy concavity lb=%1d, ub=%1d for ci=%1d, cj=%1d at\n", 
      	       
      	      -1 * d->u.crd.arc[ci].upper_bound, 
      	      ch->u.crd.arc[cj].upper_bound, 
      	      ci, cj
      	    ); 
      	    red_print_graph(ch->u.crd.arc[cj].child); 
*/
      	    child_stop = push_easy_concavity_lb_ub( 
      	      c2, 
      	      -1 * d->u.crd.arc[ci].upper_bound, 
      	      ch->u.crd.arc[cj].upper_bound, 
      	      rec_easy_concavity_analysis(ch->u.crd.arc[cj].child, TYPE_CRD)
      	    ); 
      	  } 
      	} 
      	else { 
/*
      	  fprintf(RED_OUT, 
      	    "\n****[%1d:%1d:%s, lb]*************************************\n",
      	    CLOCK[c2], c2, VAR[CLOCK[c2]].NAME  
      	  ); 
      	  fprintf(RED_OUT, 
      	    "To push easy concavity lb=%1d, ub=oo for ci=%1d at\n", 
      	    -1 * d->u.crd.arc[ci].upper_bound, 
      	    ci 
      	  ); 
      	  red_print_graph(d->u.crd.arc[ci].child); 
*/
      	  child_stop = push_easy_concavity_lb_ub( 
      	    c2, 
      	    -1 * d->u.crd.arc[ci].upper_bound, 
      	    CLOCK_POS_INFINITY, 
      	    rec_easy_concavity_analysis(d->u.crd.arc[ci].child, TYPE_CRD)
      	  );       		
      	} 
      } 
    }
    else if (c2 == 0) { 
      child_start = easy_concavity_top+1; 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
/*
        fprintf(RED_OUT, 
          "\n****[%1d:%1d:%s, ub]*************************************\n",
          CLOCK[c1], c1, VAR[CLOCK[c1]].NAME  
        ); 
        fprintf(RED_OUT, 
          "To push easy concavity lb=0, ub=%1d for ci=%1d at\n", 
          d->u.crd.arc[ci].upper_bound, 
          ci 
        ); 
        red_print_graph(d->u.crd.arc[ci].child); 
*/
      	child_stop = push_easy_concavity_lb_ub( 
      	  c1, 
      	  0, 
      	  d->u.crd.arc[ci].upper_bound, 
      	  rec_easy_concavity_analysis(d->u.crd.arc[ci].child, TYPE_CRD)
      	);       		
      } 
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
/*
        fprintf(RED_OUT, 
          "\n****[%1d:(%1d)-(%1d):%s, diagonal]*************************************\n",
          d->var_index, c1, c2, VAR[d->var_index].NAME  
        ); 
        fprintf(RED_OUT, 
          "To push easy concavity ub=%1d for ci=%1d at\n", 
          d->u.crd.arc[ci].upper_bound, 
          ci 
        ); 
        red_print_graph(d->u.crd.arc[ci].child); 
*/
      	child_stop = push_easy_concavity_diagonal( 
      	  d->var_index, 
      	  d->u.crd.arc[ci].upper_bound, 
      	  rec_easy_concavity_analysis(d->u.crd.arc[ci].child, TYPE_CRD)
      	);       		
      } 
    } 
    fill_in_concavity_analysis(
      result, child_start, child_stop
    ); 
    if (easy_concavity_check(child_start, child_stop)) {
      result->easy_concavity = d; 
    } 
    else {
      split_convexities_concavities(result, d, child_start, child_stop); 
    } 
    chunk_pop_easy_concavity(child_start-1); 
    break;
  case TYPE_HRD:
  case TYPE_HDD:
    fprintf(RED_OUT,"ERROR in rec_easy_concavity_analysis()");
    exit(0);
    break;
  
  case TYPE_FLOAT:
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_easy_concavity_analysis(d->u.fdd.arc[ci].child, TYPE_DISCRETE);
      evex = fdd_one_constraint(
        child->easy_convexity, vi, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result->easy_convexity 
      = red_bop(OR, result->easy_convexity, evex);
      ecave = fdd_one_constraint(
        child->easy_concavity, vi, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result->easy_concavity 
      = red_bop(OR, result->easy_concavity, ecave); 
      result->lb_ub_list = NULL; 
      result->shared_diagonal_list = NULL; 
    }
    break;
  
  case TYPE_DOUBLE:
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_easy_concavity_analysis(d->u.dfdd.arc[ci].child, TYPE_DISCRETE);
      evex = dfdd_one_constraint(
        child->easy_convexity, vi, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result->easy_convexity 
      = red_bop(OR, result->easy_convexity, evex);
      ecave = dfdd_one_constraint(
        child->easy_concavity, vi, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result->easy_concavity 
      = red_bop(OR, result->easy_concavity, ecave); 
      result->lb_ub_list = NULL; 
      result->shared_diagonal_list = NULL; 
    }
    break;
  
  default:
    vi = d->var_index; 
    switch (VAR[d->var_index].TYPE) { 
    case TYPE_DISCRETE: 
    case TYPE_POINTER: 
      if (   VAR[d->var_index].PROC_INDEX == 0
          && (VAR[d->var_index].STATUS & FLAG_VAR_AUX_BOTTOM_ORDERING) 
          ) { 
    	vi = VAR[d->var_index].U.DISC.AUX_VI_BOTTOM_ORDERING; 
      } 
      break; 
    } 
  
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      ic = &(d->u.ddd.arc[ci]); 
      child = rec_easy_concavity_analysis(ic->child, TYPE_DISCRETE);
      evex = ddd_one_constraint(
        child->easy_convexity, vi, ic->lower_bound, ic->upper_bound
      ); 
      result->easy_convexity 
      = red_bop(OR, result->easy_convexity, evex);
      ecave = ddd_one_constraint(
        child->easy_concavity, vi, ic->lower_bound, ic->upper_bound
      ); 
      result->easy_concavity 
      = red_bop(OR, result->easy_concavity, ecave); 
      result->lb_ub_list = NULL; 
      result->shared_diagonal_list = NULL; 
    }
  }

  rec->result = (struct red_type *) result; 
  return(result);
}
  /* rec_easy_concavity_analysis() */




int	count_easy_concavity_analysis = 0; 

struct red_type	*easy_concavity_analysis(
  struct red_type	*d 
) { 
  struct easy_concavity_analysis_type	*result; 
  struct red_type			*dresult, *c0, *c1; 
  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    double	start_time_progress_overhead, 
		stop_time_progress_overhead; 
					
    start_time_progress_overhead = red_user_time(); 
    #endif  
  #endif 

  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nEasy concavity %1d: Entering for:\n", 
      ++count_easy_concavity_analysis
    ); 
    red_print_graph(d); 
    #endif 
  #endif 
  
  d = red_bottom_ordering(d); 
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nEasy concavity %1d: after bottom ordering:\n", 
      count_easy_concavity_analysis
    ); 
    red_print_graph(d); 
    #endif 
  #endif 
  
  init_23tree(&easy_concavity_tree); 
  result = rec_easy_concavity_analysis(d, TYPE_DISCRETE); 
  
  c0 = ddd_one_constraint(result->easy_concavity, VI_VALUE, 0, 0); 
  c1 = ddd_one_constraint(result->easy_convexity, VI_VALUE, 1, 1); 
  dresult = red_bop(OR, c0, c1); 
  #ifdef RED_DEBUG_ZONE_MODE 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nEasy concavity %1d: after analysis, concavity:\n", 
      count_easy_concavity_analysis
    ); 
    red_print_graph(c0); 
  
    fprintf(RED_OUT, "\nEasy concavity %1d: after analysis, convexity:\n", 
      count_easy_concavity_analysis
    ); 
    red_print_graph(c1); 
    #endif 
  #endif 
  
  free_entire_23tree(easy_concavity_tree, rec_easy_concavity_analysis_free); 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    stop_time_progress_overhead = red_user_time(); 
    update_time_progress_statistics(
      0.0, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      0.0, 
      0.0, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      "IT %1d, easy concavity analysis", ITERATION_COUNT  
    );
    #endif  
  #endif 
  
  return(dresult); 
} 
  /* easy_concavity_analysis() */  


  
  
  
  
#define shared_concavity	path_convex_start

int	count_ptp = 0; 

void	print_time_path(
  int	path 
) { 
  int	i; 
  
  ++count_ptp;   
  switch (GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS) { 
  case FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with assumed convexities:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 

  case FLAG_TIME_PROGRESS_FULL_FORMULATION: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with full formulation:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_SHARED_CONCAVITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with shared concavity from invariance:\n", 
      count_ptp
    ); 
    break; 
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with ADAPTIVE shared concavity from invariance:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress, the ADAPTIVE shared concavity from invariance:\n", 
      count_ptp
    ); 
    break; 
    
  case FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with split convexities:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with SHARED convexities for:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with SHARED convexities for:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with SHARED convexities for:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
    
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with ADAPTIVE shared easy concavities:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with shared easy concavities:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  case FLAG_TIME_PROGRESS_EASY_CONCAVITY: 
    fprintf(RED_OUT, "\nPTP %1d, path of time progress with easy concavities:\n", 
      count_ptp
    ); 
    red_print_graph(RT[path]); 
    break; 
  default: 
    fprintf(RED_OUT, "Illegal option %x on print time path() to time progress bck.\n", 
      GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* print_time_path() */ 
  
  


struct red_type	*red_time_progress_noxtive_fwd(w)
     int 	w;
{
  int	time, result, urgent;

  /*
  fprintf(RED_OUT, "\nRED size at the start of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  */
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[urgent = RT_TOP++] = red_bop(AND, RT[w], RT[INDEX_URGENT]);
  if (RT[urgent] != NORM_FALSE)
    RT[time = RT_TOP++] = red_bop(SUBTRACT, RT[w], RT[INDEX_URGENT]);
  else 
    RT[time = RT_TOP++] = RT[w]; 

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[time] = hybrid_delta_transitivity_for_umprimed_variables(RT[time], TIME_FORWARD);
    RT[time] = hybrid_delta_extend(RT[time], TIME_FORWARD);
    RT[time] = hybrid_relative_eliminate(RT[time]);

    RT[time] = hybrid_abstract_magnitude(RT[time]);
  }
  else
    RT[time] = red_clock_upper_extend(RT[time]);

  RT[result] = red_bop(OR, RT[time], RT[urgent]);
  RT_TOP = RT_TOP-2; // urgent, time 
  garbage_collect(FLAG_GC_SILENT);
  RT_TOP--;// result 
  return(RT[result]);
  /*
  fprintf(RED_OUT, "\nRED size at the end of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  red_print_graph(RED_NEW_REACHABLE);
  */
}
/* red_time_progress_noxtive_fwd() */



struct red_type	*red_time_progress_special_fwd(w)
     int 	w;
{
  int	time, result, urgent;

  /*
  fprintf(RED_OUT, "\nRED size at the start of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  */
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[urgent = RT_TOP++] = red_bop(AND, RT[w], RT[INDEX_URGENT]);
  if (RT[urgent] != NORM_FALSE)
    RT[time = RT_TOP++] = red_bop(SUBTRACT, RT[w], RT[INDEX_URGENT]);
  else 
    RT[time = RT_TOP++] = RT[w]; 

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[result] = hybrid_time_progress(time, REFINED_GLOBAL_INVARIANCE, TIME_FORWARD);
  }
  else {
    switch (GSTATUS[INDEX_NORM_ZONE] & MASK_NORM_ZONE) {
    case FLAG_NORM_ZONE_CLOSURE_PROPAGATE:
      RT[result] = RT[time]; 
      break;
    case FLAG_NORM_ZONE_CLOSURE_EQ:
      ZB_DOWNWARD = CLOCK_POS_INFINITY;
      RT[result] = rec_tight_differences_DOWNWARD_through_magnitudes(RT[time]);
      garbage_collect(FLAG_GC_SILENT);
      break;
    default:
      RT[result] = RED_BYPASS_FWD(time, 0);
    }
    RT[result] = red_clock_upper_extend(RT[result]);
  }

  RT[result] = red_bop(OR, RT[result], RT[urgent]);
  RT_TOP = RT_TOP-2; // time, urgent 
  garbage_collect(FLAG_GC_SILENT);
  RT_TOP--; // result 
  return(RT[result]);
  /*
  fprintf(RED_OUT, "\nRED size at the end of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  red_print_graph(RED_NEW_REACHABLE);
  */
}
/* red_time_progress_special_fwd() */





struct red_type	*red_time_progress_fwd(
	int	w, 
	int	path
	)
//      int 	w;
{
  int	general, result, time, urgent;

  /*
  fprintf(RED_OUT, "\nRED size at the start of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  */
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[urgent = RT_TOP++] = red_bop(AND, RT[w], RT[INDEX_URGENT]);
  if (RT[urgent] != NORM_FALSE)
    RT[time = RT_TOP++] = red_bop(SUBTRACT, RT[w], RT[INDEX_URGENT]);
  else 
    RT[time = RT_TOP++] = RT[w]; 
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[time] = hybrid_time_progress(time, path, TIME_FORWARD);
    RT[result] = red_bop(OR, RT[time], RT[urgent]);
    RT_TOP = RT_TOP-2; // time, urgent 
    garbage_collect(FLAG_GC_SILENT);
    RT_TOP--; // result 
    return(RT[result]);
  }
  RT[time] = RED_BYPASS_FWD(time, 0);
  RT[time] = red_clock_upper_extend(RT[time]);
/*
  fprintf(RED_OUT, "to be finished.\n"); 
  red_print_graph(RED_OUT); 
  exit(0); 
*/
  RT[result] = red_bop(OR, RT[time], RT[urgent]);
  RT_TOP = RT_TOP-2; /* time, urgent */
  garbage_collect(FLAG_GC_SILENT);
  
  RT[result] = red_bop(AND, RT[result], RT[path]); 
  RT_TOP--; // result 
  
  return(RT[result]);
  /*
  fprintf(RED_OUT, "\nRED size at the end of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  red_print_graph(RED_NEW_REACHABLE);
  */
}
/* red_time_progress_fwd() */





struct red_type	*red_time_progress_noxtive_bck(w)
     int 	w;
{
  int	time, result, urgent;

  /*
  fprintf(RED_OUT, "\nRED size at the start of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  */
  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[urgent = RT_TOP++] = red_bop(AND, RT[w], RT[INDEX_URGENT]);
  if (RT[urgent] != NORM_FALSE)
    RT[time = RT_TOP++] = red_bop(SUBTRACT, RT[w], RT[INDEX_URGENT]);
  else 
    RT[time = RT_TOP++] = RT[w]; 

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[time] = hybrid_delta_transitivity_for_umprimed_variables(
      RT[time], TIME_BACKWARD
    );
    RT[time] = hybrid_delta_extend(RT[time], TIME_BACKWARD);
    RT[time] = hybrid_relative_eliminate(RT[time]);
    RT[time] = hybrid_abstract_magnitude(RT[time]);
  }
  else
    RT[time] = red_clock_noxtive_lower_extend(RT[time]);

  RT[result] = red_bop(OR, RT[time], RT[urgent]);
  RT_TOP = RT_TOP-2; /* time, urgent */
  garbage_collect(FLAG_GC_SILENT);
  RT_TOP--; // result 
  
  return(RT[result]);
  /*
  fprintf(RED_OUT, "\nRED size at the end of red_time saturate at iteration %1d\n", ITERATION_COUNT);
  red_size(RED_NEW_REACHABLE, SIZE_REPORT, NULL, NULL);
  print_cpu_time();
  red_print_graph(RED_NEW_REACHABLE);
  */
}
/* red_time_progress_noxtive_bck() */







/*******************************************************
 * This following procedure must take care of the issue that 
 * RT[w] \cup RT[path] must be used as the path condition.   
 */
  


#ifdef RED_DEBUG_ZONE_MODE 
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
  int	count_tpb_cvx = 0; 
  #endif 
#endif 
  

struct red_type	*red_time_progress_bck_convex(w, path) 
	int	w, path; 
{ 
  int	flag_copath, result, step, new_path; 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    ++count_tpb_cvx; 
    #endif 
  #endif 
  
  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_BRANCHING_BISIM_CHECKING:  
  case TASK_BRANCHING_SIM_CHECKING: 
    if (GSTATUS[INDEX_GFP] & FLAG_IN_GAME_GFP)
      if (   RT[path] == NORM_NO_RESTRICTION
          || RT[path] == RT[DECLARED_GLOBAL_INVARIANCE]
          || RT[path] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
          ) {
        flag_copath = TYPE_FALSE; 
        new_path = INDEX_GAME_INVARIANCE_WITH_EQUALITIES; 
      }
      else {
        flag_copath = TYPE_TRUE; 
        RT[new_path = RT_TOP++] = red_bop(OR, RT[path], RT[w]); 
      } 
    else if (   RT[path] == NORM_NO_RESTRICTION
             || RT[path] == RT[DECLARED_GLOBAL_INVARIANCE]
             || RT[path] == RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]] 
             || RT[path] == RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]] 
             ) { 
      flag_copath = TYPE_FALSE; 
      new_path = path; 
    } 
    else { 
      flag_copath = TYPE_TRUE; 
      RT[new_path = RT_TOP++] = red_bop(OR, RT[path], RT[w]); 
    } 
    break; 
  default: 
    if (   RT[path] == NORM_NO_RESTRICTION
        || RT[path] == RT[DECLARED_GLOBAL_INVARIANCE]
        || RT[path] == RT[REFINED_GLOBAL_INVARIANCE]
        ) { 
      flag_copath = TYPE_FALSE; 
      new_path = REFINED_GLOBAL_INVARIANCE; 
    } 
    else { 
      flag_copath = TYPE_TRUE; 
      RT[new_path = RT_TOP++] = red_bop(OR, RT[path], RT[w]); 
  } }
      
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX
      step = 0; 
      fprintf(RED_OUT, "\nTPCv %1d:%1d, convex time progress for RT[w=%1d]:\n", 
        count_tpb_cvx, ++step, 
        w
      ); 
      red_print_graph(RT[w]); 
      fprintf(RED_OUT, "\nTPCv %1d:%1d, convex time progress for RT[path=%1d]:\n", 
        count_tpb_cvx, ++step, 
        path
      ); 
      red_print_graph(RT[path]); 
      #endif 
    #endif 
  #endif 
  
  RT[result = RT_TOP++] = RT[w]; 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX
      fprintf(RED_OUT, "\nTPCv %1d:%1d, conjuncting RT[w=%1d] and RT[path=%1d]:\n", 
        count_tpb_cvx, ++step, 
        w, path 
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 
  #endif 
  
  RT[result] = RED_BYPASS_BCK(result, 0); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX
      fprintf(RED_OUT, "\nTPCv %1d:%1d, bypassing zero for RT[result=%1d]:\n", 
        count_tpb_cvx, ++step, 
        result  
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 
  #endif 
  /* Note that now the following procedure also have to remove 
   * all the annoations added in by red_annotate_clock_upper_deltap() 
   */
  RT[result] = red_clock_lower_extend(RT[result]); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX
      fprintf(RED_OUT, "\nTPCv %1d:%1d, LB extension for RT[result=%1d]:\n", 
        count_tpb_cvx, ++step, 
        result  
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 
  #endif 

  RT[result] = red_bop(AND, RT[result], RT[new_path]); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX
      fprintf(RED_OUT, "\nTPCv %1d:%1d, conjuncting with RT[path=%1d]:\n", 
        count_tpb_cvx, ++step, 
        path 
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 
  #endif 
  
  if (flag_copath) 
    RT_TOP--; // new_path 
  RT_TOP--; // result 
  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    #endif 
  #endif 
  return(RT[result]); 
}
  /* red_time_progress_bck_convex() */ 







int	INDEX_AMOUNT_PROGRESS; 

// int	count_rec_time_progress_by_amount = 0; 

struct red_type	*rec_time_progress_by_amount(d) 
     struct red_type	*d; 
{
  int				b, b1, b2, ci, c1, c2, 
				old_bound, old_c1_bound, old_c2_bound; 
  struct red_type		*result, *child, *grown_child; 
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    return(d); 
  
  ce = cache2_check_result_key(OP_TIME_PROGRESS_BY_AMOUNT, d, 
    (struct red_type *) INDEX_AMOUNT_PROGRESS
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    c1 = VAR[d->var_index].U.CRD.CLOCK1; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (c1 == 0) {
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        child = rec_time_progress_by_amount(d->u.crd.arc[ci].child);   
        child = crd_one_constraint(child, ZONE[INDEX_AMOUNT_PROGRESS][c2], d->u.crd.arc[ci].upper_bound); 
        result = red_bop(OR, result, child); 
      } 
    }
    else if (c2 == 0) { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        child = rec_time_progress_by_amount(d->u.crd.arc[ci].child);   
        child = crd_one_constraint(child, ZONE[c1][INDEX_AMOUNT_PROGRESS], d->u.crd.arc[ci].upper_bound); 
        result = red_bop(OR, result, child); 
      }
    } 
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        child = rec_time_progress_by_amount(d->u.crd.arc[ci].child);   
        child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
        result = red_bop(OR, result, child); 
      }
    } 
    break; 
  case TYPE_FLOAT: 
/*
    fprintf(RED_OUT, "\nrec time progress by amount %1d, %1d:%s\n", 
      ++count_rec_time_progress_by_amount, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_time_progress_by_amount(d->u.fdd.arc[ci].child); 
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE: 
/*
    fprintf(RED_OUT, "\nrec time progress by amount %1d, %1d:%s\n", 
      ++count_rec_time_progress_by_amount, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_time_progress_by_amount(d->u.dfdd.arc[ci].child); 
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default: 
/*
    fprintf(RED_OUT, "\nrec time progress by amount %1d, %1d:%s\n", 
      ++count_rec_time_progress_by_amount, 
      d->var_index, VAR[d->var_index].NAME
    ); 
    fflush(RED_OUT); 
*/
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_time_progress_by_amount(d->u.ddd.arc[ci].child); 
      child = ddd_one_constraint(child, d->var_index, d->u.ddd.arc[ci].lower_bound, 
				      d->u.ddd.arc[ci].upper_bound
				      ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_time_progress_by_amount() */ 



struct red_type	*red_time_progress_by_amount(d, index_amount) 
	struct red_type	*d; 
	int		index_amount; 
{ 
  struct red_type	*result; 

  if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
         != FLAG_SYSTEM_TIMED
      || d == NORM_FALSE
      ) 
    return(d); 
    
  /* 
  print_cpu_time("Entering red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */  
  switch (index_amount) {
  case DELTA: 
    INDEX_AMOUNT_PROGRESS = NEG_DELTA; 
    break; 
  case DELTAP: 
    INDEX_AMOUNT_PROGRESS = NEG_DELTAP; 
    break; 
  case NEG_DELTA: 
    INDEX_AMOUNT_PROGRESS = DELTA; 
    break; 
  case NEG_DELTAP: 
    INDEX_AMOUNT_PROGRESS = DELTAP; 
    break; 
  } 
    
  result = rec_time_progress_by_amount(d); 
  switch (INDEX_AMOUNT_PROGRESS) {
  case DELTA: 
  case DELTAP: 
    result = crd_one_constraint(result, ZONE[0][INDEX_AMOUNT_PROGRESS], 0); 
    break; 
  case NEG_DELTA: 
  case NEG_DELTAP: 
    result = crd_one_constraint(result, ZONE[INDEX_AMOUNT_PROGRESS][0], 0); 
    break; 
  } 
   
  /* 
  print_cpu_time("Leaving red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */ 
  return(result); 	
}
  /* red_time_progress_by_amount() */ 
  


#ifdef RED_DEBUG_ZONE_MODE 
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
  int	count_ext_cv_bck = 0; 
  #endif 
#endif 

struct red_type	*red_extract_concavity_bck(int path) { 
  int			mid, step; 
  struct red_type	*conj; 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED: 
    return(NORM_FALSE); 
  case FLAG_SYSTEM_HYBRID: 
    fprintf(RED_OUT, 
      "Sorry that we have not implemented concavity extraction\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    exit(0); 
  } 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    ++count_ext_cv_bck; 
    step = 0; 
    fprintf(RED_OUT, "\n\nExCv %1d:%1d for RT[path=%1d]:\n", 
      count_ext_cv_bck, ++step, path
    ); 
    red_print_graph(RT[path]); 
    #endif 
  #endif 
  
  RT[mid = RT_TOP++] = red_complement(RT[path]); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, complementing path for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = red_time_progress_by_amount(RT[mid], NEG_DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, progress by %s for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = crd_one_constraint(RT[mid], ZONE[DELTAP][DELTA], -1); 
  RT[mid] = crd_one_constraint(RT[mid], ZONE[0][DELTAP], 0); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, conjuncting %s<0&&%s<=0 for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, 
        VAR[ZONE[DELTAP][DELTA]].NAME, 
        VAR[ZONE[0][DELTAP]].NAME, 
        mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = red_bypass_DOWNWARD(mid, DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, bypassing %s for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = red_time_clock_eliminate(RT[mid], DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, eliminating clock %s for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  conj = red_time_progress_by_amount(RT[path], NEG_DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, progress by %s for RT[path=%1d]:\n", 
      count_ext_cv_bck, ++step, VAR[CLOCK[NEG_DELTA]].NAME, path
    ); 
    red_print_graph(conj); 
    #endif 
  #endif 
  
  RT[mid] = red_bop(AND, RT[mid], conj); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, 2nd conjunction, RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, mid 
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
    
  RT[mid] = red_bypass_DOWNWARD(mid, DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, bypassing %s for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, 
      VAR[CLOCK[DELTA]].NAME, 
      mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = red_time_clock_eliminate(RT[mid], DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, eliminating %s for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, 
      VAR[CLOCK[DELTA]].NAME, 
      mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT[mid] = red_bop(AND, RT[mid], RT[path]); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    fprintf(RED_OUT, "\nExCv %1d:%1d, conjuncting with input path for RT[mid=%1d]:\n", 
      count_ext_cv_bck, ++step, 
      mid
    ); 
    red_print_graph(RT[mid]); 
    #endif 
  #endif 
  
  RT_TOP--; // mid 
  return(RT[mid]); 
}
  /* red_extract_concavity_bck() */ 
  




int	count_extract_concavity_bck_shared = 0; 

struct red_type	*red_extract_concavity_bck_shared(
  int 	path, 
  int 	shared_comp
) { 
  int			mid, step; 
  struct red_type	*conj; 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED: 
    return(NORM_FALSE); 
  case FLAG_SYSTEM_HYBRID: 
    fprintf(RED_OUT, 
      "Sorry that we have not implemented concavity extraction\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    exit(0); 
  } 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
    ++count_extract_concavity_bck_shared; 
/*
    step = 0; 
    fprintf(RED_OUT, "\n\nExCv I%1d:%1d S:%1d for RT[path=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, path
    ); 
    red_print_graph(RT[path]); 
*/
    #endif 
  #endif 
  
  RT[mid = RT_TOP++] = RT[shared_comp]; 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, complementing path for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_time_progress_by_amount(RT[mid], DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, progress by %s for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = crd_one_constraint(RT[mid], ZONE[NEG_DELTA][NEG_DELTAP], -1); 
  RT[mid] = crd_one_constraint(RT[mid], ZONE[NEG_DELTAP][0], 0); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, conjuncting %s<0&&%s<=0 for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, 
      VAR[ZONE[NEG_DELTA][NEG_DELTAP]].NAME, 
      VAR[ZONE[NEG_DELTAP][0]].NAME, 
      mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_bypass_DOWNWARD(mid, NEG_DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, bypassing %s for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_time_clock_eliminate(RT[mid], NEG_DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, eliminating clock %s for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, VAR[CLOCK[NEG_DELTAP]].NAME, mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  conj = red_time_progress_by_amount(RT[path], DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, progress by %s for RT[path=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, VAR[CLOCK[NEG_DELTA]].NAME, path
    ); 
    red_print_graph(conj); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_bop(AND, RT[mid], conj); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, 2nd conjunction, RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, mid 
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
    
  RT[mid] = red_bypass_DOWNWARD(mid, NEG_DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, bypassing %s for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, 
      VAR[CLOCK[NEG_DELTA]].NAME, 
      mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_time_clock_eliminate(RT[mid], NEG_DELTA); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, eliminating %s for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, 
      VAR[CLOCK[NEG_DELTA]].NAME, 
      mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT[mid] = red_bop(AND, RT[mid], RT[path]); 
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS 
/*
    fprintf(RED_OUT, "\nExCv I%1d:%1d:%1d S, conjuncting with input path for RT[mid=%1d]:\n", 
      ITERATION_COUNT, count_extract_concavity_bck_shared, ++step, 
      mid
    ); 
    red_print_graph(RT[mid]); 
*/
    #endif 
  #endif 
  
  RT_TOP--; // mid 
  return(RT[mid]); 
}
  /* red_extract_concavity_bck_shared() */ 
  




/****************************************************************
 * 
 */
int	check_time_convexity(d)
     struct red_type	*d; 
{
  int	tmp;

  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED: 
    return(FLAG_TCTCTL_SUBFORM); 
  case FLAG_SYSTEM_HYBRID: 
    fprintf(RED_OUT, 
      "Sorry that we have not implemented time convexity checking\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    bk(0); 
  } 
/*
  fprintf(RED_OUT, "count_print_graph = %1d\n", ++count_print_graph); 
  for (; count_print_graph == 119; ) ; 
*/
  RT[tmp = RT_TOP++] = d; 
  RT[tmp] = red_extract_concavity_bck(tmp); 
  RT_TOP--; 
  if (RT[tmp] == NORM_FALSE) 
    return (FLAG_TCTCTL_SUBFORM); 
  else 
    return (TYPE_FALSE); 
}
  /* check_time_convexity() */



  
#ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
int	count_scbck = 0; 
#endif 

struct red_type	*red_shared_concavity_bck(
  int			path, 
  struct red_type	*inv
) { 
  int	wp; 
  
  RT[wp = RT_TOP++] = red_complement(RT[path]); // ....................(a)
    
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nSC_BCK %1d: In time progression after complementing path, RT[wp=%1d]:\n", 
    ++count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is ~phi:\n", 
    count_scbck
  ); 
  red_print_graph(RT[wp]); 
  #endif 
  
  RT[wp] = red_bop(AND, RT[wp], inv); 
  RT[wp] = red_tight_all_pairs(wp); /* red_hull_normalize(wp); */ 

  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nSC_BCK %1d: In time progression after conjuncting negative path with invariance, RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is normalized ~phi:\n", 
    count_scbck 
  ); 
  red_print_graph(RT[wp]); 
  #endif 
  
  RT[wp] = red_time_progress_by_amount(RT[wp], DELTAP); 
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nSC_BCK %1d: In time progression after progrssion by deltap, RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: Now all clocks should have been changed to x-(-t')]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is (~phi)-(-t'):\n", 
    count_scbck 
  ); 
  red_print_graph(RT[wp]); 
  #endif 
  
  RT[wp] = crd_one_constraint(RT[wp], ZONE[NEG_DELTA][NEG_DELTAP], 0); 
  RT[wp] = crd_one_constraint(RT[wp], ZONE[NEG_DELTAP][0], 0); 
    
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nSC_BCK %1d: after conjuncting t'-t=(-t)-(-t')<=0&& (-t')<=0, RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is (-t')<=0&&(-t)-(-t')<=0&&(~phi)-(-t'):\n", 
    count_scbck 
  ); 
  red_print_graph(RT[wp]); 
  #endif 

  RT[wp] = RED_BYPASS_BCK(wp, NEG_DELTAP);  // .....................................(b)
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, "\nSC_BCK %1d: after bypassing on (-t'), RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is NORMALIZED (-t')<=0&&(-t)-(-t')<=0&&(~phi)-(-t'):\n", 
    count_scbck 
  ); 
  red_print_graph(RT[wp]); 
  #endif 

    /* We then have to annotate the upperbound constraints in RT[path] 
     * so that they don't participate in the transitivity through 
     * delta in the second round. 
     */
  RT[wp] = red_time_clock_eliminate(RT[wp], NEG_DELTAP); // ................................(c)
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nSC_BCK %1d: after deactivating (-t'), RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is exists (-t')<=0((-t)-(-t')<=0&&(~phi)-(-t')):\n", 
    count_scbck
  ); 
  red_print_graph(RT[wp]); 
  #endif 

  RT[wp] = red_complement(RT[wp]);  // .......................................(d)
  RT[wp] = red_bop(AND, RT[wp], RT[path]); 
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\n\nSC_BCK %1d: after the 2nd complementing, RT[wp=%1d]:\n", 
    count_scbck, wp
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is ~(exists (-t')<=0((-t)-(-t')<=0&&(~phi)-(-t'))):\n", 
    count_scbck
  ); 
  red_print_graph(RT[wp]); 
  #endif 

  RT[wp] = red_tight_all_pairs(wp);  // .......................................(d)
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\n\nSC_BCK %1d: after the normalization, RT[wp=%1d]:\n", 
    count_scbck, wp 
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is normalized ~(exists (-t')<=0((-t)-(-t')<=0&&(~phi)-(-t'))):\n", 
    count_scbck
  ); 
  red_print_graph(RT[wp]); 
  #endif 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    stop_time_progress_overhead = red_user_time(); 
    update_time_progress_statistics(
      0.0, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      0.0, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      0.0, 
      "IT %1d, push shared concavity", ITERATION_COUNT  
    ); 
    #endif 
  #endif 

  
  RT_TOP--; // wp 
  return(RT[wp]); 
}
  /* red_shared_concavity_bck() */ 
  
  

inline int	check_inv_path_role(
  struct red_type	*dpath, 
  int			flag_roles
) { 
  switch (flag_roles) { 
  case (FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL): 
    if (GSTATUS[INDEX_GFP] & FLAG_IN_GAME_GFP) 
      if (   dpath == RT[INDEX_TRUE] 
          || dpath == RT[DECLARED_GLOBAL_INVARIANCE] 
          || dpath == RT[REFINED_GLOBAL_INVARIANCE] 
          || dpath == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES] 
          ) { 
        return(TYPE_TRUE); 
      }
      else 
        return(TYPE_FALSE); 
    else 
      if (   dpath == RT[INDEX_TRUE] 
          || dpath == RT[DECLARED_GLOBAL_INVARIANCE] 
          || dpath == RT[REFINED_GLOBAL_INVARIANCE] 
          ) { 
        return(TYPE_TRUE); 
      }
      else 
        return(TYPE_FALSE); 
    break; 
  case (FLAG_GAME_ENVR | FLAG_GAME_SPEC): 
    if (dpath == RT[INDEX_TRUE] || dpath == RT[INDEX_GAME_SPEC_INVARIANCE]) { 
      return(TYPE_TRUE); 
    }
    else 
      return(TYPE_FALSE); 
    break; 
  case (FLAG_GAME_ENVR | FLAG_GAME_MODL): 
    if (dpath == RT[INDEX_TRUE] || dpath == RT[INDEX_GAME_MODL_INVARIANCE]) { 
      return(TYPE_TRUE); 
    }
    else 
      return(TYPE_FALSE); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nError: unexpected role %x in check_inv_path_role().\n", 
      flag_roles 
    );
    fflush(RED_OUT); 
    bk(0);  
  } 
} 
  /* check_inv_path() */  
  
  
        
  

/*****************************************************
 * The correctness of the following procedure depends on 
 * the assumption that 
 * RT[w] \subseteq RT[path].  
#define OP_TIME_PATH_ASSUMED_CONVEXITY			(0x14110) 
#define OP_TIME_PATH_FULL_FORMULATION			(0x14120) 
#define	OP_TIME_PATH_SHARED_CONCAVITY			(0x14130)
#define	OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY		(0x14140)
#define	OP_TIME_PATH_SPLIT_CONVEXITIES			(0x14150) 
#define	OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES		(0x14160)	
#define OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES 	(0x14170)
#define OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES 	(0x14180)
#define OP_TIME_PATH_EASY_CONCAVITY				(0x14190) 
#define OP_TIME_PATH_SHARED_EASY_CONCAVITY			(0x141A0) 
#define OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY		(0x141B0) 
 */
 
inline int	opcode_game_time_path(int flag_roles) {
  switch(GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS) { 
  case FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY: 
    return(OP_TIME_PATH_ASSUMED_CONVEXITY | flag_roles); 
    break; 
    
  case FLAG_TIME_PROGRESS_FULL_FORMULATION: 
    return(OP_TIME_PATH_FULL_FORMULATION | flag_roles); 
    break; 
/*    
  case FLAG_TIME_PROGRESS_SHARED_CONCAVITY: 
    return(OP_TIME_PATH_SHARED_CONCAVITY | flag_roles); 
    break; 
*/
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    return(OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY | flag_roles); 
    break; 
/*
  case FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES: 
    return(OP_TIME_PATH_SPLIT_CONVEXITIES | flag_roles);  
    break; 
    
  case FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 
    return(OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES | flag_roles); 	
    break; 
*/    
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 
    return(OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES | flag_roles); 
    break; 
/*
  case FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 
    return(OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES | flag_roles); 
    break; 
*/
/*
  case FLAG_TIME_PROGRESS_EASY_CONCAVITY: 
    return(OP_TIME_PATH_EASY_CONCAVITY | flag_roles);  
    break; 
*/
/*
  case FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY: 
    return(OP_TIME_PATH_SHARED_EASY_CONCAVITY | flag_roles);  
    break; 
*/
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY: 
    return(OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY | flag_roles); 
    break; 
  default: 
    fprintf(RED_OUT, "Illegal option %x on time path to time path analysis.\n", 
      GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
} 
  /* opcode_game_time_path() */ 


  
  


  
inline struct red_type	*fillin_game_shared_concavity_bck(
  int	path, 
  int 	flag_roles
) { 
  int				wp; 
  struct cache1_hash_entry_type	*ce; 

  if (RT[path] == NORM_NO_RESTRICTION || RT[path] == NORM_FALSE)
    return(RT[path]);

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    double	start_time_progress_overhead, stop_time_progress_overhead; 

    start_time_progress_overhead = red_user_time(); 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  ++count_scbck; 
  #endif 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_HYBRID: 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    fprintf(RED_OUT, 
      "SC_BCK %1d, Sorry that we have not done backward shared concavity pushing\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    fflush(RED_OUT); 
    #endif 
    exit(0); 
  case FLAG_SYSTEM_UNTIMED: 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    fprintf(RED_OUT, 
      "SC_BCK %1d, It is weird to do time progression for untimed systems.\n", 
      ++count_scbck
    ); 
    fflush(RED_OUT); 
    #endif 
    return (RT[path]); 
    break; 
  }
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, "\n**********************************************************\n"); 
  fprintf(RED_OUT, 
    "SC_BCK %1d, We want to calculate ~(exists t'>=0(t'<=t&&(~phi)+t')):\n", 
    count_scbck
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is ~(exists (-t')<=0((-t)-(-t')<=0&&(~phi)-(-t'))):\n", 
    count_scbck 
  ); 
  #endif 
   
  ce = cache1_check_result_key(
    opcode_game_time_path(flag_roles), RT[path]
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (flag_roles) { 
  case (FLAG_GAME_SPEC | FLAG_GAME_MODL | FLAG_GAME_ENVR): 
    ce->result = red_shared_concavity_bck(
      path, RT[DECLARED_GLOBAL_INVARIANCE]
    ); 
    break; 
  case (FLAG_GAME_SPEC | FLAG_GAME_ENVR): 
    ce->result = red_shared_concavity_bck(
      path, 
      RT[INDEX_GAME_SPEC_INVARIANCE]
    ); 
    break; 
  case (FLAG_GAME_MODL | FLAG_GAME_ENVR): 
    ce->result = red_shared_concavity_bck(
      path, 
      RT[INDEX_GAME_MODL_INVARIANCE]
    ); 
    break; 
  }
  return (ce->result); 
} 
  /* fillin_game_shared_concavity_bck() */ 
  




  
inline struct red_type	*fillin_game_easy_concavity_analysis(
  int	path, 
  int 	flag_roles
) { 
  int				wp; 
  struct cache1_hash_entry_type	*ce; 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    double	start_time_progress_overhead, stop_time_progress_overhead; 

    start_time_progress_overhead = red_user_time(); 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  ++count_scbck; 
  #endif 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_HYBRID: 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    fprintf(RED_OUT, 
      "SC_BCK %1d, Sorry that we have not done backward shared concavity pushing\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    fflush(RED_OUT); 
    #endif 
    exit(0); 
  case FLAG_SYSTEM_UNTIMED: 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    fprintf(RED_OUT, 
      "SC_BCK %1d, It is weird to do time progression for untimed systems.\n", 
      ++count_scbck
    ); 
    fflush(RED_OUT); 
    #endif 
    return; 
    break; 
  }
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, "\n**********************************************************\n"); 
  fprintf(RED_OUT, 
    "SC_BCK %1d, We want to calculate ~(exists t'>=0(t'<=t&&(~phi)+t')):\n", 
    count_scbck
  ); 
  fprintf(RED_OUT, 
    "SC_BCK %1d: That is ~(exists (-t')<=0((-t)-(-t')<=0&&(~phi)-(-t'))):\n", 
    count_scbck 
  ); 
  #endif 
   
  ce = cache1_check_result_key(opcode_game_time_path(flag_roles), RT[path]); 
  if (ce->result) {
    return(ce->result); 
  } 

  ce->result = easy_concavity_analysis(RT[path]); 
  return (ce->result); 
} 
  /* fillin_game_easy_concavity_analysis() */ 
  







int	count_split_convexities_bck = 0; 

struct red_type	*red_split_convexities_bck(
  int	path
) { 
  int			i, orig_rttop, comp, cvx_index, result; 
  struct red_type	*cvx, *conj; 
  
  // An exception handling. 
  if (RT[path] == NORM_FALSE) { 
    return (RT[path]); 
  } 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_UNTIMED: 
    return (RT[path]); 
  case FLAG_SYSTEM_HYBRID: 
    fprintf(RED_OUT, 
      "Sorry that we have not implemented backward convexity splitting\n"
    ); 
    fprintf(RED_OUT, "  for hybrid systems.\n"); 
    exit(0); 
  } 

  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  print_cpu_time("\nsplit %d, entering split convexities bck.\n", 
    ++count_split_convexities_bck
  ); 
  #endif 

  orig_rttop = RT_TOP; 
  RT[path] = red_hull_normalize(path); 
  if (  GSTATUS[INDEX_TIME_PROGRESS] 
      & FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS
      ) { 
    RT[comp = RT_TOP++] = red_complement(RT[path]); 
    RT[i = RT_TOP++] = RT[path]; 
    for (; TYPE_TRUE; ) { 
      cvx = red_extract_concavity_bck_shared(i, comp); 
      RT[i = RT_TOP++] = red_bop(AND, RT[path], cvx); 
      RT[i] = red_hull_normalize(i); 
      if (RT[i] == NORM_FALSE) { 
        RT_TOP--; // i, the last one is false. 
// To avoid the undesirable side-effect, we have removed the following 
// statement.  
// The update to the path_pair start index should be done outside the procedure. 
        RT[result = RT_TOP++] = NORM_FALSE; 
        for (cvx_index = 0, i = comp+1; 
             i < RT_TOP; 
             cvx_index++, i++
             ) {
          RT[result] = red_bop(OR, RT[result], 
            ddd_one_constraint(RT[i] = red_hull_normalize(i), 
              VI_VALUE, cvx_index, cvx_index
          ) ); 
        } 
        RT_TOP = orig_rttop; 

        #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
        print_cpu_time(
          "\n>>> split %d, %d new split frames, leaving split convexities bck.\n", 
          count_split_convexities_bck, 
          RT_TOP-orig_rttop 
        ); 
        fprintf(RED_OUT, "\n>>> split %d, From path image RT[path=%1d]:\n", 
          count_split_convexities_bck, 
          path
        ); 
/*
        red_print_graph(RT[path]); 
        for (i = orig_rttop; i < RT_TOP; i++) { 
          fprintf(RED_OUT, "\n>>> split %d, convex component %d.\n", 
            count_split_convexities_bck, 
            i
          ); 
          red_print_graph(RT[i]); 
        } 
*/
        #endif 

        return (RT[result]); 
      } 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
      fprintf(RED_OUT, "\n>>> split %d, new concavity at %1d\n", 
        count_split_convexities_bck, 
        i
      ); 
      red_print_graph(RT[i]); 
      #endif 
      
      conj = red_complement(RT[i]); 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
      fprintf(RED_OUT, "\n>>> split %d, complement of new concavity at %1d\n", 
        count_split_convexities_bck, 
        i
      ); 
//      red_print_graph(conj); 

      fprintf(RED_OUT, "\n>>> split %d, prev concavity at i-1=%1d\n", 
        count_split_convexities_bck, 
        i-1
      ); 
//      red_print_graph(RT[i-1]); 
      #endif 
      
      RT[i-1] = red_bop(AND, RT[i-1], conj); 
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
/*
      fprintf(RED_OUT, 
        "\n>>> split %d, new convexity at %1d after subtracting RT[i-1=%1d]:\n", 
        count_split_convexities_bck, 
        i-1, i 
      ); 
      red_print_graph(RT[i-1]); 
      RT[i-1] = red_hull_normalize(i-1); 
      fprintf(RED_OUT, 
        "\n>>> split %d, new convexity at %1d after normalizing RT[i-1=%1d]:\n", 
        count_split_convexities_bck, 
        i-1, i 
      ); 
      red_print_graph(RT[i-1]); 
*/
      #endif 

      RT[comp] = red_bop(OR, RT[comp], RT[i-1]); 
    } 
  }
  else {
    RT[i = RT_TOP++] = RT[path]; 
    for (; TYPE_TRUE; ) { 
      conj = red_extract_concavity_bck(i); 	
      RT[i = RT_TOP++] = conj; 
      if (RT[i] == NORM_FALSE) { 
        RT_TOP--; // i, the last one is false. 
// To avoid the undesirable side-effect, we have removed the following 
// statement.  
// The update to the path_pair start index should be done outside the procedure. 
        RT[result = RT_TOP++] = NORM_FALSE; 
        for (cvx_index = 0, i = comp+1; 
             i < RT_TOP; 
             cvx_index++, i++
             ) {
          RT[result] = red_bop(OR, RT[result], 
            ddd_one_constraint(RT[i] = red_hull_normalize(i), 
              VI_VALUE, cvx_index, cvx_index
          ) ); 
        } 

        RT_TOP = orig_rttop; 
        #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
        print_cpu_time("\nsplit %d, %d new split frames, leaving split convexities bck.\n", 
          count_split_convexities_bck, 
          RT_TOP-orig_rttop 
        ); 
        #endif 
        return; 
      } 
      RT[i-1] = red_bop(AND, RT[i-1], red_complement(RT[i])); 
  } }
  fprintf(RED_OUT, "Error, in looping for splitting convexities.\n"); 
  fflush(RED_OUT); 
  exit(0); 
}
  /* red_split_convexities_bck() */ 
  
  

int	count_print_fillin_split_convexities = 0; 

void	print_fillin_split_convexities(char *s) { 
  int	i; 

  fprintf(RED_OUT, 
    "\n(%1d(I%1d)))))))))))))))))))))))))))))))))))))))))\n", 
    ++count_print_fillin_split_convexities, 
    ITERATION_COUNT
  ); 
}
  /* print_fillin_split_convexities() */ 








inline struct red_type	*fillin_game_path_split_convexities(
  int	path, 
  int	flag_roles 
) { 
  int				i, j; 
  struct cache1_hash_entry_type	*ce; 

  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    double	start_time_progress_overhead, stop_time_progress_overhead; 
    
    start_time_progress_overhead = red_user_time(); 
    #endif  
  #endif 

  ce = cache1_check_result_key(opcode_game_time_path(flag_roles), RT[path]); 
  if (ce->result) {
    return(ce->result); 
  } 

  ce->result = red_split_convexities_bck(path);
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    print_fillin_split_convexities("combi"); 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
    stop_time_progress_overhead = red_user_time(); 
    update_time_progress_statistics(
      0.0, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      stop_time_progress_overhead - start_time_progress_overhead, 
      0.0, 
      0.0, 
      "IT %1d, overhead push_path_split", ITERATION_COUNT  
    ); 
    #endif  
  #endif 
  return(ce->result); 
} 
  /* fillin_game_path_split_convexities() */ 




  

#ifdef RED_DEBUG_ZONE_MODE
int	local_count_label = 0; 
#endif 
  

int	count_push_game_shared = 0; 



int	ctpb = 0; 
#ifdef RED_DEBUG_ZONE_MODE
int	count_tpb_gsc = 0; 
#endif 

struct red_type *red_time_progress_bck_with_given_shared_concavity(
  int 			w, 
  struct red_type	*concavity  
) { 
  int	result; 
  
  #ifdef RED_DEBUG_ZONE_MODE
  ++count_tpb_gsc; 
  #endif 
  
  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_HYBRID: 
    #ifdef RED_DEBUG_ZONE_MODE
    fprintf(RED_OUT, "GSC %1d: Sorry that we have not done\n", count_tpb_gsc); 
    fprintf(RED_OUT, "  backward time progress\n"); 
    fprintf(RED_OUT, "  with shared concavity for hybrid systems.\n"); 
    fflush(RED_OUT); 
    fflush(RED_OUT); 
    #endif 
    exit(0); 
  case FLAG_SYSTEM_UNTIMED: 
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    fprintf(RED_OUT, 
      "GSC %1d: It is weird to do time progression for untimed systems.\n", 
      count_tpb_gsc 
    ); 
    fflush(RED_OUT); 
    #endif 
    break; 
  }
/* The general formulation for backward time progression of timed automata is as follows.    
   Given destination predicate W and path predicate P, 
   
     v = exists t (t >= 0 && v+t |= W && ~ exists t'(t'>=0 && t'<= t && v+t' |= ~P)).  
   
   In the inner quantification of ~P, we have 
   
       -t'<= 0    ..... (a)
       t'-t<= 0   ..... (b)
       x+t'<= c   ..... (c) 
       -y-t'<= -d ..... (d) 
       x-y <= e   ..... (e) 
       
   (a)+(b)+(c)+(d)+(e) --> exists t' (-t'<=0 && t'-t <= 0 && ~ P+t') 
   except that -y -t'<= -d are replaced with (b) + (d) --> -y - t <= -d 
   This means that we can do the backward time progress of ~P by keeping in mind that 
   only the lower-bound atoms of the inner quantification will participate the 
   bypass operation of the outer quantification.  
   Thus we use variable deltap as a dummy variable in place of zero 
   in the the upper-bound atoms of bypass(~P, 0) (in statement (b)) 
   so that they won't participate
   the bypass operation in the outer quantification.  
   This is done with red_clock_upper_deltap() in statement (c).  
   Then later, the upper-bound atoms will be changed to lower-upperbound atoms by the 
   complement in statement (d). 
   So finally, after the quantification of the outer loop, we need to eliminate all the 
   deltap in the lower-bound atoms.  
   This is done with red_clock_lower_extend().  
   
   Note that when the path condition is RT[DECLARED_GLOBAL_INVARIANCE], 
   we can do the off-line computation and use the result of statement (d) repetitively. 
   This is what we have done.  
   We save the result from statements (a) to (d) for RT[path]== RT[DECLARED_GLOBAL_INVARIANCE]
   in RED_INVARIANCE_CONTINUITY.  
  fprintf(RED_OUT, "parameter to red_time_progress_bck_with_shared_concavity()\n"); 
  red_print_graph(RT[w]); 
  if (path != FLAG_TIME_PATH_INVARIANCE) 
    red_print_graph(RT[path]); 
*/
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  fprintf(RED_OUT, 
    "\nGSC %1d: Calculating time progress bck with a given shared concavity:\n", 
    count_tpb_gsc 
  ); 
  fprintf(RED_OUT, "GSC %1d: For dst:\n", 
    count_tpb_gsc 
  ); 
  red_print_graph(RT[w]); 
  fprintf(RED_OUT, "GSC %1d: That is, exists t>=0&&(dst+t&& sc)\n", 
    count_tpb_gsc 
  ); 
  fprintf(RED_OUT, 
    "GSC %1d:          exists t((-t)<=0 && (dst-(-t)) && sc)\n", 
    count_tpb_gsc 
  ); 
  #endif 
  
  RT[result = RT_TOP++] = red_time_progress_by_amount(RT[w], DELTA); 
  RT[result] = red_bop(AND, RT[result], concavity); 
  RT[result] = crd_one_constraint(RT[result], ZONE[NEG_DELTA][0], 0); 
  RT[result] = red_bypass_DOWNWARD(result, NEG_DELTA); // tight_all_pairs(w); 
  /* Note that now the following procedure also have to remove 
   * all the annoations added in by red_annotate_clock_upper_deltap() 
   */
  RT[result] = red_time_clock_eliminate(RT[result], NEG_DELTA); 
  RT_TOP--; // result 
  
  return(RT[result]); 
}
  /* red_time_progress_bck_with_given_shared_concavity() */ 




  
inline struct red_type *red_game_time_progress_bck_full_formulation(
  int	w, 
  int	path
) { 
  int	result; 
  
/* The general formulation for backward time progression of timed automata is as follows.    
   Given destination predicate W and path predicate P, 
   
     v = exists t (t >= 0 && v+t |= W && ~ exists t'(t'>=0 && t'<= t && v+t' |= ~P)).  
   
   In the inner quantification of ~P, we have 
   
       -t'<= 0    ..... (a)
       t'-t<= 0   ..... (b)
       x+t'<= c   ..... (c) 
       -y-t'<= -d ..... (d) 
       x-y <= e   ..... (e) 
       
   (a)+(b)+(c)+(d)+(e) --> exists t' (-t'<=0 && t'-t <= 0 && ~ P+t') 
   except that -y -t'<= -d are replaced with (b) + (d) --> -y - t <= -d 
   This means that we can do the backward time progress of ~P by keeping in mind that 
   only the lower-bound atoms of the inner quantification will participate the 
   bypass operation of the outer quantification.  
   Thus we use variable deltap as a dummy variable in place of zero 
   in the the upper-bound atoms of bypass(~P, 0) (in statement (b)) 
   so that they won't participate
   the bypass operation in the outer quantification.  
   This is done with red_clock_upper_deltap() in statement (c).  
   Then later, the upper-bound atoms will be changed to lower-upperbound atoms by the 
   complement in statement (d). 
   So finally, after the quantification of the outer loop, we need to eliminate all the 
   deltap in the lower-bound atoms.  
   This is done with red_clock_lower_extend().  
   
   Note that when the path condition is RT[DECLARED_GLOBAL_INVARIANCE], 
   we can do the off-line computation and use the result of statement (d) repetitively. 
   This is what we have done.  
   We save the result from statements (a) to (d) for RT[path]== RT[DECLARED_GLOBAL_INVARIANCE]
   in RED_INVARIANCE_CONTINUITY.  
  fprintf(RED_OUT, "parameter to red_time_progress_bck_full_formulation()\n"); 
  red_print_graph(RT[w]); 
  if (path != FLAG_TIME_PATH_INVARIANCE) 
    red_print_graph(RT[path]); 
*/
  RT[result = RT_TOP++] = red_shared_concavity_bck(path, RT[path]); 
/*
    print_cpu_time("time progress f"); 
*/
/*
  } 
*/
  RT[result] 
  = red_time_progress_bck_with_given_shared_concavity(w, RT[result]); 

  RT_TOP--; // result 
  return(RT[result]); 
}
  /* red_game_time_progress_bck_full_formulation() */ 





inline struct red_type	*red_time_progress_bck_given_split_convexities(
  int			w, 
  struct red_type	*red_split_convexities   
) { 
  int	ci, result, convex; 
  
  if (red_split_convexities == NORM_FALSE) 
    return(RT[w]); 

  RT[result = RT_TOP++] = NORM_FALSE; 
  convex = RT_TOP++; 
  for (ci = 0; ci < red_split_convexities->u.ddd.child_count; ci++) { 
    RT[convex] = red_split_convexities->u.ddd.arc[ci].child; 
    RT[result] = red_bop(OR, RT[result], 
      red_time_progress_bck_convex(w, convex) 
    ); 
  } 
  RT_TOP = RT_TOP-2; // convex, result 
  return(RT[result]); 
}
  /* red_time_progress_bck_given_split_convexities() */ 






inline struct red_type	*red_time_progress_bck_given_easy_concavity(
  int			w, 
  struct red_type	*red_easy_concavity_analysis  
) { 
  int	concave, convex; 
  
  RT[concave = RT_TOP++] = red_easy_concavity_analysis->u.ddd.arc[0].child; 
  RT[convex = RT_TOP++] = red_easy_concavity_analysis->u.ddd.arc[1].child; 
  RT[concave] = red_time_progress_bck_with_given_shared_concavity(
    w, 
    RT[concave] 
  ); 

  RT[convex] = red_time_progress_bck_convex(w, convex); 
  RT[concave] = red_bop(OR, RT[concave], RT[convex]); 
  RT_TOP = RT_TOP-2; // concave, convex 
  
  return(RT[concave]); 
}
  /* red_time_progress_bck_given_easy_concavity() */  










  
#ifdef RED_DEBUG_ZONE_MODE
  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  int	ctpb_h = 0, ctpb2_h = 0; 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
  double	ctpb_time = 0.0; 
  #endif 
#endif 

/* We are not supposed to write the result back to RT[w]. 
*/ 



int	check_time_progress_downward_closure(
  struct red_type	*dpath, 
  struct red_type	*ddest 
) { 
  return(TYPE_TRUE); 	
}
  /* check_time_progress_downward_closure() */ 







/* 
 *  How we evaluate the time progress from the dest to path ? 
 *  We need to set up two parameters, 
 *  the flag_path_includes_dest, 
 *  and the time_progress_option.  
 * 
 *  To show the performance of our techniques, 
 *  we only allow TC analysis in the following cases. 

     1. EA segmented evaluation has been turned on, 
     2. TCTCTL option has been turned on, 

    So here is our strategy: 

     1. We create a new flag, FLAG_TIME_PROGRESS_ANALYSIS_LEVEL.  
     
          #define FLAG_TIME_PROGRESS_ANALYSIS_NONE	0
          #define FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL	1
          #define FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED	2 
           
     2. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_NONE, 
        then we use the following strategy. 

        2.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        2.b In all other cases, we use T(flat_path_includes_dest = false). 

     3. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL, 

        3.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        3.b If
            3.b.A the path is TCTCTL and 
            // a flag in exp. 
            3.b.B one of the following two is true. 
                3.b.B.i   the path is the invariance or 
                // conditional statement 
                3.b.B.ii  the path includes the dest, 
	        // a flag to T and T'
            then we use T'(flat_path_includes_dest = true).  
        3.c In all other cases, we use T(flat_path_includes_dest = false). 

     4. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED, 

        4.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        4.b If 
            4.b.A the path is TCTCTL and 
            // a flag in exp. 
            4.b.B one of the following two is true. 
                4.b.B.i   the path is the invariance or 
                // conditional statement 
                4.b.B.ii  the path includes the dest, 
	        // a flag to T and T'
            then we use T'(flat_path_includes_dest = true).  
        4.c If 
            4.c.A the verification subtask is either EU or EA and 
            // the path_exp is not null. 
            4.c.B the path is TCTCTL, 
            // a flag in exp. 
            4.c.C one of the following three is true. 
                4.c.C.i   the path is the invariance, or 
                // conditional statement 
                then we use T'(flat_path_includes_dest = true).  
                4.c.C.ii  the path includes the dest, or 
	        // a flag to T and T'
                then we use T'(flat_path_includes_dest = true).  
                4.c.C.iii the dest satisfies the down-closedness property 
                    with respect to the path.
	        // a procedure test
                then we use T'(flat_path_includes_dest = false).  
        4.d In all other cases, we use T(flat_path_includes_dest = false). 

 */ 

struct red_type	*red_game_time_progress_bck(
  struct ps_exp_type	*path_exp, 
  int			w, 
  int			path,  
  int			flag_roles, 
  int			flag_path_includes_dest 
                                // TYPE_FALSE actually means maybe not.
                                // This is used specifically in the 
                                // evaluation of EU. 
) { 
  int				local_option_time_progress, 
				urgent, result, time, i, 
				convex, concave, w_concave, true_path; 
  struct cache2_hash_entry_type	*ce; 
  struct red_type		*red_path_analysis; 

  #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
  double			local_time = red_user_time(); 
  #endif 

  switch (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) {
  case FLAG_SYSTEM_TIMED: 
  case FLAG_SYSTEM_HYBRID: 
    break; 
  default: 
    return (RT[w]); 
  }  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    int top = GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS; 

    ctpb_h++; 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE_TIME_MEASURE
  start_time_progress = red_user_time(); 
  #endif 

  #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
  int	rec_rttop = RT_TOP; 
  #endif 
  
  switch (flag_roles) { 
  case (FLAG_GAME_SPEC | FLAG_GAME_ENVR): 
  case (FLAG_GAME_MODL | FLAG_GAME_ENVR): 
  case (FLAG_GAME_SPEC | FLAG_GAME_MODL | FLAG_GAME_ENVR): 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nError: Illegal role specification %x in red_game_time_progress_bck().\n", 
      flag_roles
    );
    fflush(RED_OUT); 
    bk(0); 
    exit(0);  	
  } 
  
  if ((GSTATUS[INDEX_SYSTEM_TYPE]&MASK_SYSTEM_TYPE) == FLAG_SYSTEM_UNTIMED) { 
    #ifdef RED_DEBUG_ZONE_MODE
    #endif 
    return(RT[w]); 
  }  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
/*
      print_cpu_time(
      "\nTP %1d:%d, entering the time progress backward.\n", 
      ctpb_h
    ); 
*/
    #endif 
/*
    fprintf(RED_OUT, "** %1d, dest of time progress back:\n", 
      ctpb_h
    ); 
//    red_print_graph(RT[w]); 
*/ 
  #endif 
  
  switch (GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_ANALYSIS) { 
  case FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED: 
/*
     4. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED, 

        4.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        4.b If 
            4.b.A the path is TCTCTL and 
            // a flag in exp. 
            4.b.B one of the following two is true. 
                4.b.B.i   the path is the invariance or 
                // conditional statement 
                4.b.B.ii  the path includes the dest, 
	        // a flag to T and T'
            then we use T'(flat_path_includes_dest = true).  
        4.c If 
            4.c.A the verification subtask is either EU or EA and 
            // the path_exp is not null. 
            4.c.B the path is TCTCTL, 
            // a flag in exp. 
            4.c.C one of the following three is true. 
                4.c.C.i   the path is the invariance, or 
                // conditional statement 
                then we use T'(flat_path_includes_dest = true).  
                4.c.C.ii  the path includes the dest, or 
	        // a flag to T and T'
                then we use T'(flat_path_includes_dest = true).  
                4.c.C.iii the dest satisfies the down-closedness property 
                    with respect to the path.
	        // a procedure test
                then we use T'(flat_path_includes_dest = false).  
        4.d In all other cases, we use T(flat_path_includes_dest = false). 
*/
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_MODEL_CHECK
        && path_exp 
        && (path_exp->exp_status & FLAG_TCTCTL_SUBFORM)
        && check_time_progress_downward_closure(RT[path], RT[w])
        ) { 
      local_option_time_progress = FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
      RT[true_path = RT_TOP++] = red_bop(OR, RT[path], RT[w]); 
      break; 
    } 

  case FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL:
/* 
     3. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL, 

        3.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        3.b If
            3.b.A the path is TCTCTL and 
            // a flag in exp. 
            3.b.B one of the following two is true. 
                3.b.B.i   the path is the invariance or 
                // conditional statement 
                3.b.B.ii  the path includes the dest, 
	        // a flag to T and T'
            then we use T'(flat_path_includes_dest = true).  
        3.c In all other cases, we use T(flat_path_includes_dest = false). 
*/
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_MODEL_CHECK
        && path_exp 
        && (path_exp->exp_status & FLAG_TCTCTL_SUBFORM)
        && (   flag_path_includes_dest 
            || check_inv_path_role(RT[path], flag_roles) 
        )   ) { 
      local_option_time_progress = FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
      RT[true_path = RT_TOP++] = RT[path]; 
      break; 
    } 

  case FLAG_TIME_PROGRESS_ANALYSIS_NONE: 
/* 
     2. If FLAG_TIME_PROGRESS_ANALYSIS_LEVEL is 
        FLAG_TIME_PROGRESS_ANALYSIS_NONE, 
        then we use the following strategy. 

        2.a In reachability analysis, if the invariance condition is TC, 
            then we use T'(flat_path_includes_dest = true).  
            // a flag in GSTATUS
        2.b In all other cases, we use T(flat_path_includes_dest = false). 
*/
    if (   (!path_exp)  
        && (GSTATUS[INDEX_TASK] & MASK_TASK) > TASK_MODEL_CHECK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) < TASK_REDLIB_SESSION
        && (GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
        && flag_path_includes_dest 
        ) { 
      local_option_time_progress = FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 
      RT[true_path = RT_TOP++] = RT[path]; 
    } 
    else {
      local_option_time_progress 
      = GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS; 
      RT[true_path = RT_TOP++] = red_bop(OR, RT[w], RT[path]); 
    }
    break; 
  }

  ce = cache2_check_result_key(
    OP_TIME_PROGRESS | flag_roles | local_option_time_progress, 
    RT[true_path], RT[w] 
  ); 
  if (ce->result) { 
    RT_TOP--; // true_path 
    return(ce->result); 
  } 

  RT[result = RT_TOP++] = NORM_FALSE; 
  RT[urgent = RT_TOP++] = red_bop(AND, RT[w], RT[INDEX_URGENT]);
/*
  fprintf(RED_OUT, "ctpb=%1d, RT[w=%1d]=%x:\n", ++ctpb, w, RT[w]); 
  red_print_graph(RT[w]);   
  if (true_path == FLAG_TIME_PATH_INVARIANCE) { 
    fprintf(RED_OUT, "input invariance used in time progression back.\n"); 
  }
  else { 
    fprintf(RED_OUT, "ctpb=%1d, RT[true_path=%1d]=%x, problem:\n", ctpb, true_path, RT[true_path]); 
    red_print_graph(RT[true_path]); 
  }
  
  fprintf(RED_OUT, "ctpb=%1d, RT[INDEX_URGENT=%1d]=%x:\n", 
    ctpb, INDEX_URGENT, RT[INDEX_URGENT]
  ); 
  red_print_graph(RT[INDEX_URGENT]); 
*/  
  if (RT[urgent] != NORM_FALSE)
    RT[time = RT_TOP++] = red_bop(SUBTRACT, RT[w], RT[INDEX_URGENT]); 
  else 
    RT[time = RT_TOP++] = RT[w]; 

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    RT[result] = NORM_FALSE; 
    RT[result] = hybrid_time_progress(time, true_path, TIME_BACKWARD); 
    RT[result] = red_bop(OR, RT[result], RT[urgent]);
    RT_TOP = RT_TOP-2; /* time, urgent */ 
    garbage_collect(FLAG_GC_SILENT);
    RT_TOP--; /* result */ 

    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
    if (rec_rttop != RT_TOP) { 
      fprintf(RED_OUT, "Error: the RT_TOP value is not consistent!\n"); 
      fflush(RED_OUT); 
      bk(0); 	
    } 
    #endif 

    RT_TOP--; // true_path 
    return(ce->result = RT[result]);
  }

  switch (local_option_time_progress) { 
  case FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY: 
    #ifdef RED_DEBUG_ZONE_MODE
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
      #endif 
    #endif 
//    fprintf(RED_OUT, "\nTime progress bck convex.\n"); 
    RT[result] = red_time_progress_bck_convex(time, true_path); 
    break; 
    
  case FLAG_TIME_PROGRESS_FULL_FORMULATION: 
//    fprintf(RED_OUT, "\nTime progress bck full formulation.\n"); 
    RT[result] = red_game_time_progress_bck_full_formulation(
      time, true_path
    ); 
    break; 

  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY: 
    #ifdef RED_DEBUG_ZONE_MODE
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
      #endif 
    #endif 

//    fprintf(RED_OUT, "\nTime progress bck shared concavity.\n"); 
    red_path_analysis = fillin_game_shared_concavity_bck(
      true_path, flag_roles
    ); 
    RT[result] = red_time_progress_bck_with_given_shared_concavity(
      time, 
      red_path_analysis 
    ); 
    break; 

    // The end of case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY 
    // and case FLAG_TIME_PROGRESS_SHARED_CONCAVITY.

  case FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES:     
  case FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES: 
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES: 
  case FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES: 
//    fprintf(RED_OUT, "\nTime progress bck split convexities.\n"); 
    red_path_analysis = fillin_game_path_split_convexities(
      true_path, flag_roles
    ); 
    RT[result] = red_time_progress_bck_given_split_convexities(
      time, red_path_analysis  
    ); 
    break; 
  
  case FLAG_TIME_PROGRESS_EASY_CONCAVITY: 
  case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY: 
  case FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY: 
    #ifdef RED_DEBUG_ZONE_MODE
      #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
      #endif 
    #endif 
//    fprintf(RED_OUT, "\nTime progress bck shared concavity.\n"); 
    red_path_analysis = fillin_game_easy_concavity_analysis(
      true_path, flag_roles
    ); 
    RT[result] = red_time_progress_bck_given_easy_concavity(
      time, red_path_analysis  
    ); 
    break; 
    // The end of case FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY 
    // and case FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY.
  
  default: 
    fprintf(RED_OUT, "Illegal option %x on time progress to time progress bck.\n", 
      GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 

  RT[result] = red_bop(OR, RT[result], RT[urgent]);
/*
  print_cpu_time("time progress i"); 
*/
  RT_TOP = RT_TOP-4; /* time, result, urgent, true_path */
  
  #ifdef RED_DEBUG_ZONE_MODE
    #ifdef RED_DEBUG_ZONE_MODE_TIME_PROGRESS
/*
    print_cpu_time( 
      "\nTP %1d:%1d, leaving the time progress backward.\n", 
      ITERATION_COUNT, ctpb_h
    ); 
*/
    #endif 
/*
  fprintf(RED_OUT, "** %1d, result of time progress back:\n", 
    ctpb_h
  ); 
  red_print_graph(RT[w]); 
*/
  if (rec_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: the RT_TOP value (old %1d; new %1d) is not consistent in red_time_progress_bck()!\n", 
      rec_rttop, RT_TOP 
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  #endif 

  #if defined(RED_REGRESS_CHECKING) || defined(RED_DEBUG_ZONE_MODE_TIME_MEASURE)
  update_time_progress_statistics(local_option_time_progress); 
  #endif 
    
  return(ce->result = RT[result]); 
} 
  /* red_game_time_progress_bck() */ 





/*******************************************************
 * This following procedure does not depend on the 
 * assumption that RT[w] \subseteq RT[path].   
 * The procedure is needed for the correct evaluation of 
 * EU properties like exists x <= 5 until x>5.  
 */
int	ctpbg_h = 0; 


 
 
 
inline struct red_type	*red_time_progress_bck_option(
  int	w, 
  int	path, 
  int	option
) { 
  int	orig_time_progress, result; 
  
  orig_time_progress = GSTATUS[INDEX_TIME_PROGRESS]; 
  GSTATUS[INDEX_TIME_PROGRESS] 
  = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS) 
  | (option & MASK_TIME_PROGRESS_OPTIONS); 
  result = RT_TOP++; 
  RT[result] = red_game_time_progress_bck(NULL, 
    w, path, MASK_GAME_ROLES, 
    TYPE_FALSE
  ); 
  RT_TOP--; // result 
  GSTATUS[INDEX_TIME_PROGRESS] = orig_time_progress; 
  
  return(RT[result]); 
}
  /* red_time_progress_bck_option() */ 









struct discrete_frame_type {
  int	vi, lb, ub; 	
}
  *discrete_frame; 
int	top_frame; 
  
struct red_type	*ID_INVARIANCE; 


struct red_type	*rec_discrete_stack_extract(d, pos)
     struct red_type	*d;
     int		pos; 
{
  struct red_type		*result, *conj;
  int				vi, lb, ub, ci;
  struct crd_child_type		*bc;
  struct ddd_child_type		*ic;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_DISCRETE_STACK_EXTRACT, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      bc = &(d->u.crd.arc[ci]);
      conj = crd_one_constraint(
        rec_discrete_stack_extract(bc->child, pos), 
	d->var_index, bc->upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_discrete_stack_extract(d->u.fdd.arc[ci].child, pos), 
	d->var_index, d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_discrete_stack_extract(d->u.dfdd.arc[ci].child, pos), 
	d->var_index, d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default: 
    for (; pos < top_frame && d->var_index > discrete_frame[pos].vi; pos++) ;
    if (pos < top_frame && d->var_index == discrete_frame[pos].vi) {
      result = NORM_FALSE; 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      	if (   d->u.ddd.arc[ci].lower_bound == discrete_frame[pos].lb 
      	    && d->u.ddd.arc[ci].upper_bound == discrete_frame[pos].ub
      	    ) {
	  result = rec_discrete_stack_extract(d->u.ddd.arc[ci].child, pos+1);
	  break; 
	} 
      } 
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
	ic = &(d->u.ddd.arc[ci]);
	conj = ddd_one_constraint
		(rec_discrete_stack_extract(ic->child, pos), 
		 d->var_index, ic->lower_bound, ic->upper_bound
		 );
	result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_discrete_stack_extract() */





struct red_type	*red_discrete_stack_extract(d, top) 
	struct red_type	*d; 
	int		top; 
{
  struct red_type	*result;

  cache1_clear(OP_DISCRETE_STACK_EXTRACT); 
  top_frame = top; 
  result = rec_discrete_stack_extract(d, 0);

  return(result);
} 
  /* red_discrete_stack_extract() */ 





void	test_time_progress(int time_option) { 
  int			c1, c2, c3, m1, m2, m3, orig_status, 
			wp, pconvex_start, pconvex_stop, 
  			t1, t2, w, tc = 0, i; 
  struct red_type	*conj1, *conj2; 

  fprintf(RED_OUT, "\n** We test the time progress bck operator with **\n"); 
  fprintf(RED_OUT, "\n** the Fischer's benchmark for 3 processes.    **\n\n"); 
  fprintf(RED_OUT, "The global invariance:\n"); 
  red_print_graph(RT[DECLARED_GLOBAL_INVARIANCE]); 
  fprintf(RED_OUT, "The BACKWARD shared concavity of the global invariance:\n"); 
  
  m1 = variable_index[TYPE_DISCRETE][1][OFFSET_MODE]; 
  m2 = variable_index[TYPE_DISCRETE][2][OFFSET_MODE]; 
  m3 = variable_index[TYPE_DISCRETE][3][OFFSET_MODE]; 
  c1 = variable_index[TYPE_CLOCK][1][0]; 
  c1 = VAR[c1].U.CLOCK.CLOCK_INDEX; 
  c2 = variable_index[TYPE_CLOCK][2][0]; 
  c2 = VAR[c2].U.CLOCK.CLOCK_INDEX; 
  c3 = variable_index[TYPE_CLOCK][3][0]; 
  c3 = VAR[c2].U.CLOCK.CLOCK_INDEX; 
  
  conj1 = crd_atom(ZONE[0][c1], -10); 
  conj2 = crd_atom(ZONE[c1][0], 5); 
  conj2 = crd_one_constraint(conj2, ZONE[0][c1], -3); 
  RT[wp = RT_TOP++] = red_bop(OR, conj1, conj2); 
  RT[wp] = ddd_one_constraint(RT[wp], m1, 0, 0); 
  
  RT[t2 = RT_TOP++] = crd_atom(ZONE[0][c1], -20); 
  fprintf(RED_OUT, ">>> %1d) The test dest = %1d:\n", tc, t2); 
  red_print_graph(RT[t2]); 

  fprintf(RED_OUT, "\n\n>>> %1d) the result of time progress bck:\n", tc); 
  red_print_graph(
    red_game_time_progress_bck(
      NULL, t2, DECLARED_GLOBAL_INVARIANCE, MASK_GAME_ROLES, TYPE_FALSE  
  ) ); 
  
/*
  fprintf(RED_OUT, "\n\n>>> %1d) test path=%1d:\n", ++tc, wp); 
  red_print_graph(RT[wp]); 
*/
  orig_status = GSTATUS[INDEX_TIME_PROGRESS]; 
  GSTATUS[INDEX_TIME_PROGRESS] 
  = (GSTATUS[INDEX_TIME_PROGRESS] & MASK_TIME_PROGRESS_OPTIONS) 
  | time_option; 
  fprintf(RED_OUT, "\nBreaking RT[wp]: \n"); 
  red_print_graph(RT[wp]);
  RT[t2] = crd_atom(ZONE[0][c1], -20); 
  fprintf(RED_OUT, ">>> %1d) The test dest = %1d:\n", ++tc, t2); 
  red_print_graph(RT[t2]); 
  fprintf(RED_OUT, "\n\n>>> %1d), the result of time progress bck:\n", tc); 
  red_print_graph(red_game_time_progress_bck(
    NULL, t2, wp, MASK_GAME_ROLES, TYPE_FALSE 
  ) ); 

  conj1 = ddd_one_constraint(conj1, m1, 1, 1); 
  RT[wp] = red_bop(OR, RT[wp], conj1); 

  fprintf(RED_OUT, "\n\n>>> %1d) test path=%1d:\n", ++tc, wp); 
  red_print_graph(RT[wp]); 

  conj1 = crd_atom(ZONE[0][c1], -10); 
  conj2 = crd_atom(ZONE[c1][0], 5); 
  conj2 = crd_one_constraint(conj2, ZONE[0][c1], -3); 
  RT[t1 = RT_TOP++] = red_bop(OR, conj1, conj2); 
  RT[t1] = ddd_one_constraint(RT[t1], m1, 0, 0); 
  conj1 = ddd_one_constraint(conj1, m1, 1, 1); 
  RT[t1] = red_bop(OR, RT[t1], conj1); 
  fprintf(RED_OUT, "\n\n>>> %1d) test dest=%1d:\n", tc, t1); 
  red_print_graph(RT[t1]); 
  RT[t2] = RT[t1]; 

  fprintf(RED_OUT, "\nBreaking RT[wp]: \n"); 
  red_print_graph(RT[wp]);

  red_print_graph(
    red_game_time_progress_bck(NULL, t1, wp, MASK_GAME_ROLES, TYPE_FALSE)
  ); 
  

  fprintf(RED_OUT, "\n\n>>> %1d) test dest=%1d:\n", tc, t2); 
  red_print_graph(RT[t2]); 
  fprintf(RED_OUT, 
    "\n\n>>> %1d), the result of time progress bck:\n", 
    tc
  ); 
  red_print_graph(red_game_time_progress_bck(
    NULL, t2, pconvex_start, pconvex_stop, TYPE_FALSE)); 
  GSTATUS[INDEX_TIME_PROGRESS] = orig_status; 
  RT_TOP = RT_TOP-3; /* t2, t1, wp */ 
  exit(0); 
}
  /* test_time_progress() */ 
  




void 	test_time_progress1() { 
  int	i, j; 
  
  for (i = 0; i < 3; i++) {
    fprintf(RED_OUT, "DEBUG_RED[i=%1d]:\n", i); 
    red_print_graph(DEBUG_RED[i]); 
    red_print_graph(zone_untimed_subtract(DEBUG_RED[i])); 
  }
  for (i = 0; i < 3; i++) { 
    for (j = 0; j < 3; j++) { 
      fprintf(RED_OUT, "%1d-%1d:\n", i, j); 
      red_print_graph(zone_subtract(DEBUG_RED[i], DEBUG_RED[j])); 
    }
  }
  exit(0); 
} 
  /* test_time_progress1() */ 
  


int	count_test_zone = 0; 

void	print_test_zone(
  char	*s, 
  int	fxp, 
  int	pstart, 
  int	pstop
) {
  int	i; 
  
  fprintf(RED_OUT, 
    "\n**(test zone %1d):%s: fxp=%1d, pstart=%1d, pstop=%1d **\n", 
    ++count_test_zone, s, fxp, pstart, pstop
  ); 
  fprintf(RED_OUT, "RT[fxp=%1d]:\n", fxp); 
  red_print_graph(RT[fxp]); 
  for (i = pstart; i <= pstop; i++) { 
    fprintf(RED_OUT, "path component %1d:\n", i); 
    red_print_graph(RT[i]); 	
  } 
}
  /* print_test_zone() */  
  
  
  
void	test_zone() {  
  int	fxp, pstart, pstop, x1, x2, x3; 
  
  x1 = variable_index[TYPE_CLOCK][1][0]; 
  x1 = VAR[x1].U.CLOCK.CLOCK_INDEX; 
  x2 = variable_index[TYPE_CLOCK][2][0]; 
  x2 = VAR[x2].U.CLOCK.CLOCK_INDEX; 
  x3 = variable_index[TYPE_CLOCK][3][0]; 
  x3 = VAR[x3].U.CLOCK.CLOCK_INDEX; 
  
  RT[fxp = RT_TOP++] = NORM_FALSE; 
  RT[pstop = pstart = RT_TOP++] = crd_atom(ZONE[0][x1], 0); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x1][0], 20); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[0][x2], -10); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x2][0], 29); 
  RT[fxp] = crd_atom(ZONE[x3][0], 16); 
  RT[fxp] = red_bop(OR, RT[fxp], crd_atom(ZONE[0][x3], -20)); 
  RT[fxp] = red_bop(AND, RT[fxp], RT[pstart]); 
  
  exit(0); 
}
  /* test_zone() */ 
  



void	test_zone2() {  
  int	fxp, pstart, pstop, x1, x2, x3; 
  
  x1 = variable_index[TYPE_CLOCK][1][0]; 
  x1 = VAR[x1].U.CLOCK.CLOCK_INDEX; 
  x2 = variable_index[TYPE_CLOCK][2][0]; 
  x2 = VAR[x2].U.CLOCK.CLOCK_INDEX; 
  x3 = variable_index[TYPE_CLOCK][3][0]; 
  x3 = VAR[x3].U.CLOCK.CLOCK_INDEX; 
  
  RT[fxp = RT_TOP++] = crd_atom(ZONE[0][x1], -10); 
  RT[fxp] = red_bop(OR, RT[fxp], crd_atom(ZONE[x2][0], 20)); 
  RT[pstart = RT_TOP++] = NORM_TRUE; 
  pstop = pstart; 
  
  exit(0); 
}
  /* test_zone2() */ 
  
  
void	test_zone3() {  
  int	fxp, pstart, pstop, x1, x2, x3; 
  
  x1 = variable_index[TYPE_CLOCK][1][0]; 
  x1 = VAR[x1].U.CLOCK.CLOCK_INDEX; 
  x2 = variable_index[TYPE_CLOCK][2][0]; 
  x2 = VAR[x2].U.CLOCK.CLOCK_INDEX; 
  x3 = variable_index[TYPE_CLOCK][3][0]; 
  x3 = VAR[x3].U.CLOCK.CLOCK_INDEX; 
  
  RT[fxp = RT_TOP++] = crd_atom(ZONE[0][x1], -20); 
  RT[fxp] = red_bop(OR, RT[fxp], crd_atom(ZONE[x1][0], 10)); 
  RT[pstart = RT_TOP++] = NORM_TRUE; 
  pstop = pstart; 
  
  exit(0); 
}
  /* test_zone3() */ 
  
  
  
  
  
void	test_zone4() {  
  int	fxp, pstart, pstop, x1, x2, x3; 
  
  x1 = variable_index[TYPE_CLOCK][1][0]; 
  x1 = VAR[x1].U.CLOCK.CLOCK_INDEX; 
  x2 = variable_index[TYPE_CLOCK][2][0]; 
  x2 = VAR[x2].U.CLOCK.CLOCK_INDEX; 
  
  RT[fxp = RT_TOP++] = NORM_FALSE; 
  RT[pstop = pstart = RT_TOP++] = crd_atom(ZONE[0][x1], 0); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x1][0], 30); 
//  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[0][x2], -10); 
//  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x2][0], 29); 
  RT[fxp] = crd_atom(ZONE[0][x1], -20); 
  RT[fxp] = red_bop(OR, RT[fxp], crd_atom(ZONE[x1][0], 10)); 
//  RT[fxp] = red_bop(AND, RT[fxp], RT[pstart]); 
  
  exit(0); 
}
  /* test_zone4() */ 
  
  
  
 void	test_zone5() {  
  int	fxp, pstart, pstop, x1, x2, x3; 
  
  x1 = variable_index[TYPE_CLOCK][1][0]; 
  x1 = VAR[x1].U.CLOCK.CLOCK_INDEX; 
  x2 = variable_index[TYPE_CLOCK][2][0]; 
  x2 = VAR[x2].U.CLOCK.CLOCK_INDEX; 
  
  RT[fxp = RT_TOP++] = NORM_FALSE; 
  RT[pstop = pstart = RT_TOP++] = crd_atom(ZONE[0][x1], 0); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x1][0], 30); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[0][x2], -10); 
  RT[pstart] = crd_one_constraint(RT[pstart], ZONE[x2][0], 29); 
  RT[fxp] = crd_atom(ZONE[0][x1], -20); 
  RT[fxp] = red_bop(OR, RT[fxp], crd_atom(ZONE[x1][0], 10)); 
  RT[fxp] = red_bop(AND, RT[fxp], RT[pstart]); 
  
  exit(0); 
}
  /* test_zone5() */ 
  
  
  
  
  
void	init_zone_management()
{
  int			wp, c1, c2, w, t1, t2; 
  struct red_type	*conj1, *conj2, *result; 

  cross_count = 0;

  flag_clock = (int *) malloc(CLOCK_COUNT * sizeof(int)); 
  easy_concavity = (struct easy_concavity_arc_type *) 
    malloc(easy_concavity_limit * sizeof(struct easy_concavity_arc_type)); 
  for (c1 = 0; c1 < easy_concavity_limit; c1++) { 
    easy_concavity[c1].status = 0; 
    easy_concavity[c1].augmented_lb_ub_list = NULL; 
    easy_concavity[c1].augmented_shared_diagonal_list = NULL; 
    easy_concavity[c1].child_result = NULL; 
  } 

/*
  RED_BYPASS_FWD = red_bypass_fwd_ARRAY;
  RED_BYPASS_BCK = red_bypass_bck_ARRAY;
*/
  RED_BYPASS_FWD = red_bypass_DOWNWARD;
  RED_BYPASS_BCK = red_bypass_DOWNWARD;
  
  /* The following structure RED_INVARIANCE_CONTINUITY is to be used repetitively 
   * in backward time progression's inner quantification.  
   */
  #ifdef RED_DEBUG_ZONE_MODE
  print_resources("init_zone_management, before path processing.\n"); 
  #endif 
  
  #ifdef RED_DEBUG_ZONE_MODE
  print_resources("init_zone_management, after path processing.\n"); 
  #endif 

  init_zapprox_management();
  initialize_gch(); 
/*
  flag_progress = (int *) malloc(CLOCK_COUNT*sizeof(int));
  flag_new_progress = (int *) malloc(CLOCK_COUNT*sizeof(int));

  BYPASS_LARGE_BOUND = (2*CLOCK_POS_INFINITY + 3)*(2 * CLOCK_POS_INFINITY+3);

  ZONE_RECORD = (int **) malloc(CLOCK_COUNT * sizeof(int *));
  for (ci = 0; ci < CLOCK_COUNT; ci++) {
    ZONE_RECORD[ci] = (int *) malloc(CLOCK_COUNT * sizeof(int));
    for (cj = 0; cj < CLOCK_COUNT; cj++)
      ZONE_RECORD[ci][cj] = CLOCK_POS_INFINITY;
  }
*/

/*
  test_time_progress(); 
  test_time_progress1(); 
  exit(0); 
*/

//  test_zone5(); 
}
/* init_zone_management() */








test_bypass_fwd() 
{
  int			conj, result;

  RT[conj = RT_TOP++] = crd_atom(ZONE[0][1], -50); 
  RT[conj] = red_bop(AND, RT[conj], crd_atom(ZONE[2][0], 30)); 
  RT[conj] = red_bop(AND, RT[conj], crd_atom(ZONE[2][1], 0));

  RT[result = RT_TOP++] = crd_atom(ZONE[0][1], -50); 
  RT[result] = red_bop(AND, RT[result], crd_atom(ZONE[2][0], 61)); 
  RT[result] = red_bop(AND, RT[result], crd_atom(ZONE[2][1], 20)); 

  RT[result] = red_bop(OR, RT[result], RT[conj]); 

  fprintf(RED_OUT, "\nbefore test_bypass_fwd()\n"); 
  red_print_graph(RT[result]);
  RT[result] = RED_BYPASS_FWD(result, 0); 
  fprintf(RED_OUT, "\nafter test_bypass_fwd()\n");
  red_print_graph(RT[result]);

}
/* test_bypass_fwd() */ 


