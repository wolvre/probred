/*********************************************************************
 * 06/05/31 One bug is how do you deal with the case that has xi=0 for all plant roles. 
 * In the ineq_to_role, we should only consider the time-progress. 
 * In the eq_to_both, we can consider both the time-progress case and the opponent-only cases. 
 * But now the time-progress case in the eq_to_both is not considered since SYNC_ITERATIVE 
 * does not execute one with zero party count. 
 * 
 *
 * For equivalence-checking and inclusion-checking, at this moment, we 
 * do not support read-write through synchronization variables.  
 * We define the equivalence with two conditions. 
 *  1. writing to global variables are the same.  
 *     We have one further restriction in this regard. 
 *     If the SPEC and the MODL want to write to a global variable, 
 *     then it must do it in the following way. 
 *     If there is already a sync between the ENVR and the plants in the sync transition, 
 *     then the write-through consistency must be carried out with the the transitions 
 *     involved in the synchronization.  
 *     If there is no such sync, then we create a pseudo sync between the SPEC and the MODL.  
 *  2. event synchronizations are the same.  
 
 * 06/07/27 characterization of timed disparity 
    
    fixpoint w
    
    A) \eta = \forall (e0,e1)
                \forall t(
                  (\eta+t\models (e0,e1) && \forall t'(t'<=t && 0<=t' && w+t')) 
                     --> \exists (v1,t1)...(vk,tk) (tk-t1==t && vk\models (e0,e1,e2))
                   )
                 
       \eta = \forall (e0,e1) 
                 \neg \exists t \neg 
                   (   (\eta+t\models (e0,e1) && \forall t'(t'<=t&& 0<=t' && w+t'))
                    && \neg \exists (v1,t1)...(vk,tk) with only e2 transitions such that  
                          (tk-t1==t && vk\models (e0,e1,e2))
                    )
    
    B) \eta = ((\forall t \eta+t\models w) 
                --> \exists non-Zeno \rho with only e2 transitions
               )
    
    In the evaluatoin of \exists nonZeno \always (-x+t<0 || \eta), 
    ModalClock is to be interpreted as ModalClock-delta.
    So we don't add -ModalClock <=0 to the body of exists always.  
    
    Then when we eliminate ModalClock with ModalClock==0, we replace ModalClock with -delta.  
    
 */
 
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>


#include "treeman.h" 
#include "treeman.e" 

#include "redbasics.h"  
#include "redbasics.e"  

#include "redbop.h"  
#include "redbop.e"  

#include "zone.h"  
#include "zone.e"  

#include "hybrid.e" 

#include "redparse.h" 
#include "redparse.e"  

#include "exp.e" 

#include "hashman.h" 
#include "hashman.e" 

#include "access_analysis.e"

#include "fxp.h"
#include "fxp.e" 
#include "action.e" 
#include "inactive.e" 

#include "bisim.h" 

#include "redgame.h" 
#include "redgame.e" 


/* The goal is to enforce that variable-value passing between the three parties: 
 * s (spec), d (dscription), and e (environment) can only happen through global variables. 
 * Currently, we do this purely in syntax level. 
 * We classify the synchronization labels into six classes. 
 * s-s, d-d, e-e, s-d, s-e, d-e
 *
 * Namely, the following synchronizations are forbitten. 
 * 1. class s-d is totally forbidden.  
 * 2. a synchronization label in classes s-s, d-d, e-e can only be used in one class. 
 * 3. a synchronization label in classes s-e and d-e can only be used in those two classes.
 * 4. a synchronization label in classes s-e and d-e may not use sync quantifiers. 
 * However, there still could be danger of breaking-down through indirections.  
 * Thus while calculating indirections, we shall restrict that indirections only happen 
 * among processes of one party.  
 *
 * Algorithmically, we only use the transition table to check all the restrictions.  
 */ 

#define MASK_GAME_SYNC_SPEC_REC		(0x01000)
#define MASK_GAME_SYNC_SPEC_XMT		(0x02000)
#define MASK_GAME_SYNC_MODL_REC		(0x04000)
#define MASK_GAME_SYNC_MODL_XMT		(0x08000)
#define MASK_GAME_SYNC_ENVR_REC		(0x10000)
#define MASK_GAME_SYNC_ENVR_XMT		(0x20000)
#define MASK_SYNC_QUANTIFIER_XMT	(0x00001) 
#define MASK_SYNC_QUANTIFIER_REC	(0x00002) 

int	IT_EC;  /* ITERATION COUNT OF THE GREATEST FIXPOINT. */ 
int	cecg = 0; 

struct red_type	
  *RED_PLANTS_ENVR_INVARIANCE,  
  *RED_GAME_SYNC_BULK_PRE, 
  *RED_GAME_SYNC_ALL_PRE, 
  **RED_GAME_SYNC_NEG_PRE,  
  **RED_GAME_INV_DIFF; 

  /* In the following, we need to declare five slots in the 
   * pointer arrays because 
   *     FLAG_GAME_SPEC is 0x2 
   * and FLAG_GAME_MODL is 0x4.   
   * Thus we can use the value of the two constants to address the 
   * two diagrams record in the five-slot arrays.  
   * Thus only slots 2 and 4 are used in the five slots. 
   * That is a little big a waste.  
   * But, hey, this problems are difficult. 
   * This is only a little overhead. 
   * We don't want to worry about it at the moment. 
   */
int
  /* This INEQ_XTION_SYNC_BULK is used to hold the candidate state pairs for 
   * those inequivalent pairs to be eliminated from the bisimulation 
   * image at a particular iteration.  
   * Note that INEQ_XTION_SYNC_BULK are for those triggering conditions of 
   * the synchronous transitions in the sync_bulk diagram.  
   * Initially, INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL] is equal to the 
   * whole state-space for the triggering condition of 
   * all the synchronous transitions in the 
   * sync bulk diagram of the dscription automata. 
   * INEQ_XTION_SYNC_BULK[FLAG_GAME_SPEC] is equal to the 
   * whole state-space for the triggering condition of 
   * all the synchronous transitions in the 
   * sync bulk diagram of the specification automata. 
   */ 
//	INEQ_XTION_SYNC_BULK[3], 
  /* GAME_ROLE_INVARIANCE is used to hold the invariance condition 
   * of a role (i.e., MODL or SPEC) together with the ENVR (environment) 
   * role.  
   * Thus it describes the invariance of a role together with the 
   * environment. 
   * It is used to help us computing the INEQ_XTION[flag_role] 
   * and INEQ_XTION_SYNC_BULK[flag_role].  
   * In the computation of INEQ_XTION[flag_role] 
   * and INEQ_XTION_SYNC_BULK[flag_role], we only care about 
   * the state-space of flag_role and the environment.  
   */  
	GAME_ROLE_INVARIANCE[3], 
  /* GAME_ROLE_INVARIANCE is used to hold the invariance condition 
   * of a role (i.e., MODL or SPEC) together with the ENVR (environment) 
   * role.  
   * Thus it describes the invariance of a role together with the 
   * environment. 
   * It is used to help us computing the INEQ_XTION[flag_role] 
   * and INEQ_XTION_SYNC_BULK[flag_role].  
   * In the computation of INEQ_XTION[flag_role] 
   * and INEQ_XTION_SYNC_BULK[flag_role], we only care about 
   * the state-space of flag_role and the environment.  
   */  
	GAME_ROLE_INVARIANCE_SHARED_CONCAVITY[3], 
  /* GAME_ROLE_INITIAL is used to hold the initial conditions 
   * respectively of the two roles and the environment. 
   * Thus GAME_ROLE_INITIAL[FLAG_GAME_MODL] is the initial condition of 
   * the description automata and the environment. 
   * GAME_ROLE_INITIAL[FLAG_GAME_SPEC] is the initial condition of 
   * the specification automata and the environment. 
   */ 
	GAME_ROLE_INITIAL[3], 
  /* XI_ROLE_SYNC_BULK holds the diagram for the 
   * synchronous transition bulks respectively of the two roles. 
   * Thus XI_ROLE_SYNC_BULK[FLAG_GAME_MODL] is the synchronous 
   * transition bulk diagram of 
   * the description automata and the environment. 
   * Thus XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC] is the synchronous 
   * transition bulk diagram of 
   * the specification automata and the environment. 
   */ 
	XI_ROLE_SYNC_BULK[3]; 


/* To be used after prepare_sync_xtions() 
 */ 
struct ps_exp_type 
  *GAME_FAIRNESS_EXP, *GAME_FAIRNESS_EXP_AUX, 
  *GAME_MODL_EXP, *GAME_SPEC_EXP, *GAME_ENVR_EXP; 

  
int	FLAG_GAME_RSP_ROLE, 
	GAME_NEWLY_REMOVED_IN_LAST_ITR, // for on-the-fly GFP
	GAME_NEWLY_REMOVED_IN_THIS_ITR, // for on-the-fly GFP
	*pxtion, 
	*stutter_xtion; 



char	*role_name(flag_role)
	int	flag_role; 
{ 
  switch (flag_role) { 
  case FLAG_GAME_SPEC: 
    return("SPEC"); 
    break; 
  case FLAG_GAME_MODL:
    return("MODL");  
    break; 
  case FLAG_GAME_ENVR: 
    return("ENVR"); 
    break; 
  default: 
    return("UNKNOWN"); 
  } 	
}
  /* role_name() */ 



  

char	sxi_name[10]; 
char	*sxi_string(int sxi) { 
  if (sxi == FLAG_GAME_SYNC_BULK) 
    return("BULK"); 
  else if (sxi < 0 || sxi >= 100000000) { 
    fprintf(RED_OUT, "sync xtion index %1d out of range.\n", sxi); 
    return("oo"); 
  } 
  else { 
    sprintf(sxi_name, "%1d", sxi); 
    return(sxi_name); 	
  } 
} 
  /* sxi_string() */ 


inline void	check_bisim_error(d, it, flag_role, flag_ec_sync) 
  struct red_type 	*d; 
  int			it, flag_role, flag_ec_sync; 
{ 
  int	pi, x1, x2; 
  
//  if (it == 1) { 
    d = ddd_one_constraint(d, 
      variable_index[TYPE_POINTER][0][0], 
      0, 0
    ); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 
      1, 1
    ); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 
      5, 5
    ); 
    for (pi = 3; pi <= PROCESS_COUNT; pi++) { 
      d = ddd_one_constraint(
        d, variable_index[TYPE_DISCRETE][pi][0], 
        5, 5
      ); 
    }     
    x1 = VAR[variable_index[TYPE_CLOCK][1][0]].U.CLOCK.CLOCK_INDEX; 
    x2 = VAR[variable_index[TYPE_CLOCK][2][0]].U.CLOCK.CLOCK_INDEX; 
    d = crd_one_constraint(d, ZONE[x1][0], 0); 
    d = crd_one_constraint(d, ZONE[x2][0], 0); 
    RT[x1 = RT_TOP++] = d; 
    RT[x1] = red_hull_normalize(x1); 
    d = RT[x1]; 
    RT_TOP--; // x1 
    if (d != NORM_FALSE) { 
      fprintf(RED_OUT, "IT_EC%1d, %s %s, detected first target removed:\n", 
        ITERATION_COUNT, role_name(flag_role), sxi_string(flag_ec_sync)  
      ); 
      red_print_graph(d); 
    } 
//  }
}
  /* check_bisim_error() */ 


inline void	check_bisim_state(s, d, it, flag_role, flag_ec_sync) 
  char			*s; 
  struct red_type 	*d; 
  int			it, flag_role, flag_ec_sync; 
{ 
  int	pi, x1, x2; 
  
  if (   it == 2
      && flag_role == FLAG_GAME_MODL
      && flag_ec_sync == 12
      ) { 
    d = ddd_one_constraint(d, 
      variable_index[TYPE_POINTER][0][0], 
      0, 0
    ); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 
      1, 1
    ); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 
      5, 5
    ); 
    for (pi = 3; pi <= PROCESS_COUNT; pi++) { 
      d = ddd_one_constraint(
        d, variable_index[TYPE_DISCRETE][pi][0], 
        5, 5
      ); 
    }     
    x1 = VAR[variable_index[TYPE_CLOCK][1][0]].U.CLOCK.CLOCK_INDEX; 
    x2 = VAR[variable_index[TYPE_CLOCK][2][0]].U.CLOCK.CLOCK_INDEX; 
    d = crd_one_constraint(d, ZONE[x1][0], 0); 
    d = crd_one_constraint(d, ZONE[x2][0], 0); 
    RT[x1 = RT_TOP++] = d; 
    RT[x1] = red_hull_normalize(x1); 
    d = RT[x1]; 
    RT_TOP--; // x1 
    if (d != NORM_FALSE) { 
      fprintf(RED_OUT, "IT_EC%1d, %s %s, %s:\n", 
        ITERATION_COUNT, role_name(flag_role), sxi_string(flag_ec_sync), s  
      ); 
      red_print_graph(d); 
    } 
  }
}
  /* check_bisim_state() */ 



  
void	init_ec_management() { 
  if (!pxtion) {
    pxtion = ((int *) malloc(PROCESS_COUNT*sizeof(int)))-1; 
    stutter_xtion = ((int *) malloc(PROCESS_COUNT*sizeof(int)))-1; 
  } 
  
  SPEC_EXP = (struct ps_exp_type *) malloc(sizeof(struct ps_exp_type)); 
  SPEC_EXP->type = RED; 
  SPEC_EXP->u.rpred.red = NORM_NO_RESTRICTION; 

  GSTATUS[INDEX_GAME_ROLES] 
  = GSTATUS[INDEX_GAME_ROLES] | FLAG_GAME_ROLES_CHANGED; 
/*  
  INEQ_XTION_SYNC_BULK[0] = -1;  
  INEQ_XTION_SYNC_BULK[FLAG_GAME_SPEC] = INDEX_GAME_INEQ_XTION_SYNC_BULK_SPEC;  
  INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL] = INDEX_GAME_INEQ_XTION_SYNC_BULK_MODL;  
*/ 
  GAME_ROLE_INVARIANCE[0] = -1;  
  GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC] = INDEX_GAME_SPEC_INVARIANCE;  
  GAME_ROLE_INVARIANCE[FLAG_GAME_MODL] = INDEX_GAME_MODL_INVARIANCE;  

/* The following RT indices have been moved to the hash tables. 
  GAME_ROLE_FAIRNESS[0] = -1;  
  GAME_ROLE_FAIRNESS[3] = -1;  
  GAME_ROLE_FAIRNESS[4] = -1;  
  GAME_ROLE_FAIRNESS[5] = -1;  
  GAME_ROLE_FAIRNESS[6] = -1;  
  GAME_ROLE_FAIRNESS[FLAG_GAME_SPEC] = INDEX_GAME_FAIRNESS_SPEC;  
  GAME_ROLE_FAIRNESS[FLAG_GAME_MODL] = INDEX_GAME_FAIRNESS_MODL;  
  GAME_ROLE_FAIRNESS[MASK_GAME_ROLES] = INDEX_GAME_FAIRNESS_ALL;  
*/ 

  GAME_ROLE_INITIAL[0] = -1;  
  GAME_ROLE_INITIAL[FLAG_GAME_SPEC] = INDEX_GAME_SPEC_INITIAL;  
  GAME_ROLE_INITIAL[FLAG_GAME_MODL] = INDEX_GAME_MODL_INITIAL;  

  XI_ROLE_SYNC_BULK[0] = -1;  
  XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC] = XI_RESTRICTION_SPEC_FWD;  
  XI_ROLE_SYNC_BULK[FLAG_GAME_MODL] = XI_RESTRICTION_MODL_FWD;  

} 
  /* init_ec_management() */ 
  
  
struct red_type	*red_test_bisim(d, s) 
	struct red_type	*d; 
	char		*s; 
{ 
  fprintf(RED_OUT, "in red_test_bisim(), %s.\n", s); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 5,5);
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 7,8);
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 11, 11);
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 11, 11);
  red_print_graph(d); 
  
  return(d); 
}
  /* red_test_bisim() */
  
  
  
  
  
  
struct red_type	*echeck(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 2, 2); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 0, 0); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck() */ 
  
struct red_type	*echeck2(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 1, 1); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck2() */ 
  
  


struct red_type	*echeck3(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck3() */ 
  
  
struct red_type	*echeck4(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_POINTER][0][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck4() */ 
  
  
struct red_type	*echeck5(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_POINTER][0][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck5() */ 
  
  

struct red_type	*echeck7(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_POINTER][0][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 5, 5); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck7() */ 
  
  

struct red_type	*echeck6(d) 
	struct red_type	*d; 
{ 
  if (ITERATION_COUNT == 1) 
    return(echeck7(d)); 
    
  d = ddd_one_constraint(d, variable_index[TYPE_POINTER][0][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 5, 5); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck6() */ 
  
  

struct red_type	*echeck8(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck8() */ 
  
  
struct red_type	*echeck9(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck9() */ 
  
  
struct red_type	*echeck10(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck10() */ 
  
  


struct red_type	*echeck11(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck11() */ 




struct red_type	*echeck11_1(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 6, 6); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck11_1() */ 
  
  


struct red_type	*echeck11_2(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 6, 6); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck11_2() */ 
  
  

struct red_type	*echeck12(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck12() */ 



struct red_type	*echeck13(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 5, 5); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck13() */ 



struct red_type	*echeck14(d) 
	struct red_type	*d; 
{ 
  switch (ITERATION_COUNT) { 
  case 1: 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
    break; 
  case 2: 
    d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
    d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 6, 6); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
    d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 0, 0); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 0, 0); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
    break; 
  } 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck14() */ 



struct red_type	*echeck15(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 1, 1); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 6, 6); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 3, 3); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 3, 3); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck15() */ 



struct red_type	*echeck16(d) 
	struct red_type	*d; 
{ 
  switch (ITERATION_COUNT) { 
  case 1: 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
    break; 
  case 2:
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 3, 3); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 3, 3); 
    break; 
  } 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck16() */ 



struct red_type	*echeck17(d) 
	struct red_type	*d; 
{ 
  switch (ITERATION_COUNT) { 
  case 1: 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
    break; 
  case 2:
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 1, 1); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 3, 3); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
    d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
    break; 
  } 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck17() */ 




struct red_type	*echeck17_1(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][1][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][2][0], 6, 6); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][3][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][4][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck17_1() */ 




struct red_type	*echeck17_2(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 2, 2); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 4, 4); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 4, 4); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck17_2() */ 



struct red_type	*echeck18_2(d) 
	struct red_type	*d; 
{ 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][0], 0, 0); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][0], 5, 5); 
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][0], 5, 5); 
  red_print_graph(d); 
  return(d); 	
}
  /* echeck18_2() */ 




void	print_process_roles() { 
  int	pi; 
  
  fprintf(RED_OUT, "\n****************************************\n"); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
      fprintf(RED_OUT, " %1d:SPEC;", pi); 
      break; 
    case FLAG_GAME_MODL: 
      fprintf(RED_OUT, " %1d:MODL;", pi); 
      break; 
    case FLAG_GAME_ENVR: 
      fprintf(RED_OUT, " %1d:ENVR;", pi); 
      break; 
    } 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
} 
  /* print_process_roles() */  
  
  

 
  
  
/********************************************************
 * This procedure computes simple clock restrictions EMR 
 * that can be derived from 
 * syntax of the mode transition systems. 
 * A mode pair (md, ms), one for the MODL and the other for SPEC, 
 * are not clock-equality-enforcing if the following are true. 
 * We can do this with the greatest-fixpoint evaluation.  
 * 
 * If the initial condition allows for (md,ms) with no strict local clock inequality, 
 * then (md,ms) is not in the initial EMR image.  
 * If (md,ms) can be entered from another mode pair with transitions that reset clocks 
 * without events, global writings, and punctual timing constraints, 
 * then (md,ms) is not in the initial EMR image.  
 * After the initial EMR image is computed, then we do the folloiwng greatest fixpoint calculation. 
 *   If (md,ms) can be entered from a transition from another pair not in the EMR image 
 *   that does not reset clocks, then (md,ms) is not in EMR either. 
 */
int	IT_EMR; 

struct red_type	*emr_check1(d)
	struct red_type	*d; 
{
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][1][OFFSET_MODE], 0, 0); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][2][OFFSET_MODE], 5, 5); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][3][OFFSET_MODE], 5, 5); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][4][OFFSET_MODE], 3, 3); 	
  d = ddd_one_constraint(d, variable_index[TYPE_DISCRETE][5][OFFSET_MODE], 5, 5); 	
  return(d); 
}
  /* emr_check1() */  
  
  
  
  

/* The information collected in this procedure serves two purposes. 
 *  1. We use it in this procedure to check if there is any anomaly in using the synchronizations. 
 *     One example is to check if there are any synchronizations between the two plants, MODL 
 *     and the SPEC. 
 *  2. We then use it in generating risk condition that results from a synchronization 
 *     that is not triggerible between SPEC and ENVR while triggerible between 
 *     MODL and ENVR. (or vice versa)
 */
void	signal_read_write_locals_through_synchronization() {
  int	flag_error, xi, ipi, pi, sci, sgi, gi, gvi, flag_ops, 
	mask_game_sync_roles_rec, mask_game_sync_roles_xmt; 

  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nprocess' roles:\n"); 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
      fprintf(RED_OUT, "  %1d is spec\n", pi); 
      break; 
    case FLAG_GAME_MODL: 
      fprintf(RED_OUT, "  %1d is modl\n", pi); 
      break; 
    case FLAG_GAME_ENVR: 
      fprintf(RED_OUT, "  %1d is envr\n", pi); 
      break; 
  } } 
  #endif 
  
  for (xi = 1; xi < XTION_COUNT; xi++) { 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "\n..................................\n"); 
    fprintf(RED_OUT, "check illegal sim synch in xi=%1d.\n", xi); 
    #endif 
    
    mask_game_sync_roles_rec = 0; 
    mask_game_sync_roles_xmt = 0; 
    for (ipi = 0; ipi < XTION[xi].process_count; ipi++) { 
      pi = XTION[xi].process[ipi]; 
      #ifdef RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "  check illegal sim synch in xi=%1d at proc %1d as ", 
        xi, pi
      ); 
      #endif 
      
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        #ifdef RED_DEBUG_BISIM_MODE
        fprintf(RED_OUT, "spec\n"); 
        #endif 
        
        mask_game_sync_roles_rec 
        = mask_game_sync_roles_rec | MASK_GAME_SYNC_SPEC_REC; 
        mask_game_sync_roles_xmt 
        = mask_game_sync_roles_xmt | MASK_GAME_SYNC_SPEC_XMT; 
        break; 
      case FLAG_GAME_MODL: 
        #ifdef RED_DEBUG_BISIM_MODE
        fprintf(RED_OUT, "modl\n"); 
        #endif 
        
        mask_game_sync_roles_rec 
        = mask_game_sync_roles_rec | MASK_GAME_SYNC_MODL_REC; 
        mask_game_sync_roles_xmt 
        = mask_game_sync_roles_xmt | MASK_GAME_SYNC_MODL_XMT; 
        break; 
      case FLAG_GAME_ENVR: 
        #ifdef RED_DEBUG_BISIM_MODE
        fprintf(RED_OUT, "envr\n"); 
        #endif 

        mask_game_sync_roles_rec 
        = mask_game_sync_roles_rec | MASK_GAME_SYNC_ENVR_REC; 
        mask_game_sync_roles_xmt 
        = mask_game_sync_roles_xmt | MASK_GAME_SYNC_ENVR_XMT; 
        break; 
      }      
      #ifdef RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, "  raw role rec bits: %x; xmt bits: %x\n", 
        mask_game_sync_roles_rec, mask_game_sync_roles_xmt
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
  	
    for (sci = 0; sci < XTION[xi].sync_count; sci++) { 
      sgi = XTION[xi].sync[sci].sync_index; 
      switch (XTION[xi].sync[sci].type) {
      case -1: // SENDING 
        GSYNC[sgi].STATUS = GSYNC[sgi].STATUS | mask_game_sync_roles_xmt; 
        switch (XTION[xi].sync[sci].status) { 
        case FLAG_ADDRESS_HOLDER: 
        case FLAG_ADDRESS_ENFORCER: 
          GSYNC[sgi].STATUS = GSYNC[sgi].STATUS | MASK_SYNC_QUANTIFIER_XMT; 
          break; 
        } 
        break; 
      case 1: // RECEIVING 
        GSYNC[sgi].STATUS = GSYNC[sgi].STATUS | mask_game_sync_roles_rec; 
        switch (XTION[xi].sync[sci].status) {  
        case FLAG_ADDRESS_HOLDER: 
        case FLAG_ADDRESS_ENFORCER: 
          GSYNC[sgi].STATUS = GSYNC[sgi].STATUS | MASK_SYNC_QUANTIFIER_REC; 
          break; 
        } 
        break; 
      } 
      #ifdef RED_DEBUG_BISIM_MODE
      fprintf(RED_OUT, 
        "Now recording the sync of xi=%1d, sci=%1d, sgi=%1d, %1d:%s:%x\n", 
        xi, sci, sgi, GSYNC[sgi].VAR_INDEX, 
        VAR[GSYNC[sgi].VAR_INDEX].NAME, GSYNC[sgi].STATUS 
      ); 
      fflush(RED_OUT); 
      #endif 
    } 
  } 
  
  flag_error = TYPE_FALSE; 
  for (gi = 0; gi < GLOBAL_COUNT[TYPE_SYNCHRONIZER]; gi++) { 
    gvi = GSYNC[gi].VAR_INDEX; 
    
    /* Firstly, check if there is any synchronizations between spec and dscr. */ 
    if (   (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_REC) 
	    && (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_XMT) 
	    )
	|| (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_XMT) 
	    && (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_REC) 
	    )
	) {
      fprintf(RED_OUT, "Error: In equivalence checking, a synchronizer %1d:%s \n", 
	      gvi, VAR[gvi].NAME
              ); 
      fprintf(RED_OUT, "       between spec and model is detected.\n"); 
      flag_error = TYPE_TRUE; 
      bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
    }
    /* Secondly, check if an autonomous sync is also used for cross-group sync. */ 
    if (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_REC) 
	&& (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_XMT) 
	) {
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_MODL_REC | MASK_GAME_SYNC_MODL_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous spec synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between spec and model.\n"); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      } 
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_ENVR_REC | MASK_GAME_SYNC_ENVR_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous spec synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between spec and environment.\n"); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      } 
    }
    if (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_REC) 
	&& (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_XMT) 
	) {
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_SPEC_REC | MASK_GAME_SYNC_SPEC_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous description synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between spec and model.\n"); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      } 
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_ENVR_REC | MASK_GAME_SYNC_ENVR_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous description synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between model and environment.\n"); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      } 
    }
/*
    if (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_REC) 
	&& (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_XMT) 
	) {
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_SPEC_REC | MASK_GAME_SYNC_SPEC_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous environment synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between spec and environment.\n"); 
        flag_error = TYPE_TRUE; 
      } 
      if (GSYNC[gi].STATUS & (MASK_GAME_SYNC_MODL_REC | MASK_GAME_SYNC_MODL_XMT)) { 
        fprintf(RED_OUT, "Error: In equivalence checking an autonomous environment synchronizer %1d:%s \n", 
        	gvi, VAR[gvi].NAME
        	); 
        fprintf(RED_OUT, "       is also used in synchronization(s) between description and environment.\n"); 
        flag_error = TYPE_TRUE; 
      }  
    }
*/
    /* Thirdly, synchronizations between spec and envr cannot use quantifiers. */ 
    if (GSYNC[gi].STATUS & (MASK_SYNC_QUANTIFIER_REC | MASK_SYNC_QUANTIFIER_XMT)) {
/*
      if (   (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_REC) 
	      && (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_XMT) 
	      ) 
          || (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_SPEC_XMT) 
	      && (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_REC) 
	      ) 
	  ) {
        fprintf(RED_OUT, "Error: In equivalence checking, a quantified variable is used in  \n"); 
        fprintf(RED_OUT, 
          "       a synchronization %1d:%1d:%s between spec and environment.\n", 
	  gi, gvi, VAR[gvi].NAME
	); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      }
      if (   (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_REC) 
	      && (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_XMT) 
	      ) 
          || (   (GSYNC[gi].STATUS & MASK_GAME_SYNC_MODL_XMT) 
	      && (GSYNC[gi].STATUS & MASK_GAME_SYNC_ENVR_REC) 
	      ) 
	  ) {
        fprintf(RED_OUT, 
          "Error: In equivalence checking, a quantified variable is used in  \n"
        ); 
        fprintf(RED_OUT, 
          "       a synchronization %1d:%1d:%s between spec and environment.\n", 
	  gi, gvi, VAR[gvi].NAME
	); 
        flag_error = TYPE_TRUE; 
        bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
      }
*/
    }
  } 
  if (flag_error) { 
    bk("Error: Illegal synchronization(s) in equivalence-checking. \n"); 
  } 
}
  /* signal_read_write_locals_through_synchronization() */
  
  
  

struct a23tree_type	*ec_tree; 

/* In this procedure, we not only eliminate transition combinations with the following 
 * properties. 
 * 
 *  1. cooperation between spec and dscr
 *  2. write-through to either dscr or spec by envr. 
 *  3. write-through and readings between locals of dscr and spec.  
 */

int	target_roles_in_red; 

int	rec_role_in_red(d)
     struct red_type	*d;
{
  int				pi, ci, result; 
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(TYPE_FALSE);

  ce = cache2_check_result_key(
    OP_ROLE_IN_RED, d, (struct red_type *) target_roles_in_red
  ); 
  if (ce->result) {
    return((int) ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    if (pi && (PROCESS[pi].status & target_roles_in_red)) {
      result = TYPE_TRUE; 
      break; 
    } 
    pi = VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (pi && (PROCESS[pi].status & target_roles_in_red)) {
      result = TYPE_TRUE; 
      break; 
    } 
    for (ci = 0; ci < d->u.crd.child_count; ci++) 
      if (rec_role_in_red(d->u.crd.arc[ci].child)) { 
      	result = TYPE_TRUE; 
      	break; 
      } 
      
    result = TYPE_FALSE; 
    break; 

  case TYPE_HRD: 

    break; 
        
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  default: 
    pi = VAR[d->var_index].PROC_INDEX; 
    if (pi && (PROCESS[pi].status & target_roles_in_red)) 
      result = TYPE_TRUE; 
    else 
      result = TYPE_FALSE; 
  }
  return((int) (ce->result 
    = (struct red_type *) result
  ) ); 
}
  /* rec_role_in_red() */

  
  

int	role_in_red(d, ec_roles) 
	struct red_type	*d; 
	int		ec_roles; 
{ 
  int	result;

  if (d == NORM_FALSE)
    return(TYPE_FALSE);

  target_roles_in_red = ec_roles; 

  result = rec_role_in_red(d);
  
  return(result);
}
  /* role_in_red() */  
  


int	role_in_exp(exp, pi, ec_roles) 
	struct ps_exp_type	*exp; 
	int			pi, ec_roles; 
{ 
  int	flag_address = 0;

  switch(exp->type){
  case TYPE_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QFD: 
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_MODE_INDEX: 
  case TYPE_PROCESS_COUNT: 
    return(TYPE_FALSE);  

  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
/*
    if (exp->u.atom.indirect_count) { 
      fprintf(RED_OUT, "\nError: Indirection is not supported in equivalence checking at this moment.\n"); 
      bk(" "); 
    } 
    else if (   ec_roles == (FLAG_GAME_SPEC | FLAG_GAME_MODL) 
	     && exp->u.atom.exp_base_proc_index->type == TYPE_POINTER
	     ) { 
      fprintf(RED_OUT, "\nError: quantified synchronization is not supported from ENVIRONMENT in equivalence checking at this moment.\n"); 
      bk(" ");     	
    } 
*/
    if (!(exp->u.atom.var->status & FLAG_LOCAL_VARIABLE)) 
      return(TYPE_FALSE); 
    pi = get_address(exp->u.atom.exp_base_proc_index, pi, &flag_address); 
    if (   flag_address != FLAG_SPECIFIC_VALUE  
        || (   pi > 0 
            && pi <= PROCESS_COUNT 
            && (PROCESS[pi].status & ec_roles)
        )   ) { 
      return(TYPE_TRUE); 
    } 
    else 
      return(TYPE_FALSE); 
  case TYPE_INTERVAL: 
    if (   role_in_exp(exp->u.interval.lbound_exp, pi, ec_roles)
        || role_in_exp(exp->u.interval.rbound_exp, pi, ec_roles)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
    if (   role_in_exp(exp->u.arith.lhs_exp, pi, ec_roles)
	|| role_in_exp(exp->u.arith.rhs_exp, pi, ec_roles)
	) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
  default:
    fprintf(RED_OUT, "\nHuh ? (EC parse 2) \n");
    bk(); 
  }

}
  /* role_in_exp() */ 

  

  

  
int	role_in_statement(st, pi, ec_roles) 
	struct statement_type	*st; 
	int			pi, ec_roles; 
{ 
  int	i, flag_address; 
  
  if (!st) 
    return(TYPE_FALSE); 

  switch (st->op) { 
  case UNCHANGED: 
    return(TYPE_FALSE); 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    if (role_in_exp(st->u.act.lhs, pi, ec_roles)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_GUARD: 
    if (role_in_exp(st->u.guard.cond, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_ERASE: 
    if (role_in_exp(st->u.erase.var, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    if (role_in_exp(st->u.act.rhs_exp, pi, ec_roles))
      return(TYPE_TRUE); 
    else if (role_in_exp(st->u.act.lhs, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      if (role_in_statement(st->u.seq.statement[i], pi, ec_roles)) 
        return(TYPE_TRUE);
    return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    if (role_in_red(st->u.loop.red_cond[pi], ec_roles)) 
      return(TYPE_TRUE); 
    else if (role_in_statement(st->u.loop.statement, pi, ec_roles)) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_IF: 
    if (role_in_red(st->u.branch.red_cond[pi], ec_roles)) 
      return(TYPE_TRUE); 
    else if (role_in_statement(st->u.branch.if_statement, pi, ec_roles)) 
      return(TYPE_TRUE);
    else if ((st->st_status & FLAG_STATEMENT_ELSE) && role_in_statement(st->u.branch.else_statement, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
    return(TYPE_FALSE); 
    break; 
  default: 
    fprintf(RED_OUT, "ERROR: illegal statement operation code %1d\n", st->op); 
    fflush(RED_OUT); 
    exit(0); 
  }
} 
  /* role_in_statement() */ 
  
  
  
  
int	no_read_write_to_roles(xi, pi, ec_roles) 
	int	xi, pi, ec_roles; 
{ 
  int 	ai; 
  
  if (role_in_red(XTION[xi].red_trigger[pi], ec_roles)) 
    return(TYPE_FALSE); 
  else if (role_in_statement(XTION[xi].statement, pi, ec_roles)) 
    return(TYPE_FALSE); 
  return(TYPE_TRUE); 
} 
  /* no_read_write_to_roles() */ 
  


int	write_through_to_roles_in_exp(exp, pi, ec_roles) 
	struct ps_exp_type	*exp; 
	int			pi, ec_roles; 
{ 
  int	flag_address = 0;

  switch(exp->type){
  case TYPE_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QFD: 
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
    return(TYPE_FALSE);  
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
/* 
    if (exp->u.atom.indirect_count) { 
      fprintf(RED_OUT, "\nError: Indirection is not supported in equivalence checking at this moment.\n"); 
      bk(" "); 
    } 
    else if (   ec_roles == (FLAG_GAME_SPEC | FLAG_GAME_MODL) 
	     && exp->u.atom.exp_base_proc_index->type == TYPE_POINTER
	     ) { 
      fprintf(RED_OUT, "\nError: quantified synchronization is not supported from ENVIRONMENT in equivalence checking at this moment.\n"); 
      bk(" ");     	
    } 
*/
    if (!(exp->u.atom.var->status & FLAG_LOCAL_VARIABLE)) 
      return(TYPE_FALSE); 
    pi = get_address(exp->u.atom.exp_base_proc_index, pi, &flag_address); 
    if (   flag_address != FLAG_SPECIFIC_VALUE
        || (   pi > 0 
            && pi <= PROCESS_COUNT 
            && (PROCESS[pi].status & ec_roles)
        )   ) { 
      return(TYPE_TRUE); 
    } 
    else 
      return(TYPE_FALSE); 
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
    if (   write_through_to_roles_in_exp(exp->u.arith.lhs_exp, pi, ec_roles)
	|| write_through_to_roles_in_exp(exp->u.arith.rhs_exp, pi, ec_roles)
	) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
  default:
    fprintf(RED_OUT, "\nHuh ? (EC parse 2) \n");
    bk(); 
  }

}
  /* write_through_to_roles_in_exp() */ 

  

  

  
int	write_through_to_roles_in_statement(st, pi, ec_roles) 
	struct statement_type	*st; 
	int			pi, ec_roles; 
{ 
  int	i, flag_address; 
  
  if (!st) 
    return(TYPE_FALSE); 
    
  switch (st->op) { 
  case UNCHANGED: 
    return(TYPE_FALSE); 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    if (write_through_to_roles_in_exp(st->u.act.lhs, pi, ec_roles)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_GUARD: 
    return(TYPE_FALSE); 
    break; 
  case ST_ERASE: 
    if (write_through_to_roles_in_exp(st->u.erase.var, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    if (write_through_to_roles_in_exp(st->u.act.lhs, pi, ec_roles))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      if (write_through_to_roles_in_statement(st->u.seq.statement[i], pi, ec_roles)) 
        return(TYPE_TRUE);
    return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    if (write_through_to_roles_in_statement(st->u.loop.statement, pi, ec_roles)) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_IF: 
    if (write_through_to_roles_in_statement(st->u.branch.if_statement, pi, ec_roles)) 
      return(TYPE_TRUE);
    else if (   (st->st_status & FLAG_STATEMENT_ELSE) 
	     && write_through_to_roles_in_statement(st->u.branch.else_statement, pi, ec_roles)
	     )
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_CALL: 
  case ST_RETURN: 
    return(TYPE_FALSE); 
    break; 
  default: 
    fprintf(RED_OUT, "ERROR: illegal statement operation code %1d\n", st->op); 
    fflush(RED_OUT); 
    exit(0); 
  }
} 
  /* write_through_to_roles_in_statement() */ 
  
  
  
int	no_write_through_to_roles(xi, pi, ec_roles) 
	int	xi, pi; 
{ 
  if (write_through_to_roles_in_statement(XTION[xi].statement, pi, ec_roles))
    return(TYPE_FALSE); 
  else 
    return(TYPE_TRUE); 	
} 
  /* no_write_through_to_roles() */ 
  
  

  

  

int	write_through_to_globals_in_exp(exp, pi) 
	struct ps_exp_type	*exp; 
	int			pi; 
{ 
  int	flag_address = 0;

  switch(exp->type){
  case TYPE_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QFD: 
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
    return(TYPE_FALSE);  
  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
/* 
    if (exp->u.atom.indirect_count) { 
      fprintf(RED_OUT, "\nError: Indirection is not supported in equivalence checking at this moment.\n"); 
      bk(" "); 
    } 
    else if (   ec_roles == (FLAG_GAME_SPEC | FLAG_GAME_MODL) 
	     && exp->u.atom.exp_base_proc_index->type == TYPE_POINTER
	     ) { 
      fprintf(RED_OUT, "\nError: quantified synchronization is not supported from ENVIRONMENT in equivalence checking at this moment.\n"); 
      bk(" ");     	
    } 
*/
    if (exp->u.atom.var->status & FLAG_LOCAL_VARIABLE) 
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
    if (   write_through_to_globals_in_exp(exp->u.arith.lhs_exp, pi)
	|| write_through_to_globals_in_exp(exp->u.arith.rhs_exp, pi)
	) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
  default:
    fprintf(RED_OUT, "\nHuh ? (EC parse 2) \n");
    bk(); 
  }

}
  /* write_through_to_globals_in_exp() */ 

  

  

int	write_through_to_globals_in_statement(st, pi) 
	struct statement_type	*st; 
	int			pi; 
{ 
  int	i; 
  
  if (!st) 
    return(TYPE_FALSE); 
    
  switch (st->op) { 
  case UNCHANGED: 
    return(TYPE_FALSE); 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    if (write_through_to_globals_in_exp(st->u.act.lhs, pi)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_GUARD: 
    return(TYPE_FALSE); 
  case ST_ERASE: 
    if (write_through_to_globals_in_exp(st->u.erase.var, pi)) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    if (write_through_to_globals_in_exp(st->u.act.lhs, pi))
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      if (write_through_to_globals_in_statement(st->u.seq.statement[i], pi)) 
        return(TYPE_TRUE);
    return(TYPE_FALSE); 
    break; 
  case ST_WHILE: 
    if (write_through_to_globals_in_statement(st->u.loop.statement, pi)) 
      return(TYPE_TRUE);
    else 
      return(TYPE_FALSE); 
    break; 

  case ST_IF: 
    if (write_through_to_globals_in_statement(st->u.branch.if_statement, pi)) 
      return(TYPE_TRUE);
    else if (   (st->st_status & FLAG_STATEMENT_ELSE) 
	     && write_through_to_globals_in_statement(st->u.branch.else_statement, pi)
	     )
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 

  case ST_CALL: 
  case ST_RETURN: 
    return(TYPE_FALSE); 

  default: 
    fprintf(RED_OUT, "ERROR: illegal statement operation code %1d\n", st->op); 
    fflush(RED_OUT); 
    exit(0); 
  }
} 
  /* write_through_to_globals_in_statement() */ 
  
  
  
int	no_write_through_to_globals(xi, pi) 
	int	xi, pi; 
{ 
  if (write_through_to_globals_in_statement(XTION[xi].statement, pi))
    return(TYPE_FALSE); 
  else 
    return(TYPE_TRUE); 	
} 
  /* no_write_through_to_globals() */ 
  
  
  
/* 
 */

struct a23tree_type	*elm_illegal_modl_spec_read_write_tree; 

struct red_type	*rec_eliminate_illegal_modl_spec_read_writes(f, flag_roles)
     struct red_type	*f;
     int		flag_roles; 
{
  int			pi, lb, ci, xi, new_flag_roles; 
  struct red_type	*conj, *child, *result;
  struct rec_type	*rec, *nrec; 

  if (f == NORM_NO_RESTRICTION || f == NORM_FALSE)
    return(f);

  rec = rec_new(f, (struct red_type *) flag_roles); //??
  nrec = (struct rec_type *) add_23tree(
    rec, elm_illegal_modl_spec_read_write_tree, 
    rec_comp, rec_free, rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) {
    return(nrec->result);
  }

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    if (f->u.ddd.arc[0].lower_bound == 0) {
      child = rec_eliminate_illegal_modl_spec_read_writes(
        f->u.ddd.arc[0].child, flag_roles
      ); 
      result = ddd_one_constraint(child, f->var_index, 0, 0); 
    } 
    else 
      result = NORM_FALSE; 
    pi = VAR[f->var_index].PROC_INDEX; 
    switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
      new_flag_roles = flag_roles | FLAG_GAME_SPEC; 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      	if (f->u.ddd.arc[ci].lower_bound != 0 || f->u.ddd.arc[ci].upper_bound != 0) {
          conj = rec_eliminate_illegal_modl_spec_read_writes
		(f->u.ddd.arc[ci].child, new_flag_roles);
	  for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
      	    if (xi && no_read_write_to_roles(xi, VAR[f->var_index].PROC_INDEX, FLAG_GAME_MODL)) { 
              child = ddd_one_constraint(conj, f->var_index, xi, xi);
              result = red_bop(OR, result, child); 
            }
          }
        }
      }
      break; 
    case FLAG_GAME_MODL: 
      new_flag_roles = flag_roles | FLAG_GAME_MODL; 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      	if (f->u.ddd.arc[ci].lower_bound != 0 || f->u.ddd.arc[ci].upper_bound != 0) {
          conj = rec_eliminate_illegal_modl_spec_read_writes
		(f->u.ddd.arc[ci].child, new_flag_roles);
      	  for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) {
      	    if (xi && no_read_write_to_roles(xi, VAR[f->var_index].PROC_INDEX, FLAG_GAME_SPEC)) { 
              child = ddd_one_constraint(conj, f->var_index, xi, xi);
              result = red_bop(OR, result, child); 
            }
          }
        }
      }
      break; 
    case FLAG_GAME_ENVR: 
      new_flag_roles = flag_roles | FLAG_GAME_ENVR; 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      	if (f->u.ddd.arc[ci].lower_bound != 0 || f->u.ddd.arc[ci].upper_bound != 0) {
          conj = rec_eliminate_illegal_modl_spec_read_writes
		(f->u.ddd.arc[ci].child, new_flag_roles);
      	  for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) {
      	    if (xi && no_write_through_to_roles
			(xi, VAR[f->var_index].PROC_INDEX, FLAG_GAME_SPEC | FLAG_GAME_MODL)
	        ) { 
              child = ddd_one_constraint(conj, f->var_index, xi, xi);
              result = red_bop(OR, result, child); 
            }
          }
        }
      }
      break; 
    } 
    
    break; 
    
  case TYPE_POINTER: 
    if (!(VAR[f->var_index].STATUS & FLAG_QUANTIFIED_SYNC)) {
      fprintf(RED_OUT, 
        "\nError: unexpected pointer variables in the prestine fliter_sync_xi_restriction.\n"
      ); 
      bk(0); 
    }
      
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      conj = rec_eliminate_illegal_modl_spec_read_writes
	(f->u.ddd.arc[ci].child, flag_roles);
      for (xi = f->u.ddd.arc[ci].lower_bound; 
           xi <= f->u.ddd.arc[ci].upper_bound; 
           xi++
           ) { 
        child = ddd_one_constraint(conj, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 
      }
    } 
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  
  return(rec->result = result); 
}
  /* rec_eliminate_illegal_modl_spec_read_writes() */


struct red_type	*red_eliminate_illegal_modl_spec_read_writes(f) 
	struct red_type	*f; 
{ 
  struct red_type	*result;

  if (f == NORM_FALSE)
    return(f);

  init_23tree(&elm_illegal_modl_spec_read_write_tree); 
  result = rec_eliminate_illegal_modl_spec_read_writes(f, 0);
  free_entire_23tree(elm_illegal_modl_spec_read_write_tree, rec_free); 

  return(result);
}
  /* red_eliminate_illegal_description_specificatoin_read_writes() */  
  
  
  

  

int	PARTY_TARGET; 


struct red_type	*rec_ec_auto_party(f)
     struct red_type	*f;
{
  int				pi, ci, xi; 
  struct red_type		*child, *result;
  struct cache2_hash_entry_type	*ce; 

  if (f == NORM_NO_RESTRICTION || f == NORM_FALSE)
    return(f);

  ce = cache2_check_result_key(
    OP_GAME_AUTO_PARTY, f, (struct red_type *) PARTY_TARGET
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    pi = VAR[f->var_index].PROC_INDEX; 
    if ((PROCESS[pi].status & MASK_GAME_ROLES) != PARTY_TARGET) { 
      if (f->u.ddd.arc[0].lower_bound == 0) {
        child = rec_ec_auto_party(f->u.ddd.arc[0].child); 
        result = ddd_one_constraint(child, f->var_index, 0, 0); 
      } 
      else 
        result = NORM_FALSE; 
    }
    else {
      result = NORM_FALSE; 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) {
        child = rec_ec_auto_party(f->u.ddd.arc[ci].child);
        for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
          if (   no_read_write_to_roles(xi, pi, (FLAG_GAME_SPEC | FLAG_GAME_MODL) & ~PARTY_TARGET)
              && no_write_through_to_roles(xi, pi, MASK_GAME_ROLES & ~PARTY_TARGET)
              && no_write_through_to_globals(xi, pi) 
              ) 
            result = red_bop(OR, result, ddd_one_constraint(child, f->var_index, xi, xi));
        }
      }
    } 
    break; 
    
  case TYPE_POINTER: 
    if (!(VAR[f->var_index].STATUS & FLAG_QUANTIFIED_SYNC)) {
      fprintf(RED_OUT, 
        "\nError: unexpected pointer variables in the prestine fliter_sync_xi_restriction.\n"
      ); 
      bk(0); 
    }
      
    pi = VAR[f->var_index].PROC_INDEX; 
    if ((PROCESS[pi].status & MASK_GAME_ROLES) != PARTY_TARGET) { 
      result = NORM_FALSE; 
    }
    else {
      result = NORM_FALSE; 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) {
        child = rec_ec_auto_party(f->u.ddd.arc[ci].child);
        for (xi = f->u.ddd.arc[ci].lower_bound; 
             xi <= f->u.ddd.arc[ci].upper_bound; 
             xi++
             ) { 
          result = red_bop(OR, result, 
            ddd_one_constraint(child, f->var_index, xi, xi)
          );
        }
      }
    } 
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  }
  return(ce->result = result); 
}
  /* rec_ec_auto_party() */




struct red_type	*red_ec_auto_party(f, party_auto) 
	struct red_type	*f; 
	int		party_auto; 
{ 
  struct red_type	*result;

  if (f == NORM_FALSE)
    return(f);

  PARTY_TARGET = party_auto; 

  result = rec_ec_auto_party(f);

  return(result);
}
  /* red_ec_auto_party() */  

  


int 	FLAG_ROLE_TO_PRESERVE, FLAG_ROLE_TO_NULLIFY; 

struct red_type	*rec_ec_role_nullify(f, flag_roles)
     struct red_type	*f;
     int		flag_roles; 
{
  int				pi, ci, xi, cur_role; 
  struct red_type		*child, *result;
  struct cache4_hash_entry_type	*ce; 

  if (f == NORM_FALSE)
    return(f);
  else if (f == NORM_NO_RESTRICTION)
    if (flag_roles & (FLAG_ROLE_TO_PRESERVE | FLAG_GAME_ENVR)) 
      return(f);
    else 
      return(NORM_FALSE); 

  ce = cache4_check_result_key(
    OP_GAME_ROLE_NULLIFY, f, (struct hrd_exp_type *) flag_roles, 
    FLAG_ROLE_TO_PRESERVE, FLAG_ROLE_TO_NULLIFY
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    pi = VAR[f->var_index].PROC_INDEX; 
    cur_role = PROCESS[pi].status & MASK_GAME_ROLES; 
    result = NORM_FALSE; 
    if (cur_role == FLAG_ROLE_TO_NULLIFY) { 
      if (f->u.ddd.arc[0].lower_bound == 0) {
        result = rec_ec_role_nullify(f->u.ddd.arc[0].child, flag_roles);
        result = ddd_one_constraint(result, f->var_index, 0, 0);
      }
    }
    else {
      for (ci = 0; ci < f->u.ddd.child_count; ci++) {
        child = rec_ec_role_nullify(f->u.ddd.arc[ci].child, flag_roles | cur_role);
        result = red_bop(OR, result, 
        		 ddd_one_constraint
        		 (child, f->var_index, 
        		  f->u.ddd.arc[ci].lower_bound, 
        		  f->u.ddd.arc[ci].upper_bound
        		  )
        		 ); 
      }
    } 
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  }
  
  return(ce->result 
    = (struct red_type *) result
  ); 
  return(result);
}
  /* rec_ec_role_nullify() */




struct red_type	*red_ec_role_nullify(f, flag_role_to_preserve, flag_role_to_nullify) 
	struct red_type	*f; 
	int		flag_role_to_preserve, flag_role_to_nullify; 
{ 
  struct red_type	*result;

  if (f == NORM_FALSE)
    return(f);

  FLAG_ROLE_TO_PRESERVE = flag_role_to_preserve; 
  FLAG_ROLE_TO_NULLIFY = flag_role_to_nullify; 
  result = rec_ec_role_nullify(f, 0);
  
  return(result);
}
  /* red_ec_role_nullify() */  

  



/***************************************************************************
 *  The following procedure is used for the construction of the 
 *  pseudo-synchronization for the write-through consistency of the globals 
 *  by MODL and SPEC. 
 */ 
struct red_type		*ECWTC_S; 
struct a23tree_type	*ecwtc_tree, *ecwtc2_tree; 
 
  

struct ec_write_link_type { 
  int				vi, value, 
				flag; 
// #define MASK_GAME_ROLES	0xE
// #define FLAG_GAME_SPEC		0x2
// #define FLAG_GAME_MODL		0x4
// #define FLAG_GAME_ENVR		0x8
#define FLAG_GAME_CONSTANT	0x100

  struct ec_write_link_type	*next_ec_write_link; 	
}; 

struct ec_write_link_type	*ECW_LIST; 
int				ECW_PI, ECW_FLAG_ROLE; 


void	print_ec_write_list(ecw_list) 
	struct ec_write_link_type	*ecw_list; 
{ 
  for (; ecw_list; ecw_list = ecw_list->next_ec_write_link) { 
    fprintf(RED_OUT, " %1d:%s:", ecw_list->vi, VAR[ecw_list->vi].NAME); 
    if (ecw_list->flag & FLAG_GAME_SPEC) 
      fprintf(RED_OUT, "S"); 
    else 
      fprintf(RED_OUT, "-"); 
    if (ecw_list->flag & FLAG_GAME_MODL) 
      fprintf(RED_OUT, "D"); 
    else 
      fprintf(RED_OUT, "-"); 
    if (ecw_list->flag & FLAG_GAME_ENVR) 
      fprintf(RED_OUT, "E"); 
    else 
      fprintf(RED_OUT, "-"); 
    if (ecw_list->flag & FLAG_GAME_CONSTANT) { 
      fprintf(RED_OUT, ":%1d;", ecw_list->value); 
    } 
    else { 
      fprintf(RED_OUT, "***;"); 
    } 
  } 
  fprintf(RED_OUT, "\n"); 
}
  /* print_ec_write_list() */  
  
  
  
int	rec_ecwtc_comp(rec1, rec2) 
	struct rec_type	*rec1, *rec2; 
{ 
  struct ec_write_link_type	*e1, *e2; 
  
  if (rec1->redx < rec2->redx) 
    return(-1); 
  else if (rec1->redx > rec2->redx) 
    return(1); 
  
  e1 = (struct ec_write_link_type *) rec1->redy; 
  e2 = (struct ec_write_link_type *) rec2->redy; 
  for (; e1 && e2; e1 = e1->next_ec_write_link, e2 = e2->next_ec_write_link) { 
    if (e1->vi < e2->vi) 
      return(-1); 
    else if (e1->vi > e2->vi) 
      return(1); 
    else if (e1->flag < e2->flag) 
      return(-1); 
    else if (e1->flag > e2->flag) 
      return(1); 
    else if (e1->flag & FLAG_GAME_CONSTANT) { 
      if (e1->value < e2->value) 
        return(-1); 
      else if (e1->value > e2->value) 
        return(1); 
    }   
  } 
  if (e1) 
    return(1); 
  else if (e2) 
    return(-1); 
  else 
    return(0); 
}
  /* rec_ecwtc_comp() */ 
  
/*  
int	ecwtc_free_count = 0; 
*/
rec_ecwtc_free(r) 
	struct rec_type	*r; 
{ 
  struct ec_write_link_type	*e1, *e2; 
  
  e1 = (struct ec_write_link_type *) r->redy; 
  for (; e1; ) {
/*
    fprintf(RED_OUT, "ecwtc_free_count=%1d\n", ++ecwtc_free_count); 
    fflush(RED_OUT); 
*/
    e2 = e1; 
    e1 = e1->next_ec_write_link; 
    free(e2); 
  }
  free(r); 
} 
  /* rec_ecwtc_free() */  
  
  
  
/*  
int	aecwt_count = 0; 
*/  
struct ec_write_link_type	*add_ec_write_throughs(list, vi, flags, value) 
  struct ec_write_link_type	*list; 
  int				vi, flags, value; 
{ 
  struct ec_write_link_type	dummy_ecw, *ecw, *pecw, *necw; 
  
  dummy_ecw.next_ec_write_link = list; 
/*  
  fprintf(RED_OUT, "aecwt_count = %1d\n", ++aecwt_count); 
  fflush(RED_OUT); 
*/  
  pecw = &dummy_ecw; 
  ecw = list; 
  for (; 
       ecw && (   ecw->vi < vi 
       	       || (ecw->vi == vi && (ecw->flag & FLAG_GAME_CONSTANT) < (flags & FLAG_GAME_CONSTANT))
       	       || (ecw->vi == vi && ((flags & FLAG_GAME_CONSTANT) && ecw->value < value))
       	       ); 
       ) {
    pecw = ecw; 
    ecw = ecw->next_ec_write_link; 
  }
  if (   !ecw 
      || ecw->vi > vi
      || (ecw->vi == vi && (   (ecw->flag & FLAG_GAME_CONSTANT) > (flags & FLAG_GAME_CONSTANT)
			    || ((flags & FLAG_GAME_CONSTANT) && ecw->value > value)
			    )
          ) 
      ) { 
    necw = (struct ec_write_link_type *) malloc(sizeof(struct ec_write_link_type)); 
    necw->vi = vi; 
    necw->flag = flags; 
    necw->value = value; 
    necw->next_ec_write_link = ecw; 
    pecw->next_ec_write_link = necw; 
    ecw = necw; 
    return(dummy_ecw.next_ec_write_link);
  } 
  else { 
    ecw->flag = flags | ecw->flag; 
    return(dummy_ecw.next_ec_write_link); 
  }
} 
  /* add_ec_write_throughs() */  
  
/*  
int	ecwlc_count = 0; 
*/
struct ec_write_link_type	*ecw_list_copy(list) 
  struct ec_write_link_type	*list; 
{ 
  struct ec_write_link_type	dummy_ecw, *ecw, *necw, *tail; 
  
  dummy_ecw.next_ec_write_link = NULL; 
  for (tail = &dummy_ecw, ecw = list; ecw; ecw = ecw->next_ec_write_link) {
    necw = (struct ec_write_link_type *) malloc(sizeof(struct ec_write_link_type)); 
    necw->vi = ecw->vi; 
/*
    fprintf(RED_OUT, "ecwlc_count = %1d\n", ++ecwlc_count); 
    fflush(RED_OUT); 
*/    
    necw->flag = ecw->flag; 
    necw->value = ecw->value; 
    tail->next_ec_write_link = necw; 
    necw->next_ec_write_link = NULL; 
  } 
  
  return(dummy_ecw.next_ec_write_link); 
} 
  /* ecw_list_copy() */  
  
  
  
  
void	*rec_add_global_write_throughs(st) 
	struct statement_type	*st; 
{ 
  int	i, value, vi; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case UNCHANGED: 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    vi = st->u.act.lhs->u.atom.var_index; 
    if (!VAR[vi].PROC_INDEX) { 
      ECW_LIST = add_ec_write_throughs(ECW_LIST, vi, ECW_FLAG_ROLE, 0); 
    } 
    break; 
  case ST_ERASE: 
    vi = st->u.erase.var->u.atom.var_index; 
    if (!VAR[vi].PROC_INDEX) { 
      ECW_LIST = add_ec_write_throughs(ECW_LIST, vi, ECW_FLAG_ROLE, 0); 
    } 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    vi = st->u.act.lhs->u.atom.var_index; 
    if (!VAR[vi].PROC_INDEX) { 
      if (st->u.act.rhs_exp->type == TYPE_INTERVAL) { 
      	int	value2, i2, k; 
      	
      	value = get_value(st->u.act.rhs_exp->u.interval.lbound_exp, ECW_PI, &i); 
      	value2 = get_value(st->u.act.rhs_exp->u.interval.rbound_exp, ECW_PI, &i2); 
        if (i != FLAG_ANY_VALUE && i2 != FLAG_ANY_VALUE) {
          for (k = value; k <= value2; k++) 
            ECW_LIST = add_ec_write_throughs(
              ECW_LIST, vi, FLAG_GAME_CONSTANT | ECW_FLAG_ROLE, k
            ); 
        }
        else 
          ECW_LIST = add_ec_write_throughs(ECW_LIST, vi, ECW_FLAG_ROLE, 0);       	
      } 
      else { 
      	value = get_value(st->u.act.rhs_exp, ECW_PI, &i); 
        if (i != FLAG_ANY_VALUE) 
          ECW_LIST = add_ec_write_throughs(ECW_LIST, vi, FLAG_GAME_CONSTANT | ECW_FLAG_ROLE, value); 
        else 
          ECW_LIST = add_ec_write_throughs(ECW_LIST, vi, ECW_FLAG_ROLE, 0); 
      }
    }   
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      rec_add_global_write_throughs(st->u.seq.statement[i]);
    break; 
  case ST_WHILE: 
    rec_add_global_write_throughs(st->u.loop.statement);
    break; 
  case ST_IF: 
    rec_add_global_write_throughs(st->u.branch.if_statement);
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      rec_add_global_write_throughs(st->u.branch.else_statement);  
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
  /* rec_add_global_write_throughs() */  



/*
int 	count_cagwt = 0; 
*/
struct ec_write_link_type	*copy_add_global_write_throughs(ecw_list, pi, st, flag_role) 
	struct ec_write_link_type	*ecw_list; 
	struct statement_type		*st; 
	int				pi, flag_role; 
{
  ECW_PI = pi; 
  ECW_FLAG_ROLE = flag_role; 
  ECW_LIST = ecw_list_copy(ecw_list); 
  rec_add_global_write_throughs(st); 
/*
  if (ecw_list) { 
    fprintf(RED_OUT, "count_cagwt = %1d, ecw_list->vi = %1d, ECW_LIST->vi = %1d\n", 
	    count_cagwt++, ecw_list->vi, ECW_LIST->vi
	    ); 
  } 
  else if (ECW_LIST) { 
    fprintf(RED_OUT, "count_cagwt = %1d, ecw_list = NULL,    ECW_LIST->vi = %1d\n", 
	    count_cagwt++, ECW_LIST->vi
	    ); 
  }
*/
  return(ECW_LIST); 
}
  /* copy_add_global_write_throughs() */  



int	*var_write_consistency; 

int	ec_write_through_consistency(list) 
	struct ec_write_link_type	*list; 
{ 
  int				vi; 
  struct ec_write_link_type	*ecw, *ecw2; 
  
  if (!list) 
    return(TYPE_TRUE); 
    
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    var_write_consistency[vi] = 0; 	
  } 
  
  /* First we need to check any values written by SPEC (or MODL) to a variable, 
   * must not written by the other plant with an inconsistent value. 
   */
  for (ecw = list; ecw; ecw = ecw->next_ec_write_link) { 
    var_write_consistency[ecw->vi] = var_write_consistency[ecw->vi] | (ecw->flag & MASK_GAME_ROLES); 
    for (ecw2 = ecw->next_ec_write_link; 
	 ecw2 && ecw2->vi == ecw->vi; 
	 ecw2 = ecw2->next_ec_write_link
	 ) { 
      if (ecw->vi == ecw2->vi) { 
      	/* First eliminate the race condition from the same party. */ 
      	if ((ecw->flag & MASK_GAME_ROLES) == (ecw2->flag & MASK_GAME_ROLES))
      	  return(TYPE_FALSE); 
      	else switch (ecw->flag & MASK_GAME_ROLES) { 
      	case FLAG_GAME_SPEC: 
      	  switch (ecw2->flag & MASK_GAME_ROLES) { 
      	  case FLAG_GAME_MODL: 
      	    if (   (ecw->flag & FLAG_GAME_CONSTANT) 
      	        && (ecw2->flag & FLAG_GAME_CONSTANT) 
      	        && (ecw->value == ecw2->value)
      	        ) 
      	      break; 
      	    else 
      	      return(TYPE_FALSE); 
      	    break; 
      	  default: 
      	  /* a race condition in the same party or with envr. */ 
      	    return(TYPE_FALSE); 
      	  } 
      	  break; 
      	case FLAG_GAME_MODL: 
      	  switch (ecw2->flag & MASK_GAME_ROLES) { 
      	  case FLAG_GAME_SPEC: 
      	    if (   (ecw->flag & FLAG_GAME_CONSTANT) 
      	        && (ecw2->flag & FLAG_GAME_CONSTANT) 
      	        && (ecw->value == ecw2->value)
      	        ) 
      	      break; 
      	    else 
      	      return(TYPE_FALSE); 
      	    break; 
      	  default: 
      	  /* a race condition in the same party or with envr. */ 
      	    return(TYPE_FALSE); 
      	  } 
      	  break; 
      	default: 
      	  return(TYPE_FALSE); 
      	  break; 
      	} 
      } 
    } 	
  } 
  /* Then we check out those inconsistency that a variable is written by only 
   * one party of MODL and SPEC.
   */ 
  for (vi = 8; vi < VARIABLE_COUNT; vi++) { 
    switch (var_write_consistency[vi] & MASK_GAME_ROLES) { 
    case 0: 
    case (FLAG_GAME_SPEC | FLAG_GAME_MODL): 
    case FLAG_GAME_ENVR: 
      break; 
    default: 
      return (TYPE_FALSE); 
    } 
  } 
  return(TYPE_TRUE); 
} 
  /* ec_write_through_consistency() */ 
  
  


void	dump_ec_SPEC_write_through_consistency(f, ecw_list, result) 
     struct red_type		*f, *result;
     struct ec_write_link_type	*ecw_list; 
{
  fprintf(RED_OUT, "In ec_SPEC_write_through_consistency()\n"); 
  red_print_graph(f); 
  print_ec_write_list(ecw_list); 
  red_print_graph(result); 
}
  /* dump_ec_MODL_SPEC_write_through_consistency() */  
  
  
  

struct red_type	*rec_ec_SPEC_write_throguh_consistency(f, ecw_list)
     struct red_type		*f;
     struct ec_write_link_type	*ecw_list; 
{
  int				lb, ci, xi, new_flag_roles; 
  struct red_type		*conj, *child, *result;
  struct ec_write_link_type	*necw_list; 
  struct cache2_hash_entry_type	*ce; 
  struct rec_type		*rec, *nrec; 

  if (f == NORM_FALSE) {
    dump_ec_SPEC_write_through_consistency(f, ecw_list, f); 
    return(f); 
  }
  else if (f == NORM_NO_RESTRICTION) { 
    if (ec_write_through_consistency(ecw_list)) {
      dump_ec_SPEC_write_through_consistency(f, ecw_list, f); 
      return(NORM_NO_RESTRICTION); 
    }
    else {
      dump_ec_SPEC_write_through_consistency(f, ecw_list, NORM_FALSE); 
      return(NORM_FALSE); 
    }
  }

  rec = rec_new(f, (struct red_type *) ecw_list); //??
  nrec = (struct rec_type *) add_23tree(
    rec, ecwtc2_tree, rec_ecwtc_comp, rec_ecwtc_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) {
    dump_ec_SPEC_write_through_consistency(f, ecw_list, nrec->result); 
    return(nrec->result);
  }

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
        if (xi == 0) 
          necw_list = ecw_list_copy(ecw_list); 
        else 
      	  necw_list = copy_add_global_write_throughs(
      	    ecw_list, VAR[f->var_index].PROC_INDEX, XTION[xi].statement, 
	    PROCESS[VAR[f->var_index].PROC_INDEX].status & MASK_GAME_ROLES
	  ); 
        child = rec_ec_SPEC_write_throguh_consistency(
          f->u.ddd.arc[ci].child, necw_list
        );
/*
        fprintf(RED_OUT, "** The above invocation is for xi=%1d by process %1d\n", 
        	xi, VAR[f->var_index].PROC_INDEX
        	); 
*/
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 
      }
    }
    
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  rec->result = (struct red_type *) result; 
  dump_ec_SPEC_write_through_consistency(f, ecw_list, rec->result); 
  return(result); 
}
  /* rec_ec_SPEC_write_throguh_consistency() */




  
void	dump_ec_MODL_SPEC_write_through_consistency(f, ecw_list, result) 
     struct red_type		*f, *result;
     struct ec_write_link_type	*ecw_list; 
{
  fprintf(RED_OUT, "In ec_MODL_SPEC_write_through_consistency()\n"); 
  red_print_graph(f); 
  print_ec_write_list(ecw_list); 
  red_print_graph(result); 
}
  /* dump_ec_MODL_SPEC_write_through_consistency() */  
  
  
  



struct red_type	*rec_ec_MODL_SPEC_write_through_consistency(f, ecw_list)
     struct red_type		*f;
     struct ec_write_link_type	*ecw_list; 
{
  int				lb, ci, xi, new_flag_roles; 
  struct red_type		*conj, *child, *result;
  struct ec_write_link_type	*necw_list; 
  struct rec_type		*rec, *nrec; 

  if (f == NORM_FALSE) {
/*
    dump_ec_MODL_SPEC_write_through_consistency(f, ecw_list, f); 
*/
    return(f); 
  }

  rec = rec_new(f, (struct red_type *) ecw_list); //??
  nrec = (struct rec_type *) add_23tree(
    rec, ecwtc_tree, rec_ecwtc_comp, rec_ecwtc_free,
    rec_nop, rec_parent_set, rec_print
  );
  if (rec != nrec) {
/*
    dump_ec_MODL_SPEC_write_through_consistency(f, (struct ec_write_link_type *) nrec->redy, nrec->result); 
*/
    return(nrec->result);
  }
  if (f == NORM_NO_RESTRICTION) { 
    if (ec_write_through_consistency(ecw_list)) {
/*
      dump_ec_MODL_SPEC_write_through_consistency(f, ecw_list, f); 
*/
      return(rec->result = NORM_NO_RESTRICTION); 
    }
    else {
/*
      dump_ec_MODL_SPEC_write_through_consistency(f, ecw_list, NORM_FALSE); 
*/
      return(rec->result = NORM_FALSE); 
    }
  }
  else switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
        if (xi == 0) 
          necw_list = ecw_list_copy(ecw_list); 
        else 
      	  necw_list = copy_add_global_write_throughs(
      	    ecw_list, VAR[f->var_index].PROC_INDEX, XTION[xi].statement,  
	    PROCESS[VAR[f->var_index].PROC_INDEX].status & MASK_GAME_ROLES
	  ); 
        child = rec_ec_MODL_SPEC_write_through_consistency(f->u.ddd.arc[ci].child, necw_list);
/*
        fprintf(RED_OUT, "** The above invocation is for xi=%1d by process %1d\n", 
        	xi, VAR[f->var_index].PROC_INDEX
        	); 
*/
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 
      }
    }
    
    break; 
    
  case TYPE_POINTER: 
    if (!(VAR[f->var_index].STATUS & FLAG_QUANTIFIED_SYNC)) {
      fprintf(RED_OUT, 
        "\nError: unexpected pointer variables in the prestine fliter_sync_xi_restriction.\n"
      ); 
      bk(0); 
    }
      
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; 
           xi <= f->u.ddd.arc[ci].upper_bound; 
           xi++
           ) { 
        child = rec_ec_MODL_SPEC_write_through_consistency(
          f->u.ddd.arc[ci].child, ecw_list_copy(ecw_list)
        );
/*
        fprintf(RED_OUT, "** The above invocation is for xi=%1d by process %1d\n", 
        	xi, VAR[f->var_index].PROC_INDEX
        	); 
*/
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 
      }
    }
    
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type %1d of variables in the prestine fliter_sync_xi_restriction.\n", 
    	    VAR[f->var_index].TYPE
    	    ); 
    bk(0); 
  } 
  
  rec->result = (struct red_type *) result; 
/*
  dump_ec_MODL_SPEC_write_through_consistency(f, ecw_list, rec->result); 
*/
  return(result); 
} 
  /* rec_ec_MODL_SPEC_write_through_consistency() */



/* This procedure generates pseudo-synchronizations with consistent variable assignments. */
struct red_type	*red_ec_MODL_SPEC_write_through_consistency(d) 
	struct red_type	*d; 
{ 
  var_write_consistency = (int *) malloc(VARIABLE_COUNT * sizeof(int)); 
  init_23tree(&ecwtc_tree); 
  d = rec_ec_MODL_SPEC_write_through_consistency(d, NULL); 
  free_entire_23tree(ecwtc_tree, rec_ecwtc_free); 
  free(var_write_consistency); 
  
  return(d); 
}
  /* red_ec_MODL_SPEC_write_through_consistency() */  
  
  
  
  
 
struct red_type	*red_eliminate_null_sync_xtion(f)
     struct red_type		*f;
{
  int			ci, xi; 
  struct red_type	*child, *result;

  if (f == NORM_FALSE || f == NORM_NO_RESTRICTION) { 
    return(NORM_FALSE); 
  }
  else switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
        if (xi == 0) 
          child = red_eliminate_null_sync_xtion(f->u.ddd.arc[ci].child);
        else 
          child = f->u.ddd.arc[ci].child; 
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 
      }
    }
    
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type %1d of variables in the prestine fliter_sync_xi_restriction.\n", 
    	    VAR[f->var_index].TYPE
    	    ); 
    bk(0); 
  } 

  return(result); 
} 
  /* red_eliminate_null_sync_xtion() */




 
/*********************************************************************************
 *
 */
struct red_type	*rec_game_eliminate_roles(f)
     struct red_type	*f;
{
  struct red_type		*child, *result;
  int				ci, cp1, cp2, hflag; 
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache2_hash_entry_type	*ce; 

  if (f == NORM_NO_RESTRICTION || f == NORM_FALSE)
    return(f);

  ce = cache2_check_result_key(
    OP_GAME_ELIMINATE_ROLES, f, (struct red_type *) PARTY_TARGET
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (PROCESS[cp1].status & PARTY_TARGET) { 
      if (f->u.ddd.arc[0].lower_bound == 0) { 
      	result = rec_game_eliminate_roles(f->u.ddd.arc[0].child);
      }
    }
    else {
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
        child = rec_game_eliminate_roles(f->u.ddd.arc[ci].child);
        child = ddd_one_constraint(child, f->var_index, 
					f->u.ddd.arc[ci].lower_bound, 
					f->u.ddd.arc[ci].upper_bound
					);
        result = red_bop(OR, result, child); 
      }
    } 
    break; 
  case TYPE_CRD:
    cp1 = VAR[CLOCK[VAR[f->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    cp2 = VAR[CLOCK[VAR[f->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   (cp1 && (PROCESS[cp1].status & PARTY_TARGET))
	|| (cp2 && (PROCESS[cp2].status & PARTY_TARGET))
	) { 
      for (ci = 0; ci < f->u.crd.child_count; ci++) {
        bc = &(f->u.crd.arc[ci]);
        child = rec_game_eliminate_roles(bc->child);
        result = red_bop(OR, result, child);
      }		
    }
    else 
      for (ci = 0; ci < f->u.crd.child_count; ci++) {
        bc = &(f->u.crd.arc[ci]);
        child = rec_game_eliminate_roles(bc->child);
        child = crd_lone_subtree(child, f->var_index, bc->upper_bound);
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_HRD:
    hflag = TYPE_FALSE; 
    for (ci = 0; ci < (f->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++) { 
      cp1 = VAR[f->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX; 
      if (cp1 && (PROCESS[cp1].status & PARTY_TARGET)) 
        hflag = TYPE_TRUE; 
    } 
    if (hflag) 
      for (ci = 0; ci < f->u.hrd.child_count; ci++) {
        hc = &(f->u.hrd.arc[ci]);
        child = rec_game_eliminate_roles(hc->child);
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = 0; ci < f->u.hrd.child_count; ci++) {
        hc = &(f->u.hrd.arc[ci]);
        child = hrd_lone_subtree(rec_game_eliminate_roles(hc->child),
				 f->u.hrd.hrd_exp,
				 hc->ub_numerator, hc->ub_denominator
				 );
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_FLOAT:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (cp1 && (PROCESS[cp1].status & PARTY_TARGET)) 
      for (ci = 0; ci < f->u.fdd.child_count; ci++) {
        child = rec_game_eliminate_roles(f->u.fdd.arc[ci].child);
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = 0; ci < f->u.fdd.child_count; ci++) {
        child = fdd_lone_subtree(
          rec_game_eliminate_roles(f->u.fdd.arc[ci].child),
	  f->var_index, f->u.fdd.arc[ci].lower_bound, 
	  f->u.fdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_DOUBLE:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (cp1 && (PROCESS[cp1].status & PARTY_TARGET)) 
      for (ci = 0; ci < f->u.dfdd.child_count; ci++) {
        child = rec_game_eliminate_roles(f->u.dfdd.arc[ci].child);
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = 0; ci < f->u.dfdd.child_count; ci++) {
        child = dfdd_lone_subtree(
          rec_game_eliminate_roles(f->u.dfdd.arc[ci].child),
	  f->var_index, f->u.dfdd.arc[ci].lower_bound, 
	  f->u.dfdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child);
      }
    break;
  default:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (cp1 && (PROCESS[cp1].status & PARTY_TARGET)) 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) {
        ic = &(f->u.ddd.arc[ci]);
        child = rec_game_eliminate_roles(ic->child);
        result = red_bop(OR, result, child);
      }
    else 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) {
        ic = &(f->u.ddd.arc[ci]);
        child = ddd_lone_subtree(
                rec_game_eliminate_roles(ic->child),
		f->var_index, ic->lower_bound, ic->upper_bound
		);
        result = red_bop(OR, result, child);
      }
    break;
  }
  return(ce->result = result); 
}
  /* rec_game_eliminate_roles() */




struct red_type	*red_game_eliminate_roles(f, roles_to_be_eliminated) 
	struct red_type	*f; 
	int		roles_to_be_eliminated; 
{ 
  struct red_type	*result;

  if (f == NORM_FALSE || !(roles_to_be_eliminated & MASK_GAME_ROLES))
    return(f);

  PARTY_TARGET = roles_to_be_eliminated & MASK_GAME_ROLES; 

  result = rec_game_eliminate_roles(f);

  return(result);
}
  /* red_game_eliminate_roles() */  
  


  
struct red_type	*red_game_eliminate_opponent(f, roles_to_be_saved) 
	struct red_type	*f; 
	int		roles_to_be_saved; 
{ 
  struct red_type	*result;

  PARTY_TARGET = (FLAG_GAME_MODL | FLAG_GAME_SPEC) & ~roles_to_be_saved; 
  if (f == NORM_FALSE || PARTY_TARGET == 0) 
    return(f);


  result = rec_game_eliminate_roles(f);

  return(result);
}
  /* red_game_eliminate_opponent() */  
  


  

 
 
 
/*********************************************************************************
 *
 */
 
int	TYPE_TARGET; 

struct red_type	*rec_ec_eliminate_type_roles(f)
     struct red_type	*f;
{
  struct red_type		*child, *result;
  int				ci, cp1, cp2, hflag; 
  struct crd_child_type		*bc;
  struct hrd_child_type		*hc;
  struct ddd_child_type		*ic;
  struct cache4_hash_entry_type	*ce; 

  if (f == NORM_NO_RESTRICTION || f == NORM_FALSE)
    return(f);

  ce = cache4_check_result_key(
    OP_GAME_ELIMINATE_TYPE_ROLES, f, (struct hrd_exp_type *) PARTY_TARGET, 
    TYPE_TARGET, 0 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[f->var_index].TYPE) {
  case TYPE_CRD:
    cp1 = VAR[CLOCK[VAR[f->var_index].U.CRD.CLOCK1]].PROC_INDEX; 
    cp2 = VAR[CLOCK[VAR[f->var_index].U.CRD.CLOCK2]].PROC_INDEX; 
    if (   (   (cp1 && (PROCESS[cp1].status & PARTY_TARGET))
	    || (cp2 && (PROCESS[cp2].status & PARTY_TARGET))
	    )
        && (VAR[f->var_index].TYPE == TYPE_TARGET)
        ) { 
      for (ci = 0; ci < f->u.crd.child_count; ci++) {
        bc = &(f->u.crd.arc[ci]);
        child = rec_ec_eliminate_type_roles(bc->child);
        result = red_bop(OR, result, child);
      }		
    }
    else 
      for (ci = 0; ci < f->u.crd.child_count; ci++) {
        bc = &(f->u.crd.arc[ci]);
        child = rec_ec_eliminate_type_roles(bc->child);
        child = crd_lone_subtree(child, f->var_index, bc->upper_bound);
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_HRD:
    hflag = TYPE_FALSE; 
    if (VAR[f->var_index].TYPE == TYPE_TARGET) {
      for (ci = 0; ci < (f->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); ci++) { 
        cp1 = VAR[f->u.hrd.hrd_exp->hrd_term[ci].var_index].PROC_INDEX; 
        if (cp1 && (PROCESS[cp1].status & PARTY_TARGET)) 
          hflag = TYPE_TRUE; 
      } 
      if (hflag) {
        for (ci = 0; ci < f->u.hrd.child_count; ci++) {
          hc = &(f->u.hrd.arc[ci]);
          child = rec_ec_eliminate_type_roles(hc->child);
          result = red_bop(OR, result, child);
        }
        break; 
      }
    }

    for (ci = 0; ci < f->u.hrd.child_count; ci++) {
      hc = &(f->u.hrd.arc[ci]);
      child = hrd_lone_subtree(rec_ec_eliminate_type_roles(hc->child),
			       f->u.hrd.hrd_exp,
			       hc->ub_numerator, hc->ub_denominator
			       );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (   (PROCESS[cp1].status & PARTY_TARGET) 
        && (VAR[f->var_index].TYPE == TYPE_TARGET)
        ) { 
      for (ci = 0; ci < f->u.fdd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.fdd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < f->u.fdd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.fdd.arc[ci].child);
        child = fdd_one_constraint(child, f->var_index, 
	  f->u.fdd.arc[ci].lower_bound, 
	  f->u.fdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child); 
      }
    } 
    break;
  case TYPE_DOUBLE:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (   (PROCESS[cp1].status & PARTY_TARGET) 
        && (VAR[f->var_index].TYPE == TYPE_TARGET)
        ) { 
      for (ci = 0; ci < f->u.dfdd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.dfdd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < f->u.dfdd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.dfdd.arc[ci].child);
        child = dfdd_one_constraint(child, f->var_index, 
	  f->u.dfdd.arc[ci].lower_bound, 
	  f->u.dfdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child); 
      }
    } 
    break;
  default:
    cp1 = VAR[f->var_index].PROC_INDEX; 
    if (   (PROCESS[cp1].status & PARTY_TARGET) 
        && (VAR[f->var_index].TYPE == TYPE_TARGET)
        ) { 
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.ddd.arc[ci].child);
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
        child = rec_ec_eliminate_type_roles(f->u.ddd.arc[ci].child);
        child = ddd_one_constraint(child, f->var_index, 
					f->u.ddd.arc[ci].lower_bound, 
					f->u.ddd.arc[ci].upper_bound
					);
        result = red_bop(OR, result, child); 
      }
    } 
    break; 
  }
  return(ce->result = result); 
}
  /* rec_ec_eliminate_type_roles() */




struct red_type	*red_ec_eliminate_type_roles(f, type, roles_to_be_eliminated) 
	struct red_type	*f; 
	int		type, roles_to_be_eliminated; 
{ 
  struct red_type	*result;

  if (f == NORM_FALSE)
    return(f);

  PARTY_TARGET = roles_to_be_eliminated & MASK_GAME_ROLES; 
  TYPE_TARGET = type; 

  result = rec_ec_eliminate_type_roles(f);

  return(result);
}
  /* red_ec_eliminate_type_roles() */  
  


  

 
 





/********************************************************************************
 *
 *  The following data-structures and procedures are for the elimination of write-through 
 *  conflicts between MODL and SPEC.  
 */
struct ec_write_through_record_type { 
  int	value, /* var_index */ 
	status; /* 0, not-written; 1, written. */ 	
}; 


int	*ECROLE_INDEX; 

struct ec_write_through_record_type	**alloc_ec_write_through_record() { 
  struct ec_write_through_record_type	**ewtr; 
  int					ri, vi; 

  ewtr = (struct ec_write_through_record_type **) 
	malloc(2 * sizeof(struct ec_write_through_record_type *)); 
  for (ri = 0; ri < 2; ri++) { 
    ewtr[ri] = (struct ec_write_through_record_type *) 
	  malloc(VARIABLE_COUNT * sizeof(struct ec_write_through_record_type)); 
    for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
      ewtr[ri][vi].value = 0; 
      ewtr[ri][vi].status = 0; 
    } 
  } 
  return(ewtr); 
} 
  /* alloc_ec_write_through_record() */  
  
  

struct ec_write_through_record_type	**duplicate_ec_write_through_record(old_ewtr) 
	struct ec_write_through_record_type	**old_ewtr; 
{ 
  struct ec_write_through_record_type	**ewtr; 
  int					ri, vi; 

  ewtr = (struct ec_write_through_record_type **) 
	malloc(2 * sizeof(struct ec_write_through_record_type *)); 
  for (ri = 0; ri < 2; ri++) { 
    ewtr[ri] = (struct ec_write_through_record_type *) 
	  malloc(VARIABLE_COUNT * sizeof(struct ec_write_through_record_type)); 
    for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
      ewtr[ri][vi].value = old_ewtr[ri][vi].value; 
      ewtr[ri][vi].status = old_ewtr[ri][vi].status; 
    } 
  } 
  return(ewtr); 
} 
  /* duplicate_ec_write_through_record() */  
  
  
  

free_ec_write_through_record(ewtr) 
  struct ec_write_through_record_type	**ewtr; 
{ 
  int	ri; 
  
  for (ri = 0; ri < 2; ri++) { 
    free(ewtr[ri]); 
  } 
  free(ewtr); 
} 
  /* free_ec_write_through_record() */ 


int	comp_rec_with_ec_write_through_record(rec1, rec2) 
  struct rec_type	*rec1, *rec2; 
{ 
  struct ec_write_through_record_type	**ewtr1, **ewtr2; 
  int					vi, ri; 
  
  if (rec1->redx < rec2->redx) 
    return(-1); 
  else if (rec1->redx > rec2->redx) 
    return(1); 
  
  ewtr1 = (struct ec_write_through_record_type **) rec1->redy; 
  ewtr2 = (struct ec_write_through_record_type **) rec2->redy; 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    for (ri = 0; ri < 2; ri++) { 
      if (ewtr1[ri][vi].status) 
        if (ewtr2[ri][vi].status) {
          if (ewtr1[ri][vi].value < ewtr2[ri][vi].value) 
            return(-1); 
          else if (ewtr1[ri][vi].value > ewtr2[ri][vi].value) 
            return(1); 
        }
        else 
          return(1); 
      else 
        if (ewtr2[ri][vi].status) 
          return(-1); 
    }
  }
  return(0); 
}
  /* comp_ec_write_through_record() */  



 


ec_write_through_record_print(ewtr)
  struct ec_write_through_record_type	**ewtr; 
{
  int					i, vi, flag; 

  fprintf(RED_OUT, "++++<EC write-through record>++++\n"); 
  fprintf(RED_OUT, "SPEC's scripts:"); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) 
    if (ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].status) { 
      fprintf(RED_OUT, "%1d:%s:%1d; ", vi, VAR[vi].NAME, ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].value); 
    }
  fprintf(RED_OUT, "\n"); 
  
  fprintf(RED_OUT, "MODL's scripts:"); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) 
    if (ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].status) { 
      fprintf(RED_OUT, "%1d:%s:%1d; ", vi, VAR[vi].NAME, ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].value); 
    }
  fprintf(RED_OUT, "\n\n"); 
  
}
  /* ec_write_through_record_print() */ 
  


/*********************************************************************
 *  (060505) 
 *  This procedure helps us eliminate some easy write-through conflicts between the MODL and 
 *  the SPEC. 
 * 
 *  First, only constants and local identifiers are checked to be written to global discretes. 
 *  Second, only clocks and discretes can be used as globals.   
 *  Third, 
 *  if pi is in spec, then we check if 
 *	pi writes to dscr's locals, or 
 *	pi writes to envr's locals, or
 *	pi writes to a global with a value inconsistent with that of dscr's.
 * 
 *  if pi is in dscr, then we check if 
 *	pi writes to spec's locals, or 
 *	pi writes to envr's locals, or
 *	pi writes to a global with a value inconsistent with that of spec's.
 * 
 *  if pi is in envr, then we check if 
 *	pi writes to dscr's locals, or 
 *	pi writes to spec's locals, 
 * 
 */
/*
int	ecwti_count = 0; 
*/
int	ec_write_xi = 0; 

int	ec_write_through_inconsistency_in_statement(ewtr, pi, st) 
	struct ec_write_through_record_type	**ewtr; 
	int					pi; 
	struct statement_type			*st; 
{ 
  int	vpi, vi, value, flag_address, i; 

  if (!st) 
    return (TYPE_FALSE); 
    
  switch (st->op) { 
  case UNCHANGED: 
    return (TYPE_FALSE); 
  case ST_GUARD: 
    return(TYPE_FALSE); 
  case ST_ERASE: 
    if (!(st->u.erase.var->u.atom.var->status & FLAG_LOCAL_VARIABLE)) 
      vpi = 0; 
    else {
      vpi = get_address(
        st->u.erase.var->u.atom.exp_base_proc_index, pi, &flag_address
      ); 
      if (   flag_address != FLAG_SPECIFIC_VALUE   
	  || (   vpi > 0 
	      && vpi <= PROCESS_COUNT 
	      && ((PROCESS[pi].status & MASK_GAME_ROLES) 
	          != (PROCESS[vpi].status & MASK_GAME_ROLES)
	          )
	      )
	  ) { 
        fprintf(RED_OUT, "Warning: In equivalence-checking, \n"); 
        fprintf(RED_OUT, "         the groups may erase one another's locals  \n"); 
        fprintf(RED_OUT, "         of by process %1d. \n", pi); 
        bk(0); 
      }
    } 
    break; 

  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    if (!(st->u.act.lhs->u.atom.var->status & FLAG_LOCAL_VARIABLE)) 
      vpi = 0; 
    else {
      vpi = get_address(
        st->u.act.lhs->u.atom.exp_base_proc_index, pi, &flag_address
      ); 
      if (   flag_address != FLAG_SPECIFIC_VALUE   
	  || (   vpi > 0 
	      && vpi <= PROCESS_COUNT 
	      && ((PROCESS[pi].status & MASK_GAME_ROLES) 
	          != (PROCESS[vpi].status & MASK_GAME_ROLES)
	          )
	      )
	  ) { 
        fprintf(RED_OUT, "Warning: In equivalence-checking, \n"); 
        fprintf(RED_OUT, "         the groups may write one another's locals  \n"); 
        fprintf(RED_OUT, "         of by process %1d. \n", pi); 
        bk(0); 
      }
    } 
    if (vpi == 0) { 
      if (st->u.act.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE) {
	break; 
/*	
        fprintf(RED_OUT, "Warning: In equivalence-checking, \n"); 
        fprintf(RED_OUT, "         the groups may write variables to globals in action %1d \n", ai); 
        fprintf(RED_OUT, "         of transition %1d by process %1d. \n", xi, pi); 
        bk(0); 
*/
      } 

      vi = st->u.act.lhs->u.atom.var_index; 
/*
      fprintf(RED_OUT, "ecwti_count = %1d\n", ecwti_count++); 
*/      
      value = get_value(st->u.act.rhs_exp, pi, &flag_address); 
      if (flag_address == FLAG_ANY_VALUE) 
        break; 
      switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
      case FLAG_GAME_SPEC: 
        if (   ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].status 
            && ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].value != value
            ) { 
          fprintf(RED_OUT, "Warning: In equivalence-checking, \n"); 
          fprintf(RED_OUT, "         a race condition may happen to globals \n"); 
          fprintf(RED_OUT, "         by spec process %1d. \n", pi); 
          bk(0); 
        } 
        else if (   ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].status 
                 && ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].value != value
                 ) { 
          return(TYPE_TRUE); 
        } 
        else { 
          ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].status = TYPE_TRUE; 
          ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].value = value;	
          return(TYPE_FALSE); 
        } 
        break; 
      case FLAG_GAME_MODL: 
        if (   ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].status 
            && ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].value != value
            ) { 
          fprintf(RED_OUT, "Warning: In equivalence-checking, \n"); 
          fprintf(RED_OUT, "         a race condition may happen to globals\n"); 
          fprintf(RED_OUT, "         of transition %1d by dscr process %1d. \n", ec_write_xi, pi); 
          bk(0); 
        } 
        else if (   ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].status 
                 && ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].value != value
                 ) { 
          return(TYPE_TRUE); 
        } 
        else { 
          ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].status = TYPE_TRUE; 
          ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].value = value;	
          return(TYPE_FALSE); 
        } 
        break; 
      } 
    } 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      if (ec_write_through_inconsistency_in_statement(ewtr, pi, st->u.seq.statement[i])) 
        return(TYPE_TRUE);
    break; 
  case ST_WHILE: 
    return(ec_write_through_inconsistency_in_statement(ewtr, pi, st->u.loop.statement)); 
    break; 

  case ST_IF: 
    if (ec_write_through_inconsistency_in_statement(ewtr, pi, st->u.branch.if_statement)) 
      return(TYPE_TRUE);
    else if (   (st->st_status & FLAG_STATEMENT_ELSE) 
	     && ec_write_through_inconsistency_in_statement(ewtr, pi, st->u.branch.else_statement)
	     )
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 

  case ST_CALL: 
  case ST_RETURN: 
    return(TYPE_FALSE); 

  default: 
    fprintf(RED_OUT, "ERROR: illegal statement operation code %1d\n", st->op); 
    fflush(RED_OUT); 
    exit(0); 
  }
  return(TYPE_FALSE); 
} 
  /* ec_write_through_inconsistency_in_statement() */   




int	ec_write_through_inconsistency(ewtr, pi, xi) 
	struct ec_write_through_record_type	**ewtr; 
	int					pi, xi; 
{ 
  ec_write_xi = xi; 
  return(ec_write_through_inconsistency_in_statement(ewtr, pi, XTION[xi].statement)); 
} 
  /* ec_write_through_inconsistency() */   




int	ec_write_through_set_match(ewtr)
	struct ec_write_through_record_type	**ewtr; 
{ 
  int	vi; 
  
  for (vi = 0; vi < VARIABLE_COUNT; vi++) { 
    if (ewtr[0][vi].status) {
      if (!ewtr[1][vi].status) 	
        return(TYPE_FALSE); 
      else if (ewtr[0][vi].value != ewtr[1][vi].value) 
        return(TYPE_FALSE); 
    }
    else 
      if (ewtr[1][vi].status) 
        return(TYPE_FALSE); 
  } 
  return(TYPE_TRUE); 
} 
  /* ec_write_through_set_match() */  
  
  
  

free_rec_with_ec_write_through_record(rec) 
	struct rec_type	*rec; 
{ 
  struct ec_write_through_record_type	**ewtr; 
  int					ri; 
  
  ewtr = (struct ec_write_through_record_type **) rec->redy; 
  for (ri = 0; ri < 2; ri++) { 
    free(ewtr[ri]); 
  } 
  free(ewtr); 
  rec_free(rec); 
} 
  /* free_rec_with_ec_write_through_record() */ 



rec_with_ec_write_through_record_print(rec, depth)
     struct rec_type	*rec; 
     int		depth; 
{
  int					i, vi, flag; 
  struct ec_write_through_record_type	**ewtr; 

  for (i = depth; i; i--) 
    fprintf(RED_OUT, "    "); 
  fprintf(RED_OUT, "++++<EC write-through record>++++\n"); 
  red_print_graph_depth(rec->redx, depth); 
  
  ewtr = (struct ec_write_through_record_type **) rec->redy; 
  for (i = depth; i; i--) 
    fprintf(RED_OUT, "    "); 
  fprintf(RED_OUT, "SPEC's scripts:"); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) 
    if (ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].status) { 
      fprintf(RED_OUT, "%1d:%s:%1d; ", vi, VAR[vi].NAME, ewtr[ECROLE_INDEX[FLAG_GAME_SPEC]][vi].value); 
    }
  fprintf(RED_OUT, "\n"); 
  
  for (i = depth; i; i--) 
    fprintf(RED_OUT, "    "); 
  fprintf(RED_OUT, "MODL's scripts:"); 
  for (vi = 0; vi < VARIABLE_COUNT; vi++) 
    if (ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].status) { 
      fprintf(RED_OUT, "%1d:%s:%1d; ", 
        vi, VAR[vi].NAME, ewtr[ECROLE_INDEX[FLAG_GAME_MODL]][vi].value
      ); 
    }
  fprintf(RED_OUT, "\n\n"); 
  
}
  /* rec_with_ec_write_through_record_print() */ 
  





struct red_type	*rec_ec_eliminate_write_through_conflicts(f, ewtr)
     struct red_type				*f;
     struct ec_write_through_record_type	**ewtr; 
{
  int					ci, pi, xi; 
  struct ec_write_through_record_type	**new_ewtr; 
  struct red_type			*child, *result;
  struct cache2_hash_entry_type		*ce; 
  struct rec_type			*rec, *nrec; 

  if (f == NORM_FALSE)
    return(f);

  rec = rec_new(f, (struct red_type *) ewtr); 
  nrec = (struct rec_type *) add_23tree(rec, ec_tree, 
					comp_rec_with_ec_write_through_record, 
					free_rec_with_ec_write_through_record, 
					rec_nop, rec_parent_set, 
					rec_with_ec_write_through_record_print 
					);
  if (rec != nrec) {
    return(nrec->result);
  }
  else if (f == NORM_NO_RESTRICTION)
    if (ec_write_through_set_match(ewtr))
      return(rec->result = NORM_NO_RESTRICTION);
    else 
      return(rec->result = NORM_FALSE); 

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    pi = VAR[f->var_index].PROC_INDEX; 
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
        new_ewtr = duplicate_ec_write_through_record(ewtr); 
        if (xi && ec_write_through_inconsistency(new_ewtr, pi, xi)) {
/*
          free_ec_write_through_record(new_ewtr); 
*/
          continue; 
	}
        child = rec_ec_eliminate_write_through_conflicts(f->u.ddd.arc[ci].child, new_ewtr);
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 

/*
        free_ec_write_through_record(new_ewtr); 
*/
      }
    }
    break; 
    
  case TYPE_POINTER: 
    if (!(VAR[f->var_index].STATUS & FLAG_QUANTIFIED_SYNC)) {
      fprintf(RED_OUT, 
        "\nError: unexpected pointer variables in the prestine fliter_sync_xi_restriction.\n"
      ); 
      bk(0); 
    }
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      for (xi = f->u.ddd.arc[ci].lower_bound; 
           xi <= f->u.ddd.arc[ci].upper_bound; 
           xi++
           ) { 
        new_ewtr = duplicate_ec_write_through_record(ewtr); 
        child = rec_ec_eliminate_write_through_conflicts(
          f->u.ddd.arc[ci].child, new_ewtr
        );
        child = ddd_one_constraint(child, f->var_index, xi, xi);
        result = red_bop(OR, result, child); 

/*
        free_ec_write_through_record(new_ewtr); 
*/
      }
    }
      
    break; 

  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  
  rec->result = (struct red_type *) result; 
  return(result); 
}
  /* rec_ec_eliminate_write_through_conflicts() */


struct red_type	*red_ec_eliminate_write_through_conflicts(f) 
	struct red_type	*f; 
{ 
  struct ec_write_through_record_type	**ewtr; 
  
  ECROLE_INDEX = (int *) malloc(16 * sizeof(int)); 
  ECROLE_INDEX[FLAG_GAME_SPEC] = 0; 
  ECROLE_INDEX[FLAG_GAME_MODL] = 1; 
 
  init_23tree(&ec_tree); 
  f = rec_ec_eliminate_write_through_conflicts(f, ewtr = alloc_ec_write_through_record()); 
  free_entire_23tree(ec_tree, free_rec_with_ec_write_through_record); 
/*  
  free_ec_write_through_record(ewtr); 
*/
  free(ECROLE_INDEX); 
  
  return(f); 
}
  /* red_ec_eliminate_write_through_conflicts() */ 
  
  
  
  



  
  


struct red_type	*rec_ec_eliminate_global_write(f)
     struct red_type	*f;
{
  int				ci, xi; 
  struct red_type		*child, *result;
  struct cache1_hash_entry_type	*ce; 

  if (f == NORM_FALSE || f == NORM_NO_RESTRICTION)
    return(f);

  ce = cache1_check_result_key(OP_GAME_ELIMINATE_GLOBAL_WRITE, f); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[f->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < f->u.ddd.child_count; ci++) { 
      child = rec_ec_eliminate_global_write(f->u.ddd.arc[ci].child);
      for (xi = f->u.ddd.arc[ci].lower_bound; xi <= f->u.ddd.arc[ci].upper_bound; xi++) { 
        if (xi && (XTION[xi].status & FLAG_XTION_GLOBAL_WRITING)) {
/*
          free_ec_write_through_record(new_ewtr); 
*/
          continue; 
	}
        result = red_bop(OR, result, ddd_one_constraint(child, f->var_index, xi, xi)); 
      }
    }
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  
  return(ce->result = result); 
}
  /* rec_ec_eliminate_global_write() */


struct red_type	*red_ec_eliminate_global_write(f) 
	struct red_type	*f; 
{ 
  struct red_type	*result; 
   
  result = rec_ec_eliminate_global_write(f); 
  
  return(result); 
}
  /* red_ec_eliminate_global_write() */ 
  
  
  



/*******************************************
 *  WE want to combine the synchronizations of those 
 *   1. write-through-consistency
 *   2. synchronizations. 
 * 
 */
struct red_type *red_ec_xi_restrictions(
	int	fi
	) 
{ 
  struct red_type	*red_auto_spec_without_modl, *d, *conj, 
			*red_auto_modl_without_spec; 
  int			plant_pair, pi, 
  			auto_spec_exclusive, auto_modl_exclusive; 

/* I think this is no longer necessary now. 
  d = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    d = ddd_one_constraint
	(d, variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0); 
	 
  RT[fi] = red_bop(OR, RT[fi], d); 
*/
/*  
  fprintf(RED_OUT, "The starting ec_xi_restriction with all NULLs in EC\n"); 
  red_print_graph(RT[fi]); 
*/
  /* The goal is to enforce that variable-value passing between the three parties: 
   * s (spec), d (dscription), and e (environment) can only happen through global variables. 
   * Currently, we do this purely in syntax level. 
   * We classify the synchronization labels into six classes. 
   * s-s, d-d, e-e, s-d, s-e, d-e
   *
   * Namely, the following synchronizations are forbitten. 
   * 1. class s-d is totally forbidden.  
   * 2. a synchronization label in classes s-s, d-d, e-e can only be used in one class. 
   * 3. a synchronization label in classes s-e and d-e can only be used in those two classes.
   * 4. a synchronization label in classes s-e and d-e may not use sync quantifiers. 
   * However, there still could be danger of breaking-down through indirections.  
   * Thus while calculating indirections, we shall restrict that indirections only happen 
   * among processes of one party.  
   */ 
  signal_read_write_locals_through_synchronization(); 
  
  /* The big secret is that the combined transition of equivalence-observers 
   * is exactly project(f, dimensions of environment and spec) AND 
   *            project(f, dimensions of environment and desc).  
   * The project is to be done through Fourier-Motzkin elimination. 
   * f is the part of filter_sync_xi_restriction without synchronization from 
   * environment to either spec or description.  
   * 
   * Note specifically, that we do not handle the case that two transitions 
   * from spec and dscr respectively may write different values to the same 
   * variables. 
   * Such combinations will be eliminated by a refinement of the race_eliminate().  
   */ 
/*   
  fprintf(RED_OUT, "*****(filter sync xtion)*************************************\n"); 
  red_print_graph(f); 
*/
  /* Basically, we just eliminate those combinations with non-zero environment transitions. 
   */ 
  /* First we get those sync transitions with only one parties.  
  */ 
  
  RT[auto_modl_exclusive = RT_TOP++] = red_ec_auto_party(
  	RT[fi], FLAG_GAME_MODL
  	); 
  RT[auto_spec_exclusive = RT_TOP++] = red_ec_auto_party(
  	RT[fi], FLAG_GAME_SPEC
  	); 
/*
  fprintf(RED_OUT, "\nECXIR 1: RT[auto_modl_exclusive=%1d]:\n", auto_modl_exclusive); 
  red_print_graph(RT[auto_modl_exclusive]); 
  fprintf(RED_OUT, "\nECXIR 2: RT[auto_spec_exclusive=%1d]:\n", auto_modl_exclusive); 
  red_print_graph(RT[auto_modl_exclusive]); 
*/     
  red_auto_modl_without_spec = red_game_eliminate_roles(
  	RT[fi], FLAG_GAME_SPEC
  	); 
  red_auto_spec_without_modl = red_game_eliminate_roles(
  	RT[fi], FLAG_GAME_MODL
  	); 
/*
  fprintf(RED_OUT, "\nECXIR 3: red_auto_modl_without_spec:\n"); 
  red_print_graph(red_auto_modl_without_spec); 
  fprintf(RED_OUT, "\nECXIR 4: red_auto_spec_without_modl:\n"); 
  red_print_graph(red_auto_spec_without_modl); 
*/  
  RT[plant_pair = RT_TOP++] 
  = red_bop(AND, red_auto_modl_without_spec, red_auto_spec_without_modl); 
/*
  RT[plant_pair] 
  = red_bop(SUBTRACT, RT[plant_pair], 
      red_game_eliminate_roles(
        RT[auto_spec_exclusive], FLAG_GAME_MODL | FLAG_GAME_ENVR
    ) ); 
  RT[plant_pair] 
  = red_bop(SUBTRACT, RT[plant_pair], 
      red_game_eliminate_roles(
        RT[auto_modl_exclusive], FLAG_GAME_SPEC | FLAG_GAME_ENVR
    ) ); 
*/
  RT[plant_pair] = red_ec_MODL_SPEC_write_through_consistency(RT[plant_pair]); 
/*  
  fprintf(RED_OUT, "\nECXIR 5: RT[plant_pair=%1d] after conjunction:\n", plant_pair); 
  red_print_graph(RT[plant_pair]); 
*/
  /* After this step, red_eqob reprsents those non-single-party transitions */ 
  RT[plant_pair] = red_eliminate_illegal_modl_spec_read_writes(RT[plant_pair]);   
/*
  fprintf(RED_OUT, "\nECXIR 6: RT[plant_pair=%1d] after eliminating illegal read writes:\n", plant_pair); 
  red_print_graph(RT[plant_pair]); 
*/
  RT[plant_pair] = red_ec_eliminate_write_through_conflicts(RT[plant_pair]); 
/*
  fprintf(RED_OUT, "\nECXIR 7: RT[plant_pair=%1d] after eliminating write-through conflicts:\n", plant_pair); 
  red_print_graph(RT[plant_pair]); 
*/
  /* Note that this procedure calls on red_hull_saturate_bck() which in turns 
   * does the garbage-collection.  
   * Thus it is necessary to take precaution. 
   */
  RT[plant_pair] = red_bop(OR, RT[plant_pair],  
			   red_bop(OR, RT[auto_modl_exclusive], 
			   	   RT[auto_spec_exclusive]
			   	   )
			   ); 
/*
  fprintf(RED_OUT, "ECXIR 8: The new ec_xi_restriction in EC\n"); 
  red_print_graph(RT[plant_pair]); 
*/

  RT_TOP = RT_TOP-3; /* plant_pair, auto_modl_exclusive, auto_spec_exclusive */ 
  
  return(RT[plant_pair]); 
}
  /* red_ec_xi_restrictions() */ 
  



  

/****************************************************************
 *  The following procedures compute the triggering constraints that 
 *  enforce the write-through consistency to the global variables.  
 */
struct ps_exp_link_type	{ 
  int				pi; 
  struct ps_exp_type		*exp; 
  struct ps_exp_link_type	*next_ps_exp_link; 
} ; 


struct ec_lhs_rhs_consistency_link_type { 
  int						vi; 
  struct ps_exp_link_type			*rhs_list; 
  struct ec_lhs_rhs_consistency_link_type	*next_ec_lhs_rhs_consistency_link; 
} 
  *EC_LHS_RHS_LIST; 
  
int	EC_LHS_RHS_PI; 



void	print_ec_lhs_rhs_consistency(sxi, e) 
	int					sxi; 
	struct ec_lhs_rhs_consistency_link_type	*e; 
{ 
  struct ps_exp_link_type	*pel; 
  
  fprintf(RED_OUT, "== SYNC_XTION_GAME[%1d], EC LHS RHS CONSISTENCY LIST ==\n", sxi); 
  for (; e; e = e->next_ec_lhs_rhs_consistency_link) { 
    fprintf(RED_OUT, "%1d:%s:\n", e->vi, VAR[e->vi].NAME); 
    for (pel = e->rhs_list; pel; pel = pel->next_ps_exp_link) { 
      fprintf(RED_OUT, "  pi=%1d:", pel->pi); 
      if (PROCESS[pel->pi].status & FLAG_GAME_SPEC) { 
      	fprintf(RED_OUT, "S"); 
      } 
      else 
        fprintf(RED_OUT, "-"); 
      if (PROCESS[pel->pi].status & FLAG_GAME_MODL) { 
      	fprintf(RED_OUT, "D"); 
      } 
      else 
        fprintf(RED_OUT, "-"); 
      if (PROCESS[pel->pi].status & FLAG_GAME_ENVR) { 
      	fprintf(RED_OUT, "E:"); 
      } 
      else 
        fprintf(RED_OUT, "-:"); 
      print_parse_subformula(pel->exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
    } 
  } 
}
  /* print_ec_lhs_rhs_consistency() */ 
  
  
  
  
int	check_ec_lhs_rhs_no_redundancy(r, list) 
	struct ps_exp_type	*r; 
	struct ps_exp_link_type	*list; 
{
  struct ps_exp_link_type	*e; 
  
  for (e = list; e; e = e->next_ps_exp_link) 
    if (!ps_exp_comp(r, e->exp)) 
      return(TYPE_FALSE); 
  return(TYPE_TRUE); 
}
  /* check_ec_lhs_rhs_no_redundancy() */ 
  
  
  
  
struct ec_lhs_rhs_consistency_link_type	*add_ec_lhs_rhs_consistency(l, vi, pi, r) 
	struct ec_lhs_rhs_consistency_link_type	*l; 
	int					vi, pi; 
	struct ps_exp_type			*r; 
{ 
  struct ec_lhs_rhs_consistency_link_type	dummy_head, *p, *c, *n; 
  struct ps_exp_link_type			*e; 

  dummy_head.next_ec_lhs_rhs_consistency_link = l; 
  p = &dummy_head; 
  c = l; 
  for (; c && c->vi < vi; p = c, c = c->next_ec_lhs_rhs_consistency_link) ; 

  if (!c || c->vi > vi) { 
    n = (struct ec_lhs_rhs_consistency_link_type *) 
	malloc(sizeof(struct ec_lhs_rhs_consistency_link_type)); 
    n->vi = vi; 
    n->rhs_list = NULL; 
    n->next_ec_lhs_rhs_consistency_link = c; 
    p->next_ec_lhs_rhs_consistency_link = n; 
    c = n; 
  } 
  if (check_ec_lhs_rhs_no_redundancy(r, c->rhs_list)) { 
    e = (struct ps_exp_link_type *) malloc(sizeof(struct ps_exp_link_type)); 
    e->pi = pi; 
    e->exp = r; 
    e->next_ps_exp_link = c->rhs_list; 
    c->rhs_list = e; 
  } 
  return(dummy_head.next_ec_lhs_rhs_consistency_link); 
}
  /* add_ec_lhs_rhs_consistency() */ 
  
  
  
  
  
void	rec_get_lhs_rhs_from_statement(st) 
	struct statement_type	*st; 
{ 
  int			vi, i; 
  struct ps_exp_type	*one, *r; 
  
  if (!st) 
    return; 
    
  switch (st->op) { 
  case UNCHANGED: 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    vi = st->u.act.lhs->u.atom.var_index; 
    if (!VAR[vi].PROC_INDEX) { 
      one = ps_exp_alloc(TYPE_CONSTANT); 
      one->u.value = 1;       
      r = ps_exp_instantiate(st->u.act.rhs_exp, EC_LHS_RHS_PI); 
      r = exp_arith(ARITH_ADD, r, one); 
      EC_LHS_RHS_LIST = add_ec_lhs_rhs_consistency(EC_LHS_RHS_LIST, vi, EC_LHS_RHS_PI, r); 
    } 
    break; 
  case ST_GUARD: 
    break; 
  case ST_ERASE: 
    break; 
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP: 
    vi = st->u.act.lhs->u.atom.var_index; 
    if (!VAR[vi].PROC_INDEX) { 
      r = ps_exp_instantiate(st->u.act.rhs_exp, EC_LHS_RHS_PI); 
      EC_LHS_RHS_LIST = add_ec_lhs_rhs_consistency(EC_LHS_RHS_LIST, vi, EC_LHS_RHS_PI, r); 
    } 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) 
      rec_get_lhs_rhs_from_statement(st->u.seq.statement[i]);
    break; 
  case ST_WHILE: 
    rec_get_lhs_rhs_from_statement(st->u.loop.statement);
    break; 
  case ST_IF: 
    rec_get_lhs_rhs_from_statement(st->u.branch.if_statement);
    if (st->st_status & FLAG_STATEMENT_ELSE) 
      rec_get_lhs_rhs_from_statement(st->u.branch.else_statement);  
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
  /* rec_get_lhs_rhs_from_statement() */  
  
  

struct ec_lhs_rhs_consistency_link_type	*get_lhs_rhs_from_statement(l, st, pi) 
	struct ec_lhs_rhs_consistency_link_type	*l; 
	struct statement_type			*st; 
	int					pi; 
{ 
  EC_LHS_RHS_LIST = l; 
  EC_LHS_RHS_PI = pi; 
  rec_get_lhs_rhs_from_statement(st); 
  return(EC_LHS_RHS_LIST); 
}
  /* get_lhs_rhs_from_statement() */  





struct red_type	*red_MODL_SPEC_write_consistency(sxi, sxi_table) 
	int			sxi; 
	struct sync_xtion_type	*sxi_table; 
{ 
  int						isi; 
  struct ec_lhs_rhs_consistency_link_type	*ec_lhs_rhs_list, *e; 
  struct ps_exp_link_type			*r1, *r2; 
  struct ps_exp_type				*a; 
  struct red_type				*trigger, *conj; 

  trigger = sxi_table[sxi].red_trigger; 
  if (sxi_table[sxi].party_count > 1) { 
    ec_lhs_rhs_list = NULL; 
    for (isi = 0; isi < sxi_table[sxi].party_count; isi++) { 
      ec_lhs_rhs_list = get_lhs_rhs_from_statement(ec_lhs_rhs_list, 
						   sxi_table[sxi].party[isi].statement, 
						   sxi_table[sxi].party[isi].proc
						   ); 
    } 	
/*
    print_ec_lhs_rhs_consistency(sxi, ec_lhs_rhs_list); 
*/
    for (e = ec_lhs_rhs_list; e; e = e->next_ec_lhs_rhs_consistency_link) { 
      for (r1 = e->rhs_list; r1; r1 = r1->next_ps_exp_link) { 
        for (r2 = r1->next_ps_exp_link; r2; r2 = r2->next_ps_exp_link) { 
          if (r1->pi != r2->pi) { 
      	    a = ps_exp_alloc(ARITH_EQ); 
      	    a->u.arith.lhs_exp = r1->exp; 
      	    a->u.arith.rhs_exp = r2->exp; 	
/*
      	    fprintf(RED_OUT, "CONJUNCT sxi_table[sxi=%1d].red_trigger with :\n", sxi); 
      	    red_print_graph(a->u.rpred.red); 
*/      	    
            trigger = red_bop(AND, trigger, 
              red_global(a, FLAG_LAZY_EVALUATION, 0)
            ); 
      	  }
      	} 
      }
    }
  } 
  return(trigger); 
}
  /* red_MODL_SPEC_write_consistency() */ 
  




  
  
  
/****************************************************************
 *
 *  Note that all information of equivalence-observers have been recorded in 
 *  fliter_sync_xi_restriction now.  
 *  So we just search each path using positive trigger condition of the target party 
 *  and the environment while using negative trigger condition of the counter-party.  
 */
  
int	EC_RISK, ecrk_count = 0; 

  
  
  
  
struct red_type	*red_role_invariance(flag_role) { 
  int			pi, imi, mi; 
  struct red_type	*result, *conj; 
  
  result = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if (PROCESS[pi].status & flag_role) { 
      conj = NORM_FALSE; 
      for (imi = 0; imi < PROCESS[pi].reachable_mode_count; imi++) { 
      	mi = PROCESS[pi].reachable_mode[imi]; 
      	conj = red_bop(OR, conj, MODE[mi].invariance[pi].red); 
      } 
      result = red_bop(AND, result, conj); 
    } 	
  } 
  return(result); 
} 
  /* red_role_invariance() */  
  
  
  
  

  




struct red_type	*rec_eliminate_role_and_single_plant(d, flag_roles)
     struct red_type	*d;
     int		flag_roles; 
{
  int					ci, pi, xi; 
  struct ec_write_through_record_type	**new_ewtr; 
  struct red_type			*child, *result;
  struct cache4_hash_entry_type		*ce; 

  if (d == NORM_FALSE)
    return(d);
  else if (d == NORM_NO_RESTRICTION)
    if ((flag_roles & FLAG_GAME_SPEC) && (flag_roles & FLAG_GAME_MODL))
      return(NORM_NO_RESTRICTION);
    else 
      return(NORM_FALSE); 

  ce = cache4_check_result_key(
    OP_ELIMINATE_ROLE_AND_SINGLE_PLANT, d, 
    NULL, flag_roles, FLAG_GAME_RSP_ROLE
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_XTION_INSTANCE: 
    pi = VAR[d->var_index].PROC_INDEX; 
    result = NORM_FALSE; 
    if (PROCESS[pi].status & FLAG_GAME_RSP_ROLE) { 
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
        if (d->u.ddd.arc[ci].upper_bound) 
          child = rec_eliminate_role_and_single_plant
		  (d->u.ddd.arc[ci].child, flag_roles | PROCESS[pi].status & MASK_GAME_ROLES);
	else 
	  child = NORM_FALSE; 
        if (!d->u.ddd.arc[ci].lower_bound) 
          child = red_bop(OR, child, rec_eliminate_role_and_single_plant
				     (d->u.ddd.arc[ci].child, flag_roles)
			  ); 
        child = ddd_one_constraint(child, d->var_index, 0, 0);
        result = red_bop(OR, result, child); 
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
        for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) { 
          if (xi) 
            child = rec_eliminate_role_and_single_plant
		    (d->u.ddd.arc[ci].child, flag_roles | PROCESS[pi].status & MASK_GAME_ROLES);
	  else 
            child = rec_eliminate_role_and_single_plant(d->u.ddd.arc[ci].child, flag_roles);	    
          child = ddd_one_constraint(child, d->var_index, xi, xi);
          result = red_bop(OR, result, child); 
	}
      }
    }    	
    break; 
    
  default: 
    fprintf(RED_OUT, "\nError: unexpected type of variables in the prestine fliter_sync_xi_restriction.\n"); 
    bk(0); 
  } 
  
  return(ce->result 
    = (struct red_type *) result
  ); 
}
  /* rec_eliminate_role_and_single_plant() */




struct red_type	*red_eliminate_role_and_single_plant(d, flag_role) 
	struct red_type	*d; 
	int		flag_role; 
{
  FLAG_GAME_RSP_ROLE = flag_role; 
  
  d = rec_eliminate_role_and_single_plant(d, 0); 
  
  return(d); 
}
  /* red_eliminate_role_and_single_plant() */ 
  
  
struct red_type	*red_ec_role_xi_construction(
  sxi, flag_role_to_be_eliminated, sxi_table 
) 
	int			sxi, flag_role_to_be_eliminated; 
	struct sync_xtion_type	*sxi_table; 
{
  int			pi, ipi; 
  
  struct red_type	*result; 
  if ((sxi_table[sxi].status & FLAG_GAME_SPEC) && (sxi_table[sxi].status & FLAG_GAME_MODL)) { 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      pxtion[pi] = 0; 
    for (ipi = 0; ipi < sxi_table[sxi].party_count; ipi++) { 
      pi = sxi_table[sxi].party[ipi].proc; 
      if (!(PROCESS[pi].status & flag_role_to_be_eliminated))
        pxtion[pi] = sxi_table[sxi].party[ipi].xtion; 
    } 
    result = NORM_NO_RESTRICTION; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) 
      result = ddd_one_constraint(result, variable_index[TYPE_XTION_INSTANCE][pi][0], 
				       pxtion[pi], pxtion[pi]
				       ); 
    return(result); 
  } 
  else 
    return(NORM_FALSE); 
}
  /* red_ec_role_xi_construction() */ 
  
  
  
struct red_type	*red_extract_null_role(d, flag_role) 
	struct red_type	*d; 
	int		flag_role; 
{ 
  int	pi; 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    if (PROCESS[pi].status & flag_role) 
      d = ddd_one_constraint(d, variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0); 
  return(d); 	
}
  /* red_extract_null_role() */ 
  



int	FLAG_GAME_ROLE_SPECIFIC, FLAG_GAME_OPPONENT_SPECIFIC; 
  




struct red_type	*red_add_role_trigger_sync_bulk(d, flag_role) 
	struct red_type	*d; 
	int		flag_role; 
{
  int			pi, fxi, ixi, xi; 
  struct red_type	*conj, *result, *subresult; 
  
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    if ((PROCESS[pi].status & FLAG_GAME_ENVR) || (PROCESS[pi].status & flag_role)) { 
      subresult = NORM_FALSE;
      fxi = variable_index[TYPE_XTION_INSTANCE][pi][0];
      for (ixi = 0; ixi < PROCESS[pi].firable_xtion_count; ixi++) {
        xi = PROCESS[pi].firable_xtion[ixi]; 
        conj = ddd_one_constraint(XTION[xi].red_trigger[pi], fxi, xi, xi); 
        if (xi && valid_mode_index(XTION[xi].src_mode_index)) 
          conj = red_bop(AND, conj, MODE[XTION[xi].src_mode_index].invariance[pi].red); 
        subresult = red_bop(OR, subresult, conj);
      }
      d = red_bop(AND, d, subresult);
    }
  } 
  return(d); 
}
  /* red_add_role_trigger_sync_bulk() */  
  
  
  
  
/* This procedure does the following: 
 *  1. eliminate all those branches with fewer than `depth' XI variables. 
 */
struct red_type	*red_ec_sync_bulk(d, depth)
     struct red_type	*d;
     int		depth; 
{
  int			ci, xi, b;
  struct red_type	*result, *new_child; 

  if (d == NORM_FALSE || depth > DEPTH_ENUMERATIVE_SYNCHRONIZATION)
    return(d);
  else if (d == NORM_NO_RESTRICTION) { 
    return(NORM_FALSE); 
  }

  switch (VAR[d->var_index].TYPE) { 
  case TYPE_XTION_INSTANCE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) 
      for (xi = d->u.ddd.arc[ci].lower_bound; xi <= d->u.ddd.arc[ci].upper_bound; xi++) {
	if (xi) { 
	  new_child = red_ec_sync_bulk(d->u.ddd.arc[ci].child, depth+1); 
	} 
	else 
	  new_child = red_ec_sync_bulk(d->u.ddd.arc[ci].child, depth); 
	result = red_bop(OR, result, ddd_one_constraint(new_child, d->var_index, xi, xi)); 
      } 
    return(result);
  
  case TYPE_CRD: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.crd.child_count; ci++) { 
      b = d->u.crd.arc[ci].upper_bound; 
      new_child = red_ec_sync_bulk(d->u.crd.arc[ci].child, depth); 
      result = red_bop(OR, result, crd_one_constraint(new_child, d->var_index, b)); 
    } 
    return(result); 
    
  case TYPE_HRD: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.hrd.child_count; ci++) { 
      new_child = red_ec_sync_bulk(d->u.hrd.arc[ci].child, depth);
      new_child = hrd_lone_subtree(new_child, d->var_index, d->u.hrd.hrd_exp,
				 d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
      result = red_bop(OR, result, new_child); 
    }
    return(result); 
  
  case TYPE_FLOAT: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) { 
      new_child = red_ec_sync_bulk(d->u.fdd.arc[ci].child, depth);
      new_child = fdd_one_constraint(new_child, d->var_index, 
	d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, new_child); 
    }
    return(result); 

  case TYPE_DOUBLE: 
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) { 
      new_child = red_ec_sync_bulk(d->u.dfdd.arc[ci].child, depth);
      new_child = fdd_one_constraint(new_child, d->var_index, 
	d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, new_child); 
    }
    return(result); 

  case TYPE_POINTER: 
    if (VAR[d->var_index].STATUS & FLAG_QUANTIFIED_SYNC)
      return(NORM_FALSE); 
  
  default:  
    result = NORM_FALSE; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) { 
      new_child = red_ec_sync_bulk(d->u.ddd.arc[ci].child, depth);
      new_child = ddd_one_constraint
			(new_child, d->var_index, 
			 d->u.ddd.arc[ci].lower_bound,
			 d->u.ddd.arc[ci].upper_bound
			 );
      result = red_bop(OR, result, new_child); 
    }
    return(result); 
  }
}
/* red_ec_sync_bulk() */




int		PREIMAGE_EIATOPTC, IMAGE_ACC_EIATOPTC, FLAG_ROLE_EIATOPTC; 

struct red_type	*red_one_ec_strongest_postcondition_sync_bulk(
  w, xi_sync, xi_sync_with_triggers, roles 
) 
     int	w, xi_sync, xi_sync_with_triggers, roles;
{
  int			explore, cur_xi, cur_pi, 
			flag, fxi, ixi, ai, result, conjm;
  struct red_type	*conj;
/*
  print_resources("===================================================================\nEntering sync_bulk_xtion()");
  report_red_management();
  */
  RT[explore = RT_TOP++] = red_bop(AND, RT[w], RT[xi_sync]); 
  get_all_firable_xtions(explore, roles); 
/*
  fprintf(RED_OUT, "** one_ec_strongest_postcondition_sync_bulk() **\n"); 
  fprintf(RED_OUT, "RT[explore=%1d]=%x\n", explore, RT[explore]);  
  fprintf(RED_OUT, "RT[xi_sync_with_triggers=%1d]=%x\n", 
    xi_sync_with_triggers, RT[xi_sync_with_triggers]
  ); 
*/
  RT[explore] = red_bop(AND, RT[explore], RT[xi_sync_with_triggers]); 
  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
    if (!(PROCESS[ITERATE_PI].status & roles & MASK_GAME_ROLES)) {
      RT[explore] = red_variable_eliminate(RT[explore], fxi);
      continue; 
    }
    RT[cur_pi = RT_TOP++] = NORM_FALSE;
    for (ixi = 0;
	    ixi < PROCESS[ITERATE_PI].firable_xtion_count
	 && current_firable_xtion[ITERATE_PI][ixi] != -1;
	 ixi++
	 ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(RT[explore], fxi, ITERATE_XI, ITERATE_XI);
      RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi);
/*
      fprintf(RED_OUT, "==========================================================================\n");
      fprintf(RED_OUT, "ITERATION %1d, before reverse action, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
      print_xtion_line(ITERATE_XI, ITERATE_PI);
      fprintf(RED_OUT, "\n");
      print_resources("before reverse action");
      report_red_management();
      red_print_graph(RT[cur_xi]);
      fflush(RED_OUT);
      probe(PROBE_PRERISK2, "WEAKEST INNER: before reverse action", RT[cur_xi]);
      red_order_check(RT[cur_xi]);
      */

      if (RT[cur_xi] == NORM_FALSE) {
	RT_TOP--;
	continue;
      }

      if (ITERATE_XI) {
/*
	  fprintf(RED_OUT, "\n****************************************************************************************\n");
	  fprintf(RED_OUT, "Iteration %1d, before ", ITERATION_COUNT);
	  print_xtion_line(ITERATE_XI, ITERATE_PI);
	  fprintf(RED_OUT, "\n");
*/
	RT[cur_xi] = red_statement_fwd(
	  cur_xi, ITERATE_PI, XTION[ITERATE_XI].statement,
	  FLAG_NO_ACTION_APPROX, 
          FLAG_ACTION_DELAYED_EVAL 
	  // GSTATUS[INDEX_ACTION_APPROX] & MASK_ACTION_APPROX 
	);
/*
  	  fprintf(RED_OUT, "----------(after ai = %1d)-----------\n", ai);
	  red_print_graph(RT[cur_xi]);
*/
/*
	fprintf(RED_OUT, "\n****************************************************************************************\n");
	fprintf(RED_OUT, "Iteration %1d, after process %1d executing xtion %1d", 
		ITERATION_COUNT, ITERATE_PI, ITERATE_XI
		);
	print_xtion_line(ITERATE_XI, ITERATE_PI);
	fprintf(RED_OUT, "\n");
	red_print_graph(RT[cur_xi]);
	fflush(RED_OUT);
	print_resources("after reverse action");
        report_red_management();
	probe(PROBE_PRERISK1, "WEAKEST INNER: after reverse action", RT[cur_xi]);
	red_order_check(RT[cur_xi]);
	*/

	if (RT[cur_xi] == NORM_FALSE) {
	  RT_TOP--;
	  continue;
	}
	if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
	          & FLAG_BULK_TRIGGER_ACTION_INTERFERE
	        ) ) 
            && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
            ) {
          if (valid_mode_index(XTION[ITERATE_XI].dst_mode_index)) { 
	    RT[cur_xi] = red_bop(AND, RT[cur_xi], 
	      MODE[XTION[ITERATE_XI].dst_mode_index].invariance[ITERATE_PI].red
	    );
	  }
	  /*
	  print_resources("after reverse triggering");
          report_red_management();
	    fprintf(RED_OUT, "I:%1d, after reverse triggering, ITERATE_XI=%1d, ITERATE_PI=%1d\n",
	    ITERATION_COUNT, ITERATE_XI, ITERATE_PI
	    );
	    red_print_graph(RT[cur_xi]);
	    fflush(RED_OUT);
	    print_resources("after reverse triggering");
	    probe(PROBE_PRERISK1, "WEAKEST INNER: after reverse triggering", RT[cur_xi]);
	  */

	  if (RT[cur_xi] == NORM_FALSE) {
	    RT_TOP--;
	    continue;
	  }
	  /*
	  print_resources("after local invariance");
          report_red_management();
	  fprintf(RED_OUT, "I:%1d, after local invariance, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
	  print_resources("after local invariance");
	  red_print_graph(RT[cur_xi]);
	  fflush(RED_OUT);
	  probe(PROBE_PRERISK1, "WEAKEST INNER: after local invariancing", RT[cur_xi]);
	  red_order_check(RT[cur_xi]);
	  */
	  RT[cur_xi] = process_inactive_variable_eliminate(cur_xi, ITERATE_PI);
	  /*
	  print_resources("after process inactive elimination");
          report_red_management();
	  fprintf(RED_OUT, "I:%1d, after local inactive elimination, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
	  red_print_graph(RT[cur_xi]);
	  fflush(RED_OUT);
	  probe(PROBE_PRERISK1, "WEAKEST INNER: after local inactive elimination", RT[cur_xi]);
	  red_order_check(RT[cur_xi]);
	  */

	}
        RT[cur_pi] = red_bop(OR, RT[cur_xi], RT[cur_pi]);
      }
      else
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

  /*
  print_resources("Leaving sync_bulk_xtion()");
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  RT_TOP--; // explore 

  return(RT[explore]);
}
/* red_one_ec_strongest_postcondition_sync_bulk() */


  
struct red_type	*red_game_mode_restrictor(roles) 
	int	roles; 
{ 
  int				w, pre, result, cur, 
				sxi, ipi, pi, sync_xtion_count, 
				xi_sync, xi_sync_with_triggers; 
  struct sync_xtion_type	*sync_xtion_table; 
  
  switch (roles & MASK_GAME_ROLES) { 
  case (FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL): 
    sync_xtion_table = SYNC_XTION_GAME; 
    sync_xtion_count = SYNC_XTION_COUNT_GAME; 
    xi_sync = XI_GAME_SYNC_BULK; 
    xi_sync_with_triggers = XI_GAME_SYNC_BULK_WITH_TRIGGERS; 
    RT[w = RT_TOP++] = red_subsume(RT[INDEX_INITIAL]); 
    break; 
  case (FLAG_GAME_ENVR | FLAG_GAME_SPEC): 
    sync_xtion_table = SYNC_XTION; 
    sync_xtion_count = SYNC_XTION_COUNT; 
    xi_sync = XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]; 
    xi_sync_with_triggers = XI_SYNC_BULK_WITH_TRIGGERS; 
    RT[w = RT_TOP++] = red_subsume(RT[GAME_ROLE_INITIAL[FLAG_GAME_SPEC]]); 
    break; 
  case (FLAG_GAME_ENVR | FLAG_GAME_MODL): 
    sync_xtion_table = SYNC_XTION; 
    sync_xtion_count = SYNC_XTION_COUNT; 
    xi_sync = XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]; 
    xi_sync_with_triggers = XI_SYNC_BULK_WITH_TRIGGERS; 
    RT[w = RT_TOP++] = red_subsume(RT[GAME_ROLE_INITIAL[FLAG_GAME_MODL]]); 
    break; 
  default: 
    fprintf(RED_OUT, "Error: an illegal role combination in ec_mode_restrictor().\n"); 
    exit(0); 
  } 
  #ifdef RED_DEBUG_BISIM_MODE
    #ifdef RED_DEBUG_BISIM_MODE_CMR
    fprintf(RED_OUT, 
      "\nCMR(%x): Initial condition in ec_mode_restrictor \n", roles 
    ); 
    red_print_graph(RT[w]); 
    #endif 
  #endif 
  
  RT[w] = red_eliminate_magnitudes(RT[w]); 
  #ifdef RED_DEBUG_BISIM_MODE
    #ifdef RED_DEBUG_BISIM_MODE_CMR
    fprintf(RED_OUT, 
      "\nCMR(%x): Initial mode clock restriction in ec_mode_restrictor\n", 
      roles 
    ); 
    red_print_graph(RT[w]); 
    #endif 
  #endif 
  
  RT[pre = RT_TOP++] = NORM_FALSE; 
  for (IT_EMR = 1; RT[w] != RT[pre]; IT_EMR++) { 
    RT[pre] = RT[w]; 
    RT[result = RT_TOP++] = NORM_FALSE; 

    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "CMR(%x)%1d, game mode restrictor, RT[w=%1d]:%x\n", 
      roles, IT_EMR, w, (unsigned int) RT[w]
    ); 
    fprintf(RED_OUT, "CMR(%x)%1d, game mode restrictor, RT[XI_GAME_SYNC_ALL=%1d]:%x\n", 
      roles, IT_EMR, XI_GAME_SYNC_BULK, (unsigned int) RT[XI_GAME_SYNC_BULK]
    ); 
    #endif 
    
    RT[result] = red_one_ec_strongest_postcondition_sync_bulk(
      w, xi_sync, xi_sync_with_triggers, roles
    ); 
    RT[result] = red_eliminate_magnitudes(RT[result]); 
    RT[result] = inactive_variable_eliminate(result); 
    #ifdef RED_DEBUG_BISIM_MODE
      #ifdef RED_DEBUG_BISIM_MODE_CMR
      fprintf(RED_OUT, "\n**************************************************\n"); 
      fprintf(RED_OUT, "CMR(%x) %1d, post-image of sync-bulk.\n", 
        roles, IT_EMR
      ); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 

    for (sxi = 0; sxi < sync_xtion_count; sxi++) { 
      #ifdef RED_DEBUG_BISIM_MODE
        #ifdef RED_DEBUG_BISIM_MODE_CMR
        print_sync_xtion_lines(sxi, sync_xtion_table); 
        #endif 
      #endif 
      
      if (   (sync_xtion_table[sxi].status & MASK_GAME_ROLES & ~roles) 
          || sync_xtion_table[sxi].party_count == 0
          )
        continue; 

      RT[cur = RT_TOP++] = red_bop(AND, RT[w], 
        sync_xtion_table[sxi].red_trigger
      );  
      for (ipi = 0; ipi < sync_xtion_table[sxi].party_count; ipi++) { 
        pi = sync_xtion_table[sxi].party[ipi].proc; 
        RT[cur] = red_statement_fwd(
          cur, pi, sync_xtion_table[sxi].party[ipi].statement, 
	  FLAG_NO_ACTION_APPROX, 
          FLAG_ACTION_DELAYED_EVAL  
        ); 
      } 
      #ifdef RED_DEBUG_BISIM_MODE
        #ifdef RED_DEBUG_BISIM_MODE_CMR
        fprintf(RED_OUT, "\nCMR(%x)%1d, sxi %1d, after statement:\n", 
          roles, IT_EMR, sxi
        ); 
        red_print_graph(RT[cur]); 
        #endif 
      #endif 

      RT[cur] = red_eliminate_magnitudes(RT[cur]); 
      #ifdef RED_DEBUG_BISIM_MODE
        #ifdef RED_DEBUG_BISIM_MODE_CMR
        fprintf(RED_OUT, "\nCMR(%x) %1d, sxi %1d, after elm mag:\n", 
          roles, IT_EMR, sxi
        ); 
        red_print_graph(RT[cur]); 
        #endif 
      #endif 

      RT[cur] = inactive_variable_eliminate(cur); 
      #ifdef RED_DEBUG_BISIM_MODE
        #ifdef RED_DEBUG_BISIM_MODE_CMR
        fprintf(RED_OUT, "===========================================\n"); 
        fprintf(RED_OUT, 
          "CMR(%x) %1d, post-condition of sync xtion %1d after inactive\n", 
          roles, IT_EMR, sxi
        ); 
        red_print_graph(RT[cur]); 
        fprintf(RED_OUT, "\n\n\n"); 
        #endif 
      #endif 

      RT[result] = red_bop(OR, RT[cur], RT[result]); 
      RT_TOP--; /* cur */ 
      garbage_collect(FLAG_GC_SILENT);
    } 
    RT[w] = red_bop(OR, RT[w], RT[result]); 
    RT_TOP--; /* result */ 
    #ifdef RED_DEBUG_BISIM_MODE
      #ifdef RED_DEBUG_BISIM_MODE_CMR
      fprintf(RED_OUT, 
        "\n**************************************************\n"
      ); 
      fprintf(RED_OUT, "CMR(%x) %1d, post-image.\n", roles, IT_EMR); 
      red_print_graph(RT[result]); 
      #endif 
    #endif 

  } 
  
  RT_TOP--; /* pre */ 
  RT[w] = inactive_variable_eliminate(w); 
  RT[w] = red_subsume(RT[w]); 

  #ifdef RED_DEBUG_BISIM_MODE
    #ifdef RED_DEBUG_BISIM_MODE_CMR
    fprintf(RED_OUT, 
      "\nCMR(%x) final mode restrictions on clocks:\n", 
      roles
    ); 
    red_print_graph(RT[w]); 
    #endif 
  #endif 
  
  RT_TOP--; /* w */ 
  return (RT[w]); 
}
  /* red_game_mode_restrictor() */  





int	flag_party_not_finished(sync_xtion_table, sxi, ipi, roles) 
	struct sync_xtion_type	*sync_xtion_table; 
	int			sxi, ipi, roles; 
{ 
  for (; ipi < sync_xtion_table[sxi].party_count; ipi++) { 
    if (PROCESS[sync_xtion_table[sxi].party[ipi].proc].status & roles) 
      return(TYPE_TRUE); 
  } 
  return(TYPE_FALSE); 
}
  /* flag_party_not_finished() */
  
  
  
prepare_game_sync_xtion_representatives(int role) { 
  int	opp, sxi, sxj, ipi, ipj, pi, pj, 
 	flag_representative_found; 
  
  // Note that push_for_local_path_shape_high_level() is 
  // destructive to its third parameter. 
  // So we need to make a copy in the following. 
  opp = MASK_GAME_ROLES & ~(role | FLAG_GAME_ENVR); 
  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    SYNC_XTION_GAME[sxi].ec_representative[role] = -1; 
    for (flag_representative_found = TYPE_FALSE, sxj = 0; 
         sxj < SYNC_XTION_COUNT; 
         sxj++
         ) { 
      if (SYNC_XTION[sxj].status & opp) 
        continue; 
        
      for (ipi = 0, ipj = 0; 
              ipi < SYNC_XTION_GAME[sxi].party_count
           && ipj < SYNC_XTION[sxj].party_count; 
           ) { 
        pi = SYNC_XTION_GAME[sxi].party[ipi].proc; 
        pj = SYNC_XTION[sxj].party[ipj].proc; 
        if (PROCESS[pi].status & opp) 
          ipi++; 
        else if (   pi != pj 
                 || SYNC_XTION_GAME[sxi].party[ipi].xtion 
                    != SYNC_XTION[sxj].party[ipj].xtion 
                 ) { 
          break; 
        } 
        else { 
          ipi++; ipj++; 
        } 
      } 
      if (   (   ipi < SYNC_XTION_GAME[sxi].party_count
              && ipj < SYNC_XTION[sxj].party_count
              )  
          || flag_party_not_finished(
               SYNC_XTION_GAME, sxi, ipi, role | FLAG_GAME_ENVR
             ) 
          || flag_party_not_finished(
               SYNC_XTION, sxj, ipj, role | FLAG_GAME_ENVR
             )
          ) 
        continue; 
      else {
        flag_representative_found = TYPE_TRUE; 
        break; 
      } 
    }
    if (!flag_representative_found) { 
      fprintf(RED_OUT, 
        "Error: game sync xtion %1d cannot find a representative.\n", 
        sxi
      ); 
      bk(0); 
    } 
    else { 
      SYNC_XTION_GAME[sxi].ec_representative[role] = sxj; 
      SYNC_XTION[sxj].ec_representative[role]++; 
    } 
  } 

  #ifdef RED_DEBUG_BISIM_MODE
  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    fprintf(RED_OUT, "SYNC XTION GAME %1d, %s's representative = %1d\n", 
      sxi, role_name(role), SYNC_XTION_GAME[sxi].ec_representative[role] 
    ); 
  } 
//  fprintf(RED_OUT, "\n--------------------------------\n"); 
  #endif 

  for (sxj = 0; sxj < SYNC_XTION_COUNT; sxj++) { 
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "SYNC XTION %1d, %s's repesentative = %1d\n", 
      sxj, role_name(role), SYNC_XTION[sxj].ec_representative[role] 
    ); 
    #endif 

    SYNC_XTION[sxj].ec_representee[role] = (int *) 
      malloc((SYNC_XTION[sxj].ec_representative[role])*sizeof(int)); 
    SYNC_XTION[sxj].ec_representative[role] = 0; 
  } 

  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    sxj = SYNC_XTION_GAME[sxi].ec_representative[role]; 
    ipi = SYNC_XTION[sxj].ec_representative[role]++;
/*
    fprintf(RED_OUT, "\nsxj %1d--> sxi %1d: size=%1d\n", 
      sxj, sxi, SYNC_XTION[sxj].ec_representative[role]
    ); 
*/
    SYNC_XTION[sxj].ec_representee[role][ipi] = sxi; 
  } 
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\n--------------------------------\n"); 
  for (sxj = 0; sxj < SYNC_XTION_COUNT; sxj++) { 
    fprintf(RED_OUT, "SYNC XTION %1d, %s's repesentative:", 
      sxj, role_name(role)
    ); 

    fprintf(RED_OUT, "(%1d)", SYNC_XTION[sxj].ec_representative[role]); 
    for (ipi = 0; ipi < SYNC_XTION[sxj].ec_representative[role]; ipi++) 
      fprintf(RED_OUT, " %1d", SYNC_XTION[sxj].ec_representee[role][ipi]); 
    fprintf(RED_OUT, "\n"); 
  } 

  #endif 
}
  /* prepare_game_sync_xtion_representatives() */ 




int	FLAG_GAME_EXTRACT_ROLES; 

struct red_type	*rec_ec_extract_role_unbounded(d) 
     struct red_type	*d; 
{
  int				ci, cv1, c2; 
  struct red_type		*result, *child; 
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION) 
    return(d); 
  
  ce = cache2_check_result_key(
    OP_GAME_EXTRACT_ROLE_UNBOUNDED, d, 
    (struct red_type *) FLAG_GAME_EXTRACT_ROLES
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE; 
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    cv1 = CLOCK[VAR[d->var_index].U.CRD.CLOCK1]; 
    c2 = VAR[d->var_index].U.CRD.CLOCK2; 
    if (   (!c2) 
        && (   (!VAR[cv1].PROC_INDEX)
            || (   VAR[cv1].PROC_INDEX 
                && (  PROCESS[VAR[cv1].PROC_INDEX].status 
                    & FLAG_GAME_EXTRACT_ROLES
                    )
                )
            )
        ) {
      ci = d->u.crd.child_count-1;  
      if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) 
        result = rec_ec_extract_role_unbounded(d->u.crd.arc[ci].child);   
    }
    else { 
      for (ci = 0; ci < d->u.crd.child_count; ci++) { 
        child = rec_ec_extract_role_unbounded(d->u.crd.arc[ci].child);   
        child = crd_one_constraint(child, d->var_index, d->u.crd.arc[ci].upper_bound); 
        result = red_bop(OR, result, child); 
      }
    } 
    break; 
  case TYPE_FLOAT: 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_ec_extract_role_unbounded(d->u.fdd.arc[ci].child); 
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, 
	d->u.fdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  case TYPE_DOUBLE: 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_ec_extract_role_unbounded(d->u.dfdd.arc[ci].child); 
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, 
	d->u.dfdd.arc[ci].upper_bound
      ); 
      result = red_bop(OR, result, child); 
    } 
    break; 
  default: 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_ec_extract_role_unbounded(d->u.ddd.arc[ci].child); 
      child = ddd_one_constraint(child, d->var_index, d->u.ddd.arc[ci].lower_bound, 
				      d->u.ddd.arc[ci].upper_bound
				      ); 
      result = red_bop(OR, result, child); 
    } 
  } 
  return(ce->result = result); 
}
  /* rec_ec_extract_role_unbounded() */ 



struct red_type	*red_ec_extract_role_unbounded(d, flag_roles) 
	struct red_type	*d; 
{ 
  struct red_type	*result; 

  /* 
  print_resources("Entering red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */  
  FLAG_GAME_EXTRACT_ROLES = flag_roles; 
  
  result = rec_ec_extract_role_unbounded(d); 
  /* 
  print_resources("Leaving red_eliminate_magnitude_redundancy()"); 
  red_size(RT[w], SIZE_REPORT, NULL, NULL); 
  red_print_graph(RT[w]); 
  */ 
  return(result); 	
}
  /* red_ec_extract_role_unbounded() */ 
  
  
  
  
 
struct red_type	*red_game_timed_weakest_precondition_sync_bulk(
  int	explore, 
  int	path, 
  int	flag_role
) {
  int			cur_xi, cur_pi, flag, fxi, ixi, ai, result, conjm;
  struct red_type	*conj;
/*
  print_resources("===================================================================\nEntering sync_bulk_xtion()");
  report_red_management();
  */
  RT[explore] = red_bop(AND, RT[explore], RT[XI_SYNC_ALL]);
/*
  switch (flag_role & MASK_GAME_ROLES) { 
  case FLAG_GAME_SPEC: 
    RT[explore] = red_bop(AND, RT[explore], RT[XI_GAME_SPEC_SYNC_BULK]);
    break; 
  case FLAG_GAME_MODL: 
    RT[explore] = red_bop(AND, RT[explore], RT[XI_GAME_MODL_SYNC_BULK]);
    break; 
  default: 
    fprintf(RED_OUT, "ERROR: Illegal role definition.\n"); 
    exit(0); 
  }  	
*/
  get_all_firable_xtions(explore, flag_role | FLAG_GAME_ENVR);
  for (ITERATE_PI = 1; ITERATE_PI <= PROCESS_COUNT; ITERATE_PI++) {
    fxi = variable_index[TYPE_XTION_INSTANCE][ITERATE_PI][0];
//    fprintf(RED_OUT, "ITERATE_PI=%1d, looping in sync bulk precondition\n", ITERATE_PI); 
    if (!(PROCESS[ITERATE_PI].status & (flag_role | FLAG_GAME_ENVR))) {
      if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) ) 
          && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
          ) 
        RT[explore] = red_variable_eliminate(RT[explore], fxi); 
      continue; 
    }
       
    RT[cur_pi = RT_TOP++] = NORM_FALSE;

    for (ixi = 0;
	    ixi < PROCESS[ITERATE_PI].firable_xtion_count
	 && current_firable_xtion[ITERATE_PI][ixi] != -1;
	 ixi++
	 ) {
      ITERATE_XI = current_firable_xtion[ITERATE_PI][ixi];
//      fprintf(RED_OUT, "ITERATE_PI=%1d, XI=%1d, looping in sync bulk precondition\n", 
//	      ITERATE_PI, ITERATE_XI
//	      ); 
      RT[cur_xi = RT_TOP++] = ddd_one_constraint(RT[explore], fxi, ITERATE_XI, ITERATE_XI);
/*
      fprintf(RED_OUT, "==========================================================================\n");
      fprintf(RED_OUT, "ITERATION %1d, before reverse action, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
      print_xtion_line(ITERATE_XI, ITERATE_PI);
      fprintf(RED_OUT, "\n");
      print_resources("before reverse action");
      report_red_management();
      red_print_graph(RT[cur_xi]);
      fflush(RED_OUT);
      probe(PROBE_PRERISK2, "WEAKEST INNER: before reverse action", RT[cur_xi]);
      red_order_check(RT[cur_xi]);
      */

      if (RT[cur_xi] == NORM_FALSE) {
	RT_TOP--;
	continue;
      }

      if (ITERATE_XI) {
/*
	  fprintf(RED_OUT, "\n****************************************************************************************\n");
	  fprintf(RED_OUT, "Iteration %1d, before ", ITERATION_COUNT);
	  print_xtion_line(ITERATE_XI, ITERATE_PI);
	  fprintf(RED_OUT, "\n");
*/
	RT[cur_xi] = red_statement_bck( 
	  cur_xi, ITERATE_PI, XTION[ITERATE_XI].statement, 
	  FLAG_NO_ACTION_APPROX, 
          FLAG_ACTION_DELAYED_EVAL  
	);
/*
  	  fprintf(RED_OUT, "----------(after ai = %1d)-----------\n", ai);
	  red_print_graph(RT[cur_xi]);
*/
/*
	fprintf(RED_OUT, "\n****************************************************************************************\n");
	fprintf(RED_OUT, "Iteration %1d, after process %1d executing xtion %1d", 
		ITERATION_COUNT, ITERATE_PI, ITERATE_XI
		);
	print_xtion_line(ITERATE_XI, ITERATE_PI);
	fprintf(RED_OUT, "\n");
	red_print_graph(RT[cur_xi]);
	fflush(RED_OUT);
	print_resources("after reverse action");
        report_red_management();
	probe(PROBE_PRERISK1, "WEAKEST INNER: after reverse action", RT[cur_xi]);
	red_order_check(RT[cur_xi]);
	*/

	if (RT[cur_xi] == NORM_FALSE) {
	  RT_TOP--;
	  continue;
	}
        if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                  & FLAG_BULK_TRIGGER_ACTION_INTERFERE
                ) ) 
            && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
            ) {
          RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi); 
	  if (valid_mode_index(XTION[ITERATE_XI].src_mode_index)) { 
	    conj = red_bop(AND, XTION[ITERATE_XI].red_trigger[ITERATE_PI],
		         MODE[XTION[ITERATE_XI].src_mode_index].invariance[ITERATE_PI].red
		         );

	    RT[cur_xi] = red_bop(AND, RT[cur_xi], conj);
	  /*
	    print_resources("after reverse triggering");
            report_red_management();
	    fprintf(RED_OUT, "I:%1d, after reverse triggering, ITERATE_XI=%1d, ITERATE_PI=%1d\n",
	    ITERATION_COUNT, ITERATE_XI, ITERATE_PI
	    );
	    red_print_graph(RT[cur_xi]);
	    fflush(RED_OUT);
	    print_resources("after reverse triggering");
	    probe(PROBE_PRERISK1, "WEAKEST INNER: after reverse triggering", RT[cur_xi]);
	  */

	    if (RT[cur_xi] == NORM_FALSE) {
	      RT_TOP--;
	      continue;
	    }
	  /*
	  print_resources("after local invariance");
          report_red_management();
	  fprintf(RED_OUT, "I:%1d, after local invariance, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
	  print_resources("after local invariance");
	  red_print_graph(RT[cur_xi]);
	  fflush(RED_OUT);
	  probe(PROBE_PRERISK1, "WEAKEST INNER: after local invariancing", RT[cur_xi]);
	  red_order_check(RT[cur_xi]);
	  */
	  }

	  RT[cur_xi] = process_inactive_variable_eliminate(
	    cur_xi, ITERATE_PI
	  );
	  /*
	  print_resources("after process inactive elimination");
          report_red_management();
	  fprintf(RED_OUT, "I:%1d, after local inactive elimination, ITERATE_XI=%1d, ITERATE_PI=%1d\n", ITERATION_COUNT, ITERATE_XI, ITERATE_PI);
	  red_print_graph(RT[cur_xi]);
	  fflush(RED_OUT);
	  probe(PROBE_PRERISK1, "WEAKEST INNER: after local inactive elimination", RT[cur_xi]);
	  red_order_check(RT[cur_xi]);
	  */
        }
      }
      if (   (!(  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
                & FLAG_BULK_TRIGGER_ACTION_INTERFERE
              ) ) 
          && (!(GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)) 
          ) {
        RT[cur_xi] = red_variable_eliminate(RT[cur_xi], fxi); 
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
/*      
      fprintf(RED_OUT, "count_ec_g = %1d\n", ++count_ec_g); 
      fflush(RED_OUT); 
*/
      garbage_collect(FLAG_GC_SILENT);
    }

    RT[explore] = RT[cur_pi];
    RT_TOP--; /* cur_pi */
    
//    fprintf(RED_OUT, "ITERATE_PI=%1d, sync bulk ineq precondition:\n", ITERATE_PI); 
//    red_print_graph(RT[explore]); 
  }

//  fprintf(RED_OUT, "End of sync bulk precondition iterations.\n"); 
//  fflush(RED_OUT); 
  
  if (   (  GSTATUS[INDEX_BULK_TRIGGER_ACTION_INTERFERE] 
          & FLAG_BULK_TRIGGER_ACTION_INTERFERE
          )
      || (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC)
      ) {
    RT[explore] = red_bop(AND, RT[explore], RT[XI_ROLE_SYNC_BULK[flag_role]]); 
    RT[explore] = red_type_eliminate(RT[explore], TYPE_XTION_INSTANCE); 
  } 
  RT[explore] = inactive_variable_eliminate(explore); 
  RT[explore] = red_bop(AND, RT[GAME_ROLE_INVARIANCE[flag_role]], RT[explore]);  
  RT[explore] = red_game_time_progress_bck(
    NULL, 
    explore, path, flag_role | FLAG_GAME_ENVR, 
    TYPE_TRUE 
  ); 
    
  RT[explore] = red_hull_normalize(explore); 

  /*
  print_resources("Leaving sync_bulk_xtion()");
  red_print_graph(RT[explore]);
  fflush(RED_OUT);
  */
  return(RT[explore]);
}
/* red_game_timed_weakest_precondition_sync_bulk() */



  
struct red_type	*red_game_time_reachable_bck(
  int	w, 
  int	path, 
  int	flag_role, 
  int	flag_approx
) { 
  int	explore, IT_GAME_NZF_RCH; 
   
  RT[explore = RT_TOP++] = RT[w]; 
  for (IT_GAME_NZF_RCH = 0; RT[explore] != NORM_FALSE; IT_GAME_NZF_RCH++) { 
/*
    fprintf(RED_OUT, "\n***[IT EC NZF=%1d, IT EC NZF RCH=%1d, role %1d]*****\n", 
      IT_GAME_NZF, IT_GAME_NZF_RCH, flag_role 
    ); 
*/
    RT[explore] = red_game_timed_weakest_precondition_sync_bulk(
      explore, path, flag_role
    ); 
    union_abstract_new(w, explore, FLAG_ROOT_NOAPPROX);
/*     
    fprintf(RED_OUT, "RT[w=%1d] at RT_TOP=%1d:\n", w, RT_TOP); 
    red_print_graph(RT[w]); 
    fprintf(RED_OUT, "RT[explore=%1d] at RT_TOP=%1d:\n", explore, RT_TOP); 
    red_print_graph(RT[explore]); 
*/
  }
  RT_TOP--; /* explore */ 
  
  return(RT[w]); 
} 
  /* red_game_time_reachable_bck() */ 
  








inline struct red_type	*red_game_invariance(int flag_role) {
  int	pi; 
  
  RT[GAME_ROLE_INVARIANCE[flag_role]] = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    if (PROCESS[pi].status & (FLAG_GAME_ENVR | flag_role)) 
      RT[GAME_ROLE_INVARIANCE[flag_role]] 
      = red_bop(AND, RT[GAME_ROLE_INVARIANCE[flag_role]], 
        RED_INVARIANCE[pi]
      ); 

  RT[GAME_ROLE_INVARIANCE[flag_role]] 
  = red_bop(AND, RT[GAME_ROLE_INVARIANCE[flag_role]], 
      red_game_mode_restrictor(FLAG_GAME_ENVR | flag_role)
    ); 
  RT[GAME_ROLE_INVARIANCE[flag_role]] 
  = red_game_eliminate_roles(RT[GAME_ROLE_INVARIANCE[flag_role]], 
    (FLAG_GAME_MODL | FLAG_GAME_SPEC) & ~flag_role
  ); 
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After game mode restrictor, RT[GAME_ROLE_INVARIANCE[%1d]=%1d]:\n", 
    flag_role, GAME_ROLE_INVARIANCE[flag_role] 
  ); 
  #endif 
  
/* The following code has been removed since we now use 
 * GAME_ROLE_FAIRNESS[flag_role] to replace GAME_ROLE_INVARIANCE[flag_role]
 * as the universe of the opponent's play space.  
 * This is because that using GAME_ROLE_INVARIANCE[flag_role] for this 
 * purpose tends to overload the semantics of 
 * GAME_ROLE_INVARIANCE[flag_role].  
  if ((GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK) {
  // Here we compute the those description states with a NZ computation.  
    RT[GAME_ROLE_INVARIANCE[flag_role]] 
    = role_fairness_bck(flag_role); 
  }
*/
  red_mark(RT[GAME_ROLE_INVARIANCE[flag_role]], FLAG_GC_STABLE);  
  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nRT[GAME_ROLE_INVARIANCE[%1d]=%1d]:\n", 
    flag_role, GAME_ROLE_INVARIANCE[flag_role]
  ); 
  red_print_graph(RT[GAME_ROLE_INVARIANCE[flag_role]]); 
  #endif 
  
  return(RT[GAME_ROLE_INVARIANCE[flag_role]]); 
}
  /* red_game_invariance() */ 
  




 
  
  
    

void	construct_bisim_structures_for_a_role_spec() { 
  int			isi, isj, pi, ipi, sxi, sxj, result, 
			old_depth_enumerative_sync, xi_tmp; 
  struct red_type	*tmp_initial, *conj; 

  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "Entering bisim structure construction with the following tables" 
  ); 
  print_processes(); 
  print_xtions(); 
  print_sync_xtions(SYNC_XTION, SYNC_XTION_COUNT); 
  #endif 
  /* First set the convenient run-time stack top index for the 
   * marking of active diagrams. 
   * Since most of the simulation related diagrams are to be constructed. 
   * We lower the top index. 
   */ 
  RT_DYNAMIC = INDEX_GAME_START; 
  
  GSTATUS[INDEX_GAME_ROLES] = GSTATUS[INDEX_GAME_ROLES] & ~FLAG_GAME_ROLES_CHANGED; 
  /* First, we have to release all the diagrams for the old role 
   * specifications. 
   * Note that this has to be done at the same time. 
   * Otherwise, we may unmark diagrams that are newly constructed for the 
   * new role specification.  
   */ 
  for (isi = INDEX_GAME_START; isi <= INDEX_GAME_STOP; isi++) { 
/*
    fprintf(RED_OUT, "\nInitial unmarking RT[isi=%1d]:%x\n", isi, RT[isi]); 
    fflush(RED_OUT); 
*/
    if (RT[isi]) {
/*
      red_print_graph(RT[isi]); 
*/
      red_unmark(RT[isi], FLAG_GC_STABLE); 
    }
  } 
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    SYNC_XTION[sxi].status = SYNC_XTION[sxi].status & ~MASK_GAME_ROLES; 
    for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) { 
      pi = SYNC_XTION[sxi].party[ipi].proc; 
      SYNC_XTION[sxi].status 
      = SYNC_XTION[sxi].status | (PROCESS[pi].status & MASK_GAME_ROLES); 
    } 	
  } 

  RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]] = RT[XI_SYNC_BULK]; 
  RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]] = RT[XI_SYNC_BULK]; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
    switch (PROCESS[pi].status & MASK_GAME_ROLES) { 
    case FLAG_GAME_SPEC: 
      RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]] 
      = ddd_one_constraint(RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]], 
        variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0
      ); 
      break; 
    case FLAG_GAME_MODL: 
      RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]] 
      = ddd_one_constraint(RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]], 
        variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0
      ); 
      break; 
    } 
  }
  RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]] 
  = red_game_eliminate_roles(red_add_trigger_sync_bulk(
    RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]]  
  ), FLAG_GAME_MODL); 
  RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]] 
  = red_game_eliminate_roles(red_add_trigger_sync_bulk(
    RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]]  
  ), FLAG_GAME_SPEC); 
  red_mark(RT[XI_ROLE_SYNC_BULK[FLAG_GAME_SPEC]], FLAG_GC_STABLE);
  red_mark(RT[XI_ROLE_SYNC_BULK[FLAG_GAME_MODL]], FLAG_GC_STABLE);

  RT[XI_GAME_SYNC_ALL] = RT[XI_SYNC_ALL]; 
/*
  fprintf(RED_OUT, "\n** Generating RT[XI_GAME_SYNC_ALL=%1d]:\n", 
    XI_GAME_SYNC_ALL
  ); 
*/
  RT[XI_GAME_SYNC_ALL] = red_ec_xi_restrictions(XI_GAME_SYNC_ALL); 
  /* The above procedure also calculates 
   * RT[XI_GAME_SPEC_SYNC_BULK] and RT[XI_GAME_MODL_SYNC_BULK]. 
   */  
//  race_eliminate(XI_GAME_SYNC_ALL); 
  red_mark(RT[XI_GAME_SYNC_ALL], FLAG_GC_STABLE);
  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nFrom RT[XI_SYNC_ALL=%1d]:\n", XI_SYNC_ALL); 
  red_print_graph(RT[XI_SYNC_ALL]); 
  print_resources(
    "After calculating the initial RT[XI_GAME_SYNC_ALL=%d]:\n", 
    XI_GAME_SYNC_ALL
  );
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  #endif 

  if (GSTATUS[INDEX_SYNCHRONIZATION] & FLAG_SYSTEM_QUANTIFIED_SYNC) {
    RT[XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS] 
    = red_ec_xi_restrictions(XI_SYNC_ALL_WITH_PROC_HOLDERS); 
    red_mark(RT[XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS], FLAG_GC_STABLE);
    RT[XI_GAME_SYNC_ALL_WITH_EVENT_PROC_HOLDERS] = RT[XI_GAME_SYNC_ALL];
/*
    = add_event_counts_from_xtions(RT[XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS]);
    red_mark(RT[XI_GAME_SYNC_ALL_WITH_EVENT_PROC_HOLDERS], FLAG_GC_STABLE);
    fprintf(RED_OUT, "Add sync proc holders\n"); 
    report_red_management(); 
*/
  }
  else { 
    RT[XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS] 
    = RT[XI_GAME_SYNC_ALL_WITH_EVENT_PROC_HOLDERS] 
    = RT[XI_GAME_SYNC_ALL];
  } 
  RT[XI_GAME_SYNC_ALL_WITH_TRIGGERS] 
  = red_add_trigger_sync_bulk(RT[XI_GAME_SYNC_ALL]);
  red_mark(RT[XI_GAME_SYNC_ALL_WITH_TRIGGERS], FLAG_GC_STABLE); 

  #ifdef RED_DEBUG_BISIM_MODE
  print_resources("After adding quantified sync holders");
  print_cpu_time("After adding quantified sync holders, RT[XI_GAME_SYNC_ALL=%d]:\n", 
    XI_GAME_SYNC_ALL
  );
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  #endif 
/*
  fprintf(RED_OUT, "After possible ec xi restriction\n"); 
  report_red_management(); 
*/
/*
  print_resources("After race elimination");
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  fflush(RED_OUT);
  print_resources("After the initial FILTER_XI_RESTRICTION");
  fprintf(out, "\nThe initial FILTER_XI_RESTRICTION:\n");
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  fprintf(RED_OUT, "After race eliminate\n"); 
  report_red_management(); 
*/
/*
  print_resources("After removing intriggerable sync xtions");
  fprintf(RED_OUT, "\nRT[XI_GAME_SYNC_ALL=%1d]:\n", XI_RESTRICTION);
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  fprintf(RED_OUT, "Before prepare sync\n"); 
  report_red_management(); 
*/
  /* The following three arrays are to be released at the end of sync_party_fillin() */ 
  RT[XI_GAME_SYNC_BULK] = red_ec_xi_restrictions(XI_SYNC_BULK); 
  /* The above procedure also calculates 
   * RT[XI_GAME_SPEC_SYNC_BULK] and RT[XI_GAME_MODL_SYNC_BULK]. 
   */  

  #ifdef RED_DEBUG_BISIM_MODE
  print_resources("After calculating the initial RT[XI_GAME_SYNC_BULK=%d]:\n", 
    XI_GAME_SYNC_BULK
  );
  red_print_graph(RT[XI_GAME_SYNC_BULK]);
  #endif 

  red_mark(RT[XI_GAME_SYNC_BULK], FLAG_GC_STABLE);
  
  RT[xi_tmp = RT_TOP++] = red_bop(SUBTRACT, 
    RT[XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS], RT[XI_GAME_SYNC_BULK]
  ); 
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources("After calculating the initial RT[xi_tmp=%d]:\n", 
    xi_tmp
  );
  red_print_graph(RT[xi_tmp]);
  #endif 

  conj = NORM_NO_RESTRICTION; 
  for (pi = 1; pi <= PROCESS_COUNT; pi++) 
    conj = ddd_one_constraint(conj, 
      variable_index[TYPE_XTION_INSTANCE][pi][0], 0, 0
    ); 
  RT[xi_tmp] = red_bop(SUBTRACT, RT[xi_tmp], conj); 
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources("After calculating the 2nd RT[xi_tmp=%d]:\n", 
    xi_tmp
  );
  fprintf(RED_OUT, "\nThis is actually the real RT[XI_GAME_SYNC_ALL]:\n"); 
  red_print_graph(RT[xi_tmp]);
  #endif 

  old_depth_enumerative_sync = DEPTH_ENUMERATIVE_SYNCHRONIZATION; 
  DEPTH_ENUMERATIVE_SYNCHRONIZATION = PROCESS_COUNT+1; 
  prepare_sync_xtions( 
    xi_tmp, &SYNC_XTION_GAME, &SYNC_XTION_COUNT_GAME, 
    TYPE_TRUE // for a bisim analysis 
  ); 
  DEPTH_ENUMERATIVE_SYNCHRONIZATION = old_depth_enumerative_sync; 
  RT_TOP--; // xi_tmp 
  
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources("After preparing SYNC_XTION_GAME:\n");
  #endif 
  /* Now mark the roles of each synchronous transitions. 
   */ 
  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    SYNC_XTION_GAME[sxi].status 
    = SYNC_XTION_GAME[sxi].status & ~MASK_GAME_ROLES; 
    for (ipi = 0; ipi < SYNC_XTION_GAME[sxi].party_count; ipi++) { 
      pi = SYNC_XTION_GAME[sxi].party[ipi].proc; 
      SYNC_XTION_GAME[sxi].status 
      = SYNC_XTION_GAME[sxi].status | (PROCESS[pi].status & MASK_GAME_ROLES); 
    } 	
  } 
/*
  fprintf(RED_OUT, "After prepare sync\n"); 
  report_red_management(); 

  print_resources("After preparing sync xtions");
*/
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\n** Regular sync xtions **\n"); 
  fprintf(RED_OUT, "\nRT[XI_SYNC_BULK=%1d]:\n", XI_SYNC_BULK);
  red_print_graph(RT[XI_SYNC_BULK]);
  print_sync_xtions(SYNC_XTION, SYNC_XTION_COUNT); 
  fprintf(RED_OUT, "\n\n** Game sync xtions **\n"); 
  fprintf(RED_OUT, "\nRT[XI_GAME_SYNC_BULK=%1d]:\n", XI_GAME_SYNC_BULK);
  red_print_graph(RT[XI_GAME_SYNC_BULK]);
  print_sync_xtions(SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME); 
  #endif 

/*
  print_resources("After ec management");
  fprintf(RED_OUT, "\nRT[XI_GAME_SYNC_BULK=%1d]:\n", XI_GAME_SYNC_BULK);
  red_print_graph(RT[XI_GAME_SYNC_BULK]);
  fprintf(RED_OUT, "After prepare_sync_xtions(), SYNC_XTION_GAME[0].qfd_sync=%x\n", 
	  SYNC_XTION_GAME[0].qfd_sync
	  ); 
  fflush(RED_OUT); 
 */
  if (RT[XI_GAME_SYNC_BULK] == NORM_FALSE) { 
    RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS] = NORM_FALSE; 
    RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION] = NORM_FALSE; 
  }
  else { 
    RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS] 
    = red_add_trigger_sync_bulk(RT[XI_GAME_SYNC_BULK]); 
    red_mark(RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS], FLAG_GC_STABLE); 

    #ifdef RED_DEBUG_BISIM_MODE
    print_cpu_time("After adding final restrictions, RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS=%d]:\n", XI_GAME_SYNC_BULK_WITH_TRIGGERS);
    red_print_graph(RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS]);
    #endif 
    
    RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION] 
    = add_post_condition(RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS]);
    red_mark(RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION], FLAG_GC_STABLE); 
    garbage_collect(FLAG_GC_SILENT); 

    #ifdef RED_DEBUG_BISIM_MODE
    print_resources( 
      "After adding postcondition to RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION=%d]:\n", 
      XI_GAME_SYNC_BULK_WITH_POSTCONDITION 
    );
    red_print_graph(RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION]);
    #endif 

/*
  fprintf(RED_OUT, 
          "\nLeaving sync bulk restriction\nRT[XI_GAME_SYNC_ALL=%1d]:\n", 
          XI_GAME_SYNC_ALL
          );
  red_print_graph(RT[XI_GAME_SYNC_ALL]);
  fprintf(RED_OUT, 
          "RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS=%1d]:\n", 
          XI_GAME_SYNC_BULK_WITH_TRIGGERS
          );
  red_print_graph(RT[XI_GAME_SYNC_BULK_WITH_TRIGGERS]);
  fprintf(RED_OUT, 
          "RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION=%1d]:\n", 
          XI_GAME_SYNC_BULK_WITH_POSTCONDITION
          );
  red_print_graph(RT[XI_GAME_SYNC_BULK_WITH_POSTCONDITION]);
  fprintf(RED_OUT, "\nTo garbage report for FILTER_SYNC_XI_RESTRICTION\n");
  */
  } 
/*
  print_resources("after ec mode restrictor"); 
*/  
 
  /* Construct RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]] 
  */ 
  RT[GAME_ROLE_INITIAL[FLAG_GAME_SPEC]] 
  = red_game_eliminate_roles(RT[INDEX_INITIAL], FLAG_GAME_MODL); 
  RT[GAME_ROLE_INITIAL[FLAG_GAME_MODL]] 
  = red_game_eliminate_roles(RT[INDEX_INITIAL], FLAG_GAME_SPEC); 
  red_mark(RT[GAME_ROLE_INITIAL[FLAG_GAME_SPEC]], FLAG_GC_STABLE);
  red_mark(RT[GAME_ROLE_INITIAL[FLAG_GAME_MODL]], FLAG_GC_STABLE);

  RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]] 
  = red_game_invariance(FLAG_GAME_MODL);   
  red_mark(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]], FLAG_GC_STABLE);  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    "\n####### RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL=%1d]=%x] #######\n", 
    FLAG_GAME_MODL, RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]
  ); 
  red_print_graph(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]); 
  #endif 
  
  /* Construct RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]] 
  */ 
  RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]] 
  = red_game_invariance(FLAG_GAME_SPEC); 
  red_mark(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]], FLAG_GC_STABLE);  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    "\n####### RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC=%1d]=%x] #######\n", 
    FLAG_GAME_SPEC, RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]]
  ); 
  red_print_graph(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]]); 
  #endif 

  RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES] 
  = red_bop(AND, RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]], 
    RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]]
  ); 
  RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES] 
  = red_bop(AND, RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      red_game_mode_restrictor(MASK_GAME_ROLES)
    ); 
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After game mode restrictor for %x, RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES=%d]:\n", 
    FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL, 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES 
  );
  red_print_graph(RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
  #endif 

  RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  = red_hull_normalize(INDEX_GAME_INVARIANCE_WITH_EQUALITIES); 
  red_mark(RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], FLAG_GC_STABLE); 

  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After normalization %x, RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES=%d]:\n", 
    FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL, 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES 
  );
  red_print_graph(RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
  #endif 
  
  RT[EC_INVARIANCE_WITH_ONLY_DIAGONAL] 
  = red_eliminate_magnitudes(RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
  red_mark(RT[EC_INVARIANCE_WITH_ONLY_DIAGONAL], FLAG_GC_STABLE);  

  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After game mode restrictor elm mag for %x, RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES=%d]:\n", 
    FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL, 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES 
  );
  fprintf(RED_OUT, "\nRT[EC_INVARIANCE_WITH_ONLY_DIAGONAL=%1d]:\n", EC_INVARIANCE_WITH_ONLY_DIAGONAL); 
  red_print_graph(RT[EC_INVARIANCE_WITH_ONLY_DIAGONAL]); 
  #endif 

  RT[XI_GAME_SPEC_SYNC_BULK] = red_ec_role_nullify( 
    RT[XI_GAME_SYNC_BULK], FLAG_GAME_SPEC, FLAG_GAME_MODL
  ); 
  red_mark(RT[XI_GAME_SPEC_SYNC_BULK], FLAG_GC_STABLE);
  
  RT[XI_GAME_MODL_SYNC_BULK] = red_ec_role_nullify(
    RT[XI_GAME_SYNC_BULK], FLAG_GAME_MODL, FLAG_GAME_SPEC
  ); 
  red_mark(RT[XI_GAME_MODL_SYNC_BULK], FLAG_GC_STABLE);
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "RED EC XI SPEC SYNC BULK (in redparse.c):\n"); 
  red_print_graph(RT[XI_GAME_SPEC_SYNC_BULK]);
  fprintf(RED_OUT, "RED EC XI MODL SYNC BULK (in redparse.c):\n"); 
  red_print_graph(RT[XI_GAME_MODL_SYNC_BULK]);
  #endif 

  /* Note the following procedure must happen no earlier than now 
   * since it uses RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]] and 
   * RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]. 
   */ 
  prepare_game_sync_xtion_representatives(FLAG_GAME_SPEC); 
  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After preparing ec sync representatives for SPEC"  
  ); 
  #endif 
  
  prepare_game_sync_xtion_representatives(FLAG_GAME_MODL); 

  RT[result = RT_TOP++] = NORM_FALSE; 
  for (sxi = 0; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    SYNC_XTION_GAME[sxi].red_pre 
    = red_role_event_precondition_sync_specific(
      PS_EXP_TRUE, 
      SYNC_XTION_GAME[sxi].red_trigger, 
      INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
      NULL, 
      INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
      
      NORM_FALSE, 
      NORM_FALSE, 
      sxi, 
      SYNC_XTION_GAME, 
      NULL,  

      MASK_GAME_ROLES, 
      FLAG_OPPONENT_KEEP,       
      FLAG_ROOT_NOAPPROX, 
      TYPE_FALSE // no post processing   
    );
    red_mark(SYNC_XTION_GAME[sxi].red_pre, FLAG_GC_STABLE); 
    RT[result] = red_bop(OR, RT[result], SYNC_XTION_GAME[sxi].red_pre); 
  } 
  RED_GAME_SYNC_BULK_PRE = red_role_event_precondition_sync_bulk(
    NORM_NO_RESTRICTION, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
    NULL, 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
    
    NORM_FALSE, 
    NORM_FALSE, 
    XI_GAME_SYNC_BULK, 
    NULL, 
    MASK_GAME_ROLES, 
    
    FLAG_OPPONENT_KEEP, 
    FLAG_ROOT_NOAPPROX, 
    TYPE_FALSE // no post processing   
  ); 
  red_mark(RED_GAME_SYNC_BULK_PRE, FLAG_GC_STABLE); 

  RT[result] = red_bop(OR, RT[result], RED_GAME_SYNC_BULK_PRE); 
  RED_GAME_SYNC_ALL_PRE = RT[result]; 
  red_mark(RED_GAME_SYNC_ALL_PRE, FLAG_GC_STABLE); 
  RT_TOP--; // result 

  RED_GAME_SYNC_NEG_PRE = (struct red_type **) 
    malloc((SYNC_XTION_COUNT+1)*sizeof(struct red_type *)); 
    
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
    if (SYNC_XTION[sxi].status & FLAG_GAME_MODL) { 
      conj = NORM_FALSE; 
      for (sxj = 0; sxj < SYNC_XTION_COUNT_GAME; sxj++) { 
    	if (SYNC_XTION_GAME[sxj].ec_representative[FLAG_GAME_MODL] == sxi) 
    	  conj = red_bop(OR, conj, SYNC_XTION_GAME[sxj].red_pre); 
      } 
      SYNC_XTION[sxi].red_pre = red_bop(AND, conj, 
        SYNC_XTION[sxi].red_pre 
      ); 
      red_mark(SYNC_XTION[sxi].red_pre, FLAG_GC_STABLE); 
    } 
    else if (SYNC_XTION[sxi].status & FLAG_GAME_SPEC) { 
      conj = NORM_FALSE; 
      for (sxj = 0; sxj < SYNC_XTION_COUNT_GAME; sxj++) { 
    	if (SYNC_XTION_GAME[sxj].ec_representative[FLAG_GAME_SPEC] == sxi) 
    	  conj = red_bop(OR, conj, SYNC_XTION_GAME[sxj].red_pre); 
      } 
      SYNC_XTION[sxi].red_pre = red_bop(AND, conj, 
        SYNC_XTION[sxi].red_pre 
      ); 
      red_mark(SYNC_XTION[sxi].red_pre, FLAG_GC_STABLE); 
    } 
    RED_GAME_SYNC_NEG_PRE[sxi] = red_bop(AND, RED_GAME_SYNC_ALL_PRE, 
      red_complement(SYNC_XTION[sxi].red_pre)
    ); 
    red_mark(RED_GAME_SYNC_NEG_PRE[sxi], FLAG_GC_STABLE);
  } 
  
  RED_GAME_INV_DIFF = (struct red_type **) 
    malloc(4*sizeof(struct red_type *)); 
  RED_GAME_INV_DIFF[FLAG_GAME_MODL] = red_bop(AND, 
    RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]], 
    red_complement(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]]) 
  ); 
  RED_GAME_INV_DIFF[FLAG_GAME_SPEC] = red_bop(AND, 
    RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]], 
    red_complement(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]) 
  ); 
  red_mark(RED_GAME_INV_DIFF[FLAG_GAME_MODL], FLAG_GC_STABLE);
  red_mark(RED_GAME_INV_DIFF[FLAG_GAME_SPEC], FLAG_GC_STABLE);


  #ifdef RED_DEBUG_BISIM_MODE
  print_resources( 
    "After preparing ec sync representatives for MODL"  
  );
  
/*
  fprintf(RED_OUT, "\n** %1d SYNC XTION **\n", SYNC_XTION_COUNT); 
  print_sync_xtions(SYNC_XTION, SYNC_XTION_COUNT); 
  fprintf(RED_OUT, "\n** %1d GAME SYNC XTION **\n", SYNC_XTION_COUNT_GAME); 
  print_sync_xtions(SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME); 
*/
  fprintf(RED_OUT, 
    "after the two prepare_game_sync_xtion_representatives(), RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
  
  /* We now calculate the bisimulation negation inequality 
   */ 
/*
  RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]] 
  = red_ineq_universe_sync_bulk(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]], 
    FLAG_GAME_MODL
  ); 
  RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_SPEC]] 
  = red_ineq_universe_sync_bulk(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]], 
    FLAG_GAME_SPEC
  ); 
*/    
  /* Finally reset the convenient run-time stack top index for the 
   * marking of active diagrams. 
   * Since most of the simulation related diagrams have now been constructed. 
   * We lift the top index back to its normal value. 
   */ 
  RT_DYNAMIC = INDEX_BOTTOM_OF_RUNTIME_STACK; 
/*
  fprintf(RED_OUT, "\nEC %1d.3, after NZF:\n", ITERATION_COUNT); 
  print_resources("after NZF of all image"); 
  red_print_graph(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]);   
*/

} 
  /* construct_bisim_structures_for_a_role_spec() */ 
  




  
  
  

int	pp_flag=0, count_ec_elm = 0; 


  






  
  
/*************************************************************************************
    A) \eta = \forall (e0,e1)
                \forall t(
                  (\eta+t\models (e0,e1) && \forall t'(t'<=t && 0<=t' && w+t')) 
                     --> \exists (v1,t1)...(vk,tk) (tk-t1==t && vk\models (e0,e1,e2))
                   )
                 
       \eta = \forall (e0,e1) 
                 \neg \exists t 
                   (   (\eta+t\models (e0,e1) && \forall t'(t'<=t&& 0<=t' && w+t'))
                    && \neg \exists (v1,t1)...(vk,tk) with only e2 transitions such that  
                          (tk-t1==t && vk\models (e0,e1,e2))
                    )
 */ 






  
int	count_xxx_pp = 0; 
#define	STOP_COUNT_GAME_ELM	-1





  
  
  
struct ps_exp_type	*SPEC_GAME_EALWAYS;

   

  



  
struct red_type	*RED_GAME_INITIAL; 


  
  
  
  

 
 
 
