/*****************************************************
 *  How we solve the simulation game ? 
 *  There are two key issues in the algorithm. 
 
 1. The first is how to evaluate the existence of a strategy of 
 *  the spec to simulate all behaviors of the model and the environment. 
 *  This is according to the definition of Rajamani, Kupferman, and 
 *  Henzinger. 
 *  However, since it is a concurrent game between the spec (S) and the 
 *  the model (M) in the arena of the envr (E), 
 *  the non-existence of a winning strategy of the S 
 *  does not imply the existence of a winning strategy of the MxE. 
 *  In fact, it implies that for all strategies of S, 
 *  there exists a strategy of MxE that works to develop an evidence 
 *  that shows how S can be violated. 
 
    1a. Explicit state. 
        We first consider the explicit-state case. 
    
        1aA. 
        In the non-deterministic case, S does not need to make a move. 
        In this case, then MxE can use an internal sequence to drive SxMxE
        to a state outside S. 
        
        1aB. 
        We then need to evaluate the condition 
        to D that cannot be avoided by S. 
        This may happen when MxE issues an event K and S must respond. 

          forall (a,b) of S matching K and for all t, 
            exists (c1,d1)...(cn,dn) of MxE of S matching K at t
              ends at NSIM.  
          = forall (a,b) of S matching K and a t, 
              exists (c1,d1)...(cn,dn) of MxE of S matching K at t
                ends at NSIM.  
          = forall (a,b) (
              T(Path(SxE),xtion(a,b,elim_role(~SIM,M))&&PTIME=C)
              => Rch(Path, xtion(a,b,c,d, ~SIM)&&PTIME=C)
            )
          = forall (a,b) (
              ~T(Path(SxE),xtion(a,b,elim_role(~SIM,M))&&PTIME=C)
              || Rch(Path, xtion(a,b,c,d, ~SIM)&&PTIME=C)
            )

 2. The second is how to evaluate the initial condition of negated 
    branch simulation. 
 */ 
 
 
/*************************************************
 *
   The following formulation is good for positive evaluation of 
   timed braching simulation. 
   
          exists (a,b) of S matching K at t, 
            forall (c1,d1)...(cn,dn) of MxE of S matching K at t
              ends at B.  
          = exists (a,b) of S matching K at t, 
            ~exists (c1,d1)...(cn,dn) of MxE of S matching K at t
              ends at ~B.  
              
            But what is ~B: 
            1) A state in which M can do an event while S cannot. 
            2) Out of the invariance condition of S but still in the invariance 
               of M. 

 */
 
/**********************************************************
 * 2012/05/12
 
   The newest formulation for <M> p is 
     stutter_reach<S> (true, xtion<M>(p&& x=C)) 
     && !stutter_reach<S>(true, xtion<M>(~p&& x=C)) 
   However, the condition is that <M> transition must be observable with 
   an event. 
   
   Now the most difficult situation is the matching of the local 
   transitions of <M>. 
   We basically need to let time pass, stay in ~p for zero time units, and 
   then let time pass again. 
   This pretty much says that we need to do time progress with 
     stutter_reach<S> (true, xtion<M>(p&& x=C)) 
     && !stutter_reach<S>(
           x<C||(x==C&&~p), 
           xtion<local(M)>(x==C&&T((~p&&x==C)||x>C, x>C))
         )
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
#include "bisim.e" 

#include "redgame.h" 

int	
  NZF, 
  FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, 
  MODL_FAIRNESS, SPEC_FAIRNESS; 

int			token_fair_sim; 

struct ps_exp_type	*game_modl_envr_exp, 
			*game_spec_envr_exp; 






inline int	flag_opponent(
  int 	flag_roles
) {
  switch (flag_roles) { 
  case FLAG_GAME_MODL: 
  case (FLAG_GAME_MODL | FLAG_GAME_ENVR): 
    return (FLAG_GAME_SPEC); 
  case FLAG_GAME_SPEC: 
  case (FLAG_GAME_SPEC | FLAG_GAME_ENVR): 
    return (FLAG_GAME_MODL); 
  case MASK_GAME_ROLES: 
    return (0); 
  default: 
    fprintf(RED_OUT, 
      "\nError: Illegal game roles %x in flag_opponent_role().\n", 
      flag_roles
    );
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* flag_opponent() */  
  
  
    



  
int	FLAG_GAME_ONE_PLANT_ONLY, 
	PREIMAGE_GAME_ONE_PLANT_ONLY, 
	IMAGE_GAME_ONE_PLANT_ONLY, 
	ACC_IMAGE_GAME_ONE_PLANT_ONLY; 


struct red_type	*game_role_fairness_bck(
  struct ps_exp_type	*game_role_spec, 
  int			flag_role  
) {
  struct cache2_hash_entry_type	*ce; 

  ce = cache2_check_result_key(
    OP_ROLE_FAIRNESS_BCK, 
    (struct red_type *) game_role_spec, 
    (struct red_type *) flag_role 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
  switch (flag_role) { 
  case FLAG_GAME_MODL: 
    if (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
           == FLAG_ZENO_CYCLE_OK
        && GAME_MODL_EXP->u.mexp.strong_fairness_list == NULL 
        ) 
      ce->result = RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]]; 
    else 
      ce->result = role_fairness_bck(
        game_role_spec, 
        TYPE_TRUE, 
        GAME_ROLE_INVARIANCE[FLAG_GAME_MODL], 
        GAME_ROLE_INVARIANCE[FLAG_GAME_MODL], 
        FLAG_GAME_ENVR | FLAG_GAME_MODL, 
        FLAG_ROOT_NOAPPROX, 
        FLAG_TCTCTL_SUBFORM  
      ); 
    break; 
  case FLAG_GAME_SPEC: 
    if (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
           == FLAG_ZENO_CYCLE_OK
        && GAME_SPEC_EXP->u.mexp.strong_fairness_list == NULL 
        ) 
      ce->result = RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]]; 
    else 
      ce->result = role_fairness_bck(
        game_role_spec, 
        TYPE_TRUE, 
        GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC], 
        GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC], 
        FLAG_GAME_ENVR | FLAG_GAME_SPEC, 
        FLAG_ROOT_NOAPPROX, 
        FLAG_TCTCTL_SUBFORM  
      ); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nError: Illegal role %x in game_role_fairness_bck().\n", 
      flag_role 
    ); 
    fflush(RED_OUT); 
    exit(0); 
/* 
  case MASK_GAME_ROLES: 
    ce->result = role_fairness_bck(
      game_role_spec, 
      TYPE_TRUE, 
      DECLARED_GLOBAL_INVARIANCE, 
      DECLARED_GLOBAL_INVARIANCE, 
      SYNC_XTION_COUNT, 
      SYNC_XTION, 
      XI_SYNC_BULK, 
      XI_SYNC_BULK_WITH_TRIGGERS, 
      FLAG_GAME_ENVR | FLAG_GAME_SPEC | FLAG_GAME_MODL, 
      FLAG_ROOT_NOAPPROX  
    ); 
    break; 
*/
  }
/*
  fprintf(RED_OUT, "\n==(After calculating game role %s fairness for)==: \n  ", 
    role_name(flag_role)
  ); 
  pcform(game_role_spec);  
  red_print_graph(ce->result); 
*/    
  return(ce->result); 
}
  /* game_role_fairness_bck() */ 
  
  
  
  
void	game_fairness_event_diagram_processing(
  struct ps_fairness_link_type	*fl  
) {  
  for (; fl; fl = fl->next_ps_fairness_link) { 
    if (   fl->fairness->u.eexp.event_exp 
        && fl->fairness->u.eexp.event_exp != PS_EXP_TRUE
        ) {
      fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp 
      = red_bop(AND, 
        fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp, 
        RT[XI_GAME_SYNC_BULK_WITH_EVENTS]
      ); 
      fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp 
      = red_type_eliminate(
        fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp, 
        TYPE_SYNCHRONIZER
      ); 
      red_mark(fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp, 
        FLAG_GC_STABLE
      ); 
    } 
  }
}
  /* game_fairness_event_diagram_processing() */ 




struct ps_exp_type	*prepare_game_fairness( 
  struct ps_exp_type	*modl_fairness_exp, 
  struct ps_exp_type	*spec_fairness_exp, 
  struct ps_exp_type	*envr_fairness_exp, 
  int			role_sim_destroyer 
) {  
  struct ps_fairness_link_type	*fl; 
  struct ps_exp_type		*fairness_exp, *f;
  int				orig_fairness_estatus;  

  game_fairness_event_diagram_processing(
    modl_fairness_exp->u.mexp.strong_fairness_list
  ); 
  game_fairness_event_diagram_processing(
    modl_fairness_exp->u.mexp.weak_fairness_list
  ); 
  game_fairness_event_diagram_processing(
    spec_fairness_exp->u.mexp.strong_fairness_list
  ); 
  game_fairness_event_diagram_processing(
    spec_fairness_exp->u.mexp.weak_fairness_list
  ); 
  game_fairness_event_diagram_processing(
    envr_fairness_exp->u.mexp.strong_fairness_list
  ); 
  game_fairness_event_diagram_processing(
    envr_fairness_exp->u.mexp.weak_fairness_list
  ); 
  
  
  fairness_exp = ps_exp_copy(envr_fairness_exp); 
  for (fl = modl_fairness_exp->u.mexp.strong_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) { 
    fairness_exp->u.mexp.strong_fairness_list = insert_sorted_flist(
      fl->fairness, 
      fl->status,  
      fairness_exp->u.mexp.strong_fairness_list, 
      &(fairness_exp->u.mexp.strong_fairness_count) 
    );
  } 

  for (fl = modl_fairness_exp->u.mexp.weak_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) { 
    fairness_exp->u.mexp.weak_fairness_list = insert_sorted_flist(
      fl->fairness, 
      fl->status,  
      fairness_exp->u.mexp.weak_fairness_list, 
      &(fairness_exp->u.mexp.weak_fairness_count) 
    );
  } 
  
  // Second, we try to negate the specification strong fairness assumptions. 
  if (fl = spec_fairness_exp->u.mexp.strong_fairness_list) { 
    orig_fairness_estatus = fairness_exp->exp_status; 
    fairness_exp->exp_status = fairness_exp->exp_status | FLAG_FAIRNESS_WEAK; 

    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\n==================================================\n"); 
    print_resources("Fair GFP"); 
    fprintf(RED_OUT, "FSIM %1d, Checking strong fairness %1d of SPEC:\n", 
      FSIM_SPEC_ITER, FSIM_SPEC_ITER 
    ); 
    pcform(fl->fairness); 
    #endif 
    /* We first update the split time path components. 
     */ 
    f = ps_exp_copy(fl->fairness); 
    if (fl->fairness->u.eexp.event_exp == NULL) {
    /* Now we calculate the new greatest fixpoint. 
     */ 
      f->u.eexp.precond_exp = add_neg(fl->fairness->u.eexp.precond_exp); 
    } 
    else { 
      f->u.eexp.postcond_exp = add_neg(fl->fairness->u.eexp.postcond_exp); 
    }
    fairness_exp->u.mexp.weak_fairness_list = insert_sorted_flist(
      f, 
      fl->status,  
      fairness_exp->u.mexp.weak_fairness_list, 
      &(fairness_exp->u.mexp.weak_fairness_count) 
    );
  } 
  else if (fl = spec_fairness_exp->u.mexp.weak_fairness_list) { 
    orig_fairness_estatus = fairness_exp->exp_status; 
    fairness_exp->exp_status = fairness_exp->exp_status | FLAG_FAIRNESS_WEAK; 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\n==================================================\n"); 
    print_resources("FSIM %1d, Fair GFP", FSIM_SPEC_ITER); 
    fprintf(RED_OUT, "FSIM %1d, Checking weak fairness %1d of SPEC:\n", 
      FSIM_SPEC_ITER, FSIM_SPEC_ITER
    ); 
    pcform(fl->fairness); 
    #endif 

    f = ps_exp_copy(fl->fairness); 
    if (fl->fairness->u.eexp.event_exp == NULL) {
    /* Now we calculate the new greatest fixpoint. 
     */ 
      f->u.eexp.precond_exp = add_neg(fl->fairness->u.eexp.precond_exp); 
    } 
    else { 
      f->u.eexp.postcond_exp = add_neg(fl->fairness->u.eexp.postcond_exp); 
    }
    fairness_exp->u.mexp.strong_fairness_list = insert_sorted_flist(
      f, 
      fl->status,  
      fairness_exp->u.mexp.strong_fairness_list, 
      &(fairness_exp->u.mexp.strong_fairness_count) 
    );
  } 
  return(ps_exp_share(fairness_exp)); 
} 
  /* prepare_game_fairness() */ 
  
  

/********************************************************************
 *
    The following routines are for the one-player single-step 
    precondition universe.  
 */ 
int	count_ineq_universe = 0; 
#define	FLAG_FAIR_SIM	1
#define FLAG_BRANCH_SIM	0 

#define	FLAG_STEP_TIME_MEASURE		1
#define	FLAG_NO_STEP_TIME_MEASURE	0 
    


struct red_type	*red_game_collective_precondition_sync_bulk(
  struct red_type		*red_game_sync_bulk_from_event_exp, 
  struct red_type		*red_dest_event_precond, 
  struct red_type		*red_base, 
  struct red_type		*red_path, 
  struct ps_fairness_link_type	*weak_fairness_list, 

  int				role_sim_destroyer  
) { 
  int	sxj, base, path, explore, acc; 
  
  RT[base = RT_TOP++] = red_base; 
  RT[path = RT_TOP++] = red_path; 
  RT[acc = RT_TOP++] = red_role_event_precondition_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_dest_event_precond, 
    base, 
    NULL, 
    path, 
  
    NORM_FALSE, 
    NORM_FALSE, 
    XI_GAME_SYNC_BULK, 
    weak_fairness_list,  
    MASK_GAME_ROLES, 
    
    FLAG_OPPONENT_KEEP, // eliminate or keep
    FLAG_ROOT_NOAPPROX, 
    FLAG_NO_POST_PROCESSING    
  ); 
  RT_TOP--; // acc 
  RT_TOP--; // path 
  RT_TOP--; // base 
  
  return(RT[acc]); 
} 
  /* red_game_collective_precondition_sync_bulk() */ 


int	check_sync_xtion_observable(int sxi) { 
  int	ipi, xi; 
  
  if (   (SYNC_XTION[sxi].status & FLAG_XTION_GLOBAL_WRITING)
      || (SYNC_XTION[sxi].status & FLAG_XTION_PEER_WRITING) 
      ) 
    return(TYPE_TRUE); 
  else for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) {
    xi = SYNC_XTION[sxi].party[ipi].xtion; 
    if (XTION[xi].sync_count) 
      return(TYPE_TRUE); 	
  }
  return(TYPE_FALSE); 
}
  /* check_sync_xtion_observable() */ 




char	s[100]; 

char	*fseq(char *cs) { 
  int	p; 
  
  if (FSIM_ITER == -1) { 
    if (GUNTIL_ITER == -1) 
      sprintf(s, "In %s, \0", cs);
    else 
      sprintf(s, "In %s, BU%1d\0", cs, GUNTIL_ITER); 	
  } 
  else { 
    sprintf(s, "In %s, I%1d \0", cs, FSIM_ITER); 
    p = strlen(s); 
    if (GUNTIL_ITER == -1) { 
      sprintf(&(s[p]), "S%1d\0", FSIM_STRONG_ITER); 
    }
    else { 
      sprintf(&(s[p]), "S%1d U%1d\0", FSIM_STRONG_ITER, GUNTIL_ITER); 
    } 
  }
  return(s); 
}
  /* fseq() */ 




struct red_type	*red_game_collective_precondition_sync_ITERATIVE(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_dest_event_precond, 
  struct red_type		*red_base, 
  struct red_type		*red_path, 
  int				sxi, 
  
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				role_sim_destroyer  
) { 
  int	sxj, base, path, explore, acc, ipi; 
  
  RT[acc = RT_TOP++] = NORM_FALSE; 
  RT[base = RT_TOP++] = red_base; 
  RT[path = RT_TOP++] = red_path; 
  for (ipi = 0; 
       ipi < SYNC_XTION[sxi].ec_representative[role_sim_destroyer]; 
       ipi++
       ) { 
    sxj = SYNC_XTION[sxi].ec_representee[role_sim_destroyer][ipi]; 
    #ifdef RED_DEBUG_GAME_MODE
    if (FSIM_ITER == 2 && sxi == 11) { 
      fprintf(RED_OUT, "EC %1d, matching sxi=%1d-->sxj=%1d\n", 
        ITERATION_COUNT, sxi, sxj
      ); 
      print_sync_xtion_lines(sxj, SYNC_XTION_GAME); 
    }
    #endif 
    if (   SYNC_XTION_GAME[sxj].ec_representative[role_sim_destroyer] != sxi
        /* The following requirement says that if sxi is for role, 
         * then sxj must be for both the role and the opponent. 
         * One key issue is how to deal with an sxi that has only 
         * ENVR transitions. 
         */ 
/*
        || (   check_sync_xtion_observable(sxi)  
            && !(  SYNC_XTION_GAME[sxj].status 
                 & flag_opponent(role_sim_destroyer)
            )    )    
*/
        ) {
      #ifdef RED_DEBUG_GAME_MODE
      fprintf(RED_OUT, "sxi=%1d, sxj=%1d skipped!\n", sxi, sxj); 
      #endif 
      continue; 
    }
    RT[explore = RT_TOP++] = red_role_event_precondition_sync_specific(
      event_exp, 
      red_dest_event_precond, 
      base, 
      NULL, 
      path, 
    
      NORM_FALSE, 
      NORM_FALSE, 
      sxj, 
      SYNC_XTION_GAME, 
      weak_fairness_list, 
      
      MASK_GAME_ROLES, 
      FLAG_OPPONENT_KEEP, 
      FLAG_ROOT_NOAPPROX, 
      FLAG_POST_PROCESSING   
    );  
    RT[explore] = red_bop(AND, RT[explore], red_dest_event_precond); 
    #ifdef RED_DEBUG_GAME_MODE
      fprintf(RED_OUT, 
        "%s, sxi %1d--> sxj %1d, precondition to RT[explore]:\n", 
        fseq("sync ITER"), sxi, sxj
      ); 
      red_print_graph(RT[explore]); 
      fflush(RED_OUT); 
    #endif 
    RT[acc] = red_bop(OR, RT[acc], RT[explore]); 
    RT_TOP--; // explore 
  }
  RT_TOP--; // path 
  RT_TOP--; // base 
  RT_TOP--; // acc 
  
  return(RT[acc]); 
} 
  /* red_game_collective_precondition_sync_ITERATIVE() */ 




#define FLAG_FOR_SIM_EVIDENCE	0
#define FLAG_FOR_NEG_SIM	1

struct red_type	*red_game_event_role_stutter_reachable_bck(
  struct red_type		*red_base, 
  struct red_type		*red_path, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_role, 
  int				sxi_sync, 
  int				flag_for_eon  
) { 
  int			pi, sxi, ipi, ii, 
			path, reach, 
			cur, // current reachable fragment 
			pre; // previous reachable fragment 
  struct red_type	*conj; 
  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
  #endif 
  #ifdef RED_DEBUG_GAME_MODE
  int			test; 
  #endif 
    
  FLAG_GAME_ONE_PLANT_ONLY = flag_role; 
  #ifdef RED_DEBUG_GAME_MODE
/*
    check_bisim_state("Entering game role stutter reachable bck() from:", 
      d, ITERATION_COUNT, 
      (FLAG_GAME_MODL | FLAG_GAME_SPEC) & ~flag_role, 
      sxi_sync
    ); 
*/
    red_print_graph(red_opp_mismatches); 
  #endif 
  RT[path = RT_TOP++] = red_path; 
  RT[reach = RT_TOP++] = red_base;  
  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_TIMED) {
    if (   flag_for_eon == FLAG_FOR_SIM_EVIDENCE 
        && sxi_sync >= 0 
        && sxi_sync < SYNC_XTION_COUNT
        && !check_sync_xtion_observable(sxi_sync)
        ) { 
    /* This is the case of a totally local MODL transition that 
       the SPEC wants to match also with one of its local transitions. 
       In this case, since there could be many eligible 
       local SPEC transitions, we must make sure that this is 
       the last one in a sequence before PLAY_TIME advances to over 
       the biggest timing constant. 
     */ 
      RT[reach] = crd_one_constraint(RT[reach], 
        ZONE[0][PLAY_TIME], CLOCK_NEG_INFINITY
      );  
/*
      RT[path] = crd_one_constraint(RT[path], 
        ZONE[0][PLAY_TIME], CLOCK_NEG_INFINITY+1 
      );  
*/
      RT[reach] = red_game_time_progress_bck(
        NULL, 
        reach, path, MASK_GAME_ROLES, 
        TYPE_TRUE   
      ); 
      RT[reach] = crd_one_constraint(RT[reach], 
        ZONE[PLAY_TIME][0], CLOCK_POS_INFINITY-1 
      );  
    }
    else { 
      RT[reach] = crd_one_constraint(RT[reach], 
        ZONE[0][PLAY_TIME], CLOCK_NEG_INFINITY+1
      );  
      RT[reach] = crd_one_constraint(RT[reach], 
        ZONE[PLAY_TIME][0], CLOCK_POS_INFINITY-1
      );  
      RT[reach] = red_game_time_progress_bck(
        NULL, 
        reach, path, MASK_GAME_ROLES, 
        TYPE_TRUE   
      ); 
    }
  }

  #ifdef RED_DEBUG_GAME_MODE
/*
    check_bisim_state(
      "EC stutter after initial time progress", 
      RT[reach], ITERATION_COUNT, 
      (FLAG_GAME_MODL | FLAG_GAME_SPEC) & ~flag_role, 
      sxi_sync
    ); 
*/
//    red_print_graph(RT[reach]); 
  #endif 
  RT[path] = red_path; 
  RT[reach] = red_hull_normalize(reach); 
  #ifdef RED_DEBUG_GAME_MODE
  print_resources("EC stutter after initial normalization"); 
  RT[test = RT_TOP++] = RT[reach]; 
  test = reach; 
  reach = test+1; 

  fprintf(RED_OUT, "EC stuttering seed after time progress:\n"); 
  fprintf(RED_OUT, "RT[test=%1d]=%x, RT[reach=%1d]=%x\n", 
    test, RT[test], 
    reach, RT[reach]
  ); 
  red_print_graph(RT[reach]); 
  #endif 
  RT[cur = RT_TOP++] = RT[reach]; 
  // this is only used for ec_explore_sync_bulk_precondition_one_plant_only()
  for (ii = 0; RT[cur] != NORM_FALSE; ii++) { 
    
    #ifdef RED_DEBUG_GAME_MODE
    #endif 
    RT[pre = RT_TOP++] = red_role_event_precondition(
      PS_EXP_TRUE, 
      NORM_NO_RESTRICTION, 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      cur, 
      NULL, 
      
      path, 
      NORM_FALSE, 
      RT[reach], 
      SYNC_XTION_GAME, 
      SYNC_XTION_COUNT_GAME, 
      
      XI_GAME_SYNC_BULK, 
      weak_fairness_list, 
      flag_role, 
      FLAG_OPPONENT_KEEP, 
      FLAG_ROOT_NOAPPROX, 
      
      FLAG_POST_PROCESSING  
    ); 

    RT[pre] = red_hull_normalize(pre); 

    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "IT_EC=%1d, %s %s, EC stutter %1d:\nwith preimiage from role events:\n", 
      ITERATION_COUNT, role_name(flag_role), sxi_string(sxi_sync), ii
    ); 
    red_print_graph(RT[pre]); 
    #endif 
      
    union_abstract_new(reach, pre, 0); 
    RT[cur] = RT[pre]; 
    RT_TOP--; /* pre */ 
    garbage_collect(FLAG_GC_SILENT);

    #ifdef RED_DEBUG_GAME_MODE
    print_resources( 
      "IT_EC=%1d, %s %s, == stutter iteration %1d =================\nIMAGE:\n", 
      ITERATION_COUNT, role_name(flag_role), sxi_string(sxi_sync), ii
    ); 

    fprintf(RED_OUT, "IMAGE:\n");  
    red_print_graph(RT[cur]); 
    fprintf(RED_OUT, 
      "IT_EC=%1d, %s %s, == stutter iteration %1d PREIMAGE:\n", 
      ITERATION_COUNT, role_name(flag_role), sxi_string(sxi_sync), ii
    ); 
    red_print_graph(RT[reach]); 
    #endif 
  } 
  RT_TOP--; // cur  
  
  #ifdef RED_DEBUG_GAME_MODE
  if (RT[test] != RT[reach]) { 

    fprintf(RED_OUT, 
      "For hcd1.1.3.d, it is strange that RT[reach=%1d] has changed after the stuttering processing.\n", 
      reach
    ); 
    fprintf(RED_OUT, "RT[test=%1d]=%x, RT[reach=%1d]=%x\n", 
      test, RT[test], 
      reach, RT[reach]
    ); 
    red_print_graph(RT[reach]); 
    fflush(RED_OUT); 

  } 
  RT_TOP--; // test 
  #endif 

  RT_TOP = RT_TOP-2; /* reach, 
		      * path, 
		      */  
  
  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: the RT_TOP value is not consistent in red_game_event_role_stutter_reachable_bck()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
  #endif 
  
  return(RT[reach]); 
}
  /* red_game_event_role_stutter_reachable_bck() */  



struct red_type	*red_game_collective_reachable_sync_ITERATIVE(
  struct red_type		*red_event_precond, 
  struct red_type		*red_base, 
  int				sxi, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  int				role_sim_destroyer, 
  int				flag_for_eon, 
  int				time_distance_lb    
) { 
  int	reach; 
  
  RT[reach = RT_TOP++] = red_base; 
  if (time_distance_lb < 0) 
    RT[reach] = crd_one_constraint(RT[reach], 
      ZONE[0][ZENO_CLOCK], time_distance_lb
    ); 
  
  RT[reach] = red_game_collective_precondition_sync_ITERATIVE(
    PS_EXP_TRUE, // red_events, 
    red_event_precond, // red_dest_event_precond, 
    RT[reach], // red_base, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // redpath, 
    sxi, 
    weak_fairness_list, 
    role_sim_destroyer  
  ); 
  
  if (   RT[reach] == NORM_FALSE 
      || RT[reach] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
      ) {
    RT_TOP--; // reach 
    return(RT[reach]); 
  }
  
  RT[reach] = red_game_event_role_stutter_reachable_bck(
    RT[reach], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    weak_fairness_list, 
    flag_opponent(role_sim_destroyer), 
    sxi, 
    flag_for_eon // Flag for sim evidence of SPEC or negative sim of MODL. 
  ); 

//  ce->result = RT[evidence]; 
  protect_from_gc_with_token(
    RT[reach], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
  RT_TOP--; // reach 
  
  return(RT[reach]); 
}
  /* red_game_collective_reachable_sync_ITERATIVE() */





struct red_type	*red_game_collective_reachable_sync_bulk(
  struct red_type		*red_event_precond, 
  struct red_type		*red_base, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  int				role_sim_destroyer, 
  int				flag_for_eon, 
  
  int				time_distance_lb    
) { 
  int	reach; 
  
  RT[reach = RT_TOP++] = red_base; 
  if (time_distance_lb < 0) 
    RT[reach] = crd_one_constraint(RT[reach], 
      ZONE[0][ZENO_CLOCK], time_distance_lb
    ); 
  
  RT[reach] = red_game_collective_precondition_sync_bulk(
    NORM_NO_RESTRICTION, // red_events, 
    red_event_precond, // red_dest_event_precond, 
    RT[reach], // red_base, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // redpath, 
    weak_fairness_list, 
    role_sim_destroyer  
  ); 
  RT[reach] = red_ec_eliminate_type_roles(
    RT[reach], TYPE_XTION_INSTANCE, flag_opponent(role_sim_destroyer) 
  ); 
  if (   RT[reach] == NORM_FALSE 
      || RT[reach] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
      ) {
    RT_TOP--; // reach 
    return(RT[reach]); 
  }
    
/* The following is the old code that does not deal with conflicting events 
 * between SPEC and MODL. 
 * Such a model file is termlag.d 
 
  RT[evidence] = red_role_event_precondition_sync_specific(
    NORM_NO_RESTRICTION, 
    red_bop(AND, 
      red_game_eliminate_roles(red_event_precond, flag_opponent(role_sim_destroyer)), 
      RT[GAME_ROLE_INVARIANCE[role_sim_destroyer]]
    ), 
    RT[evidence], 
    NULL, 
    GAME_ROLE_INVARIANCE[role_sim_destroyer], 
    
    sxi, 
    SYNC_XTION, 
    weak_fairness_list, 
    role_sim_destroyer | FLAG_GAME_ENVR, 
    FLAG_OPPONENT_ELIMINATE, 
    
    FLAG_ROOT_NOAPPROX, 
    flag_post_processing  
  );  
*/ 
  RT[reach] = red_game_event_role_stutter_reachable_bck(
    RT[reach], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    weak_fairness_list, 
    flag_opponent(role_sim_destroyer), 
    FLAG_GAME_SYNC_BULK, 
    flag_for_eon // Flag for sim evidence of SPEC or negative sim of MODL. 
  ); 

//  ce->result = RT[evidence]; 
  protect_from_gc_with_token(
    RT[reach], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
  RT_TOP--; // reach 
  
  return(RT[reach]); 
}
  /* red_game_collective_reachable_sync_bulk() */


/***********************************************************
 *  
   T(E&&M&&S&&~X(S), E&&M&&~S)
 */
struct red_type	*red_base_precondition_timed(int role_sim_destroyer) {
  int dest, path, conj, sxi; 
  
  RT[path = RT_TOP++] = NORM_NO_RESTRICTION; 
  for (sxi = 1; sxi < SYNC_XTION_COUNT_GAME; sxi++) { 
    if (  SYNC_XTION_GAME[sxi].status 
        & (role_sim_destroyer | FLAG_GAME_ENVR)
        ) 
      continue; 
    RT[conj = RT_TOP++] = red_bop(AND, 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      red_complement(SYNC_XTION_GAME[sxi].red_trigger) 
    ); 
    RT[conj] = red_hull_normalize(conj); 
    RT[path] = red_bop(AND, RT[path], RT[conj]); 
    RT_TOP--; // conj 
  } 
  RT[dest = RT_TOP++] = red_bop(AND, 
    RT[GAME_ROLE_INVARIANCE[FLAG_GAME_MODL]], 
    red_complement(RT[GAME_ROLE_INVARIANCE[FLAG_GAME_SPEC]])
  ); 
  RT[dest] = red_hull_normalize(dest); 
  RT[path] = red_game_time_progress_bck(
    NULL, dest, path, MASK_GAME_ROLES, TYPE_FALSE   
  ); 
  RT[path] = red_bop(AND, RT[path], red_complement(RT[dest])); 
  RT[path] = red_bop(AND, RT[path], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES] 
  ); 
  RT[path] = red_hull_normalize(path); 
  RT_TOP--; // dest, path 
  
  return(RT[path]); 
}
  /* red_base_precondition_timed() */ 
  
  


/*****************************************************************
 *  The following routines are specifically for the base cases of negated 
    branching simulation. 
    They are the base cases since the evidence agains branching simulation 
    can be obtained with either 
      . only one time progress operation (without discrete transitions) 
      . only one discrete transition (without time progress).
 */

#define FLAG_BASE_NEG_SIM		0
#define FLAG_BASE_SIM_EVIDENCE		1
#define FLAG_INDUCTIVE_NEG_SIM		2
#define FLAG_INDUCTIVE_SIM_EVIDENCE	3 

struct red_type	*red_base_neg_sim_universe(
  int				sxi, 
  int				role_sim_destroyer, 
  int				flag_fair_sim 
) { 
  struct cache7_hash_entry_type	*ce; 
  int				universe, orig_rttop = RT_TOP; 

  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nineq universe %1d, sxi = %1d, role_sim_destroyer =%1d:%s\n", 
    ++count_ineq_universe, sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  #endif 

  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE, 
    NORM_NO_RESTRICTION, 
    (struct hrd_exp_type *) NORM_NO_RESTRICTION, 
    (int) NORM_NO_RESTRICTION, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) 0, 
    sxi,  
    + flag_fair_sim * 32 
    + FLAG_BASE_NEG_SIM * 8
    + role_sim_destroyer    
  ); 
  
  if (ce->result) {
    #ifdef RED_DEBUG_BISIM_MODE
    if (sxi == 49) { 
      fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%s), old\n", 
        sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
      ); 
//      print_sync_xtion(sxi, SYNC_XTION); 
      fprintf(RED_OUT, "the cached neg sim universe is: \n"); 
      red_print_graph(ce->result); 
      fflush(RED_OUT); 
    }
    #endif 
  
    return(ce->result); 
  } 
  RT[universe = RT_TOP++] = RT[GAME_ROLE_INVARIANCE[role_sim_destroyer]]; 
  switch (role_sim_destroyer & MASK_GAME_ROLES) { 
  case FLAG_GAME_MODL: 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_modl_envr_exp
                && game_modl_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_modl_envr_exp, FLAG_GAME_MODL)
      );
    }
    break; 
  case FLAG_GAME_SPEC: 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_spec_envr_exp 
                && game_spec_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_spec_envr_exp, FLAG_GAME_SPEC)
      );
    }
    break; 
  default:  
    RT_TOP--; // result 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_neg_sim_universe: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result = NULL); 
  }
    
/*
  RT[universe] = crd_one_constraint(RT[universe], ZONE[0][PLAY_TIME], 
    CLOCK_NEG_INFINITY+1
  ); 
  RT[universe] = crd_one_constraint(RT[universe], ZONE[PLAY_TIME][0], 
    CLOCK_POS_INFINITY-1
  ); 
*/  
  RT[universe] = red_role_event_precondition_sync_specific(
    PS_EXP_TRUE, 
    RT[GAME_ROLE_INVARIANCE[role_sim_destroyer]], 
    universe, 
    NULL, 
    GAME_ROLE_INVARIANCE[role_sim_destroyer], 
    
    NORM_FALSE, 
    NORM_FALSE, 
    sxi, 
    SYNC_XTION, 
    NULL, 
    
    role_sim_destroyer | FLAG_GAME_ENVR, 
    FLAG_OPPONENT_ELIMINATE, 
    FLAG_ROOT_NOAPPROX, 
    FLAG_NO_POST_PROCESSING   
  );  

  RT[universe] = red_bop(AND, RT[universe], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
/*
  RT[result] = red_game_eliminate_roles(
    RT[result], flag_opponent(role_sim_destroyer)  
  );
*/
//  ce->result = RT[universe]; 
  protect_from_gc_with_token(
    RT[universe], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
  
  RT_TOP--; // universe 
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%x), new\n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  print_sync_xtion(sxi, SYNC_XTION); 
  fprintf(RED_OUT, "the ineq universe for sxi %1d of %1d:%s is: \n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer)
  );  
  red_print_graph(RT[universe]); 
  #endif 
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_neg_sim_universe: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[universe]); 
}
  /* red_base_neg_sim_universe() */ 


int	count_ec_g = 0; 




struct red_type	*red_neg_sim_universe_long_dest_with_uapprox(
  struct red_type	*red_dest_at_cmax, 
  int			flag_role, 
  int			flag_post_processing 
) { 
  struct cache2_hash_entry_type	*ce; 
  int				result; 

  ce = cache2_check_result_key(
    OP_INEQ_UNIVERSE_LONG_DEST_WITH_UAPPROX, 
    red_dest_at_cmax, (struct red_type *) flag_role 
  ); 
  if (ce->result) {
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, 
      "\nIn red_neg_sim_universe_long_dest_with_uapprox(%s), old\n", 
      role_name(flag_role) 
    ); 
    fprintf(RED_OUT, "the ineq universe at long dest with uapprox is: \n"); 
    red_print_graph(ce->result); 
    #endif 
  
    return(ce->result); 
  } 
  RT[result = RT_TOP++] = red_dest_at_cmax; 
  RT[result] = red_time_clock_eliminate(RT[result], PLAY_TIME); 
  RT[result] = crd_one_constraint(RT[result], 
    ZONE[0][PLAY_TIME], CLOCK_NEG_INFINITY
  ); 
  RT[result] = red_game_time_progress_bck(
    NULL, 
    result, GAME_ROLE_INVARIANCE[flag_role], 
    flag_role | FLAG_GAME_ENVR, 
    TYPE_TRUE  
  ); 
  RT[result] = red_bop(AND, RT[result], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[result] = red_bop(AND, RT[result], 
    crd_one_constraint(crd_atom(ZONE[PLAY_TIME][0], 0), 
      ZONE[0][PLAY_TIME], 0
  ) ); 
  RT[result] = red_time_clock_eliminate(RT[result], PLAY_TIME); 

  ce->result = RT[result]; 
  protect_from_gc_with_token(
    ce->result, token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
  
  RT_TOP--; // result 
  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nIn red_neg_sim_universe_long_dest_with_uapprox(%s), new\n", 
    role_name(flag_role)
  ); 
  fprintf(RED_OUT, "the ineq universe for %s is: \n", 
    role_name(flag_role)
  );  
  red_print_graph(ce->result); 
  #endif 
  
  return(ce->result); 
}
  /* red_neg_sim_universe_long_dest_with_uapprox() */ 




  
struct red_type	*red_base_neg_sim_universe_sync_bulk(
  int	role_sim_destroyer, 
  int	flag_fair_sim  
) { 
  struct cache7_hash_entry_type	*ce; 
  int				universe, orig_rttop = RT_TOP; 

  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE, 
    NORM_NO_RESTRICTION, 
    (struct hrd_exp_type *) NORM_NO_RESTRICTION, 
    (int) NORM_NO_RESTRICTION, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) 0,   
    SYNC_XTION_COUNT,  
    + flag_fair_sim * 32 
    + FLAG_BASE_NEG_SIM * 8
    + role_sim_destroyer    
  ); 
/*
  ce = cache2_check_result_key(
    OP_INEQ_UNIVERSE, RT[result], 
    SYNC_XTION_COUNT * 8 + role_sim_destroyer 
  ); 
*/
  if (ce->result) {
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result); 
  } 
  RT[universe = RT_TOP++] = RT[GAME_ROLE_INVARIANCE[role_sim_destroyer]];
  if (role_sim_destroyer & FLAG_GAME_MODL) { 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_modl_envr_exp 
                && game_modl_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_modl_envr_exp, FLAG_GAME_MODL)
      );
  } }
  else if (role_sim_destroyer & FLAG_GAME_SPEC) { 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_spec_envr_exp 
                && game_spec_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_spec_envr_exp, FLAG_GAME_SPEC)
      );
  } }
  else {
    RT_TOP--; // result 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result = NULL); 
  }
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after role invariancing"); 
*/
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    "before the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
  
/*
  RT[universe] = crd_one_constraint(RT[universe], ZONE[0][PLAY_TIME], 
    CLOCK_NEG_INFINITY+1
  ); 
  RT[universe] = crd_one_constraint(RT[universe], ZONE[PLAY_TIME][0], 
    CLOCK_POS_INFINITY-1
  ); 
*/
  RT[universe] = red_role_event_precondition_sync_bulk(
    NORM_NO_RESTRICTION, 
    RT[GAME_ROLE_INVARIANCE[role_sim_destroyer]], 
    universe, 
    NULL, 
    GAME_ROLE_INVARIANCE[role_sim_destroyer], 
  
    NORM_FALSE, 
    NORM_FALSE, 
    XI_SYNC_BULK, 
    NULL,  
    role_sim_destroyer | FLAG_GAME_ENVR, 
    
    FLAG_OPPONENT_ELIMINATE, // eliminate or keep
    FLAG_ROOT_NOAPPROX, 
    FLAG_NO_POST_PROCESSING    
  ); 
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    " after the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after weakest precondition"); 
*/
  protect_from_gc_with_token(
    RT[universe], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
    
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nRT[universe=%1d] for role %s:\n", 
    result, role_name(role_sim_destroyer)
  ); 
  red_print_graph(RT[universe]); 
  #endif 
  
  RT_TOP--; // universe  
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[universe]);
}
  /* red_base_neg_sim_universe_sync_bulk() */ 




struct red_type	*red_base_precondition_sync_bulk_to_forced_neg_branch_sim(
  int	role_sim_destroyer  
) { 
  int	evidence, path, universe; 
//  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
//  #endif 

  RT[universe = RT_TOP++] = red_base_neg_sim_universe_sync_bulk(
    role_sim_destroyer, 
    FLAG_BRANCH_SIM 
  );  
  if (RT[universe] == NORM_FALSE) {
    RT_TOP--; // universe 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_base_precondition_sync_bulk_to_forced_neg_branch_sim: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_FALSE); 
  } 

  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK at RT_TOP %1d, initial universe sync bulk\n", 
      RT_TOP
    ); 
    red_print_graph(RT[universe]); 
    #endif 
  #endif 
  RT[evidence = RT_TOP++] = red_game_collective_precondition_sync_bulk(
    NORM_NO_RESTRICTION, // red_events, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // red_dest_event_precond, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // red_base, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // redpath, 
    NULL, 
    role_sim_destroyer  
  ); 
/*
  RT[evidence = RT_TOP++] = red_game_collective_reachable_sync_bulk(
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    NULL, 
    role_sim_destroyer, 
    FLAG_FOR_SIM_EVIDENCE, 
    
    0 // time_distance_lb   
  );  
*/
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK RT_TOP %1d, after initial evidence sync bulk\n", 
      RT_TOP
    ); 
    red_print_graph(RT[evidence]); 
    #endif 
  #endif 
  
  RT[evidence] = red_complement(RT[evidence]); 
  RT[universe] = red_bop(AND, RT[universe], RT[evidence]); 
  RT_TOP--; // evidence 
  
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "*** eq basic precondition ***\n"); 
    red_print_graph(RT[RESULT_ITERATE]); 
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, before elm type roles\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, after elm type roles\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  garbage_collect(FLAG_GC_SILENT);

  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, before inactive var elm\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  /* Get the part with XI variables. 
   * This will latter be used for sync bulk postprocessing.  
   */ 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, before sync bulk post proc\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  RT[universe] = red_bop(AND, RT[universe], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[universe] = red_hull_normalize(universe); 
  RT[universe] = red_type_eliminate(RT[universe], TYPE_XTION_INSTANCE); 
//  RT[universe] = red_time_clock_eliminate(RT[universe], PLAY_TIME); 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, after inactive var elm\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  RT[universe] = inactive_variable_eliminate(universe); 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, after inactive var elm\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    ">>> EC %1d, forcible precondition by %s through sync bulk\n", 
    ITERATION_COUNT, role_name(flag_role)
  ); 
  red_print_graph(RT[explore]); 
  #endif 
  RT_TOP--; /* universe */

//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: the RT_TOP value is not consistent in red_game_forced_event_precondition_sync_bulk()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
//  #endif 
  
  return(RT[universe]); 
}
  /* red_base_precondition_sync_bulk_to_forced_neg_branch_sim() */ 





struct red_type	
*red_base_precondition_sync_ITERATIVE_to_forced_neg_branch_sim(
  int			sxi, 
  int			role_sim_destroyer 
) { 
  int	evidence, universe; 

//  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
//  #endif 

  if (   (SYNC_XTION[sxi].status & flag_opponent(role_sim_destroyer))
      || !(SYNC_XTION[sxi].status & role_sim_destroyer)
      ) {
/*
    fprintf(RED_OUT, "sxi=%1d skipped due to opponent involvement to %s\n", 
      sxi, role_name(role_sim_destroyer)
    ); 
    fflush(RED_OUT); 
*/
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_base_precondition_sync_ITERATIVE_to_forced_neg_branch_sim: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 

    return(NORM_FALSE); 
  } 

  #ifdef RED_DEBUG_GAME_MODE
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      "BASE game forced precondition of sxi=%1d from the %s side at RT_TOP=%1d\n", 
      sxi, role_name(role_sim_destroyer), RT_TOP 
    ); 
    fprintf(RED_OUT, "===========================================\n"); 
    print_sync_xtion_lines(sxi, SYNC_XTION); 
    fflush(RED_OUT); 
  }
  #endif 
  
  RT[universe = RT_TOP++] = red_base_neg_sim_universe(
    sxi, 
    role_sim_destroyer, 
    FLAG_BRANCH_SIM // flag_fair_sim, 
  ); 

  if (RT[universe] == NORM_FALSE) {
    RT_TOP--; // universe 
    return(NORM_FALSE); 
  } 

  #ifdef RED_DEBUG_GAME_MODE
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      "BASE after game forced precondition of sxi=%1d from the %s side at RT_TOP=%1d\n", 
      sxi, role_name(role_sim_destroyer), RT_TOP 
    ); 
    fprintf(RED_OUT, "===========================================\n"); 
//    print_sync_xtion_lines(sxi, SYNC_XTION); 
    red_print_graph(RT[universe]); 
    fflush(RED_OUT); 
  }
  #endif 
  
  RT[evidence = RT_TOP++] = red_game_collective_precondition_sync_ITERATIVE(
    PS_EXP_TRUE, // red_events, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // red_dest_event_precond, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // red_base, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], // redpath, 
    sxi, 
    NULL, 
    role_sim_destroyer  
  ); 
/*
  RT[evidence = RT_TOP++] = red_game_collective_reachable_sync_ITERATIVE(
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    sxi, 
    NULL,  
    role_sim_destroyer, 
    FLAG_FOR_SIM_EVIDENCE, // flag_for_eon, 
    0    
  ); 
*/   
  #ifdef RED_DEBUG_GAME_MODE
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      "BASE evidence of sxi=%1d from the %s side at RT_TOP=%1d\n", 
      sxi, role_name(flag_opponent(role_sim_destroyer)), RT_TOP 
    ); 
    fprintf(RED_OUT, "===========================================\n"); 
//    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(RT[evidence]); 
    fflush(RED_OUT); 
  }
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      "BASE universe before elimination of sxi=%1d from the %s side at RT_TOP=%1d\n", 
      sxi, role_name(flag_opponent(role_sim_destroyer)), RT_TOP 
    ); 
    fprintf(RED_OUT, "===========================================\n"); 
//    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(RT[universe]); 
    fflush(RED_OUT); 
  }
  #endif 

  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, 
      "\nKKK EC %1d at RT_TOP %1d, sxi=%1d, before sync iter post proc\n", 
      ITERATION_COUNT, RT_TOP, sxi
    ); 
    red_print_graph(RT[acc]); 
    fprintf(RED_OUT, 
      "\ncheck nsim %1d: before the targeted game post processing.\n", 
      ++count_check_nsim
    ); 
    fflush(RED_OUT); 
    #endif 
  #endif 

  RT[evidence] = red_complement(RT[evidence]); 
  RT[universe] = red_bop(AND, RT[universe], RT[evidence]); 
  RT_TOP--; // evidence 
  RT[universe] = red_bop(AND, RT[universe], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  #ifdef RED_DEBUG_GAME_MODE
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      ">>> EC %1d, RT[universe=%1d] after %s ineq elimination for sxi=%1d\n", 
      ITERATION_COUNT, universe, role_name(role_sim_destroyer), sxi
    ); 
//    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(RT[universe]); 
  }
  #endif 
//  RT[universe] = red_time_clock_eliminate(RT[universe], PLAY_TIME); 
  RT[universe] = red_hull_normalize(universe); 
/*
  fprintf(RED_OUT, "\n~~~ neg_sim remains of %s through sxi %1d:\n", 
    role_name(role_sim_destroyer), sxi
  ); 
  red_print_graph(RT[neg_sim_universe]); 
*/
  
  RT[universe] = inactive_variable_eliminate(universe); 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, "\nKKK EC %1d at RT_TOP %1d, after inactive var elm\n", 
      ITERATION_COUNT, RT_TOP
    ); 
    #endif 
  #endif 
  
  garbage_collect(FLAG_GC_SILENT);
  #ifdef RED_DEBUG_GAME_MODE
  if (sxi == 7) { 
    fprintf(RED_OUT, 
      ">>> EC %1d, RT[universe=%1d] after %s ineq normalization for sxi=%1d\n", 
      ITERATION_COUNT, universe, role_name(role_sim_destroyer), sxi
    ); 
//    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(RT[universe]); 
  }
  #endif 
  RT_TOP--; // universe 
  
//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, "Error: the RT_TOP value is not consistent in red_game_forced_event_precondition_sync_ITERATIVE()!\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
//  #endif 
  
  return(RT[universe]); 
} 
  /* red_base_precondition_sync_ITERATIVE_to_forced_neg_branch_sim() */ 








struct red_type	*red_neg_branch_sim_base(int role_sim_destroyer) {
  int			neg_sim, sxi, neg_fsim_base; 
  struct red_type	*child; 
  int			orig_rttop = RT_TOP; 
  
  sxi = -1; 
//  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    "\n>>>>>>red_neg_branch_sim_base() of %s to the space:\n", 
    role_name(role_sim_destroyer)
  ); 
  red_print_graph(RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
  fflush(RED_OUT); 
//  #endif 

  RT[neg_sim = RT_TOP++] = red_base_precondition_timed(role_sim_destroyer); 
//  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, "\nBase neg sim of %s through timed: \n", 
    role_name(role_sim_destroyer) 
  ); 
  red_print_graph(RT[neg_sim]); 
  fflush(RED_OUT); 
//  #endif 

  RT[neg_sim] = red_bop(OR, RT[neg_sim], 
    red_base_precondition_sync_bulk_to_forced_neg_branch_sim(
      role_sim_destroyer
  ) ); 
//  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, "\nBase neg sim of %s through sxi bulk: \n", 
    role_name(role_sim_destroyer) 
  ); 
  red_print_graph(RT[neg_sim]); 
  fflush(RED_OUT); 
//  #endif 
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
//    #ifdef RED_DEBUG_GAME_MODE
      fprintf(RED_OUT, 
        "\n===[Detecting base neg sim by %s through sxi=%1d/%1d]==================\n", 
        role_name(role_sim_destroyer), sxi, SYNC_XTION_COUNT 
      ); 
      print_sync_xtion_lines(sxi, SYNC_XTION); 
//      red_print_graph(red_sim); 
//    #endif 

    child = red_base_precondition_sync_ITERATIVE_to_forced_neg_branch_sim(
      sxi, role_sim_destroyer 
    ); 
//    #ifdef RED_DEBUG_GAME_MODE 
    fprintf(RED_OUT, "\nBase neg sim of %s through sxi %1d/%1d: \n", 
      role_name(role_sim_destroyer), sxi, SYNC_XTION_COUNT  
    ); 
    print_sync_xtion_lines(sxi, SYNC_XTION); 
    red_print_graph(child); 
    fflush(RED_OUT); 
//    #endif 

    RT[neg_sim] = red_bop(OR, RT[neg_sim], child); 
  }
  sxi = -2; 
  RT[neg_sim] = red_subsume(RT[neg_sim]); 

  
  RT_TOP--; // neg_sim 
///*
  fprintf(RED_OUT, "\nThe negative base for branching simulation by %s:\n", 
    role_name(role_sim_destroyer)
  ); 
  red_print_graph(RT[neg_sim]); 
  fflush(RED_OUT); 
//*/   
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: FSIM %1d:%1d:%1d*%1d, the RT_TOP values (New %1d, Old %1d)\n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, 
      RT_TOP, orig_rttop 
    ); 
    fprintf(RED_OUT, 
      "       are not consistent in red_event_precondition_to_forced_neg_fxp()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 

  return(RT[neg_sim]); 
}
  /* red_neg_branch_sim_base() */ 





/*****************************************************************
 *  The following procedures are for the inductive construction 
 *  of negative simulations.  
 */


struct red_type	*red_inductive_neg_sim_universe(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_event_precond, 
  int				sxi, 
  struct red_type		*red_neg_sim_base, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  
  int				role_sim_destroyer, 
  int				flag_fair_sim, 
  int				time_distance_lb 
) { 
  struct cache7_hash_entry_type	*ce; 
  int				universe, orig_rttop = RT_TOP; 

  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nineq universe %1d, sxi = %1d, role_sim_destroyer =%1d:%s\n", 
    ++count_ineq_universe, sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  #endif 

  if (   (SYNC_XTION[sxi].status & flag_opponent(role_sim_destroyer)) 
      || check_sxi_event_exp(sxi, SYNC_XTION, event_exp) == TYPE_FALSE 
      ) { 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_FALSE); 
  } 

  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE_SYNC_ITERATIVE, 
    red_event_precond, 
    (struct hrd_exp_type *) red_neg_sim_base, 
    (int) event_exp, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) time_distance_lb, 
    sxi,  
    flag_fair_sim * 32 
    + FLAG_INDUCTIVE_NEG_SIM * 8
    + role_sim_destroyer 
  ); 

  if (ce->result) {
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%s), old\n", 
      sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
    ); 
    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(red_neg_sim_base); 
    fprintf(RED_OUT, "the ineq universe is: \n"); 
    red_print_graph(ce->result); 
    #endif 
  
    return(ce->result); 
  } 

  RT[universe = RT_TOP++] = red_neg_sim_base; 
  switch (role_sim_destroyer & MASK_GAME_ROLES) { 
  case FLAG_GAME_MODL: 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_modl_envr_exp
                && game_modl_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_modl_envr_exp, FLAG_GAME_MODL)
      );
    }
    break; 
  case FLAG_GAME_SPEC: 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_spec_envr_exp 
                && game_spec_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_spec_envr_exp, FLAG_GAME_SPEC)
      );
    }
    break; 
  default:  
    RT_TOP--; // universe  
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_neg_sim_universe: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result = NULL); 
  }

  if (RT[universe] == NORM_FALSE) {
    RT_TOP--; // universe 
    return(ce->result = RT[universe]); 
  }
  
  if (!(SYNC_XTION[sxi].status & (FLAG_GAME_SPEC | FLAG_GAME_MODL))) { 
    RT[universe] = red_role_event_precondition_sync_specific(
      PS_EXP_TRUE, 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
      universe, 
      NULL, 
      INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
    
      NORM_FALSE, 
      NORM_FALSE, 
      sxi, 
      SYNC_XTION, 
      weak_fairness_list, 

      FLAG_GAME_ENVR, 
      FLAG_OPPONENT_KEEP,     
      FLAG_ROOT_NOAPPROX, 
      FLAG_POST_PROCESSING   
    );  

    RT_TOP--; //universe
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(RT[universe]); 	
  } 
  
  RT[universe] = red_game_collective_reachable_sync_ITERATIVE(
    red_event_precond, 
    RT[universe], // red_base, 
    sxi, 
    weak_fairness_list,  
    role_sim_destroyer, 
    
    FLAG_FOR_NEG_SIM, 
    time_distance_lb    
  ); 
  
  RT_TOP--; // universe 
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%x), new\n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  print_sync_xtion(sxi, SYNC_XTION); 
  red_print_graph(red_dest); 
  fprintf(RED_OUT, "the ineq universe for sxi %1d of %1d:%s is: \n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer)
  );  
  red_print_graph(RT[universe]); 
  #endif 
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_neg_sim_universe: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[universe]); 
}
  /* red_inductive_neg_sim_universe() */ 

  



int count_sim_evidence = 0; 

struct red_type	*red_inductive_sim_evidence(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_event_precond, 
  int				sxi, 
  struct red_type		*red_neg_sim_base, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  
  int				role_sim_destroyer, 
  int				flag_fair_sim, 
  int				time_distance_lb 
) { 
  struct cache7_hash_entry_type	*ce; 
  int				evidence, orig_rttop = RT_TOP; 

  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nineq evidence %1d, sxi = %1d, role_sim_destroyer =%1d:%s\n", 
    ++count_sim_evidence, sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  #endif 

  if (   (SYNC_XTION[sxi].status & flag_opponent(role_sim_destroyer)) 
      || check_sxi_event_exp(sxi, SYNC_XTION, event_exp) == TYPE_FALSE 
      ) { 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_NO_RESTRICTION); 
  } 
  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE_SYNC_ITERATIVE, 
    red_event_precond, 
    (struct hrd_exp_type *) red_neg_sim_base, 
    (int) event_exp, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) time_distance_lb, 
      sxi,  
    flag_fair_sim * 32 
    + FLAG_INDUCTIVE_SIM_EVIDENCE * 8
    + role_sim_destroyer    
  ); 

  if (ce->result) {
    #ifdef RED_DEBUG_BISIM_MODE
    fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%s), old\n", 
      sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
    ); 
    print_sync_xtion(sxi, SYNC_XTION); 
    red_print_graph(red_neg_sim_base); 
    fprintf(RED_OUT, "the ineq universe is: \n"); 
    red_print_graph(ce->result); 
    #endif 
  
    return(ce->result); 
  } 

  RT[evidence = RT_TOP++] = red_complement(red_neg_sim_base); 
  RT[evidence] = red_bop(AND, RT[evidence], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[evidence] = red_hull_normalize(evidence); 
  
  if (   RT[evidence] == NORM_FALSE 
      || RT[evidence] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
      ) {
    RT_TOP--; // evidence 
    return(ce->result = RT[evidence]); 
  }
  RT[evidence] = red_game_collective_reachable_sync_ITERATIVE(
    red_event_precond, 
    RT[evidence], // red_base, 
    sxi, 
    weak_fairness_list,  
    role_sim_destroyer, 
    
    FLAG_FOR_SIM_EVIDENCE, 
    time_distance_lb    
  ); 
    
  RT_TOP--; // evidence 
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nIn red_neg_sim_universe(sxi=%1d, ..., %1d:%x), new\n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer) 
  ); 
  print_sync_xtion(sxi, SYNC_XTION); 
  red_print_graph(red_dest); 
  fprintf(RED_OUT, "the ineq evidence for sxi %1d of %1d:%s is: \n", 
    sxi, role_sim_destroyer, role_name(role_sim_destroyer)
  );  
  red_print_graph(RT[evidence]); 
  #endif 
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_neg_sim_universe: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[evidence]); 
}
  /* red_inductive_sim_evidence() */ 

  



  
struct red_type	*red_inductive_neg_sim_universe_sync_bulk(
  struct red_type		*red_game_sync_bulk_from_event_exp, 
  struct red_type		*red_event_precond, 
  struct red_type		*red_neg_sim_base, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  int				role_sim_destroyer, 
  
  int				flag_fair_sim, 
  int				time_distance_lb  
) { 
  struct cache7_hash_entry_type	*ce; 
  int				universe, orig_rttop = RT_TOP; 

/*
  RT[result = RT_TOP++] 
  = red_game_eliminate_roles(RT[XI_SYNC_BULK], flag_opponent(role_sim_destroyer)); 
  RT[result] = red_ec_eliminate_type_roles(
    RT[result], TYPE_XTION_INSTANCE, 
    flag_opponent(role_sim_destroyer) 
  ); 
*/
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after role elimination"); 
*/
/*
  fprintf(RED_OUT, "\nIn red_inductive_neg_sim_universe_sync_bulk()\n"); 
  fprintf(RED_OUT, "XI_GAME_SYNC_BULK_WITH_EVENTS=%1d\n", 
    XI_GAME_SYNC_BULK_WITH_EVENTS
  ); 
  fprintf(RED_OUT, "red_game_sync_bulk_from_event_exp:\n"); 
  red_print_graph(red_game_sync_bulk_from_event_exp); 
  fflush(RED_OUT); 
*/

  if (red_bop(AND, RT[XI_GAME_SYNC_BULK], 
                red_game_sync_bulk_from_event_exp
              ) == NORM_FALSE 
      ) { 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_FALSE); 
  } 
  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE, 
    red_game_sync_bulk_from_event_exp, 
    (struct hrd_exp_type *) red_neg_sim_base, 
    (int) red_event_precond, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) time_distance_lb,   
    SYNC_XTION_COUNT,  
    flag_fair_sim * 32
    + FLAG_INDUCTIVE_NEG_SIM * 8  
    + role_sim_destroyer 
  ); 
/*
  ce = cache2_check_result_key(
    OP_INEQ_UNIVERSE, RT[result], 
    SYNC_XTION_COUNT * 8 + role_sim_destroyer 
  ); 
*/
  if (ce->result) {
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_inductive_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result); 
  } 
  RT[universe = RT_TOP++] = red_neg_sim_base;
  if (role_sim_destroyer & FLAG_GAME_MODL) { 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_modl_envr_exp 
                && game_modl_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_modl_envr_exp, FLAG_GAME_MODL)
      );
  } }
  else if (role_sim_destroyer & FLAG_GAME_SPEC) { 
    if (   flag_fair_sim == FLAG_BRANCH_SIM
        && (   (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) 
               != FLAG_ZENO_CYCLE_OK
            || (   game_spec_envr_exp 
                && game_spec_envr_exp->u.mexp.strong_fairness_count
        )   )   ) { 
      RT[universe] = red_bop(AND, RT[universe], 
        game_role_fairness_bck(game_spec_envr_exp, FLAG_GAME_SPEC)
      );
  } }
  else {
    RT_TOP--; // universe   
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_inductive_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result = NULL); 
  }
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after role invariancing"); 
*/
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    "before the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
  
/* The following procedure is decided not to be replaced by 
 * the standard game event preconditon routine: 
 *   red_role_event_precondition_sync_bulk()
 * The reason is that we need insert Zeno-clock constraints to 
 * the immediate precondition before time progressing. 
 * That means another parameter to the standard routine. 
 * We feel that is too much. 
 */
  RT[universe] = red_game_collective_precondition_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_event_precond, 
    RT[universe], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES],     
    weak_fairness_list, 
    
    role_sim_destroyer  
  ); 
  RT[universe] = red_ec_eliminate_type_roles(
    RT[universe], TYPE_XTION_INSTANCE, 
    flag_opponent(role_sim_destroyer) 
  ); 

  if (   RT[universe] == NORM_FALSE 
      || RT[universe] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
      ) {
    RT_TOP--; // universe 
    return(ce->result = RT[universe]); 
  }
  
  RT[universe] = red_game_collective_reachable_sync_bulk(
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    RT[universe], 
    weak_fairness_list, 
    role_sim_destroyer, 
    FLAG_FOR_NEG_SIM, 
    
    time_distance_lb   
  );  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    " after the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after weakest precondition"); 
*/
  protect_from_gc_with_token(
    RT[universe], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
    
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nRT[result=%1d] for role %s:\n", 
    result, role_name(role_sim_destroyer)
  ); 
  red_print_graph(RT[universe]); 
  #endif 
  
  RT_TOP--; // universe 
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_inductive_neg_sim_universe_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[universe]);
}
  /* red_inductive_neg_sim_universe_sync_bulk() */ 




struct red_type	*red_inductive_sim_evidence_sync_bulk(
  struct red_type		*red_game_sync_bulk_from_event_exp, 
  struct red_type		*red_event_precond, 
  struct red_type		*red_neg_sim_base, 
  struct ps_fairness_link_type	*weak_fairness_list,  
  int				role_sim_destroyer, 
  
  int				flag_fair_sim, 
  int				time_distance_lb  
) { 
  struct cache7_hash_entry_type	*ce; 
  int				evidence, orig_rttop = RT_TOP; 

/*
  RT[result = RT_TOP++] 
  = red_game_eliminate_roles(RT[XI_SYNC_BULK], flag_opponent(role_sim_destroyer)); 
  RT[result] = red_ec_eliminate_type_roles(
    RT[result], TYPE_XTION_INSTANCE, 
    flag_opponent(role_sim_destroyer) 
  ); 
*/
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after role elimination"); 
*/

  if (red_bop(AND, RT[XI_GAME_SYNC_BULK], 
              red_game_sync_bulk_from_event_exp
              ) == NORM_FALSE 
      ) { 
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_NO_RESTRICTION); 
  } 
  ce = cache7_check_result_key(
    OP_INEQ_UNIVERSE, 
    red_game_sync_bulk_from_event_exp, 
    (struct hrd_exp_type *) red_neg_sim_base, 
    (int) red_event_precond, 
    (int) GAME_FAIRNESS_EXP, 
    (struct hrd_exp_type *) time_distance_lb,   
    SYNC_XTION_COUNT,  
    flag_fair_sim * 32 
    + FLAG_INDUCTIVE_SIM_EVIDENCE*8 
    + role_sim_destroyer 
  ); 
/*
  ce = cache2_check_result_key(
    OP_INEQ_UNIVERSE, RT[result], 
    SYNC_XTION_COUNT * 8 + role_sim_destroyer 
  ); 
*/
  if (ce->result) {
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_inductive_sim_evidence_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(ce->result); 
  } 
  RT[evidence = RT_TOP++] = red_complement(red_neg_sim_base); 
  RT[evidence] = red_bop(AND, RT[evidence], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[evidence] = red_hull_normalize(evidence); 

  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    "before the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
  
/* The following procedure is decided not to be replaced by 
 * the standard game event preconditon routine: 
 *   red_role_event_precondition_sync_bulk()
 * The reason is that we need insert Zeno-clock constraints to 
 * the immediate precondition before time progressing. 
 * That means another parameter to the standard routine. 
 * We feel that is too much. 
 */
  RT[evidence] = red_game_collective_precondition_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_event_precond, 
    RT[evidence], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES],     
    weak_fairness_list, 
    
    role_sim_destroyer  
  ); 
  RT[evidence] = red_ec_eliminate_type_roles(
    RT[evidence], TYPE_XTION_INSTANCE, 
    flag_opponent(role_sim_destroyer) 
  ); 

  if (   RT[evidence] == NORM_FALSE 
      || RT[evidence] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
      ) {
    RT_TOP--; // evidence 
    return(ce->result = RT[evidence]); 
  }
  
  RT[evidence] = red_game_collective_reachable_sync_bulk(
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    RT[evidence], 
    weak_fairness_list, 
    role_sim_destroyer, 
    FLAG_FOR_SIM_EVIDENCE, 
    
    time_distance_lb   
  );  
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, 
    " after the universe sync bulk for MODL, RT_TOP=%1d\n", 
    RT_TOP
  ); 
  #endif 
/*
  red_test_bisim(RT[INEQ_XTION_SYNC_BULK[FLAG_GAME_MODL]], "after weakest precondition"); 
*/
  protect_from_gc_with_token(
    RT[evidence], token_fair_sim, TOKEN_PROTECTION_LIST
  ); 
    
  #ifdef RED_DEBUG_BISIM_MODE
  fprintf(RED_OUT, "\nRT[result=%1d] for role %s:\n", 
    result, role_name(role_sim_destroyer)
  ); 
  red_print_graph(RT[evidence]); 
  #endif 
  
  RT_TOP--; // evidence 
  
  if (RT_TOP != orig_rttop) { 
    fprintf(RED_OUT, 
      "\nred_inductive_sim_evidence_sync_bulk: Caught a stack mismatch %1d-->%1d\n", 
      orig_rttop, RT_TOP
    ); 
    bk(0); 
  } 
  return(ce->result = RT[evidence]);
}
  /* red_inductive_sim_evidence_sync_bulk() */ 




#ifdef RED_DEBUG_GAME_MODE
int	count_time_in_stutter = 0; 
#endif 



void	test_intersection(s, dx, dy) 
  char			*s; 
  struct red_type	*dx, *dy; 
{
  fprintf(RED_OUT, "\n>> Testing emptiness of %s:\n", s); 
  red_print_graph(red_bop(AND, dx, dy)); 
}
  /* test_intersect() */ 









/*****************************************************
 *  The following procedures are for the inductive cases of negated simulation, 
 *  either branching or fair. 
 */

  
  



  
  
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


  












/* Note that the following procedure is used to prune the preconditon of 
 * fsim to weak fairness from the neg_fsim. 
 */ 







struct red_type	*red_game_forced_event_precondition_sync_bulk(
  struct red_type		*red_game_sync_bulk_from_event_exp, 
  struct red_type		*red_event_precond, 
  struct red_type		*red_neg_sim_base, 
  struct red_type		*red_neg_sim, 
  struct red_type		*red_path, 
  
  struct red_type		*red_neg_sim_wfair, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				role_sim_destroyer, 
  int				flag_fair_sim, 
  int				flag_step_time  
) { 
  int	sim_evidence, neg_sim_universe; 
//  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
//  #endif 

  RT[neg_sim_universe = RT_TOP++] = red_inductive_neg_sim_universe_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_event_precond, 
    red_bop(AND, red_neg_sim_base, red_neg_sim_wfair), 
    weak_fairness_list,  
    role_sim_destroyer, 

    flag_fair_sim, 
    0 // time_distance_lb 
  );  
  if (RT[neg_sim_universe] == NORM_FALSE) { 
    RT_TOP--; // neg_sim_universe
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_FALSE); 	
  } 
  RT[sim_evidence = RT_TOP++] = red_inductive_sim_evidence_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_event_precond, 
    red_bop(AND, red_neg_sim_base, red_neg_sim_wfair), 
    weak_fairness_list,  
    role_sim_destroyer, 
    
    flag_fair_sim, 
    0 // time_distance_lb 
  );  
  RT[sim_evidence] = red_complement(RT[sim_evidence]); 
  RT[neg_sim_universe] = red_bop(AND, RT[neg_sim_universe], 
    RT[sim_evidence]
  ); 
  RT_TOP--; // sim_evidence 
  RT[neg_sim_universe] = red_bop(AND, 
    RT[neg_sim_universe], RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[neg_sim_universe] = red_hull_normalize(neg_sim_universe); 
  RT[neg_sim_universe] = red_type_eliminate(RT[neg_sim_universe], 
    TYPE_XTION_INSTANCE
  ); 
  RT[neg_sim_universe] = red_time_clock_eliminate(RT[neg_sim_universe], PLAY_TIME); 
  RT[neg_sim_universe] = red_hull_normalize(neg_sim_universe); 
  RT[neg_sim_universe] = red_subsume(RT[neg_sim_universe]); 
    
//  #ifdef RED_DEBUG_GAME_MODE
/*
  if (   (FSIM_ITER == 1 || FSIM_ITER == 2) 
      && FSIM_STRONG_ITER == 1
      && GUNTIL_ITER == -1
      && sxi == 13
      ) { 
*/
    fprintf(RED_OUT, "%s, after counter matching sync bulk of %s\n", 
      fseq("sync ITER"), role_name(role_sim_destroyer)
    ); 
    red_print_graph(RT[neg_sim_universe]); 
/*
  }
*/
//  #endif 

  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, 
      "\nKKK EC %1d at RT_TOP %1d, sxi=%1d, before sync iter post proc\n", 
      ITERATION_COUNT, RT_TOP, sxi
    ); 
    red_print_graph(RT[neg_sim_universe]); 
    fprintf(RED_OUT, 
      "\ncheck nsim %1d: before the targeted game post processing.\n", 
      ++count_check_nsim
    ); 
    fflush(RED_OUT); 
    #endif 
  #endif 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    if (FSIM_ITER == 2 && sxi == 11) { 
      fprintf(RED_OUT, "%s, %s, sxi %1d, RT[sim] after postconditioning\n", 
        fseq("sync_ITER", role_name(role_sim_destroyer), sxi
      ); 
      red_print_graph(RT[neg_sim_universe]); 
      fflush(RED_OUT); 
    } 
    #endif 
  #endif 

  garbage_collect(FLAG_GC_SILENT);
//  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    ">>> %s, RT[acc=%1d] after %s neg sim elimination for sync bulk\n", 
    fseq("sync_ITER"), neg_sim_universe, role_name(role_sim_destroyer) 
  ); 
  red_print_graph(RT[neg_sim_universe]); 
//  #endif 
  RT_TOP--; // neg_sim_universe 
  
//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, "Error: the RT_TOP value is not consistent in red_game_forced_event_precondition_sync_ITERATIVE()!\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
//  #endif 
  
  return(RT[neg_sim_universe]); 
}
  /* red_game_forced_event_precondition_sync_bulk() */ 







int	count_check_nsim = 0; 

struct red_type	*red_game_forced_event_precondition_sync_ITERATIVE(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_event_precond, 
  struct red_type		*red_neg_sim_base, 
  struct red_type		*red_neg_sim, 
  struct red_type		*red_path, 
  
  int				sxi, 
  struct red_type		*red_neg_sim_wfair, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				role_sim_destroyer, 
  int				flag_fair_sim, 
  
  int 				flag_step_time  
) { 
  int	sim_evidence, neg_sim_universe, 
  	flag_old_time_progress; 

//  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
//  #endif 


  #ifdef RED_DEBUG_GAME_MODE
  if (   (FSIM_ITER == 1 || FSIM_ITER == 2) 
      && FSIM_STRONG_ITER == 1
      && GUNTIL_ITER == -1
      && sxi == 13
      ) { 
    fprintf(RED_OUT, 
      "Inductive %1d, game forced precondition of sxi=%1d from the %s side at RT_TOP=%1d\n", 
      ITERATION_COUNT, sxi, role_name(role_sim_destroyer), RT_TOP 
    ); 
    fprintf(RED_OUT, "===========================================\n"); 
    print_sync_xtion(sxi, SYNC_XTION); 
    fprintf(RED_OUT, "%s, The forced target by %s:\n", 
      fseq("sync ITER"), role_name(role_sim_destroyer)
    ); 
    red_print_graph(red_neg_sim_base); 
  }
  #endif 
    
  RT[neg_sim_universe = RT_TOP++] = red_inductive_neg_sim_universe(
    event_exp, 
    red_event_precond, 
    sxi, 
    red_bop(AND, red_neg_sim_base, red_neg_sim_wfair), 
    weak_fairness_list,  
    
    role_sim_destroyer, 
    flag_fair_sim, 
    0 // time_distance_lb 
  );  
  if (RT[neg_sim_universe] == NORM_FALSE) { 
    RT_TOP--; // neg_sim_universe
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(NORM_FALSE); 	
  } 
  else if (!(SYNC_XTION[sxi].status & (FLAG_GAME_SPEC | FLAG_GAME_MODL))) { 
    RT_TOP--; // neg_sim_universe
    if (RT_TOP != orig_rttop) { 
      fprintf(RED_OUT, 
        "\nred_game_forced_event_precondition_sync_ITERATIVE: Caught a stack mismatch %1d-->%1d\n", 
        orig_rttop, RT_TOP
      ); 
      bk(0); 
    } 
    return(RT[neg_sim_universe]); 	
  } 
  
  RT[sim_evidence = RT_TOP++] = red_inductive_sim_evidence(
    event_exp, 
    red_event_precond, 
    sxi, 
    red_bop(AND, red_neg_sim_base, red_neg_sim_wfair), 
    weak_fairness_list,  
    
    role_sim_destroyer, 
    flag_fair_sim, 
    0 // time_distance_lb 
  );  
  RT[sim_evidence] = red_complement(RT[sim_evidence]); 
  RT[neg_sim_universe] = red_bop(AND, RT[neg_sim_universe], 
    RT[sim_evidence]
  ); 
  RT_TOP--; // sim_evidence 
  RT[neg_sim_universe] = red_bop(AND, 
    RT[neg_sim_universe], RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[neg_sim_universe] = red_time_clock_eliminate(RT[neg_sim_universe], PLAY_TIME); 
  RT[neg_sim_universe] = red_hull_normalize(neg_sim_universe); 
    
  #ifdef RED_DEBUG_GAME_MODE
/*
  if (   (FSIM_ITER == 1 || FSIM_ITER == 2) 
      && FSIM_STRONG_ITER == 1
      && GUNTIL_ITER == -1
      && sxi == 13
      ) { 
*/
    fprintf(RED_OUT, "%s, after counter matching sync iter %d of %s\n", 
      fseq("sync ITER"), sxi, role_name(role_sim_destroyer)
    ); 
    red_print_graph(RT[neg_sim_universe]); 
/*
  }
*/
  #endif 

  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    fprintf(RED_OUT, 
      "\nKKK EC %1d at RT_TOP %1d, sxi=%1d, before sync iter post proc\n", 
      ITERATION_COUNT, RT_TOP, sxi
    ); 
    red_print_graph(RT[neg_sim_universe]); 
    fprintf(RED_OUT, 
      "\ncheck nsim %1d: before the targeted game post processing.\n", 
      ++count_check_nsim
    ); 
    fflush(RED_OUT); 
    #endif 
  #endif 
  #ifdef RED_DEBUG_GAME_MODE
    #ifdef RED_DEBUG_GAME_MODE_FORCED_PRECOND
    if (FSIM_ITER == 2 && sxi == 11) { 
      fprintf(RED_OUT, "%s, %s, sxi %1d, RT[sim] after postconditioning\n", 
        fseq("sync_ITER", role_name(role_sim_destroyer), sxi
      ); 
      red_print_graph(RT[neg_sim_universe]); 
      fflush(RED_OUT); 
    } 
    #endif 
  #endif 

  garbage_collect(FLAG_GC_SILENT);
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    ">>> %s, RT[acc=%1d] after %s neg sim elimination for sxi=%1d\n", 
    fseq("sync_ITER"), neg_sim_universe, role_name(role_sim_destroyer), sxi
  ); 
  print_sync_xtion(sxi, SYNC_XTION); 
  red_print_graph(RT[neg_sim_universe]); 
  #endif 
  RT_TOP--; // neg_sim_universe 
  
//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, "Error: the RT_TOP value is not consistent in red_game_forced_event_precondition_sync_ITERATIVE()!\n"); 
    fflush(RED_OUT); 
    bk(0); 
  } 
//  #endif 
  
  return(RT[neg_sim_universe]); 
} 
  /* red_game_forced_event_precondition_sync_ITERATIVE() */ 








/*******************************************************************
 *  
 *  Now we have separated the precondition procedure for branching 
 *  simulation from that for fair simulation. 
 *  The following is for branching simulation. 
 *  It is actually for forced mismatches.  
 *  It works by using side-effect on RT[fxp] and RT[neg_fxp].  
 *  In each iteration, RT[fxp] shrinks while RT[neg_fxp] grows.  
 */ 
//  Given a forced destination postcond S, 
//  the formulation for the return value of the procedure is 
//  as follows. 
//         \bigcup_{sxi, only model} pre(sxi, S)
//         && ~(rbck_{only spec}(\bigcup_{sxj, matches sxi}pre(sxj, S)))
//  Now what is the answer if S is INV ? 
//    
//  What is the answer if S is ~INV ? 
//  What is the answer if S is false ? 
// 
//  If argument flag_neg_dest is FLAG_NO_NEGATION, 
//  red_dest_event_dest is to be directly 
//  used for the controled reachability analysis of the opponent. 
//  This means that we want to calculate those state pairs 
//  with a model strategy to opp_mismatches those state pairs 
//  in red_dest_event_dest by the opponent.  
//
//  If argument flag_neg_dest is FLAG_NEGATION, 
//  we want to calculate those 
//  state pairs with a model strategy to force to red_dest_event_dest 
//  or can make sure that nothing happens by the opponent. 
// 

struct red_type	*red_event_precondition_to_forced_neg_sim(
  struct ps_exp_type		*event_exp, 
  struct red_type		*red_game_sync_bulk_from_event_exp, 
  struct red_type		*red_event_precond, 
  struct red_type		*red_neg_sim, 
  struct red_type		*red_path, 
  struct red_type		*red_neg_sim_wfair, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_role, 
  int				flag_fair_sim,  
  int				time_distance_lb
) { 
  int			result, sxi, neg_fsim_base; 
  struct red_type	*child; 
  #ifdef RED_DEBUG_GAME_MODE
  int			orig_rttop = RT_TOP; 
  #endif 
  
  sxi = -1; 
//  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    "\nFSIM %1d:%1d:%1d*%1d:sxi bulk, Before forced through sxi all]==================\n", 
    FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER 
  ); 
  fprintf(RED_OUT, "FSIM %1d:%1d:%1d*%1d:sxi all, To destination: \n", 
    FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER 
  ); 
  red_print_graph(red_neg_sim); 
  fprintf(RED_OUT, "FSIM %1d:%1d:%1d*%1d:sxi all, Through events: \n", 
    FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER 
  ); 
  red_print_graph(red_game_sync_bulk_from_event_exp); 
//  #endif 
/*
  switch (flag_avoid_as_dest) { 
  case FLAG_AVOID_AS_NEGATED_DEST: 
    RT[local_nfxp = RT_TOP++] = red_bop(AND, 
      red_complement(red_event_postcond), 
      RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
    ); 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nred_event_precondition_to_forced_neg_fxp() with negated dest:\n"
    ); 
    red_print_graph(RT[local_nfxp]); 
    fflush(RED_OUT); 
    #endif 
    break; 
  case FLAG_AVOID_AS_DEST: 
*/
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nred_event_precondition_to_forced_neg_fxp() with original dest:\n"
    ); 
    red_print_graph(red_neg_sim); 
    fflush(RED_OUT); 
    #endif 
/*
    break; 
  default: 
    fprintf(RED_OUT, "Error: Illegal flag_neg_dest option value %1d.\n", 
      flag_avoid_as_dest
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
*/
  RT[neg_fsim_base = RT_TOP++] = red_bop(AND, red_neg_sim, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  if (time_distance_lb < 0) 
    RT[neg_fsim_base] = crd_one_constraint(
      RT[neg_fsim_base], ZONE[0][ZENO_CLOCK], time_distance_lb
    ); 

  RT[result = RT_TOP++] = red_game_forced_event_precondition_sync_bulk(
    red_game_sync_bulk_from_event_exp, 
    red_event_precond, 
    RT[neg_fsim_base], 
    red_neg_sim, 
    red_path, 
    
    red_neg_sim_wfair, 
    weak_fairness_list, 
    flag_role, 
    flag_fair_sim, 
    FLAG_STEP_TIME_MEASURE  
  ); 
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    "\nFSIM %1d:%1d:%1d*%1d:sxi bulk, after forced through sxi bulk]==================\n", 
    FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER 
  ); 
  red_print_graph(RT[result]); 
  #endif 
  for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
//    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nFSIM %1d:%1d:%1d*%1d:sxi %1d, RT[neg_sim_base] before forced through sxi]==================\n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, sxi
    ); 
    print_sync_xtion_lines(sxi, SYNC_XTION); 
/*
    if (FSIM_ITER == 2 && sxi == 11) { 
      fprintf(RED_OUT, "\nCaught FSIM_ITER == 2 and sxi == 11\n"); 
      fprintf(RED_OUT, "\n"); 
    } 
*/
//    red_print_graph(RT[neg_fsim_base]); 
//    #endif 

    child = red_game_forced_event_precondition_sync_ITERATIVE(
      event_exp, 
      red_event_precond, 
      RT[neg_fsim_base], 
      red_neg_sim, 
      red_path, 
      sxi, 
      red_neg_sim_wfair, 
      weak_fairness_list, 
      flag_role, 
      flag_fair_sim, 
      FLAG_STEP_TIME_MEASURE  
    ); 
//    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "FSIM %1d:%1d:%1d*%1d:sxi %1d, To destination: \n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, sxi
    ); 
    red_print_graph(red_event_precond); 
    fprintf(RED_OUT, "FSIM %1d:%1d:%1d*%1d:sxi %1d, Through events: \n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, sxi
    ); 
    pcform(event_exp); 
    fprintf(RED_OUT, 
      "FSIM %1d:%1d:%1d*%1d, neg sim: a new forcible component through sxi %1d:\n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, sxi
    ); 
    red_print_graph(child); 
//    #endif 

    RT[result] = red_bop(OR, RT[result], child); 
  }
  sxi = -2; 
  RT[result] = red_subsume(RT[result]); 
  RT_TOP--; // result 
  RT_TOP--; // fsim_base  

  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: FSIM %1d:%1d:%1d*%1d, the RT_TOP values (New %1d, Old %1d)\n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, GUNTIL_ITER, 
      RT_TOP, orig_rttop 
    ); 
    fprintf(RED_OUT, 
      "       are not consistent in red_event_precondition_to_forced_neg_fxp()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
  #endif 
  
  return(RT[result]); 
}
  /* red_event_precondition_to_forced_neg_sim() */  









/*****************************************************************
 *  The fixpoint calculated is ~fxp. 
 *  Thus the early termination condition is that there 
 *  exists an initial state s1 of the model such that 
 *  for all initial state s2 of the specification, 
 *  s1 and s2 is in ~fxp. 
 *  Suppose I1 and I2 are the initial conditions of the model and the spec
 *  respectively.  
 *  Basically, exists s2 (I1&&~(~fxp)) characterizes those 
 *  initial states in I1 with a matching initial state in I2 in fxp. 
 *  Our strategy is to check I1 && ~exists s2 (I1&&~(~fxp)).  
 *  If it is empty, then it means that every initial state in I1
 *  has a matching initial state in I2 in fxp 
 *  and we can deny the simulation immediately.  
 */
 
int	check_game_timed_branching_early_failure(
  int			neg_sim, 
  struct red_type	*red_init, 
  int			role_sim_destroyer // the model 
) { 
  int	init_neg_sim; 
  
  RT[init_neg_sim = RT_TOP++] = red_bop(AND, red_init, RT[neg_sim]); 
  RT[init_neg_sim] = red_hull_normalize(init_neg_sim); 
  if (RT[init_neg_sim] != NORM_FALSE) { 
    RT_TOP--; // init_neg_sim 
    return(TYPE_TRUE); 
  } 
  else {
    RT_TOP--; // init_neg_sim 
    return(TYPE_FALSE); 
  }
}
  /* check_game_timed_branching_early_failure() */ 



struct red_type	*red_update_sim(
  struct red_type	*red_sim, 
  struct red_type	*red_neg_sim
) { 
  int	sim; 
  
  RT[sim = RT_TOP++] = red_bop(AND, red_complement(red_neg_sim), 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  RT[sim] = red_hull_normalize(sim); 
  RT[sim] = red_subsume(RT[sim]); 
  RT_TOP--; 
  return(RT[sim]); 	
}
  /* red_update_sim() */  
  
  
  






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
 */




#ifdef RED_DEBUG_GAME_MODE
int	count_guntil = 0; 
#endif 


struct red_type	*red_game_euntil_bck(
  struct red_type		*red_init, 
  struct red_type		*red_neg_fsim_base, 
  struct red_type		*red_path, 
  struct red_type		*red_neg_sim_wfair, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				time_distance_lb, 
  int				flag_role, 
  int				*flag_result_ptr    
) { 
  struct red_type	*conj, *filter, *modal_constraint;
  int			fsim, pre_neg_fsim, neg_fsim, path; 

  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
  #endif 

/*
  fprintf(RED_OUT, "count_euntil=%1d\n", ++count_euntil); 
  fflush(RED_OUT); 

  fprintf(RED_OUT, "\nIn red_reachable(%x)\nInitial RED:\n", RED_NEW_REACHABLE);
  red_print_graph(RED_NEW_REACHABLE);
  */
  #ifdef RED_DEBUG_GAME_MODE
  ++count_guntil; 
  orig_rttop = RT_TOP;  
  #endif 
  
  GUNTIL_ITER = 0;
  /*
  fprintf(RED_OUT, "\nStarting computing reachable state set:\n");
  */

  /* We first need to calculate the suffix to the destination of 
   * the until image. 
   */ 
    
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "%s, after the initial event precondition (NTP), red_dest:\n", 
      fseq("GU"),     
    ); 
    red_print_graph(red_neg_fsim_base); 
  #endif 
  
  RT[neg_fsim = RT_TOP++] = red_neg_fsim_base; 
  if (   red_init != NORM_FALSE
      && time_distance_lb < 0 
      && red_bop(AND, red_init, RT[neg_fsim]) != NORM_FALSE
      ) { 
    fprintf(RED_OUT, 
      "\n%s, early base simulation failure detected.\n", 
      fseq("GU") 
    ); 
    *flag_result_ptr = FLAG_GOAL_EARLY_REACHED; 
    RT_TOP--; // neg_fsim 
    return(RT[neg_fsim]);  
  } 
  if (time_distance_lb < 0) 
    RT[neg_fsim] = crd_one_constraint(
      RT[neg_fsim], ZONE[0][ZENO_CLOCK], time_distance_lb
    );
  RT[pre_neg_fsim = RT_TOP++] = NORM_FALSE; 
  for (GUNTIL_ITER = 1; RT[pre_neg_fsim] != RT[neg_fsim]; GUNTIL_ITER++) { 
    RT[pre_neg_fsim] = RT[neg_fsim]; 
    #ifdef RED_DEBUG_GAME_MODE
      fprintf(RED_OUT, 
        "\n%s, Before one iteration of GUNTIL fixpoint.\n", 
        fseq("GU")     
      ); 
      red_print_graph(RT[neg_fsim]); 
    #endif 
  // This is the first such call in red_game_euntil_bck() 
    RT[neg_fsim] = red_event_precondition_to_forced_neg_sim(
      PS_EXP_TRUE, 
      NORM_NO_RESTRICTION, // red_game_sync_bulk_from_event_exp
      NORM_NO_RESTRICTION, // event_precond, 
      RT[neg_fsim], 
      red_path, 
      red_neg_sim_wfair, 
      weak_fairness_list, 
      flag_role, 
      FLAG_FAIR_SIM, 
      (time_distance_lb < 0 && GUNTIL_ITER == 1) ? time_distance_lb : 0 
    ); 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\n%s, After one iteration of GUNTIL fixpoint.\n", 
      fseq("GU")    
    ); 
    red_print_graph(RT[neg_fsim]); 
    #endif 
    if (   red_init != NORM_FALSE
//        && time_distance_lb < 0 
        && red_bop(AND, red_init, RT[neg_fsim]) != NORM_FALSE
        ) { 
      fprintf(RED_OUT, 
        "\nGU %1d, early inductive simulation failure detected.\n", 
        GUNTIL_ITER
      ); 
      *flag_result_ptr = FLAG_GOAL_EARLY_REACHED; 
      RT[neg_fsim] = red_bop(OR, RT[neg_fsim], RT[pre_neg_fsim]); 
      RT[neg_fsim] = red_subsume(RT[neg_fsim]); 
      RT_TOP--; // pre_neg_fsim 
      RT_TOP--; // neg_fsim 
      return(RT[neg_fsim]);  
    } 
    RT[neg_fsim] = red_bop(OR, RT[neg_fsim], RT[pre_neg_fsim]); 
    
    RT[neg_fsim] = red_subsume(RT[neg_fsim]); 

    garbage_collect(FLAG_GC_SILENT); 
  } 
  GUNTIL_ITER = -1; 
  RT_TOP--; // pre 
  
  if (time_distance_lb < 0) {
    #ifdef RED_DEBUG_GAME_MODE
    print_cpu_time(
      "%s, in fairness bck, before deactivating ZENO_CLOCK=%1d", 
      fseq("GU"), ZENO_CLOCK
    ); 
    red_print_graph(RT[neg_fsim]); 
    #endif 
    RT[neg_fsim] = red_time_clock_eliminate(RT[neg_fsim], ZENO_CLOCK); 
  }
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, 
    "\n%s, Leaving red_game_euntil_bck().\n", 
    fseq("GU"),    
  ); 
  red_print_graph(RT[neg_fsim]); 
  #endif 
  
  RT_TOP--; // neg_fsim  
  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: %s, the RT_TOP value (New %1d, Old %1d)\n", 
      fseq("GU"), 
      RT_TOP, orig_rttop     
    ); 
    fprintf(RED_OUT, 
      "       is not consistent in red_game_euntil_bck()!\n"  
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
  #endif 
  
  *flag_result_ptr = FLAG_GOAL_NORMAL; 
  return(RT[neg_fsim]);

  /*
  fprintf(RED_OUT, "\nEnd of reachable state set computation\n");
  fflush(RED_OUT);
  */
}
  /* red_game_euntil_bck() */




/* This procedure returns the state pairs that do not 
 * have a timed branching simulation. 
 */ 
struct red_type	*game_timed_branching_nsim_bck(
  struct red_type	*red_init, 
  int			path, 
  int			sim, 
  int			flag_bisim_checking, 
  int			role_sim_destroyer, 
  int			*flag_result_ptr  
) {
  int			neg_sim, prev_neg_sim, gfp_path, necessary_fair, 
			local_flag_time_progress, i;
  struct ps_exp_type	*game_empty; 

//  #ifdef RED_DEBUG_GAME_MODE
  int orig_rttop = RT_TOP; 
//  #endif 
  
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\n===============================================\n"); 
    fprintf(RED_OUT, 
      "FSIM %1d:0, RT_TOP=%1d, Evaluating the negated timed branching simulation:\n", 
      FSIM_SPEC_ITER, RT_TOP
    ); 
    print_sync_xtions("Entering neg timed br sim", 
      SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME
    ); 
  #endif 

  local_flag_time_progress = GSTATUS[INDEX_TIME_PROGRESS]; 
  if (   (GSTATUS[INDEX_TIME_MODE_SHAPES] & FLAG_TIME_MODE_ALL_TCONVEX)
      && (   RT[path] == NORM_TRUE
          || RT[path] == RT[DECLARED_GLOBAL_INVARIANCE]
          || RT[path] == RT[REFINED_GLOBAL_INVARIANCE] 
          || RT[path] == RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES] 
      )   ) 
    GSTATUS[INDEX_TIME_PROGRESS] 
    = (GSTATUS[INDEX_TIME_PROGRESS] & ~MASK_TIME_PROGRESS_OPTIONS)
    | FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY; 

  RT[neg_sim = RT_TOP++] = red_neg_branch_sim_base(role_sim_destroyer); 
  // This is the first such call in game_timed_branching_nsim_bck() 
  
  if (check_game_timed_branching_early_failure(
        neg_sim, red_init, role_sim_destroyer 
      )  ) {  
    RT_TOP = RT_TOP-1; // neg_sim 
    *flag_result_ptr = FLAG_NO_BRANCHING_SIM;  
    GSTATUS[INDEX_TIME_PROGRESS] = local_flag_time_progress; 
//    #ifdef RED_DEBUG_GAME_MODE
    if (orig_rttop != RT_TOP) { 
      fprintf(RED_OUT, 
        "Error: FSIM %1d:%1d, the RT_TOP value is not consistent in fairness_bck()!\n", 
        FSIM_SPEC_ITER, FSIM_ITER
      ); 
      fflush(RED_OUT); 
      bk(0); 	
    } 
//    #endif 
    return(RT[neg_sim]); 
  } 
  else if (!flag_bisim_checking) 
    game_spec_envr_exp = NULL; 
  else { 
    fprintf(RED_OUT, 
      "\nERROR: At the moment, bisimulation is not supported. \n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
      
  RT[neg_sim] = red_game_euntil_bck(
    red_init, 
    RT[neg_sim], 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES], 
    NORM_NO_RESTRICTION, 
    NULL, 
    0, // time_distance_lb 
    role_sim_destroyer, 
    flag_result_ptr   
  );   
  if (check_game_timed_branching_early_failure(
        neg_sim, red_init, role_sim_destroyer 
      )  ) {  
    RT_TOP = RT_TOP-1; // neg_sim 
    *flag_result_ptr = FLAG_NO_BRANCHING_SIM;  
    GSTATUS[INDEX_TIME_PROGRESS] = local_flag_time_progress; 
//    #ifdef RED_DEBUG_GAME_MODE
    if (orig_rttop != RT_TOP) { 
      fprintf(RED_OUT, 
        "Error: FSIM %1d:%1d, the RT_TOP value is not consistent in fairness_bck()!\n", 
        FSIM_SPEC_ITER, FSIM_ITER
      ); 
      fflush(RED_OUT); 
      bk(0); 	
    } 
//    #endif 
  
    return(RT[neg_sim]); 
  } 
  RT_TOP--; /* neg_sim */ 

  *flag_result_ptr = FLAG_A_BRANCHING_SIM_EXISTS; 
  GSTATUS[INDEX_TIME_PROGRESS] = local_flag_time_progress; 

//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: FSIM %1d:%1d, the RT_TOP value is not consistent in fairness_bck()!\n", 
      FSIM_SPEC_ITER, FSIM_ITER
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
//  #endif 
  
  return(RT[neg_sim]);
}
  /* game_timed_branching_nsim_bck() */ 






inline void	setup_game_fairness_before_gfp(
  struct ps_exp_type	*game_exp, 
  int			path, 
  int			neg_sim_wfair, 
  int			token_fair_sim, 
  int			flag_polarity   
) { 
  struct ps_fairness_link_type	*fl;

  RT[neg_sim_wfair] = NORM_NO_RESTRICTION; 
  for (fl = game_exp->u.mexp.weak_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) {
    fl->fairness->u.eexp.red_precond = red_label_bck( 
      fl->fairness->u.eexp.precond_exp, 
      TYPE_TRUE, 
      path, 
      path, // This won't change in the evaluation of red_label_bck().      
      flag_polarity
    ); 
    protect_from_gc_with_token(
      fl->fairness->u.eexp.red_precond, 
      token_fair_sim, TOKEN_PROTECTION_LIST
    ); 
    fl->fairness->u.eexp.red_postcond = red_label_bck( 
      fl->fairness->u.eexp.postcond_exp, 
      TYPE_TRUE, 
      path, 
      path, // This won't change in the evaluation of red_label_bck().      
      flag_polarity
    ); 
    protect_from_gc_with_token(
      fl->fairness->u.eexp.red_postcond, 
      token_fair_sim, TOKEN_PROTECTION_LIST
    ); 
    if (fl->fairness->u.eexp.event_exp == NULL) {
      RT[neg_sim_wfair] = red_bop(AND, RT[neg_sim_wfair], 
        fl->fairness->u.eexp.red_precond
      ); 
    }
  } 

  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nBefore looping for the strong fairness assumptions. \nThe neg sim weak fairness: \n"); 
    red_print_graph(RT[neg_sim_wfair]); 
  #endif 

  for (fl = game_exp->u.mexp.strong_fairness_list; 
       fl; 
       fl = fl->next_ps_fairness_link
       ) { 
    fl->fairness->u.eexp.red_precond = red_label_bck( 
      fl->fairness->u.eexp.precond_exp, 
      TYPE_TRUE, 
      path, 
      path, // This won't change in the evaluation of red_label_bck().      
      flag_polarity
    ); 
    protect_from_gc_with_token(
      fl->fairness->u.eexp.red_precond, 
      token_fair_sim, TOKEN_PROTECTION_LIST
    ); 
    if (fl->fairness->u.eexp.event_exp) { 
      fl->fairness->u.eexp.red_postcond = red_label_bck( 
        fl->fairness->u.eexp.postcond_exp, 
        TYPE_TRUE, 
        path, 
        path, // This won't change in the evaluation of red_label_bck().      
        flag_polarity
      ); 
      protect_from_gc_with_token(
        fl->fairness->u.eexp.red_postcond, 
        token_fair_sim, TOKEN_PROTECTION_LIST
      ); 
    } 
    #ifdef RED_DEBUG_GAME_MODE
/*        print_resources("Connecting strong fairness"); 
*/
      fprintf(RED_OUT, "\nstrong fairness for "); 
      pcform(fl->fairness); 
      fprintf(RED_OUT, "\n"); 
      fprintf(RED_OUT, "\nstrong red fairness for "); 
      red_print_graph(fl->red_fairness); 
      fprintf(RED_OUT, "\n"); 
    #endif 
  }
} 
  /* setup_game_fairness_before_gfp() */ 




  
struct red_type	*red_forced_neg_sim_through_strong_fairness( 
  struct ps_exp_type		*game_exp, 
  int				prev_neg_sim, 
  int				path, 
  struct red_type		*red_neg_sim_wfair, 
  struct ps_fairness_link_type	*weak_fairness_list, 
  int				flag_role 
) {   
  struct ps_fairness_link_type	*fl;
  struct cache4_hash_entry_type	*ce; 
  int				neg_sim, count_strong, sim, neg_sim_wfair, 
  				flag_result; 
  
//  #ifdef RED_DEBUG_GAME_MODE
  int	orig_rttop = RT_TOP; 
//  #endif 

  RT[neg_sim = RT_TOP++] = RT[prev_neg_sim]; 
//  fprintf(RED_OUT, "\nBefore looping for the strong fairness assumptions.:\n"); 
  
  for (FSIM_STRONG_ITER = 1, fl = game_exp->u.mexp.strong_fairness_list; 
       fl; 
       FSIM_STRONG_ITER++, fl = fl->next_ps_fairness_link
       ) { 
    int	strong_events; 

    #ifdef RED_DEBUG_GAME_MODE
      fprintf(RED_OUT, 
        "\n====[Checking STRONG FAIRNESS %1d]===========\n", 
        FSIM_STRONG_ITER
      ); 
      pcform(fl->fairness);  
      fprintf(RED_OUT, "\nTo forced destination: \n"); 
      red_print_graph(RT[neg_sim]); 
    #endif 
    
    ce = cache4_check_result_key(OP_GAME_FORCED_ONE_STRONG_FAIRNESS, 
      RT[neg_sim], 
      // The procedure is called under the assumption that 
      // the following three CRD+RED will not be garbage-collected. 
      (struct hrd_exp_type *) fl->fairness->u.eexp.red_precond, 
      (int) fl->fairness->u.eexp.event_exp, 
      (int) fl->fairness->u.eexp.red_precond
    ); 
    if (ce->result) {
      RT[neg_sim] = ce->result; 
      continue; 
    } 
    if (fl->fairness->u.eexp.event_exp == NULL) {
      RT[neg_sim] = red_bop(AND, RT[neg_sim], 
        fl->fairness->u.eexp.red_precond
      ); 
      RT[neg_sim_wfair = RT_TOP++] = red_bop(AND, RT[path], 
        red_neg_sim_wfair
      ); 
      RT[neg_sim] = red_game_time_progress_bck(
        NULL, 
        neg_sim, neg_sim_wfair, MASK_GAME_ROLES, 
        TYPE_TRUE   
      ); 
      RT_TOP--; // neg_sim_wfair 
      RT[neg_sim] = red_hull_normalize(neg_sim); 
    }
    else {
  // This is the first such call 
  // in red_forced_neg_sim_through_strong_fairness(). 
      RT[neg_sim] = red_event_precondition_to_forced_neg_sim(
        fl->fairness->u.eexp.event_exp, 
        fl->fairness->u.eexp.red_game_sync_bulk_from_event_exp, 
        fl->fairness->u.eexp.red_precond, 
        RT[neg_sim],  // post condition 
        RT[path], 
        red_neg_sim_wfair, 
        game_exp->u.mexp.weak_fairness_list, 
        flag_role, 
        FLAG_FAIR_SIM, 
        0 // for time_distance_lb, 
      ); 
    } 
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nFSIM %1d:%1d:%1d, Instantaneous precondition to game destination for strong fairness:\n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER  
    );
    pcform(fl->fairness);  
    fprintf(RED_OUT, "\n"); 
    red_print_graph(RT[neg_sim]); 
  #endif 
    ce->result = RT[neg_sim] = red_game_euntil_bck(
      NORM_FALSE, 
      RT[neg_sim], 
      RT[path], 
      red_neg_sim_wfair, 
      game_exp->u.mexp.weak_fairness_list, 
      0, // for zero timing distance lower-bound 
      flag_role, 
      &flag_result   
    ); 

    #ifdef RED_DEBUG_GAME_MODE
/* 
      print_resources("Connecting strong fairness"); 
*/
      fprintf(RED_OUT, 
        "\nFSIM %1d:%1d:%1d, Game reachability for strong fairness:\n", 
        FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER  
      ); 
      pcform(fl->fairness); 
      fprintf(RED_OUT, "\n"); 
      red_print_graph(RT[neg_sim]); 
    #endif 
  }
  FSIM_STRONG_ITER = -1; 
  RT_TOP--; // neg_sim 
//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: FSIM %1d:%1d:%1d, the RT_TOP values, (new %1d, old %1d) \n", 
      FSIM_SPEC_ITER, FSIM_ITER, FSIM_STRONG_ITER, RT_TOP, orig_rttop   
    ); 
    fprintf(RED_OUT, 
      "       is not consistent in red_forced_neg_sim_through_strong_fairness()!\n"
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
//  #endif 
  return(RT[neg_sim]); 
} 
  /* red_forced_neg_sim_through_strong_fairness() */ 
  
  
  
 
  
  
    

/* The invariance is that RT[share_discontinuity] is for RT[path]. 
 * One important restriction for the correct execution of the 
 * procedure is that path_start and path_stop together specify 
 * a consecutive range of RT frames such that 
 * path_stop = RT_TOP-1 at the time of the procedure invocation.  
 */ 

// Now it seems that we need to use different postconditions for 
// the backward analysis of spec and model. 
// The postconditions for the model, as ineq_universe, needs 
// to take into consideration of the weak fair state conditions. 
// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
struct red_type	*game_fair_nsim_bck(
  struct ps_exp_type	*game_spec, 
  struct red_type	*red_init, 
  int			path, 
  int			sim, 
  int			flag_role 
) {
  int				prev_neg_sim, neg_sim, w, neg_sim_wfair, 
				neg_fair_path, 
				i, orig_time_progress, flag_result;
  struct ps_fairness_link_type	*fl;

//  #ifdef RED_DEBUG_GAME_MODE
  int orig_rttop = RT_TOP; 
//  #endif 
  
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\n===============================================\n"); 
    fprintf(RED_OUT, 
      "FSIM %1d:0, RT_TOP=%1d, Evaluating the fairness of :\n", 
      FSIM_SPEC_ITER, RT_TOP
    ); 
    pcform(game_spec); 
  #endif 
  
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "FSIM %1d:0, RT_TOP=%1d, after setting up the fairness for model\n", 
      FSIM_SPEC_ITER, RT_TOP
    ); 
  #endif 
  RT[neg_sim_wfair = RT_TOP++] = NORM_NO_RESTRICTION; 
  setup_game_fairness_before_gfp(
    game_spec, 
    path, 
    neg_sim_wfair, 
    token_fair_sim, 
    FLAG_ROOT_NOAPPROX 
  ); 
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "FSIM %1d:0, For RT[neg_sim_wfair=%1d]:\n", 
      FSIM_SPEC_ITER, neg_sim_wfair
    ); 
    red_print_graph(RT[neg_sim_wfair]); 
  #endif 

  ITERATION_COUNT = 0; 
  RT[neg_sim = RT_TOP++] = red_bop(AND, RT[sim], RT[neg_sim_wfair]); 
  RT[sim] = red_bop(AND, RT[sim], red_complement(RT[neg_sim_wfair])); 
  RT[neg_fair_path = RT_TOP++] = red_bop(AND, RT[path], RT[neg_sim_wfair]); 
  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "FSIM %1d:0, For RT[sim=%1d]:\n", 
      FSIM_SPEC_ITER, sim
    ); 
    red_print_graph(RT[sim]); 
    fprintf(RED_OUT, "FSIM %1d:0, For RT[neg_sim=%1d]:\n", 
      FSIM_SPEC_ITER, neg_sim
    ); 
    red_print_graph(RT[neg_sim]); 
    fprintf(RED_OUT, "FSIM %1d:0, For RT[neg_fair_path=%1d]:\n", 
      FSIM_SPEC_ITER, neg_fair_path
    ); 
    red_print_graph(RT[neg_fair_path]); 
  #endif 
  RT[prev_neg_sim = RT_TOP++] = NORM_NO_RESTRICTION; 
  for (FSIM_ITER=1, NZF = 0; 
       RT[neg_sim] != NORM_FALSE && RT[neg_sim] != RT[prev_neg_sim]; 
       FSIM_ITER++, NZF++
       ) {
    int	dest; 

    /* Check if early decision has happend.
     */ 

    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\n---[FSIM %1d:%1d]---------------------------\n", 
      FSIM_SPEC_ITER, FSIM_ITER   
    ); 
    fprintf(RED_OUT, 
      "Start a negated fairness iteration from RT[neg_sim=%1d]:\n", 
      neg_sim  
    ); 
    red_print_graph(RT[neg_sim]); 
/* 
    print_resources("NZF"); 
*/
    #endif 

    RT[prev_neg_sim] = RT[neg_sim];
    if (   CLOCK_COUNT 
        && (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) != FLAG_ZENO_CYCLE_OK
        ) { 
      FSIM_STRONG_ITER = 0; 
      RT[neg_sim] = red_game_euntil_bck(
        NORM_FALSE, 
        RT[neg_sim], // dest   
        RT[neg_fair_path], 
        RT[neg_sim_wfair], 
        game_spec->u.mexp.weak_fairness_list, 
        CLOCK_NEG_INFINITY, 
        flag_role, 
        &flag_result  
      );

      #ifdef RED_DEBUG_GAME_MODE 
      print_cpu_time(
        "FSIM %1d:%1d, in fairness bck, after strong non-Zeno progress", 
        FSIM_SPEC_ITER, FSIM_ITER
      ); 
      red_print_graph(RT[neg_sim]); 
      #endif 

      RT[neg_sim] = red_subsume(RT[neg_sim]);
      RT[neg_sim] = red_hull_normalize(neg_sim);
      RT[neg_sim] = red_subsume(RT[neg_sim]);
      #ifdef RED_DEBUG_GAME_MODE
      print_cpu_time(
        "FSIM %1d:%1d, after checking nonZeno requirement", 
        FSIM_SPEC_ITER, FSIM_ITER
      ); 
      red_print_graph(RT[neg_sim]);
      #endif 
    } 

    RT[neg_sim] = red_forced_neg_sim_through_strong_fairness( 
      game_spec, 
      neg_sim /* dest */,  
      neg_fair_path, 
      RT[neg_sim_wfair], 
      game_spec->u.mexp.weak_fairness_list, 
      flag_role 
    ); 
    RT[neg_sim] = red_hull_normalize(neg_sim); 

    #ifdef RED_DEBUG_GAME_MODE
      /* We are just curious at what has been eliminated. 
       */ 
    fprintf(RED_OUT, 
      "\nFSIM %1d:%1d, a fair_cycle end, new RT[neg_fair_cycle=%1d]:\n", 
      FSIM_SPEC_ITER, FSIM_ITER, neg_sim
    );
    red_print_graph(RT[neg_sim]);
    fprintf(RED_OUT, 
      "\nFSIM %1d:%1d, newly removed neg sim states for :\n", 
      FSIM_SPEC_ITER, FSIM_ITER   
    );
    pcform(game_spec); 
    RT[w = RT_TOP++] = red_complement(RT[neg_sim]);
    RT[w] = red_bop(AND, RT[prev_neg_sim], RT[w]); 
    RT[w] = red_hull_normalize(w); 
    red_print_graph(RT[w]); 
    RT_TOP--; // w 
    #endif 
  } 
  FSIM_ITER = -1; 
  RT_TOP--; /* prev_neg_sim */ 
  RT_TOP--; /* neg_fair_path */ 
  
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, "\n===============================================\n"); 
  fprintf(RED_OUT, 
    "FSIM %1d:%1d, RT[neg_sim] after the fairness GFP :\n", 
    FSIM_SPEC_ITER, FSIM_ITER 
  ); 
  pcform(game_spec); 
/*
    print_resources("\nThe result of fair cycle evaluation"); 
*/
  red_print_graph(RT[neg_sim]); 
  #endif 

  RT[neg_sim] = red_game_euntil_bck(
    red_init, 
    RT[neg_sim], 
    RT[path], 
    NORM_NO_RESTRICTION, 
    NULL, 
    0, 
    flag_role, 
    &flag_result   
  ); 

  #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\n===============================================\n"); 
    fprintf(RED_OUT, 
      "FSIM %1d:%1d, RT_TOP:%1d->%1d, leaving the fairness of :\n", 
      FSIM_SPEC_ITER, FSIM_ITER, orig_rttop, RT_TOP
    ); 
    pcform(game_spec); 
/*
    print_resources("\nThe result of fair path evaluation"); 
*/
    red_print_graph(RT[neg_fair_cycle]); 
  #endif 
  
  RT[sim] = red_update_sim(RT[sim], RT[neg_sim]); 
  RT_TOP--; /* neg_sim */ 
  RT_TOP--; // neg_sim_wfair

//  #ifdef RED_DEBUG_GAME_MODE
  if (orig_rttop != RT_TOP) { 
    fprintf(RED_OUT, 
      "Error: FSIM %1d:%1d, the RT_TOP value is not consistent in fairness_bck()!\n", 
      FSIM_SPEC_ITER, FSIM_ITER
    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
//  #endif 
  
  return(RT[neg_sim]);
}
  /* game_fair_nsim_bck() */ 








void	commit_branching_sim_result(
  int				result, 
  int				itr, 
  struct red_type		*red_neg_sim, 
  struct sim_check_return_type	*sr 
) { 
  char	*nz_name, *sim_name, *app_name; 
  
  sr->status  
  = (sr->status & ~MASK_BRANCHING_SIM_RESULT) 
  | (result & MASK_BRANCHING_SIM_RESULT);  
  
  sr->iteration_count = itr; 
  
  switch (sr->status & MASK_GFP_TASK_TYPE) {
  case FLAG_GFP_TASK_SIM_CHECK: 
    sim_name = "simulation\0"; 
    break; 
  case FLAG_GFP_TASK_BISIM_CHECK: 
    sim_name = "bisimulation\0"; 
    break; 
  }

  switch (sr->status & MASK_SIM_ZENO_CYCLE) {
  case FLAG_SIM_USE_PLAIN_NONZENO: 
    nz_name = "non-Zeno "; 
    app_name = "\0"; 
    break; 
  case FLAG_SIM_USE_APPROX_NONZENO:
    nz_name = "non-Zeno "; 
    app_name = "approximate "; 
    break; 
  case FLAG_SIM_ZENO_CYCLE_OK: 
    nz_name = "\0"; 
    app_name = "\0"; 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal non-Zeno and approximation option %x in simulation.\n", 
      sr->status & MASK_SIM_ZENO_CYCLE
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }

  switch (sr->status & MASK_BRANCHING_SIM_RESULT) {
  case FLAG_BRANCHING_SIM_UNDECIDED: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: %s%sbranching %s undecided.\n", 
      app_name, nz_name, sim_name   
    ); 
    break; 
  case FLAG_NO_BRANCHING_SIM: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: No %s%sbranching %s!\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_BRANCHING_SIM_INCONCLUSIVE: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: %s%sbranching %s inconclusive.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_A_BRANCHING_SIM_EXISTS: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: A %s%sbranching %s exists.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal %s%sbranching %s result value %x.\n", 
      app_name, nz_name, sim_name, 
      sr->status & MASK_BRANCHING_SIM_RESULT
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  fflush(RED_OUT); 
  sr->final_neg_sim_relation_diagram = red_neg_sim; 
  red_mark(red_neg_sim, FLAG_GC_USER_STATIC1); 
}
  /* commit_branching_sim_result() */ 




void	commit_fair_sim_result(
  int				result, 
  int				itr, 
  struct red_type		*red_neg_sim, 
  struct sim_check_return_type	*sr 
) { 
  char	*nz_name, *sim_name, *app_name; 
  
  sr->status  
  = (sr->status & ~MASK_FAIR_SIM_RESULT) 
  | (result & MASK_FAIR_SIM_RESULT);  
  
  sr->iteration_count = itr; 
  
  switch (sr->status & MASK_GFP_TASK_TYPE) {
  case FLAG_GFP_TASK_SIM_CHECK: 
    sim_name = "simulation\0"; 
    break; 
  case FLAG_GFP_TASK_BISIM_CHECK: 
    sim_name = "bisimulation\0"; 
    break; 
  }

  switch (sr->status & MASK_SIM_ZENO_CYCLE) {
  case FLAG_SIM_USE_PLAIN_NONZENO: 
    nz_name = "non-Zeno "; 
    app_name = "\0"; 
    break; 
  case FLAG_SIM_USE_APPROX_NONZENO:
    nz_name = "non-Zeno "; 
    app_name = "approximate "; 
    break; 
  case FLAG_SIM_ZENO_CYCLE_OK: 
    nz_name = "\0"; 
    app_name = "\0"; 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal non-Zeno and approximation option %x in simulation.\n", 
      sr->status & MASK_SIM_ZENO_CYCLE
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }

  switch (sr->status & MASK_FAIR_SIM_RESULT) {
  case FLAG_FAIR_SIM_UNDECIDED: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: %s%sfair %s undecided.\n", 
      app_name, nz_name, sim_name   
    ); 
    break; 
  case FLAG_NO_FAIR_SIM: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: No %s%sfair %s!\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_FAIR_SIM_INCONCLUSIVE: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: %s%sfair %s inconclusive.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_A_FAIR_SIM_EXISTS: 
    fprintf(RED_OUT, 
      ">> RESULT COMMITTED: A %s%sfair %s exists.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal %s%sfair %s result value %x.\n", 
      app_name, nz_name, sim_name, 
      sr->status & MASK_BRANCHING_SIM_RESULT
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  fflush(RED_OUT); 
  sr->final_neg_sim_relation_diagram = red_neg_sim; 
  red_mark(red_neg_sim, FLAG_GC_USER_STATIC1); 
}
  /* commit_fair_sim_result() */ 




  
  
  
/********************************************************************
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
    
*/
struct sim_check_return_type	*red_fair_sim_check(
  struct red_type	*red_init, 
  struct red_type	*red_inv, 
  int			flag_bisim_checking  
) {
  int				fair, count_fairness, init_w, counter, 
				sim, neg_sim, prev_neg_sim, gfp_path, 
				modl_fairness, spec_fairness, 
				flag_result, orig_fairness_estatus; 
  struct red_type		*conj, *tmp_initial; 
  struct sim_check_return_type	*sr; 
  struct red_link_type		dummy_red_head, *red_tail, *rl; 
  struct ps_fairness_link_type	*fair_fl, *fl;
  struct ps_exp_type		*game_empty; 

  #ifdef RED_DEBUG_GAME_MODE
  print_resources("entering red_simulation_check\n"); 
  red_print_graph(red_sim); 
  #endif 
  
/* The following specification structure is used for zeno constraint 
 * calculation. 
 * In the first version of the algorithm, we did not consider 
 * zeno states in the quantification. 
 */ 
/*  
  fprintf(RED_OUT, "\nRT[XI_GAME_SYNC_BULK=%1d]:\n", XI_GAME_SYNC_BULK); 
  red_print_graph(RT[XI_GAME_SYNC_BULK]); 
*/  
  if (GSTATUS[INDEX_GAME_ROLES] & FLAG_GAME_ROLES_CHANGED) {
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nBefore game fairness structuring: RT[15]->status=%x\n", 
      RT[15]->status
    ); 
    fflush(RED_OUT); 
    psx("before constructing bisim structures"); 
    #endif 

    construct_bisim_structures_for_a_role_spec(); 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, 
      "\nAfter game fairness structuring: RT[15]->status=%x\n", 
      RT[15]->status
    ); 
    psx("after constructing bisim structures"); 
    psx_status("g sxi after constructing bisim structures", 
      SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME
    ); 
    fflush(RED_OUT); 
    #endif 
  } 

 // print_sync_xtions("DECLARED", SYNC_XTION, SYNC_XTION_COUNT); 
 // print_sync_xtions("GAME", SYNC_XTION_GAME, SYNC_XTION_COUNT_GAME); 
  
  sr = (struct sim_check_return_type *) 
    malloc(sizeof(struct sim_check_return_type)); 
  sr->status = 0; 
  sr->iteration_count = 0; 
  sr->initial_state_pair_diagram = red_init; 
  red_mark(red_init, FLAG_GC_USER_STATIC1); 
  sr->counter_example_tree = NULL;  
  
  switch (GSTATUS[INDEX_ZENO_CYCLE] & MASK_ZENO_CYCLE) { 
  case FLAG_USE_PLAIN_NONZENO: 
    sr->status = FLAG_BISIM_USE_PLAIN_NONZENO; 
    break; 
  case FLAG_SIM_USE_APPROX_NONZENO: 
    sr->status = FLAG_BISIM_USE_APPROX_NONZENO; 
    break; 
  case FLAG_SIM_ZENO_CYCLE_OK: 
    sr->status = FLAG_BISIM_ZENO_CYCLE_OK; 
    break; 
  } 

  switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
  case TASK_BRANCHING_BISIM_CHECKING:  
    sr->status = (sr->status & ~MASK_GFP_TASK_TYPE) 
    | FLAG_GFP_TASK_BISIM_CHECK; 
    break; 
  case TASK_BRANCHING_SIM_CHECKING:  
    sr->status = (sr->status & ~MASK_GFP_TASK_TYPE) 
    | FLAG_GFP_TASK_SIM_CHECK;
    break;  
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Incompatible task %x in simulation.\n", 
      GSTATUS[INDEX_TASK] & MASK_TASK
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  if (GSTATUS[INDEX_COUNTER_EXAMPLE] & FLAG_COUNTER_EXAMPLE) { 
    red_tail = &dummy_red_head; 
    red_tail->result = NORM_TRUE; 
    red_tail->next_red_link = NULL; 
  } 

  // Note in each gfp loop, we need the splitted path components 
  // on the top of the RT stack. 
  #ifdef RED_DEBUG_GAME_MODE
  fprintf(RED_OUT, "\nBefore iterating the game model fairness:\n"); 
  pcform(GAME_MODL_EXP); 
  fprintf(RED_OUT, "\nBefore iterating the game spec fairness:\n"); 
  pcform(GAME_SPEC_EXP); 
  #endif 
  
  FSIM_ITER = -1; 
  FSIM_STRONG_ITER = -1; 

  GSTATUS[INDEX_GFP] = GSTATUS[INDEX_GFP] | FLAG_IN_GAME_GFP; 
  token_fair_sim = get_a_new_gc_token(&TOKEN_PROTECTION_LIST); 
  game_empty = ps_exp_alloc(TYPE_GAME_SIM); 
  game_modl_envr_exp = prepare_game_fairness(
    GAME_MODL_EXP, game_empty, GAME_ENVR_EXP, FLAG_GAME_MODL 
  ); 

/*
  fprintf(RED_OUT, "\ngame modl envr exp:\n"); 
  pcform(game_modl_envr_exp); 
  fflush(RED_OUT); 
*/

  /* We first check the negation of branching simulation, 
   * maybe with Zeno checking option. 
   */ 
  RT[sim = RT_TOP++] = red_bop(AND, red_inv, 
    RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]
  ); 
  // First, try to refute with non-Zeno timed branching simulation. 
  RT[neg_sim = RT_TOP++] = game_timed_branching_nsim_bck(
    red_init, 
    INDEX_GAME_INVARIANCE_WITH_EQUALITIES, 
    sim, // side-effect to be on RT[sim]
    flag_bisim_checking, 
    FLAG_GAME_MODL, 
    &flag_result  
  ); 
  
  // Now we calculate the simulation pairs after the timed branching 
  // simulation construction. 
  // 
  // Now we check if the simulation can be denied early. 
  if (flag_result == FLAG_NO_BRANCHING_SIM) { 
    // sim_failure_process(RT[neg_sim], "timed branching", flag_bisim_checking, sr); 
    commit_branching_sim_result(
      FLAG_NO_BRANCHING_SIM, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 
    commit_fair_sim_result(
      FLAG_FAIR_SIM_UNDECIDED, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 
    RT_TOP = RT_TOP-2; // neg_sim, sim  
    release_gc_token(token_fair_sim, &TOKEN_PROTECTION_LIST); 
    return (sr); 
  } 
  else if (   GAME_MODL_EXP->u.mexp.strong_fairness_list == NULL 
           && GAME_MODL_EXP->u.mexp.weak_fairness_list == NULL           
           && GAME_SPEC_EXP->u.mexp.strong_fairness_list == NULL 
           && GAME_SPEC_EXP->u.mexp.weak_fairness_list == NULL           
           && GAME_ENVR_EXP->u.mexp.strong_fairness_list == NULL 
           && GAME_ENVR_EXP->u.mexp.weak_fairness_list == NULL           
           ) { 
    commit_branching_sim_result(
      FLAG_A_BRANCHING_SIM_EXISTS, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 
    commit_fair_sim_result(
      FLAG_FAIR_SIM_UNDECIDED, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 
    RT_TOP = RT_TOP-2; // neg_sim, sim  
    release_gc_token(token_fair_sim, &TOKEN_PROTECTION_LIST); 
    return (sr); 
  } 
  else { 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\nThe RT[neg_fxp=%1d] after branching simulation.\n", 
      neg_sim
    ); 
    red_print_graph(RT[neg_sim]); 
    #endif 
  
    commit_branching_sim_result(
      FLAG_A_BRANCHING_SIM_EXISTS, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 

    GAME_FAIRNESS_EXP = prepare_game_fairness(
      GAME_MODL_EXP, GAME_SPEC_EXP, GAME_ENVR_EXP, FLAG_GAME_MODL 
    ); 
    #ifdef RED_DEBUG_GAME_MODE
    fprintf(RED_OUT, "\nBefore iterating the GAME_FAIRNESS_EXP:\n"); 
    pcform(GAME_FAIRNESS_EXP); 
    #endif 
    RT[sim] 
    = red_bop(AND, red_inv, RT[INDEX_GAME_INVARIANCE_WITH_EQUALITIES]); 
    RT[neg_sim] = NORM_FALSE; 

    if ((GSTATUS[INDEX_GFP] & MASK_GFP_PATH) == FLAG_GFP_PATH_INVARIANCE) 
      gfp_path = INDEX_GAME_INVARIANCE_WITH_EQUALITIES; 
    else 
      gfp_path = sim; 
    
    if (flag_bisim_checking) {
      fprintf(RED_OUT, 
        "\nSORRY that fair bisimulation is not supported now.\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    GAME_FAIRNESS_EXP_AUX = NULL; 
    RT[neg_sim] = game_fair_nsim_bck(
      GAME_FAIRNESS_EXP, 
      red_init, gfp_path, sim, 
      FLAG_GAME_MODL  
    ); 
/*
      fprintf(RED_OUT, "\nAfter game_fair_nsim_bck(), \nRT[neg_sim=%1d]:\n", 
        neg_sim
      ); 
      red_print_graph(RT[neg_sim]); 
      fprintf(RED_OUT, "\nRT[sim=%1d]:\n", 
        sim
      ); 
      red_print_graph(RT[sim]); 
*/
    if (check_game_timed_branching_early_failure(
          neg_sim, red_init, FLAG_GAME_MODL 
        )  ) { 
      commit_fair_sim_result(
        FLAG_NO_FAIR_SIM, ITERATION_COUNT-1, RT[neg_sim], sr 
      ); 
      RT_TOP = RT_TOP-2; // neg_sim, sim  
      release_gc_token(token_fair_sim, &TOKEN_PROTECTION_LIST); 
      return(sr); 
    }

    FSIM_SPEC_ITER = -1; 
    GSTATUS[INDEX_GFP] = GSTATUS[INDEX_GFP] & ~FLAG_IN_GAME_GFP; 

    commit_fair_sim_result(
      FLAG_A_FAIR_SIM_EXISTS, ITERATION_COUNT-1, RT[neg_sim], sr 
    ); 
  }
  RT_TOP = RT_TOP-2; // neg_sim, sim  
  release_gc_token(token_fair_sim, &TOKEN_PROTECTION_LIST); 
  return (sr); 
}
  /* red_fair_sim_check() */ 




struct red_type	**construct_red_array_from_one(list, rc) 
	struct red_link_type	*list; 
	int			rc; 
{ 
  struct red_type	**a; 
  struct red_link_type	*rl; 
  int			ii; 
  
  a = ((struct red_type **) 
       malloc(ITERATION_COUNT * sizeof(struct red_type *))
       ) - 1; 
  for (ii = 1, rl = list; ii <= rc; ii++, rl = rl->next_red_link) { 
    a[ii] = rl->result; 
  } 
  free_red_list(list); 
  return(a); 
}
  /* construct_red_array_from_one() */ 




void	print_counter_example_tree(t) 
  struct counter_example_tree_node_type	*t;  
{ 
} 
  /* print_counter_example_tree() */ 
  
  
  
 
#define print_bisim_check_return print_sim_check_return 
void	print_sim_check_return(sr) 
  struct sim_check_return_type	*sr; 
{ 
  int	i, ic; 
  char	*sim_name, *nz_name, *app_name; 
  
  switch (sr->status & MASK_GFP_TASK_TYPE) {
  case FLAG_GFP_TASK_SIM_CHECK: 
    sim_name = "simulation\0"; 
    break; 
  case FLAG_GFP_TASK_BISIM_CHECK: 
    sim_name = "bisimulation\0"; 
    break; 
  }

  switch (sr->status & MASK_SIM_ZENO_CYCLE) {
  case FLAG_SIM_USE_PLAIN_NONZENO: 
    nz_name = "non-Zeno "; 
    app_name = "\0"; 
    break; 
  case FLAG_SIM_USE_APPROX_NONZENO:
    nz_name = "non-Zeno "; 
    app_name = "approximate "; 
    break; 
  case FLAG_SIM_ZENO_CYCLE_OK: 
    nz_name = "\0"; 
    app_name = "\0"; 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal non-Zeno and approximation option %x in simulation.\n", 
      sr->status & MASK_SIM_ZENO_CYCLE
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
  fprintf(RED_OUT, "\n==[Report of a %s-checking]============\n", sim_name); 
  fprintf(RED_OUT, "RED>> Initial state pair diagram: \n"); 
  red_print_graph(sr->initial_state_pair_diagram); 
  switch (sr->status & MASK_SIM_CHECK_RETURN) { 
  case FLAG_RESULT_EARLY_REACHED: 
    ic = sr->iteration_count; 
    fprintf(RED_OUT, 
      "RED>> Early negative %s relation diagram calculated in preset %1d steps\n", 
      sim_name, sr->iteration_count 
    ); 
    fprintf(RED_OUT, "  on denial of any %s relation!\n", sim_name); 
    break; 
  case FLAG_RESULT_FULL_FIXPOINT: 
    ic = sr->iteration_count-1; 
    fprintf(RED_OUT, 
      "RED>> Full negative %s relation diagram calculated in %1d steps:\n", 
      sim_name, sr->iteration_count 
    ); 
    break; 
  case FLAG_RESULT_DEPTH_BOUND_FINISHED: 
    ic = sr->iteration_count-1; 
    fprintf(RED_OUT, 
      "RED>> Bounded negative %s relation diagram calculated in preset %1d steps:\n", 
      sim_name, sr->iteration_count 
    ); 
    break; 
  }
  red_print_graph(sr->final_neg_sim_relation_diagram); 
  if (sr->status & FLAG_COUNTER_EXAMPLE_GENERATED) { 
    fprintf(RED_OUT, "The diagram for state pairs removed in the steps: \n"); 
    for (i = 1; i <= ic; i++) { 
      fprintf(RED_OUT, "----<Step %1d: state pairs removed>------------\n", i); 
      red_print_graph(sr->iteratively_removed_diagram[i]); 
    } 
    if (sr->counter_example_tree != NULL) { 
      fprintf(RED_OUT, "Counter example tree:\n"); 
      print_counter_example_tree(sr->counter_example_tree); 
    }
  } 

  fprintf(RED_OUT, "RED>> Task:"); 
  for (i = 1; i < red_argc(); i++) { 
    fprintf(RED_OUT, " %s", red_argv()[i]); 
  } 
  fprintf(RED_OUT, "\n"); 
  switch (sr->status & MASK_BRANCHING_SIM_RESULT) {
  case FLAG_BRANCHING_SIM_UNDECIDED: 
    fprintf(RED_OUT, "RED>> %s%sbranching %s undecided.\n", 
      app_name, nz_name, sim_name   
    ); 
    break; 
  case FLAG_NO_BRANCHING_SIM: 
    fprintf(RED_OUT, "RED>> No %s%sbranching %s!\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_BRANCHING_SIM_INCONCLUSIVE: 
    fprintf(RED_OUT, "RED>> %s%sbranching %s inconclusive.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_A_BRANCHING_SIM_EXISTS: 
    fprintf(RED_OUT, "RED>> A %s%sbranching %s exists.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Illegal %s%sbranching %s result value %x.\n", 
      app_name, nz_name, sim_name, 
      sr->status & MASK_BRANCHING_SIM_RESULT
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  switch (sr->status & MASK_FAIR_SIM_RESULT) {
  case FLAG_FAIR_SIM_UNDECIDED: 
/*
    fprintf(RED_OUT, "RED>> %s%sfair %s undecided.\n", 
      app_name, nz_name, sim_name   
    ); 
*/
    break; 
  case FLAG_NO_FAIR_SIM: 
    fprintf(RED_OUT, "RED>> No %s%sfair %s!\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_FAIR_SIM_INCONCLUSIVE: 
    fprintf(RED_OUT, "RED>> %s%sfair %s inconclusive.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  case FLAG_A_FAIR_SIM_EXISTS: 
    fprintf(RED_OUT, "RED>> A %s%sfair %s exists.\n", 
      app_name, nz_name, sim_name  
    ); 
    break; 
  default: 
    fprintf(RED_OUT, "\nERROR: Illegal %s%sfair %s result value %x.\n", 
      app_name, nz_name, sim_name, 
      sr->status & MASK_FAIR_SIM_RESULT
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }

  fflush(RED_OUT); 

} 
  /* print_sim_check_return() */ 
  
  










