#define STOP_COUNT_EC_ELM	176

extern int 
  count_ec_elm; 
  
extern int
  FLAG_GAME_RSP_ROLE, 
  GAME_NEWLY_REMOVED_IN_LAST_ITR, // for on-the-fly GFP
  GAME_NEWLY_REMOVED_IN_THIS_ITR, // for on-the-fly GFP
  INEQ_XTION_SYNC_BULK[3]; 



extern int	
  GAME_ROLE_INVARIANCE[3], 
  GAME_ROLE_INVARIANCE_SHARED_CONCAVITY[3], 
  GAME_ROLE_INITIAL[3], 
  XI_ROLE_SYNC_BULK[3]; 
  
extern struct ps_exp_type 
  *GAME_MODL_EXP, *GAME_SPEC_EXP, *GAME_ENVR_EXP, 
  *GAME_FAIRNESS_EXP, *GAME_FAIRNESS_EXP_AUX; 

extern char 
  *role_name(int), 
  *sxi_string(int); 

extern struct red_type	
  *RED_EC_XI_SYNC_BULK, 
  *RED_EC_XI_DSCR_SYNC_BULK, 
  *RED_EC_XI_SPEC_SYNC_BULK, 
  *RED_PLANTS_ENVR_INVARIANCE, 

  *RED_GAME_SYNC_BULK_PRE, 
  *RED_GAME_SYNC_ALL_PRE, 
  **RED_GAME_SYNC_NEG_PRE,  
  **RED_GAME_INV_DIFF,  

  *red_ec_eliminate_type_roles( 
    struct red_type *, 
    int, 
    int
  ), 
  *red_game_invariance(), 
  *red_ec_eliminate_roles(
    struct red_type *, 
    int 
  ), 
  *red_ec_role_nullify(), 
  *red_ec_xi_restrictions(),
  *red_MODL_SPEC_write_consistency(), 
  *red_ec_risk(), 
  *red_game_eliminate_roles(), 
  *red_game_eliminate_opponent(), 
  *red_one_ec_strongest_postcondition_sync_bulk(), 
  *red_test_bisim(); 


extern struct sim_check_return_type 
  *red_simulation_check(), 
  *red_bisimulation_check(); 
   
extern int 
  write_through_to_roles_in_statement(); 
  
extern void
  init_ec_management(), 
  construct_bisim_structures_for_a_role_spec(); 
  

