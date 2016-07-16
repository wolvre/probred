struct hash_hrd_exp_link_type { 
  struct hrd_exp_type		*hrd_exp; 
  struct hash_hrd_exp_link_type	*next_hash_hrd_exp_link; 
}; 

#define SIZE_HASH_SHARED_HRD_EXPS	(0x20000)
#define LEHGTH_SHIFT_SHARED_HRD_EXPS	2 
#define MASK_HASH_SHARED_HRD_EXPS	(0x1FFFF) 

struct hash_hrd_exp_type { 
  int				count; 
  struct hash_hrd_exp_link_type	*hrd_exp_list; 
}; 

struct hash_red_link_type { 
  struct red_type		*diagram; 
  struct hash_red_link_type	*next_hash_red_link; 
}; 
     
#define SIZE_HASH_SHARED_DIAGRAMS	(0x100000) 
#define LEHGTH_SHIFT_SHARED_DIAGRAMS	2 
#define MASK_HASH_SHARED_DIAGRAMS	(0x0FFFFF) 

struct hash_share_type { 
  int				count;  
  struct hash_red_link_type	*shared_list; 
}; 




/********************************************************************8
 * for cache1
 */
#define SIZE_HASH_CACHE1	(0x100000) 
#define LENGTH_SHIFT_CACHE1	2
#define MASK_HASH_CACHE1	(0x0FFFFF)  

struct cache1_hash_entry_type { 
  int				op; 
  struct red_type		*d, *result; 
  struct cache1_hash_entry_type	*next_cache1_hash_entry; 
}; 

struct cache1_hash_type { 
  int				count_entry_used; 
  struct cache1_hash_entry_type	*cache; 
}; // [SIZE_HASH_CACHE1]; 




/********************************************************************8
 * for cache2
 */
#define SIZE_HASH_CACHE2	(0x1000000)
#define LEHGTH_SHIFT_CACHE2	2
#define	MASK_HASH_CACHE2	(0x0FFFFFF) 

struct cache2_hash_entry_type { 
  int				op; 
  struct red_type		*d1, *d2, *result; 
  struct cache2_hash_entry_type	*next_cache2_hash_entry; 
}; 
     
struct cache2_hash_type { 
  int				count_entry_used; 
  struct cache2_hash_entry_type	*cache; //[SIZE_HASH_CACHE2]; 
}; 
     


/********************************************************************8
 * for cache4
 */
#define SIZE_HASH_CACHE4	(0x0100000)
#define LEHGTH_SHIFT_CACHE4	2
#define	MASK_HASH_CACHE4	(0x00FFFFF) 

struct cache4_hash_entry_type { 
  int				op, bn0, bd0; 
  struct red_type		*d, *result; 
  struct hrd_exp_type		*hr0; 
  struct cache4_hash_entry_type	*next_cache4_hash_entry; 
}; 
     
struct cache4_hash_type { 
  int				count_entry_used; 
  struct cache4_hash_entry_type	*cache; //[SIZE_HASH_CACHE2]; 
}; 
     


/********************************************************************8
 * for cache7
 */
#define SIZE_HASH_CACHE7	(0x010000)
#define LEHGTH_SHIFT_CACHE7	2
#define	MASK_HASH_CACHE7	(0x00FFFF) 

struct cache7_hash_entry_type { 
  int				op, bn0, bd0, bn1, bd1; 
  struct red_type		*d, *result; 
  struct hrd_exp_type		*hr0, *hr1; 
  struct cache7_hash_entry_type	*next_cache7_hash_entry; 
}; 
     
struct cache7_hash_type { 
  int				count_entry_used; 
  struct cache7_hash_entry_type	*cache; //[SIZE_HASH_CACHE7]; 
}; 



/********************************************************************8
 * for cache10
 */
#define SIZE_HASH_CACHE10	(0x010000)
#define LEHGTH_SHIFT_CACHE10	2
#define	MASK_HASH_CACHE10	(0x00FFFF) 

struct cache10_hash_entry_type { 
  int					op, bn0, bd0, bn1, bd1, bn2, bd2; 
  struct red_type			*d, *result; 
  struct hrd_exp_type			*hr0, *hr1, *hr2; 
  struct cache10_hash_entry_type	*next_cache10_hash_entry; 
}; 
     
struct cache10_hash_type { 
  int					count_entry_used; 
  struct cache10_hash_entry_type	*cache; //[SIZE_HASH_CACHE10]; 
}; 



/********************************************************************8
 * for cache13
 */
#define SIZE_HASH_CACHE13	(0x010000)
#define LEHGTH_SHIFT_CACHE13	2
#define	MASK_HASH_CACHE13	(0x00FFFF) 

struct cache13_hash_entry_type { 
  int					op, 
					bn0, bd0, bn1, bd1, 
					bn2, bd2, bn3, bd3; 
  struct red_type			*d, *result; 
  struct hrd_exp_type			*hr0, *hr1, *hr2, *hr3; 
  struct cache13_hash_entry_type	*next_cache13_hash_entry; 
}; 
     
struct cache13_hash_type { 
  int					count_entry_used; 
  struct cache13_hash_entry_type	*cache; //[SIZE_HASH_CACHE13]; 
}; 



/***************************************************
 *  for token based garbage protection. 
 */
#define	FLAG_TOKEN_PROTECTED_NOT_YET		-1 
#define FLAG_TOKEN_PROTECTION_NOT_NECESSARY	-2 

struct token_protection_type { 
  int				token; 
  struct red_link_type		*protection_list; 
  struct token_protection_type	*next_token_protection; 
}; 


/*************************************************************
 */
#define	MASK_GC_STAGES		(0xF) 
#define	FLAG_GC_INITIAL		(0x1)
#define	FLAG_GC_PARSING		(0x2)
#define	FLAG_GC_ANALYSIS	(0x3) 

#define	MASK_GC_REPORT		(0xF0)
#define	FLAG_GC_REPORT		(0x10) 
#define	FLAG_GC_SILENT		(0x00)



/* Some additional operator for cache sharing. 
 */ 
/* These are the operator constant used in redbop.c. 
 * 
 *   between [1000, 1999]
 */ 
/* for d=(op,d,i) */ 
#define	OP_VARIABLE_ELIMINATE		1001
#define	OP_VARIABLE_SIM_ELIMINATE	1002
#define	OP_TIME_CLOCK_SIM_ELIMINATE	1003

/* for void(op,d,i,i,i) */
#define OP_REGISTER_RED_READ		1004

/* for i=(op,d) */
#define OP_QUERY_SIZE			1005
#define	OP_ORDER_CHECK			1006 




/***************************************************
 * The following are the operator constant used in mtred.c
 *  between [2000, 2999] 
 */
#define	OP_MT_MINMAX			2001
#define	OP_MT_THRESHOLD			2002
#define OP_MT_ABS			2003 
#define	OP_MT_APPLY_CONST		2004
#define OP_MT_ABSTRACT			2005
#define OP_MT_MATRIX_MULTIPLY_TAIL	2006
#define	OP_MT_MATRIX_MULTIPLY_MATCH	2007
#define	OP_MT_MATRIX_MULTIPLY		2008
#define	OP_MT_ADD			2009
#define	OP_MT_MULTIPLY			2010

/***********************************************************
 * The following are the operator constant used in fxp.c. 
 * between [3000,3999].  
 *
 */
#define OP_ELIMINATE_PROC_QFD_SYNC	3001
#define	OP_ELIMINATE_ALL_QFD_SYNC	3002
#define	OP_GET_PROCESS_FIRABLE_XTIONS	3003
#define	OP_GET_ALL_FIRABLE_XTIONS	3004
#define	OP_EXTRACT_NO_UPPERBOUND	3005


/***********************************************************
 * The following are the operator constant used in redparse.c. 
 * between [4000,4999].  
 *
 */
#define	OP_INDIRECT_REFERENCE			4001
#define OP_GET_EVENT_XTIONS			4002
#define	OP_ADD_EVENT_COUNTS_FROM_XTIONS		4003
#define	OP_IDENTIFY_UNIQUE_ZONE			4004
#define	OP_MODE_INVARIANCE_ANALYZE		4005
#define	OP_SPEC_PROCESS				4006
#define	OP_ADD_NECESSARY_LOWERBOUND		4007
#define	OP_ADD_SYNC_PROC_HOLDERS		4008
#define	OP_REPLACE_SYNC_PROC_HOLDERS		4009
#define	OP_REMOVE_INTRIGGERABLE_SYNC_XTIONS	4010
#define	OP_PARTY_COUNT				4011
#define	OP_SYNC_PARTY_COUNT			4012
#define	OP_ELIMINATE_SIMPLE_QFD_SYNC		4013
#define	OP_EVENT_PATH_EVALUATE			4014
#define	OP_BIG_TIMING_CONSTANT_IN_CRD		4015



/***********************************************************
 * The following are the operator constant used in redbop.c. 
 * between [5000,5999].  
 *
 */
#define	OP_SIZE_SPACE				5001
#define OP_UNTIMED_SUBTRACT			5002
#define OP_ZONE_SUBTRACT			5003
#define	OP_DDD_ONE_CONSTRAINT			5004
#define	OP_DDD_PROJECT_THROUGH_ONE_CONSTRAINT	5005
#define	OP_COMPLEMENT				5006
#define	OP_ZONE_COMPLEMENT			5007
#define	OP_SUPER_INTERSECT_UNTIMED		5008
#define	OP_SUPER_INTERSECT			5009
#define	OP_EXCLUDE_WITH_REDUCTION		5010
#define	OP_DDD_ONE_PROJECT_CONSTRAINT		5011
#define	OP_ASSIGN_INTERVAL			5012
#define	OP_ASSIGN_INTERVAL_DOUBLE		5013
#define	OP_HYBRID_ASSIGN_BOUND			5014
#define	OP_TYPE_ELIMINATE			5015
#define	OP_PI_TYPE_ELIMINATE			5016
#define	OP_SWITCH_PRIMED_AND_UMPRIMED		5017
#define	OP_LIFT_ALL_UMPRIMED			5018
#define	OP_LOWER_ALL_PRIMED			5019
#define	OP_LOCAL_ELIMINATE			5020
#define	OP_SYNC_PLACE_ELIMINATE			5021
#define	OP_QSYNC_ELIMINATE			5022
#define	OP_PI_ELIMINATE				5023
#define	OP_ALL_TRIGGER				5024
#define	OP_TIME_INACTIVE			5025
#define	OP_TIME_ELIMINATE			5026
#define	OP_NONMODAL_CLOCK_ELIMINATE		5027
#define	OP_TIME_CLOCK_ELIMINATE			5028
#define	OP_DIAGONAL_ELIMINATE			5029
#define	OP_TIME_CLOCK_ELIMINATE_REPLACE		5030
#define	OP_TIME_CLOCK_INC			5031
#define	OP_DETECT				5032
#define	OP_INC					5033
#define	OP_INC_MOD				5034
#define	OP_SWITCH_VI				5035
#define	OP_PI_PERMUTE				5036
#define OP_CDD					5037
#define OP_BOTTOM_ORDERING 			5038
#define OP_BACK_TO_ORIGINAL_ORDERING		5039
#define	OP_MODE_ZERO_DISTANCE			5040
#define	OP_CHECK_ABNORMAL_XTION_INSTANCE	5041
#define	OP_VOLUME_CDD				5042
#define	OP_TRIGGER_XTION_COUNT			5043
#define	OP_PATH_COUNT				5044
#define	OP_VARIABLE_OCCURRENCE_CHECK		5045
#define	OP_TRIGGER_TO_BE_ABSTRACTED		5046
#define	OP_TRIGGER_ABSTRACTION			5047
#define	OP_ELIMINATE_MAGNITUDE			5048
#define	OP_ZONE_ASSIGN_BOUND			5049
#define	OP_PROC_ELIMINATE			5050
#define	OP_PEER_ELIMINATE			5051
#define	OP_INACTIVE_CLOCK_TIGHT_MAGNITUDES_DOWNWARD	5052
#define OP_TIME_UPPERBOUNDED			5053 
#define	OP_DISCRETE_MODEL_COUNT			5054

#define OP_VAR_ABSENCE				5055
#define OP_VAR_PRESENCE				5056

#define	OP_ROLE_TYPE_ELIMINATE			5057

#define	OP_PATH_THRESHOLD			5058

#define	OP_DDD_ONE_CONSTRAINT_DOUBLE		5059 

#define OP_SPACE_SUBTRACT			5060 



 
/***********************************************************
 * The following are the operator constant used in action.c. 
 * between [6000,6999].  
 *
 */
#define	OP_EFFECT_SIMPLE		6001
#define	OP_TIME_CLOCK_MAGNITUDE_INC	6002
#define	OP_CLOCK_ASSIGN_BCK		6003
#define OP_CHANGE_LHS_TO_VIVALUE	6004

/***********************************************************
 * The following are the operator constant used in bisim.c. 
 * between [7000,7999].  
 *
 */
#define	OP_ROLE_IN_RED				7001
#define	OP_ELIMINATE_ILLEGAL_DESCRIPTION_SPECIFICATION_READ_WRITES \
						7002
#define	OP_GAME_AUTO_PARTY			7003
#define	OP_GAME_ROLE_NULLIFY			7004
#define	OP_GAME_ELIMINATE_ROLES			7005
#define	OP_GAME_ELIMINATE_TYPE_ROLES		7006
#define	OP_GAME_ELIMINATE_GLOBAL_WRITE		7007
#define OP_ELIMINATE_ROLE_AND_SINGLE_PLANT	7008
#define	OP_GAME_EXTRACT_ROLE_UNBOUNDED		7009
#define	OP_COUNT_PATH_DEPTH			7010


/***********************************************************
 * The following are the operator constant used in access_analysis.c. 
 * between [8000,8999].  
 *
 */
#define	OP_FILTER_ROLE_WRITES			8001
#define	OP_DSCR_SPEC_WRITE_SYNCHRONIZATIONS	8002
#define	OP_ELIMINATE_SINGLE_PARTY		8003



/***********************************************************
 * The following are the operator constant used in redsymmetry.c. 
 * between [9000,9999].  
 *
 */
#define	OP_SYMMETRY_POINTER_FIXPOINT_ONLINE_FANOUT_ONEPAIR	9001
#define	OP_ZONE_ONE_PAIR_REVERSE				9002
#define	OP_CLOCK_DEPENDENT					9005



/***********************************************************
 * The following are the operator constant used in inactive.c. 
 * between [10000,10999].  
 *
 */
#define	OP_ACTIVE_VARIABLE_GLOBAL_UNTIMED_EXTRACT	10001
#define	OP_ACTIVE_CLOCK_SUPPORT_EXTRACT			10002
#define	OP_ACTIVE_GLOBAL_UNTIMED_EXTRACT		10003
#define	OP_ACTIVE_GLOBAL_LOCAL_UNTIMED_EXTRACT		10004
#define	OP_ACTIVE_VARIABLE_SUPPORT_EXTRACT		10005
#define	OP_ACTIVE_UNTIMED_EXTRACT			10006
#define	OP_ELIMINATE_PEERS				10007
#define	OP_TIMED_INVARIANCE_BOUNDS			10008
#define	OP_VARIABLE_ACTIVE				10009
#define	OP_CHECK_NOT_TYPE_III				10010
#define	OP_COLLECT_RED_TIMED_CONSTANT_EXCLUSION		10011



/***********************************************************
 * The following are the operator constant used in inactive.c. 
 * between [11000,11999].  
 *
 */
#define	OP_ZONE_INTERSECT			11001
#define	OP_PATH_ELIMINATE			11002
#define	OP_EXTRACT_INTERVAL			11003
#define	OP_SUBTRACT_INTERVAL			11004
#define	OP_CLOCK_UPPER_EXTEND			11005
#define	OP_CLOCK_UPPER_DELTAP			11006
#define	OP_CLOCK_LOWER_EXTEND			11007
#define	OP_CLOCK_LOWER_DELTAP			11008
#define	OP_CLOCK_NOXTIVE_LOWER_EXTEND		11009
#define	OP_ELIMINATE_SIMPLE_NEGATIVE_CYCLES	11010
#define	OP_BYPASS_DOWNWARD_MATCHING_LEFT	11011
#define	OP_BYPASS_DOWNWARD_MATCHING_RIGHT	11012
#define	OP_BYPASS_GIVEN_LEFT_DOWNWARD		11013
#define	OP_BYPASS_GIVEN_RIGHT_DOWNWARD		11014
#define	OP_BYPASS_DOWNWARD			11015
#define	OP_TIGHT_MAGNITUDES_FROM_ZERO_DOWNWARD	11016
#define	OP_TIGHT_MAGNITUDES_TO_ZERO_DOWNWARD	11017
#define	OP_TIGHT_MAGNITUDES_DOWNWARD_THROUGH_MAGNITUDES	11018
#define	OP_TIGHT_DIFFERENCES_FROM_ZERO_DOWNWARD	11019
#define	OP_TIGHT_DIFFERENCES_TO_ZERO_DOWNWARD	11020
#define	OP_TIGHT_DIFFERENCES_DOWNWRAD_THROUGH_MAGNITUDES	11021
#define	OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_FROM_ZERO_DOWNWARD	11022
#define	OP_INACTIVE_CLOCK_TIGHT_MAGNITUDE_TO_ZERO_DOWNWARD	11023
#define	OP_ELIMINATE_ONE_GROUP_MAGNITUDE_REDUNDANCY_DOWNWARD	11024
#define	OP_ELIMINATE_MAGNITUDE_REDUDANCY_DOWNWARD		11025
#define	OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_RIGHT_DOWNWARD	11026
#define	OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_GIVEN_LEFT_DOWNWARD	11027
#define	OP_ELIMINATE_MAGNITUDE_REDUNDANT_DIFFERENCES_DOWNWARD	11028
#define	OP_PUSH_BIG_TIMING_CONSTANT		11029
#define	OP_SUBSUME				11030
#define	OP_ZONE_SUBSUME				11031
#define	OP_TIME_PROGRESS_BY_AMOUNT		11032
#define	OP_CHECK_DISCONTINUITY_LOW_PRECISION	11033
#define	OP_CHECK_TIME_DISCONTINUITY		11034
#define	OP_DISCRETE_STACK_EXTRACT		11035
#define	OP_INVARIANCE_DISCONTINUITY		11036
#define	OP_LUB_EXTRAPOLATE			11037
#define	OP_LUB_EXTRAPOLATE_GIVEN_RIGHT		11038


/***********************************************************
 * The following are the operator constant used in zapprox.c. 
 * between [12000,12999].  
 *
 */
#define	OP_HULL_FILTER					12001
#define	OP_ONE_CONVEX_HULL				12002
#define	OP_ZONE_CONVEX_HULL				12003
#define	OP_UNION_FILTER					12004
#define	OP_ABSTRACTION_GAME_BASED_INSIG			12005
#define	OP_ABSTRACTON_GAME_BASED_INSIG_DISCRETE		12006
#define	OP_ABSTRACTON_GAME_BASED_INSIG_TIME		12007
#define	OP_ABSTRACTION_GAME_BASED_INSIG_MAGNITUDE	12008
#define	OP_ABS_GAME					12009



/***********************************************************
 * The following are the operator constant used in hybrid.c. 
 * between [13000,13999].  
 *
 */
#define	OP_HYBRID_ADD_PRIMED_CONSTRAINTS		13001
#define	OP_HYBRID_ELIMINATE				13002
#define	OP_HYBRID_EXTRACT_LOWERHALF			13003
#define	OP_HYBRID_EXTRACT_UPPERHALF			13004
#define	OP_HYBRID_SUBTRACT_UPPERHALF			13005
#define	OP_HYBRID_ELIMINATE_RELATIVE			13006
#define	OP_HYBRID_ELIMINATE_SIMPLE_NEGATIVE_CYCLES	13007
#define	OP_HYBRID_BYPASS_GIVEN_DOWNWARD			13008
#define	OP_HYBRID_BYPASS_DOWNWARD			13009
#define	OP_HYBRID_BYPASS_GIVEN_DOWNWARD_FOR_PRIMED	13010
#define	OP_HYBRID_BYPASS_DOWNWARD_FOR_PRIMED		13011
#define	OP_HYBRID_SPECIFIC_CONSTANT_REPLACE		13012
#define	OP_HYBRID_CONSTANT_REPLACE			13013
#define	OP_HYBRID_RELATIVE_ELIMINATE			13014
#define	OP_HYBRID_TIME_CROSS_GIVEN			13015
#define	OP_HYBRID_REPLACE				13016
#define	OP_HYBRID_GIVEN_PRIMED_REPLACE			13017
#define	OP_HYBRID_DELTA_EXTEND				13018
#define	OP_HYBRID_DELTA_TRANSITIVITY_FOR_UMPRIMED_VARIABLES	13019
#define	OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENXY_DOWNWARD	13020
#define OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENX_DOWNWARD	13021
#define	OP_HYBRID_ELIMINATE_INCONSISTENCY_DOWNWARD	13022
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXY_DOWNWARD	13023
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD	13024
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_DOWNWARD	13025
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED	13026
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_DOWNWARD_FOR_PRIMED	13027
#define OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXZ_LOOKAHEAD	13028
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_LOOKAHEAD	13029
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_LOOKAHEAD	13030
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD	13031
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD	13032
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD		13033
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD		13034
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_FOR_PRIMED	13035
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED	13036
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_FOR_PRIMED	13037
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE	13038
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE	13039
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE	13040
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED \
								13041
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED	13042
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE	13043
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE	13044
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE	13045
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE	13046
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE_FOR_PRIMED \
								13047
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE_FOR_PRIMED \
								13048
#define	OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_COLLECTIVE_FOR_PRIMED	13049
#define	OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZU_DOWNWARD_COLLECTIVE	13050
#define	OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZ_DOWNWARD_COLLECTIVE	13051
#define	OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENXY_DOWNWARD_COLLECTIVE	13052
#define	OP_HYBRID_ELIMINATE_4REDUNDANCY_GIVENX_DOWNWARD_COLLECTIVE	13053
#define	OP_HYBRID_ELIMINATE_4REDUNDANCY_DOWNWARD_COLLECTIVE		13054
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENXZ_LOOKAHEAD_COLLECTIVE	13055
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_GIVENX_LOOKAHEAD_COLLECTIVE	13056
#define	OP_HYBRID_ELIMINATE_2REDUNDANCY_LOOKAHEAD_COLLECTIVE	13057
#define	OP_HYBRID_EXTRACT_BOUND_REDUNDANCY_COLLECTIVE		13058
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_TARGET_COLLECTIVE	13059
#define	OP_HYBRID_ELIMINATE_REDUNDANCY_COLLECTIVE		13060
#define	OP_HYBRID_CHECK_LONG					13063
#define	OP_HYBRID_EXTRACT_LONG					13064
#define	OP_COLLECT_PROOF_OBLIGATIONS				13066
#define	OP_HYBRID_PROOF_OBLIGATION_GIVENX			13067
#define	OP_HYBRID_PROOF_OBLIGATION				13068
#define	OP_HYBRID_ABSTRACT_PRECISION			13069
#define OP_HYBRID_DELTA_EXPRESSION			13070
#define	OP_HYBRID_DELTA_EXPRESSION_INACTIVE_CHANGE_BACK	13071
#define	OP_HYBRID_COLLECT_ALL_PRIMED			13072
#define	OP_HYBRID_PARAMETER_EXTRACT			13073
#define	OP_HYBRID_REMOVE_ALL_DISCRETES			13074
#define	OP_HDD_ONE_CONSTRAINT_ASCENDING			13075
#define	OP_HYBRID_ABSTRACT_MAGNITUDE			13076

#define	OP_HYBRID_EXACT_CONSTANT_REDUCE			13077
#define	OP_HYBRID_GIVEN_EXACT_CONSTANT_REDUCE		13078

/***********************************************************
 * The following are the operator constant used in zone.c. 
 * between [14000,14999].  
 *
 */
 
#define	OP_TIME_PROGRESS				(0x14010)
#define	OP_TIME_PROGRESS_ALL	\
	((0x14010)|MASK_GAME_ROLES)
#define	OP_TIME_PROGRESS_SPEC	\
	((0x14010)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define	OP_TIME_PROGRESS_MODL	\
	((0x14010)|FLAG_GAME_MODL|FLAG_GAME_ENVR)

#define OP_TIME_PATH_ASSUMED_CONVEXITY			(0x14110) 
#define OP_TIME_PATH_ASSUMED_CONVEXITY_ALL	\
	((0x14110)|MASK_GAME_ROLES) 
#define OP_TIME_PATH_ASSUMED_CONVEXITY_SPEC	\
	((0x14110)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define OP_TIME_PATH_ASSUMED_CONVEXITY_MODL	\
	((0x14110)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 

#define OP_TIME_PATH_FULL_FORMULATION			(0x14120) 
#define OP_TIME_PATH_FULL_FORMULATION_ALL	\
	((0x14120)|MASK_GAME_ROLES) 
#define OP_TIME_PATH_FULL_FORMULATION_SPEC	\
	((0x14120)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define OP_TIME_PATH_FULL_FORMULATION_MODL	\
	((0x14120)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 

/* This is obsolete.
#define	OP_TIME_PATH_SHARED_CONCAVITY			(0x14130)
#define	OP_TIME_PATH_SHARED_CONCAVITY_ALL	\
	((0x14130)|MASK_GAME_ROLES)
#define	OP_TIME_PATH_SHARED_CONCAVITY_SPEC	\
	((0x14130)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define	OP_TIME_PATH_SHARED_CONCAVITY_MODL	\
	((0x14130)|FLAG_GAME_MODL|FLAG_GAME_ENVR)
*/

#define	OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY		(0x14140)
#define	OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_ALL	\
	((0x14140)|MASK_GAME_ROLES)
#define	OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_SPEC	\
	((0x14140)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define	OP_TIME_PATH_ADAPTIVE_SHARED_CONCAVITY_MODL	\
	((0x14140)|FLAG_GAME_MODL|FLAG_GAME_ENVR)

/* These are obsolete. 
#define	OP_TIME_PATH_SPLIT_CONVEXITIES			(0x14150) 
#define	OP_TIME_PATH_SPLIT_CONVEXITIES_ALL	\
	((0x14150)|MASK_GAME_ROLES) 
#define	OP_TIME_PATH_SPLIT_CONVEXITIES_SPEC	\
	((0x14150)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define	OP_TIME_PATH_SPLIT_CONVEXITIES_MODL	\
	((0x14150)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 

#define	OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES		(0x14160)	
#define	OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_ALL	\
	((0x14160)|MASK_GAME_ROLES)	
#define	OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_SPEC	\
	((0x14160)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define	OP_TIME_PATH_SHARED_SPLIT_CONVEXITIES_MODL	\
	((0x14160)|FLAG_GAME_MODL|FLAG_GAME_ENVR)
*/ 

#define OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES 	(0x14170)
#define OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_ALL	\
 	((0x14170)|MASK_GAME_ROLES)
#define OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_SPEC	\
 	((0x14170)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define OP_TIME_PATH_ADAPTIVE_SHARED_SPLIT_CONVEXITIES_MODL	\
 	((0x14170)|FLAG_GAME_MODL|FLAG_GAME_ENVR)
/* These are obsolete. 
#define OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES 	(0x14180)
#define OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_ALL	\
 	((0x14180)|MASK_GAME_ROLES)
#define OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_SPEC	\
 	((0x14180)|FLAG_GAME_SPEC|FLAG_GAME_ENVR)
#define OP_TIME_PATH_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES_MODL	\
 	((0x14180)|FLAG_GAME_MODL|FLAG_GAME_ENVR)

#define OP_TIME_PATH_EASY_CONCAVITY				(0x14190) 
#define OP_TIME_PATH_EASY_CONCAVITY_ALL	\
	((0x14190)|MASK_GAME_ROLES) 
#define OP_TIME_PATH_EASY_CONCAVITY_SPEC	\
	((0x14190)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define OP_TIME_PATH_EASY_CONCAVITY_MODL	\
	((0x14190)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 

#define OP_TIME_PATH_SHARED_EASY_CONCAVITY			(0x141A0) 
#define OP_TIME_PATH_SHARED_EASY_CONCAVITY_ALL	\
	((0x141A0)|MASK_GAME_ROLES) 
#define OP_TIME_PATH_SHARED_EASY_CONCAVITY_SPEC	\
	((0x141A0)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define OP_TIME_PATH_SHARED_EASY_CONCAVITY_MODL	\
	((0x141A0)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 
*/ 
#define OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY	(0x141B0) 
#define OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_ALL	\
	((0x141B0)|MASK_GAME_ROLES) 
#define OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_SPEC	\
	((0x141B0)|FLAG_GAME_SPEC|FLAG_GAME_ENVR) 
#define OP_TIME_PATH_ADAPTIVE_SHARED_EASY_CONCAVITY_MODL	\
	((0x141B0)|FLAG_GAME_MODL|FLAG_GAME_ENVR) 

#define	OP_REDUCE_EQ			(0x14200) 
#define	OP_REDUCE_EQ_REMOVE_CLOCK	(0x14201) 
#define	OP_MERGE_ZONES			(0x14202) 

/***********************************************************
 * The following are the operator constant used in redbasics.c. 
 * between [15000,15999].  
 *
 */
#define	OP_CONJUNCT_ROLE_PRECONDITION			15001
#define OP_ROLE_DEADLOCK				15002
#define	OP_ROLE_SIMPLE_ZENO				15003



/***********************************************************
 * The following are the operator constant used in redgame.c. 
 * between [16000,16999].  
 *
 */
#define	OP_ADD_ROLE_EVENTS				16001
#define	OP_INEQ_UNIVERSE				16002
#define	OP_INEQ_UNIVERSE_SYNC_ITERATIVE			16003
#define	OP_INEQ_UNIVERSE_LONG_DEST_WITH_UAPPROX		16004 
#define	OP_ROLE_FAIRNESS_BCK				16005

#define	OP_GAME_FORCED_ONE_STRONG_FAIRNESS		16006

/***********************************************************
 * The following are the operator constant used in redgame.c. 
 * between [17000,17999].  
 *
 */
#define	OP_VI_IN_EXP_POSSIBLY				17001
#define	OP_VI_SIM_IN_EXP				17002
#define	OP_CLOCK_SIM_IN_EXP				17003
#define	OP_TYPE_IN_EXP					17004
#define	OP_TIME_IN_EXP					17005
#define	OP_QSYNC_IN_EXP					17006
#define	OP_CLOCK_IN_EXP					17007
#define	OP_PEER_IN_EXP					17008
#define	OP_LOCAL_IN_EXP					17009
#define	OP_PROC_AND_GLOBAL_IN_EXP			17010
#define	OP_MCHUNK_IN_EXP				17011


/***********************************************************
 * The following are the operator constant used in redstream.c. 
 * between [18000,18999].  
 *
 */
#define	OP_STREAM_INPUT_FROM_BUFFER			18001
#define	OP_STREAM_OUTPUT_TO_BUFFER			18002
#define	OP_HEAP_MALLOC					18003 
#define	OP_HEAP_FREE					18004

/*************************************************************
 * The following are the operator constant used in exp.c. 
 * between [19000,19999].  
 *
 */
#define	OP_EXTRACT_VARIABLE_VALUES			19001



// The following constants are for the stack management to 
// escape from garbage collection. 
// 
#define	INDEX_FALSE				0
#define	INDEX_TRUE 				1

#define DECLARED_GLOBAL_INVARIANCE 		2
#define INDEX_INITIAL				3
#define	INDEX_GOAL 				4
#define INDEX_ZENO_FROM_DESCRIPTION		5
#define INDEX_NONZENO_FROM_DESCRIPTION		6
#define	INDEX_URGENT				7 

#define	INDEX_DEADLOCK				8 
#define	INDEX_ZENO				9
#define INDEX_MODE_CONCAVITY			10 
#define INDEX_MODE_CONVEXITY			11 
#define REFINED_GLOBAL_INVARIANCE		12
#define INDEX_NONZENO_BY_OAPPROX_FAIRNESS	13
#define INDEX_NONZENO_BY_FAIRNESS_TERMINATION	14

#define INDEX_MALLOC_SPACE			15 
#define	XI_SYNC_ALL				16 
#define XI_SYNC_ALL_WITH_POSTCONDITION		17 
#define XI_SYNC_ALL_WITH_TRIGGERS		18

#define OFFSET_WITH_TRIGGERS			2
 
#define XI_SYNC_ALL_WITH_EVENTS			19 

#define OFFSET_WITH_EVENTS			3 

#define XI_SYNC_ALL_WITH_PROC_HOLDERS		20
#define XI_SYNC_ALL_WITH_EVENT_PROC_HOLDERS	21 

#define	XI_SYNC_BULK				22
#define XI_SYNC_BULK_WITH_POSTCONDITION		23
#define XI_SYNC_BULK_WITH_TRIGGERS		24
#define XI_SYNC_BULK_WITH_EVENTS		25

/* These have been moved to the hash table. 
#define INDEX_GAME_FAIRNESS_ALL			23
#define INDEX_GAME_FAIRNESS_MODL		24
#define INDEX_GAME_FAIRNESS_SPEC 		25
*/
 
#define	INDEX_GAME_START 			26 
#define INDEX_GAME_INVARIANCE_WITH_EQUALITIES	INDEX_GAME_START

#define	XI_GAME_SYNC_ALL			27
#define XI_GAME_SYNC_ALL_WITH_POSTCONDITION	28 
#define XI_GAME_SYNC_ALL_WITH_TRIGGERS		29 
#define XI_GAME_SYNC_ALL_WITH_EVENTS		30 
#define XI_GAME_SYNC_ALL_WITH_PROC_HOLDERS	31 // This actually not used 
						  // since we don't know how 
						  // to forbid the synchronization
						  // between SPEC and MODL.  
#define XI_GAME_SYNC_ALL_WITH_EVENT_PROC_HOLDERS	32 

#define	XI_GAME_SYNC_BULK			33
#define XI_GAME_SYNC_BULK_WITH_POSTCONDITION	34
#define XI_GAME_SYNC_BULK_WITH_TRIGGERS		35
#define XI_GAME_SYNC_BULK_WITH_EVENTS		36

#define	XI_GAME_SPEC_SYNC_BULK 			37 
#define	XI_GAME_MODL_SYNC_BULK			38 
  
#define	EC_INVARIANCE_WITH_ONLY_DIAGONAL	39 

#define	INDEX_GAME_SPEC_INVARIANCE		40  
#define	INDEX_GAME_MODL_INVARIANCE		41

#define	INDEX_GAME_SPEC_INITIAL			42  
#define	INDEX_GAME_MODL_INITIAL			43  

#define	XI_RESTRICTION_SPEC_FWD			44  
#define	XI_RESTRICTION_MODL_FWD			45  
#define	INDEX_GAME_STOP				XI_RESTRICTION_MODL_FWD 
  

#define	INDEX_BOTTOM_OF_RUNTIME_STACK		46 















