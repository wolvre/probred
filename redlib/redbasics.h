#include <stdarg.h> 
#include "reddebug.h" 

extern int	CPLUG_IN_W, CPLUG_IN_PI; 

extern int	cplugin_proc(
  int, 	// module index 
  int	// proc index
); 

/* MASK values for GLOBAL_STATUS[0]  */
/* This should be for the generatl system characteristics. 
 */ 

#define	RED_DEBUG_ACTIVE	1
#define	RED_DEBUG_INACTIVE	0

// #define RED_DEBUG_LEX_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_YACC_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_PARSE_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_EXP_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_BASICS_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_ACTION_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_REDBOP_MODE	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_ACCESS_MODE	RED_DEBUG_ACTIVE 


/* The following constants are used for the compile-time 
 * debugging output control. 
 */ 
// #define	RED_DEBUG_FXP_MODE	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_REFINEMENT	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_STATEMENT	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_LABEL	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_FAIRNESS	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_EUNTIL	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_EVENTS	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_MODE_POST_PROC	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_FXP_DEBUG	RED_DEBUG_ACTIVE 


// The compiler control constant for dumping trace information 
// for LIB procedures. 
// #define	RED_DEBUG_LIB_MODE	RED_DEBUG_ACTIVE 


// #define	RED_DEBUG_BISIM_MODE	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_BISIM_MODE_CMR	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_BISIM_MODE_GFP	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_BISIM_MODE_STUTTER	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_GAME_MODE			RED_DEBUG_ACTIVE 
// #define	RED_DEBUG_GAME_MODE_FORCED_PRECOND	RED_DEBUG_ACTIVE 



// #define	RED_DEBUG_INACTIVE_MODE	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_REDSTRING_MODE	RED_DEBUG_ACTIVE 


/* The following constants are used for the compile-time 
 * debugging output control. 
 */ 
// #define	RED_DEBUG_ZONE_MODE	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_ZONE_MODE_NORMALIZE	RED_DEBUG_ACTIVE 

// #define	RED_DEBUG_ZONE_MODE_BYPASS	RED_DEBUG_ACTIVE 

// #define RED_DEBUG_ZONE_MODE_TIME_PROGRESS	RED_DEBUG_ACTIVE

// #define RED_DEBUG_ZONE_MODE_TIME_MEASURE	RED_DEBUG_ACTIVE

// #define RED_DEBUG_ZONE_MODE_TIME_PROGRESS_CONVEX	RED_DEBUG_ACTIVE

// #define	RED_DEBUG_ZAPPROX_MODE	RED_DEBUG_ACTIVE 

/* The following constants are used for the compile-time 
 * debugging output control. 
 */ 
// #define	RED_DEBUG_HYBRID_MODE	RED_DEBUG_ACTIVE 

// #define 	RED_ZONE_BYPASS_HASH	1


#define	RED_MECH_CACHE_STACK	1
#define RED_MECH_CACHE_HASH	2
#define	RED_MECH_CACHE_TREE	3

#define	RED_MECH_CACHE7	RED_MECH_CACHE_STACK 
// #define	RED_MECH_CACHE7	RED_MECH_CACHE_HASH 
// #define	RED_MECH_CACHE7	RED_MECH_CACHE_TREE 

#define	RED_MECH_CACHE4	RED_MECH_CACHE_STACK 
// #define	RED_MECH_CACHE4	RED_MECH_CACHE_HASH 
// #define	RED_MECH_CACHE4	RED_MECH_CACHE_TREE 

// #define RED_REGRESS_CHECKING	RED_DEBUG_ACTIVE 



/*********************************************************************
 */
#define	GSTATUS_SIZE	20 


#define	RED_OPT_SYSTEM_TYPE		93
#define	INDEX_SYSTEM_TYPE		0
#define	MASK_SYSTEM_TYPE		(0x0F)
#define FLAG_SYSTEM_UNTIMED		(0x00)
#define	FLAG_SYSTEM_TIMED		(0x01)
#define FLAG_SYSTEM_HYBRID		(0x02)
#define FLAG_SYSTEM_MTTIMED		(0x04)


#define INDEX_SYNCHRONIZATION		0
#define	RED_OPT_QUANTIFIED_SYNC		170 
#define FLAG_SYSTEM_QUANTIFIED_SYNC	(0x0010)  
#define FLAG_HUGE_SYNC			(0x0020)
#define FLAG_SYNC_ADDRESS_RESRICTION	(0x0040)

#define	RED_OPT_NO_SYNCHRONIZERS	40 
#define	RED_OPT_ALL_SYNC_XTIONS		41
#define	RED_OPT_SYNCHRONIZERS		42 
#define	FLAG_NO_SYNCHRONIZERS		(0x0080)
#define	FLAG_ALL_SYNC_XTIONS		(0x0100)


#define	DEPTH_ENUMERATIVE_DEFAULT	-1 
#define	DEPTH_ENUMERATIVE_ALL		-2

#define	INDEX_GLOBAL_VARIABLE		0
#define FLAG_GLOBAL_VARIABLE		(0x0200)

#define INDEX_POINTER_ARITH		0 
#define FLAG_POINTER_ARITH		(0x0400)

#define	INDEX_BULK_TRIGGER_ACTION_INTERFERE	0
#define	FLAG_BULK_TRIGGER_ACTION_INTERFERE	(0x800)

/* MASK values for GLOBAL_STATUS[1] */ 
/* This should be for the verification tasks. 
 */ 
#define	RED_OPT_TASK			190
#define	MASK_TASK  			(0xFF)
#define	INDEX_TASK			1

#define	TASK_MODEL_CHECK		(0x00)
#define TASK_RISK			(0x01)
#define TASK_GOAL			(0x02)
#define	TASK_SAFETY			(0x03)
#define	TASK_SIMULATE			(0x04)
#define	TASK_ZENO			(0x05)
#define	TASK_DEADLOCK			(0x06)
#define TASK_BRANCHING_BISIM_CHECKING	(0x0A) 
#define TASK_BRANCHING_SIM_CHECKING	(0x0B) 

#define TASK_REDLIB_SESSION		(0x10) 
#define TASK_UNSPECIFIED		(0x11) 


#define	RED_OPT_SPEC			200
#define INDEX_SPEC			1
#define MASK_SPEC			(0xF00)

#define	RED_OPT_SPEC_W_EUNTIL		201 
#define FLAG_SPEC_W_EUNTIL		(0x100)

#define	RED_OPT_SPEC_W_EALWAYS		202
#define FLAG_SPEC_W_EALWAYS		(0x200) 


#define	RED_OPT_PARAMETRIC_ANALYSIS	191 
#define	INDEX_PARAMETRIC_ANALYSIS	1
#define FLAG_PARAMETRIC_ANALYSIS	(0x400)


#define	RED_OPT_INFERENCE_DIRECTION   	20	
#define	RED_OPT_BCK_ANALYSIS	       	21
#define	INDEX_INFERENCE_DIRECTION	1
#define	FLAG_BCK_ANALYSIS		(0x1000) 
#define	FLAG_FWD_ANALYSIS		(0x0000)

#define	INDEX_XTION_INSTANCE		1
#define FLAG_XTION_INSTANCE_MAINTAIN	(0x2000) 
#define	FLAG_XTION_INSTANCE_ELIMINATE	(0x0000) 

#define	IDNEX_MANY_TRANSITIONS			1 
#define FLAG_MANY_TRANSITIONS			(0x004000) 

#define INDEX_PARSE				1
#define FLAG_PARSER_MODEL_DONE			(0x008000) 

#define	MASK_GRAM_PHASE				(0x0F0000) 
#define	GRAM_PHASE_UNKNOWN			(0x000000) 
#define	GRAM_PHASE_WINDOW_SIZE			(0x010000)
#define GRAM_PHASE_PROCESS_COUNT		(0x020000) 
#define GRAM_PHASE_VAR_DECL			(0x030000) 
#define GRAM_PHASE_INLINE_DECL			(0x040000) 
#define GRAM_PHASE_MODE_DECL			(0x050000) 
#define GRAM_PHASE_INITIAL_DECL			(0x060000) 
#define GRAM_PHASE_SPEC_DECL			(0x070000) 
#define	GRAM_PHASE_DEBUG_INFOS			(0x080000) 

#define MASK_MODEL_PROCESSING			(0xF00000)
#define FLAG_MODEL_PARSING_ONLY			(0x000000)
#define	FLAG_MODEL_NO_REFINED_ABSTRACT_SPACE	(0x100000) 
#define	FLAG_MODEL_REFINED_ABSTRACT_SPACE	(0x200000) 

/* MASK values for GLOBAL_STATUS[2] */ 
/* This should be for the variable ordering. 
 */ 
#define	RED_OPT_DISCRETE_DENSE_INTERLEAVING		90 
#define	INDEX_DISCRETE_DENSE_INTERLEAVING		2 
#define INDEX_MATRIX_INTERLEAVING			2 

#define MASK_DISCRETE_DENSE_INTERLEAVING		(0x0000FFFF) /* bits 5-7 is to distinguish between hybrid and timed systems. */
#define MASK_MATRIX_INTERLEAVING			(0x0000FFFF) /* bits 5-7 is to distinguish between hybrid and timed systems. */
#define FLAG_DISCRETE_DENSE_BOTTOM			(0x00000001)
#define FLAG_MATRIX_BOTTOM				(0x00000001)
#define FLAG_DISCRETE_DENSE_HALF_INTERLEAVING		(0x00000002)
#define FLAG_DISCRETE_DENSE_FULL_INTERLEAVING		(0x00000003)
#define FLAG_MATRIX_FULL_INTERLEAVING			(0x00000003)
#define FLAG_MATRIX_TOP					(0x00000004)

#define	RED_OPT_HYBRID_ENCODING				91 

#define	INDEX_HYBRID_ENCODING				2
#define	MASK_HYBRID_ENCODING				(0xFFFF0000)
#define	FLAG_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS	(0x00010000)
#define	FLAG_HYBRID_ENCODING_NORMALIZED_MAGNITUDES	(0x00020000)
#define	FLAG_HYBRID_ENCODING_NORMALIZED_STRING		(0x00030000)



/* GSTATUS[3] */
#define	INDEXX_ZONE_ORDERING				3
#define MASKK_ZONE_ORDERING				(0x00000FFF) 

#define	INDEXX_HYBRID_ORDERING				3
#define	MASKK_HYBRID_ORDERING				(0x00FFF000) 
/*
#define	RED_OPT_HYBRID_ORDERING				92 

#define	INDEX_HYBRID_ORDERING				2
#define MASK_HYBRID_ORDERING				(0x00F00000) 
#define FLAG_HYBRID_ORDERING_BOTTOM			(0x00100000) 
#define FLAG_HYBRID_ORDERING_HALF_INTERLEAVING		(0x00200000) 
#define FLAG_HYBRID_ORDERING_FULL_INTERLEAVING		(0x00300000) 
*/
#define	INDEXX_MATRIX_ENCODING				3
#define MASKK_MATRIX_ENCODING				(0xFF000000)
/*
#define	FLAG_MATRIX_ENCODING_TOP			(0x00000000)
#define FLAG_MATRIX_ENCODING_BOTTOM			(0x01000000)
*/

/*********************************************************************
 *  Constants for normal form options
 */
/* GSTATUS[4] */ 

#define	RED_OPT_NORM_ZONE				220 
#define	INDEX_NORM_ZONE					4

#define	MASK_NORM_ZONE					(0x0000FFFF)
#define	FLAG_NORM_ZONE_NONE				0
#define	FLAG_NORM_ZONE_MAGNITUDE_WITH_ONLY_TABLE_LOOKUP	(0x00000001)
#define	FLAG_NORM_ZONE_CLOSURE				(0x00000002)
#define	FLAG_NORM_ZONE_CLOSURE_EQ			(0x00000003)
#define FLAG_NORM_ZONE_CLOSURE_PROPAGATE		(0x00000004)
#define FLAG_NORM_ZONE_CLOSURE_REDUCTION		(0x00000005)
#define	FLAG_NORM_ZONE_MAGNITUDE			(0x00000006)
#define FLAG_NORM_ZONE_MAGNITUDE_ONE_RIPPLE		(0x00000007)
#define FLAG_NORM_ZONE_REDUCED				(0x00000008)
#define FLAG_NORM_ZONE_MAGNITUDE_REDUCTION		(0x00000009)
#define FLAG_NORM_ZONE_MAGNITUDE_WITH_NO_TABLE_LOOKUP	(0x0000000A)
#define FLAG_NORM_ZONE_2REDUNDANCY_ELIMINATION_DOWNWARD	(0x0000000B)

#define	RED_OPT_NORM_HYBRID					221 
#define	INDEX_NORM_HYBRID					4
#define	MASK_NORM_HYBRID					(0xFFFF0000)
#define FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD	(0x00010000)
#define FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD	(0x00020000)
#define FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD	(0x00040000)
#define FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD	(0x00080000)
#define FLAG_NORM_HYBRID_PROOF_OBLIGATIONS			(0x00100000)


/* All flags to the reachability procedures. 
 * These include the 
     MASK_GAME_ROLES, in 0xF
     FLAG_TIME for time progress, in 0x2000000 
     FLAG_NONZENO for non-Zeno computation in GFP, in 0x4000000
     FLAG_COUNTER_EXAMPLE for counter-examples, in 0x1000000 
     flags for abstractions
 */ 
/* The two least significant bits are for over or under 
 * at the specification level. 
 */ 
/* GSTATUS[5] */ 
#define	RED_OPT_APPROX			10
#define	INDEX_APPROX			5
#define MASK_APPROX			(0xFFFFFFFF)


#define MASK_ROOT_POLARITY		(0xD0000000) 
#define	FLAG_ROOT_NOAPPROX		(0x00000000) // Note this is a zero.
#define	FLAG_ROOT_OAPPROX		(0x40000000) // Note this is positive. 
#define	FLAG_ROOT_UAPPROX		(0x80000000) // Note this is a negative number.

  
// All over-approximations are with flags > FLAG_NOAPPROX.  
// All under-approximations are with flags < FLAG_NOAPPROX. 

#define MASK_OAPPROX_DISCRETE		(0x00100000) 
#define FLAG_NOAPPROX_DISCRETE_LAZY	(0x00000000) 
#define FLAG_OAPPROX_DISCRETE_LAZY	(0x00100000) 


      
/* The following five over approximate representation methods 
 * are mutual exclusive. 
 * Thus they occupy 3 bits. 
 */ 
#define	MASK_OAPPROX				(0xD00FFFFF) 


#define MASK_OAPPROX_STRATEGY			(0xF0000) 
#define FLAG_OAPPROX_STRATEGY_GAME		(0x10000) 

#define MASK_OAPPROX_SPEC_GAME			(0xF000F) 
#define	FLAG_NOAPPROX_SPEC_GAME			(0x10000) 
#define FLAG_OAPPROX_SPEC_GAME_DIAG_MAG		(0x10001)
#define FLAG_OAPPROX_SPEC_GAME_DIAGONAL		(0x10002)
#define FLAG_OAPPROX_SPEC_GAME_MAGNITUDE	(0x10003)
#define FLAG_OAPPROX_SPEC_GAME_UNTIMED		(0x10004)
#define FLAG_OAPPROX_SPEC_GAME_MODE_ONLY	(0x10005)
#define FLAG_OAPPROX_SPEC_GAME_NONE		(0x10006)

#define MASK_OAPPROX_MODL_GAME			(0xF00F0) 
#define	FLAG_NOAPPROX_MODL_GAME			(0x10000) 
#define FLAG_OAPPROX_MODL_GAME_DIAG_MAG		(0x10010)
#define FLAG_OAPPROX_MODL_GAME_DIAGONAL		(0x10020)
#define FLAG_OAPPROX_MODL_GAME_MAGNITUDE	(0x10030)
#define FLAG_OAPPROX_MODL_GAME_UNTIMED		(0x10040)
#define FLAG_OAPPROX_MODL_GAME_MODE_ONLY	(0x10050)
#define FLAG_OAPPROX_MODL_GAME_NONE		(0x10060)

#define MASK_OAPPROX_ENVR_GAME			(0xF0F00) 
#define	FLAG_NOAPPROX_ENVR_GAME			(0x10000) 
#define FLAG_OAPPROX_ENVR_GAME_DIAG_MAG		(0x10100)
#define FLAG_OAPPROX_ENVR_GAME_DIAGONAL		(0x10200)
#define FLAG_OAPPROX_ENVR_GAME_MAGNITUDE	(0x10300)
#define FLAG_OAPPROX_ENVR_GAME_UNTIMED		(0x10400)
#define FLAG_OAPPROX_ENVR_GAME_MODE_ONLY	(0x10500)
#define FLAG_OAPPROX_ENVR_GAME_NONE		(0x10600)

#define MASK_OAPPROX_GLOBAL_GAME		(0xFF000) 
#define FLAG_NOAPPROX_GLOBAL_GAME		(0x10000)
#define FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG	(0x11000)
#define FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL	(0x12000)
#define FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE	(0x13000)
#define FLAG_OAPPROX_GLOBAL_GAME_UNTIMED	(0x14000)
#define FLAG_OAPPROX_GLOBAL_GAME_NONE		(0x16000)

#define FLAG_OAPPROX_GAME_DIAG_MAG	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_DIAG_MAG \
					 | FLAG_OAPPROX_MODL_GAME_DIAG_MAG \
					 | FLAG_OAPPROX_ENVR_GAME_DIAG_MAG \
					 | FLAG_OAPPROX_GLOBAL_GAME_DIAG_MAG \
					 )
#define FLAG_OAPPROX_GAME_DIAGONAL	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_DIAGONAL \
					 | FLAG_OAPPROX_MODL_GAME_DIAGONAL \
					 | FLAG_OAPPROX_ENVR_GAME_DIAGONAL \
					 | FLAG_OAPPROX_GLOBAL_GAME_DIAGONAL \
					 )
#define FLAG_OAPPROX_GAME_MAGNITUDE	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE \
					 | FLAG_OAPPROX_MODL_GAME_MAGNITUDE \
					 | FLAG_OAPPROX_ENVR_GAME_MAGNITUDE \
					 | FLAG_OAPPROX_GLOBAL_GAME_MAGNITUDE \
					 )
#define FLAG_OAPPROX_GAME_LOCAL_MAGNITUDE	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_MAGNITUDE \
					 | FLAG_OAPPROX_MODL_GAME_MAGNITUDE \
					 | FLAG_OAPPROX_ENVR_GAME_MAGNITUDE \
					 | FLAG_NOAPPROX_GLOBAL_GAME \
					 )
#define FLAG_OAPPROX_GAME_UNTIMED	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_UNTIMED \
					 | FLAG_OAPPROX_MODL_GAME_UNTIMED \
					 | FLAG_OAPPROX_ENVR_GAME_UNTIMED \
					 | FLAG_OAPPROX_GLOBAL_GAME_UNTIMED \
					 )

#define FLAG_OAPPROX_GAME_MODE_ONLY	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_OAPPROX_SPEC_GAME_MODE_ONLY \
					 | FLAG_OAPPROX_MODL_GAME_MODE_ONLY \
					 | FLAG_OAPPROX_ENVR_GAME_MODE_ONLY \
					 | FLAG_OAPPROX_GLOBAL_GAME_NONE \
					 )

#define FLAG_OAPPROX_STRATEGY_SLICE		(0x20000) 

#define MASK_OAPPROX_SIG_SLICE			(0xF000F) 
#define	FLAG_NOAPPROX_SIG_SLICE			(0x00000) 
#define FLAG_OAPPROX_SIG_SLICE_DIAGONAL		(0x20001)
#define FLAG_OAPPROX_SIG_SLICE_MAGNITUDE	(0x20002)
#define FLAG_OAPPROX_SIG_SLICE_UNTIMED		(0x20003)
#define FLAG_OAPPROX_SIG_SLICE_MODE_ONLY	(0x20004)
#define FLAG_OAPPROX_SIG_SLICE_NONE		(0x20005)

#define MASK_OAPPROX_INSIG_SLICE		(0xF00F0) 
#define	FLAG_NOAPPROX_INSIG_SLICE		(0x00000) 
#define FLAG_OAPPROX_INSIG_SLICE_DIAGONAL	(0x20010)
#define FLAG_OAPPROX_INSIG_SLICE_MAGNITUDE	(0x20020)
#define FLAG_OAPPROX_INSIG_SLICE_UNTIMED	(0x20030)
#define FLAG_OAPPROX_INSIG_SLICE_MODE_ONLY	(0x20040)
#define FLAG_OAPPROX_INSIG_SLICE_NONE		(0x20050)

#define	FLAG_NOAPPROX_SLICE		(  FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_NOAPPROX_INSIG_SLICE \
					 ) 
#define	FLAG_OAPPROX_SLICE_DIAGONAL	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_OAPPROX_INSIG_SLICE_DIAGONAL \
					 ) 
#define	FLAG_OAPPROX_SLICE_MAGNITUDE	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_OAPPROX_INSIG_SLICE_MAGNITUDE \
					 ) 
#define	FLAG_OAPPROX_SLICE_UNTIMED	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_OAPPROX_INSIG_SLICE_UNTIMED \
					 ) 
#define	FLAG_OAPPROX_SLICE_MODE_ONLY	(  FLAG_ROOT_OAPPROX \
                                         | FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_OAPPROX_INSIG_SLICE_MODE_ONLY \
					 ) 
#define	FLAG_OAPPROX_SLICE_NONE		(  FLAG_ROOT_OAPPROX \
                                         | FLAG_NOAPPROX_SIG_SLICE \
					 | FLAG_OAPPROX_INSIG_SLICE_NONE \
					 ) 

#define MASK_UAPPROX			(0xF00000)

/*************************************************************************
 *  Constants for system types
 */
/* MASK values for GLOBAL_STATUS[6] */

#define RED_OPT_GAME_ROLES	3099 
#define	INDEX_GAME_ROLES		6 
#define MASK_GAME_ROLES		(0x7) // The following four flags & masks are also used in 
#define FLAG_GAME_SPEC		(0x1) // PROCESS[].status.  
#define FLAG_GAME_MODL		(0x2)
#define FLAG_GAME_ENVR		(0x4)
#define	FLAG_GAME_ROLES_CHANGED	(0x8) 

#define	INDEX_EXECUTION		6
#define	MASK_EXECUTION		(0xF0)
#define FLAG_EXEC_SYNC		(0x10)
#define FLAG_EXEC_ITERATIVE	(0x20)



#define	RED_OPT_INITIAL_ZERO	30
#define	INDEX_INITIAL_ZERO	6
#define	FLAG_INITIAL_ZERO	(0x0100)

#define	RED_OPT_MODAL_CLOCK	50
#define	INDEX_MODAL_CLOCK	6
#define	FLAG_MODAL_CLOCK	(0x0200)

#define	RED_OPT_SYMMETRY	150 
#define	INDEX_SYMMETRY		6
#define MASK_SYMMETRY		(0xF000)
#define	FLAG_NO_SYMMETRY			(0x0000)

#define	FLAG_SYMMETRY_ZONE			(0x1000)
#define	FLAG_SYMMETRY_STATE			(0x2000)

#define	FLAG_SYMMETRY_POINTER_ONESTEP_OFFLINE	(0x3000)
#define	FLAG_SYMMETRY_POINTER_FIXPOINT_ONLINE	(0X4000)
#define FLAG_SYMMETRY_POINTER_FIXPOINT_OFFLINE	(0x5000)
#define FLAG_SYMMETRY_DISCRETE_GENERAL		(0x6000)


#define	RED_OPT_USE_PLAIN_NONZENO	100 
#define	RED_OPT_USE_APPROX_NONZENO	101 
#define RED_OPT_USE_NONZENO  		102
#define	INDEX_ZENO_CYCLE		6
#define MASK_ZENO_CYCLE			(0xF00000)
#define	FLAG_USE_PLAIN_NONZENO		(0x000000)
#define FLAG_USE_APPROX_NONZENO		(0x100000)
#define FLAG_ZENO_CYCLE_OK		(0x200000)

#define	INDEX_MODAL_CONVEXITY_CHECKING		6
#define	MASK_MODAL_CONVEXITY_CHECKING		(0x400000) 
#define	FLAG_MODAL_CONVEXITY_CHECKING		(0x400000) 
#define	FLAG_MODAL_NO_CONVEXITY_CHECKING	(0x000000) 


/* MASK values for GLOBAL_STATUS[7] */
/* This should be for the speed up techniques. 
 */ 
/* MASK values for GSTATUS[7] */ 
#define	INDEX_REDUCTION_INACTIVE	7
#define	MASK_REDUCTION_INACTIVE		(0xF)
#define	FLAG_NO_REDUCTION_INACTIVE	(0x0) 
#define	FLAG_REDUCTION_INACTIVE_NOXTIVE	(0x1) 
#define	FLAG_REDUCTION_INACTIVE		(0x2) 

#define	INDEX_ACTION_APPROX		7
#define	MASK_ACTION_APPROX		(0xF0)
#define	FLAG_NO_ACTION_APPROX		(0x00) 
#define	FLAG_ACTION_APPROX_NOXTIVE	(0x10) 
#define	FLAG_ACTION_APPROX_UNTIMED	(0x20) 

#define	INDEX_ACTION_STAGE_EVAL		7 
#define	MASK_ACTION_STAGE_EVAL		(0x300) 
#define FLAG_ACTION_LAZY_EVAL		(0x000) 
#define FLAG_ACTION_DELAYED_EVAL	(0x100) 

#define INDEX_ACTION_ADDRESS_AFFECTING	7 
#define FLAG_ACTION_ADDRESS_AFFECTING_ONLY	(0x400)  
#define FLAG_ACTION_ADDRESS_AFFECTING_ALL	(0x000)  


#define	INDEX_FULL_REACHABILITY				7
#define	FLAG_FULL_REACHABILITY				(0x00001000)

#define	INDEX_COMPLETE_GREATEST_FIXPOINT		7
#define	FLAG_COMPLETE_GREATEST_FIXPOINT			(0x00001000)

#define	RED_OPT_GFP_NO_EARLY_DECISION			210
#define	INDEX_GFP_NO_EARLY_DECISION			7
#define	FLAG_GFP_NO_EARLY_DECISION			(0x00002000)

#define	INDEX_GFP					7
#define FLAG_GFP_FORCED_LONG_DEST_WITH_UAPPROX		(0x00004000)
#define FLAG_GFP_ON_THE_FLY				(0x00008000)

#define FLAG_IN_GAME_GFP	 			(0x00010000)
#define FLAG_IN_GFP_EASY_STRONG_FAIRNESS		(0x00020000)

#define	INDEX_FAIRNESS					7 
#define	FLAG_FAIRNESS_ASSUMPTIONS			(0x00040000) 

#define INDEX_SIMULATION_REASONING			7 
#define	MASK_SIMULATION_REASONING			(0x00080000)
#define	FLAG_SIMULATION_UNIVERSAL			(0x00080000)
#define	FLAG_SIMULATION_NEG_EXISTENTIAL 		(0x00000000) 

/*  The following flags are obsolete. 
#define MASK_FAIRNESS_ASSUMPTIONS_EVAL			(0x000C0000) 
#define FLAG_FAIRNESS_ASSUMPTIONS_EVAL_CONJ 		(0x00040000) 
#define	FLAG_FAIRNESS_ASSUMPTIONS_EVAL_CONCAT		(0x00080000)
#define FLAG_FAIRNESS_ASSUMPTIONS_EVAL_OCC_VAR		(0x000C0000) 
*/
#define MASK_GFP_PATH		 			(0x00100000) 
#define FLAG_GFP_PATH_INVARIANCE 			(0x00000000) 
#define	FLAG_GFP_PATH_FXP				(0x00100000) 

#define INDEX_COMPLEX_INDIRECT_SHAPES			7 
#define	FLAG_COMPLEX_INDIRECT_SHAPES			(0x00200000) 

#define INDEX_LUB_EXTRAPOLATION				7 
#define MASK_LUB_EXTRAPOLATION				(0x0F000000)
#define FLAG_GLUB_EXTRAPOLATION		 		(0x01000000) 
#define FLAG_LUB_EXTRAPOLATION		 		(0x02000000) 


/* MASK values for GLOBAL_STATUS[8] */
#define	INDEX_DEBUG				8
#define MASK_DEBUG				(0xFE00)
#define FLAG_DEBUG_TRACE			(0x0800)
#define FLAG_DEBUG_GOAL				(0x1000) 

#define	FLAG_DEBUG_INITIAL			(0x2000)

#define	FLAG_BUG_DETECTED			(0x4000)

#define FLAG_DEBUG_INITIAL_STOP			(0x8000) 



#define	INDEX_STRATEGY_COMPARISON		8
#define FLAG_STRATEGY_COMPARISON		(0x10000) 



/* MASK values for controlled early exit. */ 
#define INDEX_EXIT                   		8
#define MASK_EXIT                               (0xE0000)
#define FLAG_EXIT_AFTER_PARSING                 (0x20000) 
#define FLAG_EXIT_AFTER_QUOTIENT                (0x40000) 
#define FLAG_EXIT_AFTER_SYNC_XTION_COUNTING     (0x80000) 


#define	RED_OPT_REDLIB_SKIP_ABSTRACT_DECISION	1000
#define INDEX_REDLIB_SKIP_ABSTRACT_DECISION	8
#define	FLAG_REDLIB_SKIP_ABSTRACT_DECISION	(0x100000) 



/* MASK values for GSTATUS[9] */ 
/* This should be for the output. 
 */

#define	RED_OPT_PRINTOUT		130 
#define	RED_OPT_PRINT_POST_PROCESSING	131 
#define	RED_OPT_PRINT_MEMORY		132 
#define	RED_OPT_PRINT_TIME		133
#define	RED_OPT_PRINT_RED_INTERMEDIATE	134 
#define	RED_OPT_PRINT  			135

#define	INDEX_PRINT			9
#define MASK_PRINT			(0x0FFFFF)
#define FLAG_NO_PRINT			(0x000000)
#define FLAG_PRINT_ALL			(0x0FFFFF)
#define FLAG_PRINT_POSTPROCESSING	(0x000001)
#define FLAG_PRINT_MEMORY		(0x000002)
#define FLAG_PRINT_TIME			(0x000004)
#define FLAG_PRINT_RED_INTERMEDIATE	(0x000008)

#define	INDEX_REGRESS_CHECKING		9
#define	FLAG_REGRESS_CHECKING		(0x100000)



/* MASK values for GSTATUS[10] */ 
#define	RED_OPT_REACHABILITY_DEPTH_BOUND	180 
#define	RED_OPT_REACHABILITY_DEPTH		181 
#define INDEX_REACHABILITY_DEPTH_BOUND		10
#define FLAG_REACHABILITY_DEPTH_BOUND		(0x1000)
#define MASK_REACHABILITY_DEPTH_BOUND		(0x0FFF) 

#define INDEX_FIXPOINT_ITERATION_BOUND		10
#define FLAG_FIXPOINT_ITERATION_BOUND		(0x1000)
#define MASK_FIXPOINT_ITERATION_BOUND		(0x0FFF) 

#define	RED_OPT_SEARCH				120 
#define	INDEX_SEARCH 				10
#define MASK_SEARCH				(0x000E000)
#define	FLAG_FIRST_BREADTH			(0x0000000)
#define	FLAG_FIRST_DEPTH			(0x0002000)
#define	FLAG_FIRST_MODE_DISTANCE		(0x0004000)
#define	FLAG_FIRST_QUOTIENT_DISTANCE		(0x0006000)

#define	RED_OPT_COUNTER_EXAMPLE			140 
#define	INDEX_COUNTER_EXAMPLE			10
#define FLAG_COUNTER_EXAMPLE			(0x0010000)



#define	FLAG_LEAST_FIXPOINT			(0x1000000) 

#define	INDEX_REACH_UTILITIES 			10 
#define MASK_REACH_UTILITIES 	(  FLAG_REACHABILITY_DEPTH_BOUND \
                                 | MASK_REACHABILITY_DEPTH_BOUND \
                                 | FLAG_COUNTER_EXAMPLE \
                                 ) 

/* MASK values for GSTATUS[11] */ 

#define	RED_OPT_HYBRID_STRATEGY				160 
#define	RED_OPT_HYBRID_STRATEGY_PARAMETER_PRUNING	161 
#define	RED_OPT_HYBRID_REACHABLE_COMPLEMENT		162
#define	INDEX_HYBRID_STRATEGY				11
#define	MASK_HYBRID_STRATEGY				(0x00000FFF)
#define	FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING		(0x00000004)
#define FLAG_HYBRID_REACHABLE_COMPLEMENT		(0x00000008)


#define	RED_OPT_COVERAGE				110 
#define	INDEX_COVERAGE					11
#define MASK_COVERAGE					(0x0FFF0000)
#define FLAG_ALL_COVERAGE				(0x0FFF0000)
#define FLAG_REGION_COVERAGE				(0x00010000)
#define FLAG_ARC_COVERAGE				(0x00020000)
#define FLAG_TRIGGER_COVERAGE				(0x00040000)
#define FLAG_DISCRETE_TRIGGER_COVERAGE			(0x00100000)
#define FLAG_DISCRETE_COVERAGE				(0x00200000)


/* MASK values for GSTATUS[12] */ 
#define	INDEX_REDLIB_CONTROL		12 
#define	FLAG_REDLIB_DECLARE_FULL_MODEL	(0x000001) 

#define	FLAG_REDLIB_RENEW_VARS		(0x000002) 
#define	FLAG_REDLIB_ADD_VARS		(0x000000) 

#define	FLAG_REDLIB_RENEW_RULES		(0x000004) 
#define	FLAG_REDLIB_ADD_RULES		(0x000000) 

#define	FLAG_REDLIB_PARSING_ONLY	(0x000008) 


/* MASK values for GSTATUS[13] */ 

#define RED_OPT_TIME_PROGRESS 					1432 
#define INDEX_TIME_PROGRESS					13 
#define	FLAG_TIME_PROGRESS					(0x00001) 
#define	FLAG_NO_TIME_PROGRESS					(0x00000) 

#define	INDEX_TIME_MODE_SHAPES					13
#define	MASK_TIME_MODE_SHAPES					(0x00002)
#define	FLAG_TIME_MODE_SOME_TCONCAVE				(0x00000)
#define	FLAG_TIME_MODE_ALL_TCONVEX				(0x00002) 

// This is for a better formulation of tconcave() 
// with detection of shared paths. 
#define	MASK_TIME_TCONVEXITY_SHARED_PARTITIONS 			(0x00004)
#define	FLAG_TIME_TCONVEXITY_SHARED_PARTITIONS			(0x00004) 
#define	FLAG_TIME_TCONVEXITY_NO_SHARED_PARTITIONS 		(0x00000) 

// This is for the checking of time-convexity with TCTL formulas.
#define INDEX_TIME_PROGRESS_ANALYSIS 				13 
#define MASK_TIME_PROGRESS_ANALYSIS				(0x000F0)
#define FLAG_TIME_PROGRESS_ANALYSIS_NONE			(0x00000)
#define FLAG_TIME_PROGRESS_ANALYSIS_TCTCTL			(0x00010)
#define FLAG_TIME_PROGRESS_ANALYSIS_ADVANCED			(0x00020) 

#define	MASK_TIME_PROGRESS_OPTIONS				(0x0FF00)
#define	FLAG_TIME_PROGRESS_NONE					(0x00000)
#define FLAG_TIME_PROGRESS_ASSUMED_CONVEXITY			(0x00100) 

#define FLAG_TIME_PROGRESS_FULL_FORMULATION			(0x00400) 
// FLAG_TIME_PROGRESS_CONCAVITY	is actually full formulation. 
#define	FLAG_TIME_PROGRESS_SHARED_CONCAVITY			(0x00500)
#define	FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_CONCAVITY		(0x00600)

#define	FLAG_TIME_PROGRESS_SPLIT_CONVEXITIES			(0x00800) 
#define	FLAG_TIME_PROGRESS_SHARED_SPLIT_CONVEXITIES		(0x00900)	
#define FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES 	(0x00A00)
#define FLAG_TIME_PROGRESS_ON_THE_FLY_SHARED_SPLIT_CONVEXITIES 	(0x00B00)

#define FLAG_TIME_PROGRESS_EASY_CONCAVITY			(0x00C00) 
#define FLAG_TIME_PROGRESS_SHARED_EASY_CONCAVITY		(0x00D00) 
#define FLAG_TIME_PROGRESS_ADAPTIVE_SHARED_EASY_CONCAVITY	(0x00E00) 


/* MASK values for GSTATUS[14] */ 

#define INDEX_TEMPLATE_PROCESS_COUNT		14
#define FLAG_TEMPLATE_PROCESS_COUNT_OVERRIDDEN	(0x10000000) 
#define MASK_TEMPLATE_PROCESS_COUNT		(0x0000FFFF) 
#define DISPLACEMENT_TEMPLATE_PROCESS_COUNT	(0x00000001) 

/* MASK values for GSTATUS[15] */ 

#define INDEX_TEMPLATE_MEMORY_SIZE		15
#define FLAG_TEMPLATE_MEMORY_SIZE_OVERRIDDEN	(0x10000000) 
#define MASK_TEMPLATE_MEMORY_SIZE		(0x0FFFFFFF) 
#define DISPLACEMENT_TEMPLATE_MEMORY_SIZE	(0x00000001) 




/* MASK values for GSTATUS[16] */ 

#define INDEX_FLOATING_DISPLAY			16
#define MASK_FLOATING_DISPLAY_FRAC_POS		(0x0000000F) 
#define MASK_FLOATING_DISPLAY_FORMAT		(0x00000030) 
#define FLAG_FLOATING_DISPLAY_NONE		(0x00000000) 
#define FLAG_FLOATING_DISPLAY_SCIENTIFIC	(0x00000010) 
#define FLAG_FLOATING_DISPLAY_DECIMAL		(0x00000020) 
#define FLAG_FLOATING_DISPLAY_SHORTEST		(0x00000030) 




/* MASK values for GSTATUS[GSTATUS_SIZE-1] */ 
#define INDEX_EXPERIMENT		(GSTATUS_SIZE-1)
#define MASK_EXPERIMENT_TOKEN		(0xFF) 
#define TOKEN_NO_EXPERIMENT		(0x00) 

#define TOKEN_CURRENT_EXPERIMENT	(0x01) 



struct name_link_type {
  char			*name;
  struct name_link_type	*next_name_link;
};

#define _INDEX_LINK_TYPE_	1

struct index_link_type {
  int				index;
  struct index_link_type	*next_index_link;
};


struct index_pair_link_type {
  int				index1, index2;
  struct index_pair_link_type	*next_index_pair_link;
};


struct index_triple_link_type {
  int				index1, index2, index3;
  struct index_triple_link_type	*next_index_triple_link;
};


struct indexed_structure_link_type {
  int					index;
  char					*structure; 
  struct indexed_structure_link_type	*next_indexed_structure_link;
};





//120714 CHANGE
#define OFFSET_PROB		0
#define PROB			variable_index[TYPE_FLOAT][0][OFFSET_PROB]

#define OFFSET_PROBW		1
#define PROBW			variable_index[TYPE_FLOAT][0][OFFSET_PROBW]

#define TIME			2
#define OFFSET_TIME		1

#define	DELTA			4
#define	OFFSET_DELTA		2
#define VI_DELTA		variable_index[TYPE_CLOCK][0][OFFSET_DELTA]

#define	DELTAP			6 /* used for time progress in the general case. */
#define	OFFSET_DELTAP		3 /* used for time progress in the general case. */

#define NEG_DELTA		8
#define OFFSET_NEG_DELTA	4

#define	NEG_DELTAP		10 /* used for time progress in the general case. */
#define	OFFSET_NEG_DELTAP	5 /* used for time progress in the general case. */

#define MODAL_CLOCK		12
#define OFFSET_MODAL_CLOCK	6

#define PLAY_TIME		14
#define OFFSET_PLAY_TIME	7

#define ZENO_CLOCK		16
#define OFFSET_ZENO_CLOCK	8

/**********************************************************
 *
 */

#define	MASK_POINTER_STABLE	1

#define MODE_NO_SPEC		-1
#define MODE_DYNAMIC		-2


#define	PROBE_RISK		0
#define	PROBE_PRERISK1		1
#define	PROBE_PRERISK2		2
#define	PROBE_PRERISK3		3
#define	PROBE_PRERISK4		4
#define	PROBE_PRERISK5		5
#define	PROBE_PRERISK21		6
#define	PROBE_PRERISK22		7
#define	PROBE_PRERISK23		8

#define	BENCHMARK_PFISCHER4	104
#define	BENCHMARK_PCD3		203
#define	BENCHMARK_PCD5a		204
#define	BENCHMARK_PCD5a1	205


#define	FLAG_PRINT_XTION	1
#define	FLAG_NO_PRINT_XTION	0


#define	FLAG_ACC_HASH_TIME	1
#define	FLAG_ACC_ACT_TIME	2
#define	FLAG_ACC_NORM_TIME	3
#define	FLAG_ACC_TIME_TIME	4 

#define FLAG_ACC_SILENT		0
#define FLAG_ACC_REPORT		1


struct declare_type {
  int	TYPE, 
	PROC_INDEX, /* 0: global; 1: local; */
	OFFSET; 
};



// The first 3 least significant bits are used for game roles. 
#define FLAG_GAME_OPERATION	(0x10) 

#define	FLAG_XTION_REDUCED	(0x10)

#define	FLAG_PROC_SIGNIFICANT	(0x40) 

struct process_type {
  char			*name;
  int			status, 
			group_process_index, 	/* the id of the root process 
						 * of the group. 
						 */ 
			depth_call, 
			*mode_distance_from_initial, 
			reachable_mode_count, *reachable_mode, 
			reachable_lower_mode, reachable_upper_mode, 
			firable_xtion_count, *firable_xtion;
  struct red_type	*red_stop;
};


struct constraint_type {
  int	 cstart, cstop, bound;
};




struct zone_bound_type	{
  int	var_index, upper_bound;
};

struct mode_invariance_type {
  struct red_type		*red, *untimed_red;
  int				zone_bound_count;
  struct zone_bound_type	*zone_bound;
};


struct clock_bound_type { 
  int	clock_index, upper_bound, lower_bound; 	
}; 


struct process_clock_bound_type { 
  int				bound_count; 
  struct clock_bound_type	*bound; 
}; 


struct rate_spec_type {
   int	var_index, lb_numerator, lb_denominator, ub_numerator, ub_denominator;
};

#define	FLAG_RATE_INTERVAL	1

struct process_rate_spec_type {
  int			status;
  struct rate_spec_type	*rate_spec;
};

struct mode_type {
  int					status,  
/* Constants and structures for the mode table status. 
 */ 
#define	FLAG_MODE_URGENT		(0x000001)
#define	FLAG_GLOBAL_EFFECT		(0x000400)
#define	FLAG_CLOCK_RESET		(0x000800)
#define	FLAG_CLOCK_UNKNOWN		(0x000008)
#define	FLAG_CLOCK_INACTIVE		(0x000010)
#define	FLAG_PARTIALLY_ACTIVE		(0x000020)
#define	FLAG_CLOCK_ACTIVE		(0x001000)
#define FLAG_INVARIANCE_TIME_CONVEX	(0x002000)
#define FLAG_TO_INFINITY		(0x004000) 

					process_count, xtion_count,
					rate_spec_count, over_bound, 
  					bound_left_open, distance, 
					*process, *bound;
  char					*name, *src_lines;
  struct ps_exp_type			*invariance_exp;
  struct mode_invariance_type		*invariance;
  int					*xtion, *local_clock_bound;
  struct process_clock_bound_type	*clock_bound; 
  struct parse_mode_type		*parse_mode;
  struct process_rate_spec_type		*process_rate_spec;
};




#define	FLAG_NO_PARENT	-1


struct stream_operation_type { 
  int			stream, 
			operation; 

#define	OP_STREAM_OPEN_INPUT	89761
#define	OP_STREAM_OPEN_OUTPUT	89762
#define	OP_STREAM_CLOSE		89763
#define	OP_STREAM_INPUT		89764
#define	OP_STREAM_OUTPUT	89765
#define	OP_MALLOC		89766
#define	OP_FREE			89767

  struct ps_exp_type	*var, *value_exp; 	
}; 


struct sync_from_xtion_type {
  int	XTION_INDEX, PLACE_INDEX;
};


#define FLAG_GAME_SYNC_CLASS		(0xFF)
#define FLAG_GAME_SYNC_SPEC_REC		(0x01)
#define FLAG_GAME_SYNC_SPEC_XMT		(0x02)
#define FLAG_GAME_SYNC_DSCR_REC		(0x04)
#define FLAG_GAME_SYNC_DSCR_XMT		(0x08)
#define FLAG_GAME_SYNC_ENVR_REC		(0x10)
#define FLAG_GAME_SYNC_ENVR_XMT		(0x20)
#define FLAG_SYNC_QUANTIFIER_REC	(0x40)
#define FLAG_SYNC_QUANTIFIER_XMT	(0x80)

struct sync_type {
  int				STATUS, VAR_INDEX, X_XTION_COUNT, Q_XTION_COUNT;
  struct sync_from_xtion_type	*X_XTION, *Q_XTION;
};


// struct operand_type {
//   int	var_index, indirect_count, *indirect;
// };

 
struct action_type { 
  int				term_count, 
				*single_coeff_numerator, *single_coeff_denominator,
				*offset_numerator, *offset_denominator, 
				*lhs_vi; // this is only for discrete value.
  struct ps_exp_type		*lhs, *rhs_exp;
  struct parse_term_type	*term;
  struct ps_exp_type		*offset; 
  struct red_type		**red_effect; 
}; 


struct guard_type { 
  struct red_type	**red_cond, **red_uncond; 
  struct ps_exp_type	*cond; 
}; 


struct erase_type { 
  struct ps_exp_type	*var;
}; 


struct call_statement_type { 
  int	call_mode_index, ret_mode_index; 
}; 


struct cplug_statement_type { 
  struct ps_exp_type	*lhs; 
  int			cmod_index, cproc_index; 
};


struct seq_statement_type { 
  int			count; 
  struct statement_type	**statement; 	
}; 


struct if_statement_type { 
  struct statement_type	*if_statement, *else_statement; 
  struct red_type	**red_cond, **red_uncond; 
  struct ps_exp_type	*parse_cond_exp; 
}; 


#define FLAG_WHILE_GFP_EVALD	1

struct while_statement_type { 
  struct statement_type *statement; 	
  struct red_type	**red_cond, **red_uncond, **red_gfp;  
  struct ps_exp_type	*parse_cond_exp; 
}; 

union	statement_union	{
  struct action_type		act;
  struct guard_type		guard; 
  struct erase_type		erase; 
  struct call_statement_type	call; 
  struct cplug_statement_type 	cplug;  
  struct seq_statement_type	seq; 
  struct if_statement_type	branch; 
  struct while_statement_type	loop; 
}; 


/* The following two flags overlap with the FLAG_ONE_POS_CLOCK and FLAG_ONE_NEG_CLOCK 
 * in redparse.h.  
 * They are only used in compound statements while 
 * FLAG_ONE_POS_CLOCK and FLAG_ONE_NEG_CLOCK are only used for simple statements.  
 */

struct statement_type { 
  int 				op, 
#define	UNCHANGED			0
#define	INCREMENT_BY_CONSTANT		1
#define	DECREMENT_BY_CONSTANT		2

#define	ASSIGN_DISCRETE_CONSTANT	10
#define	ASSIGN_DISCRETE_POLYNOMIAL	11 /* x = polynomial */

#define	ASSIGN_CLOCK_CONSTANT		20 /* x = y + c */
#define	ASSIGN_CLOCK_MIXED		21 /* x = y + c */
#define	ASSIGN_CLOCK_DIFFERENCE		22 /* x = y + c */
#define	ASSIGN_CLOCK_DIFFERENCE_MIXED	23 /* x = y + c */

#define	ASSIGN_HYBRID_EXP		30 /* x = (a/b)x + ... + (c/d) */

#define ASSIGN_TRASH			40

#define	ST_GUARD			41
#define ST_ERASE			42

#define ST_SEQ				50
#define ST_WHILE			51
#define ST_IF				52 

#define	ST_CALL				60
#define	ST_RETURN			61
 
#define ST_CPLUG			70

				st_status; 
				
#define	LOCAL_ACTION_IDENTIFIER			-1
#define GLOBAL_ACTION_IDENTIFIER		0

#define	FLAG_ACTION_INDIRECTION			(0x00001)
#define	FLAG_ACTION_LHS_RECURSION		(0x00002)
#define	FLAG_ACTION_COEFF_CONSTANT		(0x00004)
#define	FLAG_ACTION_LOCAL_IDENTIFIER		(0x00008)
#define	FLAG_ACTION_QUANTIFIED_SYNC		(0x00010)

#define	MASK_STATEMENT_COMPOUND			(0x03000) 
#define	FLAG_STATEMENT_COMPOUND			(0x01000)
#define FLAG_STATEMENT_ELSE			(0x02000) 

#define MASK_ACTION_OFFSET_TYPE			(0xF0000) 
#define	FLAG_ACTION_OFFSET_CONSTANT		(0x10000)
#define FLAG_ACTION_OFFSET_PROCESS_CONSTANT	(0x20000)
#define	FLAG_ACTION_OFFSET_INTERVAL_CONSTANT	(0x30000) 
#define	FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL	(0x40000) 

  struct parse_statement_type	*parse_statement; 
  struct statement_type		*parent; 
  union statement_union		u;
}; 





struct sync_var_type {
  int			type, /* +1 for ? and -1 for ! */
#define	FLAG_ACCESS_WRITE		-1
#define	FLAG_ACCESS_READ		1
  
			status, 
#define	FLAG_NO_QUANTIFIED_SYNC		-1
#define MASK_SYNC_ADDRESS		7
#define	FLAG_ADDRESS_NULL		0
#define	FLAG_ADDRESS_HOLDER		1
#define FLAG_ADDRESS_ENFORCER		2 
#define	FLAG_ADDRESS_MULTIPLE		3
#define	FLAG_ADDRESS_DUPLICATE		4

#define FLAG_ADDRESS_STACK_PLUS		5
#define FLAG_ADDRESS_STACK_MINUS	6

			sync_index, qsync_vi;  
  struct ps_exp_type	*exp_quantification; 
}; 

struct xtion_type {
  int				index, 
				status, 
#define	FLAG_XTION_QUANTIFIED_SYNC	(0x000010) 
#define	FLAG_XTION_CLOCK_INACTIVE	(0x000020) 
#define MASK_LOCAL_IDENTIFIER_COUNT	(0x003000)
#define	FLAG_LOCAL_IDENTIFIER_ZERO	0
#define	FLAG_LOCAL_IDENTIFIER_ONE	(0x001000)
#define	FLAG_LOCAL_IDENTIFIER_MANY	(0x002000)
#define FLAG_XTION_WORKING		(0x010000)
/* The following flags are also used in SYNC_XTION[].status. 
 */
#define MASK_XTION_SIDE_EFFECTS			(0xFF00000) 
#define FLAG_XTION_GLOBAL_WRITING		(0x0100000)
#define	FLAG_XTION_SRC_GLOBAL_READING		(0x0200000) 
#define	FLAG_XTION_DST_GLOBAL_READING		(0x0400000) 

#define FLAG_XTION_PEER_WRITING			(0X0800000) 
#define FLAG_XTION_SRC_PEER_READING		(0x1000000) 
#define FLAG_XTION_DST_PEER_READING		(0x2000000) 

#define	FLAG_XTION_FWD_ACTION_INV_INTERFERE	(0x4000000)
#define	FLAG_XTION_BKW_TRIGGER_ACTION_INTERFERE	(0x8000000)

				process_count, *process, 
				src_mode_index, dst_mode_index, 
				stream_operation_count, 
				sync_count; 
  char				*src_lines; 
  struct stream_operation_type	*stream_operation; 
  struct sync_var_type		*sync; 
  struct statement_type		*statement;
  struct red_type		**red_trigger, **red_events;
  struct parse_xtion_type	*parse_xtion; 
};



struct sync_party_type {
  int			xtion, proc; 
  struct red_type	*red_trigger; 
  struct ps_exp_type	*trigger_exp; 
  struct statement_type	*statement; 
};



struct qfd_sync_type { 
  int 
    vi, 	// pointer type for the quantified sync
    value; 	
}; 


#define	FLAG_SYNC_INITIAL	-2 
#define	FLAG_SYNC_BULK		-1 


struct sync_xtion_type {
  int 				index, // sometimes we may need to pass a pointer 
                                       // to an sync_xtion entry to a procedure. 
                                       // In that case, this is the way that 
                                       // we can reference the index of the 
                                       // synchronous transition. 
				status, 
#define FLAG_SYNC_XTION_QUANTIFIED_SYNC	(0x001) 
// The 3 least significant bits are used for simulation roles.  
#define	FLAG_EVENT_SIGNIFICANT		(0x10)
#define FLAG_BRANCHING_QFD_SYNC		(0x20) 
#define FLAG_SPECIFIC_QFD_SYNC		(0x40) 
#define	FLAG_RW_RACE			(0x100)
#define	FLAG_WW_RACE			(0x200) 
/* The following flags are also used for SYNC_XTION[].status.  
 * FLAG_TRIGGER_ACTION_INTERFERE	(0x000080)
 */
#define	FLAG_GLOBAL_REFERENCE		(0x1000)
/* The following flags are also used in XTION[].status. 
#define MASK_XTION_SIDE_EFFECTS			(0xFF00000) 
#define FLAG_XTION_GLOBAL_WRITING		(0x0100000)
#define	FLAG_XTION_SRC_GLOBAL_READING		(0x0200000) 
#define	FLAG_XTION_DST_GLOBAL_READING		(0x0400000) 

#define FLAG_XTION_PEER_WRITING			(0x1000000) 
#define FLAG_XTION_SRC_PEER_READING		(0x2000000) 
#define FLAG_XTION_DST_PEER_READING		(0x4000000) 

#define	FLAG_XTION_TRIGGER_ACTION_INTERFERE	(0x8000000)
*/
#define FLAG_SXI_ENABLED		(0x10000000) 

#define FLAG_SXI_ACTIVE_ON_THE_FLY	(0x20000000)

#define	FLAG_SXI_NO_GAME_MATCH		(0x40000000) 

				party_count, action_count, 
				distance_change, 
				qfd_sync_count, 
				*ec_representative, 
				**ec_representee;  
  struct qfd_sync_type 		*qfd_sync;
  struct sync_party_type	*party;
  struct red_type		*red_trigger, 
  				*red_pre, *red_post, *red_events, 
				*red_ec_global_write_consistency; 
  int				occ_vi_count, *occ_vi; 
}; 





struct dfs_stack_type {
  int			sync_xtion_index;
  struct red_type	*sync_xtion_red;
  struct dfs_stack_type	*next_dfs_stack;
};


struct trace_execution_type {
  struct red_type	*red_precond, *red_postcond;
};

struct trace_frame_type	{
  int				nr, sync_xtion_index;
  struct trace_execution_type	*sync_xtion;
  struct trace_frame_type	*prev_trace_frame;
};


/* Two constants used to control the abstraction of red_reachable_bck() 
 * and red_reachable_fwd().  
 */ 
#define	FLAG_ABS_REACHABLE_MAGNITUDE_ONLY	1
#define FLAG_NO_ABS_REACHABLE_MAGNITUDE		0 

// Note that result is used as a name, instead of as an address. 
#define	string_var(result, head, tail, f, args)\
{ \
  va_start(args, f); \
  result = string_var_given_length( \
    leng_string_var(head, tail, f, args), \
    head, tail, f, args \
  ); \
  va_end(args); \
} \
  /*string_var() */ \


// Note that result1 and result2 is used as names, instead of as addresses. 
#define	string_2var(result1, result2, f1, f2, args)\
{ \
  va_start(args, f2); \
  result1 = string_var_given_length( \
    leng_string_var("", "", f1, args), "", "", f1, args \
  ); \
  result2 = string_var_given_length( \
    leng_string_var("", "", f2, args), "", "", f2, args \
  ); \
  va_end(args); \
} \
  /*string_2var() */ \





  



