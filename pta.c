/************************************************************************
 *
 *  This is an experiment that utilizes REDLIB to do MC and MDP. 
 *  It reads in three files. 
 *  The first is a RED model file. 
 *  The second is a specification file for the risk condition. 
 *  The third is a probability description file which consists of 
    of the following information. 
     1. a number that indicates the number of elements in the following 
        list 
     2. a list whose elements are lists of the following form.  
     
          [pl,pu],n: (d1, x1), ..., (dn, xn)
         
        Here [pl,pu] is an interval of process indices.   
        If pu is '*', then it means the total number of processes. 
        Also, di a probability value in [0,1] and 
        xi is a transition index.

    In addition, the program also accepts an option 
    
        -max 
        -min 

    The default is max. 
    
    After reading in the three files, 
    we need to build a table that relates probability of sync transitions. 
    The algorithm is as follows. 
    We first build the table of PROB_XTION[pi] of the following structure. 
    
      struct discrete_choice_type { 
        float	prob; 
        int	choice; 	
      }; 
      
      struct prob_xtion_type {
      	int	count; 
      	struct discrete_choice_type 
      		*comb; // the size of the array is count. 
      }; 
    
    Then we need the following collection of prob sync xtions. 
    
      struct prob_sync_xtion_type { 
        int	count; 
        struct sync_xtion_choice_type
        	*comb; 	
      };  
      
    Then we scan all sync_xtions sxi to collect prob_sync_xtion. 
    Specifically, we use the following code. 
    
      for (sxi = 0; 
           sxi < red_query_sync_xtion_count(RED_USE_DECLARED_SYNC_XTION); 
           sxi++
           ) { 
        if (there is no prob_sync_xtion[psxi] with the same combination of 
            prob_xtions
            ) 
          create a new prob_sync_xtion[psxi]; 
        Add sxi as a combination to prob_sync_xtion[psxi];     	
      } 
      
    Then in the calculation of reachability. 
    We first again calculate the abstract forward image. 
    Then we use the folloiwng code to compute an iteration of the fixpoint. 
    
      create Z1 as prob = 1 && goal. 
      Z2 = false; 
      for (Z2 != Z1) { 
      	Z2 = Z1; 
        for (psxi = 0; psxi < PROB_SYNC_XOUNT_COUNT; psxi++) { 
      	  Let S = false; 
      	  for all sxi in the combination of psxi { 
      	    compute precondition Z2 = pre(Z1, sxi); 
      	    S = prob_sum(S, prob_multiply(Z2, prob of sxi)); 
      	  } 
      	  if (a maximizer) 
      	    Z1 = prob_max(Z1, S); 
      	  else 
      	    Z1 = prob_min(Z1, S); 
      } }
      return the probability of Z1 && initial condition. 
 */
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include "redlib.h"
#include "redlib.e"


#define	FLAG_MAXIMIZER			1
#define FLAG_MINIMIZER 			-1 
#define	FLAG_MINIMIZER_TIMED_IDLE	-2 

int	status_max_min = FLAG_MAXIMIZER; 

FILE 	*fprob = NULL; 

int	flag_analysis_direction, 
#define FLAG_ANALYSIS_BACKWARD	0
#define	FLAG_ANALYSIS_FORWARD	1 

	flag_my_system_type, 

	flag_normality, 
	flag_action_approx, 
	flag_reduction, 
	flag_fairness_assumptions_eval, 
        flag_gfp_path,  
        flag_gfp_on_the_fly, 
	flag_lub_extrapolation,  
	flag_zeno,
	flag_approx, 
	flag_counter_example, 
	flag_full_reachability, 
	flag_simulation_reasoning, 
	flag_symmetry, 
	flag_print, 
	my_depth_enumerative_synchronization,  
	pc_command_line,  
	my_proc_count, 
	bound_reachability, 

#define	PTA_RULE_EXPANSION	100

	task_type, 
	DEPTH_RULE_EXPANSION = 0 
	; 
	
redgram	DGOAL; 

#define FLAG_FALSE	0
#define FLAG_TRUE	1

char	*model_fname,  
	*spec_fname,
	*prob_fname, 
	*output_fname; 

float	PRECISION_THRESHOLD = 0.001; 

struct discrete_choice_type { 
  float	prob; 
  int	choice; 	
}; 

struct prob_xtion_type {
  int 
    count, 
    pi_lb, pi_ub; 
  struct discrete_choice_type 
    *comb; // the size of the array is count. 
}; 


struct prob_sync_xtion_type {
  int 
    count; 
  struct discrete_choice_type 
    *comb; // the size of the array is count. 
}; 


struct discrete_choice_link_type { 
  float					prob; 
  int					choice; 
  struct discrete_choice_link_type	*next_discrete_choice_link; 	
}; 


struct prob_sync_xtion_link_type { 
  int 
    count; 
  struct discrete_choice_link_type 
    *choice_list; 
  struct prob_sync_xtion_link_type 
    *next_prob_sync_xtion_link; 
}; 


int 
  prob_xtion_count, 
  prob_sync_xtion_count, 
  *bck_xtion_prob; 
#define	FLAG_NOT_A_PROB_XTION	-1 

struct prob_xtion_type	
  *prob_xtion; 

struct prob_sync_xtion_type 
  *prob_sync_xtion; 
  
struct prob_sync_xtion_link_type 
  *prob_sync_xtion_list = NULL; 


int	count_px8c = 0; 

void 	print_psx8c(int pic, int psxi, int ci) { 
  fprintf(RED_OUT, "\n(%1d)[%1d,%1d,%1d]:prob_sync_xtion[8].count=%1d.\n", 
    ++count_px8c, pic, psxi, ci, 
    prob_sync_xtion[8].count
  ); 
  fflush(RED_OUT); 
}
  /* print_psx8c() */ 

/********************************************************
 *
 *  Structures for probabilistic rule extensions. 
 
 */ 
struct sync_action_link_type { 
#define	SA_TIME		1
#define SA_GUARD	2
#define	SA_ERASE	3
  int				op, index; 
  redgram			guard; 
  int				var_index; 
  struct sync_action_link_type	*next_sync_action_link; 
}; 

int	count_sync_action_generated = 0; 

struct sync_action_link_type	*alloc_sync_action_link() { 
  struct sync_action_link_type	*sa; 
  
  sa = (struct sync_action_link_type *) 
    malloc(sizeof(struct sync_action_link_type)); 
  sa->index = ++count_sync_action_generated; 
  sa->op = 0; 
  sa->guard = NULL; 
  sa->var_index = 0; 
  sa->next_sync_action_link = NULL; 

  return(sa); 
} 
  /* alloc_sync_action_link() */ 




struct echoice_link_type { 
  int				index; 
  float				prob; 
  int				count, choice; 
  redgram			red_postcond; 
  struct sync_action_link_type	*sync_action_list; 
  struct echoice_link_type	*next_echoice_link; 	
}; 


int	count_echoice_generated = 0; 

struct echoice_link_type	*alloc_echoice_link() { 
  struct echoice_link_type	*ech; 
  
  ech = (struct echoice_link_type *) 
    malloc(sizeof(struct echoice_link_type)); 
  ech->index = ++count_echoice_generated; 
  ech->prob = 0.0; 
  ech->next_echoice_link = NULL; 
  ech->choice = 0; 
  ech->count = 0; 
  ech->red_postcond = NULL; 
  ech->sync_action_list = NULL; 
  ech->next_echoice_link = NULL; 

  return(ech); 
} 
  /* alloc_echoice_link() */ 




struct eprob_sx_link_type { 
  int 
    index, 
    depth, 
    count; 
  redgram 
    joint_precond; 
  struct echoice_link_type 
    *echoice_list; 
  struct eprob_sx_link_type 
    *next_eprob_sx_link; 	
}; 


int	count_epsx_generated = 0; 

struct eprob_sx_link_type *alloc_eprob_sx_link() { 
  struct eprob_sx_link_type	*nepsx; 
  
  nepsx = (struct eprob_sx_link_type *) 
    malloc(sizeof(struct eprob_sx_link_type)); 
  nepsx->index = ++count_epsx_generated; 
  nepsx->count = 0; 
  nepsx->depth = 0; 
  nepsx->joint_precond = NULL; 
  nepsx->echoice_list = NULL; 
  nepsx->next_eprob_sx_link = NULL; 

  return(nepsx); 
} 
  /* alloc_eprob_sx_link() */ 



int 
  count_eprob_sx = 0; 
struct eprob_sx_link_type 
  *eprob_sx_list = NULL; 
int	TOKEN_RULE_EXPANSION; 


redgram	*ddx = NULL, *ddy = NULL; 
int	size_of_dd = 0; 


int	my_status_initialize() { 
  int	i; 
  
  my_proc_count = -1; 
  flag_analysis_direction = 
    FLAG_ANALYSIS_BACKWARD; 
//    FLAG_ANALYSIS_FORWARD; 
    
  flag_my_system_type = RED_SYSTEM_UNTIMED; 

  flag_zeno = 
//      RED_PLAIN_NONZENO;
//      RED_APPROX_NONZENO;
      RED_ZENO_TRACES_OK; 
  flag_normality = RED_NORM_ZONE_MAGNITUDE_REDUCED; 
  flag_action_approx = RED_NO_ACTION_APPROX; 
  flag_reduction = RED_REDUCTION_INACTIVE; 
  flag_approx = RED_NOAPPROX; 
  flag_symmetry = RED_NO_SYMMETRY; 
  flag_print = RED_NO_PRINT; 
  flag_counter_example = RED_NO_COUNTER_EXAMPLE; 
  flag_full_reachability = RED_NO_FULL_REACHABILITY; 
  flag_fairness_assumptions_eval = RED_GFP_EASY_STRONG_FAIRNESS; 
  flag_gfp_path = RED_GFP_PATH_INVARIANCE; 

//  flag_gfp_on_the_fly = RED_GFP_ON_THE_FLY; 
  flag_gfp_on_the_fly = RED_GFP_COMBINATONAL; 

  flag_lub_extrapolation = 0; 
  flag_simulation_reasoning = RED_SIMULATION_NEG_EXISTENTIAL; 
  
  my_depth_enumerative_synchronization = RED_DEPTH_ENUMERATIVE_DEFAULT; 

  pc_command_line = -1; 

  model_fname = "STDIN"; 
  spec_fname = "STDIN"; 
  prob_fname = "STDIN"; 
  output_fname = "STDOUT"; 
  
  PRECISION_THRESHOLD = 0.001;
  
  task_type = RED_TASK_GOAL; 

  size_of_dd = 200; 
  ddx = (redgram *) malloc(200 * sizeof(redgram)); 
  ddy = (redgram *) malloc(200 * sizeof(redgram)); 
} 
  /* my_status_initialize() */ 
  
  

int	my_process_command_line(argc, argv) 
	int	argc; 
	char	**argv; 
{ 
  int	i, j, k, file_count, value; 
  
  red_register_arg(argc, argv); 
  
  my_status_initialize(); 
  
  for (file_count = 0, i = 1; i < argc; i++)
    if (argv[i][0] != '-') { 
      switch (file_count) {
      case 0: 
        model_fname = argv[i]; 
        break; 
      case 1: 
        spec_fname = argv[i]; 
        break; 
      case 2: 
        prob_fname = argv[i]; 
        break; 
      case 3: 
        output_fname = argv[i]; 
        RED_OUT = fopen(argv[i], "w"); 
        break; 
      } 
      file_count++;
    }
    else {
      for (j = 1; j < strlen(argv[i]); j++)
	switch (argv[i][j]) {
	case '?': 
	  
	  exit(0); 
	case 'A': 
	  flag_approx = RED_OAPPROX_GAME_MAGNITUDE; 
	  break;
	  
	case 'G': 
//	  printf("\n-G%s:%0.6f\n", &(argv[i][j+1]), atof(&(argv[i][j+1]))); 
	  PRECISION_THRESHOLD = atof(&(argv[i][j+1])); 
	  j = strlen(argv[i]); 
	  break;

	case 'M': 
	  if (argv[i][j+1] == 'a' && argv[i][j+2] == 'x') { 
	    status_max_min = FLAG_MAXIMIZER; 
	    j = j+2; 
	  } 
	  else if (argv[i][j+1] == 'i' && argv[i][j+2] == 'n') { 
	    status_max_min = FLAG_MINIMIZER; 
	    j = j+2; 
	  } 
	  else if (argv[i][j+1] == 'i' && argv[i][j+2] == 't') { 
	    status_max_min = FLAG_MINIMIZER_TIMED_IDLE; 
	    j = j+2; 
	  } 
	  break; 
	  
	case 'P': // For the number of processes to override the one in the 
		  // the template. 
	  for (k = j+1; argv[i][k] >= '0' && argv[i][k] <= '9'; k++) {
	    argv[i][k-1] = argv[i][k];
	  }
          argv[i][k-1] = '\0';
          pc_command_line = atoi(&(argv[i][j])); 
          my_proc_count = pc_command_line; 
          j = k; 
	  break; 
	  	  
	case 'T':
	  switch (argv[i][++j]) { 
	  case 'd': 
	    task_type = RED_TASK_DEADLOCK; 
	    break; 
	  case 'e': 
	    task_type = PTA_RULE_EXPANSION; 
	    DEPTH_RULE_EXPANSION = atoi(&(argv[i][++j])); 
	    if (DEPTH_RULE_EXPANSION < 0) { 
	      fprintf(RED_OUT, "\nIllegal rule expansion depth %s\n", 
	        argv[i]
	      ); 
	      fflush(RED_OUT); 
	      DEPTH_RULE_EXPANSION = 0; 
	    } 
	    break; 
	  case 'g': 
	    task_type = RED_TASK_GOAL; 
	    break; 
	  case 'm': 
	    task_type = RED_TASK_MODEL_CHECK; 
	    break; 
	  case 'r': 
	    task_type = RED_TASK_RISK; 
	    break; 
	  case 's': 
	    task_type = RED_TASK_SAFETY; 
	    break; 
	  case 'z': 
	    task_type = RED_TASK_ZENO; 
	    break; 
	  default: 
	    printf("\nCommand-line error: unrecognized task option 'T%c'\n", argv[i][j]);
	    exit(0);
	  }
	  break; 

	case 'X': // for experiments 
          break; 

        default: 
	  printf("\nCommand-line error: unrecognized option '%c'\n", argv[i][j]);
	  exit(0); 
	} 
    } 

  red_set_sync_bulk_depth(my_depth_enumerative_synchronization); 
  printf("\nProbability precision set at %.10f.\n", 
    PRECISION_THRESHOLD
  ); 
  return(file_count); 
}
  /* my_process_command_line() */ 
  


  
void	input_xtion_probabilities(char *prob_fname) {
  int	pxi, xi, ci; 
  float	tprob; 
  
  fprob = fopen(prob_fname, "r"); 
  fscanf(fprob, "%d", &prob_xtion_count); 
  if (prob_xtion_count <= 0) { 
    fprintf(RED_OUT, "\nERROR: Illegal probability transition count %1d.\n", 
      prob_xtion_count
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  prob_xtion = (struct prob_xtion_type *) 
    malloc(prob_xtion_count * sizeof(struct prob_xtion_type)); 
  bck_xtion_prob = (int *) malloc(red_query_xtion_count()*sizeof(int)); 
  for(xi = 0; xi < red_query_xtion_count(); xi++) { 
    bck_xtion_prob[xi] = FLAG_NOT_A_PROB_XTION; 
  } 
  for (pxi = 0; pxi < prob_xtion_count; pxi++) { 
    fscanf(fprob, " [ %d ,", &(prob_xtion[pxi].pi_lb)); 
    if (   prob_xtion[pxi].pi_lb < 1 
        || prob_xtion[pxi].pi_lb > red_query_process_count()
        ) {
      fprintf(RED_OUT, "\nERROR: Illegal process index lower-bound %1d.\n", 
        prob_xtion[pxi].pi_lb
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    if (fscanf(fprob, " %d ] , %d :", 
          &(prob_xtion[pxi].pi_ub), &(prob_xtion[pxi].count)
        ) < 1) { 
      prob_xtion[pxi].pi_ub = red_query_process_count();
      fscanf(fprob, " oo ] , %d :", &(prob_xtion[pxi].count));  	
    }  
    if (   prob_xtion[pxi].pi_ub == 0 
        || prob_xtion[pxi].pi_ub > red_query_process_count()
        ) {
      fprintf(RED_OUT, "\nERROR: Illegal process index upper-bound %1d.\n", 
        prob_xtion[pxi].pi_ub
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (prob_xtion[pxi].count <= 0) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal combination count %1d of probabilistic transition %1d.\n", 
        prob_xtion[pxi].count, pxi
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
       
    prob_xtion[pxi].comb = (struct discrete_choice_type *) 
      malloc(prob_xtion[pxi].count * sizeof(struct discrete_choice_type)); 
      
    tprob = 0.0; 
    
    for (ci = 0; ci < prob_xtion[pxi].count; ci++) { 
      fscanf(fprob, " ( %f , %d )", &(prob_xtion[pxi].comb[ci].prob), 
        &(prob_xtion[pxi].comb[ci].choice)
      ); 
      if (   prob_xtion[pxi].comb[ci].choice < 0 
          || prob_xtion[pxi].comb[ci].choice > red_query_xtion_count()
          ) {
        fprintf(RED_OUT, "\nERROR: Illegal transition index %1d.\n", 
          prob_xtion[pxi].comb[ci].choice
        ); 
        fflush(RED_OUT); 
        exit(0); 
      }
      else if (   prob_xtion[pxi].comb[ci].prob < 0.0 
               || prob_xtion[pxi].comb[ci].prob > 1.0
               ) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal probability %f for transition %1d.\n", 
          prob_xtion[pxi].comb[ci].prob, 
          prob_xtion[pxi].comb[ci].choice 
        ); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      else if (bck_xtion_prob[prob_xtion[pxi].comb[ci].choice] 
               != FLAG_NOT_A_PROB_XTION
               ) { 
      	fprintf(RED_OUT, 
      	  "\nERROR: Duplicate usage of declared transition %1d \n", 
      	  prob_xtion[pxi].comb[ci].choice
      	); 
      	fprintf(RED_OUT, 
      	  "      in two probabilistic transition %1d and %1d\n", 
      	  bck_xtion_prob[prob_xtion[pxi].comb[ci].choice], pxi
      	); 
      	fflush(RED_OUT); 
      	exit(0); 
      } 
      bck_xtion_prob[prob_xtion[pxi].comb[ci].choice] = pxi; 
      tprob = tprob + prob_xtion[pxi].comb[ci].prob; 
    } 
    if (tprob > 1.0) { 
      fprintf(RED_OUT, "\nERROR: Illegal total probability %f of probabilistic transition %1d.\n", 
        tprob, pxi 
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  } 
  fprintf(RED_OUT, "\n%1d prob xtions\n", prob_xtion_count); 
  for (pxi = 0; pxi < prob_xtion_count; pxi++) { 
    fprintf(RED_OUT, "[%1d,%1d],%1d:", 
      prob_xtion[pxi].pi_lb, prob_xtion[pxi].pi_ub, prob_xtion[pxi].count
    ); 
    for (ci = 0; ci < prob_xtion[pxi].count; ci++) { 
      fprintf(RED_OUT, "(%f,%1d)", prob_xtion[pxi].comb[ci].prob, 
        prob_xtion[pxi].comb[ci].choice
      ); 
    } 
    fprintf(RED_OUT, "\n"); 
  } 
  fflush(RED_OUT); 
}
  /* input_xtion_probabilities() */ 



float	xi_prob(int pi, int xi) { 
  float	tprob = 1.0; 
  int	pxi, ci; 
  
  for (pxi = 0; pxi < prob_xtion_count; pxi++) { 
    if (   pi >= prob_xtion[pxi].pi_lb
        && pi <= prob_xtion[pxi].pi_ub
        ) { 
      for (ci = 0; ci < prob_xtion[pxi].count; ci++) { 
      	if (prob_xtion[pxi].comb[ci].choice == xi) {
      	  tprob = tprob * prob_xtion[pxi].comb[ci].prob; 
      	  break; 
      	} 
      } 
      if (ci < prob_xtion[pxi].count) { 
      	break; 
      } 	
    } 
  } 
  return(tprob); 
} 
  /* xi_prob() */ 


float	sxi_prob(int sxi) { 
  float	tprob = 1.0; 
  int	ipi; 
  
  for (ipi = 0; 
       ipi < red_query_sync_xtion_party_count(
               RED_USE_DECLARED_SYNC_XTION, sxi
             ); 
       ipi++
       ) { 
    tprob = tprob * xi_prob(
      red_query_sync_xtion_party_process(
        RED_USE_DECLARED_SYNC_XTION, sxi, ipi
      ), 
      red_query_sync_xtion_party_xtion(
        RED_USE_DECLARED_SYNC_XTION, sxi, ipi
      )
    ); 
  } 
  return(tprob); 
}
  /* sxi_prob() */ 


void	new_prob_sync_xtion(int sxi) { 
  struct prob_sync_xtion_link_type	*psxl; 
  
  psxl = (struct prob_sync_xtion_link_type *) 
    malloc(sizeof(struct prob_sync_xtion_link_type)); 
  psxl->next_prob_sync_xtion_link = prob_sync_xtion_list; 
  prob_sync_xtion_list = psxl; 
  prob_sync_xtion_count++; 

  psxl->count = 1; 
  psxl->choice_list = (struct discrete_choice_link_type *)
    malloc(sizeof(struct discrete_choice_link_type)); 
  psxl->choice_list->next_discrete_choice_link = NULL; 
  psxl->choice_list->prob = sxi_prob(sxi); 
  psxl->choice_list->choice = sxi; 
}
  /* new_prob_sync_xtion() */ 



int	sxi_prob_match(int sxi, struct prob_sync_xtion_link_type *psxl) {
  int	sxj, sxic, sxjc, ipi, pi, pj, xi, xj, flag_prob_sync_xtion; 
  
  sxj = psxl->choice_list->choice; 
  sxic = red_query_sync_xtion_party_count(RED_USE_DECLARED_SYNC_XTION, sxi); 
  sxjc = red_query_sync_xtion_party_count(RED_USE_DECLARED_SYNC_XTION, sxj);
  if (sxic != sxjc) { 
    return(FLAG_FALSE); 	
  } 
  flag_prob_sync_xtion = FLAG_FALSE; 
  for (ipi = 0; ipi < sxic; ipi++) { 
    pi = red_query_sync_xtion_party_process(
      RED_USE_DECLARED_SYNC_XTION, sxi, ipi
    ); 
    pj = red_query_sync_xtion_party_process(
      RED_USE_DECLARED_SYNC_XTION, sxj, ipi
    ); 
    if (pi != pj) 
      return(FLAG_FALSE); 
    xi = red_query_sync_xtion_party_xtion(
      RED_USE_DECLARED_SYNC_XTION, sxi, ipi
    ); 
    xj = red_query_sync_xtion_party_xtion(
      RED_USE_DECLARED_SYNC_XTION, sxj, ipi
    ); 
    if (bck_xtion_prob[xi] != bck_xtion_prob[xj]) 
      return(FLAG_FALSE); 
    else if (   bck_xtion_prob[xi] == FLAG_NOT_A_PROB_XTION 
             && xi != xj
             ) 
      return(FLAG_FALSE); 
    else if (bck_xtion_prob[xi] != FLAG_NOT_A_PROB_XTION) 
      flag_prob_sync_xtion = FLAG_TRUE; 
  } 
  if (flag_prob_sync_xtion) 
    return(FLAG_TRUE); 
  else 
    return(FLAG_FALSE); 
}
  /* sxi_prob_match() */ 




void	prepare_sync_xtion_probabilities(char *prob_fname) {
  int					sxi, psxi, ci; 
  struct prob_sync_xtion_link_type	*psxl, *ppsxl; 
  struct discrete_choice_link_type	*cl, *pcl; 
  
  input_xtion_probabilities(prob_fname); 
  
  prob_sync_xtion_list = NULL; 
  prob_sync_xtion_count = 0; 
  new_prob_sync_xtion(0); 
  
  for (sxi = 1; 
       sxi < red_query_sync_xtion_count(RED_USE_DECLARED_SYNC_XTION)-1
       // Note the last sync_xiton index is for the bulk transition
       ; 
       sxi++
       ) { 
    for (psxl = prob_sync_xtion_list; 
         psxl; 
         psxl = psxl->next_prob_sync_xtion_link
         ) { 
      if (sxi_prob_match(sxi, psxl)) { 
      	psxl->count++; 
      	cl = (struct discrete_choice_link_type *) 
      	  malloc(sizeof(struct discrete_choice_link_type)); 
      	cl->next_discrete_choice_link = psxl->choice_list; 
      	psxl->choice_list = cl; 
      	cl->choice = sxi; 
      	cl->prob = sxi_prob(sxi); 
      	break; 
      }    	
    } 
    if (!psxl) { 
      new_prob_sync_xtion(sxi); 
    } 
  } 
  
  /* Now copy all prob sync xtions to a static array. 
   */ 
  prob_sync_xtion = (struct prob_sync_xtion_type *) 
    malloc(prob_sync_xtion_count * sizeof(struct prob_sync_xtion_type)); 
  for (psxi = prob_sync_xtion_count-1, psxl = prob_sync_xtion_list; 
       psxi >= 0; 
       psxi--, psxl = psxl->next_prob_sync_xtion_link
       ) { 
    prob_sync_xtion[psxi].count = psxl->count; 
    prob_sync_xtion[psxi].comb = (struct discrete_choice_type *) 
      malloc(psxl->count * sizeof(struct discrete_choice_type)); 
    for (ci = psxl->count-1, cl = psxl->choice_list; 
         ci >= 0; 
         ci--, cl = cl->next_discrete_choice_link
         ) { 
      prob_sync_xtion[psxi].comb[ci].prob = cl->prob; 
      prob_sync_xtion[psxi].comb[ci].choice = cl->choice;    	
    } 
    for (cl = psxl->choice_list; cl; ) { 
      pcl = cl; 
      cl = cl->next_discrete_choice_link; 
      free(pcl); 
    } 
  } 
  /* Now free the dynamic list for prob sync xtions.
   */ 
  for (psxl = prob_sync_xtion_list; psxl; ) { 
    ppsxl = psxl; 
    psxl = psxl->next_prob_sync_xtion_link; 
    free(ppsxl); 	
  } 
  
  free(bck_xtion_prob); 
  
  red_print_sync_xtion_compositions(); 
  
  fprintf(RED_OUT, "\n%1d probabilistic sync xtions:\n", 
    prob_sync_xtion_count
  ); 
  for (psxi = 0; psxi < prob_sync_xtion_count; psxi++) { 
    fprintf(RED_OUT, "%2d,%1d:", psxi, prob_sync_xtion[psxi].count); 
    for (ci = 0; ci < prob_sync_xtion[psxi].count; ci++) { 
      fprintf(RED_OUT, "(%f,%1d)", 
        prob_sync_xtion[psxi].comb[ci].prob, 
        prob_sync_xtion[psxi].comb[ci].choice
      ); 
    } 
    fprintf(RED_OUT, "\n"); 
  } 
  fflush(RED_OUT); 
  
//  print_psx8c(-1, -2, -2); 
}
  /* prepare_sync_xtion_probabilities() */ 



int	check_float_no_overlap(redgram d, float lb, float ub) {
  int	ci; 
  float	clb, cub; 
  
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    clb = red_query_diagram_float_arc_lb(d, ci); 
    cub = red_query_diagram_float_arc_ub(d, ci); 
    if (clb > ub) 
      return(FLAG_TRUE); 
    else if (cub >= lb) 
      return(FLAG_FALSE); 
  } 
  return(FLAG_TRUE); 
}
  /* check_float_no_overlap() */ 




int	count_prob_multiply = 0; 

redgram prob_multiply(redgram d, float mult) { 
  redgram	child, result; 
  int		ci; 
  float		clb, cub; 
  
  result = red_false(); 
/*
  fprintf(RED_OUT, "\nprob_multiply (%1d), mult = %f:\n", 
    ++count_prob_multiply, 
    mult
  ); 
  red_print_diagram(d); 
  fflush(RED_OUT); 
*/  
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    child = red_query_diagram_child(d, ci); 
    clb = red_query_diagram_float_arc_lb(d, ci); 
    cub = red_query_diagram_float_arc_ub(d, ci); 
    /* 
    if (clb == 0.0) { 
      fprintf(RED_OUT, "\nERROR: zero probability in dx.\n"); 
      fflush(RED_OUT); 
      exit(0); 	
    } 
    else 
    */ 
    if (clb != cub) { 
      fprintf(RED_OUT, 
        "\nERROR in prob_multiply(): non-singleton probability [%f,%f] in dx.\n", 
        clb, cub 
      ); 
      fflush(RED_OUT); 
      exit(0); 	
    } 
    result = red_or(result, red_diagram_float(
      child, red_var_prob(), clb*mult, cub*mult 
    ) ); 
  } 
  return(result); 
} 
  /* prob_multiply() */ 
  




int	count_prob_add = 0; 

int 	count_prob_add_one = 0; 

int	count_prob_lift = 0; 

redgram prob_lift(redgram d, float lb, float ub) { 
  redgram	child, result; 
  int		ci; 
  float		clb, cub, clb_result, cub_result; 
  
//  fprintf(RED_OUT, "\np-lift (%1d)\n", ++count_prob_lift); 

  if (lb < 0.0 || ub > 1 || lb > ub) { 
    return(red_false()); 	
  } 
  
  result = red_false(); 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    if (count_prob_add == 497) { 
      fprintf(RED_OUT, "\n    dx ci = %1d\n", ci); 
    } 
    child = red_query_diagram_child(d, ci); 
    clb = red_query_diagram_float_arc_lb(d, ci); 
    cub = red_query_diagram_float_arc_ub(d, ci); 
    /*
    if (clb == 0.0) { 
      fprintf(RED_OUT, "\nERROR: zero probability in dx.\n"); 
      fflush(RED_OUT); 
      exit(0); 	
    } 
    else 
    */
    if (clb != cub) { 
      fprintf(RED_OUT, 
        "\nERROR in prob_lift(): non-singleton probability [%f,%f] in dx.\n", 
        clb, cub 
      ); 
      fflush(RED_OUT); 
      exit(0); 	
    } 
    cub_result = cub + ub; 
    if (cub_result > 1.0) { 
      fprintf(RED_OUT, 
        "\nERROR: probability ub addition of %f and %f out of bound 1.0.\n", 
        cub, ub
      ); 
      red_print_graph(child); 
      fflush(RED_OUT);
      cub_result = 1.0;  
//      exit(0); 
    } 
    else if (cub_result < 0.0) { 
      fprintf(RED_OUT, 
        "\nERROR: probability ub addition of %f and %f out of bound 0.0.\n", 
        cub, ub
      ); 
      red_print_graph(child); 
      fflush(RED_OUT);
      cub_result = 0.0;  
//      exit(0); 
    } 
    clb_result = clb + lb; 
    if (clb_result > 1.0) { 
      fprintf(RED_OUT, 
        "\nERROR: probability lb addition of %f and %f out of bound 1.0.\n", 
        clb, lb
      ); 
      red_print_graph(child); 
      fflush(RED_OUT); 
      clb_result = 1.0; 
//      exit(0); 
    } 
    else if (clb_result < 0.0) { 
      fprintf(RED_OUT, 
        "\nERROR: probability lb addition of %f and %f out of bound 0.0.\n", 
        clb, lb
      ); 
      red_print_graph(child); 
      fflush(RED_OUT); 
      clb_result = 0.0; 
//      exit(0); 
    } 
    result = red_or(result, red_diagram_float(
      child, red_var_prob(), clb_result, cub_result 
    ) ); 
  } 
  return(result); 
} 
  /* prob_lift() */ 
  



/* This procedure works under the assumption that all probability 
 * sections of dx are disjoint. 
 * The root of dy is not prob.  
 * lb and ub are the probability bounds of dy. 
 * dx is with root prob.  
 
 * This procedure may cause garbage collection. 
 * So please protect all the important diagrams outside this procedure. 
 */ 
redgram prob_add_one(redgram dx, redgram dy, float lb, float ub) { 
  redgram	child, result, conj, disjx, disjy; 
  int		ci; 
  float		clb, cub; 
  
/*
  fprintf(RED_OUT, "\ncount prob add one %1d.\n", 
    ++count_prob_add_one
  ); 
  fflush(RED_OUT); 
*/  
  if (lb != ub) { 
    fprintf(RED_OUT, 
      "\nERROR in prob_add_one(): non-singleton probability [%f,%f] in dy.\n", 
      lb, ub
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  }
/*
  else if (lb == 0.0) { 
    fprintf(RED_OUT, "\nERROR: zero probability in dy.\n"); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
*/
  disjy = dy; 
  for (ci = 0; 
       disjy != red_false() && ci < red_query_diagram_child_count(dx); 
       ci++
       ) 
    disjy = red_subtract(disjy, red_query_diagram_child(dx, ci)); 
  disjy = red_diagram_float(disjy, red_var_prob(), lb, ub); 
  disjx = red_subtract(dx, dy); 
  conj = red_and(dx, dy); 

  conj = prob_lift(conj, lb, ub); 
  result = red_or(disjx, disjy); 
  result = red_or(result, conj); 
  
  return(result); 
} 
  /* prob_add_one() */ 
  




/* Note that the following routine are all based on the assumption that 
   no probability zero wil be used. 
   Moreover, all probablity intervals are singleton. 
 */ 
redgram	prob_add(redgram dx, redgram dy) {
  redgram	result; 
  int		ci; 

//  fprintf(RED_OUT, "\np-add %1d\n", ++count_prob_add); 
    
  if (dx == red_false()) 
    return(dy); 
  else if (dy == red_false()) 
    return(dx); 
  else if (red_query_diagram_root_var(dx) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal root variable %1d:%s of probability diagram dx.\n", 
      red_query_diagram_root_var(dx), 
      red_query_var_name(red_query_diagram_root_var(dx))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 	
  else if (red_query_diagram_root_var(dy) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "ERROR: Illegal root variable %1d:%s of probability diagram dy.\n", 
      red_query_diagram_root_var(dy), 
      red_query_var_name(red_query_diagram_root_var(dy))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  for (ci = 0; ci < red_query_diagram_child_count(dy); ci++) { 
    dx = prob_add_one(dx, red_query_diagram_child(dy, ci), 
      red_query_diagram_float_arc_lb(dy, ci), 
      red_query_diagram_float_arc_ub(dy, ci)
    );  	
  } 
  return(red_norm(dx, RED_NORM_ZONE_CLOSURE_EQ)); 
}
  /* prob_add() */ 





/* Note that the following routine are all based on the assumption that 
   no probability zero wil be used. 
   Moreover, all probablity intervals are singleton. 
 */ 
void	check_size_of_dd(redgram dx, redgram dy) {
  int	sx, sy;  
  
  if (dx) 
    sx = red_query_diagram_child_count(dx); 
  else 
    sx = 0; 
  if (dy) 
    sy = red_query_diagram_child_count(dy); 
  else 
    sy = 0; 
  if (sx < sy) 
    sx = sy; 
  if (size_of_dd < sx) { 
    if (ddx != NULL) { 
      free(ddx); 
      free(ddy); 
    } 
    size_of_dd = 2*sx; 
    ddx = (redgram *) malloc(size_of_dd * sizeof(redgram)); 
    ddy = (redgram *) malloc(size_of_dd * sizeof(redgram)); 
  } 
}
  /* check_size_of_dd() */ 



redgram	prob_self_max(redgram d) { 
  int		ci, cj, flag; 
  redgram	result, child; 
  
  if (d == red_false()) 
    return(d); 
  else if (red_query_diagram_root_var(d) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal root variable %1d:%s of probability diagram d.\n", 
      red_query_diagram_root_var(d), 
      red_query_var_name(red_query_diagram_root_var(d))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  
  check_size_of_dd(d, NULL); 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    ddx[ci] = red_query_diagram_child(d, ci); 
  }
  flag = 0; 
  for (ci = red_query_diagram_child_count(d)-1; ci>0; ci--) { 
    if (ddx[ci] == red_false())
      continue;  
    for (cj = 0; cj < ci; cj++) { 
      child = red_subtract(ddx[cj], ddx[ci]); 
      if (child != ddx[cj]) { 
      	flag = 1; 
      	ddx[cj] = child;  
    } }
  }
  if (!flag) {
    return(d); 
  }
  result = red_false(); 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    if (ddx[ci] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddx[ci], red_var_prob(), 
        red_query_diagram_float_arc_lb(d, ci), 
        red_query_diagram_float_arc_lb(d, ci)
    ) ); 
  }

  return(red_norm(result, RED_NORM_ZONE_CLOSURE_EQ)); 
} 
  /* prob_self_max() */ 





redgram	prob_self_min(redgram d) { 
  int		ci, cj, flag; 
  redgram	result, child, conj; 
  
  if (d == red_false()) 
    return(d); 
  else if (red_query_diagram_root_var(d) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal root variable %1d:%s of probability diagram d.\n", 
      red_query_diagram_root_var(d), 
      red_query_var_name(red_query_diagram_root_var(d))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  
  check_size_of_dd(d, NULL); 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    ddx[ci] = red_query_diagram_child(d, ci); 
  }
  flag = 0; 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    if (ddx[ci] == red_false())
      continue;  
    for (cj = ci+1; cj < red_query_diagram_child_count(d); cj++) { 
      child = red_subtract(ddx[cj], ddx[ci]); 
      if (child != ddx[cj]) { 
      	flag = 1; 
      	conj = red_and(ddx[ci], ddx[cj]); 
      	if (conj != red_false()) { 
      	  fprintf(RED_OUT, 
      	    "\nSelf min effective at (%1d/%1d)p=%f and (%1d/%1d)p=%f with:\n", 
      	    ci, red_query_diagram_child_count(d), 
      	    red_query_diagram_float_arc_lb(d, ci), 
      	    cj, red_query_diagram_child_count(d), 
      	    red_query_diagram_float_arc_lb(d, cj)
      	  );  
      	  red_print_diagram(conj); 
      	}
      	else 
      	  fprintf(RED_OUT, 
      	    "\nSelf min false effective at (%1d/%1d)p=%f and (%1d/%1d)p=%f with:\n", 
      	    ci, red_query_diagram_child_count(d), 
      	    red_query_diagram_float_arc_lb(d, ci), 
      	    cj, red_query_diagram_child_count(d), 
      	    red_query_diagram_float_arc_lb(d, cj)
      	  );  
      	fflush(RED_OUT); 
      	
      	ddx[cj] = child;  
    } }
  }
  if (!flag) {
    return(d);
  } 
  result = red_false(); 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    if (ddx[ci] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddx[ci], red_var_prob(), 
        red_query_diagram_float_arc_lb(d, ci), 
        red_query_diagram_float_arc_lb(d, ci)
    ) ); 
  }

  return(red_norm(result, RED_NORM_ZONE_CLOSURE_EQ)); 
} 
  /* prob_self_min() */ 





redgram	prob_max(redgram dx, redgram dy) {
  redgram	result, childx, childy; 
  int		cix, ciy; 
  float		px, py; 
  
  if (dx == red_false()) 
    return(dy); 
  else if (dy  == red_false()) 
    return(dx); 
  else if (red_query_diagram_root_var(dx) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal root variable %1d:%s of probability diagram dx.\n", 
      red_query_diagram_root_var(dx), 
      red_query_var_name(red_query_diagram_root_var(dx))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 	
  else if (red_query_diagram_root_var(dy) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "ERROR: Illegal root variable %1d:%s of probability diagram dy.\n", 
      red_query_diagram_root_var(dy), 
      red_query_var_name(red_query_diagram_root_var(dy))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
/*
  print_psx8c(-2000, -2000, 1000001); 
  fprintf(RED_OUT, "\nprob_max(): dx child count = %1d.\n", 
    red_query_diagram_child_count(dx)  
  ); 
  if (count_px8c > 8180) 
    red_print_diagram(dx); 
*/

  check_size_of_dd(dx, dy); 
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    ddx[cix] = red_query_diagram_child(dx, cix); 
  }
/*
  print_psx8c(-2000, -2000, 1000002); 
  fprintf(RED_OUT, "\nprob_max(): dy child count = %1d.\n", 
    red_query_diagram_child_count(dy)  
  ); 
  if (count_px8c > 8180) 
    red_print_diagram(dy); 
*/
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    ddy[ciy] = red_query_diagram_child(dy, ciy); 
  }
//  print_psx8c(-2000, -2000, 1000003); 
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    px = red_query_diagram_float_arc_lb(dx, cix); 
//    print_psx8c(-2000, -2000, 1000004); 
    for (ciy = 0; 
            ciy < red_query_diagram_child_count(dy)
         && red_query_diagram_float_arc_lb(dy, ciy) < px; 
         ciy++
         ) { 
      ddy[ciy] = red_subtract(ddy[ciy], ddx[cix]); 
    }
  }
//  print_psx8c(-2000, -2000, 1000005); 
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    py = red_query_diagram_float_arc_lb(dy, ciy); 
//    print_psx8c(-2000, -2000, 1000006); 
    for (cix = 0; 
            cix < red_query_diagram_child_count(dx)
         && red_query_diagram_float_arc_lb(dx, cix) < py; 
         cix++
         ) { 
      ddx[cix] = red_subtract(ddx[cix], ddy[ciy]); 
    }
  } 
  result = red_false(); 
//  print_psx8c(-2000, -2000, 1000007); 
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    if (ddx[cix] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddx[cix], red_var_prob(), 
        red_query_diagram_float_arc_lb(dx, cix), 
        red_query_diagram_float_arc_lb(dx, cix)
    ) ); 
  }
//  print_psx8c(-2000, -2000, 1000008); 
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    if (ddy[ciy] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddy[ciy], red_var_prob(), 
        red_query_diagram_float_arc_lb(dy, ciy), 
        red_query_diagram_float_arc_lb(dy, ciy)
    ) ); 
  }
//  print_psx8c(-2000, -2000, 1000009); 

  return(red_norm(result, RED_NORM_ZONE_CLOSURE_EQ)); 
}
  /* prob_max() */ 
  



redgram	prob_min(redgram dx, redgram dy) {
  redgram	result, childx, childy; 
  int		cix, ciy; 
  float		px, py; 
  
  if (dx == red_false()) 
    return(dy); 
  else if (dy  == red_false()) 
    return(dx); 
  else if (red_query_diagram_root_var(dx) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal root variable %1d:%s of probability diagram dx.\n", 
      red_query_diagram_root_var(dx), 
      red_query_var_name(red_query_diagram_root_var(dx))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 	
  else if (red_query_diagram_root_var(dy) != red_var_prob()) { 
    fprintf(RED_OUT, 
      "ERROR: Illegal root variable %1d:%s of probability diagram dy.\n", 
      red_query_diagram_root_var(dy), 
      red_query_var_name(red_query_diagram_root_var(dy))
    ); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
/*
  fprintf(RED_OUT, "\n>>>> Prob min, dx:\n"); 
  red_print_diagram(dx); 
  fprintf(RED_OUT, "\n>>>> Prob min, dy:\n"); 
  red_print_diagram(dy); 
*/
  check_size_of_dd(dx, dy); 
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    ddx[cix] = red_query_diagram_child(dx, cix); 
  }
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    ddy[ciy] = red_query_diagram_child(dy, ciy); 
  }
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    px = red_query_diagram_float_arc_lb(dx, cix); 
    for (ciy = red_query_diagram_child_count(dy)-1; 
         ciy >= 0 && red_query_diagram_float_arc_lb(dy, ciy) > px; 
         ciy--
         ) { 
      ddy[ciy] = red_subtract(ddy[ciy], ddx[cix]); 
    }
  }
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    py = red_query_diagram_float_arc_lb(dy, ciy); 
    for (cix = red_query_diagram_child_count(dx)-1; 
         cix >= 0 && red_query_diagram_float_arc_lb(dx, cix) > py; 
         cix--
         ) { 
      ddx[cix] = red_subtract(ddx[cix], ddy[ciy]); 
    }
  } 
  result = red_false(); 
  for (cix = 0; cix < red_query_diagram_child_count(dx); cix++) { 
    if (ddx[cix] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddx[cix], red_var_prob(), 
        red_query_diagram_float_arc_lb(dx, cix), 
        red_query_diagram_float_arc_ub(dx, cix)
    ) ); 
  }
  for (ciy = 0; ciy < red_query_diagram_child_count(dy); ciy++) { 
    if (ddy[ciy] == red_false()) 
      continue; 
    result = red_or(result, 
      red_diagram_float(ddy[ciy], red_var_prob(), 
        red_query_diagram_float_arc_lb(dy, ciy), 
        red_query_diagram_float_arc_ub(dy, ciy)
    ) ); 
  }

  return(red_norm(result, RED_NORM_ZONE_CLOSURE_EQ)); 
}
  /* prob_min() */ 
  



/**************************************************************
 *
 2012/10/14 (the date is randomly written):
 
    The major challenge for the reachability analysis from s happens 
    when s is dominated by an infinite cycle of approaching 
    a probability limit. 
        
    One interesting thing about s is that the probability only 
    increase in one iteration of the limit approaching cycle. 
    Thus it does not affect the max operation.  
    
    However when we want to compute the minimum probability, 
    then the limit approaching cycle posts a difficulty regarding 
    whether we need to keep the probability for s at an iteration. 
    
     1. When the probability of s is dominated by a limit-approaching cycle,
        then due to non-monotonically increasing feature of the 
        probability values, it is apparent that we should not keep the 
        probability value of s at an iteration for the the min operation.  
        
     2. When the probability of s is not dominated by a limit-approaching 
        cycle, then we want to keep the probability value 
        of s at each iteration for the min operations. 
   
    Thus the problem is whether we can decide a unified approach to 
    handle both min and max probability.   
    


 2013/07/15 (This is an exact date):
    For minimizer probability: 
      . The ngoal_unbounded can choose to be zero forever. 
      . So initially, ngoal_unbounded is assigned probability zero 
        and goal is assigned probability one. 
      . Then in each iteration, we calculate the minimal probability 
        of all states in INV - red_or(red_stack(ngoal_unbounded), 
                                      red_stack(goal)
                                      ); 
        For this purpose, we let 
          unprob_fixed = red_or(red_stack(ngoal_unbounded), red_stack(goal)) 
          and 
          prob_fixed = red_or(prob(red_stack(ngoal_unbounded),0.0,0.0), 
            prob(red_stack(goal), 1.0, 1.0)
          ); 
        Initially, the probability of all states in INV - unprob_fixed 
          is zero. 
          
    For maximizer probability: 
      . The ngoal_unbounded CANNOT choose to be zero forever. 
      . So initially, ngoal_unbounded is assigned probability zero 
        and goal is assigned probability one. 
      . Then in each iteration, we calculate the minimal probability 
        of all states in INV - red_stack(goal); 
        For this purpose, we let 
          unprob_fixed = red_stack(goal) 
          and 
          prob_fixed = prob(red_stack(goal), 1.0, 1.0); 

        Initially, the probability of all states in INV - unprob_fixed 
          is zero. 
 */ 
 
float get_init_prob(
  redgram	d 
) { 
  d = red_norm(
    red_and(red_query_diagram_initial(), d), RED_NORM_ZONE_CLOSURE_EQ
  ); 
  if (d == red_false()) 
    return(0.0); 
  else if (red_query_diagram_root_var(d) != red_var_prob()) { 
    fprintf(RED_OUT, "\nERROR: Illegal reachability root variable.\n"); 
    red_print_diagram(d); 
    fflush(RED_OUT); 
    exit(0); 	
  } 
  else 
    return(red_query_diagram_float_arc_lb(d, 0)); 
}
  /* get_init_prob() */ 


int	it_continue(int it, int reachp, int reach) { 
  redgram	rp, r; 
  int		cc, ccp, ci; 
  
  r = red_stack(reach); 
  rp = red_stack(reachp); 
  if (   red_query_diagram_root_var(r) != red_var_prob()
      || red_query_diagram_root_var(r) != red_query_diagram_root_var(rp) 
      ) 
    return(1); 

  cc = red_query_diagram_child_count(r); 
  ccp = red_query_diagram_child_count(rp); 
  if (cc != ccp) 
    return(1); 
  
  for (ci = 0; ci < cc; ci++) { 
    if (red_query_diagram_child(r,ci) != red_query_diagram_child(rp,ci))
      return(1); 
    else if (fabs(red_query_diagram_float_arc_lb(r,ci)
                  - red_query_diagram_float_arc_lb(rp,ci)
                  ) > PRECISION_THRESHOLD
             ) 
      return(1);    
  } 
  return(0); 
} 
  /* it_continue() */ 



int	check_prob_overlap(redgram d) { 
  int		ci, cj, flag; 
  redgram	conj; 
  
  flag = 0; 
  for (ci = 0; ci < red_query_diagram_child_count(d); ci++) { 
    for (cj = ci+1; cj < red_query_diagram_child_count(d); cj++) { 
      conj = red_and(
        red_query_diagram_child(d,ci), 
        red_query_diagram_child(d,cj)
      ); 
      if (conj != red_false()) { 
      	flag = 1; 
      	fprintf(RED_OUT, 
      	  "\nCaught suspicious precondition overlapping ci=%1d,%1d.\n", 
      	  ci, cj 
      	); 
      	fprintf(RED_OUT, "conjunction:\n"); 
      	red_print_graph(conj); 
      	fprintf(RED_OUT, "d:\n"); 
      	red_print_graph(d); 
  } } } 
  return(flag); 
}
  /* check_prob_overlap() */ 



int	check_qtrace(int i, int sxi) {
  if (   (i == 1 && sxi == 75) 
      || (i == 2 && sxi == 65) 
      || (i == 3 && sxi == 74) 
      || (i == 4 && sxi >= 15 && sxi <= 30) 
      || (i == 5 && sxi == 73) 
      || (i == 6 && sxi == 7) 
      || (i == 7 && sxi == 73) 
      || (i == 8 && sxi == 3) 
      || (i == 9 && sxi == 73) 
      || (i == 10 && sxi == 63) 
      || (i == 11 && sxi == 1) 
      || (i == 12 && sxi == 32) 
      || (i == 13 && sxi == 76) 
      || (i == 14 && sxi == 68) 
      || (i == 15 && sxi == 62) 
      ) 
    return(1); 
  else 
    return(0); 
}
  /* check_qtrace() */ 



redgram	dd_qtrace(redgram d, int i, int sxi) {
  if (i == 1 && sxi == 75) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==4&&cd1@(2)==1&&s2@(3)==1&&cd2@(3)==4"
    ) ) ); 
  }
  else if (i == 2 && sxi == 65) {
    return(red_and(d, red_diagram(
      "b@(1)==0&&s1@(2)==4&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==4"
    ) ) ); 
  }
  else if (i == 3 && sxi == 74) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==4"
    ) ) ); 
  }
  else if (i == 4 && sxi >= 15 && sxi<=30) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==4"
    ) ) ); 
  }
  else if (i == 5 && sxi == 73) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==3"
    ) ) ); 
  }
  else if (i == 6 && sxi == 7) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==3"
    ) ) ); 
  }
  else if (i == 7 && sxi == 73) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==2"
    ) ) ); 
  }
  else if (i == 8 && sxi == 3) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==2"
    ) ) ); 
  }
  else if (i == 9 && sxi == 73) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==1"
    ) ) ); 
  }
  else if (i == 10 && sxi == 63) {
    return(red_and(d, red_diagram(
      "b@(1)==0&&s1@(2)==3&&cd1@(2)==1&&s2@(3)==3&&cd2@(3)==1"
    ) ) ); 
  } 
  else if (i == 11 && sxi == 1) {
    return(red_and(d, red_diagram(
      "b@(1)==0&&s1@(2)==3&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==1"
    ) ) ); 
  } 
  else if (i == 12 && sxi == 32) {
    return(red_and(d, red_diagram(
      "b@(1)==0&&s1@(2)==2&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==1"
    ) ) ); 
  } 
  else if (i == 13 && sxi == 76) {
    return(red_and(d, red_diagram(
      "b@(1)==2&&s1@(2)==1&&cd1@(2)==0&&s2@(3)==1&&cd2@(3)==0"
    ) ) ); 
  } 
  else if (i == 14 && sxi == 68) {
    return(red_and(d, red_diagram(
      "b@(1)==1&&s1@(2)==1&&cd1@(2)==0&&s2@(3)==0&&cd2@(3)==0"
    ) ) ); 
  } 
  else if (i == 15 && sxi == 62) {
    return(red_and(d, red_diagram(
      "b@(1)==0&&s1@(2)==0&&cd1@(2)==0&&s2@(3)==0&&cd2@(3)==0"
    ) ) ); 
  } 
  else 
    return(d);  
}
  /* dd_qtrace() */ 


redgram dd_ini(redgram d) { 
  return(red_and(d, red_diagram(
    "b@(1)==0&&s1@(2)==0&&cd1@(2)==0&&s2@(3)==0&&cd2@(3)==0"
  ) ) ); 
}
  /* dd_ini() */ 





redgram	prob_reach_analysis(int task_type, redgram dgoal) {
  int		prob_fix, unprob_fix, unprob_unfix, ngoal, 
  		pic, reach, reachp, unprob, psxi, ci, 
  		prob_pre, pre; 
  redgram 	dngoal, d_time_bounded, d_time_unbounded, dreach; 
  
  ngoal = red_push(red_not(dgoal)); 

  // reset all timeless nongoal states to probability zero.
  switch (status_max_min) { 
  case FLAG_MAXIMIZER:  
  case FLAG_MINIMIZER:  
    unprob_fix = red_push(red_and(
      red_query_diagram_enhanced_global_invariance(), dgoal
    ) ); 
    unprob_unfix = red_push(red_subtract(
      red_query_diagram_enhanced_global_invariance(), dgoal  
    ) ); 
    prob_fix = red_push(red_diagram_float(red_stack(unprob_fix), 
      red_var_prob(), 1.0, 1.0 
    ) );
    break; 
  case FLAG_MINIMIZER_TIMED_IDLE:  
    red_timeless(red_query_diagram_enhanced_global_invariance(), 
      &d_time_unbounded, &d_time_bounded
    ); 
    dngoal = red_subtract(d_time_unbounded, dgoal); 
    unprob_fix = red_push(red_or(
      red_and(dgoal, red_query_diagram_enhanced_global_invariance()), 
      dngoal
    ) ); 
    unprob_unfix = red_push(red_subtract(
      red_query_diagram_enhanced_global_invariance(), 
      red_stack(unprob_fix)  
    ) ); 
    prob_fix = red_push(red_or(
      red_diagram_float(
        red_and(dgoal, red_query_diagram_enhanced_global_invariance()), 
        red_var_prob(), 1.0, 1.0
      ), 
      red_diagram_float(dngoal, red_var_prob(), 0.0, 0.0)  
    ) );
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: prob_reach_analysis(), Illegal maximum/minimum option %1d.\n", 
      status_max_min
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }  
  dreach = red_and(red_query_diagram_enhanced_global_invariance(), 
    red_stack(unprob_unfix)
  ); 
  reach = red_push(red_diagram_float(red_true(), red_var_prob(), 1.0, 1.0)); 
  reachp = red_push(red_stack(prob_fix)); 
  
  for (pic = 1; it_continue(pic, reachp, reach); pic++) { 
    red_set_stack(reach, red_stack(reachp)); 
    red_set_stack(reachp, red_false()); 
    for (psxi = 1; psxi < prob_sync_xtion_count; psxi++) { 
///*
      fprintf(RED_OUT, "\n===[(%1d), psxi %1d with %1d choices]=====================\n", 
        pic, psxi, prob_sync_xtion[psxi].count
      ); 
//*/
      prob_pre = red_push(red_false()); 
      for (ci = 0; ci < prob_sync_xtion[psxi].count; ci++) { 
///*
      	fprintf(RED_OUT, 
      	  "$$$[(%1d), psx %1d, choice %1d is sxi=%1d]$$$$$$$$$$$$$$$$$$$$$$\n", 
      	  pic, psxi, ci, prob_sync_xtion[psxi].comb[ci].choice 
      	); 
      	fflush(RED_OUT); 
      	if (check_qtrace(pic,prob_sync_xtion[psxi].comb[ci].choice)) { 
      	  red_print_sync_xtion_lines(prob_sync_xtion[psxi].comb[ci].choice); 
//      	  red_print_graph(red_stack(reach)); 
      	  fflush(RED_OUT); 
      	} 
//*/
      	pre = red_push(red_sync_xtion_bck(red_stack(reach), 
      	  red_query_diagram_enhanced_global_invariance(), 
      	  RED_USE_DECLARED_SYNC_XTION, 
      	  prob_sync_xtion[psxi].comb[ci].choice, 
      	  task_type, 
      	  RED_ALL_ROLES, 		// flag_game_roles,  
	  RED_TIME_PROGRESS, 		// flag_time_progress, 
	  RED_NORM_ZONE_CLOSURE_EQ, 	// flag_normality, 
	  RED_NO_ACTION_APPROX, 	// flag_action_approx, 
	  RED_NO_REDUCTION_INACTIVE, 	// flag_reduction, 
	  RED_NOAPPROX, 		// flag_state_approx, 
	  RED_NO_SYMMETRY, 		// flag_symmetry, 
	    RED_TIME_PROGRESS_ANALYSIS_ADVANCED
	  | RED_TIME_PROGRESS_ADAPTIVE_SHARED_SPLIT_CONVEXITIES
	  | RED_TIME_TCONVEXITY_SHARED_PARTITIONS
	  	// flag_experiment 
      	) ); 
/*
      	if (check_qtrace(pic,prob_sync_xtion[psxi].comb[ci].choice)) { 
          fprintf(RED_OUT, 
      	    "-----((%1d), psxi %1d, %f, sxi %1d, after pre)-----------\n", 
      	    pic, psxi, 
      	    prob_sync_xtion[psxi].comb[ci].prob, 
      	    prob_sync_xtion[psxi].comb[ci].choice
      	  ); 
      	  red_print_diagram(dd_qtrace(red_stack(pre), pic, 
      	    prob_sync_xtion[psxi].comb[ci].choice
      	  ) ); 
      	}
*/
      	red_set_stack(pre, red_and(red_stack(pre), red_stack(unprob_unfix))); 
/* The following commented code can never be used with the assumption 
that all zones are disjoint. 

        switch (status_max_min) { 
        case FLAG_MAXIMIZER:  
          red_set_stack(pre, prob_self_max(red_stack(pre))); 
          break; 
        case FLAG_MINIMIZER: 
        case FLAG_MINIMIZER_TIMED_IDLE:  
          red_set_stack(pre, prob_self_min(red_stack(pre))); 
          break; 
        } 
*/
      	red_set_stack(pre, prob_multiply(
      	  red_stack(pre), prob_sync_xtion[psxi].comb[ci].prob
      	) ); 
/*
      	fprintf(RED_OUT, 
      	  "-----((%1d), psxi %1d, %f, sxi %1d, after multiplication)-----------\n", 
      	  pic, psxi, 
      	  prob_sync_xtion[psxi].comb[ci].prob, 
      	  prob_sync_xtion[psxi].comb[ci].choice
      	); 
      	red_print_diagram(pre); 
      	fprintf(RED_OUT, "\n>>>>red_stack(prob_pre=%1d):\n", prob_pre); 
      	red_print_diagram(red_stack(prob_pre)); 
*/
/*        
      	if (check_qtrace(pic,prob_sync_xtion[psxi].comb[ci].choice)) { 
          fprintf(RED_OUT, 
      	    "-----((%1d), psxi %1d, %f, sxi %1d, after pre multiplication)-----------\n", 
      	    pic, psxi, 
      	    prob_sync_xtion[psxi].comb[ci].prob, 
      	    prob_sync_xtion[psxi].comb[ci].choice
      	  ); 
      	  red_print_diagram(dd_qtrace(red_stack(pre), pic, 
      	    prob_sync_xtion[psxi].comb[ci].choice
      	  ) ); 
      	}
*/
      	red_set_stack(prob_pre, 
      	  prob_add(red_stack(prob_pre), red_stack(pre))
      	); 
      	red_pop(pre); 
/*
      	if (check_qtrace(pic,prob_sync_xtion[psxi].comb[ci].choice)) { 
       	  fprintf(RED_OUT, 
      	    "-----((%1d), psxi %1d, %f, sxi %1d, after addition)-----------\n", 
      	    pic, psxi, 
      	    prob_sync_xtion[psxi].comb[ci].prob, 
      	    prob_sync_xtion[psxi].comb[ci].choice
      	  ); 
      	  red_print_diagram(dd_qtrace(red_stack(prob_pre), 
      	    pic, prob_sync_xtion[psxi].comb[ci].choice
      	  ) ); 
      	}
*/
      } 
//      print_psx8c(pic, psxi+1000, -1); 
      switch (status_max_min) { 
      case FLAG_MAXIMIZER:  
        red_set_stack(reachp, 
          prob_max(red_stack(prob_pre), red_stack(reachp))
        ); 
        break; 
      case FLAG_MINIMIZER: 
      case FLAG_MINIMIZER_TIMED_IDLE:  
        red_set_stack(reachp, 
          prob_min(red_stack(prob_pre), red_stack(reachp))
        ); 
        break; 
      default: 
        fprintf(RED_OUT, 
          "\nERROR: prob_reach_analysis(), Illegal maximum/minimum option %1d.\n", 
          status_max_min
        ); 
        fflush(RED_OUT); 
        exit(0); 
        break; 
      }  
      
      red_pop(prob_pre); 
/*
      fprintf(RED_OUT, 
        "***<(%1d), psxi %1d, after minimax>********************\n", 
        pic, psxi
      ); 
      red_print_diagram(red_stack(reachp)); 
*/
      red_garbage_collect(); 
    } 
/*
    if (pic == 4) {
      fprintf(RED_OUT, "+++(4), check fixpoint iteration++++++++++\n"); 
      red_print_graph(red_stack(reachp), 
        red_diagram( 
          "b@(1)==1&&s1@(2)==1&&cd1@(2)==1&&s2@(3)==2&&cd2@(3)==4"
      ) ); 
    }
*/ 
    red_set_stack(reachp, red_or(red_stack(reachp), red_stack(prob_fix))); 
///*
    fprintf(RED_OUT, 
      "+++(%1d), after a fixpoint iteration++++++++++++++++++++++++\n", 
      pic 
    ); 
/*
    red_print_diagram(red_stack(reachp)); 
    fprintf(RED_OUT, ">>%1d>> initial state probability >>:\n", pic); 
    red_print_diagram(dd_ini(red_stack(reachp))); 
*/
//*/
  } 
  fprintf(RED_OUT, "\nFixpoint reached after %1d iterations.\n", pic-1); 
  
  dgoal = red_stack(reachp); 
  red_pop(reachp); 
  red_pop(reach); 
  red_bop(prob_fix); 
  red_bop(unprob_unfix); 
  red_pop(unprob_fix); 
  red_pop(ngoal); 
  return(dgoal); 
}
  /* prob_reach_analysis() */ 
  




/**************************************************************
 *  An example of rule expansions. 
 
    (a+b,c+d)
    => (a(e+f,g+h)+b(i+j,k+l),c(m+n,o+p)+d(q+r,s+t))
    => ((ae+af,ag+ah)+(bi+bj,bk+bl), (cm+cn,co+cp)+(dq+dr,ds+dt))
    => (ae+af+bi+bj,ae+af+bk+bl,ag+ah+bi+bj,ag+ah+bk+bl, 
        cm+cn+dq+dr,cm+cn+ds+dt,co+cp+dq+dr,co+cp+ds+dt
        ) 
 
    There are several issues to investigate. 
    
      * how to normalize an action sequence with reset and assert operations.
      
         . assert m==c&& x<a; reset x; assert x==0; reset m; assert m==d; 
         
        In fact, there could be invariants respectively related 
        to m==c and m==d. 
        I think we can define what a clean action sequence is. 
        A clean action sequence does not have side effect. 
        That means, all value changes by the action sequence will 
        be forgotten after the sequence. 
        
        Two action sequences are the same if they have the same side effect. 

      * how to check the subsumption between two action sequences. 
      * how to deduce upper-bounds of probability limits from 
        iterations of fixpoints ? 
 */
struct eprob_sx_link_type	*BASE; 
int				FLAG_PRINT_INDEX = 0; 

void	print_salist(struct sync_action_link_type *salist) {
  struct sync_action_link_type	*sa;
  
  for (sa = salist; sa; sa = sa->next_sync_action_link) { 
    switch (sa->op) { 
    case SA_TIME: 
      if (FLAG_PRINT_INDEX) 
        fprintf(RED_OUT, "    sa%1d:T;\n", sa->index); 
      else 
        fprintf(RED_OUT, "    T;\n"); 
      break; 
    case SA_GUARD: 
      if (FLAG_PRINT_INDEX) 
        fprintf(RED_OUT, "    sa%1d:guard (", sa->index); 
      else 
        fprintf(RED_OUT, "    guard ("); 
//      fprintf(RED_OUT, "%1d:guard (", sa->index); 
      red_print_diagram_formula(sa->guard); 
      fprintf(RED_OUT, ");\n"); 
      break; 
    case SA_ERASE: 
      if (FLAG_PRINT_INDEX) 
        fprintf(RED_OUT, "    sa%1d:erase %s;\n", 
          sa->index, red_query_var_name(sa->var_index)
        ); 
      else 
        fprintf(RED_OUT, "    erase %s;\n", 
          red_query_var_name(sa->var_index)
        ); 
/*
      fprintf(RED_OUT, "%1d:erase %s; ", 
        sa->index, red_query_var_name(sa->var_index)
      ); 
*/
      break; 
    default: 
      fprintf(RED_OUT, "\nERROR, print_eprob_sx(), illegal op=%1d\n", sa->op); 
      fflush(RED_OUT); 
      exit(0); 	
    } 
  } 
  fprintf(RED_OUT, "\n"); 
}
  /* print_salist() */ 
  
  
void	print_echoice(struct echoice_link_type *ec) { 
  if (FLAG_PRINT_INDEX) 
    fprintf(RED_OUT, "  --ech%1d(%f)--->\n", ec->index, ec->prob); 
  else 
    fprintf(RED_OUT, "  --(%f)--->\n", ec->prob); 
  red_print_line(ec->red_postcond); 
  fprintf(RED_OUT, "\n  when (true) may \n"); 
  print_salist(ec->sync_action_list); 
}
  /* print_echoice() */ 



void	print_eprob_sx(struct eprob_sx_link_type *epsx) { 
  struct echoice_link_type	*ec; 
  int				ecc;  
  
  fprintf(RED_OUT, "----Probabilistic [%1d:%1d]----------------\njoint precond:\n", 
    epsx->index, epsx->count
  ); 
  red_print_line(epsx->joint_precond); 
  fprintf(RED_OUT, "\n");   
  for (ecc = 0, ec = epsx->echoice_list; 
       ec; 
       ecc++, ec = ec->next_echoice_link
       ) { 
    print_echoice(ec); 
  } 
  fprintf(RED_OUT, "\n"); 
} 
  /* print_eprob_sx() */  




void	print_eprob_sx_list(struct eprob_sx_link_type *list, int len) { 
  struct eprob_sx_link_type	*ep; 
  int				epc; 

  fprintf(RED_OUT, 
    "\n===[Expanded %1d probabilistic rules]====================\n", 
    len 
  ); 
  for (epc = 0, ep = list; ep; epc++, ep = ep->next_eprob_sx_link) { 
    fprintf(RED_OUT, "\n****eprob sx %1d******************************\n", 
      epc
    ); 
    print_eprob_sx(ep); 
  } 
} 
  /* print_eprob_sx_list() */  





/****************************************************************
 *  The following codes and procedures are for expansion of rules. 
 */ 
int				w_count_sal; 
struct sync_action_link_type	*w_sa_tail, w_dummy_sync_action; 

/* 0 for false while not zero for true. 
 */ 
int	check_sync_action_redundancy(
  int				op, 
  redgram			guard, 
  int				var_index
) {
  /* We should check whether the new action is redundant with 
     respect to the list saved in w_dummy_sync_action.next_sync_action_link.
   */ 
  return(0); 	
}
  /* check_sync_action_redundancy() */  




void	reset_sync_action_list( ) { 
  w_count_sal = 0; 
  w_dummy_sync_action.next_sync_action_link = NULL; 
  w_sa_tail = &w_dummy_sync_action; 
  w_sa_tail->op = 0; 
  w_sa_tail->guard = NULL; 
  w_sa_tail->var_index = -1; 
}
  /* reset_sync_action_list() */ 



void	add_sync_action(
  int		op, 
  int		pi, 
  redgram	guard, 
  int		var_index  
) { 
  struct sync_action_link_type 	*sal; 

  if (check_sync_action_redundancy(op, guard, var_index)) 
    return ; 
  
  switch (op) { 
  case SA_TIME: 
    if (w_sa_tail->op == SA_TIME) 
      return; 
    sal = alloc_sync_action_link(); 
    sal->op = op; 
    sal->guard = NULL; 
    sal->var_index = -1; 
    break; 
  case SA_GUARD: 
    if (w_sa_tail->guard != NULL) { 
      w_sa_tail->guard = red_and(w_sa_tail->guard, guard); 
      red_protect_with_token(w_sa_tail->guard, TOKEN_RULE_EXPANSION); 
      return; 
    }
    sal = alloc_sync_action_link(); 
    sal->op = op; 
    sal->guard = guard; 
    sal->var_index = -1; 
    break; 
  case SA_ERASE: 
    sal = alloc_sync_action_link(); 
    sal->op = op; 
    sal->guard = NULL; 
    sal->var_index = var_index; 
    break; 
  default: 
    fprintf(RED_OUT, "\nIllegal action code %1d\n", op); 
    fflush(RED_OUT); 
    exit(0); 
    break; 
  } 
  sal->next_sync_action_link = NULL; 
  w_sa_tail->next_sync_action_link = sal; 
  w_sa_tail = sal; 
  w_count_sal++; 
  return ; 
}
  /* add_sync_action() */ 
 


struct sync_action_link_type	*query_sync_action_head(int *cptr) { 
  *cptr = w_count_sal; 
  return(w_dummy_sync_action.next_sync_action_link); 
} 
  /* query_sync_action_head() */ 


void	basic_add_sync_action(
  int		pi, 
  redgram	cond, 
  int		var_index 
) {  
  add_sync_action(
    (cond != NULL) ? SA_GUARD : SA_ERASE, 
    pi, 
    cond, 
    var_index  
  ); 
}
  /* basic_add_sync_action() */ 


void	free_sync_action_list(
  struct sync_action_link_type	*sa  
) { 
  struct sync_action_link_type	*sap;   
  
  for (; sa; sap = sa, sa = sa->next_sync_action_link, free(sap)) ; 
} 
  /* free_sync_action_list() */ 


struct sync_action_link_type	*reverse_sa_list(
  struct sync_action_link_type	*sa
) { 
  struct sync_action_link_type	*sap, *sas; 
  
  if (sa == NULL || sa->next_sync_action_link == NULL) 
    return(sa); 

  for (sap = NULL, sas = sa->next_sync_action_link; sas; ) {
    sa->next_sync_action_link = sap; 
    sap = sa; 
    sa = sas; 
    sas = sas->next_sync_action_link; 
  } 
  
  sa->next_sync_action_link = sap; 
  return(sa);  
}
  /* reverse_sa_list() */ 



       	
redgram	red_calc_precond(
  redgram			d, 
  struct sync_action_link_type	*sa 
) { 
  struct sync_action_link_type	*sa_tail; 
  
  sa_tail = sa = reverse_sa_list(sa); 
  if (sa_tail->op == SA_TIME) 
    sa = sa->next_sync_action_link; 
  for (; sa; sa = sa->next_sync_action_link) { 
    switch (sa->op) { 
    case SA_TIME: 
      d = red_time_bck(
        red_and(d, red_query_diagram_enhanced_global_invariance()), 
        red_query_diagram_enhanced_global_invariance()
      ); 
      break; 
    case SA_GUARD: 
      d = red_and(d, sa->guard); 
      if (d == red_false()) {
        sa = reverse_sa_list(sa_tail); 
        return(d); 
      }
      break; 
    case SA_ERASE: 
      d = red_FM_elm(d, sa->var_index); 
      break; 
    } 
  } 
  if (sa_tail->op == SA_TIME) 
    d = red_time_bck(
      red_and(d, red_query_diagram_enhanced_global_invariance()), 
      red_query_diagram_enhanced_global_invariance()
    ); 
  d = red_norm(d, RED_NORM_ZONE_CLOSURE_EQ); 
  sa = reverse_sa_list(sa_tail); 
  red_protect_with_token(d, TOKEN_RULE_EXPANSION); 
  return(d); 
}
  /* red_calc_precond() */ 




redgram	red_calc_postcond(
  redgram			d, 
  struct sync_action_link_type	*sa 
) { 
  for (; sa; sa = sa->next_sync_action_link) { 
    switch (sa->op) { 
    case SA_TIME: 
      d = red_time_fwd(d, red_query_diagram_global_invariance()); 
      break; 
    case SA_GUARD: 
      d = red_and(d, sa->guard); 
      if (d == red_false()) 
        return(d); 
      break; 
    case SA_ERASE: 
      d = red_FM_elm(d, sa->var_index); 
      break; 
    } 
  } 
  red_protect_with_token(d, TOKEN_RULE_EXPANSION); 
  return(d); 
}
  /* red_calc_postcond() */ 




struct echoice_link_type	*copy_echoice(
  struct echoice_link_type	*ech 
) { 
  struct echoice_link_type	*nech; 
  struct sync_action_link_type 	dummy_sa, *tail_sa, *sa, *nsa; 

  nech = alloc_echoice_link(); 
  nech->prob = ech->prob; 
  nech->count = ech->count; 
  nech->choice = ech->choice; 
  nech->red_postcond = ech->red_postcond; 
  nech->next_echoice_link = NULL; 

  dummy_sa.next_sync_action_link = NULL; 
  tail_sa = &dummy_sa; 

  for (sa = ech->sync_action_list; sa; sa = sa->next_sync_action_link) { 
    nsa = alloc_sync_action_link(); 
    nsa->op = sa->op; 
    nsa->guard = sa->guard; 
    nsa->var_index = sa->var_index; 
    tail_sa->next_sync_action_link = nsa; 
    tail_sa = nsa; 
  } 
  tail_sa->next_sync_action_link = NULL; 
  nech->sync_action_list = dummy_sa.next_sync_action_link; 
  
  return(nech); 
}
  /* copy_echoice() */ 




struct eprob_sx_link_type	*copy_eprob_sx(
  struct eprob_sx_link_type	*epsx
) { 
  struct eprob_sx_link_type	*nepsx; 
  struct echoice_link_type 	dummy_echoice, *tail_echoice, *ech, *nech;  
  
  nepsx = alloc_eprob_sx_link(); 
  nepsx->next_eprob_sx_link = NULL; 
  nepsx->count = epsx->count; 
  nepsx->depth = epsx->depth; 
  nepsx->joint_precond = epsx->joint_precond; 

  tail_echoice = &dummy_echoice; 
  tail_echoice->next_echoice_link = NULL; 
    
  for (ech = epsx->echoice_list; ech; ech = ech->next_echoice_link) { 
  /* Iterate for all sync transitions in the probabilistic sync transition. 
   */ 
    nech = copy_echoice(ech); 
    tail_echoice->next_echoice_link = nech; 
    tail_echoice = nech; 
  } 
  tail_echoice->next_echoice_link = NULL; 
  nepsx->echoice_list = dummy_echoice.next_echoice_link; 
  
  fprintf(RED_OUT, "\n}}}}}}Copy epsx %1d to new epsx %1d:\n", 
    epsx->index, nepsx->index
  ); 
  print_eprob_sx(nepsx); 
  
  return(nepsx); 
}
  /* copy_eprob_sx() */ 


void	free_echoice_list(struct echoice_link_type *ech) { 
  struct echoice_link_type	*echp; 
  
  for (; ech; ) { 
    free_sync_action_list(ech->sync_action_list);
    echp = ech; 
    ech = ech->next_echoice_link; 
    free(echp); 
  } 
}
  /* free_echoice_list() */ 




struct eprob_sx_link_type	*create_eprob_sx_array() { 
  struct eprob_sx_link_type	*eprob_sx; 
  struct echoice_link_type 	dummy_echoice, *tail_echoice, *ech;  
  struct sync_action_link_type 	*sa; 
  int				psxi, sxi, ipi, chi, jp; 
  redgram			jpre; 
  
  BASE = (struct eprob_sx_link_type *) 
    malloc(prob_sync_xtion_count * sizeof(struct eprob_sx_link_type)); 
  
  for (psxi = 0; psxi < prob_sync_xtion_count; psxi++) { 
  /* Iterate for all probabilistic sync transitions. 
   */ 
    if (psxi < prob_sync_xtion_count -1) 
      BASE[psxi].next_eprob_sx_link = &(BASE[psxi+1]); 
    else 
      BASE[psxi].next_eprob_sx_link = NULL; 
    
    BASE[psxi].count = prob_sync_xtion[psxi].count; 
    BASE[psxi].index = count_epsx_generated++; 
    
    tail_echoice = &dummy_echoice; 
    tail_echoice->next_echoice_link = NULL; 
    
    jp = red_push(red_true()); 
    for (chi = 0; chi < prob_sync_xtion[psxi].count; chi++) { 
    /* Iterate for all sync transitions in the probabilistic sync transition. 
     */ 
      sxi = prob_sync_xtion[psxi].comb[chi].choice; 
      if (red_query_diagram_sync_xtion_trigger(
            RED_USE_DECLARED_SYNC_XTION, sxi
          ) == red_false()
          ) 
        continue; 
      
      ech = alloc_echoice_link(); 
      ech->next_echoice_link = NULL; 
      reset_sync_action_list();  
      if (red_query_diagram_sync_xtion_trigger(
            RED_USE_DECLARED_SYNC_XTION, sxi
	  ) != red_true() 
	  ) {
        add_sync_action(
          SA_GUARD, 
          0, 
          red_query_diagram_sync_xtion_trigger(
	    RED_USE_DECLARED_SYNC_XTION, sxi
	  ), 
          -1 
        ); 
      }
      for (ipi = 0; 
           ipi < red_query_sync_xtion_party_count(
	           RED_USE_DECLARED_SYNC_XTION, sxi
	         ); 
           ipi++
           ) { 
      	red_user_sync_statements(
          sxi, ipi, 
      	  basic_add_sync_action
      	); 
      } 
      add_sync_action(SA_TIME, 0, NULL, -1); 
      ech->sync_action_list = query_sync_action_head(&(ech->count)); 
      jpre = red_calc_precond(red_true(), 
        ech->sync_action_list
      ); 
      jpre = red_and(jpre, red_stack(jp)); 
      red_set_stack(jp, jpre); 
      
      /* Now add this ech to the list of choices. 
       */ 
      if (jpre == red_false()) { 
      	break; 
      } 

      BASE[psxi].joint_precond = jpre; 
      ech->red_postcond = red_calc_postcond(red_true(), 
        ech->sync_action_list
      ); 
      
      tail_echoice->next_echoice_link = ech; 
      tail_echoice = ech; 
      
      ech->prob = prob_sync_xtion[psxi].comb[chi].prob; 
      ech->choice = sxi = prob_sync_xtion[psxi].comb[chi].choice; 
    } 
    if (red_stack(jp) == red_false()) { 
      free_sync_action_list(ech->sync_action_list); 
      free(ech); 
      free_echoice_list(dummy_echoice.next_echoice_link); 
      
      BASE[psxi].echoice_list = NULL; 
      BASE[psxi].count = 0; 
      BASE[psxi].joint_precond = red_false(); 
    } 
    else { 
      BASE[psxi].joint_precond = red_stack(jp); 
      red_protect_with_token(BASE[psxi].joint_precond, TOKEN_RULE_EXPANSION); 
      BASE[psxi].echoice_list = dummy_echoice.next_echoice_link; 
    }
    red_pop(jp); 
  }

  fprintf(RED_OUT, "\nThe BASE eprob sx list of %1d epsxs: \n", 
    prob_sync_xtion_count 
  ); 
  print_eprob_sx_list(BASE, prob_sync_xtion_count); 
  
  return(BASE); 
}
  /* create_eprob_sx_array() */ 



struct sync_action_link_type	*reduce_sync_actions(
  struct sync_action_link_type	*list, 
  int				*lptr 
) { 
  /* Hi, dear Peng & When_Geese_Return, 
     you need to work out the reduction. 
   */ 
  return(list); 	
}
  /* reduce_sync_actions() */ 




struct sync_action_link_type	*concat_echoice(
  struct sync_action_link_type	*lx, 
  struct sync_action_link_type	*ly, 
  int				*lptr 
) { 
  struct sync_action_link_type	dummy_sa, *sa, *sap, *satail; 
  
  dummy_sa.next_sync_action_link = NULL; 
  satail = &dummy_sa; 
  *lptr = 0; 
  for (sa = lx; sa; sa = sa->next_sync_action_link) {
    sap = alloc_sync_action_link(); 
    sap->op = sa->op; 
    sap->guard = sa->guard; 
    sap->var_index = sa->var_index; 
    satail->next_sync_action_link = sap; 
    satail = sap; 
    (*lptr)++; 
  }
  for (sa = ly; sa; sa = sa->next_sync_action_link) {
    sap = alloc_sync_action_link(); 
    sap->op = sa->op; 
    sap->guard = sa->guard; 
    sap->var_index = sa->var_index; 
    satail->next_sync_action_link = sap; 
    satail = sap; 
    (*lptr)++; 
  }     
  satail->next_sync_action_link = NULL; 
  sa = reduce_sync_actions(dummy_sa.next_sync_action_link, lptr); 
  return(sa); 
}
  /* concat_echoice() */ 



int	count_sync_action_comp = 0; 

int	sync_action_comp(
  struct sync_action_link_type	*sx, 
  int				lx, 
  struct sync_action_link_type	*sy, 
  int				ly 
) { 
  int	comp; 
  
/*
  fprintf(RED_OUT, "\n===[sync action comp %1d]===(lx=%1d)\n", 
    ++count_sync_action_comp, lx 
  ); 
  fprintf(RED_OUT, "   [sync action comp %1d]===(ly=%1d)\n  sx:", 
    ++count_sync_action_comp, ly
  ); 
  print_salist(sx); 
  fprintf(RED_OUT, "  sy:"); 
  print_salist(sy); 
  fflush(RED_OUT); 
*/  
  if (comp == lx - ly) 
    return(comp); 
  for (; sx; sx = sx->next_sync_action_link, sy = sy->next_sync_action_link) { 
    if (comp == sx->op - sy->op) 
      return(comp); 
    else if (sx->guard < sy->guard) 
      return(-1); 
    else if (sx->guard > sy->guard) 
      return(1); 
    else if (comp == sx->var_index - sy->var_index)  	
      return(comp); 
  } 
  return(0); 
} 
  /* sync_action_comp() */ 
  
  
  

struct echoice_link_type	*merge_new_echoice(
  struct echoice_link_type	*eclist, 
  struct sync_action_link_type	*sa, 
  int				len, 
  redgram			postcond, 
  float				prob, 
  int				*cptr
) { 
  struct echoice_link_type	dummy_ec, *ec, *ecp, *ecpp; 
  int				comp; 
  
  dummy_ec.next_echoice_link = eclist; 
  for (ecp = &dummy_ec, ec = eclist; 
       ec; 
       ecp = ec, ec = ec->next_echoice_link
       ) { 
     comp = sync_action_comp(sa, len, ec->sync_action_list, ec->count); 
     if (comp < 0) { 
       ecpp = alloc_echoice_link(); 
       ecpp->count = len; 
       ecpp->sync_action_list = sa; 
       ecpp->red_postcond = postcond; 
       ecpp->prob = prob; 
       ecpp->next_echoice_link = ec; 
       ecp->next_echoice_link = ecpp; 
       (*cptr)++; 
/*
       fprintf(RED_OUT, "\nA newly generated echoice_link:%1d\n", 
         ecpp->index
       ); 
       print_echoice(ecpp); 
*/
       return(dummy_ec.next_echoice_link); 
     } 
     else if (comp == 0) { 
       free_sync_action_list(sa); 
       ec->prob = ec->prob + prob; 
       return(dummy_ec.next_echoice_link); 
     } 
  } 
  ecpp = alloc_echoice_link(); 
  ecpp->count = len; 
  ecpp->sync_action_list = sa; 
  ecpp->red_postcond = postcond; 
  ecpp->prob = prob; 
  ecpp->next_echoice_link = NULL; 
  ecp->next_echoice_link = ecpp; 
  (*cptr)++; 
/*
  fprintf(RED_OUT, "\nA newly generated echoice_link:%1d\n", 
    ecpp->index
  ); 
  print_echoice(ecpp); 
*/
  return(dummy_ec.next_echoice_link); 
}
  /* merge_new_echoice() */ 

  

int	count_extend = 0; 

void	print_sa_extension(
  struct sync_action_link_type	*salx, 
  redgram			dx, 
  struct sync_action_link_type	*saly, 
  redgram			dy
) { 
  fprintf(RED_OUT, "\neeeee(%1d) extend of SA sequence: ", ++count_extend); 
  print_salist(salx);
  fprintf(RED_OUT, "  with post cond: "); 
  red_print_line(dx); 
  fprintf(RED_OUT, "\n  via sequence: "); 
  print_salist(saly);  
  fprintf(RED_OUT, "\n  The new postcondition: "); 
  red_print_line(dy); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
}
  /* print_sa_extension() */ 


      
#define CHOICE_ALREADY_GOAL	-1 


struct choice_level_type { 
  int				*base_prob_sx,  
				*initial_prob_sx, 
				num_choices, 
  				size; 
  struct eprob_sx_link_type	*epsx; 
}
  *next_choice; 
  
int	COUNT_COMBS, count_print_next_choices = 0; 

void	print_next_choices(int depth) { 
  int	ci; 
  
  fprintf(RED_OUT, "\n\n====[%1d] choice (%1d@epsx %1d,%1d):", 
    ++count_print_next_choices,  
    depth, next_choice[depth].epsx->index, COUNT_COMBS
  ); 
  for (ci = 0; ci < next_choice[depth].num_choices; ci++) { 
    if (next_choice[depth].base_prob_sx[ci] == CHOICE_ALREADY_GOAL) 
      fprintf(RED_OUT, " G"); 
    else 
      fprintf(RED_OUT, " %1d", next_choice[depth].base_prob_sx[ci]); 
  } 
  fprintf(RED_OUT, "\n----from:\n"); 
  print_eprob_sx(next_choice[depth].epsx); 
  for (ci = 0; ci < next_choice[depth].num_choices; ci++) { 
    if (next_choice[depth].base_prob_sx[ci] == CHOICE_ALREADY_GOAL) 
      fprintf(RED_OUT, "----to G!\n"); 
    else {
      fprintf(RED_OUT, "----to BASE[%1d]:\n", next_choice[depth].base_prob_sx[ci]); 
      print_eprob_sx(&(BASE[next_choice[depth].base_prob_sx[ci]]));
  } } 
  fflush(RED_OUT); 
} 
  /* print_next_choices() */ 



/***********************************************
 *  The following two procedures tries all the choices in 
 *  probabilistic transition expansion. 
 *  It is complicate because we need early pruning of some paths. 
 *  The early pruning comes in two ways.
 *  
 *   1. If a parent expansion already extends to the goal state, then 
 *      we stop extension immediately. 
 *   2. If the next-step extension leads to a condictory precondition 
 *      of the whole extension path, then we drop the extension. 
 */
#define	CHOICE_NONE	0  // The last possible choice has been tried. 
#define	CHOICE_RETRY	1  // The last possible choice under the 
                           // ancestors' choices have been tried. 
#define	CHOICE_ONE	2  // One choice is found. 

int	reset_echoice(
  int 				depth, 
  struct eprob_sx_link_type	*epsx, 
  redgram			*ptr_joint_precond 
) { 
  int				ci, jp; 
  struct echoice_link_type	*ech; 
  redgram			jpre; 
  
  if (epsx->count > next_choice[depth].size) {
    if (next_choice[depth].size > 0) {
      free(next_choice[depth].base_prob_sx); 
      free(next_choice[depth].initial_prob_sx); 
    }
    next_choice[depth].base_prob_sx = (int *) 
      malloc(epsx->count * sizeof(int)); 
    next_choice[depth].initial_prob_sx = (int *) 
      malloc(epsx->count * sizeof(int)); 
    next_choice[depth].size = epsx->count; 
  } 
  next_choice[depth].epsx = epsx; 
  next_choice[depth].num_choices = epsx->count; 
  jp = red_push(red_true()); 
  for (ci = 0, ech = epsx->echoice_list; 
       ci < next_choice[depth].num_choices; 
       ci++, ech = ech->next_echoice_link
       ) { 
    if (red_and(ech->red_postcond, red_not(DGOAL)) == red_false()) {
      next_choice[depth].base_prob_sx[ci] = CHOICE_ALREADY_GOAL; 
      jpre = red_calc_precond(red_true(), ech->sync_action_list); 
      jpre = red_and(jpre, red_stack(jp)); 
      if (jpre == red_false()) {
      	red_pop(jp); 
      	*ptr_joint_precond = NULL; 
        if (ci == 0) 
          return (CHOICE_NONE); 
        else 
          return (CHOICE_RETRY); 
      }
      else { 
        red_set_stack(jp, jpre); 
    } }
    else {
      for (next_choice[depth].base_prob_sx[ci] = 1; 
           next_choice[depth].base_prob_sx[ci] < prob_sync_xtion_count; 
           next_choice[depth].base_prob_sx[ci]++
           ) {
        jpre = red_calc_precond(
          BASE[next_choice[depth].base_prob_sx[ci]].joint_precond, 
          ech->sync_action_list
        ); 
        jpre = red_and(jpre, red_stack(jp)); 
        if (jpre != red_false()) 
          break; 
      }
      if (next_choice[depth].base_prob_sx[ci] >= prob_sync_xtion_count) {
      	red_pop(jp); 
      	*ptr_joint_precond = NULL; 
        if (ci == 0) 
          return (CHOICE_NONE); 
        else 
          return (CHOICE_RETRY); 
      } 
      red_set_stack(jp, jpre); 
      next_choice[depth].initial_prob_sx[ci] 
      = next_choice[depth].base_prob_sx[ci]; 
  } } 
  *ptr_joint_precond = red_stack(jp); 
  red_protect_with_token(*ptr_joint_precond, TOKEN_RULE_EXPANSION); 
  COUNT_COMBS = 0; 
  red_pop(jp); 
//  print_next_choices(depth); 
  
  return(CHOICE_ONE); 
}
  /* reset_echoice() */ 



redgram red_joint_precond_tail(
  int				depth, 
  int				ci, 
  struct echoice_link_type	*ech
) {
  redgram	jpre; 
  
  jpre = red_true(); 
  for (ci++, ech = ech->next_echoice_link; 
       ci < next_choice[depth].num_choices; 
       ci++, ech = ech->next_echoice_link
       ) { 
    if (next_choice[depth].base_prob_sx[ci] != CHOICE_ALREADY_GOAL) { 
      jpre = red_and(jpre, red_calc_precond(
        BASE[next_choice[depth].base_prob_sx[ci]].joint_precond, 
        ech->sync_action_list 
      ) ); 
    } 
  } 
  return(jpre); 
}
  /* red_joint_precond_tail() */ 




int	inc_echoice(
  int 		depth, 
  redgram	*ptr_joint_precond
) { 
  int				ci, cj, jp; 
  struct echoice_link_type	*ech, *echp; 
  redgram			jpre; 
  
  jp = red_push(red_true()); 
  for (ci = 0, ech = next_choice[depth].epsx->echoice_list; 
       ci < next_choice[depth].num_choices; 
       ci++, ech = ech->next_echoice_link
       ) { 
    if (next_choice[depth].base_prob_sx[ci] == CHOICE_ALREADY_GOAL) { 
      jpre = red_calc_precond(red_true(), ech->sync_action_list); 
      jpre = red_and(jpre, red_stack(jp)); 
      if (jpre == red_false()) {
      	red_pop(jp); 
      	*ptr_joint_precond = NULL; 
        if (ci == 0) 
          return (CHOICE_NONE); 
        else 
          return (CHOICE_RETRY); 
      }
      else { 
        red_set_stack(jp, jpre); 
    } }
    else { 
      for (++(next_choice[depth].base_prob_sx[ci]); 
           next_choice[depth].base_prob_sx[ci] < prob_sync_xtion_count;  
           ++(next_choice[depth].base_prob_sx[ci])
           ) {
        jpre = red_calc_precond(
          BASE[next_choice[depth].base_prob_sx[ci]].joint_precond, 
          ech->sync_action_list
        ); 
        jpre = red_and(jpre, red_stack(jp)); 
        jpre = red_and(jpre, red_joint_precond_tail(depth, ci, ech)); 
        if (jpre != red_false()) 
          break; 
      }
      if (next_choice[depth].base_prob_sx[ci] < prob_sync_xtion_count) {
        COUNT_COMBS++; 
        *ptr_joint_precond = jpre; 
        red_pop(jp); 
        print_next_choices(depth); 
        return(CHOICE_ONE); 
      } 
      else if (ci == 0) {
        red_pop(jp); 
        *ptr_joint_precond = NULL; 
        return(CHOICE_NONE); 
      }
      next_choice[depth].base_prob_sx[ci]
      = next_choice[depth].initial_prob_sx[ci]; 
      jpre = red_calc_precond(
        BASE[next_choice[depth].base_prob_sx[ci]].joint_precond, 
          ech->sync_action_list
      ); 
      jpre = red_and(jpre, red_stack(jp)); 
      red_set_stack(jp, jpre); 
  } } 
  *ptr_joint_precond = NULL; 
  red_pop(jp); 
  return(CHOICE_NONE); 
}
  /* inc_echoice() */ 



struct eprob_sx_link_type	*get_epsx(
  int		depth, 
  redgram	joint_precond  
) { 
  struct eprob_sx_link_type	*epsx; 
  struct echoice_link_type	*ecl, *ei, *ej; 
  struct sync_action_link_type	*sa; 
  int				len, ci, psxj, ecc; 
  redgram			d; 
  
  ecl = NULL; 
  ecc = 0; 
  for (ci = 0, ei = next_choice[depth].epsx->echoice_list; 
       ci< next_choice[depth].num_choices; 
       ci++, ei = ei->next_echoice_link
       ) {
    psxj = next_choice[depth].base_prob_sx[ci]; 
    if (psxj == -1) { 
      sa = concat_echoice(
        ei->sync_action_list, NULL, &len 
      ); 
/*
      print_sa_extension(
        ei->sync_action_list, ei->red_postcond, NULL, ei->red_postcond
      );
*/
      ecl = merge_new_echoice(
        ecl, sa, len, ei->red_postcond, ei->prob, &ecc
      ); 
    } 
    else for (ej = BASE[psxj].echoice_list; ej; ej = ej->next_echoice_link) { 
      d = red_calc_postcond(ei->red_postcond, ej->sync_action_list); 
      if (d != red_false()) { 
      	red_protect_with_token(d, TOKEN_RULE_EXPANSION); 
        sa = concat_echoice(
          ei->sync_action_list, ej->sync_action_list, &len 
        ); 
/*
        print_sa_extension(
          ei->sync_action_list, ei->red_postcond, ej->sync_action_list, d
        );
*/
        ecl = merge_new_echoice(
          ecl, sa, len, d, ei->prob*ej->prob, &ecc
        ); 
    } }
  }
  if (ecc > 0) { 
    epsx = alloc_eprob_sx_link(); 
    epsx->depth = depth; 
    epsx->count = ecc; 
    epsx->joint_precond = joint_precond; 
    epsx->echoice_list = ecl; 
    
    fprintf(RED_OUT, "\n))))New epsx generated(((((((((((((((((((\n"); 
    print_eprob_sx(epsx); 
    
    return(epsx); 
  }
  else 
    return(NULL); 
}
  /* get_epsx() */ 


struct eprob_sx_link_type	*get_first_echoice(
  int				depth, 
  struct eprob_sx_link_type	*epsx
) { 
  struct eprob_sx_link_type	*nepsx; 
  int				inc_succ; 
  redgram			jpre; 
  
  for (inc_succ = reset_echoice(depth, epsx, &jpre); 
       inc_succ != CHOICE_NONE; 
       inc_succ = inc_echoice(depth, &jpre)
       ) 
    if (inc_succ == CHOICE_ONE && (nepsx = get_epsx(depth, jpre))) {
      return(nepsx); 
    }

  return(NULL); 
} 
  /* get_first_echoice() */ 


struct eprob_sx_link_type	*get_next_echoice(int depth) { 
  struct eprob_sx_link_type	*nepsx; 
  int				inc_succ; 
  redgram			jpre; 
  
  for (inc_succ = inc_echoice(depth, &jpre); 
       inc_succ != CHOICE_NONE; 
       inc_succ = inc_echoice(depth, &jpre)
       ) 
    if (inc_succ == CHOICE_ONE && (nepsx = get_epsx(depth, jpre))) {
      return(nepsx); 
    }

  return(NULL); 
}
  /* get_next_echoice() */ 



void	free_eprob_sx(struct eprob_sx_link_type	*epsx) { 
  struct echoice_link_type	*ech, *echp; 
  struct sync_action_link_type	*sa, *sap; 
  
  for (ech = epsx->echoice_list; ech; ) {
/*
    fprintf(RED_OUT, "\n(%1d,%1d),sync action list: \n  ", 
      epsx->index, ech->index 
    ); 
    print_salist(ech->sync_action_list); 
*/
    for (sa = ech->sync_action_list; sa; ) {
      sap = sa; 
/*
      fprintf(RED_OUT, "\n    >>>epsx %1d, ech %1d, sa %1d\n", 
        epsx->index, ech->index, sa->index
      ); 
      fflush(RED_OUT); 
*/
      sa = sa->next_sync_action_link; 
      free(sap); 
    }
    echp = ech; 
    ech = ech->next_echoice_link; 
    free(echp);
  }
  free(epsx); 
} 
  /* free_eprob_sx() */ 


void	reset_eprob_sx_list() { 
  count_eprob_sx = 0; 
  eprob_sx_list = NULL; 
}
  /* reset_eprob_sx_list() */ 


struct eprob_sx_link_type	*query_eprob_sx_list(int *cptr) { 
  *cptr = count_eprob_sx; 
  return (eprob_sx_list); 	
} 
  /* query_eprob_sx_list() */ 




int	eprob_sx_comp(
  struct eprob_sx_link_type	*ex, 
  struct eprob_sx_link_type	*ey 
) {
  int				comp; 
  struct echoice_link_type	*ecx, *ecy; 
  
  if (comp == ex->count - ey->count) {
    return(comp); 
  }
  else for (ecx = ex->echoice_list, ecy = ey->echoice_list; 
            ecx; 
            ecx = ecx->next_echoice_link, ecy = ecy->next_echoice_link
            ) { 
    if (comp == sync_action_comp(
          ecx->sync_action_list, ecx->count, 
          ecy->sync_action_list, ecy->count
        )) 
      return(comp);        	
  } 
  return(0); 
}
  /* eprob_sx_comp() */



int	epsx_subsumed(
  struct eprob_sx_link_type	*ex, 
  struct eprob_sx_link_type	*ey
) {
  int				comp; 
  struct echoice_link_type	*ecx, *ecy; 
  
  if (comp == ex->count > ey->count) {
    return(0); 
  }
  for (ecx = ex->echoice_list, ecy = ey->echoice_list; ecx && ecy; ) {
    comp = sync_action_comp(
      ecx->sync_action_list, ecx->count, 
      ecy->sync_action_list, ecy->count
    ); 
    if (comp < 0)  
      return(0); 
    else if (comp > 0) { 
      ecy = ecy->next_echoice_link; 
    } 
    else { 
      ecx = ecx->next_echoice_link; 
      ecy = ecy->next_echoice_link; 
    } 
  } 
  if (ecx != NULL) 
    return(0); 
  else 
    return(1); 
}
  /* epsx_subsumed() */ 




void	add_eprob_sx(struct eprob_sx_link_type *epsx) { 
  struct eprob_sx_link_type	dummy_epsx, *cepsx, *pepsx; 
  int				comp; 
  
  dummy_epsx.next_eprob_sx_link = eprob_sx_list; 
  for (pepsx = &dummy_epsx, cepsx = eprob_sx_list; 
       cepsx; 
       pepsx = cepsx, cepsx = cepsx->next_eprob_sx_link
       ) { 
    comp = eprob_sx_comp(epsx, cepsx); 
    if (comp < 0) { 
      if (epsx_subsumed(epsx, cepsx)) {
        eprob_sx_list = dummy_epsx.next_eprob_sx_link; 
        return; 
      }
    }
    else if (comp > 0) { 
      epsx->next_eprob_sx_link = cepsx; 
      pepsx->next_eprob_sx_link = epsx; 
      count_eprob_sx++; 

      eprob_sx_list = dummy_epsx.next_eprob_sx_link; 
      return; 
    } 
    else if (comp == 0) { 
      free_eprob_sx(epsx); 
      return; 
    } 
  } 
  count_eprob_sx++; 
  epsx->next_eprob_sx_link = NULL; 
  pepsx->next_eprob_sx_link = epsx; 
  eprob_sx_list = dummy_epsx.next_eprob_sx_link; 
  return; 
} 
  /* add_eprob_sx() */ 



void	expand_prob_sx(
  struct eprob_sx_link_type	*eprob_sx, 
  int				depth, 
  int				*cptr
) {
  struct eprob_sx_link_type	*nepsx; 
  
  if (depth <= 0) { 
    add_eprob_sx(eprob_sx); 
    return; 
  } 
  for (nepsx = get_first_echoice(depth, eprob_sx); 
       nepsx; 
       nepsx = get_next_echoice(depth)
       ) { 
    expand_prob_sx(nepsx, depth-1, cptr); 
    if (depth > 1) 
      free_eprob_sx(nepsx); 
  } 
  return; 
}
  /* expand_prob_sx() */ 





struct eprob_sx_link_type	*prob_rule_expansion(
  char	*mfname, 
  char	*pfname 
) {
  int	epi; 
  
/*
  fprintf(RED_OUT, 
    "\nStart expansion probabilistic rules to depth %1d:\n", 
    DEPTH_RULE_EXPANSION
  ); 
  fprintf(RED_OUT, 
    "New model and probabilisty files are `%s.ex' and `%s.ex.'\n", 
    mfname, pfname
  ); 
*/  
  /* Construct the list of probabilitic global transitions. 
   */ 
  BASE = create_eprob_sx_array(); 
  reset_eprob_sx_list(); 
  for (epi = 1; epi < prob_sync_xtion_count; epi++) { 
    expand_prob_sx(
      copy_eprob_sx(&(BASE[epi])), 
      DEPTH_RULE_EXPANSION, &count_eprob_sx
    ); 
  } 
  
  eprob_sx_list = query_eprob_sx_list(&count_eprob_sx); 
/*  
  fprintf(RED_OUT, 
    "\nThe final expanded probabilisitic rules to depth %1d:\n", 
    DEPTH_RULE_EXPANSION
  ); 
  print_eprob_sx_list(eprob_sx_list, count_eprob_sx); 
*/
  return(eprob_sx_list); 
}
  /* prob_rule_expansion() */ 

    
int	flag_stop = 1; 

redgram	eprob_reach_analysis(redgram dgoal) {
  int				ngoal, // index of stack frame for non-goal states
  				pgoal, // index of stack frame for goal states with probability 1.0
  				nzinv, // index of stack frame for timeless states with 
  				zpinv, // index of stack frame for timeless states with 
  				       // zero probabilities
  				pic, reach, reachp, prob_pre, unprob, 
  				psxi, ci; 
  redgram 			pre, timeless, timed; 
  struct eprob_sx_link_type	*epsx; 
  struct echoice_link_type	*ech; 
  
  ngoal = red_push(red_and(
    red_not(dgoal), 
    red_query_diagram_enhanced_global_invariance()
  ) ); 
  pgoal = red_push(red_diagram_float(dgoal, red_var_prob(), 1.0, 1.0));

  red_timeless(red_query_diagram_global_invariance(), &timeless, &timed); 
  nzinv = red_push(red_or(dgoal, timed)); 
  fprintf(RED_OUT, "\nred_stack(nzinv=%1d):\n", nzinv); 
  red_print_diagram(red_stack(nzinv)); 

  timeless = red_and(timeless, red_stack(ngoal));  
  zpinv = red_push(red_diagram_float(timeless, red_var_prob(), 0.0, 0.0)); 
  fprintf(RED_OUT, "\nred_stack(zpinv=%1d):\n", zpinv); 
  red_print_diagram(red_stack(zpinv)); 
  
  pre = red_and(red_query_diagram_global_invariance(), red_stack(ngoal)); 
  pre = red_diagram_float(pre, red_var_prob(), 0.0, 0.0);
  reach = red_push(red_or(pre, red_stack(pgoal))); 
  reachp = red_push(red_false()); 
  for (pic = 1; red_stack(reach) != red_stack(reachp); pic++) { 
    red_set_stack(reachp, red_stack(reach)); 
    red_set_stack(reach, red_false()); 
    for (epsx = eprob_sx_list; epsx; epsx = epsx->next_eprob_sx_link) { 
/*
//      if (epsx->index == 27) {
        fprintf(RED_OUT, "\n===[(%1d), epsx %1d with %1d choices]=====================\n", 
          pic, epsx->index, epsx->count
        ); 
//      }
*/
      unprob = red_push(red_true()); 
      prob_pre = red_push(red_false()); 
      for (ech = epsx->echoice_list; ech; ech = ech->next_echoice_link) { 
/*
//        if (epsx->index == 27) {
      	  fprintf(RED_OUT, 
      	    "$$$[(%1d), epsx %1d, echoice %1d]$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n", 
      	    pic, epsx->index, ech->index 
      	  ); 
      	  print_echoice(ech); 
//      	}
*/
/*
        if (ech->index == 32) {
          fprintf(RED_OUT, "Caught ech->index == %1d\n", ech->index); 
          fflush(RED_OUT);  
          for (; flag_stop; ); 	
        } 
*/
      	pre = red_calc_precond(red_stack(reachp), ech->sync_action_list); 
/*
//        if (epsx->index == 27) {
      	  fprintf(RED_OUT, 
      	    "-----((%1d), epsx %1d, %f, ech %1d, after pre)-----------\n", 
      	    pic, epsx->index, 
      	    ech->prob, 
      	    ech->index
      	  ); 
      	  red_print_diagram(pre); 
//      	}
*/
      	pre = prob_multiply(pre, ech->prob); 
/*
//        if (epsx->index == 27) {
      	  fprintf(RED_OUT, 
      	    "-----((%1d), epsx %1d, %f, ech %1d, after multiplication)-----------\n", 
      	    pic, epsx->index, 
      	    ech->prob, 
      	    ech->index
      	  ); 
      	  red_print_diagram(pre); 
//      	}
*/
        red_set_stack(unprob, red_and(
          red_FM_elm(pre, red_var_prob()), red_stack(unprob) 
        ) ); 
        
      	red_set_stack(prob_pre, prob_add(
      	  red_and(red_stack(prob_pre), red_stack(unprob)), 
      	  red_and(pre, red_stack(unprob)) 
      	) ); 
/*
//        if (epsx->index == 27) {
      	  fprintf(RED_OUT, 
      	    "-----((%1d), epsx %1d, %f, ech %1d, after addition)-----------\n", 
      	    pic, epsx->index, 
      	    ech->prob, 
      	    ech->index
      	  ); 
      	  red_print_diagram(red_stack(prob_pre)); 
//      	}
*/
      } 
      switch (status_max_min) { 
      case FLAG_MAXIMIZER:  
        red_set_stack(reach, prob_max(red_stack(prob_pre), red_stack(reach))); 
        break; 
      case FLAG_MINIMIZER:  
      case FLAG_MINIMIZER_TIMED_IDLE:  
        red_set_stack(reach, prob_min(red_stack(prob_pre), red_stack(reach))); 
        break; 
      default: 
        fprintf(RED_OUT, 
          "\nERROR: eprob_reach_analysis(), Illegal maximum/minimum option %1d.\n", 
          status_max_min
        ); 
        fflush(RED_OUT); 
        exit(0); 
        break; 
      }  
      
      red_pop(prob_pre); 
      red_pop(unprob); 
/*
//      if (epsx->index == 27) {
        fprintf(RED_OUT, 
          "***<(%1d), epsx %1d, after minimax>********************\n", 
          pic, epsx->index  
        ); 
        red_print_diagram(red_stack(reach)); 
//      }
*/
    } 
    // reset all goal states to probability one. 
    pre = red_and(red_stack(reach), red_stack(ngoal));  
    
    // reset all timeless nongoal states to probability zero.
    switch (status_max_min) { 
    case FLAG_MAXIMIZER:  
      break; 
    case FLAG_MINIMIZER:  
    case FLAG_MINIMIZER_TIMED_IDLE:  
      pre = red_and(pre, red_stack(nzinv)); 
      pre = red_or(pre, red_stack(zpinv)); 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nERROR: eprob_reach_analysis(), Illegal maximum/minimum option %1d.\n", 
        status_max_min
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }  
    
    pre = red_or(pre, red_stack(pgoal)); 
    
    red_set_stack(reach, pre); 
/*
    fprintf(RED_OUT, 
      "+++(%1d), after a fixpoint iteration++++++++++++++++++++++++\n", 
      pic 
    ); 
    red_print_diagram(red_stack(reach)); 
*/
  } 
  dgoal = red_stack(reach); 
  red_pop(reachp); 
  red_pop(reach); 
  red_pop(zpinv); 
  red_pop(nzinv); 
  red_pop(pgoal); 
  red_pop(ngoal); 
  return(dgoal); 
}
  /* eprob_reach_analysis() */ 
  



char	*minmax_option_name() { 
  switch (status_max_min) { 
  case FLAG_MAXIMIZER: 
    return ("MAX"); 
    break; 
  case FLAG_MINIMIZER:  
    return("MIN"); 
    break; 
  case FLAG_MINIMIZER_TIMED_IDLE:  
    return("MIN Timed Idle"); 
    break; 
  default: 
    return("ERROR"); 
    break; 
  } 
}
  /* minmax_option_name() */ 


int	pta(tt, s)
	int	tt; // task type
	char	*s; // string for the spec. 
{
  int					NEGATED_SPEC, assume, pi, xi, 
  					deadlock, wreach;
  struct reachable_return_type		*rr; 
  struct sim_check_return_type		*sr; 
  struct model_check_return_type	*mr; 
  redgram				result, ds; 

  /* goal processing */ 

  switch (tt) {

  case RED_TASK_DEADLOCK: 
    ds = red_query_diagram_deadlock();
    result = prob_reach_analysis(tt, ds); 
    fprintf(RED_OUT, "The %s probability diagram for deadlock:\n", 
      minmax_option_name()
    ); 
    red_print_diagram(red_and(red_query_diagram_initial(), result)); 
    break; 

  case RED_TASK_ZENO: 
    ds = red_query_diagram_zeno();
    result = prob_reach_analysis(tt, ds); 
    fprintf(RED_OUT, "The %s probability diagram for Zenoness:\n", 
      minmax_option_name()
    ); 
    red_print_diagram(red_and(red_query_diagram_initial(), result)); 
    break; 

  case RED_TASK_SAFETY: 
    ds = red_diagram(s); 
    ds = red_not(ds); 
    result = prob_reach_analysis(tt, ds); 
    fprintf(RED_OUT, "The %s probability diagram for no safety:\n", 
      minmax_option_name()
    ); 
    red_print_diagram(red_and(red_query_diagram_initial(), result)); 
    break;

  case RED_TASK_RISK:
    ds = red_diagram(s); 
    result = prob_reach_analysis(tt, ds); 
    fprintf(RED_OUT, "The %s probability diagram for risk:\n", 
      minmax_option_name()
    ); 
    red_print_diagram(red_and(red_query_diagram_initial(), result)); 
    break;

  case RED_TASK_GOAL:
    ds = red_diagram(s); 
    result = prob_reach_analysis(tt, ds); 
    fprintf(RED_OUT, "The %s probability diagram for goal:\n", 
      minmax_option_name()
    ); 
    red_print_diagram(red_and(red_query_diagram_initial(), result)); 
    break;

  case RED_TASK_MODEL_CHECK:
    fprintf(RED_OUT, 
      "\nSorry the probability analysis of TCTL has not been implemented yet.\n"
    ); 
    fflush(RED_OUT); 
    exit(0); 
    break; 

  case PTA_RULE_EXPANSION: 
    if (DEPTH_RULE_EXPANSION > 0) { 
      FLAG_PRINT_INDEX = 1; 
      next_choice = (struct choice_level_type *) 
        malloc((DEPTH_RULE_EXPANSION + 1)*sizeof(struct choice_level_type)); 
      for (xi = 0; xi <= DEPTH_RULE_EXPANSION; xi++) { 
      	next_choice[xi].size = 0; 
      	next_choice[xi].num_choices = 0; 
      	next_choice[xi].base_prob_sx = NULL; 
      	next_choice[xi].initial_prob_sx = NULL; 
      } 
      TOKEN_RULE_EXPANSION = red_get_a_protection_token(); 
      DGOAL = red_and(red_diagram(s), 
        red_query_diagram_enhanced_global_invariance()
      ); 
      red_protect_with_token(DGOAL, TOKEN_RULE_EXPANSION); 
      eprob_sx_list = prob_rule_expansion(
        model_fname, prob_fname 
      ); 
      result = eprob_reach_analysis(DGOAL); 
      fprintf(RED_OUT, "\nThe %s EXTENDED probability diagram for goal:\n", 
        minmax_option_name()
      ); 
      red_print_diagram(red_and(red_query_diagram_initial(), result)); 
      red_release_token(TOKEN_RULE_EXPANSION); 
      for (xi = 0; xi <= DEPTH_RULE_EXPANSION; xi++) { 
      	if (next_choice[xi].base_prob_sx != NULL)
      	  free(next_choice[xi].base_prob_sx); 
      } 
      free(next_choice); 
    } 
    break; 
  }
}
/* pta() */


main(argc, argv)
  int	argc; 
  char	**argv; 
{ 
  redgram 	sub, conj; 
  char		*spec; 
 
  if (!my_process_command_line(argc, argv) /* the number of files */) 
    fprintf(RED_OUT, 
      "Use a line beginning with \"%%end\" to end the formula input.\n\n"
    );

  red_begin_session(flag_my_system_type, model_fname, my_proc_count);
/* 
  fprintf(RED_OUT, "after process command line, PC=%1d\n", my_proc_count); 
*/
  red_input_model(model_fname, RED_REFINE_GLOBAL_INVARIANCE); 
  spec = red_file_to_string(spec_fname); 
  prepare_sync_xtion_probabilities(prob_fname); 
  
  pta(task_type, spec); 
/*  
  fprintf(RED_OUT, "RED>> Total system time: %fsec., user time: %fsec.\n", 
    red_query_system_time(), 
    red_query_user_time() 
  ); 
  fprintf(RED_OUT, "RED>> Total memory (HRD+CRD+MDD): %1dbytes.\n", 
    red_query_memory()
  ); 
*/
  red_end_session(model_fname); 
}
  /* main() */ 
