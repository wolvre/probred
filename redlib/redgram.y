%{ 
#include <stdlib.h>
#include <string.h> 
#include <ctype.h>
#include <stdio.h>
#include <float.h>

#include <limits.h>

#include "redbasics.h"
#include "redbasics.e" 

#include "vindex.e"

#include "redbop.h"
#include "redbop.e"

#include "redparse.h"
#include "redparse.e"

#include "hashman.h" 
#include "hashman.e" 

#include "exp.e" 

#include "tctctl.e" 

#include "bisim.e" 

#include "dmem.h"
#include "dmem.e"

#include "redstring.e"

char			*lexbuf; 
int			count_red_src_lines = 0; 
struct name_link_type	*red_src_lines; 


#define	SCOPE_CHOICE		0 /* all local variables must be specified with process id. */ 
#define	SCOPE_PROC_DECLARATION	1 /* only macro constants are allowed. */ 
#define	SCOPE_PROC_DECLARED	2 
#define	SCOPE_RANGE_DECLARATION	3 /* only macro constants are allowed. */ 
#define	SCOPE_GLOBAL		4 /* all local variables must be specified with process id. */ 
#define	SCOPE_GLOBAL_EVENT	5 /* only synchronizers, macro constants are allowed. */
#define	SCOPE_LOCAL		6 /* everything but quantified synchronization holders can be used. */ 
#define	SCOPE_LOCAL_XTION	7 /* everything, including quantified synchronizatoin holders, can be used. */
#define	SCOPE_STACK		8 /* everything, including quantified synchronizatoin holders, can be used. */
#define SCOPE_ADDRESS_ENFORCER	9 /* only macro constants and quantified synchronization holders are allowed. */

#define	SCOPE_SYSTEM_INFO	20 /* all names are identifiers. */ 

#define GRAM_STREAM_ORDERED	30
#define GRAM_STREAM_UNORDERED	31 

/*
struct parse_indirect_type {
  struct ps_exp_type		*pointer; 
  struct parse_indirect_type	*next_parse_indirect; 
}; 
*/

int 
  count_debug1 = 0, 
  count_debug2 = 0, 
  count_pi_arith = 0; 

int				CUR_SCOPE[20], TOP_SCOPE, CUR_VAR_TYPE, CUR_GAME_ROLE; 
struct parse_variable_type	*CUR_VAR_HEAD; 

int	flag_address_type; 

struct name_link_type		*qfd_stack; 

struct parse_mode_type		*CURRENT_MODE;
struct parse_xtion_type		*CURRENT_XTION, *xt2;
char				*CURRENT_QNAME1, *CURRENT_QNAME2; 
int				CURRENT_FAIRNESS_STRENGTH, 
				CURRENT_XTION_SYNC_COUNT; 
int				LENGTH_CURRENT_POINT_LIST; 


struct parse_xtion_type		*tpx; 

int	lineno, flag_line_start, spec_size, formula_connector_count;
int	flag_comment_to_end_of_line = 0; 

struct parse_xtion_type			*X14 = NULL; 

struct ps_exp_type			*CURRENT_PSEXP, 
					*CURRENT_TOKEN_QFD, 
					*CURRENT_FAIRNESS;  

struct parse_variable_type		*CURRENT_TOKEN_VAR; 
struct parse_stream_operation_type	*CURRENT_STREAM_OP; 
int					CURRENT_VALUE; 
int					CURRENT_INLINE_FORMAL_ARGUMENT_COUNT; 
struct name_link_type			*CURRENT_INLINE_FORMAL_ARGUMENT_LIST; 

struct gram_interval_type {
  int lb, ub;
};


struct gram_fairness_type {
  int 				strong_fairness_count, weak_fairness_count;
  struct ps_fairness_link_type	*strong_fairness_list, *weak_fairness_list;
};

struct ps_fairness_link_type 
  *weak_fl_tail, 
  dummy_weak_fl, 
  *strong_fl_tail, 
  dummy_strong_fl; 


struct gram_optional_address_type { 
  int			flag_address_type; 
  struct ps_exp_type	*exp_address; 
}; 

  
struct gram_fairness_type 
  *CURRENT_GRAM_FAIRNESS;  

char	*gram_test, *gram_macro_name; 


#define	FLAG_PS_OPEN	0
#define	FLAG_PS_CLOSED	1

struct rational_type {
  int	numerator, denominator;
};

#define	FLAG_INPUT_FILE		0
#define	FLAG_INPUT_STRING	1 
int			flag_redlib_input_source = FLAG_INPUT_FILE; 
char			*redlib_input_string; 
int			redlib_input_string_len = 0; 
FILE			*redlibin; 
struct yy_buffer_state*	redlib_handle; 


void			redlib_switch_to_buffer(); 
void			redlib_delete_buffer(); 
struct yy_buffer_state*	redlib_scan_buffer(); 

#define	NAME_MACRO			1
#define	NAME_PROCESS			2
#define NAME_MODE			3
#define	NAME_SYNCHRONIZER_GLOBAL	4
#define	NAME_SYNCHRONIZER_LOCAL		5 
#define	NAME_POINTER_GLOBAL		6
#define	NAME_POINTER_LOCAL		7
#define	NAME_DISCRETE_GLOBAL		8
#define	NAME_DISCRETE_LOCAL		9
#define	NAME_CLOCK_GLOBAL		10
#define	NAME_CLOCK_LOCAL		11
#define	NAME_DENSE_GLOBAL		12
#define	NAME_DENSE_LOCAL		13

struct parse_xtion_type	*pst9; 


int	first_few_primes(
  int 	i
) {
  switch (i % 8) { 
  case 1: 
    return(3);  
  case 2: 
    return(5); 
  case 3: 
    return(7);  
  case 4: 
    return(11);  
  case 5: 
    return(13); 
  case 6: 
    return(17); 
  case 7: 
    return(19);  
  default: 
    return(23);  
} }
  /* first_few_primes() */ 



int	PC_CONNECT; 

int	irregular_connect(
  int	i, 
  int	j
) { 
  if (i == PC_CONNECT && j == PC_CONNECT-1) 
    return(TYPE_FALSE); 
  else if (i == PC_CONNECT-1 && j == PC_CONNECT) 
    return(TYPE_FALSE); 
  
  if (i == PC_CONNECT) 
    i--; 
  if (j == PC_CONNECT) 
    j--; 
  if (   /* i < j 
      && */
         (i * first_few_primes(i % 8) + first_few_primes(j % 8)) % 7 == 0
      ) 
    return(TYPE_TRUE); 
  else 
    return(TYPE_FALSE); 
}
  /* irregular_connect() */ 



void	print_irregular_connection(
  int	pc
) { 
  int	pi, pj; 
  
  PC_CONNECT = pc; 
  fprintf(RED_OUT, "\n\n(((Irregular network connections)))\n***"); 
  for (pi = 2; pi <= pc; pi++) { 
    fprintf(RED_OUT, " %2d", pi); 
  } 
  fprintf(RED_OUT, "\n"); 
  for (pi = 2; pi <= pc; pi++) { 
    fprintf(RED_OUT, "%3d", pi); 
    for (pj = 2; pj <= pc; pj++) { 
      if (irregular_connect(pi, pj)) 
        fprintf(RED_OUT, "  C"); 
      else 
        fprintf(RED_OUT, "   "); 
    } 
    fprintf(RED_OUT, "\n"); 
  }
  fprintf(RED_OUT, "\n\n"); 
}
  /* print_irregular_connection() */ 







struct ps_exp_type	*rec_ineq_analyze();  

// 2007/11/04
// The following declarations are for the multiple choices in 
// input parsing. 
// To support parsing in redlib, the users can choose from 
// parsing from a model transition system, 
// a formula, 
// a transition rule, 
// or a role specification.  
// Variable TYPE_PARSE_CHOICE and PARSER_INPUT_FORMULA 
// are externally accessible.  
// Variable TYPE_PARSE_CHOICE lets the 
// redlib procedures know what the choice is.  
// When the choice is formula, then PARSER_INPUT_FORMULA points 
// to the parsing tree of the formula. 
//
// Variable STATUS_FORMULA_CHOICE records the local features and global 
// features of the formula being parsed. 
// Local variable references are local features. 
// Event references, modal operators are global features. 
// Together with the two flag values, STATUS_FORMULA_CHOICE tells us 
// what kind of features have been used in the formula. 
// Then we use the flags to return the proper choice values to the users. 

char	*scope_name(s) 
	int	s; 
{
  switch (s) { 
  case SCOPE_CHOICE:
    return("choice"); 
  case SCOPE_PROC_DECLARATION: 
    return("proc_declaration"); 
  case SCOPE_RANGE_DECLARATION: 
    return("range-declaration"); 
  case SCOPE_GLOBAL: 
    return("global"); 
  case SCOPE_GLOBAL_EVENT: 
    return("global-event"); 
  case SCOPE_LOCAL: 
    return("local"); 
  case SCOPE_LOCAL_XTION: 
    return("local-xtion"); 
  case SCOPE_ADDRESS_ENFORCER: 
    return("address-enforcer"); 
  case SCOPE_SYSTEM_INFO: 
    return("system-info"); 
  default: 
    return("unknown-scope"); 
  }
}
  /* scope_name() */ 
  
  

int	top_scope() { 
  return(CUR_SCOPE[TOP_SCOPE]); 
}
  /* top_scope() */ 
  

void	print_scope_stack() { 
  int	i; 
  
  for (i = TOP_SCOPE; i > 0; i--) 
    fprintf(RED_OUT, "%1d:%1d:%s-->", 
            i, CUR_SCOPE[i], scope_name(CUR_SCOPE[i])
            );  
  fprintf(RED_OUT, "0:%1d:%s", CUR_SCOPE[0], scope_name(CUR_SCOPE[0])); 
  fprintf(RED_OUT, "\n"); 
}
  /* print_scope_stack() */ 
  
  
void	push_scope(s) 
	int	s; 
{ 
  CUR_SCOPE[++TOP_SCOPE] = s; 
/*
  fprintf(RED_OUT, "push a scope %1d:%s at frame %1d\n", 
          s, scope_name(s), TOP_SCOPE
          ); 
  print_scope_stack(); 
*/
}
  /* push_scope() */ 
  
  

void	change_scope(s) 
	int	s; 
{ 
/*
  fprintf(RED_OUT, "change to a scope %1d:%s at frame %1d\n", 
          s, scope_name(s), TOP_SCOPE
          ); 
*/
  CUR_SCOPE[TOP_SCOPE] = s; 
/*
  print_scope_stack(); 
*/
}
  /* change_scope() */ 
  
  

void	pop_scope() 
{ 
  if (TOP_SCOPE < 0) { 
    fprintf(RED_OUT, "Error: a pop operation to an empty scope stack.\n"); 
    exit(0); 
  }
  TOP_SCOPE--; 
/*
  fprintf(RED_OUT, "pop a scope %1d:%s at frame %1d\n", 
          top_scope(), scope_name(top_scope()), TOP_SCOPE
          ); 
  print_scope_stack(); 
*/
}
  /* pop_scope() */ 



  
  
  
void	check_choice_formula_local() { 
  switch (top_scope()) {
  case SCOPE_LOCAL: 
    break; 
  case SCOPE_CHOICE: 
    STATUS_FORMULA_CHOICE = STATUS_FORMULA_CHOICE 
        		  | FLAG_FORMULA_CHOICE_LOCAL; 
    break; 
  default:  
    fprintf(RED_OUT, 
	    "Error: a local feature in a non-local formula scope %1d:%s at line %1d.\n", 
	    top_scope(), scope_name(top_scope()), lineno
	    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}
  /* check_choice_formula_local() */ 
  


void	check_choice_formula_global() { 
  switch (top_scope()) {
  case SCOPE_GLOBAL: 
  case SCOPE_GLOBAL_EVENT: 
    break; 
  case SCOPE_CHOICE: 
    STATUS_FORMULA_CHOICE = STATUS_FORMULA_CHOICE 
        		  | FLAG_FORMULA_CHOICE_GLOBAL; 
    break; 
  default:  
    fprintf(RED_OUT, 
      "Error (check_choice_formula_global):\n  a global feature in a non-global formula scope %1d:%s at line %1d.\n", 
	    top_scope(), scope_name(top_scope()), lineno
	    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* check_choice_formula_global() */ 
  


void	check_choice_formula_global_event() { 
  switch (top_scope()) {
  case SCOPE_GLOBAL_EVENT: 
    break; 
  case SCOPE_CHOICE: 
    STATUS_FORMULA_CHOICE = STATUS_FORMULA_CHOICE 
        		  | FLAG_FORMULA_CHOICE_GLOBAL; 
    break; 
  default:  
    fprintf(RED_OUT, 
	    "Error (check_choice_formula_global_event):\n  a global feature in a non-global formula scope %1d:%s at line %1d.\n", 
	    top_scope(), scope_name(top_scope()), lineno
	    ); 
    fflush(RED_OUT); 
    bk(0); 
  } 
}
  /* check_choice_formula_global_event() */ 



int	count_naming_restrictions = 0; 

void	check_naming_restrictions(name)
	char	*name; 
{
/*
  fprintf(RED_OUT, "\n%1d, check naming restrictions: %s\n", 
    ++count_naming_restrictions, name
  ); 
  fflush(RED_OUT); 
*/
  if (strlen(name) >= 3 && name[0] == '_' && name[1] == 'R' && name[2] == '_') { 
    fprintf(RED_OUT, "Error: a bad name %s at line %1d.\n", name, lineno); 
    fprintf(RED_OUT, "       Names starting with ``_R_'' are reserved for system usage.\n"); 
    bk(name); 
  } 
}
  /* check_naming_restrictions() */ 
  
  

struct name_link_type	*push_name(name, name_stack) 
	char			*name; 
	struct name_link_type	*name_stack; 
{ 
  struct name_link_type	*nl; 
  
  nl = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
  nl->name = name; 
  nl->next_name_link = name_stack; 
  
  return(nl); 
}
  /* push_name() */ 
  
  
char	*pop_name(name_stack_ptr) 
	struct name_link_type	**name_stack_ptr; 
{
  char			*name; 
  struct name_link_type	*nl; 
  
  if (*name_stack_ptr == NULL) 
    return(NULL); 
  
  nl = *name_stack_ptr; 
  name = nl->name; 
  *name_stack_ptr = nl->next_name_link; 
  free(nl); 
  
  return(name); 
}
  /* pop_name() */ 
  
  
	
char	*name_check_holder; 

int	name_duplicate(name, name_check_holder_ptr)
  char	*name, **name_check_holder_ptr; 
{
  int					i, type;
  struct ps_bunit_type			*gm;
  struct parse_mode_type		*pm;
  struct parse_variable_type		*pv;
  struct parse_variable_link_type	*pvl;
  struct indexed_structure_link_type	*il; 

/*
  fprintf(RED_OUT, "name_duplicate: %s\n", name); 
  fflush(RED_OUT); 
*/
  if (!strcmp("PC", name)) { 
    fprintf(RED_OUT, "Error: Conflict with reserved words 'PC' at line %1d.\n", 
	    lineno
	    ); 
    exit(0); 
  } 
  
  for (gm = declare_inline_exp_list; gm; gm = gm->bnext)
    if (!strcmp(name, gm->subexp->u.inline_declare.inline_exp_name)) {
      *name_check_holder_ptr = (char *) gm->subexp; 
      return(NAME_MACRO); 
    } 
    
  for (il = process_list; il; il = il->next_indexed_structure_link)
    if (!strcmp(name, il->structure)) {
      *name_check_holder_ptr = (char *) i; 
      return(NAME_PROCESS);
    }
    
  for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) 
    if (!strcmp(name, pm->name)) {
      *name_check_holder_ptr = (char *) pm; 
      return(NAME_MODE); 
    }
    
  for (pv = declare_global_pointer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_POINTER_GLOBAL); 
    } 
    
  for (pv = declare_global_discrete_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) { 
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_DISCRETE_GLOBAL);
    }
    
  for (pv = declare_global_clock_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_CLOCK_GLOBAL); 
    }
    
  for (pv = declare_global_dense_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_DENSE_GLOBAL); 
    }
    
  for (pv = declare_global_synchronizer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_SYNCHRONIZER_GLOBAL);
    }

  /* for locals */ 
  for (pv = declare_local_pointer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_POINTER_LOCAL); 
    } 
    
  for (pv = declare_local_discrete_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) { 
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_DISCRETE_LOCAL);
    }
    
  for (pv = declare_local_clock_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_CLOCK_LOCAL); 
    }
    
  for (pv = declare_local_dense_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_DENSE_LOCAL); 
    }
    
  for (pv = declare_local_synchronizer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) {
      *name_check_holder_ptr = (char *) pv; 
      return(NAME_SYNCHRONIZER_LOCAL);
    }

  return(TYPE_FALSE); 
}
/* name_duplicate() */ 



void	print_inline_declare(psub) 
  struct ps_exp_type	*psub; 
{ 
  struct name_link_type	*nl; 
  
  switch (psub->u.inline_declare.status & MASK_INLINE_TYPE) { 
  case FLAG_INLINE_CONSTANT: 
    fprintf(RED_OUT, "\n#define\t%s\t%1d\n", 
      psub->u.inline_declare.inline_exp_name, 
      psub->u.inline_declare.declare_exp->u.value
    ); 
    return; 
    break; 
  case FLAG_INLINE_BOOLEAN: 
    fprintf(RED_OUT, "inline boolean"); 
    break; 
  case FLAG_INLINE_DISCRETE: 
    fprintf(RED_OUT, "inline discrete "); 
    break; 
  } 
  fprintf(RED_OUT, "%s(", 
    psub->u.inline_declare.inline_exp_name
  ); 
  if (nl = psub->u.inline_declare.formal_argument_list) { 
    fprintf(RED_OUT, "%s", nl->name); 
    for (nl = nl->next_name_link; 
         nl; 
         nl = nl->next_name_link
         ) { 
      fprintf(RED_OUT, ", %s", nl->name);    
    }
  }
  fprintf(RED_OUT, ") {\n  "); 
  pcform(psub->u.inline_declare.declare_exp); 
  fprintf(RED_OUT, "}\n"); 
  fflush(RED_OUT); 
}
  /* print_inline_declare() */ 
  
  
 
macro_register(
  int			flag_type, 
  char			*name, 
  int			formal_argument_count, 
  struct name_link_type	*formal_argument_list, 
  struct ps_exp_type	*declare_exp
) { 
  struct ps_exp_type	*gm; 
  struct ps_bunit_type	*bu; 
 
  /*
  fprintf(RED_OUT, "macro register:[%s], [%1d]\n", name, value);
  */
  check_naming_restrictions(name); 

  if (name_duplicate(name, &name_check_holder)) {
    fprintf(RED_OUT, "\nError in macro register: variable name duplicate: %s at line %1d.\n", name, lineno);
    bk(); 
  } 
  
  switch (flag_type & MASK_INLINE_TYPE) { 
  case FLAG_INLINE_CONSTANT: 
  case FLAG_INLINE_DISCRETE: 
    gm = ps_exp_alloc(TYPE_INLINE_DISCRETE_DECLARE); 
    break; 
  case FLAG_INLINE_BOOLEAN: 
    gm = ps_exp_alloc(TYPE_INLINE_BOOLEAN_DECLARE); 
    break; 
  }
  gm->u.inline_declare.status = (flag_type & MASK_INLINE_TYPE); 
  gm->u.inline_declare.inline_exp_name = name; 
  gm->u.inline_declare.formal_argument_count = formal_argument_count; 
  gm->u.inline_declare.formal_argument_list = formal_argument_list; 
  gm->u.inline_declare.declare_exp = declare_exp; 
  
  bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
  bu->subexp = gm; 
  bu->bnext = declare_inline_exp_list; 
  declare_inline_exp_list = bu; 
  declare_inline_exp_count++; 
  
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "Leaving macro_register():\n"); 
  print_inline_declare(gm); 
/*
  fprintf(RED_OUT, "%1d: macro constant %1s with value %1d registered\n", 
	  gram_macro_count, name, value
	  ); 
*/
  #endif 
}
/* macro_register() */ 





  




int	qfd_sync_name_duplicate(name) 
	char	*name; 
{ 
  struct parse_xtion_sync_type		*xs; 

  if (name_duplicate(name, &name_check_holder)) 
    return(TYPE_TRUE); 
  
  for (xs = CURRENT_XTION->sync_list; xs; xs = xs->next_parse_xtion_sync) 
    if (xs->qsync_var && !strcmp(name, xs->qsync_var->name)) 
      return(TYPE_TRUE); 
  
  return(TYPE_FALSE); 
}
  /* qfd_sync_name_duplicate() */ 
  
  
  
int	sysgen_qsync_var_index = 0, sysgen_qsync_var_count = 0, sysgen_qsync_var_limit = 100; 
struct parse_variable_type **sysgen_qsync_var;

char	*get_a_new_var_name(prefix) 
	char	*prefix; 
{ 
  char	*name; 
  
  name = (char *) malloc(strlen(prefix)+intlen(sysgen_qsync_var_index)+6); 
  sprintf(name, "_R_%s-%1d\0", prefix, sysgen_qsync_var_index++); 
    
  for (; qfd_sync_name_duplicate(name); ) { 
    free(name); 
    name = (char *) malloc(strlen(prefix)+intlen(sysgen_qsync_var_index)+6); 
    sprintf(name, "_R_%s-%1d\0", prefix, sysgen_qsync_var_index++); 
  }
  return(name); 
}
  /* get_a_new_var_name() */ 
  
  

struct parse_variable_type	*get_a_sysgen_qsync_var() { 
  struct parse_variable_type	**nva, *pv;
  int				i; 
  
  if (sysgen_qsync_var_index < sysgen_qsync_var_count) {
    return(sysgen_qsync_var[sysgen_qsync_var_index++]); 
  } 
  
  if (sysgen_qsync_var_index >= sysgen_qsync_var_limit) { 
    sysgen_qsync_var_limit = sysgen_qsync_var_limit + 100; 
    nva = (struct parse_variable_type **) 
	malloc(sysgen_qsync_var_limit * sizeof(struct parse_variable_type *)); 
    for (i = 0; i < sysgen_qsync_var_limit - 100; i++) { 
      nva[i] = sysgen_qsync_var[i]; 
    } 
    free(sysgen_qsync_var); 
    sysgen_qsync_var = nva; 
  } 
  
  pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
  pv->name = (char *) malloc(intlen(sysgen_qsync_var_index)+8); 
  sprintf(pv->name, "_R_QS-%1d\0", sysgen_qsync_var_index++); 
  pv->index = LOCAL_COUNT[TYPE_POINTER]++; 
  CUR_VAR_TYPE = TYPE_POINTER; 
  push_scope(SCOPE_LOCAL); 
  pv->type = CUR_VAR_TYPE;
  pv->Q_xtion_count = 0;
  pv->X_xtion_count = 0;

  /*
    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
   */
  pv->next_parse_variable = declare_local_pointer_list; 
  declare_local_pointer_list = pv; 

  pv->status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
  pv->u.disc.lb = 1;
  pv->u.disc.ub = PROCESS_COUNT;
  pop_scope(); 

  return(pv);
}
  /* get_a_sysgen_qsync_var() */   
  
  
  

struct parse_variable_type	*check_register_qfd_sync(name)
  char	*name;
{
  struct parse_variable_type		*pv;
  struct parse_variable_link_type	*pvl; 
  struct parse_xtion_sync_type		*xs; 
  int					i; 

  check_naming_restrictions(name); 

  switch (name_duplicate(name, &name_check_holder)) {
  case TYPE_FALSE: 
    break; 
  case NAME_POINTER_LOCAL: 
    pv = (struct parse_variable_type *) name_check_holder; 
    if (pv->status & FLAG_QUANTIFIED_SYNC) { 
      return(pv); 
    }
  default: 
    fprintf(RED_OUT, "\nError in check register qfd sync: variable name duplicate: %s at line %1d.\n", name, lineno);
    bk(); 
  }

  for (xs = CURRENT_XTION->sync_list; xs; xs = xs->next_parse_xtion_sync) 
    if (xs->qsync_var && !strcmp(name, xs->qsync_var->name)) { 
      pv = xs->qsync_var; 
      fprintf(RED_OUT, "\nError: a duplicate quantified process holder %s at line %1d.\n", 
	      name, lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
      break; 
    } 
  
  pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
  pv->lineno = lineno; 
  pv->name = name;
  pv->index = LOCAL_COUNT[TYPE_POINTER]++; 
  CUR_VAR_TYPE = TYPE_POINTER; 
  push_scope(SCOPE_LOCAL); 
  pv->type = CUR_VAR_TYPE;
  pv->Q_xtion_count = 0;
  pv->X_xtion_count = 0;

  /*
    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
   */
  pv->next_parse_variable = declare_local_pointer_list; 
  declare_local_pointer_list = pv; 
        
  pv->status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
  pv->u.disc.lb = 1;
  pv->u.disc.ub = PROCESS_COUNT;
  pop_scope(); 

  return(pv);
}
/* check_register_qfd_sync() */



struct parse_variable_type	*check_qfd_sync(pv)
	struct parse_variable_type	*pv;
{
  struct parse_xtion_sync_type		*xs; 

  if (   pv->type != TYPE_POINTER 
      || !(pv->status & FLAG_LOCAL_VARIABLE)
      || !(pv->status & FLAG_QUANTIFIED_SYNC)
      ) { 
    fprintf(RED_OUT, "Syntax error: an unquantified sync variable %s used \n", pv->name); 
    fprintf(RED_OUT, "              in quantified synchronization at line %1d.\n", lineno); 
    bk(); 
  } 
      
  for (xs = CURRENT_XTION->sync_list; xs; xs = xs->next_parse_xtion_sync) 
    if (xs->qsync_var && !strcmp(pv->name, xs->qsync_var->name)) { 
      fprintf(RED_OUT, "\nError: a duplicate quantified process holder %s at line %1d.\n", 
	      pv->name, lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
      break; 
    } 
  
  return(pv);
}
/* check_qfd_sync() */






int	rgv_count = 0; 

struct parse_variable_type	*register_variable(name)
  char	*name;
{
  struct parse_variable_type		*pv;
  int					flag; 

  check_naming_restrictions(name); 

  if (name_duplicate(name, &name_check_holder)) {
    fprintf(RED_OUT, "\nError in register variable: variable name duplicate: %s at line %1d.\n", name, lineno);
    bk(); 
  }

  switch (CUR_VAR_TYPE) {
  case TYPE_CLOCK:
    if (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) != FLAG_SYSTEM_HYBRID
        && strcmp(name, "0")
        && strcmp(name, "TIME")
        && strcmp(name, "delta")
        && strcmp(name, "deltap")
        && strcmp(name, "-delta")
        && strcmp(name, "-deltap")
        && strcmp(name, "MODAL_CLOCK") 
        && strcmp(name, "PLAYTIME") 
        && strcmp(name, "ZENO_CLOCK") 
        ) {
      GSTATUS[INDEX_SYSTEM_TYPE] 
      = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) 
      | FLAG_SYSTEM_TIMED;
    }

    if (top_scope() == SCOPE_LOCAL) {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
        /*
          fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
         */
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_CLOCK]++; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = FLAG_LOCAL_VARIABLE;

      pv->next_parse_variable = declare_local_clock_list; 
      declare_local_clock_list = pv;         
    } 
    else {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_clock_list;
      declare_global_clock_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_CLOCK]++;
    }
    pv->u.clock.lb = pv->u.clock.ub = 0;
    break;
  case TYPE_DENSE: 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\n1. Detecting hybrid system at line %1d.\n", lineno); 
    #endif 
    
    if (strcmp(name, "PROB_DENSE"))
      GSTATUS[INDEX_SYSTEM_TYPE] 
      = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) 
      | FLAG_SYSTEM_HYBRID;
    if (top_scope() == SCOPE_LOCAL) {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_DENSE]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = FLAG_LOCAL_VARIABLE;
	  
      pv->next_parse_variable = declare_local_dense_list; 
      declare_local_dense_list = pv;         
    }
    else {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_dense_list;
      declare_global_dense_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_DENSE]++;
    }
    pv->u.dense.lb = pv->u.dense.ub = 0;
    break;

  case TYPE_QSYNC_HOLDER:
    if (top_scope() != SCOPE_LOCAL_XTION) {
      fprintf(RED_OUT, "\nError: No, a sync place holder must be a local variable %s at line %1d.\n", 
	      name, lineno
	      ); 
      bk(0); 
    } 
    
    pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
    pv->lineno = lineno; 
    pv->index = LOCAL_COUNT[TYPE_QSYNC_HOLDER]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
    pv->name = name;
    pv->Q_xtion_count = 0;
    pv->X_xtion_count = 0;
    pv->type = CUR_VAR_TYPE;
    pv->status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
	  
    pv->next_parse_variable = declare_local_qsholder_list; 
    declare_local_qsholder_list = pv;         
    pv->u.disc.lb = 1; 
    pv->u.disc.ub = PROCESS_COUNT;
    break;

  case TYPE_PARAMETER:
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\n2. Detecting hybrid system at line %1d.\n", lineno); 
    #endif 
    
    GSTATUS[INDEX_SYSTEM_TYPE] 
    = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) 
    | FLAG_SYSTEM_HYBRID;
    pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));
    pv->lineno = lineno; 
    pv->name = name;
    pv->Q_xtion_count = 0;
    pv->X_xtion_count = 0;
    pv->type = TYPE_DENSE;

    pv->next_parse_variable = declare_global_dense_list;
    declare_global_dense_list = pv; 
    pv->index = GLOBAL_COUNT[TYPE_DENSE]++;
    pv->status = FLAG_VAR_STATIC;
    pv->u.dense.lb = pv->u.dense.ub = 0;
    break; 

  case TYPE_STREAM:
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\n2. Detecting stream declarations at line %1d.\n", lineno); 
    #endif 
    
    pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));
    pv->lineno = lineno; 
    pv->name = name;
    pv->Q_xtion_count = 0;
    pv->X_xtion_count = 0;
    pv->type = TYPE_STREAM;

    pv->next_parse_variable = declare_global_stream_list;
    declare_global_stream_list = pv; 
    pv->index = GLOBAL_COUNT[TYPE_STREAM]++;
    switch (top_scope()) {
    case GRAM_STREAM_ORDERED: 
      pv->status = FLAG_STREAM_ORDERED; 
      break; 
    case GRAM_STREAM_UNORDERED: 
      pv->status = FLAG_STREAM_UNORDERED; 
      break; 
    default: 
      fprintf(RED_OUT, "\nIllegal stream type %1d at lineno %1d\n", 
        top_scope(), lineno
      ); 
      exit(0); 
    } 
    pv->u.disc.lb = pv->u.disc.ub = 0;

    break; 

  case TYPE_BDD:
    if (top_scope() == SCOPE_LOCAL) {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_BDD]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_local_bdd_list; 
      declare_local_bdd_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE;
    }
    else {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

/*      
	fprintf(RED_OUT, "\npv = %x in register_variable(%s)\n", pv, name);
*/	
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_bdd_list;
      declare_global_bdd_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_BDD]++;
    }
    pv->u.bdd.lb = 0; 
    pv->u.bdd.ub = 1;
    break;

  case TYPE_DISCRETE:
    switch (top_scope()) {
    case SCOPE_STACK: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = count_stack_discrete++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_stack_discrete_list; 
      declare_stack_discrete_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE | FLAG_VAR_STACK;
      break; 
    case SCOPE_LOCAL: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_DISCRETE]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_local_discrete_list; 
      declare_local_discrete_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE;
      break; 
    default: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_discrete_list;
      declare_global_discrete_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_DISCRETE]++;
    }
    pv->u.disc.lb = pv->u.disc.ub = 0;
    break;
  case TYPE_FLOAT:
    switch (top_scope()) {
    case SCOPE_STACK: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = count_stack_float++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_stack_float_list; 
      declare_stack_float_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE | FLAG_VAR_STACK;
      break; 
    case SCOPE_LOCAL: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_FLOAT]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_local_float_list; 
      declare_local_float_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE;
      break; 
    default: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_float_list;
      declare_global_float_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_FLOAT]++;
    }
    pv->u.flt.lb = -1 * FLT_MAX; 
    pv->u.flt.ub = FLT_MAX;
    break;
  case TYPE_DOUBLE:
    switch (top_scope()) {
    case SCOPE_STACK: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = count_stack_double++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_stack_double_list; 
      declare_stack_double_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE | FLAG_VAR_STACK;
      break; 
    case SCOPE_LOCAL: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_DOUBLE]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_local_double_list; 
      declare_local_double_list = pv; 
      pv->status = FLAG_LOCAL_VARIABLE;
      break; 
    default: 
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = 0;

      pv->next_parse_variable = declare_global_double_list;
      declare_global_double_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_DOUBLE]++;
    }
    pv->u.dble.lb = -1 * DBL_MAX; 
    pv->u.dble.ub = DBL_MAX;
    break;

  case TYPE_POINTER:
    if (top_scope() == SCOPE_LOCAL) {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_POINTER]++; 
	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = TYPE_DISCRETE;

      pv->next_parse_variable = declare_local_pointer_list; 
      declare_local_pointer_list = pv; 
      pv->u.disc.lb = 0;
      pv->u.disc.ub = PROCESS_COUNT;
        
      pv->status = FLAG_LOCAL_VARIABLE 
      | FLAG_POINTER | FLAG_BOUND_DECLARED;
    }
    else {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = TYPE_DISCRETE;
      pv->status = FLAG_POINTER | FLAG_BOUND_DECLARED;

      pv->next_parse_variable = declare_global_pointer_list;
      declare_global_pointer_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_POINTER]++;
      pv->u.disc.lb = 0;
      pv->u.disc.ub = PROCESS_COUNT;
    }
    break;

  case TYPE_SYNCHRONIZER:
    if (top_scope() == SCOPE_LOCAL) {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type)); 
      pv->lineno = lineno; 
      pv->index = LOCAL_COUNT[TYPE_SYNCHRONIZER]++; 

	/*
	    fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;

      pv->next_parse_variable = declare_global_synchronizer_list; 
      declare_global_synchronizer_list = pv; 
        
      pv->status = FLAG_LOCAL_VARIABLE | FLAG_SYNCHRONIZER;
      pv->u.sync.lb = 0; 
      pv->u.sync.ub = 1;
    }
    else {
      pv = (struct parse_variable_type *) malloc(sizeof(struct parse_variable_type));

      /*
	fprintf(RED_OUT, "\npv = %x in register_variable()\n", pv);
	*/
      pv->lineno = lineno; 
      pv->name = name;
      pv->Q_xtion_count = 0;
      pv->X_xtion_count = 0;
      pv->type = CUR_VAR_TYPE;
      pv->status = FLAG_SYNCHRONIZER;

      pv->next_parse_variable = declare_global_synchronizer_list;
      declare_global_synchronizer_list = pv;
      pv->index = GLOBAL_COUNT[TYPE_SYNCHRONIZER]++;
      pv->u.sync.lb = 0; 
      pv->u.sync.ub = 1;
    }
    break;

  default:
    fprintf(RED_OUT, "\nError: Illegal variable type %s at line %1d.\n", name, lineno);
    fflush(RED_OUT);
    exit(0);
  }
  return(pv);
}
/* register_variable() */



struct parse_variable_type	*parse_variable_list_reverse(
  struct parse_variable_type	*pv_list 
) { 
  struct parse_variable_type	*pv, *tpv; 
  
  for (pv = NULL; pv_list; ) { 
    tpv = pv_list; 
    pv_list = pv_list->next_parse_variable; 
    tpv->next_parse_variable = pv; 
    pv = tpv; 
  } 
  return (pv); 
}
  /* parse_variable_list_reverse() */  




char	*inline_formal_argument_search(char *name) { 
  struct name_link_type	*nl; 
  
  for (nl = CURRENT_INLINE_FORMAL_ARGUMENT_LIST; 
       nl; 
       nl = nl->next_name_link
       ) { 
    if (!strcmp(nl->name, name)) 
      return(name);    
  } 
  return(NULL); 
}
  /* inline_formal_argument_search() */ 




struct ps_exp_type	*macro_search(name)
  char	*name;
{
  struct ps_bunit_type	*bu;
  struct ps_exp_type	*gm; 
  
  /*
  fflush(RED_OUT);
  fprintf(RED_OUT, "\nSearching for macro %s at line %1d\n",
	  name, lineno
	  );
  */
  for (bu = declare_inline_exp_list; bu; bu = bu->bnext) {
    gm = bu->subexp; 
    /*
    fprintf(RED_OUT, "    comparing with (%s)", 
      gm->u.inline_declare.inline_exp_name
    );
    */
    if (!strcmp(name, gm->u.inline_declare.inline_exp_name)) {
      /*
      fprintf(RED_OUT, "  Match! \n");
      */
      return(gm);
    }
    else {
      /*
      fprintf(RED_OUT, "  \n");
      */
    }
  }
  /*
  fprintf(RED_OUT, "No Match!\n");
  */
  fflush(RED_OUT);
  return(NULL);
}
/* macro_search() */



struct parse_variable_type	*var_search(name) 
  char				*name; 
{
  struct parse_variable_type		*pv;

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "  var_search(%s) at lineno %1d;\n", name, lineno); 
  fflush(RED_OUT); 
  #endif 
  
  for (pv = declare_stack_discrete_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_local_discrete_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_stack_float_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_local_float_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_stack_double_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_local_double_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_local_pointer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name))
      return(pv);

  for (pv = declare_local_bdd_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_local_clock_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name))
      return(pv);

  for (pv = declare_local_dense_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name))
      return(pv);
      
  for (pv = declare_global_pointer_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name))
      return(pv);

  for (pv = declare_global_discrete_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_global_float_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_global_double_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_global_bdd_list; pv; pv = pv->next_parse_variable) 
    if (!strcmp(name, pv->name)) 
      return(pv); 

  for (pv = declare_global_clock_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name))
      return(pv);

  for (pv = declare_global_dense_list; pv; pv = pv->next_parse_variable)
    if (!strcmp(name, pv->name))
      return(pv);
      
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\n------------------\n"); 
  #endif 
  
  for (pv = declare_global_synchronizer_list; pv; pv = pv->next_parse_variable) {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "synchronizers '%s' compared to '%s'\n", pv->name, name); 
    #endif 
        
    if (!strcmp(name, pv->name)) 
      return(pv); 
  }
  for (pv = declare_global_stream_list; pv; pv = pv->next_parse_variable) {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "stream '%s' compared to '%s'\n", pv->name, name); 
    #endif 
        
    if (!strcmp(name, pv->name)) 
      return(pv); 
  }
  return(NULL); 
  
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nError: Unrecognized variable name %s at line %1d\n", 
	  name, lineno
	  );
  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
  exit(10);
  #endif 
}
/* var_search() */ 



struct parse_mode_type	*mode_search(name)
  char	*name; 
{
  struct parse_mode_type	*pm;

  for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) 
    if (!strcmp(pm->name, name))
      return(pm);

  return(NULL); 
}
/* mode_search() */ 







int	sync_list_equal(la, lb) 
     struct parse_sync_type	*la, *lb;
{
  for (; 
       la != NULL && lb != NULL; 
       la = la->next_parse_sync, lb = lb->next_parse_sync
       ) 
    if (la->sync_var != lb->sync_var) 
      return(TYPE_FALSE); 

  if (la != NULL || lb != NULL) 
    return(TYPE_FALSE);
  else
    return(TYPE_TRUE); 
}
/* sync_list_equal() */




struct parse_xtion_sync_type	*add_parse_xtion_sync(
  int				place_index, 
  int				flag_address_type, 
  int				type, // > 0: ?, < 0: !
  struct parse_variable_type	*sync_var, 
  struct ps_exp_type		*multiplicity_exp, 
  struct ps_exp_type		*qsync_exp
) { 
  struct parse_xtion_sync_type		*xs; 
  struct parse_variable_type		*pv; 
  char					*name; 
  
  int	pre; 
  
/*
  if (CURRENT_XTION->index == 1600) 
    for (fprintf(RED_OUT, "Target hit!\n"), fflush(RED_OUT), pre = 1; pre; ); 
*/    
  xs = (struct parse_xtion_sync_type *) 
	malloc(sizeof(struct parse_xtion_sync_type));
  xs->next_parse_xtion_sync = CURRENT_XTION->sync_list; 
  CURRENT_XTION->sync_list = xs;
  xs->type = type; 

  #ifdef RED_DEBUG_PARSE_MODE 
  if (type > 0) 
    fprintf(RED_OUT, "XT %1d, ?%1d:%s, a place index=%1d\n", 
      CURRENT_XTION->index, sync_var->index, sync_var->name, place_index
    ); 
  else 
    fprintf(RED_OUT, "XT %1d, !%1d:%s, a place index=%1d\n", 
      CURRENT_XTION->index, sync_var->index, sync_var->name, place_index
    ); 
  fprintf(RED_OUT, "  MC:"); 
  if (multiplicity_exp != (struct ps_exp_type *) 1) 
    pcform(multiplicity_exp); 
  fflush(RED_OUT); 
  #endif 

  xs->place_index = place_index; 
  xs->status = flag_address_type; 
  xs->sync_var = sync_var; 
  xs->exp_multiplicity = multiplicity_exp; 
  xs->exp_quantification = qsync_exp; 
  if (place_index < LOCAL_COUNT[TYPE_QSYNC_HOLDER]) {
    for (pv = declare_local_qsholder_list; pv; pv = pv->next_parse_variable) 
      if (pv->index == place_index) 
	break; 
    xs->place_holder_var = pv; 
/*
    fprintf(RED_OUT, "\nFound an old place holder variable %1d:%s\n", 
      pv->index, 
      pv->name
    ); 
*/
  }
  else { 
    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    name = (char *) malloc(5+intlen(place_index)); 
    sprintf(name, "SP-%1d\0", place_index); 
    xs->place_holder_var = register_variable(name); 
/*
    fprintf(RED_OUT, "\nAdd a new place holder variable %1d:%s\n", 
      xs->place_holder_var->index, 
      xs->place_holder_var->name
    ); 
*/
  } 
  if (qsync_exp && qsync_exp->type == TYPE_QSYNC_HOLDER) { 
    xs->qsync_var = qsync_exp->u.qsholder.qsync_var; 
    qsync_exp->u.qsholder.place_holder_var = xs->place_holder_var; 
  } 
  else 
    xs->qsync_var = NULL; 

  CURRENT_XTION->sync_count++; 
  if (type < 0 /* ! */) 
    sync_var->X_xtion_count++; 
  else 
    sync_var->Q_xtion_count++; 

  #ifdef RED_DEBUG_PARSE_MODE 
  fprintf(RED_OUT, "\ngram: x %1d, sync %1d, type %1d, status %1d\n", 
    CURRENT_XTION->index, place_index, type, flag_address_type 
  ); 
  if (xs->exp_quantification) 
    pcform(xs->exp_quantification); 
  fflush(RED_OUT); 
  #endif 

  return(CURRENT_XTION->sync_list); 
}
  /* add_parse_xtion_sync() */ 
  
  


void	replicate_parse_xtion_sync(
  struct parse_xtion_type	*px,  
  struct parse_xtion_sync_type	*pxs 
) { 
  struct parse_xtion_sync_type	*xs; 
  struct parse_variable_type	*pv; 
  char				*name; 
  
/*
  if (CURRENT_XTION->index == 1600) 
    for (fprintf(RED_OUT, "Target hit!\n"), fflush(RED_OUT), pre = 1; pre; ); 
*/    
  xs = (struct parse_xtion_sync_type *) 
	malloc(sizeof(struct parse_xtion_sync_type));
  *xs = *pxs; 
  xs->status = FLAG_ADDRESS_DUPLICATE; 
  xs->next_parse_xtion_sync = pxs->next_parse_xtion_sync; 
  pxs->next_parse_xtion_sync = xs; 
  xs->place_index = px->sync_count; 
  #ifdef RED_DEBUG_PARSE_MODE 
  if (pxs->type > 0) 
    fprintf(RED_OUT, "XT %1d, ?%1d:%s, a replicate place index=%1d\n", 
      CURRENT_XTION->index, pxs->sync_var->index, pxs->sync_var->name, 
      xs->place_index
    ); 
  else 
    fprintf(RED_OUT, "XT %1d, !%1d:%s, a replicate place index=%1d\n", 
      CURRENT_XTION->index, pxs->sync_var->index, pxs->sync_var->name, 
      xs->place_index
    ); 
  #endif 

  if (xs->place_index < LOCAL_COUNT[TYPE_QSYNC_HOLDER]) {
    for (pv = declare_local_qsholder_list; pv; pv = pv->next_parse_variable) 
      if (pv->index == px->sync_count) 
	break; 
    xs->place_holder_var = pv; 
/*
    fprintf(RED_OUT, "\nReplicate an old place holder variable %1d:%s\n", 
      pv->index, 
      pv->name
    ); 
    fflush(RED_OUT); 
*/
  }
  else { 
    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    name = (char *) malloc(5+intlen(xs->place_index)); 
    sprintf(name, "SP-%1d\0", xs->place_index); 
    push_scope(SCOPE_LOCAL_XTION); 
    xs->place_holder_var = register_variable(name); 
    TOP_SCOPE--; 
/*
    fprintf(RED_OUT, "\nReplicate a new place holder variable %1d:%s\n", 
      xs->place_holder_var->index, 
      xs->place_holder_var->name
    ); 
    fflush(RED_OUT); 
*/
  } 

  px->sync_count++; 
  if (pxs->type < 0 /* ! */) 
    pxs->sync_var->X_xtion_count++; 
  else 
    pxs->sync_var->Q_xtion_count++; 
  xs->exp_multiplicity = NULL; 
  xs->exp_quantification = ps_exp_copy(pxs->exp_quantification); 
  if (   xs->exp_quantification 
      && xs->exp_quantification->type == TYPE_QSYNC_HOLDER
      ) { 
    xs->qsync_var = xs->exp_quantification->u.qsholder.qsync_var; 
    xs->exp_quantification->u.qsholder.place_holder_var = xs->place_holder_var; 
  } 
  else 
    xs->qsync_var = NULL; 
}
  /* replicate_parse_xtion_sync() */ 
  
  

int	qfd_var_undefined(name) 
  char	*name; 
{
  struct name_link_type	*qfd; 
  /*
  fflush(RED_OUT);
  fprintf(RED_OUT, "\nSearching for macro %s at line %1d\n", 
	  name, lineno
	  );
  */
  for (qfd = qfd_stack; qfd; qfd = qfd->next_name_link) {
    /*
    fprintf(RED_OUT, "    comparing with (%s)", qfd->name); 
    */
    if (!strcmp(name, qfd->name)) {
      /*
      fprintf(RED_OUT, "  Match! \n"); 
      */
      return(TYPE_FALSE); 
    }
    else {
      /*
      fprintf(RED_OUT, "  \n"); 
      */
    }
  } 
  /*
  fprintf(RED_OUT, "No Match!\n");
  */
  fflush(RED_OUT); 
  return(TYPE_TRUE); 
}
/* qfd_var_undefined() */ 




struct ps_exp_type	*pexp_remove_neg(psub, flag_positive)
     struct ps_exp_type	*psub;
     int		flag_positive;
{
  int			i, jj, epi, cepi;
  struct ps_bunit_type	*pbu, dummy_bu;
  struct ps_exp_type	*tmp, *newsub, *child;

  switch(psub->type) {
  case TYPE_FALSE :
    if (!flag_positive)
      return(PS_EXP_TRUE);
    else 
      return(PS_EXP_FALSE);
  case TYPE_TRUE :
    if (!flag_positive)
      return(PS_EXP_FALSE);
    else 
      return(PS_EXP_TRUE);

  case TYPE_MODE_INDEX: 
  case TYPE_CONSTANT:
  case TYPE_MACRO_CONSTANT: 
  case TYPE_NULL:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_QFD:
  case TYPE_QSYNC_HOLDER: 
  case TYPE_INLINE_ARGUMENT: 
    return(psub); 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
    newsub = ps_exp_copy(psub); 
    newsub->u.exp = pexp_remove_neg(psub->u.exp, TYPE_TRUE); 
    newsub->u.exp = pexp_remove_neg(psub->u.exp, TYPE_TRUE); 
    return(ps_exp_share(newsub)); 

  case TYPE_CLOCK: 
  case TYPE_DENSE: 
  case TYPE_DISCRETE:
  case TYPE_POINTER: 
    newsub = ps_exp_copy(psub); 
    newsub->u.atom.exp_base_proc_index 
    = pexp_remove_neg(psub->u.atom.exp_base_proc_index, TYPE_TRUE); 
/*
    for (jj = 0; jj < psub->u.atom.indirect_count; jj++) { 
      newsub->u.atom.indirect_exp[jj] 
      = pexp_remove_neg(newsub->u.atom.indirect_exp[jj], flag_positive); 
    }
*/
    return(ps_exp_share(newsub)); 

  case BIT_NOT: 
    newsub = ps_exp_copy(psub); 
    newsub->u.exp = pexp_remove_neg(psub->u.exp, TYPE_TRUE); 
    return(ps_exp_share(newsub)); 

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_MINUS:
  case ARITH_ADD:
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    newsub = ps_exp_copy(psub); 
    newsub->u.arith.lhs_exp = pexp_remove_neg(psub->u.arith.lhs_exp, TYPE_TRUE); 
    newsub->u.arith.rhs_exp = pexp_remove_neg(psub->u.arith.rhs_exp, TYPE_TRUE); 
    return(ps_exp_share(newsub)); 

  case ARITH_CONDITIONAL: 
    newsub = ps_exp_copy(psub); 
    newsub->u.arith_cond.cond = pexp_remove_neg(psub->u.arith_cond.cond, TYPE_TRUE); 
    newsub->u.arith_cond.if_exp = pexp_remove_neg(psub->u.arith_cond.if_exp, TYPE_TRUE); 
    newsub->u.arith_cond.else_exp = pexp_remove_neg(psub->u.arith_cond.else_exp, TYPE_TRUE); 
    if (!flag_positive) 
      return(add_neg(ps_exp_share(newsub))); 
    else 
      return(ps_exp_share(newsub)); 
  
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    if (!flag_positive)
      return(add_neg(psub)); 
    else 
      return(psub);
  case EQ : 
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = NEQ; 
      return(ps_exp_share(newsub)); 
    }
    else 
      return(psub);
  case NEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = EQ; 
      return(ps_exp_share(newsub)); 
    }
    else 
      return(psub);
  case LEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = GREATER; 
      return(ps_exp_share(newsub)); 
    }
    else 
      return(psub);
  case LESS :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = GEQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case GREATER :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = LEQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case GEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = LESS; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);

  case ARITH_EQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_NEQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);

  case ARITH_NEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_EQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case ARITH_LEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_GREATER; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case ARITH_LESS :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_GEQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case ARITH_GREATER :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_LEQ; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub);
  case ARITH_GEQ :
    if (!flag_positive) {
      newsub = ps_exp_copy(psub); 
      newsub->type = ARITH_LESS; 
      return(ps_exp_share(newsub)); 
    } 
    else 
      return(psub); 
  case TYPE_INLINE_CALL: 
    if (psub->u.inline_call.instantiated_exp)  
      return(pexp_remove_neg(psub->u.inline_call.instantiated_exp, flag_positive)); 
    else 
      return(pexp_remove_neg(
        psub->u.inline_call.inline_declare->u.inline_declare.declare_exp, 
        flag_positive
      ) ); 
  case AND :
    newsub = ps_exp_copy(psub); 
    if (!flag_positive) { 
      newsub->type = OR; 
    } 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      child = pexp_remove_neg(pbu->subexp, flag_positive); 
      if (child == PS_EXP_FALSE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        return(PS_EXP_FALSE); 
      } 
      insert_sorted_blist_dummy_head(
        AND, 
        child, 
        &dummy_bu, 
        &(newsub->u.bexp.len)
      ); 
    }
    
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_TRUE); 

    case 1: 
      child = dummy_bu.bnext->subexp; 
      free(dummy_bu.bnext); 
      free(newsub); 
      return(child); 

    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub)); 
    }
    break; 

  case OR :
    newsub = ps_exp_copy(psub); 
    if (!flag_positive) { 
      newsub->type = AND; 
    } 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (jj = psub->u.bexp.len, pbu = psub->u.bexp.blist;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      child = pexp_remove_neg(pbu->subexp, flag_positive); 
      if (child == PS_EXP_TRUE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        return(PS_EXP_TRUE); 
      } 
      insert_sorted_blist_dummy_head(
        OR, 
        child,  
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    switch (newsub->u.bexp.len) { 
    case 0: 
      free(newsub); 
      return(PS_EXP_FALSE); 

    case 1: 
      child = dummy_bu.bnext->subexp; 
      free(dummy_bu.bnext); 
      free(newsub); 
      return(child); 

    default: 
      newsub->u.bexp.blist = dummy_bu.bnext; 
      return(ps_exp_share(newsub)); 
    }
    break; 

  case NOT :
    if (flag_positive)
      flag_positive = TYPE_FALSE;
    else
      flag_positive = TYPE_TRUE;
    return(pexp_remove_neg(psub->u.bexp.blist->subexp, flag_positive));

  case IMPLY :
    newsub = ps_exp_copy(psub); 
    if (flag_positive) {
      newsub->type = OR;
      newsub->u.bexp.len = 0; 
      dummy_bu.bnext = NULL; 
      insert_sorted_blist_dummy_head(
        OR, 
        pexp_remove_neg(psub->u.bexp.blist->subexp, TYPE_FALSE), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
      insert_sorted_blist_dummy_head(
        OR, 
        pexp_remove_neg(psub->u.bexp.blist->bnext->subexp, TYPE_TRUE), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    }
    else {
      newsub->type = AND;
      newsub->u.bexp.len = 0; 
      dummy_bu.bnext = NULL; 
      insert_sorted_blist_dummy_head(
        AND, 
        pexp_remove_neg(psub->u.bexp.blist->subexp, TYPE_TRUE), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
      insert_sorted_blist_dummy_head(
        AND, 
        pexp_remove_neg(psub->u.bexp.blist->bnext->subexp, TYPE_FALSE), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    } 
    newsub->u.bexp.blist = dummy_bu.bnext; 
    return(ps_exp_share(newsub)); 

  case FORALL :
    newsub = ps_exp_copy(psub); 
    newsub->u.qexp.lb_exp = pexp_remove_neg(psub->u.qexp.lb_exp, TYPE_TRUE);
    newsub->u.qexp.ub_exp = pexp_remove_neg(psub->u.qexp.ub_exp, TYPE_TRUE);
    if (flag_positive) {
      newsub->u.qexp.child = pexp_remove_neg(psub->u.qexp.child, TYPE_TRUE);
    }
    else {
      newsub->type = EXISTS;
      newsub->u.qexp.child = pexp_remove_neg(psub->u.qexp.child, TYPE_FALSE);
    }
    return(ps_exp_share(newsub));

  case EXISTS :
    newsub = ps_exp_copy(psub); 
    newsub->u.qexp.lb_exp = pexp_remove_neg(psub->u.qexp.lb_exp, TYPE_TRUE);
    newsub->u.qexp.ub_exp = pexp_remove_neg(psub->u.qexp.ub_exp, TYPE_TRUE);
    if (flag_positive) {
      newsub->u.qexp.child = pexp_remove_neg(psub->u.qexp.child, TYPE_TRUE);
    }
    else {
      newsub->type = FORALL;
      newsub->u.qexp.child = pexp_remove_neg(psub->u.qexp.child, TYPE_FALSE);
    }
    return(ps_exp_share(newsub));

  default:
    fprintf(RED_OUT, 
      "\nError 7: Unrecognized condition operator[%d] at lineno %1d at removing.\n", 
      psub->type, lineno
    );
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(12);
  }
}
/* pexp_remove_neg() */



int	mif_count = 0; 
int	count_inline_call_static = 0; 




struct instantiated_argument_type { 
  char					*formal_argument_name; 
  struct ps_exp_type			*instantiated_argument; 
  struct instantiated_argument_type	*next_instantiated_argument; 
}; 

struct actual_argument_frame_type { 
  struct instantiated_argument_type	*instantiated_argument_list; 
  struct actual_argument_frame_type	*next_actual_argument_frame; 
} 
  *top_inline_stack = NULL; 
  
  

int	count_inline_inst = 0; 

inline int	arith_calculate(int op, int lv, int rv) {
  switch (op) { 
  case ARITH_ADD:
    return(lv + rv); 
  case ARITH_MINUS:
    return(lv - rv); 
  case ARITH_MULTIPLY:
    return(lv * rv); 
  case ARITH_DIVIDE:
    return(lv / rv); 
  case ARITH_MODULO:
    return(lv % rv); 
  case ARITH_MAX:
    return(int_max(lv, rv)); 
  case ARITH_MIN:
    return(int_min(lv, rv)); 
  case BIT_OR: 
    return(lv | rv); 
  case BIT_AND: 
    return(lv & rv); 
  case BIT_SHIFT_RIGHT: 
    return(lv >> rv); 
  case BIT_SHIFT_LEFT: 
    return(lv << rv); 
  }
}
  /* arith_calculate() */ 
  
  
  
inline int 	ineq_calculate(int op, int lv, int rv) { 
  switch (op) {
  case ARITH_EQ :
    if (lv == rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_NEQ :
    if (lv != rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_LEQ :
    if (lv <= rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_LESS :
    if (lv < rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_GREATER :
    if (lv > rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case ARITH_GEQ :
    if (lv >= rv) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  } 
}
  /* ineq_calculate() */ 
  


#define	FLAG_NO_PI_STATIC_EVAL	-1 

int			PI_STATIC_EVAL; 
struct sync_xtion_type	*PSX_STATIC_EVAL; 
  
struct ps_exp_type 
  *rec_static_evaluation(struct ps_exp_type *); 


struct ps_fairness_link_type	*rec_static_seq_evaluation( 
  struct ps_fairness_link_type	*list,  
  int				*fcount_ptr 
) { 
  struct ps_fairness_link_type	*fl, *nfl, *rlist;
  
  rlist = NULL;  
  *fcount_ptr = 0; 
  for (fl = list; fl; fl = fl->next_ps_fairness_link) { 
    rlist = insert_sorted_flist(
      rec_static_evaluation(fl->fairness), 
      fl->status, 
      rlist, 
      fcount_ptr  
    ); 
  } 
  return(rlist); 
} 
  /* rec_static_seq_evaluation() */  





int				count_inline_call_instance = 0; 
int				count_static_evaluation = 0; 
struct ps_exp_type		*tseval; 
struct ps_fairness_link_type	*CURRENT_MULTIPLE_FAIRNESS_LINK_IN_STATIC_EVAL; 

struct ps_exp_type	*rec_static_evaluation(psub)
     struct ps_exp_type	*psub; 
{
  int					i, jj, rec_count, value, 
					llb, ulb, lub, uub, local_count;
  struct ps_exp_type			*newsub, *child, *child2; 
  struct ps_bunit_type			*pbu, dummy_bu; 
  struct actual_argument_frame_type	*top;
  struct ps_fairness_link_type		*fl, *fl_tail; 
  struct name_link_type			*nl, *pnl, dummy_nl, *nl_tail; 
  struct instantiated_argument_type	*ia, dummy_ia, *ia_tail; 


  local_count = ++count_static_evaluation; 
  #ifdef RED_DEBUG_YACC_MODE
//  if (count_static_evaluation == 132) { 
    fprintf(RED_OUT, 
      "\nstatic evaluation = %1d, entering rec_static_evaluation().\n", 
      count_static_evaluation
    ); 
    fflush(RED_OUT); 
    pcform(psub); 
    fflush(RED_OUT); 
//  }
  #endif 
  
  if (!psub) 
    return(NULL); 

  switch(psub->type) {
  case TYPE_NULL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = TYPE_CONSTANT; 
    newsub->u.value = 0; 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_PROCESS_COUNT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = TYPE_CONSTANT; 
    newsub->u.value = PROCESS_COUNT; 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_MODE_COUNT: 
    psub->u.value = MODE_COUNT; 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = TYPE_CONSTANT; 
    newsub->u.value = MODE_COUNT; 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_XTION_COUNT: 
    psub->u.value = XTION_COUNT; 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = TYPE_CONSTANT; 
    newsub->u.value = XTION_COUNT; 
    newsub = ps_exp_share(newsub); 
    break; 
 
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
    newsub = psub; 
    break; 

  case TYPE_LOCAL_IDENTIFIER:
    if (PI_STATIC_EVAL > 0 && PI_STATIC_EVAL <= PROCESS_COUNT) {
      newsub = exp_atom(TYPE_CONSTANT, PI_STATIC_EVAL, NULL); 
      break; 
    } 

  case TYPE_QSYNC_HOLDER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
    newsub = psub; 
    break; 

  case TYPE_QFD: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->type = TYPE_CONSTANT; 
    newsub->u.value = qfd_value(psub->u.atom.var_name);
    newsub = ps_exp_share(newsub); 
    break; 
    
  case TYPE_MODE_INDEX: 
    psub->u.mode_index.parse_mode 
    = search_parse_mode(psub->u.mode_index.mode_name); 
    if (psub->u.mode_index.parse_mode == NULL) { 
      fprintf(RED_OUT, "\nError: Undefined mode name %s at line %1d.\n", 
        psub->u.mode_index.mode_name, psub->lineno
      ); 
      bk(0); 
    } 
    newsub = ps_exp_alloc(TYPE_CONSTANT); 
    newsub->u.value 
    = psub->u.mode_index.value 
    = psub->u.mode_index.parse_mode->index; 
    newsub = ps_exp_share(newsub); 
    break; 
    
  case TYPE_MACRO_CONSTANT: 
    newsub = ps_exp_alloc(TYPE_CONSTANT); 
    newsub->u.value 
    = psub->u.inline_call.inline_declare
    ->u.inline_declare.declare_exp
    ->u.value; 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_REFERENCE:
  case TYPE_DEREFERENCE:
/*
    fprintf(RED_OUT, 
      "\nIn static evaluation, status %x, for: ", 
      psub->status 
    ); 
    pcform(psub); 
    fflush(RED_OUT); 
*/    
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_static_evaluation(psub->u.exp); 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_POINTER: 
    if (   PSX_STATIC_EVAL
        && PI_STATIC_EVAL > 0
        && PI_STATIC_EVAL <= PROCESS_COUNT 
        && (VAR[psub->u.atom.var_index].STATUS & FLAG_QUANTIFIED_SYNC)
        ) { 
      i = VAR[psub->u.atom.var_index].OFFSET; 
      return(exp_atom(TYPE_CONSTANT, 
        get_qsync_value_in_sync_xtion( 
          variable_index[TYPE_POINTER][PI_STATIC_EVAL][i], 
          PSX_STATIC_EVAL
        ), 
        NULL 
      ) ); 
    } 

  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT:
  case TYPE_DOUBLE:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_BDD: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
/*
    if (psub->u.atom.indirect_count) {
      newsub->u.atom.indirect_exp = (struct ps_exp_type **) 
        malloc(psub->u.atom.indirect_count 
        * sizeof(struct ps_exp_type *) 
        ); 
      for (i = 0; i < psub->u.atom.indirect_count; i++) 
        newsub->u.atom.indirect_exp[i] = rec_static_evaluation(
          psub->u.atom.indirect_exp[i]
        ); 
    } 
*/
/*
    fprintf(RED_OUT, "\nstatic evaluation %1d\n", local_count); 
    fflush(RED_OUT); 
*/     
/*
    if (psub->u.atom.indirect_vi) {
      newsub->u.atom.indirect_vi = (int *) 
        malloc((PROCESS_COUNT+1) * sizeof(int) 
      ); 
      for (i = 1; i <= PROCESS_COUNT; i++) 
        newsub->u.atom.indirect_vi[i] = psub->u.atom.indirect_vi[i]; 
    } 
*/
    newsub->u.atom.exp_base_proc_index 
    = rec_static_evaluation(psub->u.atom.exp_base_proc_index); 
    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_INTERVAL:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.interval.lbound_exp 
    = rec_static_evaluation(psub->u.interval.lbound_exp);  
    newsub->u.interval.rbound_exp 
    = rec_static_evaluation(psub->u.interval.rbound_exp);  
    if (   newsub->u.interval.lbound_exp 
        && newsub->u.interval.lbound_exp->type == TYPE_CONSTANT
        && newsub->u.interval.rbound_exp 
        && newsub->u.interval.rbound_exp->type == TYPE_CONSTANT
        && (!(newsub->u.interval.status & INTERVAL_LEFT_OPEN)) 
        && (!(newsub->u.interval.status & INTERVAL_RIGHT_OPEN)) 
        && newsub->u.interval.lbound_exp->u.value
           == newsub->u.interval.rbound_exp->u.value
        ) { 
      value = newsub->u.interval.lbound_exp->u.value; 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = value; 
    }
    newsub = ps_exp_share(newsub); 
    break; 
    
  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_static_evaluation(psub->u.exp);  
    if (newsub->u.exp->type == TYPE_CONSTANT) { 
      value = ~newsub->u.exp->u.value; 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = value; 
      newsub = ps_exp_share(newsub); 
    } 
    else { 
      newsub = ps_exp_share(newsub); 
    }
    break; 
  
  case ARITH_DIVIDE:
    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
        == FLAG_SYSTEM_HYBRID
        ) {
      newsub = ps_exp_alloc(psub->type); 
      *newsub = *psub; 
      newsub->u.arith.lhs_exp 
      = rec_static_evaluation(psub->u.arith.lhs_exp);  
      newsub->u.arith.rhs_exp 
      = rec_static_evaluation(psub->u.arith.rhs_exp);  
      newsub = ps_exp_share(newsub); 
/*
      fprintf(RED_OUT, "\nStatic valuating with %1d, s%x: ", 
        ++count_static_evaluation, newsub->status
      ); 
      pcform(newsub); 
*/
      break; 
    }

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp 
    = rec_static_evaluation(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp 
    = rec_static_evaluation(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      value = arith_calculate(
        psub->type, 
        newsub->u.arith.lhs_exp->u.value,  
        newsub->u.arith.rhs_exp->u.value
      ); 
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = value; 
      newsub = ps_exp_share(newsub); 
    } 
    else { 
      newsub = ps_exp_share(newsub); 
    }
/*
    fprintf(RED_OUT, "\nStatic valuating with %1d, s%x: ", 
      ++count_static_evaluation, newsub->status
    ); 
    pcform(newsub); 
*/
    break; 
  
  case ARITH_SUM: {
    float	flb, fub; 
    int		flag, flag_constant, sum; 
    
    flag = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      newsub = PS_EXP_ZERO; 
      break; 
    } 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    flag_constant = TYPE_TRUE; 
    sum = 0; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      child = rec_static_evaluation(psub->u.qexp.child); 
      if (child->type == TYPE_CONSTANT) {
        sum = sum + child->u.value; 
      }
      else 
        flag_constant = TYPE_FALSE; 
    }
    pop_quantified_value_stack(psub); 
    
    if (flag_constant) {
      newsub->type = TYPE_CONSTANT; 
      newsub->u.value = sum; 
      newsub = ps_exp_share(newsub); 
    } 
    else {
      free(newsub); 
      newsub = psub; 
    }
    break; 
  }

  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp 
    = rec_static_evaluation(psub->u.arith.lhs_exp);  
    newsub->u.arith.rhs_exp 
    = rec_static_evaluation(psub->u.arith.rhs_exp);  
    if (   newsub->u.arith.lhs_exp->type == TYPE_CONSTANT
        && newsub->u.arith.rhs_exp->type == TYPE_CONSTANT
        ) { 
      if (ineq_calculate(psub->type, 
            newsub->u.arith.lhs_exp->u.value,  
            newsub->u.arith.rhs_exp->u.value
          ) ) {
        free(newsub); 
        return(PS_EXP_TRUE); 
      }
      else { 
        free(newsub); 
        return(PS_EXP_FALSE); 
      } 
    } 
    newsub = ps_exp_share(newsub); 
    break; 

  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith_cond.cond 
    = rec_static_evaluation(psub->u.arith_cond.cond);  
    if (newsub->u.arith_cond.cond == PS_EXP_TRUE) { 
      free(newsub);  
      newsub = rec_static_evaluation(psub->u.arith_cond.if_exp);  
      break; 
    } 
    else if (newsub->u.arith_cond.cond == PS_EXP_FALSE) { 
      free(newsub); 
      newsub = rec_static_evaluation(psub->u.arith_cond.else_exp); 
      break; 
    } 

    newsub->u.arith_cond.if_exp 
    = rec_static_evaluation(psub->u.arith_cond.if_exp);  
    newsub->u.arith_cond.else_exp 
    = rec_static_evaluation(psub->u.arith_cond.else_exp);  
    if (   newsub->u.arith_cond.if_exp->type == TYPE_CONSTANT
        && newsub->u.arith_cond.else_exp->type == TYPE_CONSTANT
        && newsub->u.arith_cond.if_exp->u.value 
           == newsub->u.arith_cond.else_exp->u.value
        ) {
      child = newsub->u.arith_cond.if_exp; 
      free(newsub); 
      newsub = child; 
      break; 
    }
    newsub = ps_exp_share(newsub); 
    break; 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.ineq.offset 
    = rec_static_evaluation(psub->u.ineq.offset); 
    newsub->u.ineq.term = (struct parse_term_type *) 
      malloc(psub->u.ineq.term_count * sizeof(struct parse_term_type)); 
    for (i = 0; i < psub->u.ineq.term_count; i++)  {
      newsub->u.ineq.term[i].coeff 
      = rec_static_evaluation(psub->u.ineq.term[i].coeff); 
      newsub->u.ineq.term[i].operand 
      = rec_static_evaluation(psub->u.ineq.term[i].operand); 
    }
    newsub = ps_exp_share(newsub); 
    break; 
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    fprintf(RED_OUT, "Basically, this should not happen!\n"); 
    fflush(RED_OUT); 
    bk(0); 
    
  case TYPE_INLINE_CALL: 
/*
    fprintf(RED_OUT, "\nmapping arguments for:\n"); 
    pcform(psub);     
*/
    top = (struct actual_argument_frame_type *) 
      malloc(sizeof(struct actual_argument_frame_type)); 
    
    ia_tail = &dummy_ia; 
    for (nl = psub->u.inline_call.inline_declare->u.inline_declare.formal_argument_list, 
         pbu = psub->u.inline_call.actual_argument_list; 
         nl && pbu; 
         nl = nl->next_name_link, pbu = pbu->bnext
         ) { 
      ia = (struct instantiated_argument_type *) 
        malloc(sizeof(struct instantiated_argument_type)); 
      ia->formal_argument_name = nl->name; 
      ia->instantiated_argument 
      = rec_static_evaluation(pbu->subexp); 
/*
      fprintf(RED_OUT, ">> mapping %s to:\n   ", nl->name); 
      pcform(pbu->subexp); 
      fprintf(RED_OUT, "    "); 
      pcform(ia->instantiated_argument); 
*/
      ia_tail->next_instantiated_argument = ia; 
      ia_tail = ia;    
    } 
    ia_tail->next_instantiated_argument = NULL; 
    top->instantiated_argument_list = dummy_ia.next_instantiated_argument; 
         
    top->next_actual_argument_frame = top_inline_stack; 
    top_inline_stack = top; 
    
    newsub = rec_static_evaluation( 
      psub->u.inline_call.inline_declare->u.inline_declare.declare_exp 
    ); 
/*
    fprintf(RED_OUT, "\nInline call %1d to:\n", ++count_inline_call_instance); 
    pcform(psub->u.inline_call.inline_declare->u.inline_declare.declare_exp);
    fprintf(RED_OUT, "with the following actual arguments:\n"); 
*/
    top = top_inline_stack; 
    top_inline_stack = top_inline_stack->next_actual_argument_frame; 
    free(top); 
/*
    fprintf(RED_OUT, "The instantiation yields:\n"); 
    pcform(newsub); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ncount_inline_inst = %1d, leaving ps_exp_inline_intantiate() from inline call.\n", 
      rec_count 
    ); 
    fflush(RED_OUT); 
    #endif 
*/    
    psub->u.inline_call.instantiated_exp = newsub; 
    break; 
    
  case TYPE_INLINE_ARGUMENT: 
    newsub = NULL; 
    if (top_inline_stack == NULL) { 
      fprintf(RED_OUT, "\nError: no inline instantiated arguments:\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    for (ia = top_inline_stack->instantiated_argument_list; 
         ia; 
         ia = ia->next_instantiated_argument
         ) { 
      if (!strcmp(ia->formal_argument_name, psub->u.argument)) 
        break;  
    } 
    if (ia) { 
      newsub = ia->instantiated_argument; 
      break; 
    } 
    else { 
      fprintf(RED_OUT, "Error: undeclared inline argument %x at line %1d:%1d.\n", 
        (unsigned int) psub->u.argument, lineno, psub->lineno
      ); 
      pcform(psub); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    break; 

  case AND :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    dummy_bu.bnext = NULL;  
    newsub->u.bexp.len = 0; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      child = rec_static_evaluation(pbu->subexp); 
      if (child == PS_EXP_FALSE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        newsub = PS_EXP_FALSE; 
        break; 
      } 
      insert_sorted_blist_dummy_head(
        AND, 
        child, 
        &dummy_bu, 
        &(newsub->u.bexp.len)
      ); 
    }
    
    if (newsub != PS_EXP_FALSE) { 
      switch (newsub->u.bexp.len) { 
      case 0: 
        free(newsub); 
        newsub = PS_EXP_TRUE; 
        break; 

      case 1: 
        child = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        free(newsub); 
        newsub = child; 
        break; 

      default: 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        newsub = ps_exp_share(newsub); 
    } }
    break;

  case OR :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    dummy_bu.bnext = NULL;  
    newsub->u.bexp.len = 0; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      child = rec_static_evaluation(pbu->subexp); 
      if (child == PS_EXP_TRUE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        newsub = PS_EXP_TRUE; 
        break; 
      } 
      insert_sorted_blist_dummy_head(
        OR, 
        child, 
        &dummy_bu, 
        &(newsub->u.bexp.len)
      ); 
    }
    
    if (newsub != PS_EXP_TRUE) { 
      switch (newsub->u.bexp.len) { 
      case 0: 
        free(newsub); 
        newsub = PS_EXP_FALSE; 
        break; 

      case 1: 
        child = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        free(newsub); 
        newsub = child; 
        break; 

      default: 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        newsub = ps_exp_share(newsub); 
    } }
    break;

  case NOT :
    newsub = rec_static_evaluation(psub->u.bexp.blist->subexp); 
    if (newsub == PS_EXP_FALSE) { 
      newsub = PS_EXP_TRUE; 
      break; 
    } 
    else if (newsub == PS_EXP_TRUE) { 
      newsub = PS_EXP_FALSE; 
      break; 
    } 
    else { 
      newsub = ps_exp_share(newsub); 
      newsub = add_neg(newsub); 
    } 
    break; 

  case IMPLY : 
    child = rec_static_evaluation(psub->u.bexp.blist->subexp); 
    if (child == PS_EXP_FALSE) {
      newsub = PS_EXP_TRUE; 
      break; 
    } 
    else if (child == PS_EXP_TRUE) { 
      newsub = rec_static_evaluation(psub->u.bexp.blist->bnext->subexp); 
      break; 
    } 
    child2 = rec_static_evaluation(psub->u.bexp.blist->bnext->subexp);
    if (child2 == PS_EXP_TRUE || child == child2) {
      newsub = PS_EXP_TRUE; 
      break; 
    }
    else if (child2 == PS_EXP_FALSE) {
      newsub = add_neg(child); 
      break; 
    } 

    newsub = ps_exp_alloc(OR); 
    *newsub = *psub; 
    newsub->type = OR; 
    dummy_bu.bnext = NULL;  
    newsub->u.bexp.len = 0; 
    insert_sorted_blist_dummy_head(
      OR, 
      add_neg(child), 
      &dummy_bu, 
      &(newsub->u.bexp.len)
    ); 
    insert_sorted_blist_dummy_head( 
      OR, 
      child2, 
      &dummy_bu, 
      &(newsub->u.bexp.len)
    ); 
    newsub->u.bexp.blist = dummy_bu.bnext; 
    newsub = ps_exp_share(newsub); 
    break; 

  case FORALL: {
    float	flb, fub; 
    int		flag; 
    
    flag = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      newsub = PS_EXP_TRUE; 
      break; 
    } 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    dummy_bu.bnext = NULL;  
    newsub->u.bexp.len = 0; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      child = rec_static_evaluation(psub->u.qexp.child); 
      if (child == PS_EXP_FALSE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        newsub = PS_EXP_FALSE; 
        break; 
      } 
      insert_sorted_blist_dummy_head(
        AND, 
        child, 
        &dummy_bu, 
        &(newsub->u.bexp.len)
      ); 
    }
    pop_quantified_value_stack(psub); 
    
    if (newsub != PS_EXP_FALSE) {
      switch (newsub->u.bexp.len) { 
      case 0: 
        newsub = PS_EXP_TRUE; 
        break; 
      case 1: 
        child = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        free(newsub); 
        newsub = child; 
        break; 
      default: 
        newsub->type = AND; 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        newsub = ps_exp_share(newsub); 
        break; 
    } }
    break;
  }
  case EXISTS: {
    float	flb, fub; 
    int		flag; 
    
    flag = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      newsub = PS_EXP_FALSE; 
      break; 
    } 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    dummy_bu.bnext = NULL;  
    newsub->u.bexp.len = 0; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      child = rec_static_evaluation(psub->u.qexp.child); 
      if (child == PS_EXP_TRUE) {
        free_ps_exp_list(dummy_bu.bnext); 
        free(newsub); 
        newsub = PS_EXP_TRUE; 
        break; 
      } 
      insert_sorted_blist_dummy_head( 
        OR, 
        child, 
        &dummy_bu, 
        &(newsub->u.bexp.len)
      ); 
    }
    pop_quantified_value_stack(psub); 
    
    if (newsub != PS_EXP_TRUE) {
      switch (newsub->u.bexp.len) { 
      case 0: 
        newsub = PS_EXP_FALSE; 
        break; 
      case 1: 
        child = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        free(newsub); 
        newsub = child; 
        break; 
      default: 
        newsub->type = OR; 
        newsub->u.bexp.blist = dummy_bu.bnext; 
        newsub = ps_exp_share(newsub); 
        break; 
      }
    }
    break;
  }
  case RESET:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = rec_static_evaluation(psub->u.reset.child); 
    newsub = ps_exp_share(newsub); 
    break; 

  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY: 
  case EXISTS_ALWAYS:
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE:
  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST:

  case TYPE_GAME_SIM: 

    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 

    newsub->u.mexp.strong_fairness_list 
    = rec_static_seq_evaluation(
      psub->u.mexp.strong_fairness_list, 
      &(newsub->u.mexp.strong_fairness_count) 
    ); 
    newsub->u.mexp.weak_fairness_list 
    = rec_static_seq_evaluation(
      psub->u.mexp.weak_fairness_list, 
      &(newsub->u.mexp.weak_fairness_count)
    ); 
    newsub->u.mexp.path_child 
    = rec_static_evaluation(psub->u.mexp.path_child);
      
    newsub->u.mexp.event_restriction = rec_static_evaluation(psub->u.mexp.event_restriction);
    newsub->u.mexp.dest_child 
    = rec_static_evaluation(psub->u.mexp.dest_child);
    newsub->u.mexp.time_restriction 
    = rec_static_evaluation(psub->u.mexp.time_restriction);

    newsub = ps_exp_share(newsub); 
    break; 

  case LINEAR_EVENT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    if (psub->u.eexp.event_exp)
      newsub->u.eexp.event_exp 
      = rec_static_evaluation(psub->u.eexp.event_exp);
    newsub->u.eexp.precond_exp 
    = rec_static_evaluation(psub->u.eexp.precond_exp);
    newsub->u.eexp.postcond_exp 
    = rec_static_evaluation(psub->u.eexp.postcond_exp);

    newsub = ps_exp_share(newsub); 
    break; 

  case TYPE_MULTIPLE_FAIRNESS: 
    fprintf(RED_OUT, 
    "\nERROR: Multiple fairness assumptions should have already been replaced at line %1d.\n", 
      lineno
    ); 
    pcform(psub); 
    bk(0); 
    break; 

  case RED:
    newsub = psub; 
    break; 
    
  default: 
    fprintf(RED_OUT, 
      "\nError: unexpected expression type %1d in rec_static_evaluation().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
  return(newsub); 
}
  /* rec_static_evaluation() */ 



struct ps_exp_type	*exp_static_evaluation(
  struct ps_exp_type		*psub, 
  int				pi, 
  struct sync_xtion_type	*psx
) { 
  PI_STATIC_EVAL = pi; 
  PSX_STATIC_EVAL = psx; 
  return(rec_static_evaluation(psub)); 
}
  /* exp_static_evaluation() */ 






struct ps_exp_type	*LHS_PCO; 
int			VALUE_PROC_INDEX_LHS_PCO, 
			FLAG_PROC_INDEX_LHS_PCO; 

int	rec_check_lhs_pco(
  struct ps_exp_type	*psub 
) {
  int			i, pi, lpi, rpi, llb, lub, ulb, uub;
  struct ps_bunit_type	*pbu; 

  #ifdef RED_DEBUG_YACC_MODE
//  if (count_check_lhs_pco == 132) { 
    fprintf(RED_OUT, 
      "\nstatic evaluation = %1d, entering rec_check_lhs_pco().\n", 
      count_check_lhs_pco
    ); 
    fflush(RED_OUT); 
    pcform(psub); 
    fflush(RED_OUT); 
//  }
  #endif 
  
  if (!psub) 
    return(TYPE_FALSE); 

  switch(psub->type) {
  case TYPE_NULL:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_COUNT: 
  case TYPE_XTION_COUNT: 
  case TYPE_FALSE :
  case TYPE_TRUE :
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QSYNC_HOLDER: 
  case TYPE_PEER_IDENTIFIER:
  case TYPE_TRASH:
  case TYPE_QFD: 
  case TYPE_MODE_INDEX: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_INLINE_ARGUMENT: 
    return(TYPE_FALSE); 

  case TYPE_REFERENCE:
  case TYPE_DEREFERENCE:
    return(TYPE_TRUE); 
    break; 

  case TYPE_POINTER: 
  case TYPE_SYNCHRONIZER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT:
  case TYPE_DOUBLE:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_BDD: 
    if (   LHS_PCO->type != psub->type
        || (LHS_PCO->var_status & FLAG_LOCAL_VARIABLE) 
           != (psub->var_status & FLAG_LOCAL_VARIABLE) 
        || (LHS_PCO->u.atom.var->index != psub->u.atom.var->index) 
        ) 
      return(TYPE_FALSE); 
    if (   (  LHS_PCO->u.atom.exp_base_proc_index->var_status 
            & FLAG_EXP_STATE_INSIDE
            )
        || (  psub->u.atom.exp_base_proc_index->var_status 
            & FLAG_EXP_STATE_INSIDE
        )   )
      return(TYPE_TRUE); 
    
    if (FLAG_PROC_INDEX_LHS_PCO == FLAG_SPECIFIC_VALUE) { 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        rpi = get_value(psub->u.atom.exp_base_proc_index, pi, &i); 
        if (   i != FLAG_SPECIFIC_VALUE
            || rpi == VALUE_PROC_INDEX_LHS_PCO
            ) 
          return(TYPE_TRUE);  
      } 
      return(TYPE_FALSE); 
    } 
    else { 
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        lpi = get_value(LHS_PCO->u.atom.exp_base_proc_index, pi, &i); 
        if (i != FLAG_SPECIFIC_VALUE) 
          return(TYPE_TRUE); 
        rpi = get_value(psub->u.atom.exp_base_proc_index, pi, &i); 
        if (   i != FLAG_SPECIFIC_VALUE
            || rpi == lpi
            ) 
          return(TYPE_TRUE);  
      } 
      return(TYPE_FALSE); 
    } 
    break; 

  case TYPE_INTERVAL:
    if (   rec_check_lhs_pco(psub->u.interval.lbound_exp)
        || rec_check_lhs_pco(psub->u.interval.rbound_exp)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 
    
  case BIT_NOT: 
    return(rec_check_lhs_pco(psub->u.exp));  
    break; 
  

  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO:
  case ARITH_MAX:
  case ARITH_MIN:

  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    if (   rec_check_lhs_pco(psub->u.arith.lhs_exp)
        || rec_check_lhs_pco(psub->u.arith.rhs_exp)
        )
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE);   
    break; 

  case ARITH_CONDITIONAL: 
    if (   rec_check_lhs_pco(psub->u.arith_cond.cond)  
        || rec_check_lhs_pco(psub->u.arith_cond.if_exp)
        || rec_check_lhs_pco(psub->u.arith_cond.else_exp)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE);   
    break; 
    
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    if (rec_check_lhs_pco(psub->u.ineq.offset)) 
      return(TYPE_TRUE);  
    for (i = 0; i < psub->u.ineq.term_count; i++)  {
      if (   rec_check_lhs_pco(psub->u.ineq.term[i].operand)
          || rec_check_lhs_pco(psub->u.ineq.term[i].coeff) 
          ) 
        return(TYPE_TRUE);  
    }
    return(TYPE_FALSE); 
    break; 
    
  case TYPE_INLINE_BOOLEAN_DECLARE: 
  case TYPE_INLINE_DISCRETE_DECLARE: 
    fprintf(RED_OUT, "Basically, this should not happen!\n"); 
    fflush(RED_OUT); 
    bk(0); 
    
  case TYPE_INLINE_CALL: 
    for (pbu = psub->u.inline_call.actual_argument_list; 
         pbu; 
         pbu = pbu->bnext
         ) { 
      if (rec_check_lhs_pco(pbu->subexp)) 
        return(TYPE_TRUE);  
    } 
    if (rec_check_lhs_pco( 
          psub->u.inline_call.inline_declare->u.inline_declare.declare_exp 
        ) ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break; 

  case AND :
  case OR :
  case NOT :
  case IMPLY : 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      if (rec_check_lhs_pco(pbu->subexp)) 
        return(TYPE_TRUE); 
    } 
    return(TYPE_FALSE);  
 
  case ARITH_SUM:
  case FORALL:
  case EXISTS: {
    float	flb, fub; 
    int		flag; 
    
    flag = rec_get_integer_range(
      psub->u.qexp.lb_exp, &llb, &lub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    flag = rec_get_integer_range(
      psub->u.qexp.ub_exp, &ulb, &uub, &flb, &fub
    ); 
    if (flag != FLAG_SPECIFIC_VALUE) {
      fprintf(RED_OUT, "\nERROR, Illegal variable range type.\n"); 
      bk(0); 
    } 
    if (llb > uub) { 
      return(TYPE_FALSE); 
    } 
    if (llb > ulb) 
      llb = ulb; 
    if (uub < lub) 
      uub = lub; 
    push_quantified_value_stack(psub); 
    for (psub->u.qexp.value = llb; 
         psub->u.qexp.value <= uub; 
         psub->u.qexp.value++
         ) { 
      if (rec_check_lhs_pco(psub->u.qexp.child))
        break; 
    }
    pop_quantified_value_stack(psub); 
    if (psub->u.qexp.value <= uub)
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
    break;
  }
  case RESET:
    if (   psub->u.reset.var == LHS_PCO->u.atom.var 
        || rec_check_lhs_pco(psub->u.reset.child)
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE);  
    break; 

  case FORALL_ALWAYS: 
  case FORALL_EVENTUALLY: 
  case EXISTS_ALWAYS:
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE:
  case EXISTS_UNTIL: 
  case FORALL_UNTIL: 
  case EXISTS_OFTEN: 
  case EXISTS_ALMOST: 
  case FORALL_OFTEN: 
  case FORALL_ALMOST:

  case TYPE_GAME_SIM: 

  case EXISTS_EVENT: 
  case FORALL_EVENT: 
  case LINEAR_EVENT: 
    return(TYPE_TRUE); 
    break; 

  case TYPE_MULTIPLE_FAIRNESS: 
    fprintf(RED_OUT, 
    "\nERROR: Multiple fairness assumptions should have already been replaced at line %1d.\n", 
      lineno
    ); 
    pcform(psub); 
    bk(0); 
    break; 

  case RED:
    if (FLAG_PROC_INDEX_LHS_PCO == FLAG_SPECIFIC_VALUE) 
      if (check_vi_in_red_possibly(psub->u.rpred.red, 
            variable_index[LHS_PCO->type]
            [VALUE_PROC_INDEX_LHS_PCO]
            [LHS_PCO->u.atom.var->index]
          ) ) 
        return(TYPE_TRUE); 
      else 
        return(TYPE_FALSE); 
    else 
      if (check_vi_sim_in_red(psub->u.rpred.red, 
            LHS_PCO->type, LHS_PCO->u.atom.var->index 
          ) ) 
        return(TYPE_TRUE); 
      else 
        return(TYPE_FALSE);  
    break; 
    
  default: 
    fprintf(RED_OUT, 
      "\nError: unexpected expression type %1d in rec_check_lhs_pco().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
}
  /* rec_check_lhs_pco() */ 




/**************************************************************** 
 *  The following procedure, I think, checks the possible 
 *  coincidence of lhs and some rhs variables. 
 *  If this is possible, then we say there could be an LHS recursion. 
 */
int	check_lhs_pco(
  struct ps_exp_type	*px, 
  struct ps_exp_type	*py
) { 
  int	pi, value; 
  
  if (px->type == TYPE_REFERENCE || px->type == TYPE_DEREFERENCE)
    return (TYPE_TRUE); 
  LHS_PCO = px; 
  VALUE_PROC_INDEX_LHS_PCO = get_value(px->u.atom.exp_base_proc_index, 
    1, &FLAG_PROC_INDEX_LHS_PCO
  ); 
  if (FLAG_PROC_INDEX_LHS_PCO == FLAG_SPECIFIC_VALUE) { 
    for (pi = 2; pi <= PROCESS_COUNT; pi++) {
      value = get_value(px->u.atom.exp_base_proc_index, 
        pi, &FLAG_PROC_INDEX_LHS_PCO
      );
      if (FLAG_PROC_INDEX_LHS_PCO != FLAG_SPECIFIC_VALUE)
        break; 
      else if (value != VALUE_PROC_INDEX_LHS_PCO) { 
        FLAG_PROC_INDEX_LHS_PCO = FLAG_ANY_VALUE; 
        break; 
      } 
    } 
  } 
  return(rec_check_lhs_pco(py)); 
}
  /* check_lhs_pco() */ 



struct exp_shape_type { 
  int	type, 
	count_clocks, 
	count_denses, 
	count_discretes, 
	count_synchronizers, 
	flag_clock_polarity; /* only used with types 
	                      * FLAG_EXP_CLOCK_CONSTANT and 
	                      * FLAG_EXP_CLOCK_MIXED. */
#define	MASK_EXP_CLOCK_POLARITY	3
#define	FLAG_EXP_NO_CLOCK	0 
#define	FLAG_EXP_POS_CLOCK	1 
#define	FLAG_EXP_NEG_CLOCK	2
}; 


struct exp_shape_type	*exp_shape_alloc() { 
  struct exp_shape_type	*es; 
  
  es = (struct exp_shape_type *) malloc(sizeof(struct exp_shape_type)); 
  es->type = 0;  
  es->count_clocks = 0;  
  es->count_denses = 0;  
  es->count_discretes = 0;  
  es->count_synchronizers = 0; 
  es->flag_clock_polarity = 0; 
  
  return(es); 
}
  /* exp_shape_alloc() */



int	merge_exp_shape_bitwise(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  es->count_clocks = les->count_clocks + res->count_clocks;  
  es->count_denses = les->count_denses + res->count_denses;  
  es->count_discretes = les->count_discretes + res->count_discretes;  
  es->count_synchronizers = les->count_synchronizers + res->count_synchronizers; 

  switch (es->type & MASK_EXP_TYPE) { 
  case FLAG_EXP_STATIC: 
    break; 
  case FLAG_EXP_DISCRETE_LINEAR: 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
  case FLAG_EXP_DENSE_MIXED: 
  case FLAG_EXP_DENSE_POLYNOMIAL: 
  case FLAG_EXP_DISCRETE_CONSTANT: 
    es->type = FLAG_EXP_DISCRETE_POLYNOMIAL; 
    break; 
  case FLAG_EXP_CLOCK_DIFFERENCE: 
  case FLAG_EXP_CLOCK_MIXED: 
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
  case FLAG_EXP_DENSE_CONSTANT: 
  case FLAG_EXP_DENSE_LINEAR: 
    fprintf(RED_OUT, 
      "\nSyntax error: illegal bitwise operation on dense variables at line %1d.\n", 
      lineno
    ); 
    bk(0); 
    break; 
  } 

  return(es->type); 
}
  /* merge_exp_shape_bitwise() */ 




int	merge_exp_shape_subtraction(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  es->count_clocks = les->count_clocks + res->count_clocks;  
  es->count_denses = les->count_denses + res->count_denses;  
  es->count_discretes = les->count_discretes + res->count_discretes;  
  es->count_synchronizers = les->count_synchronizers + res->count_synchronizers; 

  switch (es->type & MASK_EXP_TYPE) { 
  case FLAG_EXP_STATIC: 
  case FLAG_EXP_DISCRETE_LINEAR: 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
  case FLAG_EXP_DENSE_MIXED: 
  case FLAG_EXP_DENSE_POLYNOMIAL: 
    break; 
  case FLAG_EXP_DISCRETE_CONSTANT: 
    if (es->count_discretes > 1) 
      es->type = FLAG_EXP_DISCRETE_LINEAR; 
    break; 
  case FLAG_EXP_CLOCK_CONSTANT: 
    switch (es->count_clocks) { 
    case 1: 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_CLOCK_MIXED; 

      if (   (les->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
          ) { 
        es->flag_clock_polarity = FLAG_EXP_POS_CLOCK; 
      } 
      else if (   (les->flag_clock_polarity & FLAG_EXP_NEG_CLOCK) 
               || (res->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
               ) 
        es->flag_clock_polarity = FLAG_EXP_NEG_CLOCK; 
      else { 
        fprintf(RED_OUT, "\nError: Shouldn't be here.\n"); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      break; 
    case 2: 
      if (   (les->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
          ) 
        es->flag_clock_polarity = es->flag_clock_polarity | FLAG_EXP_POS_CLOCK; 
      if (   (les->flag_clock_polarity & FLAG_EXP_NEG_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_POS_CLOCK)
          ) 
        es->flag_clock_polarity = es->flag_clock_polarity | FLAG_EXP_NEG_CLOCK; 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) { 
        if (   (es->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
            && (es->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
            ) { 
          es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
        }
        else { 
          es->type = FLAG_EXP_DENSE_MIXED; 
        } 
      } 
      else 
        if (   (es->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
            && (es->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
            ) { 
          es->type = FLAG_EXP_CLOCK_DIFFERENCE; 
        } 
        else {
          es->type = FLAG_EXP_DENSE_LINEAR; 
        } 
      break; 
    default: // > 2 OR == 0 
      fprintf(RED_OUT, "\nThere is something wrong.\n"); 
      fflush(RED_OUT); 
      bk(0);  
    } 
    break; 
  case FLAG_EXP_CLOCK_DIFFERENCE: 
    if (es->count_clocks > 2) { 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_DENSE_MIXED; 
      else 
        es->type = FLAG_EXP_DENSE_LINEAR; 
    } 
    else /* clock difference for DBM */ { 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
    } 
    break; 
  case FLAG_EXP_CLOCK_MIXED: 
    if (es->count_clocks > 2) { 
      es->type = FLAG_EXP_DENSE_MIXED; 
    } 
    else if ((les->flag_clock_polarity & MASK_EXP_CLOCK_POLARITY) 
             == (res->flag_clock_polarity & MASK_EXP_CLOCK_POLARITY) 
             ) { 
    /* This means that both clocks have the same polarity. */ 
      es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
      es->flag_clock_polarity = FLAG_EXP_POS_CLOCK | FLAG_EXP_NEG_CLOCK;     
    } 
    else { 
    /* This means that both clocks have different polarities. */ 
      es->type = FLAG_EXP_DENSE_MIXED; 
      es->flag_clock_polarity = les->flag_clock_polarity; 
    } 
    break; 
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    if (les->type == es->type) 
      mes = res; 
    else 
      mes = les; 
    switch (es->type & MASK_EXP_TYPE) { 
    case FLAG_EXP_STATIC: 
    case FLAG_EXP_DISCRETE_CONSTANT: 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL: 
      break; 
    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
      es->type = FLAG_EXP_DENSE_MIXED; 
      break; 
    } 
    break; 
  case FLAG_EXP_DENSE_CONSTANT: 
  case FLAG_EXP_DENSE_LINEAR: 
    if (es->count_discretes > 0 || es->count_synchronizers > 0) 
      es->type = FLAG_EXP_DENSE_MIXED; 
    break; 
  } 

  return(es->type); 
}
  /* merge_exp_shape_subtraction() */ 




int	merge_exp_shape_addition(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  es->count_clocks = les->count_clocks + res->count_clocks;  
  es->count_denses = les->count_denses + res->count_denses;  
  es->count_discretes = les->count_discretes + res->count_discretes;  
  es->count_synchronizers = les->count_synchronizers + res->count_synchronizers; 

  switch (es->type & MASK_EXP_TYPE) { 
  case FLAG_EXP_STATIC: 
  case FLAG_EXP_DISCRETE_LINEAR: 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
  case FLAG_EXP_DENSE_MIXED: 
  case FLAG_EXP_DENSE_POLYNOMIAL: 
    break; 
  case FLAG_EXP_DISCRETE_CONSTANT: 
    if (es->count_discretes > 1) 
      es->type = FLAG_EXP_DISCRETE_LINEAR; 
    break;
  case FLAG_EXP_CLOCK_CONSTANT: 
    switch (es->count_clocks) { 
    case 1: 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_CLOCK_MIXED; 

      if (   (les->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_POS_CLOCK)
          ) { 
        es->flag_clock_polarity = FLAG_EXP_POS_CLOCK; 
      } 
      else if (   (les->flag_clock_polarity & FLAG_EXP_NEG_CLOCK) 
               || (res->flag_clock_polarity & FLAG_EXP_NEG_CLOCK) 
               ) 
        es->flag_clock_polarity = FLAG_EXP_NEG_CLOCK; 
      else { 
        fprintf(RED_OUT, "\nError: Shouldn't be here.\n"); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      break; 
    case 2: 
      if (   (les->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_POS_CLOCK)
          ) 
        es->flag_clock_polarity = es->flag_clock_polarity | FLAG_EXP_POS_CLOCK; 
      if (   (les->flag_clock_polarity & FLAG_EXP_NEG_CLOCK) 
          || (res->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
          ) 
        es->flag_clock_polarity = es->flag_clock_polarity | FLAG_EXP_NEG_CLOCK; 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) { 
        if (   (es->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
            && (es->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
            ) { 
          es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
        }
        else {
          es->type = FLAG_EXP_DENSE_MIXED; 
        } 
      } 
      else 
        if (   (es->flag_clock_polarity & FLAG_EXP_POS_CLOCK) 
            && (es->flag_clock_polarity & FLAG_EXP_NEG_CLOCK)
            ) { 
          es->type = FLAG_EXP_CLOCK_DIFFERENCE; 
        } 
        else {
          es->type = FLAG_EXP_DENSE_LINEAR; 
        } 
      break; 
    default: // > 2 OR == 0
      fprintf(RED_OUT, "\nThere is something wrong.\n"); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    break; 
  case FLAG_EXP_CLOCK_DIFFERENCE: 
    if (es->count_clocks > 2) { 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_DENSE_MIXED; 
      else 
        es->type = FLAG_EXP_DENSE_LINEAR; 
    } 
    else /* clock difference for DBM */ { 
      if (es->count_discretes > 0 || es->count_synchronizers > 0) 
        es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
    } 
    break; 
  case FLAG_EXP_CLOCK_MIXED: 
    if (es->count_clocks > 2) { 
      es->type = FLAG_EXP_DENSE_MIXED; 
    } 
    else if ((les->flag_clock_polarity & MASK_EXP_CLOCK_POLARITY) 
             == (res->flag_clock_polarity & MASK_EXP_CLOCK_POLARITY) 
             ) { 
    /* This means that both clocks have the same polarity. */ 
      es->type = FLAG_EXP_DENSE_MIXED; 
      es->flag_clock_polarity = les->flag_clock_polarity; 
    } 
    else { 
    /* This means that both clocks have different polarities. */ 
      es->type = FLAG_EXP_CLOCK_DIFFERENCE_MIXED; 
      es->flag_clock_polarity = FLAG_EXP_POS_CLOCK | FLAG_EXP_NEG_CLOCK;     
    } 
    break; 
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    if (les->type == es->type) 
      mes = res; 
    else 
      mes = les; 
    switch (es->type & MASK_EXP_TYPE) { 
    case FLAG_EXP_STATIC: 
    case FLAG_EXP_DISCRETE_CONSTANT: 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL: 
      break; 
    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
      es->type = FLAG_EXP_DENSE_MIXED; 
      break; 
    } 
    break; 
  case FLAG_EXP_DENSE_CONSTANT: 
  case FLAG_EXP_DENSE_LINEAR: 
    if (es->count_discretes > 0 || es->count_synchronizers > 0) 
      es->type = FLAG_EXP_DENSE_MIXED; 
    break; 
  } 

  return(es->type); 
}
  /* merge_exp_shape_addition() */ 




int	merge_exp_shape_multiply(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  es->count_clocks = les->count_clocks + res->count_clocks;  
  es->count_denses = les->count_denses + res->count_denses;  
  es->count_discretes = les->count_discretes + res->count_discretes;  
  es->count_synchronizers = les->count_synchronizers + res->count_synchronizers; 

  switch (es->type & MASK_EXP_TYPE) { 
  case FLAG_EXP_STATIC: 
    break; 
  case FLAG_EXP_DISCRETE_CONSTANT: 
  case FLAG_EXP_DISCRETE_LINEAR: 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
    if (   les->type != FLAG_EXP_STATIC
        || res->type != FLAG_EXP_STATIC
        ) 
      es->type = FLAG_EXP_DISCRETE_POLYNOMIAL; 
    break; 
  case FLAG_EXP_CLOCK_CONSTANT: 
  case FLAG_EXP_CLOCK_DIFFERENCE: 
  case FLAG_EXP_CLOCK_MIXED: 
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
  case FLAG_EXP_DENSE_CONSTANT: 
  case FLAG_EXP_DENSE_LINEAR: 
  case FLAG_EXP_DENSE_MIXED: 
  case FLAG_EXP_DENSE_POLYNOMIAL: 
    es->type = FLAG_EXP_DENSE_POLYNOMIAL; 
    break; 
  } 

  return(es->type); 
}
  /* merge_exp_shape_multiply() */ 



int	merge_exp_shape_divide(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  es->count_clocks = les->count_clocks + res->count_clocks;  
  es->count_denses = les->count_denses + res->count_denses;  
  es->count_discretes = les->count_discretes + res->count_discretes;  
  es->count_synchronizers = les->count_synchronizers + res->count_synchronizers; 

  switch (es->type & MASK_EXP_TYPE) { 
  case FLAG_EXP_STATIC: 
    break; 
  case FLAG_EXP_DISCRETE_CONSTANT: 
  case FLAG_EXP_DISCRETE_LINEAR: 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
    es->type = FLAG_EXP_DISCRETE_POLYNOMIAL; 
    break; 
  case FLAG_EXP_CLOCK_CONSTANT: 
  case FLAG_EXP_CLOCK_DIFFERENCE: 
  case FLAG_EXP_CLOCK_MIXED: 
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
  case FLAG_EXP_DENSE_CONSTANT: 
  case FLAG_EXP_DENSE_LINEAR: 
  case FLAG_EXP_DENSE_MIXED: 
  case FLAG_EXP_DENSE_POLYNOMIAL: 
    es->type = FLAG_EXP_DENSE_POLYNOMIAL; 
    break; 
  } 

  return(es->type); 
}
  /* merge_exp_shape_divide() */ 



  
int	merge_exp_shape_conditional(es, les, res) 
  struct exp_shape_type	*es, *les, *res; 
{ 
  struct exp_shape_type	*mes; 
  
  es->type = int_max(les->type, res->type); 
    
  if (les->count_clocks > res->count_clocks) 
    es->count_clocks = les->count_clocks;  
  else 
    es->count_clocks = res->count_clocks;  
  if (les->count_denses > res->count_denses)  
    es->count_denses = les->count_denses;  
  else 
    es->count_denses = res->count_denses;  
  if (les->count_discretes > res->count_discretes)   
    es->count_discretes = les->count_discretes;  
  else 
    es->count_discretes = res->count_discretes;  
  if (les->count_synchronizers > res->count_synchronizers)  
    es->count_synchronizers = les->count_synchronizers; 
  else 
    es->count_synchronizers = res->count_synchronizers; 

  return(es->type); 
}
  /* merge_exp_shape_conditional() */ 




// Note that the field of FLAG_CONSTANT has already been set 
// by rec_static_evaluation().  
// Thus we keep it unchanged.  
int	count_exp_shape_check = 0; 

struct exp_shape_type	*exp_shape_check(psub)
  struct ps_exp_type	*psub;
{
  struct exp_shape_type	*es, *les, *res; 
  int			flag, v; 
    
 /*
  fprintf(RED_OUT, 
    "exp_shape_check=%1d, Entering exp_shape_check() for type %1d\n", 
    ++count_exp_shape_check, psub->type 
  ); 
//
  pcform(psub); 
 */
  es = exp_shape_alloc(); 
  switch(psub->type) {
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_QFD:
  case TYPE_QSYNC_HOLDER: 
    es->type = FLAG_EXP_STATIC; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 

  case TYPE_MODE_INDEX: 
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_NULL:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MACRO_CONSTANT: 
    es->type = FLAG_EXP_STATIC; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
/*
    fprintf(RED_OUT, "Leaving exp_shape_check() for constant\n"); 
    pcform(psub); 
*/
    return(es); 
    
  case TYPE_REFERENCE:
  case TYPE_DEREFERENCE:
    free(es); 
    es = exp_shape_check(psub->u.exp);
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (psub->u.exp->exp_status & ~FLAG_CONSTANT)  
    | FLAG_INDIRECTION; 
    es->type = FLAG_EXP_DISCRETE_POLYNOMIAL; 
/*
    pcform(psub); 
*/
/*
    fprintf(RED_OUT, "exp shape -: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    return(es); 
    
  case TYPE_CLOCK: 
    psub->var_status = psub->var_status | FLAG_CLOCK; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE)
        || (psub->exp_status & FLAG_INDIRECTION)
        ) { 
      es->type = FLAG_EXP_CLOCK_MIXED; 
    }
    else { 
      es->type = FLAG_EXP_CLOCK_CONSTANT; 
    }
    es->count_clocks = 1; 
    es->flag_clock_polarity = FLAG_EXP_POS_CLOCK; 
/*
    fprintf(RED_OUT, "Leaving polynomial checking for clock\n"); 
    pcform(psub); 
*/
    return(es); 

  case TYPE_DENSE: 
    psub->var_status = psub->var_status | FLAG_DENSE; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE)
        || (psub->exp_status & FLAG_INDIRECTION)
        ) { 
      es->type = FLAG_EXP_DENSE_LINEAR; 
    }
    else { 
      es->type = FLAG_EXP_DENSE_CONSTANT; 
    }
    es->count_denses = 1; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 
    
  case TYPE_DISCRETE:
    psub->var_status = psub->var_status | FLAG_DISCRETE; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE) 
        || (psub->exp_status & FLAG_INDIRECTION)
        ) {
      es->type = FLAG_EXP_DISCRETE_POLYNOMIAL;
    }
    else { 
      es->type = FLAG_EXP_DISCRETE_CONSTANT; 
    }
    es->count_discretes = 1; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 
    
  case TYPE_POINTER: 
    if (   (psub->u.atom.var->status & FLAG_QUANTIFIED_SYNC)
        && (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)
        ) { 
      es->type = FLAG_EXP_STATIC; 
      psub->var_status = (psub->var_status & ~FLAG_POINTER); 
      es->count_discretes = 0; 
      es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
      return(es); 
    } 
    psub->var_status = psub->var_status | FLAG_POINTER; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE)
        || (psub->exp_status & FLAG_INDIRECTION)
        ) { 
      es->type = FLAG_EXP_DISCRETE_POLYNOMIAL;
    }
    else { 
      es->type = FLAG_EXP_DISCRETE_CONSTANT; 
    }
    es->count_discretes = 1; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 
    
  case TYPE_FLOAT:
    psub->var_status = psub->var_status | FLAG_FLOAT; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE) 
        || (psub->exp_status & FLAG_INDIRECTION)
        ) {
      es->type = FLAG_EXP_DISCRETE_POLYNOMIAL;
    }
    else { 
      es->type = FLAG_EXP_DISCRETE_CONSTANT; 
    }
    es->count_discretes = 1; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 
    
  case TYPE_DOUBLE:
    psub->var_status = psub->var_status | FLAG_DOUBLE; 
    if (   (psub->u.atom.exp_base_proc_index->var_status & FLAG_EXP_STATE_INSIDE) 
        || (psub->exp_status & FLAG_INDIRECTION)
        ) {
      es->type = FLAG_EXP_DISCRETE_POLYNOMIAL;
    }
    else { 
      es->type = FLAG_EXP_DISCRETE_CONSTANT; 
    }
    es->count_discretes = 1; 
    es->flag_clock_polarity = FLAG_EXP_NO_CLOCK; 
    return(es); 
    
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, "ERROR: a synchronizer variable %s in an arithmetic expression at line %1d.\n", 
	    psub->u.atom.var->name, psub->lineno
	    ); 
    exit(0); 
    break; 
    
  case TYPE_BDD: 
    fprintf(RED_OUT, 
      "ERROR: in exp_shape_check(), \n" 
    ); 
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n", 
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 

  case BIT_NOT: 
    es = exp_shape_check(psub->u.exp);
    res = exp_shape_check(psub->u.arith.rhs_exp); 
    es->count_clocks = res->count_clocks;  
    es->count_denses = res->count_denses;  
    es->count_discretes = res->count_discretes;  
    es->count_synchronizers = res->count_synchronizers; 

    psub->var_status = psub->var_status | psub->u.exp->var_status; 
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (psub->u.exp->exp_status & ~FLAG_CONSTANT); 
/*
    pcform(psub); 
*/
    free(res); 
    es->type = FLAG_EXP_DISCRETE_POLYNOMIAL; 
    return(es); 
    break; 
    
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    les = exp_shape_check(psub->u.arith.lhs_exp);
    res = exp_shape_check(psub->u.arith.rhs_exp); 
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status
          ) 
       & ~FLAG_CONSTANT
       ); 
/*
    pcform(psub); 
*/
    psub->u.arith.status 
    = (psub->u.arith.status & ~MASK_EXP_TYPE)
    | merge_exp_shape_bitwise(es, les, res); 
/*
    fprintf(RED_OUT, "exp shape +: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    free(res); 
    return(es); 

  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_GEQ:
  case ARITH_LESS:
  case ARITH_GREATER: 

  case ARITH_MINUS:
    les = exp_shape_check(psub->u.arith.lhs_exp);
    res = exp_shape_check(psub->u.arith.rhs_exp); 
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status
          ) 
       & ~FLAG_CONSTANT
       ); 
/*
    pcform(psub); 
*/
    psub->u.arith.status 
    = (psub->u.arith.status & ~MASK_EXP_TYPE)
    | merge_exp_shape_subtraction(es, les, res); 
/*
    fprintf(RED_OUT, "exp shape -: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    free(res); 
/*
    fprintf(RED_OUT, "\nexp shape check with s%x: ", 
      psub->status
    ); 
    pcform(psub); 
*/
    return(es); 
    
  case ARITH_ADD:
    les = exp_shape_check(psub->u.arith.lhs_exp);
    res = exp_shape_check(psub->u.arith.rhs_exp); 
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status
          ) 
       & ~FLAG_CONSTANT
       ); 
/*
    pcform(psub); 
*/
    psub->u.arith.status 
    = (psub->u.arith.status & ~MASK_EXP_TYPE)
    | merge_exp_shape_addition(es, les, res); 
/*
    fprintf(RED_OUT, "exp shape +: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    free(res); 
    return(es); 

  case ARITH_MULTIPLY: 
    les = exp_shape_check(psub->u.arith.lhs_exp); 
/*
    fprintf(RED_OUT, "exp shape mdm, lhs: les->type = %1d\n", 
      les->type
    ); 
*/
    res = exp_shape_check(psub->u.arith.rhs_exp); 
/*
    fprintf(RED_OUT, "exp shape mdm, rhs: res->type = %1d\n", 
      res->type
    ); 
*/
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status
          ) 
       & ~FLAG_CONSTANT
       ); 
/*
    pcform(psub); 
*/
    psub->u.arith.status 
    = (psub->u.arith.status & ~MASK_EXP_TYPE)
    | merge_exp_shape_multiply(es, les, res); 
/*
    fprintf(RED_OUT, "exp shape mdm: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    free(res); 
    return(es); 

  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    les = exp_shape_check(psub->u.arith.lhs_exp); 
/*
    fprintf(RED_OUT, "exp shape mdm, lhs: les->type = %1d\n", 
      les->type
    ); 
*/
    res = exp_shape_check(psub->u.arith.rhs_exp); 
/*
    fprintf(RED_OUT, "exp shape mdm, rhs: res->type = %1d\n", 
      res->type
    ); 
*/
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT) 
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status 
          ) 
       & ~FLAG_CONSTANT 
       ); 
/*
    pcform(psub); 
*/
    psub->u.arith.status 
    = (psub->u.arith.status & ~MASK_EXP_TYPE)
    | merge_exp_shape_divide(es, les, res); 
/*
    fprintf(RED_OUT, "exp shape mdm: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    free(res); 
    return(es); 

  case ARITH_CONDITIONAL: 
    psub->u.arith_cond.cond = rec_ineq_analyze(psub->u.arith_cond.cond); 
    les = exp_shape_check(psub->u.arith_cond.if_exp); 
    if (les->count_clocks > 0 || les->count_denses > 0) { 
      fprintf(RED_OUT, 
        "\nError: Continuous variables in conditional expression at lineno %1d.\n", 
        lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    res = exp_shape_check(psub->u.arith_cond.else_exp); 
    if (res->count_clocks > 0 || res->count_denses > 0) { 
      fprintf(RED_OUT, 
        "\nError: Continuous variables in conditional expression at lineno %1d.\n", 
        lineno 
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    psub->var_status = psub->var_status 
    | psub->u.arith.lhs_exp->var_status | psub->u.arith.rhs_exp->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (  (  psub->u.arith.lhs_exp->exp_status 
          | psub->u.arith.rhs_exp->exp_status
          ) 
       & ~FLAG_CONSTANT
       ); 
    psub->u.arith_cond.type = merge_exp_shape_conditional(es, les, res); 
    return(es); 

  case ARITH_SUM:
    les = exp_shape_check(psub->u.qexp.child);
    psub->var_status = psub->var_status | psub->u.qexp.child->var_status;  
    psub->exp_status = (psub->exp_status & FLAG_CONSTANT)
    | (psub->u.qexp.child->exp_status & ~FLAG_CONSTANT); 
/*
    pcform(psub); 
    fprintf(RED_OUT, "exp shape +: psub->u.arith.type = %1d\n", 
      psub->u.arith.type
    ); 
*/
    free(les); 
    return(es); 

  case TYPE_INLINE_CALL: 
    es = exp_shape_check(psub->u.inline_call.instantiated_exp); 
    psub->var_status = psub->u.inline_call.instantiated_exp->var_status; 
    psub->exp_status = psub->u.inline_call.instantiated_exp->exp_status; 
    return(es); 
    
  default: 
    fprintf(RED_OUT, "\nError 4: Illegal operation or operand of type %1d at line %1d.\n",
	    psub->type, lineno
	    );
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0); 
    exit(0);
  }
}
  /* exp_shape_check() */


  


/*
int	pat_count = 0; 
*/
int	arith_term_count(psub)
  struct ps_exp_type	*psub;
{
  int 	lret, rret;

/*
  fprintf(RED_OUT, "arith_term_count psub type: psub->type=%1d\n", 
	  psub->type
	  ); 
  pcform(psub); 
  fflush(RED_OUT); 
*/
  
  switch(psub->type) {
  case TYPE_MODE_INDEX: 
  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_NULL:
  case TYPE_QFD:
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_INTERVAL: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER: 
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    return(0); 
    
  case TYPE_CLOCK:
  case TYPE_DENSE: 
    return(1); 
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "ERROR: in arith_term_count()\n"
    );  
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n", 
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 
  
  case ARITH_EQ:
  case ARITH_NEQ:
  case ARITH_LEQ:
  case ARITH_GEQ:
  case ARITH_LESS:
  case ARITH_GREATER: 
  case ARITH_ADD:
  case ARITH_MINUS:
    return(arith_term_count(psub->u.arith.lhs_exp)+arith_term_count(psub->u.arith.rhs_exp)); 

  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
/*
    fprintf(RED_OUT, "status checking before return.\n"); 
    fflush(RED_OUT); 
*/
    if (   (psub->var_status & FLAG_CLOCK) 
        || (psub->exp_status & FLAG_HYBRID)
        ) 
      return(1); 
    else 
      return(0); 

  case ARITH_MODULO:
    if (   (psub->var_status & FLAG_CLOCK) 
        || (psub->exp_status & FLAG_HYBRID)
        ) {
      fprintf(RED_OUT, "Error: did not expect to see modulo in this stage.\n"); 
      bk(0); 
    }
    else 
      return(0); 
      
  case ARITH_CONDITIONAL: 
    // Supposedly there should be no clocks and dense variables.  
    return(0); 
      
  case TYPE_INLINE_CALL: 
    return(arith_term_count(psub->u.inline_call.instantiated_exp)); 

  default:
    fprintf(RED_OUT, "\nError 4.1: Illegal operation or operand of type %1d at line %1d.\n",
	    psub->type, lineno
	    ); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0);
  }
}
  /* arith_term_count() */




/********************************************************
 *
 */

struct ps_exp_type	*arith_distribute_on_addition(add_exp, coeff_exp)
     struct ps_exp_type *add_exp, *coeff_exp;
{
  struct ps_exp_type	*lexp, *rexp;

  if (!(  (  add_exp->var_status 
	   & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	   ) 
	||(add_exp->exp_status & FLAG_HYBRID) 
	)
      ) { 
    return(exp_arith(ARITH_MULTIPLY, ps_exp_copy(add_exp), ps_exp_copy(coeff_exp))); 
  } 
    
  switch (add_exp->type) {
  case TYPE_REFERENCE:
  case TYPE_DEREFERENCE: 
  
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_QSYNC_HOLDER: 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_CONDITIONAL: 
    return(exp_arith(ARITH_MULTIPLY, ps_exp_copy(add_exp), ps_exp_copy(coeff_exp))); 
  case ARITH_ADD:
    lexp = arith_distribute_on_addition(add_exp->u.arith.lhs_exp, coeff_exp); 
    rexp = arith_distribute_on_addition(add_exp->u.arith.rhs_exp, coeff_exp); 
    return(exp_arith(ARITH_ADD, lexp, rexp)); 
  case TYPE_INLINE_CALL: 
    return(arith_distribute_on_addition(
      add_exp->u.inline_call.instantiated_exp, 
      coeff_exp 
    ) ); 
  case ARITH_MINUS:
    fprintf(RED_OUT, 
      "Error: there is a minus operator in arith_distribute_left().\n"
    );
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  default:
    fprintf(RED_OUT, "\nError: Illegal arithmetic operation or"); 
    fprintf(RED_OUT, " operand of type %1d at line %1d at arith_distribute_left().\n", add_exp->type, lineno);
    fflush(RED_OUT); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
/* arith_distribute_on_addition() */


int count_arith_distribute = 0; 

struct ps_exp_type	*arith_distribute(psub, coeff)
	struct ps_exp_type	*psub;
	int			coeff;
{
  struct ps_exp_type	*child, *newsub;
/*
  fprintf(RED_OUT, "arith_distribute %1d, psub type: psub->type=%1d, coeff=%1d\n", 
	  ++count_arith_distribute, psub->type, 
	  coeff
	  ); 
  pcform(psub); 
*/  
  switch(psub->type) {
  case TYPE_MODE_INDEX: 
    return(psub); 
    
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_POINTER:
    if (coeff == 1) {
/*
      fprintf(RED_OUT, "\ncount_debug2 = %1d\n", count_debug2++); 
      print_parse_subformula_structure(psub, 0); 
      fprintf(RED_OUT, "\n"); 
*/      
      return(psub); 
    }
    else {
      child = ps_exp_alloc(ARITH_MULTIPLY);
      child->u.arith.lhs_exp = ps_exp_alloc(TYPE_CONSTANT);
      child->u.arith.lhs_exp->u.value = coeff;
/*
      fprintf(RED_OUT, "\ncount_debug2 = %1d\n", count_debug2++); 
      print_parse_subformula_structure(psub, 0); 
      fprintf(RED_OUT, "\n"); 
*/      
      child->u.arith.rhs_exp = psub;
      child->var_status = psub->var_status; 
      child->exp_status = psub->exp_status; 
      return(ps_exp_share(child)); 
    }
    break;
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "ERROR: in arith_distribute()\n"
    ); 
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n", 
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 
  
  case ARITH_ADD:
    if (!(  (   psub->u.arith.lhs_exp->var_status 
	     & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	     )  
          || (psub->u.arith.lhs_exp->exp_status & FLAG_HYBRID)
	  )
        ) { 
      switch (coeff) { 
      case 0: 
        return(exp_atom(TYPE_CONSTANT, 0, NULL)); 
      case 1: 
        return(psub); 
      default: 
        newsub = exp_arith(ARITH_MULTIPLY, psub, 
          exp_atom(TYPE_CONSTANT, coeff, NULL)
        );
        return(newsub);  
      }
    }  
    newsub = exp_arith(psub->type, 
      arith_distribute(psub->u.arith.lhs_exp, coeff), 
      arith_distribute(psub->u.arith.rhs_exp, coeff)
    );
    return(newsub);

  case ARITH_MINUS:
    if (!(  (   psub->u.arith.lhs_exp->var_status 
	     & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	     )  
          ||(   psub->u.arith.rhs_exp->var_status 
	     & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	     )  
          ||(psub->u.arith.lhs_exp->exp_status & FLAG_HYBRID)
          ||(psub->u.arith.rhs_exp->exp_status & FLAG_HYBRID)
	  )
        ) { 
      switch (coeff) { 
      case 0: 
        return(exp_atom(TYPE_CONSTANT, 0, NULL)); 
      case 1: 
        return(psub); 
      default: 
        newsub = exp_arith(ARITH_MULTIPLY, psub, 
          exp_atom(TYPE_CONSTANT, coeff, NULL)
        );
        return(newsub);  
      }
    }  
    newsub = exp_arith(ARITH_ADD, 
      arith_distribute(psub->u.arith.lhs_exp, coeff), 
      arith_distribute(psub->u.arith.rhs_exp, -1*coeff)
    );
    return(newsub); 
    
  case ARITH_MULTIPLY: 
    /* Note that only one of the multiplicants is with variables. */ 
    if (  (   psub->u.arith.lhs_exp->var_status 
	   & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	   )  
        || (psub->u.arith.lhs_exp->exp_status & FLAG_HYBRID)
	) { 
      newsub = ps_exp_alloc(psub->type); 
      newsub->u.arith.lhs_exp = arith_distribute(psub->u.arith.lhs_exp, coeff);
      newsub = arith_distribute_on_addition(newsub->u.arith.lhs_exp, psub->u.arith.rhs_exp); 
      return(newsub); 
    } 
    else if (  (   psub->u.arith.rhs_exp->var_status 
	        & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)
	        )  
             || (psub->u.arith.rhs_exp->exp_status & FLAG_HYBRID)
	     ) { 
      newsub = ps_exp_alloc(psub->type); 
      newsub->u.arith.rhs_exp = arith_distribute(psub->u.arith.rhs_exp, coeff);
      newsub = arith_distribute_on_addition(newsub->u.arith.rhs_exp, psub->u.arith.lhs_exp); 
      return(newsub); 
    } 
    else switch (coeff) { 
    case 0: 
      return(exp_atom(TYPE_CONSTANT, 0, NULL)); 
    case 1: 
      return(psub); 
    default: 
      newsub = exp_arith(ARITH_MULTIPLY, psub, exp_atom(TYPE_CONSTANT, coeff, NULL));
      return(newsub);  
    }  
    
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    if (   (!(   (psub->var_status & FLAG_EXP_STATE_INSIDE)
              || (psub->exp_status & FLAG_HYBRID)
            ) )
        || (   (GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID
            && (!(psub->u.arith.rhs_exp->var_status & FLAG_EXP_STATE_INSIDE))
        )   ) { 
      switch (coeff) { 
      case 0: 
        return(exp_atom(TYPE_CONSTANT, 0, NULL)); 
      case 1: 
        return(psub); 
      default: 
        newsub = exp_arith(ARITH_MULTIPLY, psub, exp_atom(TYPE_CONSTANT, coeff, NULL));
        return(newsub);  
      }
    }  
    fprintf(RED_OUT, "\nError: We don't distribute polynomial constraints.  \n"); 
    fprintf(RED_OUT, "       Division and modulo operaions on variables are treated\n"); 
    fprintf(RED_OUT, "       as polynomial constraints at line %1d.\n", lineno); 
    bk(""); 
    
  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith_cond.cond = psub->u.arith_cond.cond; 
    newsub->u.arith_cond.if_exp 
    = arith_distribute(psub->u.arith_cond.if_exp, coeff); 
    newsub->u.arith_cond.else_exp 
    = arith_distribute(psub->u.arith_cond.else_exp, coeff); 
    return(ps_exp_share(newsub)); 
    break; 
  case TYPE_INLINE_CALL: 
    return(arith_distribute(psub->u.inline_call.instantiated_exp, coeff)); 
    break; 
    
  case ARITH_EQ:
  case ARITH_LEQ:
  case ARITH_LESS:
  case ARITH_GEQ:
  case ARITH_GREATER:
  case ARITH_NEQ:
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith.lhs_exp = arith_distribute(psub->u.arith.lhs_exp, -1*coeff);
    newsub->u.arith.rhs_exp = arith_distribute(psub->u.arith.rhs_exp, coeff);
    return(ps_exp_share(newsub));

  default:
    if (  (!(  (psub->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER))
	     ||(psub->exp_status & FLAG_HYBRID)
           ) )  
        && (   (!(psub->var_status & FLAG_POINTER)) 
            || (psub->var_status & FLAG_QUANTIFIED_SYNC)
            ) 
        ) { 
      switch (coeff) { 
      case 0: 
        return(PS_EXP_ZERO); 
      case 1: 
        return(psub); 
      default: 
        return(exp_arith(ARITH_MULTIPLY, psub, 
          exp_atom(TYPE_CONSTANT, coeff, NULL)
        ) ); 
      }
    }  
    fprintf(RED_OUT, "\nError 2: Illegal operation or operand of type %1d at line %1d.\n",
	    psub->type, lineno
	    );
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0); 
    exit(0);
  }
}
/* arith_distribute() */








struct ps_exp_type	*ARITH_COEFF_VAR;
int			ARITH_TERM_COUNT;
struct parse_term_type	*ARITH_TERM;

/**************************************
* returns NULL if some coefficients are zero.
* otherwise, return the coefficient.
* Please note that this procedure has to be non-distructive on psub.  
*/
struct ps_exp_type	*arith_bound_coeff_analyze_multiply(psub)
  struct ps_exp_type	*psub;
{
  struct ps_exp_type	*lret, *rret, *newp, *newsub;

  switch(psub->type) {
  case TYPE_CONSTANT:
    if (psub->u.value == 0) {
/*
      free(psub);
*/
      return(NULL);
    }

  case TYPE_MODE_INDEX: 
  case TYPE_QFD:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PROCESS_COUNT: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
      return(psub);

  case TYPE_NULL:
/*
    free(psub);
*/
    return(NULL);

  case TYPE_CLOCK:
  case TYPE_DENSE:
    if (ARITH_COEFF_VAR) {
      fprintf(RED_OUT, "Error: a skipped hybrid or polynomial at line %1d in arith_bound_coeff_analyze_multiply().\n", lineno);
      fflush(RED_OUT);
      exit(0);
    }
    ARITH_COEFF_VAR = psub; 
/*
    fprintf(RED_OUT, "\ncount_debug2 = %1d\n", count_debug2++); 
    print_parse_subformula_structure(psub, 0); 
    fprintf(RED_OUT, "\n"); 
*/    
    return(PS_EXP_ONE); 

  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
  case ARITH_CONDITIONAL: 

  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_DISCRETE:
  case TYPE_POINTER:
    return(psub); 
  
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER:
    fprintf(RED_OUT, 
      "ERROR: in arith_bound_coeff_analyze_multiply(), \n"
    ); 
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n", 
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 

  case ARITH_ADD:
    if (!(  (psub->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER))
	  ||(psub->exp_status & FLAG_HYBRID)
        ) ) { 
      if (psub->type == TYPE_CONSTANT && psub->u.value == 0) 
        return(NULL); 
      else 
        return(psub);  
    }
    fprintf(RED_OUT, "Error: there is an add operator in arith_bound_coeff_analyze_multiply().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case ARITH_MINUS:
    if (!(  (psub->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER))
	  ||(psub->exp_status & FLAG_HYBRID)
        ) ) { 
      if (psub->type == TYPE_CONSTANT && psub->u.value == 0) 
        return(NULL); 
      else 
        return(psub);  
    }
    fprintf(RED_OUT, 
      "Error: there is a minus operator in arith_bound_coeff_analyze_multiply().\n"
    );
    pcform(psub); 
    fflush(RED_OUT);
    bk(0); 
    for (; 1; );
    exit(0);
  case ARITH_MULTIPLY:
    lret = arith_bound_coeff_analyze_multiply(psub->u.arith.lhs_exp);
    rret = arith_bound_coeff_analyze_multiply(psub->u.arith.rhs_exp);
    if (lret == NULL) {
      return(NULL);
    }
    else if (rret == NULL) {
      return(NULL); 
    } 
    else if (lret->type == TYPE_CONSTANT) {
      switch (lret->u.value) { 
      case 0:
	return(NULL); 
      case 1:
        return(rret); 
      default:
        if (rret->type == TYPE_CONSTANT) {
	  switch (rret->u.value) {
	  case 0:
	    return(NULL);
	  case 1:
	    return(lret);
	  default:
	    newsub = ps_exp_alloc(TYPE_CONSTANT); 
	    newsub->var_status = 0; 
	    newsub->exp_status = 0; 
	    newsub->u.value = lret->u.value * rret->u.value;
	    return(ps_exp_share(newsub));
	  }
	}
	else {
	  return(exp_arith(ARITH_MULTIPLY, lret, rret));
	}
      }
    }
    else if (rret->type == TYPE_CONSTANT) {
      switch (rret->u.value) {
      case 0:
	return(rret);
      case 1:
        return(lret);
      default:
	return(exp_arith(ARITH_MULTIPLY, lret, rret));
      }
    }
    else {
      return(exp_arith(ARITH_MULTIPLY, lret, rret));
    }
    break;

  case ARITH_DIVIDE:
    return(exp_arith(psub->type, 
      arith_bound_coeff_analyze_multiply(
        psub->u.arith.lhs_exp
      ), 
      psub->u.arith.rhs_exp
    ) );
    break;
    
  case ARITH_MODULO: 
    return(psub); 

  default:
    fprintf(RED_OUT, "\nError 5: Illegal operation or operand at line %1d.\n", lineno);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

}
  /* arith_bound_coeff_analyze_multiply() */



/* This procedure is used to extract the offset in an linear inequality. 
 * The offset can be composed of constants, discrete variables, 
 * and arithmetic operators. 
 * It returns a ps_exp if psub does not contain a variable
 * since variables are supposed to be recorded on LHS in ARITH_TERM.
 * If psub contains a variable, then it returns a NULL since it is
 * supposed to be recorded on LHS.
 * Please note that this procedure has to be non-distructive on psub.  
 */
struct ps_exp_type	*rec_arith_bound_coeff_analyze(psub)
  struct ps_exp_type	*psub;
{
  struct ps_exp_type	*lret, *rret;
  struct ps_exp_type	*newp, *newsub;
  int			s; 

  switch(psub->type) {
  case TYPE_CONSTANT:
    if (psub->u.value == 0)
      return(NULL);
    else 
      return(psub); 

  case TYPE_FLOAT_CONSTANT: 
    if (psub->u.float_value == 0.0) 
      return(NULL); 
    else 
      return(psub); 
      
  case TYPE_QFD:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_PROCESS_COUNT: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case TYPE_DISCRETE:
  case TYPE_POINTER:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    return(psub);
  case TYPE_MODE_INDEX: 
    return(psub); 
    
  case TYPE_NULL:
    return(NULL);
  case TYPE_CLOCK:
  case TYPE_DENSE:
    ARITH_TERM[ARITH_TERM_COUNT].coeff = PS_EXP_NEG_ONE;  
/* 
    fprintf(RED_OUT, "\ntesting count_debug2 = %1d\n", count_debug2++); 
    print_parse_subformula_structure(psub, 0); 
    fprintf(RED_OUT, "\n"); 
    if (psub->status) newp = psub; 
*/ 
    ARITH_TERM[ARITH_TERM_COUNT].operand = psub;
    ARITH_TERM_COUNT++;
    return(NULL);

  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
    fprintf(RED_OUT,
      "ERROR: in rec_arith_bound_coeff_analyze()\n" 
    ); 
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n",  
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 

  case ARITH_ADD:
    lret = rec_arith_bound_coeff_analyze(psub->u.arith.lhs_exp);
    rret = rec_arith_bound_coeff_analyze(psub->u.arith.rhs_exp);
    if (lret)
      if (rret) {
        if (lret->type == TYPE_CONSTANT)
	  if (lret->u.value == 0) {
	    return(rret);
	  }
	  else if (rret->type == TYPE_CONSTANT) { 
	    if ((s = lret->u.value + rret->u.value) == 0) {
	      return(NULL);
	    }
	    else {
	      newp = ps_exp_alloc(TYPE_CONSTANT); 
	      newp->u.value = s;
	      return(ps_exp_share(newp)); 
	    }
	  }

        if (rret->type == TYPE_CONSTANT && rret->u.value == 0) {
	  return(lret);
  	}
        return(exp_arith(ARITH_ADD, lret, rret));
      }
      else
        return(lret);
    else
      return(rret);

  case ARITH_MINUS:
    lret = rec_arith_bound_coeff_analyze(psub->u.arith.lhs_exp);
    rret = rec_arith_bound_coeff_analyze(psub->u.arith.rhs_exp);
    if (lret)
      if (rret) {
        if (lret->type == TYPE_CONSTANT)
	  if (lret->u.value == 0) {
            if (rret->type == TYPE_CONSTANT) { 
	      return(exp_atom(TYPE_CONSTANT, -1 * rret->u.value, NULL));
	    }
	    else { 
              return(exp_arith(ARITH_MULTIPLY, 
                exp_atom(TYPE_CONSTANT, -1, NULL), 
                rret
              ) ); 
	    } 
	  }
	  else if (rret->type == TYPE_CONSTANT) { 
	    if ((s = lret->u.value - rret->u.value) == 0) {
	      return(NULL);
	    }
	    else {
	      return(exp_atom(TYPE_CONSTANT, s, NULL)); 
	    }
	  }

        if (rret->type == TYPE_CONSTANT && rret->u.value == 0) {
	  return(lret);
  	}

        return(exp_arith(ARITH_MINUS, lret, rret)); 
      }
      else
        return(lret);
    else 
      if (rret)  
        if (rret->type == TYPE_CONSTANT) {
          return(exp_atom(TYPE_CONSTANT, -1 * rret->u.value, NULL)); 
        } 
        else { 
          return(exp_arith(ARITH_MULTIPLY, 
            exp_atom(TYPE_CONSTANT, -1, NULL),  
	    rret
	  ) ); 
        }
      else 
        return(NULL);
/*
    fprintf(RED_OUT, 
      "Error: there is a minus operator in arith_bound_coeff_analyze().\n"
    );
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
 */ 
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
    ARITH_COEFF_VAR = NULL; 
    /* The following routine gives us the coefficient and, with side-effect, puts 
     * the variable in ARITH_COEFF_VAR. 
     */ 
    psub = arith_bound_coeff_analyze_multiply(psub);
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "psub from arith_bound_coeff_analyze_multiply:\n"); 
    pcform(psub); 
    #endif 
    
    if (psub == NULL)
      return(NULL);
    else if (ARITH_COEFF_VAR == NULL)
      return(psub);
    else if (psub->type == TYPE_CONSTANT) {
      switch (psub->u.value) {
      case 0:
	return(NULL);
	break;
      default:
        ARITH_TERM[ARITH_TERM_COUNT].coeff = exp_atom(
          TYPE_CONSTANT, -1*psub->u.value, NULL
        );
	ARITH_TERM[ARITH_TERM_COUNT].operand = ARITH_COEFF_VAR;
        ARITH_TERM_COUNT++;
        return(NULL);
      }
    }
    else {
      ARITH_TERM[ARITH_TERM_COUNT].coeff = exp_arith(
        ARITH_MULTIPLY, PS_EXP_NEG_ONE, psub
      );
      ARITH_TERM[ARITH_TERM_COUNT].operand = ARITH_COEFF_VAR;
      ARITH_TERM_COUNT++;
      return(NULL);
    }
    break;

  case ARITH_MODULO: 
  case ARITH_CONDITIONAL: 
    return(psub); 
  
  case TYPE_INLINE_CALL: 
    return(rec_arith_bound_coeff_analyze(
      psub->u.inline_call.instantiated_exp
    ) ); 
    
  default:
    fprintf(RED_OUT, "\nError 6: Illegal operation or operand of type %1d at line %1d.\n",
	    psub->type, lineno
	    ); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

}
  /* rec_arith_bound_coeff_analyze() */


int	count_abca = 0; 

struct ps_exp_type	*arith_bound_coeff_analyze(psub, term_count)
	struct ps_exp_type	*psub;
{
  int			original_ineq_type, ti; 
  struct ps_exp_type	*newsub; 

/*
  fprintf(RED_OUT, "count_abca = %1d with term_count = %1d\n", 
    ++count_abca, term_count 
  ); 
  pcform(psub); 
*/  
  ARITH_TERM = (struct parse_term_type *) malloc(term_count * sizeof(struct parse_term_type));
  ARITH_TERM_COUNT = 0;
  newsub = ps_exp_alloc(psub->type-10);
  original_ineq_type = psub->type; 
  psub->type = ARITH_ADD;

  newsub->u.ineq.offset = rec_arith_bound_coeff_analyze(psub);
  psub->type = original_ineq_type;
  if (newsub->u.ineq.offset == NULL) {
    newsub->u.ineq.offset = PS_EXP_ZERO; 
  }
  newsub->u.ineq.offset = exp_static_evaluation(
    newsub->u.ineq.offset, FLAG_NO_PI_STATIC_EVAL, NULL
  );  
  newsub->u.ineq.term_count = term_count;
  newsub->u.ineq.term = ARITH_TERM; 
  newsub->var_status = 0; 
  newsub->exp_status = 0; 
  for (ti = 0; ti < term_count; ti++) {
    newsub->var_status = newsub->var_status 
    | newsub->u.ineq.term[ti].operand->var_status; 
    newsub->exp_status = newsub->exp_status 
    | newsub->u.ineq.term[ti].operand->exp_status; 
  } 
  newsub->u.ineq.type = psub->u.arith.status & MASK_EXP_TYPE; 
/*  
  fprintf(RED_OUT, "YYY count_debug2 = %1d at line %1d\n", count_debug2++, lineno); 
  print_parse_subformula_structure(psub->u.ineq.term[0].operand, 0); 
  fprintf(RED_OUT, "\n"); 
*/  
  return(ps_exp_share(newsub));
}
  /* arith_bound_coeff_analyze() */




void	find_coeff_in_discrete_constant_arith(
  struct ps_exp_type	*psub, 
  struct ps_exp_type	**var_ptr, 
  struct ps_exp_type	**coeff_ptr, 
  struct ps_exp_type	**offset_ptr
) { 
  struct ps_exp_type	*lvar, *loffset, *lcoeff, *rvar, *roffset, *rcoeff;
  struct ps_exp_type	*newp, *newsub;

  switch(psub->type) {
  case TYPE_NULL: 
  case TYPE_FALSE:
    *offset_ptr = PS_EXP_ZERO; 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_TRUE: 
    *offset_ptr = PS_EXP_ONE; 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_MACRO_CONSTANT: 
    *offset_ptr = psub->u.inline_call.instantiated_exp; 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_CONSTANT:
  case TYPE_FLOAT_CONSTANT: 
    *offset_ptr = psub; 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_MODE_INDEX: 
    *offset_ptr = exp_atom(TYPE_CONSTANT, psub->u.mode_index.value, NULL); 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_PROCESS_COUNT: 
    *offset_ptr = exp_atom(TYPE_CONSTANT, PROCESS_COUNT, NULL); 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 

  case TYPE_QFD:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_QSYNC_HOLDER: 
    *offset_ptr = psub; 
    *coeff_ptr = NULL; 
    *var_ptr = NULL; 
    return; 
  
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    if (   (!(psub->u.atom.var->status & FLAG_VAR_STACK)) 
        && (  psub->u.atom.exp_base_proc_index->var_status 
            & FLAG_EXP_STATE_INSIDE
        )   ) { 
      fprintf(RED_OUT, 
        "\nERROR: inappropriate classification on inequality: "
      ); 
      pcform(psub); 
      bk(0); 
    }
    *var_ptr = psub; 
    *offset_ptr = NULL; 
    *coeff_ptr = PS_EXP_ONE; 
    return; 

  case TYPE_POINTER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_BDD: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
  case ARITH_CONDITIONAL:     
    fprintf(RED_OUT, 
      "ERROR: find_coeff_in_discrete_constant_arith()\n"
    );  
    fprintf(RED_OUT, 
      "       a bdd variable %s in an arithmetic expression at line %1d.\n", 
      psub->u.atom.var->name, psub->lineno
    ); 
    bk(0); 
    break; 

  case ARITH_ADD:
    find_coeff_in_discrete_constant_arith(psub->u.arith.lhs_exp, 
      &lvar, &lcoeff, &loffset 
    );
    if (lvar) { 
      *var_ptr = lvar; 
      *coeff_ptr = lcoeff; 
      if (loffset) 
        *offset_ptr = exp_arith(ARITH_ADD, loffset, psub->u.arith.rhs_exp); 
      else 
        *offset_ptr = psub->u.arith.rhs_exp; 
    }
    else {
      find_coeff_in_discrete_constant_arith(psub->u.arith.rhs_exp, 
        &rvar, &rcoeff, &roffset 
      ); 
      if (rvar) { 
        *var_ptr = rvar; 
        *coeff_ptr = rcoeff; 
        if (roffset) 
          *offset_ptr = exp_arith(ARITH_ADD, psub->u.arith.lhs_exp, roffset); 
        else 
          *offset_ptr = psub->u.arith.lhs_exp; 
      }
      else { 
        *offset_ptr = psub; 
        *coeff_ptr = NULL; 
        *var_ptr = NULL; 
      }
    } 
    return; 

  case ARITH_MINUS:
    find_coeff_in_discrete_constant_arith(psub->u.arith.lhs_exp, 
      &lvar, &lcoeff, &loffset 
    );
    if (lvar) { 
      *var_ptr = lvar; 
      *coeff_ptr = lcoeff; 
      if (loffset) 
        *offset_ptr = exp_arith(ARITH_MINUS, loffset, psub->u.arith.rhs_exp); 
      else 
        *offset_ptr = exp_arith(ARITH_MULTIPLY, PS_EXP_NEG_ONE, 
          psub->u.arith.rhs_exp
        ); 
    }
    else {
      find_coeff_in_discrete_constant_arith(psub->u.arith.rhs_exp, 
        &rvar, &rcoeff, &roffset 
      ); 
      if (rvar) { 
        *var_ptr = rvar; 
        *coeff_ptr = exp_arith(ARITH_MULTIPLY, PS_EXP_NEG_ONE, rcoeff); 
        if (roffset) 
          *offset_ptr = exp_arith(ARITH_MINUS, psub->u.arith.lhs_exp, roffset); 
        else 
          *offset_ptr = psub->u.arith.lhs_exp; 
      }
      else { 
        *offset_ptr = psub; 
        *coeff_ptr = NULL; 
        *var_ptr = NULL; 
      } 
    } 
    return; 

  case ARITH_MULTIPLY:
    find_coeff_in_discrete_constant_arith(psub->u.arith.lhs_exp, 
      &lvar, &lcoeff, &loffset 
    ); 
    if (lvar) { 
      *var_ptr = lvar; 
      *coeff_ptr = exp_arith(ARITH_MULTIPLY, lcoeff, psub->u.arith.rhs_exp); 
      if (loffset) 
        *offset_ptr = exp_arith(ARITH_MULTIPLY, loffset, psub->u.arith.rhs_exp); 
      else 
        *offset_ptr = NULL; 
    }
    else {
      find_coeff_in_discrete_constant_arith(psub->u.arith.rhs_exp, 
        &rvar, &rcoeff, &roffset 
      ); 
      if (rvar) { 
        *var_ptr = rvar; 
        *coeff_ptr = exp_arith(ARITH_MULTIPLY, rcoeff, psub->u.arith.lhs_exp); 
        if (roffset) 
          *offset_ptr = exp_arith(ARITH_MULTIPLY, psub->u.arith.lhs_exp, roffset); 
        else 
          *offset_ptr = NULL; 
      }
      else { 
        *offset_ptr = psub; 
        *coeff_ptr = NULL; 
        *var_ptr = NULL; 
      }
    } 
    return; 

  case TYPE_INLINE_CALL: 
    find_coeff_in_discrete_constant_arith(
      psub->u.inline_call.instantiated_exp, var_ptr, coeff_ptr, offset_ptr 
    ); 
    return; 

  default:
    fprintf(RED_OUT, "\nError 6: Illegal operation or operand of type %1d at line %1d.\n",
	    psub->type, lineno
	    ); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
}
  /* find_coeff_in_discrete_constant_arith() */  
  

struct ps_exp_type	*exp_ineq_discrete_constant_special_form(
  struct ps_exp_type	*psub
) { 
  struct ps_exp_type	*newsub, *var, *coeff, *offset, *rhs; 
  int			op; 
  
  if (psub->u.arith.lhs_exp->var_status 
      & (FLAG_DISCRETE | FLAG_POINTER | FLAG_FLOAT | FLAG_DOUBLE)
      ) {
    find_coeff_in_discrete_constant_arith(
      psub->u.arith.lhs_exp, &var, &coeff, &offset
    ); 
    op = psub->type; 
    if (offset) 
      rhs = exp_arith(ARITH_MINUS, psub->u.arith.rhs_exp, offset); 
    else 
      rhs = psub->u.arith.rhs_exp; 
  } 
  else { 
    find_coeff_in_discrete_constant_arith(
      psub->u.arith.rhs_exp, &var, &coeff, &offset
    ); 
    op = op_ineq_reverse(psub->type); 
    if (offset) 
      rhs = exp_arith(ARITH_MINUS, psub->u.arith.lhs_exp, offset); 
    else 
      rhs = psub->u.arith.lhs_exp; 
  }
  if (coeff == NULL) 
    coeff = PS_EXP_ONE; 
  if (coeff->type == TYPE_CONSTANT) { 
    if (coeff->u.value == 0) {
      newsub = exp_arith(op, PS_EXP_ZERO, rhs); 
      newsub->var_status = newsub->var_status & ~FLAG_EXP_STATE_INSIDE; 
      newsub->u.arith.status 
      = (newsub->u.arith.status & ~MASK_EXP_TYPE) 
      | FLAG_EXP_STATIC;
    } 
    else if (coeff->u.value < 0) { 
      op = op_ineq_reverse(op); 
      newsub = exp_arith(op, var, exp_arith(ARITH_DIVIDE, rhs, coeff)); 
      newsub->u.arith.status 
      = (newsub->u.arith.status & ~MASK_EXP_TYPE) 
      | FLAG_EXP_DISCRETE_CONSTANT;
    } 
    else { 
      newsub = exp_arith(op, var, exp_arith(ARITH_DIVIDE, rhs, coeff)); 
      newsub->u.arith.status 
      = (newsub->u.arith.status & ~MASK_EXP_TYPE) 
      | FLAG_EXP_DISCRETE_CONSTANT;
    } 
  } 
  else {
    struct ps_exp_type		*neg, *pos, *zero; 
    struct ps_bunit_type	*bu; 
    
    neg = exp_boolean(AND, exp_arith(ARITH_LESS, coeff, PS_EXP_ZERO), 
      exp_arith(op_ineq_reverse(op), var, 
        exp_arith(ARITH_DIVIDE, rhs, coeff)
    ) ); 
    neg->u.arith.status = (neg->u.arith.status & ~MASK_EXP_TYPE) 
    | FLAG_EXP_DISCRETE_CONSTANT;

    zero = exp_boolean(AND, exp_arith(ARITH_EQ, coeff, PS_EXP_ZERO), 
      exp_arith(op, PS_EXP_ZERO, rhs)
    ); 
    zero->u.arith.status = (zero->u.arith.status & ~MASK_EXP_TYPE) 
    | FLAG_EXP_DISCRETE_CONSTANT;

    pos = exp_boolean(AND, exp_arith(ARITH_GREATER, coeff, PS_EXP_ZERO), 
      exp_arith(op, var, 
        exp_arith(ARITH_DIVIDE, rhs, coeff)
    ) ); 
    pos->u.arith.status = (pos->u.arith.status & ~MASK_EXP_TYPE) 
    | FLAG_EXP_DISCRETE_CONSTANT; 

    newsub = ps_exp_alloc(OR); 
    newsub->u.bexp.len = 3; 
    newsub->u.bexp.blist = NULL; 
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = pos; 
    bu->bnext = newsub->u.bexp.blist; 
    newsub->u.bexp.blist = bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = zero; 
    bu->bnext = newsub->u.bexp.blist; 
    newsub->u.bexp.blist = bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = neg; 
    bu->bnext = newsub->u.bexp.blist; 
    newsub->u.bexp.blist = bu; 
    
    newsub->var_status = FLAG_DISCRETE; 
    newsub->exp_status = FLAG_CONSTANT; 
    newsub = ps_exp_share(newsub); 
  }
/*
  fprintf(RED_OUT, "\nsimplified form of "); 
  pcform(psub); 
  fprintf(RED_OUT, "  is "); 
  pcform(newsub); 
*/
  return(newsub); 
}
  /* exp_ineq_discrete_constant_special_form() */ 



/* Analyze the coefficient and number of clocks. */
struct ps_exp_type	*CLOCK_POS, *CLOCK_NEG;





/* equality and inequality will be removed.
   larger than and leq will be replaced.
*/
int	count_ineq_ana = 0; 

struct ps_exp_type	*ineq_analyze(psub) 
     struct ps_exp_type	*psub;
{
  int			op, ti, term_count, pi, 
			more_qfd_valuation, num, den;
  struct ps_exp_type	*tmp, *newsub; 
  struct exp_shape_type	*es; 

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "====(%1d, Entering ineq_analyze(%x))==============:\n", 
    ++count_ineq_ana, psub  
  );
  // print_parse_subformula_structure(psub, 0); 
  pcform(psub); 
  #endif 

  es = exp_shape_check(psub); 
  psub->u.arith.status = (psub->u.arith.status & MASK_EXP_TYPE) | es->type; 
  switch (es->type) { 
  case FLAG_EXP_STATIC: 
/*
    fprintf(RED_OUT, "\nineq shape = static.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    free(es); 
    return(psub); 
  case FLAG_EXP_DISCRETE_CONSTANT: 
/*
    fprintf(RED_OUT, "\nineq shape = disc const.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    free(es); 
    if (psub->var_status & FLAG_QUANTIFIED_SYNC) 
      // This is to be processed in sync_statement or prepare_sync_xtions().
      return(psub); 
    else 
      return(exp_ineq_discrete_constant_special_form(psub)); 
    break; 
  case FLAG_EXP_DISCRETE_LINEAR: 
/*
    fprintf(RED_OUT, "\nineq shape = disc lin.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    free(es); 
    return(psub); 
  case FLAG_EXP_DISCRETE_POLYNOMIAL: 
/*
    fprintf(RED_OUT, "\nineq shape = disc poly.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    free(es); 
    return(psub); 
  case FLAG_EXP_CLOCK_MIXED: 
/*
    fprintf(RED_OUT, "\nineq shape = clock mixed.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    break; 
      
  case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
/*
    fprintf(RED_OUT, "\nineq shape = clock mixed.\n"); 
    pcform(psub); 
    fflush(RED_OUT);  
*/
    break; 

  case FLAG_EXP_DENSE_POLYNOMIAL: 
    fprintf(RED_OUT, 
      "Error: Illegal polynomial operations on dense variables at line %1d\n", 
      lineno
    ); 
    bk(0); 
    break; 
  } 
  free(es); 
  
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nAfter polynomial check().\n"); 
//  print_parse_subformula_structure(psub, 0); 
  pcform(psub); 
  fflush(RED_OUT); 
/*
  fprintf(RED_OUT, "** \n"); 
*/
  #endif 
  
  op = psub->type;
  tmp = arith_distribute(psub, 1); /* After this statement, negation on LHS
				  * has already been performed.  Thus don't
				  * count on the signs of the LHS before
				  * arith_bound_coeff_analyze().
				  */
  psub = tmp; 
  // The following special case analysis is important for the 
  // efficiency of the model. 
  // The reason is that inequalities that can be rewritten to ax~b for 
  // some discrete variable x occur so often.  

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nAfter arith distribute().\n"); 
  print_parse_subformula_structure(psub, 0); 
  fflush(RED_OUT); 
  #endif 

  term_count = arith_term_count(psub);
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nAfter term counting().\n"); 
  print_parse_subformula_structure(psub, 0); 
  fflush(RED_OUT); 
  #endif 

  if (term_count > MAX_TERM_COUNT)
    MAX_TERM_COUNT = term_count;

  psub = arith_bound_coeff_analyze(psub, term_count);
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\nAfter bound coeff analysis().\n"); 
  print_parse_subformula_structure(psub, 0); 
  fflush(RED_OUT); 
  #endif 

  /* set the flag based on the operand types */
  
    /* if it is only a discrete inequality, then we classify its type. */
  if (   (psub->var_status & FLAG_DISCRETE) 
      && (!(psub->var_status & FLAG_CLOCK))
      && (!(psub->exp_status & FLAG_HYBRID))
      ) {
    if (term_count > 1)  
      psub->u.ineq.type = FLAG_EXP_DISCRETE_LINEAR;
    else 
      psub->u.ineq.type = FLAG_EXP_DISCRETE_CONSTANT;
  }

//  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "====(%1d, ineq_analyze, finding max time bound)==============:\n", 
    ++count_ineq_ana   
  );
  pcform(psub); 
//  #endif 
  if (psub->var_status & (FLAG_CLOCK | FLAG_DENSE)) {
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      int	lb, ub, flag; 
      float	flb, fub; 
      
      flag = get_integer_range(psub->u.ineq.offset, pi, &lb, &ub, &flb, &fub); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
/*
        fprintf(RED_OUT, 
          "\nWARNING: unspecific quantification range type at line %1d in ineq_analyze().\n", 
          psub->lineno 
        ); 
        pcform(psub); 
        fflush(RED_OUT); 
*/
        continue; 
//        bk(0); 
      } 
      if (lb < 0) 
        lb = -1 * lb; 
      if (ub < 0) 
        ub = -1 * ub; 
      if (lb > ub) 
        ub = lb; 
        
      if (ALL_CLOCK_TIMING_BOUND < ub) {
	ALL_CLOCK_TIMING_BOUND = ub; 
// #ifdef RED_DEBUG_YACC_MODE
	fprintf(RED_OUT, "0: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
	  ALL_CLOCK_TIMING_BOUND
	); 
	fflush(RED_OUT); 
// #endif 
      } 
    }
  }

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, 
    "\n====(Leaving ineq_analyze() with psub->type = %1d):\n", 
    psub->type 
  );
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 

  return(psub);
}
  /* ineq_analyze() */





struct ps_exp_type	*rec_ineq_analyze(psub) 
	struct ps_exp_type	*psub; 
{ 
  int				jj; 
  struct ps_bunit_type		*pbu, dummy_bu;
  struct ps_exp_type		*newsub; 
  struct ps_fairness_link_type	*fl; 
  
/*
  fprintf(RED_OUT, "****(Entering rec_ineq_analyze())==============:\n");
  print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
  fprintf(RED_OUT, "\n"); 
*/
  if (!psub) 
    return(NULL); 
    
  switch(psub->type) {
  case TYPE_FALSE : 
  case TYPE_TRUE :
  case TYPE_CONSTANT: 
  case TYPE_FLOAT_CONSTANT: 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_MODE_INDEX: 
  case TYPE_INTERVAL: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_NULL:  
  case TYPE_QFD: 
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case TYPE_SYNCHRONIZER: 
  case TYPE_CLOCK: 
  case TYPE_DENSE: 
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_BDD: 
  case EQ :
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
    return(psub); 
  
  case BIT_NOT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.exp = rec_ineq_analyze(psub->u.exp); 
    if (newsub->u.exp->type == TYPE_CONSTANT) { 
      newsub->u.value = ~newsub->u.exp->u.value; 
      newsub->var_status = 0; 
      newsub->exp_status = FLAG_CONSTANT; 
    } 
    return(ps_exp_share(newsub)); 
  
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    newsub = exp_arith(psub->type, 
      rec_ineq_analyze(psub->u.arith.lhs_exp), 
      rec_ineq_analyze(psub->u.arith.rhs_exp)
    ); 
/*
    fprintf(RED_OUT, "\nineq analyze with s%x: ", 
      newsub->status
    ); 
    pcform(newsub); 
*/
    return(newsub); 
 
  case ARITH_CONDITIONAL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.arith_cond.cond = rec_ineq_analyze(psub->u.arith_cond.cond); 
    newsub->u.arith_cond.if_exp 
    = rec_ineq_analyze(psub->u.arith_cond.if_exp); 
    newsub->u.arith_cond.else_exp 
    = rec_ineq_analyze(psub->u.arith_cond.else_exp); 
    return(ps_exp_share(newsub)); 
    break; 
  
  case TYPE_INLINE_CALL: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.inline_call.instantiated_exp
    = rec_ineq_analyze( 
      psub->u.inline_call.instantiated_exp
    ); 
    return(ps_exp_share(newsub)); 
    
  case ARITH_EQ :
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ : 
    return(ineq_analyze(psub)); 
    break; 
  case AND :
  case OR :
  case NOT : 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.len = 0; 
    dummy_bu.bnext = NULL; 
    for (pbu = psub->u.bexp.blist; pbu; pbu = pbu->bnext) { 
      insert_sorted_blist_dummy_head(
        psub->type, 
        rec_ineq_analyze(pbu->subexp), 
        &dummy_bu, &(newsub->u.bexp.len) 
      ); 
    } 
    newsub->u.bexp.blist = dummy_bu.bnext; 
/*
    fprintf(RED_OUT, "Modal rewriting AND-OR: EXP_MODAL_INSIDE, %1x", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    for (jj = newsub->u.bexp.len, pbu = psub->u.bexp.blist; 
	 jj; 
	 jj--, pbu = pbu->bnext
	 ) {
      fprintf(RED_OUT, ", %1x", pbu->subexp->status & FLAG_EXP_MODAL_INSIDE); 
    }
    fprintf(RED_OUT, "\n"); 
    print_parse_subformula_structure(newsub, 
      FLAG_GENERAL_PROCESS_IDENTIFIER
    ); 
*/
    return(ps_exp_share(newsub)); 
    
  case IMPLY :
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.bexp.blist = (struct ps_bunit_type *) 
      malloc(sizeof(struct ps_bunit_type)); 
    newsub->u.bexp.blist->subexp = rec_ineq_analyze(
      psub->u.bexp.blist->subexp
    ); 
    newsub->u.bexp.blist->bnext = (struct ps_bunit_type *) 
      malloc(sizeof(struct ps_bunit_type)); 
    newsub->u.bexp.blist->bnext->subexp = rec_ineq_analyze(
      psub->u.bexp.blist->bnext->subexp
    ); 
    newsub->u.bexp.blist->bnext->bnext = NULL; 
    /*
    fprintf(RED_OUT, "Shorthand analyzing AND-OR: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 0); 
*/
    return(ps_exp_share(newsub)); 

  case FORALL: 
  case EXISTS: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.qexp.child = rec_ineq_analyze(psub->u.qexp.child); 
    newsub->u.qexp.lb_exp = rec_ineq_analyze(psub->u.qexp.lb_exp); 
    newsub->u.qexp.ub_exp = rec_ineq_analyze(psub->u.qexp.ub_exp); 
/*
    fprintf(RED_OUT, "Shorthand analyzing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 0); 
*/
    return(ps_exp_share(newsub)); 
    break; 
    
  case RESET: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.reset.child = rec_ineq_analyze(psub->u.reset.child); 
/*
    fprintf(RED_OUT, "Shorthand analyzing RESET: EXP_MODAL_INSIDE, %1x\n", 
	    newsub->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure(newsub, 0); 
*/
    return(ps_exp_share(newsub)); 
    break; 
    
  case FORALL_ALWAYS: 
  case EXISTS_ALWAYS: 
  case EXISTS_ALMOST: 
  case FORALL_ALMOST: 

  case FORALL_EVENTUALLY : 
  case EXISTS_EVENTUALLY: 
  case EXISTS_CHANGE: 
  case FORALL_CHANGE: 
  case EXISTS_OFTEN: 
  case FORALL_OFTEN: 

  case FORALL_UNTIL: 
  case EXISTS_UNTIL: 
  
  case TYPE_GAME_SIM: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
    newsub->u.mexp.dest_child = rec_ineq_analyze(psub->u.mexp.dest_child); 
    newsub->u.mexp.event_restriction = rec_ineq_analyze(psub->u.mexp.event_restriction); 
    newsub->u.mexp.path_child = rec_ineq_analyze(psub->u.mexp.path_child); 
    newsub->u.mexp.time_restriction 
    = rec_ineq_analyze(psub->u.mexp.time_restriction); 
    newsub->u.mexp.strong_fairness_list = NULL; 
    newsub->u.mexp.strong_fairness_count = 0; 
    for (fl = psub->u.mexp.strong_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.strong_fairness_list = insert_sorted_flist(
        rec_ineq_analyze(fl->fairness), 
        fl->status, 
        newsub->u.mexp.strong_fairness_list, 
        &(newsub->u.mexp.strong_fairness_count) 
      ); 
    } 

    newsub->u.mexp.weak_fairness_list = NULL; 
    newsub->u.mexp.weak_fairness_count = 0; 
    for (fl = psub->u.mexp.weak_fairness_list; 
      fl; 
      fl = fl->next_ps_fairness_link
    ) {
      newsub->u.mexp.weak_fairness_list = insert_sorted_flist(
        rec_ineq_analyze(fl->fairness), 
        fl->status, 
        newsub->u.mexp.weak_fairness_list, 
        &(newsub->u.mexp.weak_fairness_count) 
      ); 
    } 

    return(ps_exp_share(newsub)); 
    break; 
  
  case LINEAR_EVENT: 
    newsub = ps_exp_alloc(psub->type); 
    *newsub = *psub; 
/*
    psub->u.eexp.event_child = rec_ineq_analyze(psub->u.eexp.event_child); 
*/
    newsub->u.eexp.precond_exp = rec_ineq_analyze(psub->u.eexp.precond_exp); 
    if (psub->u.eexp.event_exp)
      newsub->u.eexp.event_exp = rec_ineq_analyze(psub->u.eexp.event_exp); 
    newsub->u.eexp.postcond_exp = rec_ineq_analyze(psub->u.eexp.postcond_exp); 
    return(ps_exp_share(newsub)); 
    break; 
    
  case RED: 
    if (psub == PS_EXP_TRUE || psub == PS_EXP_FALSE) 
      return(psub); 
    else { 
      fprintf(RED_OUT, "ineq_analyze() already analyzed the following:\n"); 
      pcform(psub);  
      return(psub); 
    }
    break; 

  default: 
    fprintf(RED_OUT, 
      "\nError 3: Unrecognized condition operator %1d at line %1d.\n", 
      psub->type, lineno
    );
    print_parse_subformula(psub, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n"); 
    bk(0); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
}
  /* rec_ineq_analyze() */  




/********************************************************
 *
 *  How should we do this for clocks ?
 *
 *  1. determine if the expressions are simple and then get the values of each expression
 *  2. get the two clocks.
 */

struct parse_statement_type 	*add_increment(
  int				op, 
  struct ps_exp_type		*lhs, 
  struct ps_exp_type		*offset
) {  
  struct parse_statement_type 	*as;

  as = (struct parse_statement_type *) 
    malloc(sizeof(struct parse_statement_type));

  as->op = op; 
  as->u.act.lhs = lhs;  
  as->u.act.offset = as->u.act.rhs_exp = offset; 
  
  as->u.act.term_count = 1;
  as->u.act.term = (struct parse_term_type *) malloc(sizeof(struct parse_term_type));
  as->u.act.term[0].operand = as->u.act.lhs;
  as->u.act.term[0].coeff = PS_EXP_ONE; 
  
  as->st_status = FLAG_ACTION_LHS_RECURSION;; 
  if (   (lhs->var_status & FLAG_QUANTIFIED_SYNC) 
      || (offset->var_status & FLAG_QUANTIFIED_SYNC) 
      ) 
    as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
  if (   (lhs->exp_status & FLAG_INDIRECTION) 
      || (offset->exp_status & FLAG_INDIRECTION) 
      ) 
    as->st_status = as->st_status | FLAG_ACTION_INDIRECTION; 

  return(as); 
}
  /* add_increment() */ 



// #ifdef RED_DEBUG_YACC_MODE
int	count_ass_bca = 0; 
// #endif 

struct ps_exp_type	*assignment_bound_coeff_analyze(as, term_count)
	struct parse_statement_type	*as;
	int				term_count;
{
  struct ps_exp_type	*psub;
  int			ineq_type;

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "\ncount_ass_bca = %1d, with term_count %1d at line %1d\n", 
    ++count_ass_bca, term_count, lineno 
  ); 
  pcform(as->u.act.lhs); 
  fprintf(RED_OUT, ":="); 
  pcform(as->u.act.rhs_exp); 
  fflush(RED_OUT); 
  
  fprintf(RED_OUT, "\n%1d, In assignment_bound_coeff_analyze(", 
    ++count_ass_bca
  ); 
  print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, ":="); 
  print_parse_subformula(as->u.act.rhs_exp, 
    FLAG_GENERAL_PROCESS_IDENTIFIER
  ); 
  fprintf(RED_OUT, "\n"); 
  #endif 
  
  ARITH_TERM = (struct parse_term_type *) 
    malloc(term_count * sizeof(struct parse_term_type));
  ARITH_TERM_COUNT = 1;
  ARITH_TERM[0].operand = as->u.act.lhs; 
  ARITH_TERM[0].coeff = PS_EXP_ONE;
  as->u.act.offset = rec_arith_bound_coeff_analyze(as->u.act.rhs_exp);
  as->st_status = 0; 
  if (as->u.act.offset == NULL) {
    as->u.act.offset = PS_EXP_ZERO;
  }
  else {
    as->u.act.offset = exp_static_evaluation(as->u.act.offset, 
      FLAG_NO_PI_STATIC_EVAL, NULL 
    );
  }
  as->u.act.term_count = term_count;
  as->u.act.term = ARITH_TERM;
}
  /* assignment_bound_coeff_analyze() */




int	address_conflict_approx(e1, e2) 
	struct ps_exp_type	*e1, *e2; 
{ 
  if (e1->type != e2->type) { 
    if (   e1 == PS_EXP_GLOBAL_IDENTIFIER 
	|| e2 == PS_EXP_GLOBAL_IDENTIFIER
	) 
      return(TYPE_FALSE); 
    else 
      return(TYPE_TRUE); 
  } 
  else switch (e1->type) { 
  case TYPE_CONSTANT: 
    if (e1->u.value == e2->u.value) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case TYPE_MACRO_CONSTANT: 
    if (   e1->u.inline_call.inline_declare
           ->u.inline_declare.declare_exp
           ->u.value 
        == e2->u.inline_call.inline_declare
           ->u.inline_declare.declare_exp
           ->u.value
        ) 
      return(TYPE_TRUE); 
    else 
      return(TYPE_FALSE); 
  case TYPE_LOCAL_IDENTIFIER: 
  case TYPE_PROCESS_COUNT: 
  case TYPE_POINTER: 
  case TYPE_QFD: 
    return(TYPE_TRUE); 
  default: 
    return(TYPE_TRUE); 
  } 
} 
  /* address_conflict_approx() */ 
  
  

struct ps_exp_type	AA_SUB;
int			AA_count = 0;   
  
int 				ass_ana_count = 0; 
struct parse_statement_type	*ass_ana; 

void	set_act_offset_flag(as, offset) 
  struct parse_statement_type	*as; 
  struct ps_exp_type		*offset; 
{ 
  if (   (as->u.act.lhs->var_status & FLAG_QUANTIFIED_SYNC)
      || (as->u.act.rhs_exp->var_status & FLAG_QUANTIFIED_SYNC) 
      ) 
    as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
  else 
    as->st_status = as->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC; 
 
  switch (offset->type) { 
  case TYPE_INTERVAL: 
    if (   offset->u.interval.lbound_exp->type == TYPE_CONSTANT
        && offset->u.interval.rbound_exp->type == TYPE_CONSTANT 
        ) { 
      if (offset->u.interval.lbound_exp->u.value 
          == offset->u.interval.rbound_exp->u.value
          ) { 
        as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
        | FLAG_ACTION_OFFSET_CONSTANT; 
      } 
      else if (   (offset->u.interval.lbound_exp->exp_status & FLAG_CONSTANT)
               && (offset->u.interval.rbound_exp->exp_status & FLAG_CONSTANT) 
               ) { 
        as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
        | FLAG_ACTION_OFFSET_INTERVAL_CONSTANT; 
      } 
    }
    else { 
      fprintf(RED_OUT, "Error: Illegal dynamic interval expression in an assignment:\n"); 
      pcform(offset); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    break; 
  default: 
    if (offset->type == TYPE_CONSTANT) 
      as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
      | FLAG_ACTION_OFFSET_CONSTANT; 
    else if (   (!(offset->var_status & FLAG_EXP_STATE_INSIDE))
             && (offset->exp_status & FLAG_LOCAL_IDENTIFIER)
             )  
      as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
      | FLAG_ACTION_OFFSET_PROCESS_CONSTANT; 
    else 
      as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
      | FLAG_ACTION_OFFSET_DISCRETE_POLYNOMIAL; 
    break; 
  } 
}
  /* set_act_offset_flag() */ 
  
  
  

int	assignment_analyze(as)
     struct parse_statement_type	*as;
{
  int 			term_count, ti, pi, 
			num, den, lb_num, lb_den, ub_num, ub_den, 
			lb, ub;
  struct ps_exp_type	*lhs, *newsub, *newrhs; 
  struct exp_shape_type	*es; 

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, " ## Entering assignment_analyze(): %1d\n", ++AA_count); 
  fprintf(RED_OUT, 
    " ** for valg: assignment analyze 1 (status %x)=(status %x)\n", 
    as->u.act.lhs->status, as->u.act.rhs_exp->status 
  ); 
  print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "="); 
  print_parse_subformula(as->u.act.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
  #endif 
  
  switch (as->u.act.lhs->type) { 
  case TYPE_REFERENCE: 
    as->op = ASSIGN_DISCRETE_POLYNOMIAL; 
    set_act_offset_flag(as, as->u.act.rhs_exp); 
    as->u.act.simple_coeff = NULL; 
    as->u.act.simple_offset = NULL; 
    as->u.act.term_count = 0; 
    as->u.act.term = NULL;
    as->u.act.offset = NULL;
    return(TYPE_TRUE);
    break; 
    
  case TYPE_DISCRETE: 
  case TYPE_POINTER: 
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    switch ((es = exp_shape_check(as->u.act.rhs_exp))->type) {
    case FLAG_EXP_STATIC: 
      as->op = ASSIGN_DISCRETE_CONSTANT; 
      break; 
    case FLAG_EXP_DISCRETE_CONSTANT: 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL:
    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
      as->op = ASSIGN_DISCRETE_POLYNOMIAL; 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, " ** for valg: assignment analyze 1\n"); 
      print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "="); 
      print_parse_subformula(as->u.act.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      #endif 
      break;
    default: 
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of dense variables\n"); 
      fprintf(RED_OUT, "              to a discrete LHS at line %1d\n", lineno); 
      print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "="); 
      print_parse_subformula(as->u.act.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    free(es); 
    set_act_offset_flag(as, as->u.act.rhs_exp); 
    as->u.act.simple_coeff = NULL; 
    as->u.act.simple_offset = NULL; 
    as->u.act.term_count = 0; 
    as->u.act.term = NULL;
    as->u.act.offset = NULL;
    return(TYPE_TRUE);
    break; 
  case TYPE_CLOCK: 
    switch ((es = exp_shape_check(as->u.act.rhs_exp))->type) { 
    case FLAG_EXP_STATIC: 
      as->op = ASSIGN_CLOCK_CONSTANT; 
      break; 
    case FLAG_EXP_DISCRETE_CONSTANT: 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL:
      as->op = ASSIGN_CLOCK_MIXED; 
      break; 
    case FLAG_EXP_CLOCK_CONSTANT: 
      as->op = ASSIGN_CLOCK_DIFFERENCE; 
      break; 
    case FLAG_EXP_CLOCK_MIXED: 
      as->op = ASSIGN_CLOCK_DIFFERENCE_MIXED; 
      break; 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_DENSE_CONSTANT:
    case FLAG_EXP_DENSE_LINEAR: 
      as->op = ASSIGN_HYBRID_EXP; 
      break; 
    case FLAG_EXP_DENSE_MIXED:
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a mixed dense \n"); 
      fprintf(RED_OUT, "              experssion to a clock LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
    case FLAG_EXP_DENSE_POLYNOMIAL:
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a polynomial dense \n"); 
      fprintf(RED_OUT, "              experssion to a clock LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nSyntax error: unexpected assignment of an unknown \n"
      ); 
      fprintf(RED_OUT, 
        "              experssion type %1d to a clock LHS at line %1d\n", 
        es->type, lineno
      ); 
      fflush(RED_OUT); 
      bk(0);       
    }
    free(es); 
    break;  
  case TYPE_DENSE: 
    switch ((es = exp_shape_check(as->u.act.rhs_exp))->type) { 
    case FLAG_EXP_STATIC: 
    case FLAG_EXP_CLOCK_CONSTANT: 
    case FLAG_EXP_CLOCK_DIFFERENCE: 
    case FLAG_EXP_DENSE_CONSTANT:
    case FLAG_EXP_DENSE_LINEAR: 
      as->op = ASSIGN_HYBRID_EXP; 
      break; 
    case FLAG_EXP_DISCRETE_LINEAR: 
    case FLAG_EXP_DISCRETE_POLYNOMIAL:
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a mixed discrete \n"); 
      fprintf(RED_OUT, "              experssion to a dense LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
      break; 
    case FLAG_EXP_CLOCK_MIXED: 
    case FLAG_EXP_CLOCK_DIFFERENCE_MIXED: 
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a mixed clock \n"); 
      fprintf(RED_OUT, "              experssion to a dense LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
    case FLAG_EXP_DENSE_MIXED:
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a mixed dense \n"); 
      fprintf(RED_OUT, "              experssion to a dense LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
    case FLAG_EXP_DENSE_POLYNOMIAL:
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of a polynomial dense \n"); 
      fprintf(RED_OUT, "              experssion to a dense LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
      break; 
    default: 
      fprintf(RED_OUT, "\nSyntax error: unexpected assignment of an unknown \n"); 
      fprintf(RED_OUT, "              experssion type to a dense LHS at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0);       
    }
    free(es); 
    break;  
  } 

  lhs = as->u.act.lhs;
  lhs = arith_distribute(lhs, -1);
  as->u.act.rhs_exp = arith_distribute(as->u.act.rhs_exp, 1); /* After this statement, negation on LHS
				  * has already been performed.  Thus don't
				  * count on the signs of the LHS before
				  * arith_bound_coeff_analyze().
				  */

  AA_SUB.type = ARITH_EQ;
  AA_SUB.var_status = 0; 
  AA_SUB.exp_status = 0; 
  AA_SUB.u.arith.lhs_exp = lhs;
  AA_SUB.u.arith.rhs_exp = as->u.act.rhs_exp;

  term_count = arith_term_count(&AA_SUB);
  if (term_count > MAX_TERM_COUNT)
    MAX_TERM_COUNT = term_count;

  assignment_bound_coeff_analyze(as, term_count);
  set_act_offset_flag(as, as->u.act.offset); 
  CLOCK_POS = NULL;
  CLOCK_NEG = NULL; 
  if (term_count > MAX_TERM_COUNT)
    MAX_TERM_COUNT = term_count;

  /* Use the term array to classify the assignment and thus the system */

  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, 
    " ** ass_ana_count=%1d ** for valg: assignment analyze 2:%x\n", 
    ++ass_ana_count, as
  ); 
  if (ass_ana_count == 3) 
    ass_ana = as; 
  print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "="); 
  print_parse_subformula(as->u.act.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  fprintf(RED_OUT, "\n"); 
  fprintf(RED_OUT, "\n ** for valg: %s.\n", as->u.act.term[0].operand->u.atom.var->name); 
//  fprintf(RED_OUT, " ** for valg: %1d.\n", as->u.act.term[0].operand->u.atom.indirect_count); 
  #endif 
  
/*
  if (as->u.act.term[0].operand->u.atom.indirect_count) {
    as->st_status = as->st_status | FLAG_ACTION_INDIRECTION;
  }
*/
  for (ti = 0; ti < term_count; ti++) {
/*
    if (as->u.act.term[ti].operand->u.atom.indirect_count) {
      as->st_status = as->st_status | FLAG_ACTION_INDIRECTION;
    }
*/
    if (   ti > 0
	&& as->u.act.term[ti].operand->u.atom.var == as->u.act.term[0].operand->u.atom.var
	&& (   /*
	       as->u.act.term[ti].operand->u.atom.indirect_count
	    || as->u.act.term[0].operand->u.atom.indirect_count 
	    || */
	       address_conflict_approx
	       (as->u.act.term[ti].operand->u.atom.exp_base_proc_index, 
		as->u.act.term[0].operand->u.atom.exp_base_proc_index
		) 
	    )
	)
      as->st_status = as->st_status | FLAG_ACTION_LHS_RECURSION;
      
    switch (as->u.act.term[ti].operand->type) {
    case TYPE_CLOCK:
      if (as->u.act.term[ti].coeff->type == TYPE_CONSTANT)
        if (as->u.act.term[ti].coeff->u.value == 1) {
          if (!CLOCK_POS)
	    CLOCK_POS = as->u.act.term[ti].operand;
        }
        else if (as->u.act.term[ti].coeff->u.value == -1) {
          if (!CLOCK_NEG)
	    CLOCK_NEG = as->u.act.term[ti].operand;
        }
      break;
    }
  }

  as->st_status = as->st_status | FLAG_ACTION_COEFF_CONSTANT;
  if (as->u.act.offset->type == TYPE_CONSTANT)
    as->st_status = (as->st_status & ~MASK_ACTION_OFFSET_TYPE) 
    | FLAG_ACTION_OFFSET_CONSTANT;
  /* starting from 1 which is the first argument of the RHS. */
  for (ti = 1; ti < as->u.act.term_count; ti++)
    if (as->u.act.term[ti].coeff->type != TYPE_CONSTANT) {
      as->st_status = as->st_status & ~FLAG_ACTION_COEFF_CONSTANT; 
      break;
    }

  switch (as->u.act.lhs->type) { 
  case TYPE_DENSE: 
    if (as->op == INCREMENT_BY_CONSTANT || as->op == DECREMENT_BY_CONSTANT) {
      fprintf(RED_OUT, "\nError: Increments on hybrid variables at line %1d.\n", lineno); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    else if ((as->st_status & MASK_ACTION_OFFSET_TYPE) 
             == FLAG_ACTION_OFFSET_CONSTANT
             ) {
      if (as->u.act.offset->u.value < 0) {
	if (ALL_CLOCK_TIMING_BOUND < -1*as->u.act.offset->u.value) {
	  ALL_CLOCK_TIMING_BOUND = -1*as->u.act.offset->u.value;
/*
	  fprintf(RED_OUT, "3: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
		  ALL_CLOCK_TIMING_BOUND
		  ); 
	  fflush(RED_OUT); 
*/
	}
      }
      else {
	if (ALL_CLOCK_TIMING_BOUND < as->u.act.offset->u.value) {
	  ALL_CLOCK_TIMING_BOUND = as->u.act.offset->u.value;
/*
	  fprintf(RED_OUT, "4: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
		  ALL_CLOCK_TIMING_BOUND
		  ); 
	  fflush(RED_OUT); 
*/
	}
      }
    }
    else {
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        int	lb, ub, flag; 
        float	flb, fub; 
        
	flag = get_integer_range(as->u.act.offset, pi, &lb, &ub, &flb, &fub);
        if (flag != FLAG_SPECIFIC_VALUE) { 
          fprintf(RED_OUT, 
            "\nERROR: Illegal quantification range type in act offset to dense lhs at line %1d in assignment_analyze().\n", 
            as->u.act.offset->lineno
          ); 
          pcform(as->u.act.offset); 
          fflush(RED_OUT); 
          bk(0); 
        } 
        if (lb < 0) 
          lb = -1 * lb; 
        if (ub < 0) 
          ub = -1 * ub; 
        if (lb > ub) 
          ub = lb; 
        
        if (ALL_CLOCK_TIMING_BOUND < ub) {
	  ALL_CLOCK_TIMING_BOUND = ub;
/*
	    fprintf(RED_OUT, "5: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
		    ALL_CLOCK_TIMING_BOUND
		    ); 
	    fflush(RED_OUT); 
*/
	}
      }
    }
    break; 
  case TYPE_CLOCK:
    if (   as->op == INCREMENT_BY_CONSTANT 
        || as->op == DECREMENT_BY_CONSTANT
        ) {
      fprintf(RED_OUT, "\nError: Increments on clock variables at line %1d.\n", lineno); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    else if ((as->st_status & MASK_ACTION_OFFSET_TYPE) 
             == FLAG_ACTION_OFFSET_CONSTANT
             ) {
      if (as->u.act.offset->u.value < 0) {
	if (ALL_CLOCK_TIMING_BOUND < -1*as->u.act.offset->u.value) {
	  ALL_CLOCK_TIMING_BOUND = -1*as->u.act.offset->u.value;
/*
	  fprintf(RED_OUT, "7: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
		  ALL_CLOCK_TIMING_BOUND
		  ); 
	  fflush(RED_OUT); 
*/
	}
      }
      else {
	if (ALL_CLOCK_TIMING_BOUND < as->u.act.offset->u.value) {
	  ALL_CLOCK_TIMING_BOUND = as->u.act.offset->u.value;
/*
	  fprintf(RED_OUT, "8: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
		  ALL_CLOCK_TIMING_BOUND
		  ); 
	  fflush(RED_OUT); 
*/
	}
      }
    }
    else {
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        int	lb, ub, flag; 
        float	flb, fub; 
        
	get_integer_range(as->u.act.offset, 1, &lb, &ub, &flb, &fub);
        if (flag != FLAG_SPECIFIC_VALUE) { 
          fprintf(RED_OUT, 
            "\nERROR: Illegal quantification range type in act offset to clock lhs at line %1d.\n", 
            as->u.act.offset->lineno 
          ); 
          pcform(as->u.act.offset); 
          fflush(RED_OUT); 
          bk(0); 
        } 
        if (lb < 0) 
          lb = -1 * lb; 
        if (ub < 0) 
          ub = -1 * ub; 
        if (lb > ub) 
          ub = lb; 
        
	if (ALL_CLOCK_TIMING_BOUND < ub) {
	  ALL_CLOCK_TIMING_BOUND = ub;
/*
	  fprintf(RED_OUT, "9: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
	    ALL_CLOCK_TIMING_BOUND
	  ); 
	  fflush(RED_OUT); 
*/
	}
      }
    }
    break;
  case TYPE_REFERENCE: 
  case TYPE_POINTER:
  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    if (as->op == INCREMENT_BY_CONSTANT || as->op == DECREMENT_BY_CONSTANT) 
      break; 
    if (as->u.act.term_count == 1) {
/*
      fprintf(RED_OUT, "ass_ana_count = %1d\n", ++ass_ana_count); 
      fflush(RED_OUT); 
*/
      for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
        int	lb, ub, flag; 
        float	flb, fub; 
        
        flag = get_integer_range(as->u.act.offset, pi, &lb, &ub, &flb, &fub); 
        if (flag != FLAG_SPECIFIC_VALUE) { 
          fprintf(RED_OUT, 
            "\nERROR: Illegal quantification range type in act offset to disc lhs at line %1d.\n", 
            as->u.act.offset->lineno 
          ); 
          pcform(as->u.act.offset); 
          fflush(RED_OUT); 
          bk(0); 
        } 
        if (as->u.act.lhs->u.atom.var->u.disc.ub < ub)
	  as->u.act.lhs->u.atom.var->u.disc.ub = ub; 
        if (as->u.act.lhs->u.atom.var->u.disc.lb > lb)
	  as->u.act.lhs->u.atom.var->u.disc.lb = lb; 
      }
    }
    break;
  default:
    fprintf(RED_OUT, "\nError: Unrecognized LHS type of assignment to constant at line %1d\n", lineno);
    fprintf(RED_OUT, "How to get this ? Maybe a dirty memory cell. \n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(14);
  }
  
  #ifdef RED_DEBUG_YACC_MODE
  fprintf(RED_OUT, "leaving assignment_analyze with dense lhs.\n"); 
  print_parse_statement_line(as); 
  fprintf(RED_OUT, "\nas->u.act.offset %x\n", as->u.act.offset); 
  pcform(as->u.act.offset); 
  fflush(RED_OUT); 
  #endif 
  
  return(TYPE_TRUE);
}
/* assignment_analyze() */




struct parse_xtion_type	*x5 = NULL; 

struct parse_xtion_type	*initialize_xtion(src, dst)
	struct parse_mode_type	*src, *dst; 
{ 
  struct parse_xtion_type	*px;
  struct parse_xtion_link_type	*pxl; 
  struct ps_bunit_type		*bunitptr; 

  px = (struct parse_xtion_type *) malloc(sizeof(struct parse_xtion_type));

  CURRENT_XTION = px;
  px->index = declare_xtion_count++;
  if (px->index == 5) 
    x5 = px; 
  px->next_parse_xtion = declare_xtion_list;
  declare_xtion_list = px;
    
  px->src_mode = src; 
  src->xtion_count++; 
  pxl = (struct parse_xtion_link_type *) malloc(sizeof(struct parse_xtion_link_type)); 
  pxl->parse_xtion = px; 
  pxl->next_parse_xtion_link = src->parse_xtion_list; 
  src->parse_xtion_list = pxl; 

  /*
  fprintf(RED_OUT, "\npx = %x:id=%1d\n", px, px->index);
  */
  px->sync_count = 0;
  px->sync_list = NULL; 

  px->statement = NULL; 
  
  px->trigger_exp = NULL; 
  px->src_mode_index = src->index; 
  px->dst_mode_index = dst->index; 
    
  if (sync_place_count < 1) 
    sync_place_count = 1; 

  return(px); 
}
  /* initialize_xtion() */ 
  




  





int	check_syntax_untimed(psub) 
  struct ps_exp_type	*psub; 
{ 
  struct ps_bunit_type	*b; 
  int 			result; 

  switch(psub->type){
  case TYPE_CONSTANT:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
  case TYPE_INTERVAL: 
  case TYPE_QFD:
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_DISCRETE:
  case TYPE_POINTER: 
    return (FLAG_INVARIANCE_TIME_CONVEX); 
    
  case TYPE_CLOCK:
  case TYPE_DENSE:
    return (TYPE_FALSE); 
    
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case ARITH_MODULO: 
  case ARITH_EQ: 
  case ARITH_LEQ: 
  case ARITH_LESS: 
  case ARITH_GEQ: 
  case ARITH_GREATER: 
    return ( 
      check_syntax_untimed(psub->u.arith.lhs_exp) 
    & check_syntax_untimed(psub->u.arith.rhs_exp) 
    );  
    break; 

  case ARITH_NEQ: 
    return (
      check_syntax_untimed(psub->u.arith.lhs_exp) 
    & check_syntax_untimed(psub->u.arith.rhs_exp)
    ); 
    break; 
    
  case ARITH_CONDITIONAL: 
    return ( 
      check_syntax_untimed(psub->u.arith_cond.cond) 
    & check_syntax_untimed(psub->u.arith_cond.if_exp) 
    & check_syntax_untimed(psub->u.arith_cond.else_exp) 
    );  
    break; 
    
  case EQ: 
  case NEQ: 
  case LEQ: 
  case LESS: 
  case GEQ: 
  case GREATER: 
    return(TYPE_FALSE); 
    break; 

  case TYPE_INLINE_CALL: 
    return (check_syntax_untimed(psub->u.inline_call.instantiated_exp));
    break;   
  
  case IMPLY: 
    return(
      check_syntax_untimed(psub->u.bexp.blist->subexp) 
    & check_syntax_untimed(psub->u.bexp.blist->bnext->subexp)
    ); 
    break; 
    
  case NOT: 
    return(check_syntax_untimed(psub->u.bexp.blist->subexp)); 
    break; 

  case AND: 
  case OR: 
    result = FLAG_INVARIANCE_TIME_CONVEX; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      result = result & check_syntax_untimed(b->subexp); 
      if (!result) 
        return(result); 
    } 
    return(result); 
    break; 

  case FORALL: 
  case EXISTS: 
    return(check_syntax_untimed(psub->u.qexp.child)); 
    break; 
    
  default:
    fprintf(RED_OUT, "\nRedgram : Huh ? (parse) \n");
    bk(); 
  }
}
  /* check_syntax_untimed() */ 
  
  
  
int	check_syntax_convexity(psub) 
  struct ps_exp_type	*psub; 
{ 
  struct ps_bunit_type	*b; 
  int 			result; 

  switch(psub->type){
  case TYPE_CONSTANT:
  case TYPE_LOCAL_IDENTIFIER:
  case TYPE_NULL:
  case TYPE_FALSE:
  case TYPE_TRUE:
  case TYPE_PROCESS_COUNT: 
  case TYPE_MODE_INDEX: 
  case TYPE_REFERENCE: 
  case TYPE_DEREFERENCE: 
  case BIT_NOT: 
  case TYPE_INTERVAL: 
  case TYPE_QFD:
  case TYPE_QSYNC_HOLDER: 
  case TYPE_MACRO_CONSTANT: 
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_DISCRETE:
  case TYPE_POINTER: 
    return (FLAG_INVARIANCE_TIME_CONVEX); 
    
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 
    
  case ARITH_ADD: 
  case ARITH_MINUS: 
  case ARITH_MULTIPLY: 
  case ARITH_DIVIDE: 
  case ARITH_MODULO: 
  case ARITH_EQ: 
  case ARITH_LEQ: 
  case ARITH_LESS: 
  case ARITH_GEQ: 
  case ARITH_GREATER: 
    return ( 
      check_syntax_convexity(psub->u.arith.lhs_exp) 
    & check_syntax_convexity(psub->u.arith.rhs_exp) 
    );  
    break; 

  case ARITH_NEQ: 
    return (
      check_syntax_untimed(psub->u.arith.lhs_exp) 
    & check_syntax_untimed(psub->u.arith.rhs_exp)
    ); 
    break; 
    
  case ARITH_CONDITIONAL: 
    return ( 
      check_syntax_convexity(psub->u.arith_cond.cond) 
    & check_syntax_convexity(psub->u.arith_cond.if_exp) 
    & check_syntax_convexity(psub->u.arith_cond.else_exp) 
    );  
    break; 
  case EQ: 
  case LEQ: 
  case LESS: 
  case GEQ: 
  case GREATER: 
    return(FLAG_INVARIANCE_TIME_CONVEX); 
    break; 
      
  case NEQ: 
    return(FLAG_TIME_MODE_SOME_TCONCAVE); 
    break; 

  case TYPE_INLINE_CALL: 
    if (psub->u.inline_call.instantiated_exp)
      return (check_syntax_convexity(psub->u.inline_call.instantiated_exp));
    else 
      return (check_syntax_convexity(
        psub->u.inline_call.inline_declare->u.inline_declare.declare_exp
      ) );
    break;   
  
  case IMPLY: 
    return(
      check_syntax_untimed(psub->u.bexp.blist->subexp) 
    & check_syntax_untimed(psub->u.bexp.blist->bnext->subexp)
    ); 
    break; 
    
  case NOT: 
    return(check_syntax_untimed(psub->u.bexp.blist->subexp)); 
    break; 

  case AND: 
    result = FLAG_INVARIANCE_TIME_CONVEX; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      result = result & check_syntax_convexity(b->subexp); 
      if (!result) 
        return(result); 
    } 
    return(result); 
    break; 

  case OR: 
    result = FLAG_INVARIANCE_TIME_CONVEX; 
    for (b = psub->u.bexp.blist; b; b = b->bnext) { 
      result = result & check_syntax_untimed(b->subexp); 
      if (!result) 
        return(result); 
    } 
    return(result); 
    break; 

  case FORALL: 
    return(check_syntax_convexity(psub->u.qexp.child)); 
    break; 
    
  case EXISTS: 
    return(check_syntax_untimed(psub->u.qexp.child)); 
    break; 
    
  default:
    fprintf(RED_OUT, "\nHuh ? (parse 2) \n");
    bk(); 
  }
}
  /* check_syntax_convexity() */ 
  
  
  
  
struct parse_mode_type	*add_mode(mstart, mode_name) 
  int			mstart; 
  char			*mode_name; 
{
  struct parse_mode_type	*pm; 
  struct ps_bunit_type		*bunitptr; 
  struct ps_exp_type		*mode_predicate;
/*
  char				*mname; 
*/
  int				len, i; 

  check_naming_restrictions(mode_name); 

  if (name_duplicate(mode_name, &name_check_holder)) { 
    fprintf(RED_OUT, "\nError in add mode: variable name duplicate %s at line %1d.\n", 
	    mode_name, lineno
	    );
    bk(); 
  }
        
  len = strlen(mode_name); 
  pm = (struct parse_mode_type *) malloc(sizeof(struct parse_mode_type));

  /*
  fprintf(RED_OUT, "\npm = %x\n", pm);
  */
  pm->status = mstart;
 
  pm->name = mode_name;
  pm->index = MODE_COUNT++;
  CURRENT_MODE = pm;
  pm->xtion_count = 0;
  pm->parse_xtion_list = NULL;
  pm->rate_spec_count = 0;
  pm->parse_rate_spec_list = NULL;
  pm->invariance_exp = NULL; 
    
  pm->next_parse_mode = declare_mode_list;
  declare_mode_list = pm;
  return(pm); 
}
  /* add_mode() */ 



void	add_mode_invariance(pm, invariance) 
  struct parse_mode_type	*pm; 
  struct ps_exp_type		*invariance; 
{
  struct ps_bunit_type		*bunitptr; 
  struct ps_exp_type		*mode_predicate;
/*
  char				*mname; 
*/
  int				len, i; 

  if (  (  invariance->var_status 
         & (FLAG_SYNCHRONIZER | FLAG_VAR_PRIMED)
         )
      ||(  invariance->exp_status 
         & (FLAG_EXP_MODAL_INSIDE | FLAG_RESET_INSIDE)
         )
      ) { 
    int	count_bugs = 0; 
    
    fprintf(RED_OUT, "\nError: Illegal"); 
    if (invariance->exp_status & FLAG_RESET_INSIDE) { 
      fprintf(RED_OUT, " reset"); 
      count_bugs++; 
    }
    if (invariance->var_status & FLAG_SYNCHRONIZER) {
      if (count_bugs) 
        fprintf(RED_OUT, ", event"); 
      else 
        fprintf(RED_OUT, " event");  
      count_bugs++; 
    }
    if (invariance->exp_status & FLAG_EXP_MODAL_INSIDE) {
      if (count_bugs) 
        fprintf(RED_OUT, ", modal"); 
      else 
        fprintf(RED_OUT, " modal");  
      count_bugs++; 
    }
    if (invariance->var_status & FLAG_VAR_PRIMED) {
      if (count_bugs) 
        fprintf(RED_OUT, ", primed"); 
      else 
        fprintf(RED_OUT, " primed");  
      count_bugs++; 
    }
    if (count_bugs > 1) 
      fprintf(RED_OUT, " opreators\n"); 
    else 
      fprintf(RED_OUT, " operator\n"); 
    fprintf(RED_OUT, 
      "       in the invariance condition for mode %s at line %1d.\n", 
      pm->name, lineno
    ); 
    fflush(RED_OUT); 
    exit(0); 
  }
 
  if (check_syntax_convexity(invariance)) { 
    pm->status = pm->status | FLAG_INVARIANCE_TIME_CONVEX; 
  } 
  else if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) 
           == FLAG_SYSTEM_HYBRID
           ) {
    fprintf(RED_OUT, "\nError: time-concavities mode %s invariance \n", 
      pm->name 
    ); 
    fprintf(RED_OUT, "       in linear-hybrid automatas at line %1d.\n", 
      lineno
    ); 
    exit(0);   
  }
  else {  
    pm->status = pm->status & ~FLAG_INVARIANCE_TIME_CONVEX; 
    GSTATUS[INDEX_TIME_MODE_SHAPES] 
    = GSTATUS[INDEX_TIME_MODE_SHAPES] & ~FLAG_TIME_MODE_ALL_TCONVEX;  
  } 

  pm->orig_invariance_exp = invariance; 
  
  mode_predicate = ps_exp_alloc(ARITH_EQ);
    
  mode_predicate->u.arith.rhs_exp = ps_exp_alloc(TYPE_CONSTANT);
  mode_predicate->u.arith.rhs_exp->var_status = 0; 
  mode_predicate->u.arith.rhs_exp->exp_status = FLAG_CONSTANT; 
  mode_predicate->u.arith.rhs_exp->u.value = CURRENT_MODE->index;
  mode_predicate->u.arith.rhs_exp = ps_exp_share(
    mode_predicate->u.arith.rhs_exp
  ); 
  mode_predicate->u.arith.lhs_exp = ps_exp_alloc(TYPE_DISCRETE); 
  mode_predicate->u.arith.lhs_exp->var_status = var_mode->status; 
  mode_predicate->u.arith.lhs_exp->exp_status = FLAG_LOCAL_IDENTIFIER; 
  mode_predicate->u.arith.lhs_exp->u.atom.var = var_mode;
  mode_predicate->u.arith.lhs_exp->u.atom.exp_base_proc_index 
  = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER); 
  mode_predicate->u.arith.lhs_exp->u.atom.var_index = var_mode->index;
  mode_predicate->u.arith.lhs_exp->u.atom.var_name = var_mode->name;
//  mode_predicate->u.arith.lhs_exp->u.atom.indirect_count = 0;
//  mode_predicate->u.arith.lhs_exp->u.atom.indirect_exp = NULL;
  mode_predicate->u.arith.lhs_exp = ps_exp_share(
    mode_predicate->u.arith.lhs_exp
  ); 

  /* pm->invariance_exp = */ 
  mode_predicate->var_status 
  = var_mode->status 
  | mode_predicate->u.arith.lhs_exp->var_status 
  | mode_predicate->u.arith.rhs_exp->var_status; 
  mode_predicate->exp_status 
  = mode_predicate->u.arith.lhs_exp->exp_status 
  | mode_predicate->u.arith.rhs_exp->exp_status; 
  mode_predicate = ps_exp_share(mode_predicate); 
  if (invariance->type == TYPE_TRUE) { 
    pm->invariance_exp = mode_predicate;
  }
  else { 
    /* Construct the mode invariance conjunction. */
    bunitptr = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*
    fprintf(RED_OUT, "bunitptr = %x in mode %1d for var_mode\n", bunitptr, pm->index);
    */
    bunitptr->subexp = invariance;

    pm->invariance_exp = ps_exp_alloc(AND);
    pm->invariance_exp->u.bexp.len = 2;
    pm->invariance_exp->u.bexp.blist = (struct ps_bunit_type *)
      malloc(sizeof(struct ps_bunit_type));
    /*
    fprintf(RED_OUT, "\npm->invariance_exp->u.bexp.blist = %x\n", pm->invariance_exp->u.bexp.blist);
    */
    bunitptr->bnext = NULL;
    pm->invariance_exp->u.bexp.blist->bnext = bunitptr;

    pm->invariance_exp->u.bexp.blist->subexp = mode_predicate;
    pm->invariance_exp = ps_exp_share(pm->invariance_exp); 
  }
  /*
    fprintf(RED_OUT, "Invariance Condition of mode %s\n", pm->name);
    pcform(pm->invariance_exp); 
    print_parse_subformula_structure(pm->invariance_exp, 0);
    fprintf(RED_OUT, "yacc literal 2 : TRIGGERING MODE INEQUALITY\n");
   */
}
  /* add_mode_invariance() */ 




    
struct parse_statement_type	*add_assignment(px, lhs_var, value) 
	struct parse_xtion_type		*px; 
	struct parse_variable_type	*lhs_var; 
	int				value; 
{
  struct parse_statement_type		*pa, *nst; 
  struct parse_statement_link_type	*psl, *nsl; 
  
  pa = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
  pa->u.act.lhs = ps_exp_alloc(lhs_var->type); 
  pa->u.act.lhs->u.atom.var = lhs_var; 
  pa->u.act.lhs->var_status = lhs_var->status; 
  pa->u.act.lhs->exp_status = 0; 
  pa->u.act.lhs->u.atom.var_name = lhs_var->name; 
//  pa->u.act.lhs->u.atom.indirect_count = 0; 
//  pa->u.act.lhs->u.atom.indirect_exp = NULL; 
  
  if (lhs_var->status & FLAG_LOCAL_VARIABLE) 
    pa->u.act.lhs->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER; 
  else 
    pa->u.act.lhs->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
  pa->u.act.lhs->u.atom.exp_base_proc_index 
  = ps_exp_share(pa->u.act.lhs->u.atom.exp_base_proc_index); 
  pa->u.act.lhs = ps_exp_share(pa->u.act.lhs); 
  
  pa->u.act.rhs_exp = ps_exp_alloc(TYPE_CONSTANT); 
  pa->u.act.rhs_exp->u.value = value; 
  pa->u.act.rhs_exp->var_status = 0; 
  pa->u.act.rhs_exp->exp_status = FLAG_CONSTANT; 
  pa->u.act.rhs_exp = ps_exp_share(pa->u.act.rhs_exp); 
  
  compose_assignment_status(pa); 
  
  if (px->statement->type == ST_SEQ) { 
    for (psl = px->statement->u.seq.statement_list; 
	 psl->next_parse_statement_link; 
	 psl = psl->next_parse_statement_link
	 ) ; 
	 
    nsl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
    nsl->statement = pa; 
    psl->next_parse_statement_link = nsl; 
    nsl->next_parse_statement_link = NULL; 
    px->statement->u.seq.statement_count++;  
  } 
  else { 
    nst = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    nst->op = ST_SEQ; 
    nst->type = 0; 
    nst->st_status = px->statement->st_status | pa->st_status; 
    nst->u.seq.statement_count = 2; 
    nsl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
    nsl->statement = pa; 
    nst->u.seq.statement_list = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
    nst->u.seq.statement_list->statement = px->statement; 
    nst->u.seq.statement_list->next_parse_statement_link = nsl; 
    nsl->next_parse_statement_link = NULL; 
    px->statement = nst; 
  }  
  return(pa); 
}
  /* add_assignment() */ 
  
  
  




struct parse_statement_type 	*parse_statement_copy(pst)
     struct parse_statement_type	*pst;
{ 
  struct parse_statement_link_type	*psl, dummy_psl, *npsl, *tail; 
  struct parse_statement_type		*npst; 

  if (!pst) 
    return (NULL); 
  
  npst = (struct parse_statement_type *) 
    malloc(sizeof(struct parse_statement_type)); 
  *npst = *pst; 

  switch (pst->op) { 
  case UNCHANGED: 
    return(npst); 
    break; 
  case ST_IF: 
    npst->u.branch.cond = pst->u.branch.cond; 
    npst->u.branch.if_statement 
    = parse_statement_copy(pst->u.branch.if_statement); 
    if (pst->st_status & FLAG_STATEMENT_ELSE) 
      npst->u.branch.else_statement 
      = parse_statement_copy(pst->u.branch.else_statement); 
    return(npst); 
    break; 
  case ST_WHILE: 
    npst->u.loop.cond = pst->u.loop.cond; 
    npst->u.loop.statement = parse_statement_copy(pst->u.loop.statement); 
    return(npst); 
    break; 
  case ST_SEQ: 
    tail = &dummy_psl; 
    for (psl = pst->u.seq.statement_list; psl; psl = psl->next_parse_statement_link) { 
      npsl = (struct parse_statement_link_type *) 
        malloc(sizeof(struct parse_statement_link_type)); 
      tail->next_parse_statement_link = npsl; 
      npsl->statement = parse_statement_copy(psl->statement);  
    } 
    tail->next_parse_statement_link = NULL; 
    npst->u.seq.statement_list = dummy_psl.next_parse_statement_link; 
    return(npst); 
    break; 
  default: 
    npst->u.act.lhs = pst->u.act.lhs; 
    npst->u.act.rhs_exp = pst->u.act.rhs_exp; 
    return(npst); 
    break; 	
  } 
}
  /* parse_statement_copy() */ 



  
  




int	count_st_se = 0; 

void 	statement_static_evaluation(px, pst)
     struct parse_xtion_type		*px; 
     struct parse_statement_type	*pst;
{ 
  struct parse_statement_link_type	*psl; 
  int					local_count; 
  struct parse_mode_type		*pm; 

  if (!pst) 
    return; 

  local_count = ++count_st_se; 
  if (local_count == -1) { 
    fprintf(RED_OUT, "\nCaught!\n"); 
  }   
  switch (pst->op) { 
  case UNCHANGED: 
    break; 
  case ST_IF: 
    pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;
    pst->u.branch.cond = exp_static_evaluation(pst->u.branch.cond, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    if (pst->u.branch.cond->var_status & FLAG_QUANTIFIED_SYNC)
      pst->st_status = pst->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    statement_static_evaluation(px, pst->u.branch.if_statement); 
    pst->st_status = pst->st_status 
    | (pst->u.branch.if_statement->st_status & FLAG_ACTION_QUANTIFIED_SYNC); 
    if (pst->st_status & FLAG_STATEMENT_ELSE) {
      statement_static_evaluation(px, pst->u.branch.else_statement); 
      pst->st_status = pst->st_status 
      | (pst->u.branch.else_statement->st_status & FLAG_ACTION_QUANTIFIED_SYNC); 
    }
    break; 
  case ST_WHILE: 
    pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;
    pst->u.loop.cond = exp_static_evaluation(pst->u.loop.cond, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    if (pst->u.loop.cond->var_status & FLAG_QUANTIFIED_SYNC)
      pst->st_status = pst->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    statement_static_evaluation(px, pst->u.loop.statement); 
    pst->st_status = pst->st_status 
    | (pst->u.loop.statement->st_status & FLAG_ACTION_QUANTIFIED_SYNC); 
    break; 
  case ST_SEQ: 
    pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;
    for (psl = pst->u.seq.statement_list; psl; psl = psl->next_parse_statement_link) { 
      statement_static_evaluation(px, psl->statement);  
      pst->st_status = pst->st_status 
      | (psl->statement->st_status & FLAG_ACTION_QUANTIFIED_SYNC); 
    } 
    break; 

  case ST_CALL: 
    pm = search_parse_mode(pst->u.call.call_mode_name); 
    if (pm == NULL) { 
      fprintf(RED_OUT, 
        "\nError: Undefined call mode name %s at line %1d.\n", 
        pst->u.call.call_mode_name, lineno
      ); 
      bk(0); 
    } 
    px->dst_mode_index 
    = pst->u.call.call_mode_index = pm->index; 
    if (pst->u.call.ret_mode_name) { 
      pm = search_parse_mode(pst->u.call.ret_mode_name); 
      if (pm == NULL) { 
        fprintf(RED_OUT, 
          "\nError: Undefined return mode name %s at line %1d.\n", 
          pst->u.call.ret_mode_name, lineno
        ); 
        bk(0); 
      } 
      pst->u.call.ret_mode_index = pm->index; 
    } 
    break; 
    
  case ST_RETURN: 
    px->dst_mode_index = MODE_DYNAMIC; 
    break; 

  case ST_GUARD: 
    pst->u.guard.cond = exp_static_evaluation(pst->u.guard.cond, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    break; 
  case ST_ERASE: 
    pst->u.erase.var = exp_static_evaluation(pst->u.erase.var, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    if (pst->u.erase.var->u.atom.var == var_mode) { 
      if (pst->u.erase.var->u.atom.exp_base_proc_index->type 
          != TYPE_LOCAL_IDENTIFIER
          ) {
        px->dst_mode_index = MODE_DYNAMIC; 
      }
      else {
        px->dst_mode_index = MODE_NO_SPEC; 
    } }
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    pst->u.act.lhs = exp_static_evaluation(pst->u.act.lhs, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    pst->u.act.offset = pst->u.act.rhs_exp 
    = exp_static_evaluation(pst->u.act.offset, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    set_act_offset_flag(pst, pst->u.act.offset); 
    if (   (pst->u.act.lhs->var_status & FLAG_QUANTIFIED_SYNC)
        || (pst->u.act.offset->var_status & FLAG_QUANTIFIED_SYNC) 
        ) { 
      pst->st_status = pst->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    } 
    else 
      pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;

    break; 

  case ASSIGN_DISCRETE_CONSTANT: 
    if (   pst->u.act.lhs->type == TYPE_REFERENCE 
        || pst->u.act.lhs->u.atom.var != var_mode
        ) { 
      pst->u.act.lhs = exp_static_evaluation(pst->u.act.lhs, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      pst->u.act.rhs_exp = exp_static_evaluation(pst->u.act.rhs_exp, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      if (pst->u.act.rhs_exp->type != TYPE_INTERVAL) 
        assignment_analyze(pst); 
    }
    else { 
      pst->u.act.lhs = exp_static_evaluation(pst->u.act.lhs, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      pst->u.act.rhs_exp = exp_static_evaluation(pst->u.act.rhs_exp, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      if (   pst->u.act.lhs->u.atom.exp_base_proc_index->type 
             != TYPE_LOCAL_IDENTIFIER
          || pst->u.act.rhs_exp->type != TYPE_CONSTANT
          || !valid_mode_index(pst->u.act.rhs_exp->u.value)
          ) {
        px->dst_mode_index = MODE_DYNAMIC; 
        if (pst->u.act.rhs_exp->type != TYPE_INTERVAL) 
          assignment_analyze(pst); 
      }
      else {
      /* This assignment is generated from a GOTO statement that assigns to the local MODE.  */ 
/*
        fprintf(RED_OUT, "filling XTION %1d:%x: MODE index from name %s.\n", 
	        px->index, px, pst->u.act.lhs->u.atom.var_name
	        ); 
        fflush(RED_OUT); 
*/ 
        px->dst_mode_index 
        = pst->u.act.rhs_exp->u.value; 
        pst->u.act.rhs_exp->exp_status 
        = pst->u.act.rhs_exp->exp_status | FLAG_CONSTANT; 
// QQQQQQQQQQQQQQ
//        pst->var_status = exp_var_status_parse_variable(var_mode); 
        pst->st_status = 0; 
        pst->u.act.offset = pst->u.act.rhs_exp; 
      }
    }    
    if (   (pst->u.act.lhs->var_status & FLAG_QUANTIFIED_SYNC)
        || (pst->u.act.rhs_exp->var_status & FLAG_QUANTIFIED_SYNC) 
        ) { 
      pst->st_status = pst->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    } 
    else 
      pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;

    break; 

  default: 
    if (   pst->u.act.lhs->type != TYPE_REFERENCE 
        && pst->u.act.lhs->u.atom.var == var_mode 
        ) { 
      px->dst_mode_index = MODE_DYNAMIC; 
    } 
    pst->u.act.lhs = exp_static_evaluation(pst->u.act.lhs, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    pst->u.act.rhs_exp = exp_static_evaluation(pst->u.act.rhs_exp, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    if (pst->u.act.rhs_exp->type != TYPE_INTERVAL) 
      assignment_analyze(pst); 
    if (   (pst->u.act.lhs->var_status & FLAG_QUANTIFIED_SYNC) 
        || (pst->u.act.rhs_exp->var_status & FLAG_QUANTIFIED_SYNC) 
        ) { 
      pst->st_status = pst->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    } 
    else 
      pst->st_status = pst->st_status & ~FLAG_ACTION_QUANTIFIED_SYNC;

    break; 
  } 
}
  /* statement_static_evaluation() */ 



  
int	count_st_in_a = 0; 

  
struct parse_statement_type 	*statement_ineq_analyze(pst)
     struct parse_statement_type	*pst;
{ 
  struct parse_statement_link_type	*psl; 
  int					i, local_count; 

  if (!pst) 
    return(NULL); 

  local_count = ++count_st_in_a; 
  if (local_count == -1) { 
    fprintf(RED_OUT, "\nCaught!\n"); 
  } 
  switch (pst->op) { 
  case UNCHANGED: 
    break; 
  case ST_IF: 
    pst->u.branch.cond = rec_ineq_analyze(pst->u.branch.cond); 
    pst->u.branch.if_statement 
    = statement_ineq_analyze(pst->u.branch.if_statement); 
    if (pst->st_status & FLAG_STATEMENT_ELSE) 
      pst->u.branch.else_statement 
      = statement_ineq_analyze(pst->u.branch.else_statement); 
    break; 
  case ST_WHILE: 
    pst->u.loop.cond = rec_ineq_analyze(pst->u.loop.cond); 
    pst->u.loop.statement = statement_ineq_analyze(pst->u.loop.statement); 
    break; 
  case ST_SEQ: 
    for (psl = pst->u.seq.statement_list; psl; psl = psl->next_parse_statement_link) { 
      psl->statement = statement_ineq_analyze(psl->statement);  
    } 
    break; 

  case ST_CALL: 
  case ST_RETURN: 
    break; 
    
  case ST_GUARD: 
    pst->u.guard.cond = rec_ineq_analyze(pst->u.guard.cond); 
    break; 
  case ST_ERASE: 
    pst->u.erase.var->u.atom.exp_base_proc_index
    = rec_ineq_analyze(pst->u.erase.var->u.atom.exp_base_proc_index); 
    break; 
  case INCREMENT_BY_CONSTANT: 
  case DECREMENT_BY_CONSTANT: 
    if (pst->u.act.lhs->type == TYPE_REFERENCE) { 
      pst->u.act.lhs->u.exp = rec_ineq_analyze(pst->u.act.lhs->u.exp); 
    } 
    else { 
      pst->u.act.lhs->u.atom.exp_base_proc_index
      = rec_ineq_analyze(pst->u.act.lhs->u.atom.exp_base_proc_index); 
/*
      for (i = 0; i < pst->u.act.lhs->u.atom.indirect_count; i++) { 
        pst->u.act.lhs->u.atom.indirect_exp[i]
        = rec_ineq_analyze(pst->u.act.lhs->u.atom.indirect_exp[i]); 
      } 
*/
    }
    break; 

  default: 
    if (pst->u.act.lhs->type == TYPE_REFERENCE) { 
      pst->u.act.lhs->u.exp = rec_ineq_analyze(pst->u.act.lhs->u.exp); 
    }
    else {
      pst->u.act.lhs->u.atom.exp_base_proc_index 
      = rec_ineq_analyze(pst->u.act.lhs->u.atom.exp_base_proc_index); 
/*
      for (i = 0; i < pst->u.act.lhs->u.atom.indirect_count; i++) { 
        pst->u.act.lhs->u.atom.indirect_exp[i]
        = rec_ineq_analyze(pst->u.act.lhs->u.atom.indirect_exp[i]); 
      } 
*/
    }
    pst->u.act.rhs_exp = rec_ineq_analyze(pst->u.act.rhs_exp); 
    break; 
  } 
  return(pst); 
}
  /* statement_ineq_analyze() */ 



 




void	compose_additive_status(op, e1, e2, vsptr, esptr) 
	int	op; 
	struct ps_exp_type	*e1, *e2; 
	int			*vsptr, *esptr; 
{ 
  *vsptr = e1->var_status | e2->var_status; 
  *esptr = (e1->exp_status | e2->exp_status) & ~FLAG_CONSTANT; 
  if (*esptr & FLAG_HYBRID)
    return; 
    
  /* Now it is for sure that there is no dense variables. */
  if ((e1->var_status | e2->var_status) & FLAG_DENSE) {
    *esptr = *esptr | FLAG_HYBRID; 
    return; 
  }
  
  /* It may happen there are no clocks at all. */ 
  if (!((*vsptr) & FLAG_CLOCK))
    return; 
  
  /* check the case where only one side has clocks. */ 
  if ((e1->var_status & FLAG_CLOCK) && !(e2->var_status & FLAG_CLOCK)) 
    return; 
    
  if ((e2->var_status & FLAG_CLOCK) && !(e1->var_status & FLAG_CLOCK)) {
    switch (op) { 
    case ARITH_MINUS: 
      if (e2->exp_status & FLAG_ONE_POS_CLOCK) {
        if (!(e2->exp_status & FLAG_ONE_NEG_CLOCK))  
          *esptr = ((*esptr) & ~FLAG_ONE_POS_CLOCK) | FLAG_ONE_NEG_CLOCK; 
      } 
      else if (e2->exp_status & FLAG_ONE_NEG_CLOCK) { 
        *esptr = (e2->exp_status & ~FLAG_ONE_NEG_CLOCK) | FLAG_ONE_POS_CLOCK; 
      } 
      break; 
    } 
    return; 
  }

  /* check the case where there are three or more clocks. */
  if (   (e1->var_status & FLAG_CLOCK) 
      && (e1->exp_status & FLAG_ONE_POS_CLOCK)
      && (e1->exp_status & FLAG_ONE_NEG_CLOCK)
      ) {
    /* since e2 must have clock in this stage, it has three or more clocks. */ 
    *esptr = (*esptr) | FLAG_HYBRID; 
    return; 
  } 
  if (   (e2->var_status & FLAG_CLOCK) 
      && (e2->exp_status & FLAG_ONE_POS_CLOCK)
      && (e2->exp_status & FLAG_ONE_NEG_CLOCK)
      ) {
    /* since e1 must have clock in this stage, it has three or more clocks. */ 
    *esptr = (*esptr) | FLAG_HYBRID; 
    return; 
  } 
  /* Now check the case where each side has exactly one clock. */ 
  if (   (e1->var_status & FLAG_CLOCK) 
      && (e1->exp_status & FLAG_ONE_POS_CLOCK)
      ) {
    if (   (e2->var_status & FLAG_CLOCK) 
        && (e2->exp_status & FLAG_ONE_NEG_CLOCK)
        ) {
      if (op == ARITH_MINUS) {
        *esptr = (*esptr) | FLAG_HYBRID; 
        return; 
      }
    }
    else if (   (e2->var_status & FLAG_CLOCK) 
             && (e2->exp_status & FLAG_ONE_POS_CLOCK)
             ) {
      if (op == ARITH_ADD) {
        *esptr = (*esptr) | FLAG_HYBRID; 
        return; 
    } }
  }
  else if (   (e1->var_status & FLAG_CLOCK) 
           && (e1->exp_status & FLAG_ONE_NEG_CLOCK)
           ) {
    if (   (e2->var_status & FLAG_CLOCK) 
        && (e2->exp_status & FLAG_ONE_POS_CLOCK)
        ) {
      if (op == ARITH_MINUS) { 
        *esptr = (*esptr) | FLAG_HYBRID; 
        return; 
    } } 
    else if (   (e2->var_status & FLAG_CLOCK) 
             && (e2->exp_status & FLAG_ONE_NEG_CLOCK)
             ) {
      if (op == ARITH_ADD) { 
        *esptr = (*esptr) | FLAG_HYBRID; 
        return; 
    } }
  }
  return; 
}
  /* compose_additive_status() */ 



void	compose_mult_status(op, e1, e2, vsptr, esptr) 
	int			op; 
	struct ps_exp_type	*e1, *e2; 
	int			*vsptr, *esptr; 
{ 
  if (   (e1->var_status & (FLAG_DENSE | FLAG_CLOCK)) 
      && (e2->var_status & (FLAG_DENSE | FLAG_CLOCK))
      ) {
    fprintf(RED_OUT, "Error: dense variables multiplication/division used at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  }
  *vsptr = e1->var_status | e2->var_status; 
  *esptr = (e1->exp_status | e2->exp_status) & ~FLAG_CONSTANT; 
  if ((*esptr) & FLAG_HYBRID)
    return; 

  /* Now it is for sure that there is no dense variables. */
  if (   (e1->var_status & FLAG_CLOCK) 
      && (e2->var_status & (FLAG_DISCRETE | FLAG_POINTER))
      ) {
    *esptr = (*esptr) | FLAG_HYBRID; 
    return; 
  } 
      
  if (   (e2->var_status & FLAG_CLOCK) 
      && (e1->var_status & (FLAG_DISCRETE | FLAG_POINTER))
      ) {
    *esptr = (*esptr) | FLAG_HYBRID; 
    return; 
  }
  /* From this point on, we assume there are only clock variables */ 
  if (!((*vsptr) & FLAG_CLOCK)) 
    return; 
  
  /* To this point, we know that only one clock exists. */ 
  
  /* It could happen that a big coefficient of clock happens. */ 
  if (   e1->type == TYPE_CONSTANT 
      && (e1->u.value > 1 || e1->u.value < -1) 
      && (e2->var_status & FLAG_CLOCK) 
      && (e2->exp_status & (FLAG_ONE_POS_CLOCK | FLAG_ONE_NEG_CLOCK)) 
      ) { 
    *esptr 
    = ((*esptr) | FLAG_HYBRID) 
    & ~FLAG_ONE_POS_CLOCK & ~FLAG_ONE_NEG_CLOCK; 
    return; 
  } 
  if (   e2->type == TYPE_CONSTANT 
      && (e2->u.value > 1 || e2->u.value < -1) 
      && (e1->var_status & FLAG_CLOCK) 
      && (e1->exp_status & (FLAG_ONE_POS_CLOCK | FLAG_ONE_NEG_CLOCK)) 
      ) { 
    *esptr 
    = ((*esptr) | FLAG_HYBRID) 
    & ~FLAG_ONE_POS_CLOCK & ~FLAG_ONE_NEG_CLOCK; 
    return; 
  } 
  
  /* It could happen that an anniheilator happen. */ 
  if (   e1->type == TYPE_CONSTANT 
      && (e1->u.value == 0) 
      && (e2->var_status & FLAG_CLOCK) 
      && (e2->exp_status & (FLAG_ONE_POS_CLOCK | FLAG_ONE_NEG_CLOCK)) 
      ) { 
    *esptr 
    = ((*esptr) | FLAG_HYBRID) 
    & ~FLAG_ONE_POS_CLOCK & ~FLAG_ONE_NEG_CLOCK; 
    return; 
  } 
  if (   e2->type == TYPE_CONSTANT 
      && (e2->u.value == 0) 
      && (e1->var_status & FLAG_CLOCK) 
      && (e1->exp_status & (FLAG_ONE_POS_CLOCK | FLAG_ONE_NEG_CLOCK)) 
      ) { 
    *esptr 
    = ((*esptr) | FLAG_HYBRID) 
    & ~FLAG_ONE_POS_CLOCK & ~FLAG_ONE_NEG_CLOCK; 
    return; 
  } 
  
  /* It could happen that a toggling coefficient happens. */ 
  if (   e1->type == TYPE_CONSTANT 
      && e1->u.value == -1 
      && (e2->var_status & FLAG_CLOCK)
      ) {
    if (e2->exp_status & FLAG_ONE_POS_CLOCK) {
      *esptr = ((*esptr) & ~FLAG_ONE_POS_CLOCK) | FLAG_ONE_NEG_CLOCK; 
      return; 
    }
    else if (e2->exp_status & FLAG_ONE_NEG_CLOCK) {
      *esptr = ((*esptr) & ~FLAG_ONE_NEG_CLOCK) | FLAG_ONE_POS_CLOCK; 
      return; 
    }
  } 
  if (   e2->type == TYPE_CONSTANT 
      && e2->u.value == -1 
      && (e1->var_status & FLAG_CLOCK)
      ) {
    if (e1->exp_status & FLAG_ONE_POS_CLOCK) {
      *esptr = ((*esptr) & ~FLAG_ONE_POS_CLOCK) | FLAG_ONE_NEG_CLOCK; 
      return; 
    }
    else if (e1->exp_status & FLAG_ONE_NEG_CLOCK) {
      *esptr = ((*esptr) & ~FLAG_ONE_NEG_CLOCK) | FLAG_ONE_POS_CLOCK; 
      return; 
    } 
  } 
}
  /* compose_mult_status() */ 
  
  
void 	compose_rel_status(r, e1, e2) 
	struct ps_exp_type	*r, *e1, *e2; 
{ 
  compose_additive_status(ARITH_MINUS, e1, e2, 
    &(r->var_status), &(r->exp_status)
  ); 

  if (r->exp_status & FLAG_HYBRID) {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\n3. Detecting hybrid system at line %1d.\n", lineno); 
    print_parse_subformula(e1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, " relop "); 
    print_parse_subformula(e2, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, "\n"); 
    #endif 
    
    GSTATUS[INDEX_SYSTEM_TYPE] = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) | FLAG_SYSTEM_HYBRID;
  }
  else if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) != FLAG_SYSTEM_HYBRID)
    if (r->var_status & FLAG_CLOCK) {
      GSTATUS[INDEX_SYSTEM_TYPE] 
      = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) 
      | FLAG_SYSTEM_TIMED;
    }

  /* If only clock variables are used, then it is a clock inequality of some types. */
  if (!((r->var_status & FLAG_DISCRETE) || (r->exp_status & FLAG_HYBRID)))
    if (e1->exp_status & FLAG_ONE_POS_CLOCK)
      if (e2->exp_status & FLAG_ONE_POS_CLOCK)
        r->u.ineq.type = FLAG_EXP_CLOCK_DIFFERENCE;
      else
 	r->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT;
    else
      if (CLOCK_NEG)
	r->u.ineq.type = FLAG_EXP_CLOCK_CONSTANT;
      else
        r->u.ineq.type = FLAG_EXP_STATIC;

  /* if it is a hybrid inequality, then we check if it is a constant or a linear constraint. */
  if (r->exp_status & FLAG_HYBRID) {
    if (r->var_status & (FLAG_CLOCK | FLAG_DENSE)) 
      r->u.ineq.type = FLAG_EXP_DENSE_LINEAR;
    else 
      r->u.ineq.type = FLAG_EXP_DENSE_CONSTANT;
  }

  if (   (r->exp_status & FLAG_EXP_STATE_INSIDE) 
      && (r->var_status & FLAG_SYNCHRONIZER)
      ) {
    fprintf(RED_OUT, "\nSyntax error: mixture of event and state predicate at line %1d.\n", lineno); 
    fflush(RED_OUT); 
    exit(0);  
  }

}
  /* compose_rel_status() */ 





  
compose_assignment_status(as) 
	struct parse_statement_type	*as; 
{
  int 	term_count, ti, pi, num, den, lb_num, lb_den, ub_num, ub_den, lb, ub;

  if (   (as->u.act.lhs->exp_status & FLAG_HYBRID)
      || (as->u.act.rhs_exp->exp_status & FLAG_HYBRID)
      ) { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\n4. Detecting hybrid system at line %1d.\n", lineno); 
    print_parse_subformula(as->u.act.lhs, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, ":="); 
    print_parse_subformula(as->u.act.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, ";\n"); 
    #endif 
    
    GSTATUS[INDEX_SYSTEM_TYPE] = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) | FLAG_SYSTEM_HYBRID; 
    as->op = ASSIGN_HYBRID_EXP; 
  } 
  else if (as->u.act.lhs->var_status & FLAG_CLOCK) { 
    if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) != FLAG_SYSTEM_HYBRID)
      GSTATUS[INDEX_SYSTEM_TYPE] = (GSTATUS[INDEX_SYSTEM_TYPE] & ~MASK_SYSTEM_TYPE) | FLAG_SYSTEM_TIMED;
    /* This is temporary for an operator code. 
     */ 
    as->op = ASSIGN_CLOCK_DIFFERENCE_MIXED; 
  }
  else {
    /* This is temporary for an operator code. 
     */ 
      as->op = ASSIGN_DISCRETE_POLYNOMIAL; 
  } 

}
  /* compose_assignment_status() */  








/* Note this procedure will release the memory occupied by l. */ 
void	system_info_process(l) 
	struct name_link_type	*l; 
{ 
  char	*name; 
  
  for (; name = pop_name(&l); ) { 
    if (!strcmp(name, "CALLING")) { 
      free(name); 
      name = pop_name(&l); 
      if (!name) 
        continue; 

/*
      CURRENT_XTION->calling_mode_index = (int) name; 
*/
      if ((!(name = pop_name(&l))) || strcmp(name, "RETURN")) 
        continue; 
      free(name); 

      if ((!(name = pop_name(&l))) || strcmp(name, "TO")) 
        continue; 
      free(name); 

      name = pop_name(&l); 
      if (!name) 
        continue; 
/* 
      CURRENT_XTION->return_mode_index = (int) name; 

      CURRENT_XTION->status = CURRENT_XTION->status | FLAG_CALLING_PROC; 
*/
    } 
  } 
}
  /* system_info_process() */ 
  



inline void	setup_game_exp() { 
  if (GAME_MODL_EXP) { 
    ps_fairness_free_list(GAME_MODL_EXP->u.mexp.strong_fairness_list); 
    ps_fairness_free_list(GAME_MODL_EXP->u.mexp.weak_fairness_list); 
    ps_fairness_free_list(GAME_SPEC_EXP->u.mexp.strong_fairness_list); 
    ps_fairness_free_list(GAME_SPEC_EXP->u.mexp.weak_fairness_list); 
    ps_fairness_free_list(GAME_ENVR_EXP->u.mexp.strong_fairness_list); 
    ps_fairness_free_list(GAME_ENVR_EXP->u.mexp.weak_fairness_list); 
  } 
  else { 
    GAME_MODL_EXP = ps_exp_alloc(TYPE_GAME_SIM); 
    GAME_SPEC_EXP = ps_exp_alloc(TYPE_GAME_SIM);
    GAME_ENVR_EXP = ps_exp_alloc(TYPE_GAME_SIM);
  } 
  GAME_MODL_EXP->u.mexp.strong_fairness_count = 0; 
  GAME_MODL_EXP->u.mexp.strong_fairness_list = NULL; 
  GAME_MODL_EXP->u.mexp.weak_fairness_count = 0; 
  GAME_MODL_EXP->u.mexp.weak_fairness_list = NULL; 

  GAME_SPEC_EXP->u.mexp.strong_fairness_count = 0; 
  GAME_SPEC_EXP->u.mexp.strong_fairness_list = NULL; 
  GAME_SPEC_EXP->u.mexp.weak_fairness_count = 0; 
  GAME_SPEC_EXP->u.mexp.weak_fairness_list = NULL; 
  
  GAME_ENVR_EXP->u.mexp.strong_fairness_count = 0; 
  GAME_ENVR_EXP->u.mexp.strong_fairness_list = NULL; 
  GAME_ENVR_EXP->u.mexp.weak_fairness_count = 0; 
  GAME_ENVR_EXP->u.mexp.weak_fairness_list = NULL; 
  
}
  /* setup_game_exp() */  


int 	count_fs_ana = 0; 

void	fairness_syntax_analyze(
  struct ps_fairness_link_type	*fl, 
  int				flag_delayed_tctl_analysis 
) {
/*
  fprintf(RED_OUT, 
    "\n====(fairness syntax analysis %1d)====\n", 
    ++count_fs_ana
  ); 
*/  
  struct ps_exp_type
    *original_game_exp_in_static_eval; 
  struct ps_fairness_link_type	
    *original_multiple_fairness_link_in_static_eval; 
    
  original_multiple_fairness_link_in_static_eval 
  = CURRENT_MULTIPLE_FAIRNESS_LINK_IN_STATIC_EVAL; 
  
  CURRENT_MULTIPLE_FAIRNESS_LINK_IN_STATIC_EVAL = fl; 
/*
  pcform(fl->fairness); 
*/
  fl->fairness = exp_static_evaluation(fl->fairness, 
    FLAG_NO_PI_STATIC_EVAL, NULL    
  ); 
/*
  fprintf(RED_OUT, "\nAfter static analysis: "); 
  pcform(fl->fairness); 
*/

  CURRENT_MULTIPLE_FAIRNESS_LINK_IN_STATIC_EVAL
  = original_multiple_fairness_link_in_static_eval; 
  
  fl->fairness = rec_ineq_analyze(fl->fairness); 
/*
  fprintf(RED_OUT, "\nAfter ineq analyze: "); 
  pcform(fl->fairness); 
*/        
  if (flag_delayed_tctl_analysis) { 
    fl->fairness = analyze_tctl(fl->fairness, 0, 0);
/*
    fprintf(RED_OUT, "\nAfter tctl analyze: "); 
    pcform(fl->fairness); 
*/  
    ps_exp_mark(fl->fairness, FLAG_GC_STABLE);
  }
}
  /* fairness_syntax_analyze() */ 
  
  
  

struct ps_fairness_link_type	*add_fairness_tail(
  struct ps_fairness_link_type	*fl_tail, 
  struct ps_exp_type		*f, 
  int				*fcount_ptr
) { 
  struct ps_fairness_link_type	*fl; 
  
  fl = (struct ps_fairness_link_type *) 
    malloc(sizeof(struct ps_fairness_link_type)); 
  fl->fairness = f; 
  fl->next_ps_fairness_link = fl_tail->next_ps_fairness_link; 
  fl_tail->next_ps_fairness_link = fl; 
  (*fcount_ptr)++; 
  return(fl); 
}
  /* add_fairness_tail() */ 




struct ps_fairness_link_type	*expand_necessary_fairness_list(
  struct ps_fairness_link_type	*flist, 
  int				*fcount_ptr
) { 
  struct ps_fairness_link_type	*fl, dummy_fl, *fl_tail;
  struct ps_exp_type		*newsub, *child; 
  int				llb, lub, ulb, uub; 

  dummy_fl.next_ps_fairness_link = NULL; 
  fl_tail = &dummy_fl; 
  for (fl = flist; fl; fl = fl->next_ps_fairness_link) {
    float 	flb, fub; 
    int		flag; 
    
    switch (fl->fairness->type) { 
    case TYPE_FALSE: 
      fprintf(RED_OUT, "\nERROR: a false fairness assumption "); 
      bk(0); 
      break; 
    case TYPE_TRUE: 
      continue; 
      break; 
    case TYPE_MULTIPLE_FAIRNESS: 
      flag = rec_get_integer_range(
        fl->fairness->u.qexp.lb_exp, &llb, &lub, &flb, &fub
      ); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in multiple fairness lb at line %1d.\n", 
          fl->fairness->lineno 
        ); 
        pcform(fl->fairness); 
        fflush(RED_OUT); 
        bk(0); 
      } 
      flag = rec_get_integer_range(
        fl->fairness->u.qexp.ub_exp, &ulb, &uub, &flb, &fub
      ); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in multiple fairness ub at line %1d.\n", 
          fl->fairness->lineno 
        ); 
        pcform(fl->fairness); 
        fflush(RED_OUT); 
        bk(0); 
      } 
      if (llb > uub) { 
        newsub = PS_EXP_TRUE; 
        break; 
      } 
      if (llb > ulb) 
        llb = ulb; 
      if (uub < lub) 
        uub = lub; 
      push_quantified_value_stack(fl->fairness); 

      for (fl->fairness->u.qexp.value = llb; 
           fl->fairness->u.qexp.value <= uub; 
           fl->fairness->u.qexp.value++
           ) { 
        child = exp_static_evaluation(fl->fairness->u.qexp.child, 
          FLAG_NO_PI_STATIC_EVAL, NULL    
        ); 
/*
        fprintf(RED_OUT, "\n-----------------------\nstatic evaluating an instance of MFA with index %1d: ", 
          fl->fairness->u.qexp.value
        ); 
        pcform(fl->fairness); 
        fprintf(RED_OUT, "The result is: "); 
        pcform(child); 
        if (   child->type == LINEAR_EVENT 
            && child->u.eexp.event_exp->type == TYPE_SYNCHRONIZER
            ) { 
          fprintf(RED_OUT, "The event address type is %1d: ", 
            child->u.eexp.event_exp->u.atom.exp_base_proc_index->type 
          ); 
          pcform(child->u.eexp.event_exp->u.atom.exp_base_proc_index); 
        } 
*/
        switch (child->type) {
        case TYPE_FALSE: 
          pop_quantified_value_stack(fl->fairness); 
          fprintf(RED_OUT, 
            "\nERROR: a false fairness assumption after instantiated with %1d.\n", 
            fl->fairness->u.qexp.value
          ); 
          bk(0); 
          break; 
        case TYPE_TRUE: 
          continue; 
          break; 
        case LINEAR_EVENT: 
          if (   child->u.eexp.precond_exp == PS_EXP_TRUE
              && child->u.eexp.event_exp == NULL 
              && child->u.eexp.postcond_exp == PS_EXP_TRUE
              ) 
            break; 
        default: 
          fl_tail = add_fairness_tail(fl_tail, child, fcount_ptr); 
          break; 
        }
      }
      pop_quantified_value_stack(fl->fairness); 
      break; 
    default: 
      fl_tail = add_fairness_tail(fl_tail, fl->fairness, fcount_ptr); 
      break; 
    } 
  }
  return(dummy_fl.next_ps_fairness_link); 
}
  /* expand_necessary_fairness_list() */ 



inline void	fillin_game_fairness_assumptions(
  struct ps_exp_type		*game_exp, 
  struct gram_fairness_type 	*game_fairness 
) { 
  if (game_fairness->strong_fairness_count <= 0) { 
    game_exp->u.mexp.strong_fairness_count = 0; 
    game_exp->u.mexp.strong_fairness_list = NULL; 
  }
  else {
    GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS;
    game_exp->exp_status = game_exp->exp_status | FLAG_FAIRNESS_STRONG; 
    game_exp->u.mexp.strong_fairness_count = 0; 
    game_exp->u.mexp.strong_fairness_list 
    = expand_necessary_fairness_list(
      game_fairness->strong_fairness_list, 
      &(game_exp->u.mexp.strong_fairness_count)
    ); 
  }

  if (game_fairness->weak_fairness_count <= 0) { 
    game_exp->u.mexp.weak_fairness_count = 0; 
    game_exp->u.mexp.weak_fairness_list = NULL; 
  }
  else {
    GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS;
    game_exp->exp_status = game_exp->exp_status | FLAG_FAIRNESS_WEAK; 
    game_exp->u.mexp.weak_fairness_count = 0; 
    game_exp->u.mexp.weak_fairness_list 
    = expand_necessary_fairness_list(
      game_fairness->weak_fairness_list, 
      &(game_exp->u.mexp.weak_fairness_count)
    ); 
  }
}
  /* fillin_game_fairness_assumptions() */ 




  
struct ps_fairness_link_type	*append_fairness_list(
  struct ps_exp_type		*parent_exp, 
  struct ps_fairness_link_type	*ftail, 
  struct ps_fairness_link_type	*flist
) { 
  struct ps_fairness_link_type	*fl, *nfl;
 
  for (fl = flist; fl; fl = fl->next_ps_fairness_link) {
    nfl = (struct ps_fairness_link_type *) 
      malloc(sizeof(struct ps_fairness_link_type));     
    ftail->next_ps_fairness_link = nfl; 
    ftail = nfl; 
    ftail->fairness = ps_exp_copy(fl->fairness); 
    ftail->red_fairness = fl->red_fairness; 
  } 
  return(ftail); 
} 
  /* append_fairness_list() */ 





struct ps_exp_type	*merge_fairness_exps(
  struct ps_exp_type	*fx, 
  struct ps_exp_type	*fy
) {
  struct ps_exp_type		*gf; 
  struct ps_fairness_link_type	dummy_head, *ftail;
  
  gf = ps_exp_alloc(TYPE_GAME_SIM); 
  
  gf->u.mexp.strong_fairness_count 
  = fx->u.mexp.strong_fairness_count + fy->u.mexp.strong_fairness_count; 

  ftail = &dummy_head; 
  ftail = append_fairness_list(gf, ftail, fx->u.mexp.strong_fairness_list);
  ftail = append_fairness_list(gf, ftail, fy->u.mexp.strong_fairness_list);
  ftail->next_ps_fairness_link = NULL; 
  gf->u.mexp.strong_fairness_list = dummy_head.next_ps_fairness_link; 

  gf->u.mexp.weak_fairness_count 
  = fx->u.mexp.weak_fairness_count + fy->u.mexp.weak_fairness_count; 
  ftail = &dummy_head; 
  ftail = append_fairness_list(gf, ftail, fx->u.mexp.weak_fairness_list);
  ftail = append_fairness_list(gf, ftail, fy->u.mexp.weak_fairness_list);
  ftail->next_ps_fairness_link = NULL; 
  gf->u.mexp.weak_fairness_list = dummy_head.next_ps_fairness_link; 
  
  return(gf); 
}
  /* merge_fairness_exps() */ 
  

void	instantiate_discrete_ranges(
  struct parse_variable_type	*pv_list
) { 
  struct parse_variable_type	*pv; 
  int				i, flag; 
      
  for (pv = pv_list; pv; pv = pv->next_parse_variable) { 
    if (pv->status & FLAG_VAR_BOUNDS_DELAYED_EVAL) {
      i = get_value((struct ps_exp_type *) pv->u.disc.lb, 0, &flag); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal discrete range specification for variable %s:\n", 
          pv->name
        ); 
        pcform((struct ps_exp_type *) pv->u.disc.lb); 
        bk(0);  
      } 
      else 
        pv->u.disc.lb = i; 
      i = get_value((struct ps_exp_type *) pv->u.disc.ub, 0, &flag); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal discrete range specification for variable %s:\n", 
          pv->name
        ); 
        pcform((struct ps_exp_type *) pv->u.disc.ub); 
        bk(0);  
      } 
      else 
        pv->u.disc.ub = i; 
    } 
  }
}
  /* instantiate_discrete_ranges() */ 





struct pnp_var_type { 
  struct parse_variable_type	*pvar; 
  int				status; 
}; 
  
%}

%union {
  int 					number;
  float					float_number; 
  char					*string;
  struct name_link_type			*nlist; 
  struct index_pair_link_type		*iplist; 
  struct parse_xtion_link_type		*xlist;
  struct parse_xtion_type		*xtion;
  struct parse_statement_type		*st; 
  struct ps_exp_type			*sp;
  struct ps_bunit_type			*splist; 
  struct gram_interval_type		*gint;
  struct gram_fairness_type		*gfair;
  struct gram_optional_address_type	*addr;
  struct ps_fairness_link_type		*gseq;
  struct parse_module_type		*module; 
  struct parse_mode_type		*mode; 
  struct parse_operand_type		*opn;
  struct parse_variable_type		*pvar; 
//  struct parse_indirect_type		*pind; 
  struct pnp_var_type			*pnp; 
  struct parse_stream_operation_type	*pso; 
}

%token  <string> 	PS_IDENTIFIER PS_INLINE_ARGUMENT
%token  <number>	PS_PROCESS PS_ROLE PS_URGENT 
%token  <number>	PS_PROCESS_COUNT PS_MODE_COUNT PS_XTION_COUNT 
%token	<number>	PS_ASSIGNMENT PS_GUARD PS_ERASE PS_GLOBALLY 
%token	<number>	PS_MODE PS_XTIONS PS_ADDRESSES 
%token	<number>	PS_RATE PS_WHEN PS_MAY PS_GOTO PS_IN 
%token	<number>	PS_WHILE PS_IF PS_ELSE  
%token	<number>	PS_LOCAL PS_GLOBAL PS_STACK PS_MEMORY 
%token	<number>	PS_BIRD PS_BIRD_PLUS PS_BIRD_MINUS
%token	<number>	PS_PARAMETER PS_FORMULA PS_QUANTIFY 
%token	<number>	PS_SYSTEM PS_INFO PS_CALL PS_RETURN PS_CPLUG 
%token	<number>	PS_CLOCK PS_DENSE PS_DISCRETE PS_FLOAT PS_DOUBLE   
%token	<number>	PS_STREAM PS_ORDERED PS_UNORDERED 
%token	<number>	PS_OPEN PS_CLOSE PS_INPUT PS_OUTPUT PS_FROM_STREAM PS_TO_STREAM  
%token	<number>	PS_FREE PS_MALLOC 
%token	<number>	PS_BOOLEAN PS_SYNCHRONIZER PS_INLINE 
%token  <number> 	PS_TCTL PS_DEBUG PS_RISK PS_GOAL PS_MATRIX 
%token	<number>	PS_CHECK PS_DIRTY PS_LEAKS PS_REDLIB PS_SESSION 
%token	<number>	PS_PARAMETRIC PS_SAFETY 
%token	<number>	PS_BRANCHING PS_BISIMULATION PS_SIMULATION 
%token 	<number>	PS_P PS_INFINITY PS_BIT_AND PS_BIT_OR 
%token	<number>	PS_AND PS_OR PS_NOT PS_BIT_NOT PS_TRUE PS_FALSE PS_IMPLY PS_RIGHTARROW
%token	<number>	PS_UNTIL PS_ALWAYS PS_EVENTUALLY PS_EVENT 
%token	<number> 	PS_WITH PS_ON PS_RESET PS_THROUGH PS_EVENTS
%token	<number> 	PS_FORALL PS_EXISTS PS_ALMOST PS_OFTEN 
%token	<number> 	PS_ASSUME PS_STRONG PS_WEAK
%token	<number>	PS_EQ PS_NEQ PS_LESS PS_LEQ PS_GREATER PS_GEQ
%token	<number>	PS_INC PS_DEC PS_CLEAR 
%token	<number>	PS_PLUS PS_MINUS PS_MULTIPLY PS_DIVIDE PS_MODULO PS_SUM 
%token	<number>	PS_LPAR PS_RPAR PS_LBRAC PS_RBRAC PS_LCURLY PS_RCURLY
%token	<number>	PS_NUMBER PS_HEX_NUMBER PS_FLOAT_NUMBER
%token	<number>	PS_NULL PS_INITIAL PS_CHANGE
%token	<number>	PS_SIMULATE PS_DEADLOCK PS_ZENO
%token	<number>	PS_INDEX PS_PRIMED 
%token	<number>	PS_COMMA PS_DDOTS PS_COLON PS_SEMICOLON PS_EXCLAMATION PS_QUESTION
%token	<number>	PS_VARIABLE PS_BDD PS_SYNC PS_QFD PS_CONSTRUCT 

%token	<number>	PS_WINDOW
%token	<number>	PS_POSITION
%token	<number>	PS_RECTANGLE
%token	<number>	PS_SHAPE
%token	<number>	PS_SQUARE
%token	<number>	PS_OVAL
%token	<number>	PS_CIRCLE
%token	<number>	PS_TRIANGLE

%token	<number>	PS_LEFTWARD
%token	<number>	PS_RIGHTWARD
%token	<number>	PS_UPWARD
%token	<number>	PS_DOWNWARD
 
%token	<number>	PS_COLOR
%token	<number>	PS_RED
%token	<number>	PS_WHITE
%token	<number>	PS_BLACK
%token	<number>	PS_BLUE
%token	<number>	PS_YELLOW
%token	<number>	PS_GREEN
%token	<number>	PS_POINT 

%token	<sp>		PS_DISCRETE_INLINE_CALL PS_BOOLEAN_INLINE_CALL 
%token	<sp>		PS_MACRO_CONSTANT 

%type	<number>	mode_xtion_system

%type	<number>	window_drawing_options 
%type	<number>	mode_drawing_options 
%type	<number>	mode_drawing_position_option
%type	<number>	mode_drawing_shape_option 
%type	<number>	mode_drawing_color_option
%type	<number>	shape_triangle_direction
%type	<number>	xtion_points 
%type	<iplist>	point_list

%type	<number>	processes process_count_declaration_tail 
%type 	<string>	process_names 
%type	<number> 	variable_declaration variable_declarations vrate vrates
%type	<number> 	var_scope var_use stream_type task_type mode_start 
%type	<number> 	optional_memory_use 
%type	<mode>		mode modes 
%type	<number>	lbrac rbrac pure_number event_direction optional_event_direction 
%type	<st> 		assignment statements statement system_info actions 
%type	<number>	fairness_strength 
%type	<number>	game_proc_indices nontrivial_game_proc_indices 
%type 	<number> 	one_var_index quantify_restriction 
%type	<number>	one_quantify_op_restriction quantify_segments

%type	<pnp> 		token_variable 
%type	<pvar>		token_sync variable_names base_variable 

%type	<sp>		exp_term sexp_term exp_bit_term
%type	<sp>		exp_arith sexp_arith exp_general 
%type	<sp>		exp_multiply sexp_multiply 

%type   <sp> 		complete_operand 
%type   <sp> 		assign_dest lbound rbound sync_address

%type	<sp>		initial specification global_condition 
%type	<sp>		local_condition trigger_condition  
%type	<sp>		formula fmla_imply fmla_disjlist fmla_conjlist
%type	<sp>		fmla_conj optional_event 
%type 	<sp> 		fmla_literal inline_exp_declaration
%type 	<sp>		count_omega global_fairness event_fairness 
%type 	<sp>		multiple_global_fairness
%type	<splist>	inline_exp_declarations inline_actual_arguments
%type	<splist>	inline_actual_argument_list 

%type	<nlist>		inline_formal_argument_declaration 
%type	<nlist>		inline_formal_argument_list

%type   <number>        rel_op path_quantifier single_modal 
%type   <number>	multiplicative_op
%type	<number> 	lboundary rboundary signed_number 

%type	<addr> 		optional_address 

%type	<gint> 		time_restriction
%type	<gseq> 		global_fairness_sequence  
%type	<gseq> 		debug
%type	<gfair> 	fairness
%type	<xlist>		mode_rules rules
%type	<xtion>		xtion rule
%type	<nlist> 	name_list; 
%type 	<pso> 		stream_operations stream_operation
%left	PS_OR PS_AND


%%
parse_result: { 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "\0\n"); 
    TOP_SCOPE = -1; 
    push_scope(SCOPE_CHOICE); 
    lineno = 1;
    flag_line_start = 1;
    flag_comment_to_end_of_line = TYPE_FALSE;
    
    lexbuf = malloc(1000); 
    count_red_src_lines = 0; 
    red_src_lines = NULL; 
    
    switch (flag_redlib_input_source) { 
    case FLAG_INPUT_STRING: 
      redlib_input_string[redlib_input_string_len-2] = 0 /*(char) NULL*/; 
      redlib_input_string[redlib_input_string_len-1] = 0 /*(char) NULL*/; 
/*
      fprintf(RED_OUT, "fillin redlib_input_string[%1d] with %1d.\n", 
        redlib_input_string_len-2, 
        redlib_input_string[redlib_input_string_len-2]
      ); 
      fprintf(RED_OUT, "fillin redlib_input_string[%1d] with %1d.\n", 
        redlib_input_string_len-1, 
        redlib_input_string[redlib_input_string_len-1]
      ); 
      fprintf(RED_OUT, "In redgram: '%s' with length %1d:%1d\n", 
        redlib_input_string, 
        strlen(redlib_input_string), 
        redlib_input_string_len
      ); 
*/
      redlib_handle = redlib_scan_buffer(
        redlib_input_string, redlib_input_string_len
      ); 
      redlib_switch_to_buffer(redlib_handle);
      break; 
    case FLAG_INPUT_FILE: 
      break; 
    } 
  }
  result_of_choices {
    free(lexbuf); 
    
    switch (flag_redlib_input_source) { 
    case FLAG_INPUT_STRING: 
/*
      fprintf(RED_OUT, "Finished parsing\n"); 
*/
      redlib_delete_buffer(redlib_handle); 
/*
      fprintf(RED_OUT, "Finished deleting buffer.\n"); 
*/
      break; 
    case FLAG_INPUT_FILE: 
      break; 
    } 
    return; 
/*
    redlibwrap(); 
    return; 
*/
  }; 


result_of_choices: 
  mode_xtion_system {
    TYPE_PARSE_CHOICE = TYPE_PARSE_MODE_XTION_SYSTEM; 
    GSTATUS[INDEX_PARSE] = GSTATUS[INDEX_PARSE] | FLAG_PARSER_MODEL_DONE; 
//    fprintf(RED_OUT, "choice of mode transition system input.\n"); 
  } 
| PS_XTIONS {
    PARSER_INPUT_SYNC_XTION = (struct parse_redlib_sync_xtion_type *) 
      malloc(sizeof(struct parse_redlib_sync_xtion_type)); 
    PARSER_INPUT_SYNC_XTION->status = 0; 
    PARSER_INPUT_SYNC_XTION->party_count = 0; 
    PARSER_INPUT_SYNC_XTION->party_list = 0; 
  }
  parties { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_SYNC_XTION; 
  } 
| PS_ROLE /*1*/ {
    int	pi; 
    
    CUR_GAME_ROLE = FLAG_GAME_MODL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = PROCESS[pi].status & ~MASK_GAME_ROLES; 
    } 
    setup_game_exp(); 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*3*/ { 
    change_scope(SCOPE_GLOBAL); 
  }
  fairness /*5*/ PS_SEMICOLON /*6*/ {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, $5); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game model fairness:\n"); 
    pcform(GAME_MODL_EXP); 
    fprintf(RED_OUT, "\nEnd of model role sequence.\n"); 
    fflush(RED_OUT);
    #endif 
    GAME_MODL_EXP = exp_static_evaluation(GAME_MODL_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_MODL_EXP = rec_ineq_analyze(GAME_MODL_EXP); 
    GAME_MODL_EXP = analyze_tctl(GAME_MODL_EXP, 0, 0);

    CUR_GAME_ROLE = FLAG_GAME_SPEC; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nEnd of model role spec.\n"); 
    fflush(RED_OUT); 
    #endif 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*8*/ { 
    change_scope(SCOPE_GLOBAL); 
  } 
  fairness /*10*/ PS_SEMICOLON /*11*/ { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, $10); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game spec fairness:\n"); 
    pcform(GAME_SPEC_EXP); 
    fprintf(RED_OUT, "\nEnd of spec role sequence.\n"); 
    fflush(RED_OUT);
    #endif 
    GAME_SPEC_EXP = exp_static_evaluation(GAME_SPEC_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_SPEC_EXP = rec_ineq_analyze(GAME_SPEC_EXP); 
    GAME_SPEC_EXP = analyze_tctl(GAME_SPEC_EXP, 0, 0);
    if (  GAME_SPEC_EXP->u.mexp.strong_fairness_count
        + GAME_SPEC_EXP->u.mexp.weak_fairness_count 
        > 1
        ) { 
      fprintf(RED_OUT, 
        "\nError: Detection of simulation checking of specification automata \n"
      ); 
      fprintf(RED_OUT, 
        "       of type general Buechi automata \n"
      ); 
      fprintf(RED_OUT, 
        "       with %1d strong and %1d weak fairness assumptions.\n", 
        GAME_SPEC_EXP->u.mexp.strong_fairness_count, 
        GAME_SPEC_EXP->u.mexp.weak_fairness_count
      ); 
      fprintf(RED_OUT, 
        "       Sorry!  It is really not a bug. \n"
      ); 
      fprintf(RED_OUT, 
        "       At this moment, we only support the simulation checking of \n"
      ); 
      fprintf(RED_OUT, 
        "       a model general Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       against a specificaiton Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       with either one strong or one weak fairness assumption. \n\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter static evaluating the game spec fairness:\n"); 
    pcform(GAME_SPEC_EXP); 
    #endif 
    push_scope(SCOPE_GLOBAL); 
  } 
  fairness /*13*/ { 
    int pi, sxi; 
    
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, $13); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game envr fairness:\n"); 
    pcform(GAME_ENVR_EXP); 
    fprintf(RED_OUT, "\nEnd of envr role sequence.\n"); 
    fflush(RED_OUT);
    #endif 
    GAME_ENVR_EXP = exp_static_evaluation(GAME_ENVR_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_ENVR_EXP = rec_ineq_analyze(GAME_ENVR_EXP); 
    GAME_ENVR_EXP = analyze_tctl(GAME_ENVR_EXP, 0, 0);
    TYPE_PARSE_CHOICE = TYPE_PARSE_GAME_ROLES; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      if (!(PROCESS[pi].status & MASK_GAME_ROLES))
        PROCESS[pi].status = PROCESS[pi].status | FLAG_GAME_ENVR; 
    } 
    for (sxi = 0; sxi < SYNC_XTION_COUNT; sxi++) { 
      SYNC_XTION[sxi].status = SYNC_XTION[sxi].status & ~MASK_GAME_ROLES; 
      for (pi = 0; pi < SYNC_XTION[sxi].party_count; pi++) { 
        SYNC_XTION[sxi].status 
        = SYNC_XTION[sxi].status 
        | (PROCESS[SYNC_XTION[sxi].party[pi].proc].status & MASK_GAME_ROLES); 
      } 
    } 
/*
    psx_status("after reading in roles", 
      SYNC_XTION, SYNC_XTION_COUNT
    ); 
*/
  }
| PS_LOCAL PS_FORMULA 
  /* Note here in every local_condition parsing, 
   * SCOPE_LOCAL is pushed and popped automatically. 
   */ 
  local_condition PS_SEMICOLON {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_LOCAL; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** After parsing initia condition.\n"); 
    #endif 
    
    PARSER_INPUT_FORMULA = $3;
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSER_INPUT_FORMULA = exp_static_evaluation(PARSER_INPUT_FORMULA, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      PARSER_INPUT_FORMULA = rec_ineq_analyze(PARSER_INPUT_FORMULA); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nAfter parsing specification\nInitial:\n");
      print_parse_subformula_structure(PARSE_SPEC, 0);
      fflush(RED_OUT);
      fprintf(RED_OUT, "\nGoal:\n");
      print_parse_subformula_structure(PARSE_SPEC, 0);
      fflush(RED_OUT);
      #endif 
    }
  } 
| PS_GLOBAL PS_FORMULA { 
    push_scope(SCOPE_GLOBAL); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "hh\n"); 
    #endif 
  }
  global_condition { 
    pop_scope(); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "kk\n"); 
    #endif 
  }
  PS_SEMICOLON {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_GLOBAL; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "*** After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = $4;
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "yacc global: parsing global before mode index fillin.\n"); 
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0); 
    #endif 
     
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSE_SPEC = exp_static_evaluation(PARSE_SPEC, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc global: parsing global after mode index fillin.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0); 
      #endif 
    
      PARSE_SPEC = rec_ineq_analyze(PARSE_SPEC); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc global: parsing global after ineq analysis.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0); 
      #endif 
    }
    // We first record the original form of the formula. 
    // This can be used for educational purpose. 
    // It can also be used for model-checking analysis. 
    PARSER_INPUT_FORMULA = PARSE_SPEC; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nyacc global: After shorthand analysis\nglobal:\n");
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0);
    fflush(RED_OUT);
    #endif 
  } 
| PS_GLOBAL PS_EVENTS { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "hh\n"); 
    #endif 
  }
  formula { 
    pop_scope(); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "kk\n"); 
    #endif 
  }
  PS_SEMICOLON {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_GLOBAL_EVENTS; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "*** After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = $4;
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "yacc global: parsing global before mode index fillin.\n"); 
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0); 
    #endif 
     
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSE_SPEC = exp_static_evaluation(PARSE_SPEC, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc global: parsing global after mode index fillin.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0); 
      #endif 
    
      PARSE_SPEC = rec_ineq_analyze(PARSE_SPEC); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc global: parsing global after ineq analysis.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0); 
      #endif 
    }
    // We first record the original form of the formula. 
    // This can be used for educational purpose. 
    // It can also be used for model-checking analysis. 
    PARSER_INPUT_FORMULA = PARSE_SPEC; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nyacc global: After shorthand analysis\nglobal:\n");
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0);
    fflush(RED_OUT);
    #endif 
  } 
| PS_QUANTIFY { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    PARSER_QUANTIFICATION_LIST = NULL;    
  }
  quantify_segments { 
    pop_scope(); 
    fprintf(RED_OUT, "After parsing the quantify segments.\n"); 
  } 
  PS_SEMICOLON { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_QUANTIFY; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** After parsing quantification exp.\n"); 
    #endif 
  } 
| PS_TCTL { 
    push_scope(SCOPE_GLOBAL_EVENT); 
  } 
  global_condition { 
    pop_scope(); 
  } 
  PS_SEMICOLON { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_TCTL; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** yacc tctl: After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = $3;
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "yacc tctl: parsing global before mode index fillin.\n"); 
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0);
    fflush(RED_OUT);
    #endif 
    
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSE_SPEC = exp_static_evaluation(PARSE_SPEC, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc tctl: parsing global after mode index fillin.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0);
      fflush(RED_OUT);
      #endif 
    
      PARSE_SPEC = rec_ineq_analyze(PARSE_SPEC); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "yacc tctl: parsing global after ineq analysis.\n"); 
      pcform(PARSE_SPEC); 
      print_parse_subformula_structure(PARSE_SPEC, 0);
      fflush(RED_OUT);
      #endif 
    } 
    // We first record the original form of the formula. 
    // This can be used for educational purpose. 
    // It can also be used for model-checking analysis. 
    PARSER_INPUT_FORMULA = PARSE_SPEC; 
    /* NOte that we do not add the fairness variables here. 
       This implies that we do not allow 
       fairness_bck_log_one_iteration() in fairness evaluation.  
    */
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nyacc tctl: after shorthand analysis:\n");
    pcform(PARSE_SPEC); 
    print_parse_subformula_structure(PARSE_SPEC, 0);
    fflush(RED_OUT);
    #endif 
  } 
; 
  
  
mode_xtion_system :
/*1*/ 
  window_drawing_options { 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_PROCESS_COUNT; 
  } 
  PS_PROCESS { 
    struct parse_variable_type	*pv;
    int				ti; 

    count_debug1 = count_debug2 = 0; 
    
    MODULE_COUNT = 0; 

    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      MEMORY_SIZE = 0; 
      MEMORY_DISCRETE_SIZE = MEMORY_FLOAT_SIZE = MEMORY_DOUBLE_SIZE = 0; 
      count_memory = 0; 
      memory_list = NULL; 
      
      variable_index = NULL; 
      GLOBAL_COUNT = ((int *) malloc((TYPE_STREAM-TYPE_SYNCHRONIZER+1)
				   * sizeof(int)
				   )
		    ) - TYPE_SYNCHRONIZER; 
      LOCAL_COUNT = ((int *) malloc((TYPE_STREAM-TYPE_SYNCHRONIZER+1)
				   * sizeof(int)
				   )
		    ) - TYPE_SYNCHRONIZER; 
      for (ti = TYPE_SYNCHRONIZER; ti <= TYPE_STREAM; ti++) {
        GLOBAL_COUNT[ti] = 0; 
        LOCAL_COUNT[ti] = 0; 
      } 

      CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
      CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 

      declare_global_synchronizer_list = NULL;
      declare_global_dense_list = NULL;
      declare_global_clock_list = NULL;
      declare_global_discrete_list = NULL;
      declare_global_float_list = NULL;
      declare_global_double_list = NULL;
      declare_global_pointer_list = NULL;
      declare_global_stream_list = NULL; 

      declare_local_synchronizer_list = NULL; 
      declare_local_dense_list = NULL; 
      declare_local_clock_list = NULL; 
      declare_local_discrete_list = NULL; 
      declare_local_pointer_list = NULL; 
      
      declare_stack_discrete_list = NULL; 
      count_stack_discrete = 0; 

      // Predeclared local variables. 
      push_scope(SCOPE_LOCAL); 
      CUR_VAR_TYPE = TYPE_DISCRETE; 
      var_mode = register_variable("mode"); 
      OFFSET_MODE = var_mode->index;
      var_mode->u.disc.lb = var_mode->u.disc.ub = 0;
      var_mode->status = var_mode->status 
      | FLAG_MODE | FLAG_BOUND_DECLARED | FLAG_VAR_SYS_GEN;
    
      var__sp = register_variable("_sp"); 
      OFFSET__SP = var__sp->index;
      var__sp->u.disc.lb = var__sp->u.disc.ub = 0;
      var__sp->status = var__sp->status 
      | FLAG_BOUND_DECLARED | FLAG_VAR_SYS_GEN;
    
      // Predeclared stack variables.  
      change_scope(SCOPE_STACK); 
      var__retmode = register_variable("_retmode"); 
      var__retmode->u.disc.lb = var__retmode->u.disc.ub = 0;
      var__retmode->status = var__retmode->status 
      | FLAG_VAR_STACK | FLAG_BOUND_DECLARED | FLAG_VAR_SYS_GEN;
    
      // Predeclared global variables. 
      change_scope(SCOPE_GLOBAL); 
      
      // Predeclared dense variables. 
      CUR_VAR_TYPE = TYPE_DENSE; 
      var_prob_dense = register_variable("PROB_DENSE\0"); 
      var_prob_dense->status = var_prob_dense->status | FLAG_VAR_SYS_GEN; 
      
      // Predeclared global clocks. 
      CUR_VAR_TYPE = TYPE_CLOCK; 
      var_zero = register_variable("0\0"); 
      var_zero->status = var_zero->status | FLAG_VAR_SYS_GEN; 

      /* constant TIME = 2 */ 
      var_time = register_variable("TIME\0");
      var_time->status = var_time->status | FLAG_VAR_SYS_GEN; 
      /* constant DELTA = 4 */ 
      var_delta = register_variable("delta\0");
      var_delta->status = var_delta->status | FLAG_VAR_SYS_GEN; 
      /* constant DELTAP = 6 */ 
      var_deltap = register_variable("deltap\0");
      var_deltap->status = var_deltap->status | FLAG_VAR_SYS_GEN; 
      /* constant NEG_DELTA = 8 */ 
      var_neg_delta = register_variable("-delta\0");
      var_neg_delta->status = var_neg_delta->status | FLAG_VAR_SYS_GEN; 
      /* constant NEG_DELTAP = 10 */ 
      var_neg_deltap = register_variable("-deltap\0");
      var_neg_deltap->status = var_neg_deltap->status | FLAG_VAR_SYS_GEN; 
      /* constant MODAL_CLOCK = 12 */ 
      var_modal_clock = register_variable("MODAL_CLOCK\0"); 
      var_modal_clock->status = var_modal_clock->status | FLAG_VAR_SYS_GEN; 
      /* constant PLAY_TIME = 14 */ 
      var_play_time = register_variable("PLAYTIME\0"); 
      var_play_time->status = var_play_time->status | FLAG_VAR_SYS_GEN; 
      /* constant CMAX_M_DELTA = 16 */ 
      var_zeno_clock = register_variable("ZENO_CLOCK\0"); 
      var_zeno_clock->status = var_zeno_clock->status | FLAG_VAR_SYS_GEN; 

      declare_global_rel_list = NULL;

      declare_clock_assign_pattern_list = NULL;
      declare_clock_assign_pattern_count = 0;

      MAX_TERM_COUNT = 0;

      pop_scope(); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nvar_mode = %x\n", var_mode);
      #endif
    } 
    MODE_COUNT = 0;
    declare_mode_list = NULL;

    declare_xtion_count = 0;
    declare_xtion_list = NULL; 

    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      process_list = NULL; 
      process_name_index = 1; 
    } 
    ALL_CLOCK_TIMING_BOUND = 0; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "11: new ALL_CLOCK_TIMING_BOUND = %1d\n", 
      ALL_CLOCK_TIMING_BOUND
    ); 
    fflush(RED_OUT); 
    #endif 

    qfd_stack = NULL;

    DEBUG_RED_COUNT = 0;
    PARSE_DEBUG_EXP = NULL;
  }
/*5*/
  processes {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      FLAG_ANY_PROCESS = -1 - PROCESS_COUNT; 
      INDEX_LOCAL_IDENTIFIER = -2 - PROCESS_COUNT; 
      FLAG_ANY_VALUE = -3 - PROCESS_COUNT;  
      FLAG_ANY_VARIABLE = -4 - PROCESS_COUNT;
      FLAG_NO_VALUE = -5 - PROCESS_COUNT;
    
      #ifdef RED_DEBUG_YACC_MODE
//      print_parse_procs();
      print_parse_variables();
      #endif 
    } 
    push_scope(SCOPE_GLOBAL); 
    
    int				i;
    struct parse_xtion_type	*px;

    /* add the null transition */
    px = (struct parse_xtion_type *) malloc(sizeof(struct parse_xtion_type));

    CURRENT_XTION = XTION_NULL = px; 
    px->index = declare_xtion_count++;
    px->src_lines = NULL; 
    px->next_parse_xtion = declare_xtion_list; 
    px->src_mode_index = px->dst_mode_index = MODE_NO_SPEC;
    px->intermediate_point_list = NULL; 
      
    declare_xtion_list = px; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\npx = %x:id=%1d\n", px, px->index);
    #endif 
    
    px->status = 0; 
    px->statement = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));
    px->statement->op = UNCHANGED; 

    px->trigger_exp = PS_EXP_TRUE;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nCURRENT_XTION->trigger_exp = %x\n", CURRENT_XTION->trigger_exp);
    #endif 
    
    sync_place_count = 0; 
    
    sysgen_qsync_var_index = 0; 
    sysgen_qsync_var_count = 0; 
    sysgen_qsync_var_limit = 100; 
    sysgen_qsync_var = (struct parse_variable_type **) 
	malloc(sysgen_qsync_var_limit * sizeof(struct parse_variable_type *)); 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_VAR_DECL; 
    DEPTH_CALL = 0; 
  } 
/*7*/
  variable_declarations {
    struct parse_variable_type	*pv; 
    
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_INLINE_DECL; 

    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 

    declare_global_synchronizer_list = parse_variable_list_reverse(
      declare_global_synchronizer_list 
    ); 
    declare_global_discrete_list = parse_variable_list_reverse(
      declare_global_discrete_list 
    ); 
    declare_global_pointer_list = parse_variable_list_reverse(
      declare_global_pointer_list 
    ); 
    declare_global_clock_list = parse_variable_list_reverse(
      declare_global_clock_list 
    ); 
    declare_global_dense_list = parse_variable_list_reverse(
      declare_global_dense_list 
    ); 
    declare_global_stream_list = parse_variable_list_reverse(
      declare_global_stream_list 
    ); 
    declare_local_synchronizer_list = parse_variable_list_reverse(
      declare_local_synchronizer_list 
    ); 
    declare_local_discrete_list = parse_variable_list_reverse(
      declare_local_discrete_list 
    ); 
    declare_stack_discrete_list = parse_variable_list_reverse(
      declare_stack_discrete_list 
    ); 
    declare_local_pointer_list = parse_variable_list_reverse(
      declare_local_pointer_list 
    ); 
    declare_local_clock_list = parse_variable_list_reverse(
      declare_local_clock_list 
    ); 
    declare_local_dense_list = parse_variable_list_reverse(
      declare_local_dense_list 
    ); 
    
    // Now we know the height of each stack frame. 
    var__sp->u.disc.lb = 0; 
    var__sp->u.disc.ub = DEPTH_CALL; 
    
    // Now append the stack discrete list to the local discrete list.  
    for (pv = declare_stack_discrete_list; 
         pv; 
         pv = pv->next_parse_variable
         ) { 
      pv->index = pv->index + LOCAL_COUNT[TYPE_DISCRETE];    
    } 
    OFFSET__RETMODE = var__retmode->index;
    STACK_START_OFFSET = LOCAL_COUNT[TYPE_DISCRETE]; 
    LOCAL_COUNT[TYPE_DISCRETE] 
    = LOCAL_COUNT[TYPE_DISCRETE] + DEPTH_CALL * count_stack_discrete; 
    HEIGHT_STACK_FRAME = count_stack_discrete; 
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      PS_EXP_MODE = ps_exp_alloc(TYPE_DISCRETE); 
      PS_EXP_MODE->var_status = FLAG_MODE | FLAG_DISCRETE | FLAG_LOCAL_VARIABLE; 
      PS_EXP_MODE->u.atom.var = var_mode; 
      PS_EXP_MODE->u.atom.var_name = var_mode->name; 
      PS_EXP_MODE->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER;  
//      PS_EXP_MODE->u.atom.indirect_vi = NULL; 
//      PS_EXP_MODE->u.atom.indirect_count = 0; 
      PS_EXP_MODE = ps_exp_share(PS_EXP_MODE); 
  
      PS_EXP__SP = ps_exp_alloc(TYPE_DISCRETE); 
      PS_EXP__SP->var_status = FLAG_DISCRETE | FLAG_LOCAL_VARIABLE; 
      PS_EXP__SP->u.atom.var = var__sp; 
      PS_EXP__SP->u.atom.var_name = var__sp->name; 
      PS_EXP__SP->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER;  
//      PS_EXP__SP->u.atom.indirect_vi = NULL; 
//      PS_EXP__SP->u.atom.indirect_count = 0; 
      PS_EXP__SP = ps_exp_share(PS_EXP__SP); 
  
      PS_EXP__SP_PLUS = exp_arith(ARITH_ADD, PS_EXP__SP, PS_EXP_ONE); 
  
      PS_EXP__SP_MINUS = exp_arith(ARITH_MINUS, PS_EXP__SP, PS_EXP_ONE); 
  
      PS_EXP__RETMODE = ps_exp_alloc(TYPE_DISCRETE); 
      PS_EXP__RETMODE->var_status = FLAG_DISCRETE | FLAG_LOCAL_VARIABLE; 
      PS_EXP__RETMODE->u.atom.var = var__retmode; 
      PS_EXP__RETMODE->u.atom.var_name = var__retmode->name; 
      PS_EXP__RETMODE->u.atom.exp_base_proc_index = PS_EXP__SP;  
//      PS_EXP__RETMODE->u.atom.indirect_vi = NULL; 
//      PS_EXP__RETMODE->u.atom.indirect_count = 0; 
      PS_EXP__RETMODE = ps_exp_share(PS_EXP__RETMODE); 
    } 
  }
  inline_exp_declarations {    
    struct ps_bunit_type	*bu, *bup;

    declare_inline_exp_list = $9; 
    // Now we reverse the order of declare_inline_exp_list.  
    bu = declare_inline_exp_list; 
    declare_inline_exp_list = NULL; 
    for (; bu; ) { 
      bup = bu->bnext; 
      bu->bnext = declare_inline_exp_list; 
      declare_inline_exp_list = bu; 
      bu = bup; 
    } 

    XTION_NULL->stream_operation_count = 0; 
    XTION_NULL->stream_operation_list = NULL; 
    XTION_NULL->sync_count = 0;
    XTION_NULL->sync_list = NULL; 
    XTION_NULL->statement = NULL; 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) | GRAM_PHASE_MODE_DECL; 
    GSTATUS[INDEX_TIME_MODE_SHAPES] 
    = GSTATUS[INDEX_TIME_MODE_SHAPES] | FLAG_TIME_MODE_ALL_TCONVEX;  
    pst9 = NULL; 
  }
/*11*/
  modes { 
    int					i, flag, lb, ub; 
    char				*name; 
    struct parse_xtion_type		*px, *pxp;
    struct parse_hyper_xtion_type	*hx;
    struct parse_assignment_type	*as;
    struct parse_mode_type		*pm, *pmp;
    struct parse_module_type		*pmdule; 
    struct parse_variable_type		*pv; 
    struct indexed_structure_link_type	*il, *til; 
    struct parse_stream_operation_type	*pso; 
    struct ps_memory_link_type		*m, *mp; 

    free(sysgen_qsync_var); 

    // Now we instantiate the lb and ub of all discrete variables. 
    instantiate_discrete_ranges(declare_global_discrete_list); 
    instantiate_discrete_ranges(declare_local_discrete_list); 
    instantiate_discrete_ranges(declare_stack_discrete_list); 
    
    // Now we reverse the order of declare_mode_list.  
    pm = declare_mode_list; 
    declare_mode_list = NULL; 
    for (; pm; ) { 
      pmp = pm->next_parse_mode; 
      pm->next_parse_mode = declare_mode_list; 
      declare_mode_list = pm; 
      pm = pmp; 
    } 
    var_mode->u.disc.lb = 0; 
    var_mode->u.disc.ub = MODE_COUNT-1; 

    var__retmode->u.disc.lb = 0; 
    var__retmode->u.disc.ub = MODE_COUNT-1; 

    // Now we reverse the order of declare_xtion_list.  
    px = declare_xtion_list; 
    declare_xtion_list = NULL; 
    for (; px; ) { 
      pxp = px->next_parse_xtion; 
      px->next_parse_xtion = declare_xtion_list; 
      declare_xtion_list = px; 
      px = pxp; 
    } 
    // Now we reverse the order of memory_list.  
    m = memory_list; 
    memory_list = NULL; 
    for (; m; ) { 
      mp = m->next_ps_memory_link; 
      m->next_ps_memory_link = memory_list; 
      memory_list = m; 
      m = mp; 
    } 
    
    PROCESS = ((struct process_type *) 
      malloc((PROCESS_COUNT+(1-DEBUG_PROCESS_OFFSET))*sizeof(struct process_type)))
      -DEBUG_PROCESS_OFFSET; 
    for (i = 1; i <= PROCESS_COUNT; i++) {
      PROCESS[i].status = FLAG_GAME_MODL; 
      PROCESS[i].name = NULL;
    }
    for (il = process_list; 
	 il; 
	 til = il, il = il->next_indexed_structure_link, free(til)
	 ) { 
      PROCESS[il->index].name = il->structure; 
    }

    /* Resolve all the GOTO references. */
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) {
        pm->invariance_exp = exp_static_evaluation(pm->invariance_exp, 
          FLAG_NO_PI_STATIC_EVAL, NULL    
        ); 
        pm->invariance_exp = pexp_remove_neg(pm->invariance_exp, TYPE_TRUE);
        pm->invariance_exp = rec_ineq_analyze(pm->invariance_exp);  
      }

      for (px = declare_xtion_list; px; px = px->next_parse_xtion) {
        struct parse_xtion_sync_type	*xs; 
      
        #ifdef RED_DEBUG_YACC_MODE
        fprintf(RED_OUT, "\n++++++++++++++++++++++++++++++++++++++\nBefore rec_static_evaluation the triggering condition:\n");
        fflush(RED_OUT); 
        fprintf(RED_OUT, "px %1d, px->status=%x\n", px->index, px->status); 
        print_parse_xtion(px, 0); 
        pcform(px->trigger_exp); 
        #endif 
      

//        red_print_time("before static eval for trigger of xi=%1d", px->index); 
        px->trigger_exp = exp_static_evaluation(px->trigger_exp, 
          FLAG_NO_PI_STATIC_EVAL, NULL    
        );
        #ifdef RED_DEBUG_YACC_MODE
        fprintf(RED_OUT, 
          "\npx %1d, after rec_static_evaluation the triggering condition:\n", 
          px->index 
        );
        pcform(px->trigger_exp);
        #endif 

        px->trigger_exp = pexp_remove_neg(px->trigger_exp, TYPE_TRUE);
//        red_print_time("after pexp_remove_neg() for trigger of xi=%1d", px->index); 
        #ifdef RED_DEBUG_YACC_MODE
        fprintf(RED_OUT, 
          "\npx %1d, after pexp_remove_neg() the triggering condition:\n", 
          px->index 
        );
        pcform(px->trigger_exp);
        #endif 

        px->trigger_exp = rec_ineq_analyze(px->trigger_exp);  
//        red_print_time("after ineq ana for trigger of xi=%1d", px->index); 
        #ifdef RED_DEBUG_YACC_MODE
        fprintf(RED_OUT, 
          "\npx %1d, after rec_ineq_analyze the triggering condition:\n", 
          px->index 
        );
        pcform(px->trigger_exp);
        #endif 
        for (pso = px->stream_operation_list; 
             pso; 
             pso = pso->next_parse_stream_operation
             ) {
          if (pso->var) { 
            pso->var = exp_static_evaluation(pso->var, 
              FLAG_NO_PI_STATIC_EVAL, NULL    
            ); 
          }    
        }   
        for(xs = px->sync_list; xs; xs = xs->next_parse_xtion_sync) { 
          if (   xs->exp_multiplicity != NULL
              && xs->exp_multiplicity != (struct ps_exp_type *) 1
              ) { 
            xs->exp_multiplicity = exp_static_evaluation(
              xs->exp_multiplicity, 
              FLAG_NO_PI_STATIC_EVAL, NULL    
            ); 
            if (xs->exp_multiplicity->type == TYPE_CONSTANT) { 
              int	sc; 
            
              for (sc = 1; sc < xs->exp_multiplicity->u.value; sc++) { 
                #ifdef RED_DEBUG_YACC_MODE
                fprintf(RED_OUT, "px = %1d, sc = %1d:%s(\n  ", 
                  px->index, sc, xs->sync_var->name
                ); 
                pcform(xs->exp_multiplicity); 
                fprintf(RED_OUT, ")\n"); 
                #endif 
              
                replicate_parse_xtion_sync(px, xs); 
              } 
            }
            else { 
              fprintf(RED_OUT, 
                "Error: transition %1d uses a dynamic multiplicity of synchronization: \n  ", 
                px->index
              ); 
              pcform(xs->exp_multiplicity); 
              fflush(RED_OUT); 
              bk(0); 
            } 
          } 
        } 
/*
        red_print_time("before static eval for stmt of xi=%1d", px->index); 
*/
        statement_static_evaluation(px, px->statement); 
        px->statement = statement_ineq_analyze(px->statement); 
/* 
        if (px->statement) 
          fprintf(RED_OUT, "\npx %1d, statement->status=%x\n",
            px->index, px->statement->status
          ); 
        else 
          fprintf(RED_OUT, "\npx %1d, statement NULL\n",
            px->index 
          ); 
        fflush(RED_OUT); 
*/          
//        red_print_time("after ineq ana for stmt of xi=%1d", px->index); 
//        fprintf(RED_OUT, "\npx %1d, dst mode index = %1d\n",
//          px->index, px->dst_mode_index
//        );  
    } }
    PARSE_INITIAL_EXP = NULL;
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) | GRAM_PHASE_INITIAL_DECL; 
  }
/*13*/
  initial { 
    PARSE_INITIAL_EXP = $13; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter parsing initial condition\n");
    pcform(PARSE_INITIAL_EXP);
    fflush(RED_OUT);
    #endif 

    ORIG_PARSE_INITIAL_EXP = $13; 
    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSE_INITIAL_EXP = exp_static_evaluation(PARSE_INITIAL_EXP, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      PARSE_INITIAL_EXP = rec_ineq_analyze(PARSE_INITIAL_EXP); 

      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nAfter static evaluating initial condition\n");
      pcform(PARSE_INITIAL_EXP);
      fflush(RED_OUT);
      #endif 
    }
    PARSE_SPEC = NULL; 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_SPEC_DECL; 
  } 
  specification { 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_DEBUG_INFOS; 
  } 
  debug {
    pop_scope(); 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_UNKNOWN; 
  };



window_drawing_options: 
  PS_WINDOW PS_LPAR PS_NUMBER PS_COMMA PS_NUMBER PS_RPAR { 
    WINDOW_WIDTH = $3; 
    WINDOW_HEIGHT = $5; 
  } 
| { 
    WINDOW_WIDTH = FLAG_WINDOW_SIZE_UNKNOWN; 
    WINDOW_HEIGHT = FLAG_WINDOW_SIZE_UNKNOWN; 
  }; 
  
  
  
  
processes : 
  PS_IDENTIFIER PS_ASSIGNMENT { 
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (strcmp($1, "count")) {
        fprintf(RED_OUT, "\nError: 'count' of processes is missing.\n");
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(0); 
      }
      if (top_scope() != SCOPE_CHOICE) {
        fprintf(RED_OUT, "\nERROR: unexpected parsing scope %s.\n", 
          scope_name(top_scope())
        ); 
        fflush(RED_OUT); 
        exit(0);  
      }
     
      change_scope(SCOPE_PROC_DECLARATION); 
      FLAG_ANY_VALUE = -1; /* This is temporary.  
			* We do this temporary setting because in the evaluation of get_value(), 
			* we will return a value that is to be compared with FLAG_ANY_VALUE.  
			* However, the value of FLAG_ANY_VALUE is to be set to -3-PROCESS_COUNT 
			* after the declaration of non-terminal `processes' and we cannot 
			* know its value at this stage. 
			* Thus we first set its value to -1 and latter will change its value to 
			* the correct one.   
			*/
    }
/*
   fprintf(RED_OUT, "\nTo analyze the process count.\n"); 
    fflush(RED_OUT); 
*/
  }
  exp_arith process_count_declaration_tail PS_SEMICOLON { 
    int	flag, original_pc; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      pop_scope(); 

      original_pc = get_value($4, 0, &flag); 
      $$ = original_pc; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn process count valuation with flag %1d from ", 
      	      flag
      	      ); 
        print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, " at line %1d.\n", lineno); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
      = (GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] & ~MASK_TEMPLATE_PROCESS_COUNT)
      | (  (original_pc * DISPLACEMENT_TEMPLATE_PROCESS_COUNT) 
         & MASK_TEMPLATE_PROCESS_COUNT
         ); 
      if (!(  GSTATUS[INDEX_TEMPLATE_PROCESS_COUNT] 
            & FLAG_TEMPLATE_PROCESS_COUNT_OVERRIDDEN
          )) 
        PROCESS_COUNT = original_pc; 
      if (PROCESS_COUNT < 1) {
        fprintf(RED_OUT, "\nError: Less than one processes. \n"); 
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(1);
      } 
    }
//    fprintf(RED_OUT, "number 7 is %1d.\n", $5); 
//    fflush(RED_OUT); 
    $$ = PROCESS_COUNT; 

    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_SIMULATE:
      DEPTH_ENUMERATIVE_SYNCHRONIZATION = 0; 
      fprintf(RED_OUT, 
        "WARNING: Enumerative depth of synchronization is forced to ZERO for task simulation.\n"
      ); 
      fprintf(RED_OUT, 
        "         This could hurt if there are quantified synchronizations in the transitions.\n"
      ); 
      fflush(RED_OUT); 
      break; 
    }
    if (GSTATUS[INDEX_COVERAGE] & MASK_COVERAGE) { 
      DEPTH_ENUMERATIVE_SYNCHRONIZATION = 0;
      fprintf(RED_OUT, 
        "WARNING: Enumerative depth of synchronization is forced to ZERO for coverage analysis.\n"
      ); 
      fprintf(RED_OUT, 
        "         This could hurt if there are quantified synchronizations in the transitions.\n"
      ); 
      fflush(RED_OUT); 
    }

    switch (DEPTH_ENUMERATIVE_SYNCHRONIZATION) { 
    case DEPTH_ENUMERATIVE_DEFAULT: 
//      DEPTH_ENUMERATIVE_SYNCHRONIZATION = 3; 
      break; 
    case DEPTH_ENUMERATIVE_ALL: 
      DEPTH_ENUMERATIVE_SYNCHRONIZATION = PROCESS_COUNT+1; 
      break; 
    default: 
      if (DEPTH_ENUMERATIVE_SYNCHRONIZATION > PROCESS_COUNT) 
        DEPTH_ENUMERATIVE_SYNCHRONIZATION = PROCESS_COUNT+1; 
      else if (DEPTH_ENUMERATIVE_SYNCHRONIZATION < DEPTH_ENUMERATIVE_ALL) 
        DEPTH_ENUMERATIVE_SYNCHRONIZATION = 3; 
      break; 
    } 
/*
    print_irregular_connection(PROCESS_COUNT); 
*/
  }; 




process_count_declaration_tail: 
  PS_COLON process_names { 
    $$ = 0; 
/*
    fprintf(RED_OUT, "\nproc name specification.\n"); 
    fflush(RED_OUT); 
*/
  }
| { 
    $$ = -1; 
/*
    fprintf(RED_OUT, "\nNO proc name specification.\n"); 
    fflush(RED_OUT); 
*/
  };



process_names : 
  PS_IDENTIFIER {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (process_name_index > PROCESS_COUNT) { 
        fprintf(RED_OUT, "\nError: More process names than PROCESS_COUNT at line %1d.\n", lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
        exit(5); 
      }
      else if (name_duplicate($1, &name_check_holder)) {
        fprintf(RED_OUT, "\nError: Duplicate process name %s at line %1d.\n", $1, lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(9); 
      }
      process_list = add_indexed_structure_count
	  	(process_list, process_name_index, $1, &process_name_index);
    } 
  }
  process_names { 
    $$ = NULL; 
  } 
| PS_IDENTIFIER {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (process_name_index > PROCESS_COUNT) {
        fprintf(RED_OUT, "\nError: More process names than PROCESS_COUNT at line %1d\n", lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(5); 
      }
      else if (name_duplicate($1, &name_check_holder)) {
        fprintf(RED_OUT, "\nError: Duplicate process name %s at line %1d.\n", $1, lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(9); 
      }
      process_list = add_indexed_structure_count(
      	process_list, process_name_index, $1, &process_name_index
    	); 
      $$ = NULL; 
    } 
  };





variable_declarations :
  variable_declaration variable_declarations 
| { 
  }; 


variable_declaration :
  PS_CALL /* 'depth' */ PS_IDENTIFIER { 
    
    if (strcmp($2, "depth")) {
      fprintf(RED_OUT, "\nError: 'depth' of procedure calls is missing.\n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      exit(0); 
    }
    else if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      push_scope(SCOPE_PROC_DECLARED); 
      FLAG_ANY_VALUE = -1; /* This is temporary.  
			* We do this temporary setting because in the evaluation of get_value(), 
			* we will return a value that is to be compared with FLAG_ANY_VALUE.  
			* However, the value of FLAG_ANY_VALUE is to be set to -3-PROCESS_COUNT 
			* after the declaration of non-terminal `processes' and we cannot 
			* know its value at this stage. 
			* Thus we first set its value to -1 and latter will change its value to 
			* the correct one.   
			*/
    }
  }
  exp_arith PS_SEMICOLON { 
    int	flag, original_dc; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      pop_scope(); 

      original_dc = get_value($4, 0, &flag); 
      $$ = original_dc; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn memory size valuation with flag %1d from ", 
      	      flag
      	      ); 
        pcform($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, " at line %1d.\n", lineno); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      DEPTH_CALL = original_dc; 
    }
//    fprintf(RED_OUT, "number 7 is %1d.\n", $5); 
    fflush(RED_OUT); 
    $$ = DEPTH_CALL; 
  } 
| PS_PARAMETER {
    change_scope(SCOPE_GLOBAL);
    CUR_VAR_TYPE = TYPE_PARAMETER;
  } variable_names PS_SEMICOLON
| stream_type PS_STREAM { 
    change_scope($1); 
    CUR_VAR_TYPE = TYPE_STREAM;
  }
  variable_names { 
    CUR_VAR_HEAD = $4; 
  }
  PS_SEMICOLON 
| PS_MEMORY optional_memory_use { 
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      push_scope(SCOPE_PROC_DECLARED); 
      FLAG_ANY_VALUE = -1; /* This is temporary.  
			* We do this temporary setting because in the evaluation of get_value(), 
			* we will return a value that is to be compared with FLAG_ANY_VALUE.  
			* However, the value of FLAG_ANY_VALUE is to be set to -3-PROCESS_COUNT 
			* after the declaration of non-terminal `processes' and we cannot 
			* know its value at this stage. 
			* Thus we first set its value to -1 and latter will change its value to 
			* the correct one.   
			*/
      CUR_VAR_TYPE = $2;
    }
  }
  exp_arith PS_SEMICOLON { 
    int	flag, original_ms; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      struct ps_memory_link_type	*m; 
      
      pop_scope(); 

      original_ms = get_value($4, 0, &flag); 
      $$ = original_ms; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn memory size valuation with flag %1d from ", 
      	      flag
      	      ); 
        pcform($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, " at line %1d.\n", lineno); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      GSTATUS[INDEX_TEMPLATE_MEMORY_SIZE] 
      = (  GSTATUS[INDEX_TEMPLATE_MEMORY_SIZE] 
         & ~MASK_TEMPLATE_MEMORY_SIZE
         )
      | (  (original_ms * DISPLACEMENT_TEMPLATE_MEMORY_SIZE) 
         & MASK_TEMPLATE_MEMORY_SIZE
         ); 

      if (original_ms < 0) {
        fprintf(RED_OUT, "\nError: Less than zero memory words. \n"); 
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(1);
      } 
      MEMORY_SIZE = MEMORY_SIZE + original_ms; 
      switch (CUR_VAR_TYPE) { 
      case TYPE_DISCRETE: 
        MEMORY_DISCRETE_SIZE = MEMORY_DISCRETE_SIZE + original_ms; 
        break; 
      case TYPE_FLOAT: 
        MEMORY_FLOAT_SIZE = MEMORY_FLOAT_SIZE + original_ms; 
        break; 
      case TYPE_DOUBLE: 
        MEMORY_DOUBLE_SIZE = MEMORY_DOUBLE_SIZE + original_ms; 
        break; 
      default: 
        bk(0); 
      } 
      m = (struct ps_memory_link_type *) 
        malloc(sizeof(struct ps_memory_link_type)); 
      m->size = original_ms; 
      m->type = CUR_VAR_TYPE; 
      m->next_ps_memory_link = memory_list; 
      memory_list = m; 
      count_memory++; 
    }
//    fprintf(RED_OUT, "number 7 is %1d.\n", $5); 
    fflush(RED_OUT); 
    $$ = MEMORY_SIZE; 
  }
| var_scope var_use {
    if ($1 == SCOPE_STACK && $2 != TYPE_DISCRETE) { 
      fprintf(RED_OUT, 
        "\nERROR: illegal non-discrete stack variable declaration at line %1d.\n", 
        lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    change_scope($1); 
    CUR_VAR_TYPE = $2; 
  }
  variable_names { 
    CUR_VAR_HEAD = $4; 
  }
  possible_discrete_range 
  ;


var_scope : 
  PS_STACK {
    $$ = SCOPE_STACK;
  }
| PS_LOCAL {
    $$ = SCOPE_LOCAL;
  }
| PS_GLOBAL {
    $$ = SCOPE_GLOBAL;
  };



optional_memory_use :
  PS_DISCRETE { 
    $$ = TYPE_DISCRETE; 
  }
| PS_FLOAT { 
    $$ = TYPE_FLOAT; 
  }
| PS_DOUBLE { 
    $$ = TYPE_DOUBLE; 
  }
| {
    $$ = TYPE_DISCRETE;
  };




var_use :
  PS_DISCRETE { 
    $$ = TYPE_DISCRETE; 
  }
/* Now the following type is not open to the users. 
| PS_POINTER { 
    $$ = TYPE_POINTER; 
  }
*/  
| PS_FLOAT { 
    $$ = TYPE_FLOAT; 
  }
| PS_DOUBLE { 
    $$ = TYPE_DOUBLE; 
  }
| PS_DENSE { 
    $$ = TYPE_DENSE; 
  }
| PS_CLOCK { 
    $$ = TYPE_CLOCK;
  }
| PS_BOOLEAN { 
    $$ = TYPE_BDD; 
  } 
| PS_SYNCHRONIZER {
    $$ = TYPE_SYNCHRONIZER;
  };

stream_type : 
  PS_ORDERED { 
    $$ = GRAM_STREAM_ORDERED; 
  } 
| PS_UNORDERED { 
    $$ = GRAM_STREAM_UNORDERED; 
  }; 


variable_names :
  variable_names PS_COMMA PS_IDENTIFIER {
    struct parse_variable_type	*pv; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      register_variable($3);
      $$ = $1;   
    } 
    else if (pv = var_search($3)) { 
      if (   pv->type != CUR_VAR_TYPE
          || (   (pv->status & FLAG_LOCAL_VARIABLE) 
              && CUR_SCOPE[TOP_SCOPE] != SCOPE_LOCAL
              ) 
          || (   (!(pv->status & FLAG_LOCAL_VARIABLE)) 
              && CUR_SCOPE[TOP_SCOPE] == SCOPE_LOCAL
              ) 
          ) { 
        fprintf(RED_OUT, 
          "\nError: a variable %s redeclared in the new rules at line %1d.\n", 
          $3, lineno
        ); 
        exit(0);   
      } 
      else { 
        fprintf(RED_OUT, "\nAn already declared variable %s at line %1d\n", 
          $3, lineno 
        ); 
      } 
    } 
    else { 
      fprintf(RED_OUT, "\nError: new variable %s declared in the new rules at line %1d.\n", 
        $3, lineno
      ); 
      fprintf(RED_OUT, "With current implementation, you need to start a new session\n"); 
      fprintf(RED_OUT, "to declare new variables. \n"); 
      bk(0); 
    } 
  }
| PS_IDENTIFIER {
    struct parse_variable_type	*pv; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      $$ = register_variable($1); 
    } 
    else if (pv = var_search($1)) { 
      if (   pv->type != CUR_VAR_TYPE
          || (   (pv->status & FLAG_LOCAL_VARIABLE) 
              && CUR_SCOPE[TOP_SCOPE] != SCOPE_LOCAL
              ) 
          || (   (!(pv->status & FLAG_LOCAL_VARIABLE)) 
              && CUR_SCOPE[TOP_SCOPE] == SCOPE_LOCAL
              ) 
          ) { 
        fprintf(RED_OUT, 
          "\nError: a variable %s redeclared in the new rules at line %1d.\n", 
          $1, lineno
        ); 
        exit(0);   
      } 
      else { 
        fprintf(RED_OUT, "\nAn already declared variable %s at line %1d\n", 
          $1, lineno 
        ); 
      } 
    } 
    else { 
      fprintf(RED_OUT, "\nError 2: new variable %s declared in the new rules at line %1d.\n", 
        $1, lineno
      ); 
      fprintf(RED_OUT, "With current implementation, you need to start a new session\n"); 
      fprintf(RED_OUT, "to declare new variables. \n"); 
      bk(0); 
    } 
  };




possible_discrete_range :
  PS_SEMICOLON {
    struct parse_variable_type	*pv;

    if (CUR_VAR_TYPE == TYPE_DISCRETE) {
      switch (top_scope()) { 
      case SCOPE_STACK: 
/*
        fprintf(RED_OUT, 
          "\ncount_debug1 = %1d; declare_stack_discrete_list = %x\n", 
          ++count_debug1, declare_stack_discrete_list
        ); 
*/
        for (pv = declare_stack_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
        }
        break; 
      case SCOPE_LOCAL: 
/*
        fprintf(RED_OUT, "\ncount_debug1 = %1d; declare_local_discrete_list = %x\n", 
          ++count_debug1, declare_local_discrete_list
        ); 
*/
        for (pv = declare_local_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
        }
        break; 
      case SCOPE_GLOBAL: 
        for (pv = declare_global_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
        } 
        break; 
      default: 
        fprintf(RED_OUT, 
          "\nERROR: Illegal scope %1d of variable declaration at line %1d.\n", 
          top_scope(), lineno
        ); 
        fflush(RED_OUT); 
        bk(0);  
      } 
    }
  }
| PS_COLON PS_ADDRESSES PS_SEMICOLON {
    struct parse_variable_type	*pv;

    if (CUR_VAR_TYPE == TYPE_DISCRETE) {
      switch (top_scope()) {
      case SCOPE_STACK: 
/*
        fprintf(RED_OUT, 
          "\ncount_debug1 = %1d; declare_stack_discrete_list = %x\n", 
          ++count_debug1, declare_stack_discrete_list
        ); 
*/
        for (pv = declare_stack_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
          pv->status = pv->status | FLAG_RANGE_ALL_VI; 
        }
        break; 
      case SCOPE_LOCAL: 
/*
        fprintf(RED_OUT, "\ncount_debug1 = %1d; declare_local_discrete_list = %x\n", 
          ++count_debug1, declare_local_discrete_list
        ); 
*/
        for (pv = declare_local_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
          pv->status = pv->status | FLAG_RANGE_ALL_VI; 
        }
        break; 
      case SCOPE_GLOBAL: 
        for (pv = declare_global_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
          pv->u.disc.lb = INT_MIN; 
          pv->u.disc.ub = INT_MAX; 
          pv->status = pv->status | FLAG_RANGE_ALL_VI; 
        }
        break; 
      default: 
        fprintf(RED_OUT, 
          "\nERROR: Illegal scope %1d of variable declaration at line %1d.\n", 
          top_scope(), lineno
        ); 
        fflush(RED_OUT); 
        bk(0);  
      } 
    }
  }
| PS_COLON  {
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  sexp_arith PS_DDOTS sexp_arith PS_SEMICOLON {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 

    pop_scope(); 
    
    if (CUR_VAR_TYPE != TYPE_DISCRETE) {
      fprintf(RED_OUT, "\nSyntax error: range declaration for non-discrete-type variable at line %1d\n", lineno); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      switch (top_scope()) { 
      case SCOPE_STACK: 
/*
        fprintf(RED_OUT, 
          "\ncount_debug1 = %1d; declare_stack_discrete_list = %x\n", 
      	  ++count_debug1, declare_stack_discrete_list
      	); 
*/
        for (pv = declare_stack_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->status = pv->status | FLAG_BOUND_DECLARED | FLAG_VAR_BOUNDS_DELAYED_EVAL; 
          pv->u.disc.lb = (int) $3; 
          pv->u.disc.ub = (int) $5; 
        }
        break; 
      case SCOPE_LOCAL: 
/*
        fprintf(RED_OUT, "\ncount_debug1 = %1d; declare_local_discrete_list = %x\n", 
      	      ++count_debug1, declare_local_discrete_list
      	      ); 
*/
        for (pv = declare_local_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
/*
          fprintf(RED_OUT, "count_debug1 = %1d; count_debug2 = %1d\n", count_debug1, ++count_debug2); 
*/
          pv->status = pv->status | FLAG_BOUND_DECLARED | FLAG_VAR_BOUNDS_DELAYED_EVAL; 
          pv->u.disc.lb = (int) $3; 
          pv->u.disc.ub = (int) $5; 
        }
        break; 
      case SCOPE_GLOBAL: 
        for (pv = declare_global_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
          pv->status = pv->status | FLAG_BOUND_DECLARED | FLAG_VAR_BOUNDS_DELAYED_EVAL; 
          pv->u.disc.lb = (int) $3; 
          pv->u.disc.ub = (int) $5; 
        } 
        break; 
      default: 
        fprintf(RED_OUT, 
          "\nERROR: Illegal scope %1d of variable declaration at line %1d.\n", 
          top_scope(), lineno
        ); 
        fflush(RED_OUT); 
        bk(0);  
      }
    }
  };



inline_exp_declarations : 
  PS_INLINE inline_exp_declaration inline_exp_declarations { 
    struct ps_bunit_type	*bu, *bup; 
    int				i; 
    struct name_link_type	*nl; 
    
    // Now we reverse the order of declare_inline_exp_list.  
    bu = declare_inline_exp_list; 
    declare_inline_exp_list = NULL; 
    for (; bu; ) { 
      bup = bu->bnext; 
      bu->bnext = declare_inline_exp_list; 
      declare_inline_exp_list = bu; 
      bu = bup; 
    } 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "There are %1d inline declarations:\n", 
      declare_inline_exp_count
    ); 
    fflush(RED_OUT); 
    for (i = 1, bu = declare_inline_exp_list; bu; i++, bu = bu->bnext) { 
      fprintf(RED_OUT, "===<inline declaration %1d>=======", i); 
      print_inline_declare(bu->subexp); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
    } 
    fprintf(RED_OUT, "\n\n"); 
    fflush(RED_OUT); 
    #endif 

    $$ = declare_inline_exp_list; 
  } 
| { 
    $$ = declare_inline_exp_list; 
  }; 



inline_exp_declaration : 
  PS_DISCRETE PS_IDENTIFIER inline_formal_argument_declaration {
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = $3; 
  } 
  PS_LCURLY exp_general PS_RCURLY { 
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
    macro_register(FLAG_INLINE_DISCRETE, $2, 
      CURRENT_INLINE_FORMAL_ARGUMENT_COUNT, 
      $3, $6
    ); 
  } 
| PS_BOOLEAN PS_IDENTIFIER inline_formal_argument_declaration {
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = $3; 
  } 
  PS_LCURLY formula PS_RCURLY { 
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
    macro_register(FLAG_INLINE_BOOLEAN, $2, 
      CURRENT_INLINE_FORMAL_ARGUMENT_COUNT, 
      $3, $6
    ); 
  }; 


inline_formal_argument_declaration: 
  PS_LPAR inline_formal_argument_list PS_RPAR {
    $$ = $2; 
  }
|
  PS_LPAR  PS_RPAR {
    $$ = NULL; 
  }
| { 
    $$ = NULL; 
  }; 
  
inline_formal_argument_list: 
  PS_IDENTIFIER PS_COMMA inline_formal_argument_list { 
    $$ = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    $$->name = $1; 
    $$->next_name_link = $3; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT++; 
  } 
| PS_IDENTIFIER { 
    $$ = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    $$->name = $1; 
    $$->next_name_link = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT++; 
  };   

modes : 
  mode modes {
    $$ = $1; 
  }
| {
    $$ = NULL; 
  }; 




mode : mode_start { 
    push_scope(SCOPE_LOCAL); 
  } 
  PS_IDENTIFIER { 
    add_mode($1, $3); 
  }
  mode_drawing_options 
  PS_LPAR local_condition PS_RPAR { 
    add_mode_invariance(CURRENT_MODE, $7); 
    CURRENT_MODE->src_lines = combine_name_cycle(
      &red_src_lines, &count_red_src_lines
    ); 
  }
  mode_rules {
    CURRENT_MODE->parse_xtion_list = $10;
    pop_scope(); 
  };


mode_start :
  PS_URGENT PS_MODE {
    $$ = FLAG_MODE_URGENT;
  }
| PS_MODE {
    $$ = 0;
  };



mode_drawing_options: 
  mode_drawing_position_option
  mode_drawing_shape_option 
  mode_drawing_color_option; 
  
  
mode_drawing_position_option: 
  PS_POSITION PS_LPAR PS_NUMBER PS_COMMA PS_NUMBER PS_RPAR { 
    CURRENT_MODE->position_x = $3; 
    CURRENT_MODE->position_y = $5; 
  }
| { 
    CURRENT_MODE->position_x = FLAG_MODE_POSITION_UNKNOWN; 
    CURRENT_MODE->position_y = FLAG_MODE_POSITION_UNKNOWN; 
  }; 



mode_drawing_shape_option: 
  PS_SHAPE PS_IDENTIFIER /* PS_RECTANGLE */
  PS_LPAR PS_NUMBER PS_COMMA PS_NUMBER PS_RPAR { 
    if (!strcmp($2, "rectangle")) {
      CURRENT_MODE->shape = FLAG_MODE_RECTANGLE; 
      CURRENT_MODE->rectangle_width = $4; 
      CURRENT_MODE->rectangle_height = $6; 
    }
    else if (!strcmp($2, "oval")) {
      CURRENT_MODE->shape = FLAG_MODE_OVAL; 
      CURRENT_MODE->oval_xradius = $4; 
      CURRENT_MODE->oval_yradius = $6; 
    }
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        $2, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  } 
| PS_SHAPE PS_IDENTIFIER PS_LPAR PS_NUMBER PS_RPAR { 
    if (!strcmp($2, "square")) {
      CURRENT_MODE->shape = FLAG_MODE_RECTANGLE; 
      CURRENT_MODE->rectangle_width = $4; 
      CURRENT_MODE->rectangle_height = $4; 
    }
    else if (!strcmp($2, "circle")) { 
      CURRENT_MODE->shape = FLAG_MODE_OVAL; 
      CURRENT_MODE->oval_xradius = $4; 
      CURRENT_MODE->oval_yradius = $4; 
    } 
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        $2, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
| PS_SHAPE PS_IDENTIFIER PS_LPAR PS_NUMBER PS_COMMA 
  shape_triangle_direction PS_RPAR { 
    if (!strcmp($2, "triangle")) {
      CURRENT_MODE->shape = FLAG_MODE_TRIANGLE; 
      CURRENT_MODE->triangle_radius = $4; 
      CURRENT_MODE->triangle_direction = $6; 
    }
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        $2, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
| {
    CURRENT_MODE->shape = FLAG_MODE_SHAPE_UNKNOWN; 
  }; 


shape_triangle_direction: 
  PS_LEFTWARD { 
    $$ = FLAG_TRIANGLE_LEFTWARD; 
  } 
| PS_RIGHTWARD { 
    $$ = FLAG_TRIANGLE_RIGHTWARD; 
  } 
| PS_UPWARD { 
    $$ = FLAG_TRIANGLE_UPWARD; 
  } 
| PS_DOWNWARD { 
    $$ = FLAG_TRIANGLE_DOWNWARD; 
  }; 

 
mode_drawing_color_option: 
  PS_COLOR PS_IDENTIFIER { 
    if (   (!strcmp($2, "red")) 
        || (!strcmp($2, "RED"))
        || (!strcmp($2, "Red"))
        ) {
      CURRENT_MODE->color = 0x000000FF;  
    }
    else if (   (!strcmp($2, "white")) 
             || (!strcmp($2, "WHITE"))
             || (!strcmp($2, "White"))
             ) { 
      CURRENT_MODE->color = 0xFFFFFFFF;  
    }
    else if (   (!strcmp($2, "black")) 
             || (!strcmp($2, "BLACK"))
             || (!strcmp($2, "Black"))
             ) {  
      CURRENT_MODE->color = 0x00000000;  
    }
    else if (   (!strcmp($2, "blue")) 
             || (!strcmp($2, "BLUE"))
             || (!strcmp($2, "Blue"))
             ) { 
      CURRENT_MODE->color = 0x00FF0000;  
    }
    else if (   (!strcmp($2, "yellow")) 
             || (!strcmp($2, "YELLOW"))
             || (!strcmp($2, "Yellow"))
             ) { 
      CURRENT_MODE->color = 0x0000FF00;  
    }
    else if (   (!strcmp($2, "green")) 
             || (!strcmp($2, "GREEN"))
             || (!strcmp($2, "Green"))
             ) { 
      CURRENT_MODE->color = 0x00FFFF00;  
    }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: unsupported symbolic color name %s at line %1d.\n", 
        $2, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
| PS_COLOR PS_HEX_NUMBER {
    CURRENT_MODE->color = $1;  
  } 
| { 
    CURRENT_MODE->color = 0xFFFFFFFF;  
  }; 



   
mode_rules :
  PS_LCURLY
  rules
  PS_RCURLY {
    $$ = $2;
  }
| PS_LCURLY PS_RCURLY {
    $$ = NULL;
  };


rules :
  rule rules {
    struct parse_xtion_link_type	*pxl;
    if ($1 == NULL)
      $$ = $2;
    else {
      pxl = (struct parse_xtion_link_type *) malloc(sizeof(struct parse_xtion_link_type));
      pxl->parse_xtion = $1;
      pxl->next_parse_xtion_link = $2;
      CURRENT_MODE->xtion_count++;

      $$ = pxl;
    }
  }
| { 
    $$ = NULL; 
  } ;


rule :
  PS_RATE vrate vrates PS_SEMICOLON { $$ = NULL; }
| xtion {
    $$ = $1;
  };



vrates :
  PS_COMMA vrate vrates
| {
    $$ = 0;  
  };

vrate :
  token_variable PS_COLON sexp_arith {
    struct parse_rate_spec_link_type	*rsl;

    rsl = (struct parse_rate_spec_link_type *) malloc(sizeof(struct parse_rate_spec_link_type));
    rsl->rate_var_name = $1->pvar->name;
    rsl->rate_var = $1->pvar; 
    if (rsl->rate_var == NULL) {
      fprintf(RED_OUT, "Syntax error: an undeclared variable NULL in rate specification at line %1d.\n",
	lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    else switch (rsl->rate_var->type) {
    case TYPE_DISCRETE:
    case TYPE_POINTER:
      fprintf(RED_OUT, 
	      "Syntax error: an uncontinuous variable %s in rate specification at line %1d.\n",
	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    case TYPE_CLOCK:
      fprintf(RED_OUT, "Syntax error: clock %s with rate specificaiton at line %1d.\n",
	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
      break;
    case TYPE_DENSE:
      if (!(rsl->rate_var->status & FLAG_LOCAL_VARIABLE)) {
        fprintf(RED_OUT, "Error: illegal rate specification to global dense variable %s at line %1d.\n",
		$1->pvar->name, lineno
		);
	fflush(RED_OUT);
	exit(0);
      }
      break;
    default:
      fprintf(RED_OUT, "Syntax error: an incompatible variable %s for rate specification at line %1d.\n",
 	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }

    rsl->next_parse_rate_spec_link = CURRENT_MODE->parse_rate_spec_list;
    CURRENT_MODE->parse_rate_spec_list = rsl;
    CURRENT_MODE->rate_spec_count++;

    rsl->rate_lb = rsl->rate_ub = $3;
    rsl->status = ~(FLAG_RATE_LB_OPEN | FLAG_RATE_UB_OPEN);
  }
| token_variable PS_COLON lbrac sexp_arith PS_COMMA sexp_arith rbrac {
    struct parse_rate_spec_link_type	*rsl;

    rsl = (struct parse_rate_spec_link_type *) malloc(sizeof(struct parse_rate_spec_link_type));
    rsl->rate_var_name = $1->pvar->name;
    rsl->rate_var = $1->pvar;
    if (rsl->rate_var == NULL) {
      fprintf(RED_OUT, "Syntax error: an undeclared variable %s in rate specification at line %1d.\n",
	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    else switch (rsl->rate_var->type) {
    case TYPE_DISCRETE:
    case TYPE_POINTER:
      fprintf(RED_OUT, "Syntax error: an uncontinuous variable %s in rate specification at line %1d.\n",
	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    case TYPE_CLOCK:
      fprintf(RED_OUT, "Syntax error: clock %s with rate specification at line %1d.\n",
	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
      break;
    case TYPE_DENSE:
      if (!(rsl->rate_var->status & FLAG_LOCAL_VARIABLE)) {
        fprintf(RED_OUT, "Error: illegal rate specification to global dense variable %s at line %1d.\n",
		$1->pvar->name, lineno
		);
	fflush(RED_OUT);
	exit(0);
      }
      break;
    default:
      fprintf(RED_OUT, "Syntax error: an incompatible variable %s for rate specification at line %1d.\n",
 	      $1->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }

    rsl->next_parse_rate_spec_link = CURRENT_MODE->parse_rate_spec_list;
    CURRENT_MODE->parse_rate_spec_list = rsl;
    CURRENT_MODE->rate_spec_count++;


    if ($3 == INTERVAL_LEFT_OPEN) {
      rsl->status = rsl->status | FLAG_RATE_LB_OPEN;
      fprintf(RED_OUT, "\nError: left open bounds in rate specification at line %1d.\n", lineno);
      fflush(RED_OUT);
      exit(0);
    }
    else
      rsl->status = rsl->status & ~FLAG_RATE_LB_OPEN;

    if ($7 == INTERVAL_RIGHT_OPEN) {
      rsl->status = rsl->status | FLAG_RATE_UB_OPEN;
      fprintf(RED_OUT, "\nError: right open bounds in rate specification at line %1d.\n", lineno);
      fflush(RED_OUT);
      exit(0);
    }
    else
      rsl->status = rsl->status & ~FLAG_RATE_UB_OPEN;

    rsl->rate_lb = $4;
    rsl->rate_ub = $6;
  };





xtion :
  PS_WHEN {
    int				i;
    struct parse_xtion_type	*px;

    px = (struct parse_xtion_type *) malloc(sizeof(struct parse_xtion_type));

    CURRENT_XTION = px;
    CURRENT_XTION->status = 0; 

    CURRENT_XTION->src_lines = combine_name_cycle(
      &red_src_lines, &count_red_src_lines
    ); 

    px->index = declare_xtion_count++;
    if (px->index == 1) 
      tpx = px; 
/*
    fprintf(RED_OUT, "\nparsing px %1d\n", px->index); 
    fflush(RED_OUT); 
    if (px->index == 4) 
      X14 = px; 
*/
    px->next_parse_xtion = declare_xtion_list;
    px->src_mode_index 
    = px->dst_mode_index 
/* We now assume that all procedure-calls are handled with preprocessors. 
 *
    = px->calling_mode_index 
    = px->return_mode_index 
*/
    = MODE_NO_SPEC; 
    declare_xtion_list = px;
    
    CURRENT_XTION->src_mode = CURRENT_MODE; 

    /*
    fprintf(RED_OUT, "\npx = %x:id=%1d\n", px, px->index);
    */
    px->sync_count = 0;
    px->sync_list = NULL; 

    px->statement = NULL; 
    
    CURRENT_XTION_SYNC_COUNT = 0; 
    
    push_scope(SCOPE_LOCAL_XTION); 
    sysgen_qsync_var_index = 0; 
  } 
  xtion_points {
    CURRENT_XTION->stream_operation_count = 0; 
    CURRENT_XTION->stream_operation_list = NULL; 
  }
  stream_operations {
    CURRENT_XTION->stream_operation_list = $5; 
  }
  trigger_condition {
    struct ps_bunit_type	*bunitptr, dummy_bu; 
    struct ps_exp_type		*mode_predicate; 
    
    bunitptr = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*
    fprintf(RED_OUT, "bunitptr = %x in xtion rule for var_mode\n", bunitptr); 
    */
    CURRENT_XTION->orig_trigger_exp = $7;     
    mode_predicate = exp_arith(ARITH_EQ, 
      exp_atom(TYPE_DISCRETE, -1, var_mode->name),  
      exp_atom(TYPE_CONSTANT, CURRENT_MODE->index, NULL)
    ); 
    /*
    fprintf(RED_OUT, "yacc literal 2 : TRIGGERING MODE INEQUALITY\n"); 
    fprintf(RED_OUT, "\noriginal triggering condition :\n"); 
    print_parse_subformula_structure(CURRENT_XTION->trigger_exp, 0); 
    */

    CURRENT_XTION->trigger_exp = exp_boolean(AND, $7, mode_predicate); 
/*
    fprintf(RED_OUT, "\nremoved-neg triggering condition :\n");
    print_parse_subformula_structure(CURRENT_XTION->trigger_exp, 0); 
*/
    CURRENT_XTION->src_mode_index 
    = CURRENT_XTION->dst_mode_index 
    = CURRENT_MODE->index; 
    
    if (sync_place_count < CURRENT_XTION->sync_count) 
      sync_place_count = CURRENT_XTION->sync_count; 
  } 
  actions { 
    CURRENT_XTION->statement = $9; 
    $$ = CURRENT_XTION;
    --TOP_SCOPE; 
    
    if (CURRENT_XTION->index == 9) {
      pst9 = CURRENT_XTION; 
    }
  }; 




xtion_points: 
  PS_POINT { 
    LENGTH_CURRENT_POINT_LIST = 0; 
  } 
  point_list PS_SEMICOLON { 
    CURRENT_XTION->intermediate_point_list = $3; 
    CURRENT_XTION->intermediate_point_count = LENGTH_CURRENT_POINT_LIST; 
    fprintf(RED_OUT, "\nyacc: After analyzing point list.\n"); 
    fflush(RED_OUT); 
  } 
| { 
    CURRENT_XTION->intermediate_point_list = NULL; 
    CURRENT_XTION->intermediate_point_count = 0; 
  }; 



point_list: PS_LPAR signed_number PS_COMMA signed_number PS_RPAR point_list { 
    struct index_pair_link_type	*ip; 

    ip = (struct index_pair_link_type *) 
      malloc(sizeof(struct index_pair_link_type)); 
    ip->next_index_pair_link = $6; 
    ip->coordinate_x = $2; 
    ip->coordinate_y = $4; 

    LENGTH_CURRENT_POINT_LIST++; 
    $$ = ip; 
  } 
| { 
    $$ = NULL; 
  }; 


stream_operations : 
  stream_operation stream_operations { 
    $1->next_parse_stream_operation = $2; 
    CURRENT_XTION->stream_operation_count++; 
    $$ = $1; 
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\nredgram: new xi=%1d, soc=%1d, so-op=%1d\n", 
      CURRENT_XTION->index, 
      CURRENT_XTION->stream_operation_count, 
      $$->operation
    ); 
    fflush(RED_OUT);  
    #endif 
  } 
| { 
    $$ = NULL; 
  }; 

stream_operation : 
  PS_OPEN PS_INPUT PS_VARIABLE PS_SEMICOLON { 
    struct parse_stream_operation_type	*pso; 
    
    if (CURRENT_TOKEN_VAR->type != TYPE_STREAM) { 
      fprintf(RED_OUT, "\nSyntax error: illegal file variable %s at line %1d.\n", 
        CURRENT_TOKEN_VAR->name, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    pso = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type)); 
    pso->stream = CURRENT_TOKEN_VAR; 
    pso->operation = OP_STREAM_OPEN_INPUT; 
    pso->var = NULL; 
    pso->value_exp = NULL; 
    
    $$ = pso; 
  } 
| PS_OPEN PS_OUTPUT PS_VARIABLE PS_SEMICOLON { 
    struct parse_stream_operation_type	*pso; 
    
    if (CURRENT_TOKEN_VAR->type != TYPE_STREAM) { 
      fprintf(RED_OUT, "\nSyntax error: illegal file variable %s at line %1d.\n", 
        CURRENT_TOKEN_VAR->name, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    pso = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type)); 
    pso->stream = CURRENT_TOKEN_VAR; 
    pso->operation = OP_STREAM_OPEN_OUTPUT; 
    pso->var = NULL; 
    pso->value_exp = NULL; 
    
    $$ = pso; 
  } 
| PS_CLOSE PS_VARIABLE PS_SEMICOLON { 
    struct parse_stream_operation_type	*pso; 
    
    if (CURRENT_TOKEN_VAR->type != TYPE_STREAM) { 
      fprintf(RED_OUT, "\nSyntax error: illegal file variable %s at line %1d.\n", 
        CURRENT_TOKEN_VAR->name, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    pso = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type)); 
    pso->stream = CURRENT_TOKEN_VAR; 
    pso->operation = OP_STREAM_CLOSE; 
    pso->var = NULL; 
    pso->value_exp = NULL; 
    
    $$ = pso; 
  } 
| PS_MALLOC PS_LPAR exp_arith PS_RPAR PS_FROM_STREAM assign_dest PS_SEMICOLON { 
    switch ($6->type) { 
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE: 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nSyntax error: at line %1d, illegal malloc operation destination:\n  ", lineno);
      pcform($6); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = NULL; 
    CURRENT_STREAM_OP->operation = OP_MALLOC; 

    CURRENT_STREAM_OP->var = $6; 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation($3, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    $$ = CURRENT_STREAM_OP; 
  } 
| PS_FREE exp_arith PS_SEMICOLON { 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = NULL; 
    CURRENT_STREAM_OP->operation = OP_FREE; 

    CURRENT_STREAM_OP->var = NULL; 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation($2, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    $$ = CURRENT_STREAM_OP; 
  } 
| PS_INPUT PS_VARIABLE { 
    if (CURRENT_TOKEN_VAR->type != TYPE_STREAM) { 
      fprintf(RED_OUT, "\nSyntax error: illegal stream variable %s at line %1d.\n", 
        CURRENT_TOKEN_VAR->name, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = CURRENT_TOKEN_VAR; 
    CURRENT_STREAM_OP->operation = OP_STREAM_INPUT; 
  }
  PS_FROM_STREAM assign_dest PS_SEMICOLON { 
    CURRENT_STREAM_OP->var = $5; 
    switch (CURRENT_STREAM_OP->var->type) { 
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE: 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nSyntax error: at line %1d, illegal stream operation destination:", 
        lineno 
      );
      pcform($5); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP->value_exp = NULL; 
    $$ = CURRENT_STREAM_OP; 
  } 
| PS_OUTPUT PS_VARIABLE { 
    if (CURRENT_TOKEN_VAR->type != TYPE_STREAM) { 
      fprintf(RED_OUT, "\nSyntax error: illegal stream variable %s at line %1d.\n", 
        CURRENT_TOKEN_VAR->name, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = CURRENT_TOKEN_VAR; 
    CURRENT_STREAM_OP->operation = OP_STREAM_OUTPUT; 
  }
  PS_TO_STREAM exp_arith PS_SEMICOLON { 
    CURRENT_STREAM_OP->var = NULL; 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation($5, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    $$ = CURRENT_STREAM_OP; 
  };  

actions : 
  PS_MAY {
    change_scope(SCOPE_LOCAL); 
/*
    fprintf(RED_OUT, "\nEntering action parsing:\n"); 
    fflush(RED_OUT); 
*/
  }
  statements { 
    $$ = $3; 
  }; 




trigger_condition : 
  synchronizations PS_LPAR local_condition PS_RPAR 
  {
    struct parse_xtion_sync_type	*xs; 
    struct ps_exp_type			*addr, *qs, *eq; 
    
    $$ = $3; 
    // The following loop is to translate all address enforcers to 
    // address holders in case that there are dynamic variables in 
    // the enforcer expressions.  
    for (xs = CURRENT_XTION->sync_list; xs; xs = xs->next_parse_xtion_sync) { 
      if (   xs->exp_quantification 
          && (xs->status & MASK_SYNC_ADDRESS) != FLAG_ADDRESS_HOLDER  
          && xs->exp_quantification->type != TYPE_QSYNC_HOLDER 
	  && (xs->exp_quantification->var_status & FLAG_EXP_STATE_INSIDE)
          ) { 
/*
        fprintf(RED_OUT, "Error: dynamic synchronization destination at line %1d \n", 
	        lineno
	        ); 
        fprintf(RED_OUT, "       are not supported at this moment.\n"); 
        exit(0); 
*/
        addr = xs->exp_quantification; 
        xs->exp_quantification = ps_exp_alloc(TYPE_QSYNC_HOLDER); 
        CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
        push_scope(SCOPE_LOCAL); 
        xs->status = (xs->status & ~MASK_SYNC_ADDRESS) | FLAG_ADDRESS_HOLDER; 
        xs->exp_quantification->u.qsholder.place_index = xs->place_index; 
        xs->exp_quantification->u.qsholder.place_holder_var = xs->place_holder_var; 
        xs->exp_quantification->u.qsholder.qsync_var 
        = xs->qsync_var 
        = get_a_sysgen_qsync_var();  
        xs->exp_quantification->u.qsholder.qsync_var_name = xs->qsync_var->name; 
    	pop_scope(); 
        CURRENT_XTION->status 
        = CURRENT_XTION->status | FLAG_XTION_QUANTIFIED_SYNC; 
        GSTATUS[INDEX_SYNCHRONIZATION] 
        = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_SYSTEM_QUANTIFIED_SYNC; 
        
        qs = ps_exp_alloc(TYPE_QSYNC_HOLDER); 
        qs->u.qsholder.place_index = xs->place_index; 
        qs->u.qsholder.place_holder_var = xs->place_holder_var; 
        qs->u.qsholder.qsync_var = xs->exp_quantification->u.qsholder.qsync_var; 
        qs->u.qsholder.qsync_var_name = xs->exp_quantification->u.qsholder.qsync_var->name; 
        eq = exp_arith(ARITH_EQ, qs, addr); 
        eq = ineq_analyze(eq); 
        $$ = exp_boolean(AND, eq, $$); 
/*
        RED_OUT = stdout; 
        fprintf(RED_OUT, 
          "\nThe new triggering condition after substituting sysgen qsync var %s at line %1d.\n", 
	  xs->qsync_var->name, lineno 
	); 
	print_parse_subformula_structure($$, 0); 
//	print_parse_subformula($$, FLAG_GENERAL_PROCESS_IDENTIFIER); 
	fprintf(RED_OUT, "\n"); 
*/
      }
    } 
  }
| PS_LPAR local_condition PS_RPAR 
  {
    $$ = $2; 
  }
;

synchronizations : 
  synchronization synchronizations 
| synchronization 
;


synchronization :
  event_direction token_sync sync_address { 
    CURRENT_XTION->sync_list 
    = add_parse_xtion_sync(
      CURRENT_XTION_SYNC_COUNT, flag_address_type, 
      $1, $2, (struct ps_exp_type *) 1, $3
    ); 
    CURRENT_XTION_SYNC_COUNT++; 
  }
| event_direction PS_LPAR exp_arith PS_RPAR token_sync { 
    CURRENT_XTION->sync_list 
    = add_parse_xtion_sync(
      CURRENT_XTION_SYNC_COUNT++, 
      FLAG_ADDRESS_MULTIPLE, 
      $1, $5, $3, NULL
    ); 
  };


event_direction: 
  PS_EXCLAMATION { 
    $$ = -1; 
  } 
| PS_TO_STREAM { 
    $$ = -1; 
  } 
| PS_QUESTION { 
    $$ = 1; 
  } 
| PS_FROM_STREAM { 
    $$ = 1; 
  }; 

sync_address : 
  PS_BIRD PS_LPAR { 
    push_scope(SCOPE_ADDRESS_ENFORCER); 
  } 
  exp_arith PS_RPAR {
    struct exp_shape_type	*es; 

    switch ((es = exp_shape_check($4))->type) { 
    case FLAG_EXP_STATIC: 
      free(es); 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nERROR: At line %1d, illegal dynamic correspondence: ", 
        lineno
      ); 
      pcform($4); 
      fprintf(RED_OUT, 
        "       in synchronization.\n"
      ); 
      free(es); 
      fflush(RED_OUT); 
      exit(0); 
    }
    $$ = $4; 
    CURRENT_TOKEN_VAR = NULL; 
    flag_address_type = FLAG_ADDRESS_ENFORCER; 
    --TOP_SCOPE; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  } 
| PS_BIRD PS_IDENTIFIER {
    int	flag; 
    
    $$ = ps_exp_alloc(TYPE_QSYNC_HOLDER); 
/*
    if (CURRENT_XTION->index == 1600) { 
      fprintf(RED_OUT, "Target prehit!\n"); 
      fflush(RED_OUT); 
      for (flag = 1; flag; ); 
    } 
*/
    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    push_scope(SCOPE_LOCAL); 
    $$->u.qsholder.place_index = CURRENT_XTION_SYNC_COUNT; 
    $$->u.qsholder.qsync_var_name = $2; 
    $$->u.qsholder.qsync_var = check_register_qfd_sync($2); 
    $$->var_status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
    flag_address_type = FLAG_ADDRESS_HOLDER; 
    pop_scope(); 
    $$ = ps_exp_share($$); 
    CURRENT_XTION->status = CURRENT_XTION->status | FLAG_XTION_QUANTIFIED_SYNC; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYSTEM_QUANTIFIED_SYNC 
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  }
| PS_BIRD PS_VARIABLE {
    int	flag; 

    check_qfd_sync(CURRENT_TOKEN_VAR); 

    $$ = ps_exp_alloc(TYPE_QSYNC_HOLDER); 

    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    push_scope(SCOPE_LOCAL); 
    $$->u.qsholder.place_index = CURRENT_XTION_SYNC_COUNT; 
    $$->u.qsholder.qsync_var_name = CURRENT_TOKEN_VAR->name; 
    $$->u.qsholder.qsync_var = CURRENT_TOKEN_VAR; 
    $$->var_status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
    flag_address_type = FLAG_ADDRESS_HOLDER; 
    pop_scope(); 
    $$ = ps_exp_share($$); 
    CURRENT_XTION->status = CURRENT_XTION->status | FLAG_XTION_QUANTIFIED_SYNC; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYSTEM_QUANTIFIED_SYNC  
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  }
| {
    $$ = NULL; 
    flag_address_type = FLAG_ADDRESS_NULL; 
  }; 

statements :
  statement statements { 
    struct parse_statement_link_type	*stl, *stlp; 
    struct parse_statement_type		*er, *e1, *e2; 
        
    e1 = $1; 
    e2 = $2; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "sequential statement at line %1d.\n1: ", lineno); 
    print_parse_statement_line(e1); 
    fprintf(RED_OUT, "\n2: "); 
    print_parse_statement_line(e2); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
    
    if ($1 == NULL) 
      $$ = $2; 
    else if ($2 == NULL) 
      $$ = $1; 
    else if ($1->op == ST_SEQ) 
      if ($2->op == ST_SEQ) { 
        for (stl = $1->u.seq.statement_list; 
             stl->next_parse_statement_link; 
             stl = stl->next_parse_statement_link
             ) ; 
        stl->next_parse_statement_link = $2->u.seq.statement_list; 
        $1->u.seq.statement_count 
        = $1->u.seq.statement_count + $2->u.seq.statement_count; 
        $1->st_status = ($1->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ($2->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        free($2); 
        $$ = $1; 
      } 
      else {
        for (stl = $1->u.seq.statement_list; stl->next_parse_statement_link; stl = stl->next_parse_statement_link) ;        
        stl->next_parse_statement_link = (struct parse_statement_link_type *) 
                                         malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link->next_parse_statement_link = NULL; 
        stl->next_parse_statement_link->statement = $2; 
        $1->u.seq.statement_count++; 
        $1->st_status = ($1->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ($2->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        $$ = $1; 
      }
    else 
      if ($2->op == ST_SEQ) { 
        stl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link = $2->u.seq.statement_list; 
        stl->statement = $1; 
        $2->u.seq.statement_list = stl; 
        $2->u.seq.statement_count++; 
        $2->st_status 
        = ($1->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ($2->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        $$ = $2; 
      } 
      else {
        stl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stlp = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link = stlp; 
        stl->statement = $1; 
        stlp->next_parse_statement_link = NULL; 
        stlp->statement = $2; 
        $$ = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
        $$->op = ST_SEQ; 
        $$->st_status 
        = ($1->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ($2->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        $$->u.seq.statement_list = stl;         
	$$->u.seq.statement_count = 2; 
      }
/*
    er = $$; 
*/
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparse seq statements %x, status=%x\n", $$, $$->status); 
    print_parse_statement_line($$); 
    fprintf(RED_OUT, "\n"); 
    fprintf(RED_OUT, "\n  1st statement %x, status=%x\n  ", $1, $1->status); 
    print_parse_statement_line($1); 
    fprintf(RED_OUT, "\n"); 
    fprintf(RED_OUT, "\n  2nd statement %x, status=%x\n  ", $2, $2->status); 
    print_parse_statement_line($2); 
    fprintf(RED_OUT, "\n"); 
    
    fflush(RED_OUT); 
    #endif 
  } 
| statement { 
    $$ = $1; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparse action=%x, status=%x\n", $$, $$->status); 
    print_parse_statement_line($$); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
  };



statement : 
  PS_SEMICOLON {
    $$ = NULL; 
  } 
| assignment { 
    $$ = $1; 
  } 
| system_info { 
    $$ = NULL; 
  } 
| PS_LCURLY statements PS_RCURLY {
    $$ = $2; 
  }
| PS_IF PS_LPAR local_condition PS_RPAR statement PS_ELSE statement { 
    struct parse_statement_type	*st; 
    
    $$ = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    $$->op = ST_IF; 
    $$->st_status 
    = ($5->st_status & ~MASK_STATEMENT_COMPOUND) 
    | ($7->st_status & ~MASK_STATEMENT_COMPOUND) 
    | FLAG_STATEMENT_COMPOUND
    | FLAG_STATEMENT_ELSE; 
    $$->u.branch.cond = $3; 
    $$->u.branch.if_statement = $5; 
    $$->u.branch.else_statement = $7; 
/*
    print_parse_statement_line(st, 1); 
*/
  } 
| PS_IF PS_LPAR local_condition PS_RPAR statement { 
    struct parse_statement_type	*st; 
    
    $$ = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    $$->op = ST_IF; 
    $$->st_status = ($5->st_status & ~MASK_STATEMENT_COMPOUND) 
	       | FLAG_STATEMENT_COMPOUND; 
    $$->u.branch.cond = $3; 
    $$->u.branch.if_statement = $5; 
    $$->u.branch.else_statement = NULL; 
/*
    print_parse_statement_line(st, 1); 
*/
  } 
| PS_WHILE PS_LPAR local_condition PS_RPAR statement { 
    struct parse_statement_type	*st; 
    
    $$ = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    $$->op = ST_WHILE; 
    $$->st_status 
    = ($5->st_status & ~MASK_STATEMENT_COMPOUND) | FLAG_STATEMENT_COMPOUND; 
    $$->u.loop.cond = $3; 
    $$->u.loop.statement = $5; 
/*
    print_parse_statement_line(st, 1); 
*/
  }; 
  


// QQQQQQQQQQQQQQQq
// We need to have FLAG_INDIRECTION PASSED ON TO THE ACTIONS. 
assignment :
  PS_GOTO PS_IDENTIFIER PS_SEMICOLON { 
  // This is for forward declaration reference of mode names. 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    /*
    fprintf(RED_OUT, "\nvc = %x for goto\n", vc);
    */
    as->u.act.term = (struct parse_term_type *) malloc(sizeof(struct parse_term_type));
    as->u.act.lhs = as->u.act.term[0].operand = ps_exp_alloc(TYPE_DISCRETE);

    as->op = ASSIGN_DISCRETE_CONSTANT; 
    as->lineno = lineno; 
    as->st_status = 0; 
    as->u.act.lhs->u.atom.var = var_mode;
    as->u.act.lhs->var_status = var_mode->status; 
    as->u.act.lhs->exp_status = 0; 
    as->u.act.lhs->u.atom.exp_base_proc_index = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER); 
    as->u.act.lhs->u.atom.exp_base_proc_index 
    = ps_exp_share(as->u.act.lhs->u.atom.exp_base_proc_index); 
    
    as->u.act.lhs->u.atom.var_name = var_mode->name; /* temporally set this way and changed after all mode names are read. */ 
/*
    fprintf(RED_OUT, "Catching transiton %1d: parsing a GOTO with destination name %s\n", 
	    CURRENT_XTION->index, $2
	    ); 
    fflush(RED_OUT); 
*/
//    as->u.act.lhs->u.atom.indirect_count = 0;
//    as->u.act.lhs->u.atom.indirect_exp = NULL;
    as->u.act.lhs = ps_exp_share(as->u.act.lhs); 
//    tpsubve(as->u.act.lhs); 
    exp_mode = as->u.act.lhs; 
    
    as->u.act.term_count = 1;
    as->u.act.term = (struct parse_term_type *) malloc(sizeof(struct parse_term_type));
    as->u.act.term[0].operand = as->u.act.lhs;
    as->u.act.term[0].coeff = ps_exp_alloc(TYPE_CONSTANT);
    as->u.act.term[0].coeff->u.value = 1;
    as->u.act.term[0].coeff = ps_exp_share(as->u.act.term[0].coeff); 
    
    as->u.act.rhs_exp = ps_exp_alloc(TYPE_MODE_INDEX);
    as->u.act.rhs_exp->u.mode_index.value = 0; 
    as->u.act.rhs_exp->u.mode_index.mode_name = $2; 
    as->u.act.rhs_exp->u.mode_index.parse_mode = NULL; 
    as->u.act.rhs_exp 
    = as->u.act.offset 
    = ps_exp_share(as->u.act.rhs_exp); 
    
    $$ = as;
  } 
| PS_CALL PS_IDENTIFIER PS_IDENTIFIER PS_IDENTIFIER PS_SEMICOLON { 
    struct parse_statement_type	*as;

    if (strcmp($3, "to")) { 
      fprintf(RED_OUT, "\nError: 'to' of procedure calls return mode is missing.\n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      exit(0); 
    } 
    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CALL; 
    as->lineno = lineno; 
    as->u.call.call_mode_name = $2; 
    as->u.call.call_mode_index = -1; 
    as->u.call.ret_mode_name = $4; 
    as->u.call.ret_mode_index = -1; 
    $$ = as;
  } 
| PS_CALL PS_IDENTIFIER PS_SEMICOLON { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_RETURN; 
    as->lineno = lineno; 
    as->u.call.call_mode_name = $2; 
    as->u.call.call_mode_index = -1; 
    as->u.call.ret_mode_name = CURRENT_MODE->name; 
    as->u.call.ret_mode_index = -1; 
    $$ = as;
  } 
| PS_RETURN { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_RETURN; 
    as->lineno = lineno; 
    $$ = as;
  } 
| PS_GUARD PS_LPAR local_condition PS_RPAR PS_SEMICOLON { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_GUARD; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.guard.cond = $3; 
    $$ = as;
  } 
| PS_ERASE assign_dest PS_SEMICOLON { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_ERASE; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.erase.var = $2; 
    $$ = as;
  } 
| assign_dest PS_ASSIGNMENT PS_CPLUG pure_number pure_number PS_SEMICOLON { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CPLUG; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.cplug.lhs = $1; 
    as->u.cplug.cmod_index = $4; 
    as->u.cplug.cproc_index = $5; 
    $$ = as;
  } 
| PS_CPLUG pure_number pure_number PS_SEMICOLON { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CPLUG; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.cplug.lhs = NULL; 
    as->u.cplug.cmod_index = $2; 
    as->u.cplug.cproc_index = $3; 
    $$ = as;
  } 
| assign_dest PS_IN lbrac lbound PS_COMMA rbound rbrac PS_SEMICOLON {
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));
    as->st_status = 0; 
    if (   ($1->var_status & FLAG_QUANTIFIED_SYNC) 
        || ($4 && ($4->var_status & FLAG_QUANTIFIED_SYNC)) 
        || ($6 && ($6->var_status & FLAG_QUANTIFIED_SYNC)) 
        ) 
      as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    if (   ($1->exp_status & FLAG_INDIRECTION) 
        || ($4 && ($4->exp_status & FLAG_INDIRECTION)) 
        || ($6 && ($6->exp_status & FLAG_INDIRECTION)) 
        ) 
      as->st_status = as->st_status | FLAG_ACTION_INDIRECTION; 

    if (   check_lhs_pco($1, $4) 
        || check_lhs_pco($1, $6) 
        ) {
      as->st_status = as->st_status | FLAG_ACTION_LHS_RECURSION; 
      as->u.act.lhs = ps_exp_copy($1);
      as->u.act.lhs = ps_exp_share(as->u.act.lhs); 
    }
    else 
      as->u.act.lhs = $1;
    
    switch (as->u.act.lhs->type) {
    case TYPE_DENSE:
      as->op = ASSIGN_HYBRID_EXP;
      break;
    case TYPE_CLOCK:
      as->op = ASSIGN_CLOCK_MIXED;
      break;
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE:
    case TYPE_POINTER:
      as->op = ASSIGN_DISCRETE_CONSTANT;
      break;
    }

    as->u.act.rhs_exp 
    = as->u.act.offset 
    = ps_exp_alloc(TYPE_INTERVAL);
    as->u.act.rhs_exp->u.interval.status = 0;
    as->u.act.rhs_exp->u.interval.status
    = as->u.act.rhs_exp->u.interval.status | $3;
    as->u.act.rhs_exp->u.interval.lbound_exp = $4;
    if (!$4) {
      as->u.act.rhs_exp->u.interval.status 
      = as->u.act.rhs_exp->u.interval.status | INTERVAL_LEFT_UNBOUNDED;
      if (!(as->u.act.rhs_exp->u.interval.status & INTERVAL_LEFT_OPEN)) {
        fprintf(RED_OUT, "Error: a negative infinity is used in left-closed interval at line %1d\n",
                lineno
                );
        fflush(RED_OUT);
        exit(0);
      }
    }
    as->u.act.rhs_exp->u.interval.status 
    = as->u.act.rhs_exp->u.interval.status | $7;
    as->u.act.rhs_exp->u.interval.rbound_exp = $6;
    if (!$6) {
      as->u.act.rhs_exp->u.interval.status 
      = as->u.act.rhs_exp->u.interval.status | INTERVAL_RIGHT_UNBOUNDED;
      if (!(as->u.act.rhs_exp->u.interval.status & INTERVAL_RIGHT_OPEN)) {
        fprintf(RED_OUT, "Error: a positive infinity is used in right-closed interval at line %1d\n",
                lineno
                );
        fflush(RED_OUT);
        exit(0);
      }
    }
    
    as->u.act.term_count = 1;
    as->u.act.term = (struct parse_term_type *) malloc(sizeof(struct parse_term_type));
    as->u.act.term[0].operand = as->u.act.lhs;
    as->u.act.term[0].coeff = ps_exp_alloc(TYPE_CONSTANT);
    as->u.act.term[0].coeff->u.value = 1; 
    as->u.act.term[0].coeff = ps_exp_share(as->u.act.term[0].coeff); 
/*
    print_parse_subformula_structure(as->u.act.rhs_exp, 0);
    fprintf(RED_OUT, "\n");
*/

    /* Adjust the open bounds to closed bounds for discrete variables. 
     */ 
    switch (as->u.act.lhs->type) {
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE:
    case TYPE_POINTER:
      if (as->u.act.rhs_exp->u.interval.status & INTERVAL_LEFT_UNBOUNDED) { 
        as->u.act.rhs_exp->u.interval.status 
        = as->u.act.rhs_exp->u.interval.status 
        & ~(INTERVAL_LEFT_UNBOUNDED | INTERVAL_LEFT_OPEN); 
        as->u.act.rhs_exp->u.interval.lbound_exp 
        = exp_atom(TYPE_CONSTANT, as->u.act.lhs->u.atom.var->u.disc.lb, NULL); 
      }
      else if (as->u.act.rhs_exp->u.interval.status & INTERVAL_LEFT_OPEN) { 
        struct ps_exp_type	*offset, *org; 
        
        as->u.act.rhs_exp->u.interval.status 
        = as->u.act.rhs_exp->u.interval.status & ~INTERVAL_LEFT_OPEN; 
        org = as->u.act.rhs_exp->u.interval.lbound_exp; 
        offset = PS_EXP_ONE; 
        as->u.act.rhs_exp->u.interval.lbound_exp = ps_exp_alloc(ARITH_ADD); 
        as->u.act.rhs_exp->u.interval.lbound_exp->u.arith.lhs_exp = org; 
        as->u.act.rhs_exp->u.interval.lbound_exp->var_status = org->var_status; 
        as->u.act.rhs_exp->u.interval.lbound_exp->exp_status = org->exp_status; 
        as->u.act.rhs_exp->u.interval.lbound_exp->u.arith.rhs_exp = offset; 
      }
      if (as->u.act.rhs_exp->u.interval.status & INTERVAL_RIGHT_UNBOUNDED) { 
        as->u.act.rhs_exp->u.interval.status 
        = as->u.act.rhs_exp->u.interval.status 
        & ~(INTERVAL_RIGHT_UNBOUNDED | INTERVAL_RIGHT_OPEN); 
        as->u.act.rhs_exp->u.interval.rbound_exp 
        = exp_atom(TYPE_CONSTANT, as->u.act.lhs->u.atom.var->u.disc.ub, NULL); 
      }
      else if (as->u.act.rhs_exp->u.interval.status & INTERVAL_RIGHT_OPEN) { 
        struct ps_exp_type	*offset, *org; 
        
        as->u.act.rhs_exp->u.interval.status 
        = as->u.act.rhs_exp->u.interval.status & ~INTERVAL_RIGHT_OPEN; 
        org = as->u.act.rhs_exp->u.interval.rbound_exp; 
        offset = PS_EXP_ONE; 
        as->u.act.rhs_exp->u.interval.rbound_exp = ps_exp_alloc(ARITH_MINUS); 
        as->u.act.rhs_exp->u.interval.rbound_exp->u.arith.lhs_exp = org; 
        as->u.act.rhs_exp->u.interval.rbound_exp->var_status = org->var_status; 
        as->u.act.rhs_exp->u.interval.rbound_exp->exp_status = org->exp_status; 
        as->u.act.rhs_exp->u.interval.rbound_exp->u.arith.rhs_exp = offset; 
      } 
      break;
    }
    as->u.act.rhs_exp = as->u.act.offset = ps_exp_share(as->u.act.rhs_exp); 
    $$ = as;
  }
|
  assign_dest PS_ASSIGNMENT exp_general PS_SEMICOLON {
    struct parse_statement_type *as;
    int				flag_increment_conversion; 

/*
    fprintf(RED_OUT, "\n%1d%:Testing status %1d of RHS of type %1d.\n", count_debug1++, $4->status, $4->type); 
*/
    if ($3->exp_status & FLAG_EXP_MODAL_INSIDE) { 
      fprintf(RED_OUT, 
        "Error: modal operators in process assignment RHS type %1d at line %1d.\n", 
	$3->type, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (   (   $1->type == TYPE_DISCRETE 
                 || $1->type == TYPE_POINTER 
                 || $1->type == TYPE_DENSE 
                 || $1->type == TYPE_CLOCK
                 )
             && $1->u.atom.var == NULL
             ) {
      fprintf(RED_OUT, 
        "\nError: a null variable or a macro constant %s on LHS at line %1d\n",
	$1->u.atom.var_name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    else { 
/*
      fprintf(RED_OUT, 
        "\nassignment lhs with exp_base_proc_index status %x: ", 
        $1->u.atom.exp_base_proc_index->status 
      ); 
*/
    }
/*
    pcform($1); 
    fflush(RED_OUT); 
*/
    flag_increment_conversion = TYPE_FALSE; 
    switch ($3->type) { 
    case ARITH_ADD:  
      if ($3->u.arith.lhs_exp == $1) { 
        flag_increment_conversion = TYPE_TRUE; 
        $$ = add_increment(INCREMENT_BY_CONSTANT, 
          $1, $3->u.arith.rhs_exp
        ); 
      } 
      else if ($3->u.arith.rhs_exp == $1) { 
        flag_increment_conversion = TYPE_TRUE; 
        $$ = add_increment(INCREMENT_BY_CONSTANT, 
          $1, $3->u.arith.lhs_exp 
        ); 
      } 
      break; 
    case ARITH_MINUS: 
      if ($3->u.arith.lhs_exp == $1) { 
        flag_increment_conversion = TYPE_TRUE; 
        $$ = add_increment(DECREMENT_BY_CONSTANT, 
          $1, $3->u.arith.rhs_exp
        ); 
      } 
      break; 
    }  
    if (!flag_increment_conversion) { 
      as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));
      /*
      fprintf(RED_OUT, "\nvc = %x for y:= c\n", vc);
      */
      as->st_status = 0; 
      if (   ($1->var_status & FLAG_QUANTIFIED_SYNC) 
          || ($3->var_status & FLAG_QUANTIFIED_SYNC) 
          ) 
        as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
      if (   ($1->exp_status & FLAG_INDIRECTION) 
          || ($3->exp_status & FLAG_INDIRECTION) 
          ) 
        as->st_status = as->st_status | FLAG_ACTION_INDIRECTION; 
      if (check_lhs_pco($1, $3)) {
        as->st_status = as->st_status | FLAG_ACTION_LHS_RECURSION; 
        as->u.act.lhs = ps_exp_copy($1);
        as->u.act.lhs = ps_exp_share(as->u.act.lhs); 
      }
      else 
        as->u.act.lhs = $1;

      as->u.act.rhs_exp = $3;
      compose_assignment_status(as); 
/*
      fprintf(RED_OUT, "\nparsing status of general assignment %x:\n", 
        as->status
      ); 
      print_parse_subformula($1, 0); 
      fprintf(RED_OUT, " = "); 
      print_parse_subformula($3, 0); 
      fprintf(RED_OUT, ";\n"); 
      fflush(RED_OUT); 
*/
      $$ = as;
    }
  }
|
  assign_dest
  PS_INC
  PS_NUMBER PS_SEMICOLON {
    /*
    fprintf(RED_OUT, "\nvc = %x for y:= c\n", vc);
    */
    if ($1->u.atom.var->type != TYPE_DISCRETE && $1->u.atom.var->type != TYPE_POINTER) {
      fprintf(RED_OUT,
        "\nError: Increment on a non-discrete variable %s at line %1d.\n", 
        $1->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(8);
    }
    else if (!($1->u.atom.var->status & FLAG_BOUND_DECLARED)) {
      fprintf(RED_OUT, 
        "\nError: Increment on a discrete variable %s without declared bounds at line %1d\n",
	$1->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(9);
    }

    $$ = add_increment(INCREMENT_BY_CONSTANT, 
      $1, exp_atom(TYPE_CONSTANT, $3, NULL)
    ); 
  }
|
  assign_dest
  PS_DEC
  PS_NUMBER PS_SEMICOLON {
    struct parse_statement_type 	*as;

    /*
    fprintf(RED_OUT, "\nvc = %x for y:= c\n", vc);
    */
    if ($1->u.atom.var->type != TYPE_DISCRETE && $1->u.atom.var->type != TYPE_POINTER) {
      fprintf(RED_OUT, 
        "\nError: Increment on a non-discrete variable %s at line %1d.\n", 
        $1->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(8);
    }
    else if (!($1->u.atom.var->status & FLAG_BOUND_DECLARED)) {
      fprintf(RED_OUT, "\nError: Increment on a discrete variable %s without declared bounds at line %1d\n",
	      $1->u.atom.var->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(9);
    }

    $$ = add_increment(DECREMENT_BY_CONSTANT, 
      $1, exp_atom(TYPE_CONSTANT, $3, NULL)
    ); 
  };




pure_number: 
  PS_NUMBER { 
    $$ = $1; 
  } 
| PS_MACRO_CONSTANT { 
    struct ps_exp_type	*mc; 
    
    mc = $1->u.inline_declare.declare_exp; 
    fprintf(RED_OUT, "\nmacro constant parsed: "); 
    pcform(mc); 
    $$ = $1->u.inline_declare.declare_exp->u.value; 
  }; 


lbrac:
  PS_LBRAC {
    $$ = INTERVAL_LEFT_CLOSED;
  }
| PS_LPAR {
    $$ = INTERVAL_LEFT_OPEN;
  };

rbrac:
  PS_RBRAC {
    $$ = INTERVAL_LEFT_CLOSED;
  }
| PS_RPAR {
    $$ = INTERVAL_RIGHT_OPEN;
  };

lbound:
  PS_MINUS PS_INFINITY {
    $$ = NULL;
  }
| exp_arith {
    if ($1->var_status & (FLAG_DENSE | FLAG_CLOCK)) { 
      fprintf(RED_OUT, "Error: dense left bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if ($1->var_status & FLAG_SYNCHRONIZER) { 
      fprintf(RED_OUT, "Error: event left bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    $$ = $1;
  };

rbound:
  PS_INFINITY {
    $$ = NULL;
  }
| exp_arith {
    if ($1->var_status & (FLAG_DENSE | FLAG_CLOCK)) { 
      fprintf(RED_OUT, "Error: dense right bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if ($1->var_status & FLAG_SYNCHRONIZER) { 
      fprintf(RED_OUT, "Error: event right bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    $$ = $1;
  };





assign_dest:
  PS_MULTIPLY PS_NUMBER { 
    $$ = ps_exp_alloc(TYPE_REFERENCE); 
    $$->u.exp = ps_exp_alloc(TYPE_CONSTANT); 
    $$->var_status = FLAG_DISCRETE; 
    $$->exp_status = FLAG_CONSTANT; 
    $$->u.exp->u.value = $2; 
  } 
| PS_MULTIPLY PS_LPAR exp_arith PS_RPAR { 
    $$ = ps_exp_alloc(TYPE_REFERENCE); 
    $$->var_status = $3->var_status | FLAG_DISCRETE; 
    $$->exp_status = $3->exp_status; 
    $$->u.exp = $3; 
  }
| PS_MULTIPLY assign_dest { 
    $$ = ps_exp_alloc(TYPE_REFERENCE); 
    $$->var_status = $2->var_status | FLAG_DISCRETE; 
    $$->exp_status = $2->exp_status; 
    $$->u.exp = $2; 
  } 
| complete_operand {
    $$ = $1;
    if(   $1->type != TYPE_CLOCK 
       && $1->type != TYPE_POINTER
       && $1->type != TYPE_DISCRETE
       && $1->type != TYPE_FLOAT
       && $1->type != TYPE_DOUBLE
       && (   $1->type != TYPE_DENSE 
           || ($1->u.atom.var->status & FLAG_VAR_STATIC)
           ) 
       && $1->type != TYPE_REFERENCE 
       ) {
      fprintf(RED_OUT, 
        "Syntax error: a non-variable in the left-hand-side at line %1d.\n", 
        lineno
      ); 
      print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nget a complete operand %x: ", $$->status); 
    pcform($$); 
    fflush(RED_OUT); 
    #endif 
  }; 





/*********************************************************************
 *
 *	Grammar rules for IF statement condition
 */
local_condition : {
    push_scope(SCOPE_LOCAL); 
  }
  formula {  
    pop_scope(); 
    $$ = $2;
/*
    fprintf(RED_OUT,"===(Local conditions)=========================\n");
    print_parse_subformula_structure($$, 0);
    fprintf(RED_OUT,"\n");
    fflush(RED_OUT);
    print_parse_subformula($$, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n\n\n"); 
    fflush(RED_OUT); 
*/
  };




multiplicative_op:
  PS_MULTIPLY {
    $$ = ARITH_MULTIPLY;
  }
| PS_DIVIDE {
    $$ = ARITH_DIVIDE;
  }
| PS_MODULO {
    $$ = ARITH_MODULO;
  };







/*****************************************************************
 *
 * Specifications
 */
initial :
  PS_INITIAL { 
/*
    fprintf(RED_OUT, "************ INITIAL ***************************\n"); 
*/
    spec_size = 0; 
    push_scope(SCOPE_GLOBAL); 
  }
  global_condition PS_SEMICOLON {
    $$ = $3;
    pop_scope(); 
  };



specification :
  PS_CHECK PS_DEADLOCK PS_SEMICOLON {
    int	pi; 
    
    if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE) {
      spec_size = 0;
      GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_DEADLOCK;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "deadlock";
    }
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES)
      			 | FLAG_GAME_MODL; 
    } 
  }
| PS_CHECK PS_ZENO PS_SEMICOLON {
    int	pi; 
    
    if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE) {
      spec_size = 0; 
      GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_ZENO;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "zeno";
    }
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES)
      			 | FLAG_GAME_MODL; 
    } 
  }
|
  PS_CHECK PS_BRANCHING PS_BISIMULATION {
    int	pi; 

    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
        		    | TASK_BRANCHING_BISIM_CHECKING;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS;
      TASK_TYPE_NAME = "branching bisimulation";
    } 
    CUR_GAME_ROLE = FLAG_GAME_MODL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = PROCESS[pi].status & ~MASK_GAME_ROLES; 
    } 
    setup_game_exp(); 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*5*/ { 
    change_scope(SCOPE_GLOBAL); 
  }
  fairness /*7*/ PS_SEMICOLON /*8*/ {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, $7); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game model fairness:\n"); 
    pcform(GAME_MODL_EXP); 
    fprintf(RED_OUT, "\nEnd of model role sequence.\n"); 
    fflush(RED_OUT);
    #endif 

    GAME_MODL_EXP = exp_static_evaluation(GAME_MODL_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_MODL_EXP = rec_ineq_analyze(GAME_MODL_EXP); 
    GAME_MODL_EXP = analyze_tctl(GAME_MODL_EXP, 0, 0);
    CUR_GAME_ROLE = FLAG_GAME_SPEC; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nEnd of model role spec.\n"); 
    fflush(RED_OUT); 
    #endif 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*10*/ { 
    change_scope(SCOPE_GLOBAL); 
  } 
  fairness /*12*/ PS_SEMICOLON /*13*/ { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, $12); 
    GAME_SPEC_EXP = exp_static_evaluation(GAME_SPEC_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_SPEC_EXP = rec_ineq_analyze(GAME_SPEC_EXP); 
    GAME_SPEC_EXP = analyze_tctl(GAME_SPEC_EXP, 0, 0);
    if (  GAME_SPEC_EXP->u.mexp.strong_fairness_count
        + GAME_SPEC_EXP->u.mexp.weak_fairness_count 
        > 1
        ) { 
      fprintf(RED_OUT, 
        "\nError: Detection of simulation checking of specification automata \n"
      ); 
      fprintf(RED_OUT, 
        "       of type general Buechi automata \n"
      ); 
      fprintf(RED_OUT, 
        "       with %1d strong and %1d weak fairness assumptions.\n", 
        GAME_SPEC_EXP->u.mexp.strong_fairness_count, 
        GAME_SPEC_EXP->u.mexp.weak_fairness_count
      ); 
      fprintf(RED_OUT, 
        "       Sorry!  It is really not a bug. \n"
      ); 
      fprintf(RED_OUT, 
        "       At this moment, we only support the simulation checking of \n"
      ); 
      fprintf(RED_OUT, 
        "       a model general Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       against a specificaiton Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       with either one strong or one weak fairness assumption. \n\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game spec fairness:\n"); 
    pcform(GAME_SPEC_EXP); 
    #endif 
    push_scope(SCOPE_GLOBAL); 
  } 
  fairness /*15*/ { 
    int	pi; 
  
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, $15); 
    GAME_ENVR_EXP = exp_static_evaluation(GAME_ENVR_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_ENVR_EXP = rec_ineq_analyze(GAME_ENVR_EXP); 
    GAME_ENVR_EXP = analyze_tctl(GAME_ENVR_EXP, 0, 0);
    TYPE_PARSE_CHOICE = TYPE_PARSE_GAME_ROLES; 
    GAME_FAIRNESS_EXP = merge_fairness_exps(GAME_MODL_EXP, GAME_SPEC_EXP); 
    GAME_FAIRNESS_EXP = ps_exp_share(GAME_FAIRNESS_EXP); 
    $$ = NULL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      if (!(PROCESS[pi].status & MASK_GAME_ROLES))
        PROCESS[pi].status = PROCESS[pi].status | FLAG_GAME_ENVR; 
    } 

    fprintf(RED_OUT, "Sorry that equivalence checking has not been implemented so far.\n"); 
    exit(0); 

  } 
|
  PS_CHECK PS_BRANCHING PS_SIMULATION {
    int	pi; 

    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
        		    | TASK_BRANCHING_SIM_CHECKING;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS;
      TASK_TYPE_NAME = "branching simulation"; 
    }
    CUR_GAME_ROLE = FLAG_GAME_MODL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = PROCESS[pi].status & ~MASK_GAME_ROLES; 
    } 
    setup_game_exp(); 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*5*/ { 
    change_scope(SCOPE_GLOBAL); 
  }
  fairness /*7*/ PS_SEMICOLON /*8*/ {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, $7); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game model fairness:\n"); 
    pcform(GAME_MODL_EXP); 
    fprintf(RED_OUT, "\nEnd of model role sequence.\n"); 
    fflush(RED_OUT);
    #endif 

    GAME_MODL_EXP = exp_static_evaluation(GAME_MODL_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_MODL_EXP = rec_ineq_analyze(GAME_MODL_EXP); 
    GAME_MODL_EXP = analyze_tctl(GAME_MODL_EXP, 0, 0);
    CUR_GAME_ROLE = FLAG_GAME_SPEC; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nEnd of model role spec.\n"); 
    fflush(RED_OUT); 
    #endif 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  game_proc_indices /*10*/ { 
    change_scope(SCOPE_GLOBAL); 
  } 
  fairness /*12*/ PS_SEMICOLON /*13*/ { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, $12); 
    GAME_SPEC_EXP = exp_static_evaluation(GAME_SPEC_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_SPEC_EXP = rec_ineq_analyze(GAME_SPEC_EXP); 
    GAME_SPEC_EXP = analyze_tctl(GAME_SPEC_EXP, 0, 0);
    if (  GAME_SPEC_EXP->u.mexp.strong_fairness_count
        + GAME_SPEC_EXP->u.mexp.weak_fairness_count 
        > 1
        ) { 
      fprintf(RED_OUT, 
        "\nError: Detection of simulation checking of specification automata \n"
      ); 
      fprintf(RED_OUT, 
        "       of type general Buechi automata \n"
      ); 
      fprintf(RED_OUT, 
        "       with %1d strong and %1d weak fairness assumptions.\n", 
        GAME_SPEC_EXP->u.mexp.strong_fairness_count, 
        GAME_SPEC_EXP->u.mexp.weak_fairness_count
      ); 
      fprintf(RED_OUT, 
        "       Sorry!  It is really not a bug. \n"
      ); 
      fprintf(RED_OUT, 
        "       At this moment, we only support the simulation checking of \n"
      ); 
      fprintf(RED_OUT, 
        "       a model general Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       against a specificaiton Buechi automaton  \n"
      ); 
      fprintf(RED_OUT, 
        "       with either one strong or one weak fairness assumption. \n\n"
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter filling the game spec fairness:\n"); 
    pcform(GAME_SPEC_EXP); 
    #endif 
    push_scope(SCOPE_GLOBAL); 
  }  
  fairness /*15*/  { 
    int	pi; 
  
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, $15); 
    GAME_ENVR_EXP = exp_static_evaluation(GAME_ENVR_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_ENVR_EXP = rec_ineq_analyze(GAME_ENVR_EXP); 
    GAME_ENVR_EXP = analyze_tctl(GAME_ENVR_EXP, 0, 0);
    TYPE_PARSE_CHOICE = TYPE_PARSE_GAME_ROLES; 
    GAME_FAIRNESS_EXP = merge_fairness_exps(GAME_MODL_EXP, GAME_SPEC_EXP); 
    GAME_FAIRNESS_EXP = ps_exp_share(GAME_FAIRNESS_EXP); 
    $$ = NULL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      if (!(PROCESS[pi].status & MASK_GAME_ROLES))
        PROCESS[pi].status = PROCESS[pi].status | FLAG_GAME_ENVR; 
    } 

    fprintf(RED_OUT, "Sorry that equivalence checking has not been implemented so far.\n"); 
    exit(0); 

  } 
| task_type { 
    int	pi; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "task type is %1d\n", GSTATUS[INDEX_TASK] & MASK_TASK); 
    #endif 
    
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_MODEL_CHECK: 
      push_scope(SCOPE_GLOBAL_EVENT); 
      break; 
    default: 
      push_scope(SCOPE_GLOBAL); 
      break; 
    } 
    spec_size = 0;
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES)
      			 | FLAG_GAME_MODL; 
    } 
  }
  global_condition PS_SEMICOLON {
    $$ = $3; 
    
    pop_scope(); 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_MODEL_CHECK: 
      CUR_VAR_TYPE = TYPE_DISCRETE; 
      break; 
    }
  }
| PS_REDLIB PS_SESSION PS_SEMICOLON { 
    int	pi; 
    
    spec_size = 0; 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
                        | TASK_REDLIB_SESSION;
    TASK_TYPE_NAME = "redlib session"; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES)
      			 | FLAG_GAME_MODL; 
    } 
  } 
| {
    int	pi; 
    
    spec_size = 0; 
    GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) 
                        | TASK_REDLIB_SESSION;
    TASK_TYPE_NAME = "redlib session"; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES)
      			 | FLAG_GAME_MODL; 
    } 
    PARSE_SPEC = NULL; 
  };


task_type :
  PS_TCTL { 
    if ((GSTATUS[INDEX_TASK] & MASK_TASK) == TASK_SIMULATE) {
      fprintf(RED_OUT, "\nAt this moment, our simulator only supports risk/goal monitoring.\n");
      fprintf(RED_OUT, "No monitoring on TCTL formulae is supported.\n");
      exit(0);
    }
    else if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
             && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
             ) {
      GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_MODEL_CHECK;
      TASK_TYPE_NAME = "model-checking";
    }
  }
|
  PS_GOAL { 
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "goal";
    } 
  }
|
  PS_SIMULATE {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SIMULATE;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "monitored";
    }
  }
|
  PS_RISK { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "entering risk specification!\n"); 
    #endif 
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_RISK;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "risk";
    }
  }
|
  PS_SAFETY {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SAFETY;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "safety";
    }
  }
|
  PS_PARAMETRIC PS_RISK {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK)
			| TASK_RISK | FLAG_PARAMETRIC_ANALYSIS
			| FLAG_FULL_REACHABILITY;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "risk";
    }
  }
|
  PS_PARAMETRIC PS_SAFETY {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK)
			| TASK_SAFETY | FLAG_PARAMETRIC_ANALYSIS
			| FLAG_FULL_REACHABILITY;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "safety";
    }
  }
|
  PS_CONSTRUCT PS_LOCAL {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK)
			| TASK_SAFETY;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "local redgram construction"; 
    }
  }
;


debug :
  PS_DEBUG { 
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_STRONG; 
  } 
  global_fairness_sequence
  {
    int					i;
    struct ps_fairness_link_type	*psl, *tpsl;

    DEBUG_RED_COUNT = PARSE_GLOBAL_SEQ_COUNT;
    PARSE_DEBUG_EXP = (struct ps_exp_type **) malloc(DEBUG_RED_COUNT * sizeof(struct ps_exp_type *));
    for (i = 0, psl = $3;
	 i < DEBUG_RED_COUNT;
	 i++, tpsl = psl, psl = psl->next_ps_fairness_link, free(tpsl)
	 ) {
      PARSE_DEBUG_EXP[i] = psl->fairness;
      if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
          > FLAG_MODEL_PARSING_ONLY
          ) {
        PARSE_DEBUG_EXP[i] = exp_static_evaluation(PARSE_DEBUG_EXP[i], 
          FLAG_NO_PI_STATIC_EVAL, NULL    
        ); 
        PARSE_DEBUG_EXP[i] = rec_ineq_analyze(PARSE_DEBUG_EXP[i]); 
    } }
    $$ = $3;
  }
| { 
/*
    printf("it is an empty debug sequence\n"); 
*/
    $$ = NULL;
/*
    printf("this should be the end of the input string. \n"); 
*/
  }
  ;


game_proc_indices : nontrivial_game_proc_indices 
| { 
  }; 


nontrivial_game_proc_indices: 
  exp_arith PS_COMMA nontrivial_game_proc_indices {
    int	pi, flag_addr; 
    
    pi = get_value($1, 0, &flag_addr); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGet a proc spec index %1d from ", pi); 
    print_parse_subformula($1, 0); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
    
    if (   flag_addr != FLAG_SPECIFIC_VALUE 
        || pi <= 0 
        || pi > PROCESS_COUNT
        ) { 
      fprintf(RED_OUT, "ERROR: Process index %1d out of range at line %1d.\n", pi, lineno); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (   (PROCESS[pi].status & MASK_GAME_ROLES) 
	     && ((PROCESS[pi].status & MASK_GAME_ROLES) != CUR_GAME_ROLE)
	     ) { 
      fprintf(RED_OUT, "ERROR: Process role conflict at line %1d.\n", lineno); 
      fflush(RED_OUT); 
      exit(0);     
    } 
    else {
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES) | CUR_GAME_ROLE; 
    }
  }
| exp_arith { 
    int	pi, flag_addr; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nexp %1d in proc indices:", ++count_pi_arith); 
    pcform($1); 
    fflush(RED_OUT); 
    #endif 

    pi = get_value($1, 0, &flag_addr); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGet a proc spec index %1d from ", pi); 
    print_parse_subformula($1, 0); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
    
    if (   flag_addr != FLAG_SPECIFIC_VALUE 
        || pi <= 0 
        || pi > PROCESS_COUNT
        ) { 
      fprintf(RED_OUT, "ERROR: Process index %1d out of range at line %1d.\n", pi, lineno); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    else if (   (PROCESS[pi].status & MASK_GAME_ROLES) 
	     && ((PROCESS[pi].status & MASK_GAME_ROLES) != CUR_GAME_ROLE)
	     ) { 
      fprintf(RED_OUT, "ERROR: Process role conflict at line %1d.\n", lineno); 
      fflush(RED_OUT); 
      exit(0);     
    } 
    else {
      PROCESS[pi].status = (PROCESS[pi].status & ~MASK_GAME_ROLES) | CUR_GAME_ROLE; 
    }
  }; 

global_condition : {
  } 
  formula { 
    /* fprintf(RED_OUT, "yacc s1 : imply expression\n");
    print_parse_subformula($2, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    $$ = $2;
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  }; 
  
formula : 
  fmla_imply {
    /* fprintf(RED_OUT, "yacc s1 : imply expression\n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    $$ = $1;
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  }
| 
  fmla_disjlist { 
    /* fprintf(RED_OUT, "yacc s2 : disj list\n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    $$ = $1;
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  };



fmla_imply :
  fmla_disjlist
  { /* fprintf(RED_OUT, "yacc implyexp : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
  }
  PS_IMPLY
  fmla_disjlist
  { struct ps_bunit_type	*bhead, *btail;

  /*    fprintf(RED_OUT, "yacc implyexp : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER);
  */
    $$ = ps_exp_alloc(IMPLY);
    $$->var_status = $1->var_status | $4->var_status; 
    $$->exp_status = $1->exp_status | $4->exp_status | FLAG_NEGATION_INSIDE | FLAG_DISJUNCTION_INSIDE; 
    spec_size++;
    formula_connector_count++; 
    bhead = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*     fprintf(RED_OUT, "\nbhead = %x\n", bhead);
     */
    bhead->subexp = $1;
    btail = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*     fprintf(RED_OUT, "\nbtail = %x\n", btail); 
     */
    btail->subexp = $4;
    bhead->bnext = btail;
    btail->bnext = NULL;
    $$->u.bexp.blist = bhead;
    $$->u.bexp.len = 2; 
    /* newpstree($$); */
    $$ = ps_exp_share($$); 
/*
    fprintf(RED_OUT, "parsing IMPLY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
  };



fmla_disjlist :
  fmla_conjlist  
  { /* fprintf(RED_OUT, "yacc disjlist : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    */
  }
  PS_OR
  fmla_disjlist
  { struct ps_bunit_type *bunitptr, dummy_bu;

  /*    fprintf(RED_OUT, "yacc disjlist : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  */
    if ($4->type == OR) { 
      $$ = ps_exp_copy($4); 
      $$->var_status = $1->var_status | $4->var_status; 
      $$->exp_status = $1->exp_status | $4->exp_status | FLAG_DISJUNCTION_INSIDE; 
      dummy_bu.bnext = $$->u.bexp.blist; 
      insert_sorted_blist_dummy_head(OR, 
        $1, &dummy_bu, &($$->u.bexp.len)
      ); 
      $$->u.bexp.blist = dummy_bu.bnext; 
    }
    else { 
      int	bcount; 
      
      bcount = 0; 
      spec_size++;
      formula_connector_count++;
      dummy_bu.bnext = NULL;  
      insert_sorted_blist_dummy_head(OR, $1, &dummy_bu, &bcount); 
      insert_sorted_blist_dummy_head(OR, $4, &dummy_bu, &bcount); 
      switch (bcount) { 
      case 0: 
        $$ = PS_EXP_FALSE; 
        break; 
      case 1: 
        $$ = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        break; 
      case 2: 
        $$ = ps_exp_alloc(OR);
        $$->var_status = $1->var_status | $4->var_status; 
        $$->exp_status = $1->exp_status | $4->exp_status | FLAG_DISJUNCTION_INSIDE; 
        $$->u.bexp.blist = dummy_bu.bnext; 
        $$->u.bexp.len = 2; 
      }
    }
    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing OR: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  }
| fmla_conjlist
  { $$ = $1;
  /*    fprintf(RED_OUT, "yacc disjlist : (3) \n"); 
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    
    fprintf(RED_OUT, "\nParsing a conjunctive formula!\n");
    print_parse_subformula_structure($$, 0); 
  */
  };



fmla_conjlist :
  fmla_conj  
  { /* fprintf(RED_OUT, "yacc conjlsit : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    */
  }
  PS_AND 
  fmla_conjlist
  { struct ps_bunit_type *bunitptr, dummy_bu;

  /*    fprintf(RED_OUT, "yacc disjlist : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  */
    if ($4->type == AND) { 
      $$ = ps_exp_copy($4); 
      $$->var_status = $1->var_status | $4->var_status; 
      $$->exp_status = $1->exp_status | $4->exp_status | FLAG_CONJUNCTION_INSIDE; 
      dummy_bu.bnext = $$->u.bexp.blist; 
      insert_sorted_blist_dummy_head(AND, $1, &dummy_bu, &($$->u.bexp.len)); 
      $$->u.bexp.blist = dummy_bu.bnext; 
    }
    else { 
      int	bcount; 
      
      bcount = 0; 
      spec_size++;
      formula_connector_count++;
      dummy_bu.bnext = NULL;  
      insert_sorted_blist_dummy_head(AND, $1, &dummy_bu, &bcount); 
      insert_sorted_blist_dummy_head(AND, $4, &dummy_bu, &bcount); 
      switch (bcount) { 
      case 0: 
        $$ = PS_EXP_TRUE; 
        break; 
      case 1: 
        $$ = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        break; 
      case 2: 
        $$ = ps_exp_alloc(AND);
        $$->var_status = $1->var_status | $4->var_status; 
        $$->exp_status = $1->exp_status | $4->exp_status | FLAG_CONJUNCTION_INSIDE; 
        $$->u.bexp.blist = dummy_bu.bnext; 
        $$->u.bexp.len = 2; 
      }
    }
    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing OR: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  } 
| fmla_conj
  { /* 
    fprintf(RED_OUT, "yacc conjlist : (4) conj\n"); 
    pcform($1); 
    fflush(RED_OUT); 
    */ 
    $$ = $1;
  };




fmla_conj : 
  PS_LPAR formula PS_RPAR { 
    $$ = $2;
    /* newpstree($$); */
  }
| PS_EXCLAMATION fmla_conj { 
    $$ = ps_exp_alloc(NOT);
    $$->var_status = $2->var_status; 
    $$->exp_status = $2->exp_status | FLAG_NEGATION_INSIDE; 
    spec_size++;
    formula_connector_count++; 
    $$->u.bexp.blist = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*    fprintf(RED_OUT, "\n$$->u.bexp.blist = %x\n",$$->u.bexp.blist); 
     */
    $$->u.bexp.len = 1;
    $$->u.bexp.blist->subexp = $2;
    $$->u.bexp.blist->bnext = NULL;

    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing NOT: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  }
| PS_RESET PS_IDENTIFIER { 
    check_choice_formula_global();  
    CUR_VAR_TYPE = TYPE_CLOCK; 
    register_variable($2);
  }
  fmla_conj {
    $$ = ps_exp_alloc(RESET); 

    $$->var_status = $4->var_status; 
    $$->exp_status = $4->exp_status | FLAG_EXP_MODAL_INSIDE; 

    $$->u.reset.var = var_search($2); 
    $$->u.reset.clock_name = $2; 
    $$->u.reset.child = $4; 
    /*     
    fprintf(RED_OUT, "\nParsing a quantified formula!\n"); 
    print_parse_subformula_structure($$, 0); 
    */ 
/*
    fprintf(RED_OUT, "parsing RESET: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/ 
    $$ = ps_exp_share($$); 
  }
|
  path_quantifier 
  fairness 
  single_modal { 
    check_choice_formula_global();  
  } 
  time_restriction 
  optional_event 
  fmla_conj {
    int 				fi; 
    struct ps_fairness_link_type	*fl; 
    struct ps_exp_type			*ag; 
    
    ag = $$ = ps_exp_alloc($1+$3);
    $$->var_status = 0; 
    $$->exp_status = FLAG_EXP_MODAL_INSIDE; 
    fillin_game_fairness_assumptions($$, $2); 
    $$->u.mexp.time_lb = $5->lb; 
    $$->u.mexp.time_ub = $5->ub; 
    $$->u.mexp.event_restriction = $6; 
    free($5); 
    
    switch ($3) { 
    case ALWAYS: 
      switch ($1) { 
      case FORALL: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL; 
        break; 
      case EXISTS: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
        break; 
      }
      $$->u.mexp.path_child = $7; 
      $$->u.mexp.dest_child = PS_EXP_FALSE; 
      break; 
    case EVENTUALLY: 
      switch ($1) { 
      case FORALL: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
        break; 
      case EXISTS: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL; 
        break; 
      }
      $$->u.mexp.dest_child = $7; 
      $$->u.mexp.path_child = PS_EXP_TRUE; 
      break; 
    case OFTEN: 
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
      $$->u.mexp.dest_child = $7; 
      $$->u.mexp.path_child = PS_EXP_TRUE; 
      break; 
    case ALMOST:
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
      $$->u.mexp.path_child = $7; 
      $$->u.mexp.dest_child = PS_EXP_FALSE; 
      break; 
    case CHANGE: 
      fprintf(RED_OUT, 
	      "\nNow we don't support modal operator CHANGE at line %1d\n", 
	      lineno
	      ); 
      exit(0); 
    }
/* 
    fprintf(RED_OUT, "\nIn the Monitoring parse initial condition in single modal temporal logics\n");
    print_parse_subformula_structure(PARSE_INITIAL_EXP, 0); 
    fflush(RED_OUT); 
*/ 
    $$->u.mexp.time_restriction = PS_EXP_TRUE; 
    free($2); 
    
    spec_size++;
    formula_connector_count++; 
/*
    fprintf(RED_OUT, "\nparsing modal formula\n"); 
    pcform($$); 
*/    
    /* newpstree($$); */    

/*    
    fprintf(RED_OUT, "path status = E:%x, S:%x\n", 
	    $$->u.mexp.path_child->status & FLAG_SYNCHRONIZER, 
	    $$->u.mexp.path_child->status & FLAG_EXP_STATE_INSIDE
	    ); 
    print_parse_subformula_structure($$->u.mexp.path_child, 0); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "\nEnd of Monitoring parse initial condition in single modal temporal logics\n");
    print_parse_subformula_structure(PARSE_INITIAL_EXP, 0); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "parsing EALWAYS: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    pcform($$); 
*/
    $$ = ps_exp_share($$); 
  }
|
  path_quantifier 
  fairness 
  fmla_conj 
  PS_UNTIL { 
    check_choice_formula_global();  
  } 
  time_restriction 
  optional_event 
  fmla_conj {
    struct ps_fairness_link_type	*fl; 
    struct ps_exp_type			*eu; 
    
    GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
    $$ = eu = ps_exp_alloc($1+UNTIL);
    $$->var_status = 0; 
    $$->exp_status = FLAG_EXP_MODAL_INSIDE; 
    fillin_game_fairness_assumptions($$, $2); 
    $$->u.mexp.time_lb = $6->lb;
    $$->u.mexp.time_ub = $6->ub; 
    free($6); // the time restriction is now stored in $$ and the parsed result 
              // can be released. 
    $$->u.mexp.time_restriction = PS_EXP_TRUE; 
    free($2); 
   
    spec_size++;
    formula_connector_count++; 
    /* newpstree($$); */    
   
    $$->u.mexp.path_child = $3; 
    $$->u.mexp.event_restriction = $7; 
    $$->u.mexp.dest_child = $8;

/*
    fprintf(RED_OUT, "parsing EUNTIL: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    pcform($$); 
*/
    $$ = ps_exp_share($$); 
  } 
| path_quantifier PS_IDENTIFIER PS_COLON {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = $2; 
    if (top_scope() < SCOPE_RANGE_DECLARATION) { 
      push_scope(SCOPE_RANGE_DECLARATION); 
    }
  }
  sexp_arith PS_DDOTS sexp_arith {
    if (top_scope() == SCOPE_RANGE_DECLARATION) { 
      pop_scope(); 
    }
  }
  PS_COMMA fmla_conj {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform($10); 
    fflush(RED_OUT); 
    #endif 
    
    $$ = ps_exp_alloc($1);
    switch ($1) { 
    case FORALL: 
      $$->var_status = $10->var_status; 
      $$->exp_status = $10->exp_status | FLAG_PATH_INSIDE | FLAG_CONJUNCTION_INSIDE; 
      break; 
    case EXISTS: 
      $$->var_status = $10->var_status; 
      $$->exp_status = $10->exp_status | FLAG_PATH_INSIDE | FLAG_DISJUNCTION_INSIDE; 
      break; 
    } 
      
    $$->u.qexp.quantifier_name = $2;
    $$->u.qexp.value = 0;

    $$->u.qexp.child = $10;
    $$->u.qexp.lb_exp = $5;
    $$->u.qexp.ub_exp = $7;

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  }
|
  fmla_literal {

    $$ = $1;
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "Got one formula literal.\n"); 
    pcform($$); 
    fflush(RED_OUT); 
    #endif 
    /* 
    if (PARSE_INITIAL_EXP) { 
      fprintf(RED_OUT, "\nLiteral Monitoring parse initial condition in single modal temporal logics\n");
      print_parse_subformula_structure(PARSE_INITIAL_EXP, 0); 
      fflush(RED_OUT); 
    }
    */ 
  }
; 


optional_event: 
  PS_EVENT { 
    push_scope(SCOPE_GLOBAL_EVENT); 
  } 
  PS_LCURLY formula PS_RCURLY { 
    int 				fi; 
    struct ps_fairness_link_type	*fl; 
    
    pop_scope(); 
    $$ = $4; 
    $$ = ps_exp_share($$); 
  }
| {
    $$ = NULL; 
  } ; 
  


fmla_literal : 
  PS_TRUE { 
    $$ = PS_EXP_TRUE;  
    spec_size++;
  }
| PS_FALSE { 
    $$ = PS_EXP_FALSE; 
    spec_size++; 
    /*    fprintf(RED_OUT, "yacc literal 2 : FALSE\n"); 
     */
  }
| exp_general {
/*
    fprintf(RED_OUT, "\nexp_general, LHS:\n"); 
    pcform($1); 
    fflush(RED_OUT); 
*/
  }
  rel_op exp_general { 
    struct ps_exp_type	*psub;
/*    
    fprintf(RED_OUT, "\nexp_general, RHS:\n"); 
    pcform($4); 
    fflush(RED_OUT); 
*/
    psub = ps_exp_alloc($3); 
    
    compose_rel_status(psub, $1, $4); 
  
    psub->u.arith.lhs_exp = $1; 
    psub->u.arith.rhs_exp = $4; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"An arith inequality:\n");
    pcform(psub);
    #endif 
    
    $$ = ps_exp_share(psub); 
  }
/* This is obsolete in redlib version 2. 
 * Now we use bitwise operation for the same purpose. 
 * However, there could be performance issue in reprenting bit patterns
 * with MDD. 
 
| PS_BDD PS_BIRD PS_LPAR exp_arith PS_RPAR { 
    $$ = ps_exp_alloc(TYPE_BDD);
    $$->u.atom.var = CURRENT_TOKEN_VAR; 
    $$->u.atom.var_name = CURRENT_TOKEN_VAR->name; 
//    $$->u.atom.indirect_count = 0; 
//    $$->u.atom.indirect_vi = NULL; 
//    $$->u.atom.indirect_exp = NULL; 
    $$->status = FLAG_DISCRETE | FLAG_LOCAL_VARIABLE;  

    $$->u.atom.exp_base_proc_index = $4; 
    $$->lineno = lineno; 
    $$ = ps_exp_share($$); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One local bdd atom:\n");
    pcform($$);
    #endif 
  } 
| PS_BDD { 
    if (CURRENT_TOKEN_VAR->status & FLAG_LOCAL_VARIABLE) 
      check_choice_formula_local(); 
    $$ = ps_exp_alloc(TYPE_BDD);
    $$->u.atom.var = CURRENT_TOKEN_VAR; 
    $$->u.atom.var_name = CURRENT_TOKEN_VAR->name; 
//    $$->u.atom.indirect_count = 0; 
//    $$->u.atom.indirect_exp = NULL; 
//    $$->u.atom.indirect_vi = NULL; 
    $$->status = FLAG_DISCRETE;  
    if ($$->u.atom.var->status & FLAG_LOCAL_VARIABLE) 
      $$->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER; 
    else 
      $$->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
    $$->lineno = lineno; 

    $$ = ps_exp_share($$); 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One bdd atom specific condition:\n");
    pcform($$);
    #endif 
  } 
*/
| optional_event_direction token_sync { 
    check_choice_formula_global_event(); 
  }
  PS_BIRD PS_LPAR {
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  exp_arith PS_RPAR { 
    pop_scope(); 
    $$ = ps_exp_alloc(TYPE_SYNCHRONIZER); 
    $$->u.atom.var = $2; 
    $$->u.atom.var_name = $2->name; 
    $$->var_status = $2->status | FLAG_SYNCHRONIZER; 
    switch ($1) { 
    case 0: 
      $$->exp_status = FLAG_EVENT_XMIT | FLAG_EVENT_RECV; 
      break; 
    case 1: 
      $$->exp_status = FLAG_EVENT_RECV; 
      break; 
    case -1: 
      $$->exp_status = FLAG_EVENT_XMIT; 
      break; 
    } 
//    $$->u.atom.indirect_exp = NULL; 
//    $$->u.atom.indirect_count = 0; 
//    $$->u.atom.indirect_vi = NULL; 

    $$->u.atom.exp_base_proc_index = $7; 
    $$ = ps_exp_share($$); 
/*
    fprintf(RED_OUT, "\nA constrained event "); 
    print_parse_subformula($$, 0); 
    fprintf(RED_OUT, " detected at line %1d\n", lineno); 
    fflush(RED_OUT); 
*/
  } 
| optional_event_direction token_sync { 
    struct ps_exp_type	*psub; 
    
    check_choice_formula_global_event(); 
    psub = $$ = ps_exp_alloc(TYPE_SYNCHRONIZER); 
    $$->u.atom.var = $2; 
    $$->u.atom.var_name = $2->name; 
    $$->var_status = $2->status | FLAG_SYNCHRONIZER; 
    switch ($1) { 
    case 0: 
      $$->exp_status = FLAG_EVENT_XMIT | FLAG_EVENT_RECV; 
      break; 
    case 1: 
      $$->exp_status = FLAG_EVENT_RECV; 
      break; 
    case -1: 
      $$->exp_status = FLAG_EVENT_XMIT; 
      break; 
    } 
//    $$->u.atom.indirect_vi = NULL; 
//    $$->u.atom.indirect_exp = NULL; 
//    $$->u.atom.indirect_count = 0; 
    
    $$->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
    $$ = ps_exp_share($$); 
/*
    fprintf(RED_OUT, "\nAn unconstrainted event "); 
    print_parse_subformula($$, 0); 
    fprintf(RED_OUT, " detected at line %1d\n", lineno); 
    fflush(RED_OUT); 
*/
  } 
| PS_IDENTIFIER PS_BIRD PS_LPAR exp_arith PS_RPAR {
    struct  parse_variable_type *pv;
    struct parse_mode_type	*pm; 
    int				mi; 
    struct ps_exp_type		*psub; 

    psub = $$ = ps_exp_alloc(ARITH_EQ);
    $$->u.arith.lhs_exp = ps_exp_alloc(var_mode->type);
    $$->u.arith.lhs_exp->u.atom.var = var_mode;
    $$->u.arith.lhs_exp->u.atom.var_index = var_mode->index;
    $$->u.arith.lhs_exp->var_status 
    = FLAG_DISCRETE | exp_var_status_parse_variable(var_mode);  
    $$->u.arith.lhs_exp->exp_status 
    = $$->u.arith.lhs_exp->exp_status | FLAG_LOCAL_IDENTIFIER; 
    
    $$->u.arith.lhs_exp->u.atom.var_name = var_mode->name;
    $$->u.arith.lhs_exp->u.atom.exp_base_proc_index = $4; 
/*
    $$->u.arith.lhs_exp->u.atom.indirect_count = 0;
    $$->u.arith.lhs_exp->u.atom.indirect_exp = NULL;
    $$->u.arith.lhs_exp->u.atom.indirect_vi = NULL;
*/
    $$->u.arith.lhs_exp = ps_exp_share($$->u.arith.lhs_exp); 
//    tpsubve($$->u.arith.lhs_exp); 
    
    $$->u.arith.rhs_exp = ps_exp_alloc(TYPE_MODE_INDEX); 
    $$->u.arith.rhs_exp->u.mode_index.value = 0; 
    $$->u.arith.rhs_exp->var_status = 0; 
    $$->u.arith.rhs_exp->exp_status = 0; 
    $$->u.arith.rhs_exp->u.mode_index.mode_name = $1; 
    $$->u.arith.rhs_exp->u.mode_index.parse_mode = NULL; 
    $$->u.arith.rhs_exp->lineno = lineno; 
    $$->u.arith.rhs_exp = ps_exp_share($$->u.arith.rhs_exp); 
    
    compose_rel_status($$, $$->u.arith.lhs_exp, $$->u.arith.rhs_exp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One local mode literal specific condition:\n");
    pcform($$);
    #endif  
    
    $$ = ps_exp_share($$); 
  }
| PS_IDENTIFIER {
    struct  parse_variable_type *pv;
    struct parse_mode_type	*pm; 
    int				mi; 
    struct ps_exp_type		*psub; 

    psub = $$ = ps_exp_alloc(ARITH_EQ);
    $$->u.arith.lhs_exp = ps_exp_alloc(var_mode->type);
    $$->u.arith.lhs_exp->u.atom.var = var_mode;
    $$->u.arith.lhs_exp->u.atom.var_index = var_mode->index;
    $$->u.arith.lhs_exp->var_status 
    = FLAG_DISCRETE | exp_var_status_parse_variable(var_mode);  
    $$->u.arith.lhs_exp->exp_status 
    = $$->u.arith.lhs_exp->exp_status | FLAG_LOCAL_IDENTIFIER; 
    
    $$->u.arith.lhs_exp->u.atom.var_name = var_mode->name;
    $$->u.arith.lhs_exp->u.atom.exp_base_proc_index 
    = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER); 
/*
    $$->u.arith.lhs_exp->u.atom.indirect_count = 0;
    $$->u.arith.lhs_exp->u.atom.indirect_exp = NULL;
    $$->u.arith.lhs_exp->u.atom.indirect_vi = NULL;
*/
    $$->u.arith.lhs_exp = ps_exp_share($$->u.arith.lhs_exp); 
//    tpsubve($$->u.arith.lhs_exp); 
    exp_mode = $$->u.arith.lhs_exp; 

    $$->u.arith.rhs_exp = ps_exp_alloc(TYPE_MODE_INDEX); 
    $$->u.arith.rhs_exp->u.mode_index.value = 0; 
    $$->u.arith.rhs_exp->var_status = 0; 
    $$->u.arith.rhs_exp->exp_status = 0; 
    $$->u.arith.rhs_exp->u.mode_index.mode_name = $1; 
    $$->u.arith.rhs_exp->u.mode_index.parse_mode = NULL; 
    $$->u.arith.rhs_exp->lineno = lineno; 
    $$->u.arith.rhs_exp = ps_exp_share($$->u.arith.rhs_exp); 
    
    compose_rel_status($$, $$->u.arith.lhs_exp, $$->u.arith.rhs_exp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One local mode literal specific condition:\n");
    pcform($$);
    #endif  
    
    $$ = ps_exp_share($$); 
  }
| PS_BOOLEAN_INLINE_CALL { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a boolean inline call:\n"); 
    pcform($1); 
    fflush(RED_OUT); 
    #endif 
  } 
  inline_actual_arguments { 
    struct ps_bunit_type	*pbu; 
    struct ps_exp_type		*ic; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "an actual argument list in inline boolean call.\n"); 
    print_ps_exp_list($3); 
    #endif 
    
    $$ = ps_exp_alloc(TYPE_INLINE_CALL); 
    $$->u.inline_call.inline_declare = $1; 
    $$->u.inline_call.inline_exp_name = $1->u.inline_declare.inline_exp_name; 
    $$->u.inline_call.actual_argument_list = $3; 
    $$->u.inline_call.instantiated_exp = NULL; 
    ic = $$; 
/*
    if ((GSTATUS[INDEX_PARSE] & MASK_GRAM_PHASE) != GRAM_PHASE_INLINE_DECL) {
      $$->u.inline_call.instantiated_exp = ps_exp_inline_instantiate($$); 

      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "Leaving boolean call with instantiated exp.\n"); 
      pcform($$->u.inline_call.instantiated_exp); 
      fflush(RED_OUT); 
      #endif 
    }
*/
    $$ = ps_exp_share($$); 
  }; 


optional_event_direction: 
  PS_TO_STREAM { 
    $$ = -1; 
  } 
| PS_QUESTION { 
    $$ = 1; 
  } 
| PS_FROM_STREAM { 
    $$ = 1; 
  }
| { 
    $$ = 0;
  }; 




exp_general: 
  PS_LPAR formula PS_RPAR PS_QUESTION {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nentering conditional arithmetic expression:\n"); 
    pcform($2); 
    fflush(RED_OUT); 
    #endif 
  } 
  sexp_arith PS_COLON exp_general { 
    struct ps_exp_type	*psub;

    psub = ps_exp_alloc(ARITH_CONDITIONAL);

    psub->var_status = $2->var_status | $6->var_status | $8->var_status; 
    psub->exp_status = $2->exp_status | $6->exp_status | $8->exp_status; 

    psub->u.arith_cond.cond = $2; 
    psub->u.arith_cond.if_exp = $6; 
    psub->u.arith_cond.else_exp = $8; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"A conditional arith exp:\n");
    pcform(psub);
    #endif 

    $$ = ps_exp_share(psub); 
  } 
| sexp_arith { 
    $$ = $1; 
  }; 



sexp_arith : 
  sexp_arith PS_PLUS exp_multiply {
    $$ = ps_exp_alloc(ARITH_ADD);
    
    compose_additive_status(ARITH_ADD, $1, $3, 
      &($$->var_status), &($$->exp_status)
    ); 
    
    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;
    
    $$ = ps_exp_share($$); 
  }
| sexp_arith PS_MINUS exp_multiply {
    $$ = ps_exp_alloc(ARITH_MINUS);
    
    compose_additive_status(ARITH_MINUS, $1, $3, 
      &($$->var_status), &($$->exp_status)
    ); 
    
    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;
    
    $$ = ps_exp_share($$); 
  }
| sexp_multiply { 
    $$ = $1;
/*
    fprintf(RED_OUT, "An sexp_multiply at line %1d:\n", lineno); 
    print_parse_subformula_structure($$, 0); 
    fprintf(RED_OUT, "\n"); 
*/
  };




exp_arith : 
  exp_arith PS_PLUS exp_multiply {
    $$ = ps_exp_alloc(ARITH_ADD);
    
    compose_additive_status(ARITH_ADD, $1, $3, 
      &($$->var_status), &($$->exp_status)
    ); 
    
    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;
    
    $$ = ps_exp_share($$); 
/* 
    fprintf(RED_OUT, "\nAn exp_arith at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  }
| exp_arith PS_MINUS exp_multiply {
    $$ = ps_exp_alloc(ARITH_MINUS);
    
    compose_additive_status(ARITH_MINUS, $1, $3, 
      &($$->var_status), &($$->exp_status)
    ); 
    
    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;
    
    $$ = ps_exp_share($$); 
/* 
    fprintf(RED_OUT, "\nAn exp_arith at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  }
| exp_multiply { 
    $$ = $1;
/*    
    fprintf(RED_OUT, "An exp_multiply at line %1d:\n", lineno); 
    pcform($$); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
*/
  };




sexp_multiply :
  sexp_multiply multiplicative_op exp_bit_term {
    $$ = ps_exp_alloc($2);
    
    compose_mult_status($2, $1, $3, &($$->var_status), &($$->exp_status)); 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In multiplication\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| sexp_term {
    $$ = $1;
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An sexp_term at line %1d:\n", lineno); 
    pcform($$); 
    #endif 
  };




exp_multiply :
  exp_multiply multiplicative_op exp_bit_term {
    $$ = ps_exp_alloc($2);
    
    compose_mult_status($2, $1, $3, &($$->var_status), &($$->exp_status)); 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In multiplication\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| exp_bit_term {
    $$ = $1;
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
    #endif 
  };






sexp_term :
  PS_MINUS PS_NUMBER { 
    $$ = ps_exp_alloc(TYPE_CONSTANT);
    $$->u.value = -1 * $2;
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", $$->u.value, lineno);
    #endif 
    
    $$ = ps_exp_share($$); 
  } 
| PS_MINUS PS_FLOAT_NUMBER { 
    $$ = ps_exp_alloc(TYPE_FLOAT_CONSTANT);
    $$->u.float_value = -1 * $2;
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", $$->u.value, lineno);
    #endif 
    
    $$ = ps_exp_share($$); 
  } 
| exp_bit_term { 
    $$ = $1;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform($$); 
    #endif 
  };

exp_bit_term :
  exp_bit_term PS_BIT_OR exp_term {
    $$ = ps_exp_alloc(BIT_OR);
    
    $$->var_status = $1->var_status | $3->var_status; 
    $$->exp_status = $1->exp_status | $3->exp_status; 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In bitwise or\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| exp_bit_term PS_BIT_AND exp_term {
    $$ = ps_exp_alloc(BIT_AND);
    
    $$->var_status = $1->var_status | $3->var_status; 
    $$->exp_status = $1->exp_status | $3->exp_status; 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In bitwise and\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| exp_bit_term PS_FROM_STREAM exp_term {
    $$ = ps_exp_alloc(BIT_SHIFT_RIGHT);
    
    $$->var_status = $1->var_status | $3->var_status; 
    $$->exp_status = $1->exp_status | $3->exp_status; 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In shift right\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| exp_bit_term PS_TO_STREAM exp_term {
    $$ = ps_exp_alloc(BIT_SHIFT_LEFT);
    
    $$->var_status = $1->var_status | $3->var_status; 
    $$->exp_status = $1->exp_status | $3->exp_status; 

    $$->u.arith.lhs_exp = $1;
    $$->u.arith.rhs_exp = $3;

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In shift left\n"); 
    pcform($$); 
    #endif 
    
    $$ = ps_exp_share($$); 
  }
| exp_term {
    $$ = $1;
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
    #endif 
  };


exp_term :
  PS_LPAR exp_general PS_RPAR {
    $$ = $2;
  }
| PS_MULTIPLY exp_term { 
    $$ = ps_exp_alloc(TYPE_REFERENCE); 
    $$->var_status = $2->var_status | FLAG_DISCRETE; 
    $$->exp_status = $2->exp_status; 
    $$->u.exp = $2; 
    $$ = ps_exp_share($$); 
  } 
| PS_BIT_NOT exp_term { 
    $$ = ps_exp_alloc(BIT_NOT); 
    $$->var_status = $2->var_status; 
    $$->exp_status = $2->exp_status; 
    $$->u.exp = $2; 
    $$ = ps_exp_share($$); 
  }
| PS_SUM PS_IDENTIFIER PS_COLON {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = $2; 
    if (top_scope() < SCOPE_RANGE_DECLARATION) { 
      push_scope(SCOPE_RANGE_DECLARATION); 
    }
  }
  sexp_arith PS_DDOTS sexp_arith {
    if (top_scope() == SCOPE_RANGE_DECLARATION) { 
      pop_scope(); 
    }
  }
  PS_COMMA exp_arith {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform($10); 
    fflush(RED_OUT); 
    #endif 
    
    $$ = ps_exp_alloc(ARITH_SUM);
    $$->var_status = $10->var_status; 
    $$->exp_status = $10->exp_status | FLAG_PATH_INSIDE | FLAG_CONJUNCTION_INSIDE; 
      
    $$->u.qexp.quantifier_name = $2;
    $$->u.qexp.value = 0;

    $$->u.qexp.child = $10;
    $$->u.qexp.lb_exp = $5;
    $$->u.qexp.ub_exp = $7;

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  }
| PS_NUMBER {
    $$ = ps_exp_alloc(TYPE_CONSTANT);
    $$->u.value = $1;
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", $$->u.value, lineno);
    #endif 
    
    $$ = ps_exp_share($$); 
  } 
| PS_HEX_NUMBER {
    $$ = ps_exp_alloc(TYPE_CONSTANT);
    $$->u.value = $1;
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", $$->u.value, lineno);
    #endif 
    
    $$ = ps_exp_share($$); 
  } 
| PS_FLOAT_NUMBER {
    $$ = ps_exp_alloc(TYPE_FLOAT_CONSTANT);
    $$->u.float_value = $1;
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", $$->u.value, lineno);
    #endif 
    
    $$ = ps_exp_share($$); 
  } 
| PS_NULL { 
    $$ = ps_exp_alloc(TYPE_NULL);
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    $$->u.value = 0; 
    
    $$ = ps_exp_share($$); 
  }
| PS_INDEX PS_IDENTIFIER { 
    $$ = ps_exp_alloc(TYPE_MODE_INDEX); 
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    $$->u.mode_index.mode_name = $2; 
    $$->u.mode_index.parse_mode = NULL; 
    $$->u.mode_index.value = 0; 
    $$->lineno = lineno; 
    
    $$ = ps_exp_share($$); 
  } 
| PS_PROCESS_COUNT { 
    $$ = ps_exp_alloc(TYPE_PROCESS_COUNT);
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    $$->u.value = PROCESS_COUNT; 
    
    $$ = ps_exp_share($$); 
  } 
| PS_MODE_COUNT { 
    $$ = ps_exp_alloc(TYPE_MODE_COUNT);
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    $$ = ps_exp_share($$); 
  } 
| PS_XTION_COUNT { 
    $$ = ps_exp_alloc(TYPE_XTION_COUNT);
    $$->var_status = 0; 
    $$->exp_status = FLAG_CONSTANT; 
    
    $$ = ps_exp_share($$); 
  } 
| PS_P {
    if (   top_scope() != SCOPE_LOCAL 
        && top_scope() != SCOPE_LOCAL_XTION
        && top_scope() != SCOPE_ADDRESS_ENFORCER
        ) {
      fprintf(RED_OUT, "\nError: a process identifier symbol 'P' in a non-local term at line %1d.\n", lineno);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(0);
    }
    $$ = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER);
    $$->var_status = 0; 
    $$->exp_status = FLAG_LOCAL_IDENTIFIER; 
    $$ = ps_exp_share($$); 
/*    
    fprintf(RED_OUT, "\nP detected\n"); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  } 
| PS_MACRO_CONSTANT { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a discrete inline call:\n"); 
    pcform($1); 
    fflush(RED_OUT); 
    #endif 
    
    $$ = ps_exp_alloc(TYPE_MACRO_CONSTANT); 
    $$->u.inline_call.inline_declare = $1; 
    $$->u.inline_call.inline_exp_name = $1->u.inline_declare.inline_exp_name; 
    $$->u.inline_call.actual_argument_list = NULL; 
    $$->u.inline_call.instantiated_exp = NULL; 
/*
    if ((GSTATUS[INDEX_PARSE] & MASK_GRAM_PHASE) != GRAM_PHASE_INLINE_DECL) {
      $$->u.inline_call.instantiated_exp = ps_exp_inline_instantiate($$); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "Leaving discrete call with instantiated exp.\n"); 
      pcform($$->u.inline_call.instantiated_exp); 
      fflush(RED_OUT); 
      #endif 
    }
*/
    $$ = ps_exp_share($$); 
  } 
| PS_DISCRETE_INLINE_CALL { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a discrete inline call:\n"); 
    pcform($1); 
    fflush(RED_OUT); 
    #endif 
  } 
  inline_actual_arguments { 
    struct ps_bunit_type	*pbu; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "an actual argument list in inline boolean call.\n"); 
    print_ps_exp_list($3); 
    #endif 
    
    $$ = ps_exp_alloc(TYPE_INLINE_CALL); 
    $$->u.inline_call.inline_declare = $1; 
    $$->u.inline_call.inline_exp_name = $1->u.inline_declare.inline_exp_name; 
    $$->u.inline_call.actual_argument_list = $3; 
    $$->u.inline_call.instantiated_exp = NULL; 
/*
    if ((GSTATUS[INDEX_PARSE] & MASK_GRAM_PHASE) != GRAM_PHASE_INLINE_DECL) {
      $$->u.inline_call.instantiated_exp = ps_exp_inline_instantiate($$); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "Leaving discrete call with instantiated exp.\n"); 
      pcform($$->u.inline_call.instantiated_exp); 
      fflush(RED_OUT); 
      #endif 
    }
*/
    $$ = ps_exp_share($$); 
  } 
| PS_INLINE_ARGUMENT { 
    $$ = ps_exp_alloc(TYPE_INLINE_ARGUMENT); 
    $$->u.argument = $1; 
    $$ = ps_exp_share($$); 
  } 
| PS_QFD { 
    $$ = CURRENT_TOKEN_QFD; 
    $$->var_status = FLAG_QFD; 
    $$->exp_status = 0; 
    
    $$ = ps_exp_share($$); 
  } 
| PS_BIT_AND complete_operand { 
    /* But you first have to check if the identifier is a macro constant. */
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 1: a variable in a NULL scope at line %1d.\n", lineno);
      fprintf(RED_OUT, "\nGot one complete operand!\n"); 
      pcform($1); 
      bk(0); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);      
    }
    if(   $2->type != TYPE_CLOCK 
       && $2->type != TYPE_POINTER
       && $2->type != TYPE_DISCRETE
       && $2->type != TYPE_FLOAT
       && $2->type != TYPE_DOUBLE
       && $2->type != TYPE_DENSE 
       ) { 
      fprintf(RED_OUT, 
        "Syntax error: a non-variable as a complete operand at line %1d.\n", 
	lineno
      ); 
      print_parse_subformula($2, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGot one complete operand!\n"); 
    pcform($2); 
    #endif 
    if (   top_scope() == SCOPE_GLOBAL 
	&& ($2->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
	&& ($2->u.atom.var->status & FLAG_LOCAL_VARIABLE)
	) {
      fprintf(RED_OUT, 
        "Syntax error: a non-indexed local variable %s used in global condition", 
        $2->u.atom.var_name
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(""); 
      exit(0);
    }
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An complete_operand at line %1d:\n", lineno); 
    pcform($$); 
    #endif 

    $$ = ps_exp_alloc(TYPE_DEREFERENCE); 
    $$->var_status = $2->var_status; 
    $$->exp_status = $2->exp_status; 
    $$->u.exp = $2; 
    $$ = ps_exp_share($$); 
  } 
| complete_operand {
    /* But you first have to check if the identifier is a macro constant. */
    if(   $1->type != TYPE_CLOCK 
       && $1->type != TYPE_POINTER
       && $1->type != TYPE_DISCRETE
       && $1->type != TYPE_FLOAT
       && $1->type != TYPE_DOUBLE
       && $1->type != TYPE_DENSE 
       && $1->type != TYPE_REFERENCE 
       ) {
      fprintf(RED_OUT, 
        "Syntax error: a non-variable from a complete operand at line %1d.\n", 
        lineno
      ); 
      print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 1: a variable in a NULL scope at line %1d.\n", lineno);
      fprintf(RED_OUT, "\nGot one complete operand!\n"); 
      pcform($1); 
      bk(0); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);      
    }
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGot one complete operand!\n"); 
    pcform($1); 
    #endif 
    if (   top_scope() == SCOPE_GLOBAL 
	&& ($1->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
	&& ($1->u.atom.var->status & FLAG_LOCAL_VARIABLE)
	) {
      fprintf(RED_OUT, "Syntax error: a non-indexed local variable %s used in global condition", $1->u.atom.var_name);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(""); 
      exit(0);
    }
    $$ = $1;
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An complete_operand at line %1d, s=%x:\n", 
      lineno, $$->status
    ); 
    pcform($$); 
    #endif 
  };





inline_actual_arguments: 
  PS_LPAR inline_actual_argument_list PS_RPAR { 
    $$ = $2; 
  } 
| PS_LPAR PS_RPAR { 
    $$ = NULL; 
  }
| { 
    $$ = NULL; 
  }; 


inline_actual_argument_list: 
  sexp_arith PS_COMMA inline_actual_argument_list {
    struct ps_bunit_type	*bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = $1; 
    bu->bnext = $3; 
    
    $$ = bu; 
  }
| sexp_arith { 
    struct ps_bunit_type	*bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = $1; 
    bu->bnext = NULL; 
    
    $$ = bu; 
  }; 

 

complete_operand : 
  PS_LPAR complete_operand PS_RPAR { 
    $$ = $2; 
  } 
| complete_operand PS_LBRAC exp_arith PS_RBRAC { 
    struct ps_exp_type	*add_offset, *ind_operand; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "-- indirection parsed: "); 
    pcform($3); 
    fflush(RED_OUT); 
    #endif 
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 2: a variable in a NULL scope at line %1d.\n", lineno);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(0);      
    } 
    add_offset = ps_exp_alloc(ARITH_ADD); 
    compose_additive_status(ARITH_ADD, $1, $3, 
      &(add_offset->var_status), &(add_offset->exp_status)
    ); 
   
    add_offset->u.arith.lhs_exp = $1; 
    add_offset->u.arith.rhs_exp = $3; 
    add_offset = ps_exp_share(add_offset); 
    
    ind_operand = ps_exp_alloc(TYPE_REFERENCE); 
    ind_operand->var_status = add_offset->var_status | FLAG_DISCRETE; 
    ind_operand->exp_status = add_offset->exp_status; 
    ind_operand->u.exp = add_offset; 
    $$ = ps_exp_share(ind_operand); 
  }
| base_variable optional_address {
    struct parse_variable_type *pv;
    struct ps_exp_type		*tt, *t3; 
    struct parse_indirect_type	*pt, *ppt; 

    if ($1->status & FLAG_VAR_STACK) { 
      if (   $2->exp_address  
          && $2->flag_address_type != FLAG_ADDRESS_STACK_PLUS
          && $2->flag_address_type != FLAG_ADDRESS_STACK_MINUS
          ) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal addressing to stack variable %s at line %1d.\n", 
          $1->name, lineno
        ); 
        fflush(RED_OUT); 
        free($2); 
        exit(0);
    } }  
    else if (   $2->exp_address  
             && (   $2->flag_address_type == FLAG_ADDRESS_STACK_PLUS
                 || $2->flag_address_type == FLAG_ADDRESS_STACK_MINUS
             )   ) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal relative addressing to non-stack variable %s at line %1d.\n", 
        $1->name, lineno
      ); 
      fflush(RED_OUT); 
      free($2); 
      exit(0);
    }

    #ifdef RED_DEBUG_YACC_MODE 
    fprintf(RED_OUT, "  token operand at line %1d.\n", lineno); 
    print_parse_subformula_structure($2->exp_address); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 

    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, 
        "\nError 2: a variable in a NULL scope at line %1d.\n", lineno
      );
      fprintf(RED_OUT, "%1d:%s", $1->index, $1->name); 
      if ($2->exp_address) {
        fprintf(RED_OUT, "@("); 
        print_parse_subformula($2->exp_address, 1); 
        fprintf(RED_OUT, ")"); 
      } 
/*
      if ($4) 
        pcform($4); 
*/        
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      free($2); 
      bk(0);      
    }
    else if ($1 == NULL) { 
      fprintf(RED_OUT, "Syntax error: an undeclared local variable %s in global condition", $1->name);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      free($2); 
      exit(0); 
    } 
    else if ($2->exp_address != NULL && !($1->status & FLAG_LOCAL_VARIABLE)) {
      fprintf(RED_OUT, 
	      "Syntax error: a global variable %s is indexed ", 
	      $1->name
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      free($2); 
      exit(0); 
    } 
/*
    else if ($1->status & FLAG_QUANTIFIED_SYNC) {
      fprintf(
	RED_OUT, 
	"Syntax error: a quantified sync variable %s is indexed ", 
	$1->name
	);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0); 
    } 
*/    
    $$ = tt = ps_exp_alloc($1->type); 
    pv = $1; 
    $$->var_status = exp_var_status_parse_variable($1);      
    $$->exp_status = 0;      
    $$->u.atom.var_index = $1->index; 
    $$->u.atom.var = $1; 
    $$->u.atom.var_name = $1->name; 
    if (!($1->status & FLAG_LOCAL_VARIABLE)) { 
      if ($2->exp_address != NULL) { 
        fprintf(RED_OUT, 
          "ERROR: Illegal address specification for global variable %s at line %1d.\n", 
          $1->name, lineno 
        ); 
        pcform($2->exp_address); 
        free($2); 
        exit(0); 
      } 
      $$->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
    } 
    else if ($2->exp_address == NULL) { 
      if ($1->status & FLAG_VAR_STACK) {
        $$->u.atom.exp_base_proc_index = PS_EXP__SP; 
        $$->var_status = $$->var_status | FLAG_LOCAL_VARIABLE; 
      } 
      else {  
        $$->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER; 
        $$->var_status = $$->var_status | FLAG_LOCAL_VARIABLE; 
      }
    } 
    else { 
      if ($1->status & FLAG_VAR_STACK) {
        switch ($2->flag_address_type) { 
        case FLAG_ADDRESS_STACK_PLUS: 
          $$->u.atom.exp_base_proc_index = exp_arith(ARITH_ADD, PS_EXP__SP, $2->exp_address); 
          break; 
        case FLAG_ADDRESS_STACK_MINUS: 
          $$->u.atom.exp_base_proc_index = exp_arith(ARITH_MINUS, PS_EXP__SP, $2->exp_address); 
          break; 
        default: 
          fprintf(RED_OUT, "\nERROR: Illegal addressing to stack variable %s at line %1d.\n", 
            $1->name, lineno
          ); 
          fflush(RED_OUT); 
          free($2); 
          exit(0); 
        } 
      } 
      else {
        $$->u.atom.exp_base_proc_index = $2->exp_address; 
        $$->var_status = $$->var_status | $2->exp_address->var_status | FLAG_LOCAL_VARIABLE; 
        if (   $2->exp_address->type != TYPE_LOCAL_IDENTIFIER  
            && top_scope() != SCOPE_GLOBAL_EVENT 
            && top_scope() != SCOPE_GLOBAL
            ) 
          GSTATUS[INDEX_SYNCHRONIZATION] 
          = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_POINTER_ARITH; 
    } }

    t3 = $2->exp_address; 

    switch ($$->type) {
    case TYPE_POINTER: 
      if ($2->exp_address && ($2->exp_address->var_status & FLAG_QUANTIFIED_SYNC)) 
        $$->var_status = $$->var_status | FLAG_QUANTIFIED_SYNC; 
      break; 
    case TYPE_CLOCK: 
      $$->exp_status = $$->exp_status | FLAG_ONE_POS_CLOCK; 
      break; 
    case TYPE_DENSE:  
      $$->exp_status = $$->exp_status | FLAG_HYBRID; 
      break; 
    } 
    free($2); 
    
/*
    $$->u.atom.indirect_count = 0; 
    for (pt = $4; pt; pt = pt->next_parse_indirect) 
      $$->u.atom.indirect_count++; 
    if ($$->u.atom.indirect_count) { 
      $$->exp_status = $$->exp_status | FLAG_INDIRECTION; 
      $$->u.atom.indirect_exp = (struct ps_exp_type **) 
        malloc($$->u.atom.indirect_count * sizeof(struct ps_exp_type *)); 
      $$->u.atom.indirect_count = 0; 
      for (pt = $4; pt; ) {
        $$->u.atom.indirect_exp[$$->u.atom.indirect_count] = pt->pointer; 
        $$->u.atom.indirect_count++; 
        ppt = pt; 
        pt = pt->next_parse_indirect; 
        free(ppt); 
      }
    }
*/
    $$ = ps_exp_share($$); 
 
    /* 
    fprintf(RED_OUT,"One literal specific condition:\n");
    print_parse_subformula($$, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n");
    */ 
    $$ = ps_exp_share($$); 
    
  }
; 


base_variable:  
  PS_MODE {
    $$ = var_mode; 
  }
| token_variable { 
    $$ = $1->pvar; 
  }
; 



optional_address :  
  PS_BIRD_PLUS PS_LPAR exp_arith PS_RPAR {
    $$ = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    $$->exp_address = $3; 
    $$->flag_address_type = FLAG_ADDRESS_STACK_PLUS; 
  }
| PS_BIRD_MINUS PS_LPAR exp_arith PS_RPAR {
    $$ = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    $$->exp_address = $3; 
    $$->flag_address_type = FLAG_ADDRESS_STACK_MINUS; 
  }
| PS_BIRD PS_LPAR exp_arith PS_RPAR {
    $$ = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    $$->exp_address = $3; 
    $$->flag_address_type = FLAG_ADDRESS_ENFORCER; 
  }
| { 
    $$ = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    $$->exp_address = NULL; 
    $$->flag_address_type = FLAG_ADDRESS_NULL; 
  }; 




 


rel_op :
  PS_EQ {
    /*    fprintf(RED_OUT, "An operand %d means '=.'\n", $1);
     */
    $$ = ARITH_EQ;
  }
|
  PS_NEQ {
  /*    fprintf(RED_OUT, "An operand %d means '!=.'\n", $1);
   */
    $$ = ARITH_NEQ;
  }
|
  PS_LESS {
    /* fprintf(RED_OUT, "An operand %d means '<.'\n", $1);
     */
    $$ = ARITH_LESS;
  }
|
  PS_LEQ {
    /*    fprintf(RED_OUT, "An operand %d means '<=.'\n", $1);
     */
    $$ = ARITH_LEQ;
  }
|
  PS_GREATER {
    /*    fprintf(RED_OUT, "An operand %d means '>.'\n", $1);
     */
    $$ = ARITH_GREATER;
  }
|
  PS_GEQ {
    /*    fprintf(RED_OUT, "An operand %d means '>=.'\n", $1);
     */
    $$ = ARITH_GEQ;
  };




single_modal :
  PS_ALWAYS {
    $$ = ALWAYS;
  }
|
  PS_EVENTUALLY {
    $$ = EVENTUALLY;
  }
|
  PS_CHANGE {
    $$ = CHANGE;
  }
|
  PS_OFTEN {
    $$ = OFTEN;
  }
|
  PS_ALMOST {
    $$ = ALMOST;
  }
;

path_quantifier :
  PS_FORALL {
    $$ = FORALL;
  }
|
  PS_EXISTS {
    $$ = EXISTS;
  }
;





fairness :
  PS_ASSUME { 
    GSTATUS[INDEX_FAIRNESS] 
    = GSTATUS[INDEX_FAIRNESS] | FLAG_FAIRNESS_ASSUMPTIONS; 
    CURRENT_GRAM_FAIRNESS = (struct gram_fairness_type *) 
      malloc(sizeof(struct gram_fairness_type)); 
    CURRENT_GRAM_FAIRNESS->strong_fairness_count = 0; 
    CURRENT_GRAM_FAIRNESS->strong_fairness_list = NULL; 
    CURRENT_GRAM_FAIRNESS->weak_fairness_count = 0; 
    CURRENT_GRAM_FAIRNESS->weak_fairness_list = NULL;    
    dummy_weak_fl.next_ps_fairness_link = NULL; 
    weak_fl_tail = &dummy_weak_fl; 
    dummy_strong_fl.next_ps_fairness_link = NULL; 
    strong_fl_tail = &dummy_strong_fl; 
  } 
  PS_LCURLY global_fairness_sequence PS_RCURLY {
    CURRENT_GRAM_FAIRNESS->strong_fairness_list 
    = dummy_strong_fl.next_ps_fairness_link; 
    CURRENT_GRAM_FAIRNESS->weak_fairness_list 
    = dummy_weak_fl.next_ps_fairness_link; 
    $$ = CURRENT_GRAM_FAIRNESS; 
  }
|
  {
    $$ = (struct gram_fairness_type *) malloc(sizeof(struct gram_fairness_type));
    $$->strong_fairness_count = 0;
    $$->strong_fairness_list = NULL;
    $$->weak_fairness_count = 0;
    $$->weak_fairness_list = NULL;
  };



global_fairness_sequence : 
  multiple_global_fairness {
    struct ps_fairness_link_type	*fl; 
    
    fl = (struct ps_fairness_link_type *) 
      malloc(sizeof(struct ps_fairness_link_type)); 
    if (CURRENT_FAIRNESS_STRENGTH == FLAG_FAIRNESS_STRONG) { 
      fl->fairness = $1; 
      strong_fl_tail->next_ps_fairness_link = fl; 
      fl->next_ps_fairness_link = NULL; 
      strong_fl_tail = fl; 
      CURRENT_GRAM_FAIRNESS->strong_fairness_count++; 
    } 
    else { 
      fl->fairness = $1; 
      weak_fl_tail->next_ps_fairness_link = fl; 
      fl->next_ps_fairness_link = NULL; 
      weak_fl_tail = fl; 
      CURRENT_GRAM_FAIRNESS->weak_fairness_count++; 
    } 
  }
  global_fairness_sequence {
    $$ = NULL; 
  }
| {
    $$ = NULL; 
  }; 


multiple_global_fairness : 
  PS_BIT_OR PS_IDENTIFIER PS_COLON {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = $2; 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
  sexp_arith PS_DDOTS sexp_arith {
    pop_scope(); 
  }
  PS_COMMA fairness_strength {
    CURRENT_FAIRNESS = ps_exp_alloc(LINEAR_EVENT); 
    CURRENT_FAIRNESS->var_status = 0; 
    CURRENT_FAIRNESS->exp_status = FLAG_EXP_MODAL_INSIDE; 
    CURRENT_FAIRNESS->u.eexp.precond_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = NULL; 
  }
  global_fairness {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform($12); 
    fflush(RED_OUT); 
    #endif 
    
    $$ = ps_exp_alloc(TYPE_MULTIPLE_FAIRNESS);
    $$->var_status = $12->var_status; 
    $$->exp_status = $12->exp_status; 
      
    $$->u.qexp.quantifier_name = $2;
    $$->u.qexp.value = 0;

    $$->u.qexp.child = $12;
    $$->u.qexp.lb_exp = $5;
    $$->u.qexp.ub_exp = $7;

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    $$ = ps_exp_share($$); 
  }
| fairness_strength {
    CURRENT_FAIRNESS = ps_exp_alloc(LINEAR_EVENT); 
    CURRENT_FAIRNESS->exp_status = FLAG_EXP_MODAL_INSIDE; 
    CURRENT_FAIRNESS->u.eexp.precond_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = NULL; 
  }
  global_fairness { 
    $$ = CURRENT_FAIRNESS; 
  }; 
  


  
fairness_strength : 
  PS_STRONG { 
    $$ = FLAG_FAIRNESS_STRONG;
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_STRONG;  
  }
| PS_WEAK { 
    $$ = FLAG_FAIRNESS_WEAK; 
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_WEAK;  
  }; 



global_fairness :
  event_fairness PS_SEMICOLON {
    $$ = $1; 
    $$->u.eexp.precond_exp = PS_EXP_TRUE; 
    $$ = ps_exp_share($$); 
  }
| global_condition {
    CURRENT_FAIRNESS->u.eexp.precond_exp = $1; 
  }
  optional_event_fairness PS_SEMICOLON {
    CURRENT_FAIRNESS = ps_exp_share(CURRENT_FAIRNESS); 
    $$ = CURRENT_FAIRNESS; 
  };




optional_event_fairness : 
  event_fairness 
| { 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = PS_EXP_TRUE; 
  }; 


event_fairness :
  PS_EVENT { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, 
      "\nPS_EVENT detected in global fairness sequence at line %1d.\n", 
      lineno
    );
    fflush(RED_OUT);  
    #endif 
  } 
  PS_LCURLY formula PS_RCURLY { 
    pop_scope(); 
  }  
  optional_event_postcond {
    CURRENT_FAIRNESS->u.eexp.event_exp = $4; 
    $$ = CURRENT_FAIRNESS; 
/*    
    fprintf(RED_OUT, "path status = E:%x, S:%x\n", 
	    $$->u.eexp.event_child->status & FLAG_SYNCHRONIZER, 
	    $$->u.eexp.restriciton_child->status & FLAG_EXP_STATE_INSIDE
	    ); 
    print_parse_subformula_structure($$->u.eexp.event_child, 0); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "\nEnd of Monitoring parse initial condition in single modal temporal logics\n");
    print_parse_subformula_structure(PARSE_INITIAL_EXP, 0); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "parsing EALWAYS: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    pcform($$); 
*/
  }; 

optional_event_postcond : 
  fmla_conj {
    CURRENT_FAIRNESS->u.eexp.postcond_exp = $1; 
  }
| { 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = PS_EXP_TRUE; 
  }; 


  
   
time_restriction :
  PS_LCURLY rel_op {
    push_scope(SCOPE_RANGE_DECLARATION); 
  } 
  exp_arith PS_RCURLY {
    struct parse_variable_type	*pv;
    int 			lb, ub, flag; 
    float			flb, fub; 

    pop_scope(); 
    if ($4->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    flag = get_integer_range($4, 0, &lb, &ub, &flb, &fub); 
    if (flag != FLAG_SPECIFIC_VALUE) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal quantification range type in modal time restriction at line %1d.\n", 
        lineno 
      ); 
      pcform($4); 
      fflush(RED_OUT); 
      bk(0); 
    } 
    if (lb != ub) { 
      fprintf(RED_OUT, "\nSyntax error: range timing distances %1d..%1d in modal operator at line %1d.\n", 
        lb, ub, lineno
      ); 
      exit(0); 
    } 
    else if (ub < 0) { 
      fprintf(RED_OUT, "\nSyntax error: negative timing distance in modal operator at line %1d.\n",
        lineno
      );
      exit(0);
    }
    else if (ub > ALL_CLOCK_TIMING_BOUND) { 
      ALL_CLOCK_TIMING_BOUND = ub; 
      CLOCK_POS_INFINITY = 2*ub+1; 
      CLOCK_NEG_INFINITY = -1 * CLOCK_POS_INFINITY; 
/*
      fprintf(RED_OUT, 
        "\nError: a timing constant %1d in TCTL specification bigger than the greatest \n", 
        ub 
      ); 
      fprintf(RED_OUT, 
        "       timing constant %1d used in the model at line %1d.\n", 
        ALL_CLOCK_TIMING_BOUND, lineno
      ); 
      exit(0);  
*/
    } 

    var_modal_clock->u.clock.ub = ub;
    $$ = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));
    switch ($2) {
    case ARITH_EQ:
      $$->lb = $$->ub = 2*ub;
      break;
    case ARITH_NEQ:
      if ($2) {
        $$->lb = 2*ub + 1;
        $$->ub = 2*ub - 1;
      }
      else {
        $$->lb = 2*ub + 1;
        $$->ub = CLOCK_POS_INFINITY;
      }
      break;
    case ARITH_LEQ:
      $$->lb = 0;
      $$->ub = 2*ub;
      break;
    case ARITH_GEQ:
      $$->lb = 2*ub;
      $$->ub = CLOCK_POS_INFINITY;
      break;
    case ARITH_GREATER:
      $$->lb = 2*ub + 1;
      $$->ub = CLOCK_POS_INFINITY;
      break;
    case ARITH_LESS:
      if (!ub) {
        fprintf(RED_OUT, "\nSyntax error: negative timing distance in modal operator at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
      $$->lb = 0;
      $$->ub = 2*ub - 1;
      break;
    }
  }
|
  PS_LCURLY lboundary { 
    push_scope(SCOPE_RANGE_DECLARATION); 
  } 
  exp_arith PS_COMMA count_omega rboundary PS_RCURLY {
    struct parse_variable_type	*pv;
    int 			lb, ub, modal_lb, modal_ub;
    
    pop_scope(); 
    /*
    if (PARSE_INITIAL_EXP) {
      fprintf(RED_OUT, "\nStarting interval monitoring parse initial condition in single modal temporal logics\n");
      print_parse_subformula_structure(PARSE_INITIAL_EXP, 0);
      fflush(RED_OUT);
    }
    */
    if ($4->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    else { 
      int	flag; 
      float	flb, fub; 
      
      flag = get_integer_range($4, 0, &lb, &ub, &flb, &fub); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in modal range lb at line %1d.\n", 
          lineno 
        ); 
        pcform($4); 
        fflush(RED_OUT); 
        bk(0); 
      } 
      if (lb != ub) { 
        fprintf(RED_OUT, "\nSyntax error: range timing distances %1d..%1d in modal operator at line %1d.\n", 
          lb, ub, lineno
        ); 
        exit(0); 
      } 
      else if (ub < 0) { 
        fprintf(RED_OUT, "\nSyntax error: negative timing distance in modal operator at line %1d.\n",
          lineno
        );
        exit(0);
      } 
      else if (ub > ALL_CLOCK_TIMING_BOUND) { 
        ALL_CLOCK_TIMING_BOUND = ub; 
        CLOCK_POS_INFINITY = 2*ub+1; 
        CLOCK_NEG_INFINITY = -1 * CLOCK_POS_INFINITY; 
/*
        fprintf(RED_OUT, 
          "\nError: a timing constant %1d in TCTL specification bigger than the greatest \n", 
          ub 
        ); 
        fprintf(RED_OUT, 
          "       timing constant %1d used in the model at line %1d.\n", 
          ALL_CLOCK_TIMING_BOUND, lineno
        ); 
        exit(0);  
*/
      } 
      modal_lb = ub; 
    }
    
    if ($6 == NULL) { 
      modal_ub = -1; 
    }
    else if ($6->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    else { 
      int	flag; 
      float	flb, fub; 
      
      flag = get_integer_range($6, 0, &lb, &ub, &flb, &fub); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in modal range ub at line %1d.\n", 
          lineno 
        ); 
        pcform($4); 
        fflush(RED_OUT); 
        bk(0); 
      } 
      if (lb != ub) { 
        fprintf(RED_OUT, "\nSyntax error: range timing distances %1d..%1d in modal operator at line %1d.\n", 
          lb, ub, lineno
        ); 
        exit(0); 
      } 
      else if (ub < 0) { 
        fprintf(RED_OUT, "\nSyntax error: negative timing distance in modal operator at line %1d.\n",
          lineno
        );
        exit(0);
      } 
      else if (ub > ALL_CLOCK_TIMING_BOUND) { 
        ALL_CLOCK_TIMING_BOUND = ub; 
        CLOCK_POS_INFINITY = 2*ub+1; 
        CLOCK_NEG_INFINITY = -1 * CLOCK_POS_INFINITY; 
/*
        fprintf(RED_OUT, 
          "\nError: a timing constant %1d in TCTL specification bigger than the greatest \n", 
          ub 
        ); 
        fprintf(RED_OUT, 
          "       timing constant %1d used in the model at line %1d.\n", 
          ALL_CLOCK_TIMING_BOUND, lineno
        ); 
        exit(0);  
*/
      } 
      modal_ub = ub; 
    }
    var_modal_clock->u.clock.ub = modal_lb;
    if (var_modal_clock->u.clock.ub < modal_ub)
      var_modal_clock->u.clock.ub = modal_ub;

    $$ = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));

    if ($2)
      $$->lb = 2*modal_lb;
    else
      $$->lb = 2*modal_lb + 1;

    if (modal_ub == -1) {
      if ($7) {
        fprintf(RED_OUT, "\nSyntax error: interval infinity bound with closed interval at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
      $$->ub = CLOCK_POS_INFINITY;
    }
    else {
      if ($7)
        $$->ub = 2*modal_ub;
      else
        $$->ub = 2*modal_ub - 1;

      if ($$->lb > $$->ub) {
        fprintf(RED_OUT, "\nSyntax error: time interval bound reversed at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
    }
  }
|
  {
    $$ = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));
    $$->lb = 0;
    $$->ub = CLOCK_POS_INFINITY;
  }
;


lboundary :
  PS_LBRAC {
    $$ = TYPE_TRUE;
  }
|
  PS_LPAR {
    $$ = TYPE_FALSE;
  }
;


rboundary :
  PS_RBRAC {
    $$ = TYPE_TRUE;
  }
|
  PS_RPAR {
    $$ = TYPE_FALSE;
  }
;


count_omega :
  exp_arith {
    $$ = $1;
  }
|
  PS_INFINITY {
    $$ = NULL;
  }
;


token_variable : 
  PS_VARIABLE { 
    $$ = (struct pnp_var_type *) malloc(sizeof(struct pnp_var_type)); 
    $$->pvar = CURRENT_TOKEN_VAR; 
    $$->status = 0; 
  }; 
  
token_sync : 
  PS_SYNC { 
    $$ = CURRENT_TOKEN_VAR; 
  }; 
 
 

/*********************************************************************
 *
 *	Grammar rules for event condition
 */



  

system_info: 
  PS_SYSTEM PS_INFO { 
    CUR_SCOPE[++TOP_SCOPE] = SCOPE_SYSTEM_INFO; 
  } 
  name_list {     
    pop_scope(); 
    system_info_process($4); 
  } 
; 

name_list : 
  PS_IDENTIFIER name_list {
    $$ = push_name($1, $2); 
  }
| { 
    $$ = NULL; 
  }; 










    
/*********************************************************************
 *  Syntax for the run time redlib sync transitions. 
 */
parties : 
  PS_NUMBER PS_COLON xtion {
    struct xtion_type			*old_xtion_table; 
    int					old_xtion_count, pi; 
    struct parse_redlib_party_link_type	*p; 
    
    PARSER_INPUT_SYNC_XTION->party_count++; 
    p = (struct parse_redlib_party_link_type *) 
      malloc(sizeof(struct parse_redlib_party_link_type)); 
    p->proc = $1; 

    old_xtion_table = XTION;  
    old_xtion_count = XTION_COUNT; 
    
    XTION = p->xtion 
    = (struct xtion_type *) malloc(sizeof(struct xtion_type)); 
    CURRENT_XTION->index = 0; 
    xtion_entry_fillin(CURRENT_XTION); 

    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      XTION[0].red_trigger[pi] 
      = red_local(XTION[0].parse_xtion->trigger_exp, pi, 0);
    }
    process_xtion_effect_alloc(XTION[0].statement); 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) {
      process_xtion_statement_fillin(pi, XTION[0].statement); 
    }

    XTION = old_xtion_table; 
    XTION_COUNT = old_xtion_count; 

    p->next_parse_redlib_party_link = PARSER_INPUT_SYNC_XTION->party_list; 
    PARSER_INPUT_SYNC_XTION->party_list = p;
  } 
  parties 
| { 
    /* empty parties. */ 
  }; 
  
  
/*********************************************************************
 *  Syntax for the run time redlib quantification expressions. 
 */
quantify_segments : 
  path_quantifier { 
    struct ps_quantify_link_type	*q; 
    
    q = (struct ps_quantify_link_type *) 
      malloc(sizeof(struct ps_quantify_link_type));  
    q->next_ps_quantify_link = PARSER_QUANTIFICATION_LIST; 
    PARSER_QUANTIFICATION_LIST = q; 
    q->op = $1; 
  }
  one_var_index { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing one var index %1d:%s.\n", 
      $3, VAR[$3].NAME
    ); 
    #endif 
  } 
  PS_COMMA { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing a comma ',' \n"); 
    #endif 
  } 
  quantify_restriction { 
    PARSER_QUANTIFICATION_LIST->var_index = $3; 
  }
  quantify_segments 
| { 
    $$ = 0; 
  } ; 
  
  
signed_number : 
  PS_NUMBER { 
    $$ = $1; 
  }
| PS_MINUS PS_NUMBER { 
    $$ = -1 * $2; 
  }; 
  
  
one_var_index : 
/* 
  PS_MODE PS_LBRAC PS_NUMBER PS_RBRAC { 
    if ($4 <= PROCESS_COUNT && $4 >= 1) { 
      $$ = variable_index[TYPE_DISCRETE][$4][OFFSET_MODE]; 
    } 
    else { 
      fprintf(RED_OUT, 
        "\nError: a mode variable is used with process index %1d.\n", 
        $4
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }   
  } 
| PS_VARIABLE PS_LBRAC {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nA local variable %d:%s to be identified.\n", 
      CURRENT_TOKEN_VAR->index, 
      CURRENT_TOKEN_VAR->name
    ); 
    #endif 
  }
  PS_NUMBER {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nA local variable %d:%s with process %1d to be identified.\n", 
      CURRENT_TOKEN_VAR->index, 
      CURRENT_TOKEN_VAR->name,
      $4 
    ); 
    #endif 
  }
  PS_RBRAC { 
    if (   (CURRENT_TOKEN_VAR->status & FLAG_LOCAL_VARIABLE)
        && $4 <= PROCESS_COUNT 
        && $4 >= 1
        ) { 
      $$ = variable_index[CURRENT_TOKEN_VAR->type][$4][CURRENT_TOKEN_VAR->index]; 
    } 
    else { 
      fprintf(RED_OUT, "\nError: a non-local variable %s is used with process index %1d.\n", 
        CURRENT_TOKEN_VAR->name, $4
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  } 
| 
*/ 
  PS_VARIABLE { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nA global variable %d:%s identified.\n", 
      CURRENT_TOKEN_VAR->index, 
      CURRENT_TOKEN_VAR->name
    ); 
    #endif 
    if (CURRENT_TOKEN_VAR->status & FLAG_LOCAL_VARIABLE) { 
      fprintf(RED_OUT, "\nError: a non-global variable %s is used in global quantification without a process index.\n", 
        CURRENT_TOKEN_VAR->name 
      ); 
      fflush(RED_OUT); 
      exit(0); 
    }
    else { 
      $$ = variable_index[CURRENT_TOKEN_VAR->type][0][CURRENT_TOKEN_VAR->index]; 
    } 
  }; 
  


quantify_restriction : 
  PS_LPAR { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing '(' for quantify_restriction.\n"); 
    #endif 
  } 
  global_condition { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing global condition for quantify_restriction.\n"); 
    pcform($3); 
    #endif 
  } 
  PS_RPAR one_quantify_op_restriction { 
    struct ps_exp_type	*e; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing ')' for quantify_restriction.\n"); 
    #endif 

    PARSER_QUANTIFICATION_LIST->exp_restriction = $3; 
    PARSER_QUANTIFICATION_LIST->op_restriction = $6; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "parsing global before mode index fillin.\n"); 
    pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
    #endif 

    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      PARSER_QUANTIFICATION_LIST->exp_restriction
      = exp_static_evaluation(PARSER_QUANTIFICATION_LIST->exp_restriction, 
        FLAG_NO_PI_STATIC_EVAL, NULL    
      ); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "parsing global after mode index fillin.\n"); 
      pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
      #endif 

      PARSER_QUANTIFICATION_LIST->exp_restriction
        = rec_ineq_analyze(PARSER_QUANTIFICATION_LIST->exp_restriction); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "parsing global after ineq analysis.\n"); 
      pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
      #endif 

      PARSER_QUANTIFICATION_LIST->exp_restriction 
      = shorthand_analysis(PARSER_QUANTIFICATION_LIST->exp_restriction);
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nquantificaiton restriciton exp:\n");
      pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
      fflush(RED_OUT);
      #endif 
    }
    var_index_fillin(PARSER_QUANTIFICATION_LIST->exp_restriction); 
/*
    fillin_indirect_reference(
      PROC_GLOBAL, PARSER_QUANTIFICATION_LIST->exp_restriction
    );
*/

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nafter indirect referencing for PC=%1d\n", PROCESS_COUNT); 
    pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
    fflush(RED_OUT);
    #endif 

    if ((GSTATUS[INDEX_PARSE] & MASK_MODEL_PROCESSING) 
        > FLAG_MODEL_PARSING_ONLY
        ) {
      e = spec_global(PARSER_QUANTIFICATION_LIST->exp_restriction, 
        PROC_GLOBAL, 
        FLAG_LAZY_EVALUATION, 
        0
      ); 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nafter spec global for PC=%1d\n", PROCESS_COUNT); 
      pcform(PARSER_QUANTIFICATION_LIST->exp_restriction); 
      fflush(RED_OUT);
      #endif 

      PARSER_QUANTIFICATION_LIST->red_restriction = e->u.rpred.red; 
      #ifdef RED_DEBUG_YACC_MODE
      fprintf(RED_OUT, "\nafter spec global with RED restriction:\n"); 
      red_print_graph(PARSER_QUANTIFICATION_LIST->red_restriction); 
      fflush(RED_OUT);
      #endif 
  } }
| PS_EXCLAMATION { 
    struct ps_exp_type	*e; 
    
    PARSER_QUANTIFICATION_LIST->exp_restriction = NULL; 
    PARSER_QUANTIFICATION_LIST->op_restriction = NOT; 
    PARSER_QUANTIFICATION_LIST->red_restriction = NULL; 
  } 
| { 
    PARSER_QUANTIFICATION_LIST->exp_restriction = NULL; 
    PARSER_QUANTIFICATION_LIST->op_restriction = -1; 
    PARSER_QUANTIFICATION_LIST->red_restriction = NULL; 
  }; 


one_quantify_op_restriction : 
  PS_AND { 
    $$ = AND; 
  }
| PS_OR { 
    $$ = OR; 
  } 
| PS_IMPLY { 
    $$ = IMPLY; 
  }; 

%%

#include "lex.redlib.c"


int	redliberror(s)
     char 	*s;
{
  fprintf(RED_OUT,"%s at line %d!  Last token read:%s\n", s, lineno, redlibtext);
  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
  bk(0); 
  exit(0); 
/*	redlib_warning(s, (char *)0); */
}
  /* redliberror() */  


int	redlibwrap() 
{
//  fclose(redlibin); 
  return(1); 
}
/* redlibwrap() */ 

  

int	redlib_warning(s,t)
     char *s,*t;
{
  fprintf(RED_OUT, "Warning! line %d : %s ", lineno, s);
  if (t) 
    fprintf(RED_OUT, " %s",t);
}


 






