/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         redlibparse
#define yylex           redliblex
#define yyerror         redliberror
#define yydebug         redlibdebug
#define yynerrs         redlibnerrs

#define yylval          redliblval
#define yychar          redlibchar

/* Copy the first part of user declarations.  */
#line 1 "redgram.y" /* yacc.c:339  */
 
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
  

#line 8508 "redgram.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "redgram.tab.h".  */
#ifndef YY_REDLIB_REDGRAM_TAB_H_INCLUDED
# define YY_REDLIB_REDGRAM_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int redlibdebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    PS_IDENTIFIER = 258,
    PS_INLINE_ARGUMENT = 259,
    PS_PROCESS = 260,
    PS_ROLE = 261,
    PS_URGENT = 262,
    PS_PROCESS_COUNT = 263,
    PS_MODE_COUNT = 264,
    PS_XTION_COUNT = 265,
    PS_ASSIGNMENT = 266,
    PS_GUARD = 267,
    PS_ERASE = 268,
    PS_GLOBALLY = 269,
    PS_MODE = 270,
    PS_XTIONS = 271,
    PS_ADDRESSES = 272,
    PS_RATE = 273,
    PS_WHEN = 274,
    PS_MAY = 275,
    PS_GOTO = 276,
    PS_IN = 277,
    PS_WHILE = 278,
    PS_IF = 279,
    PS_ELSE = 280,
    PS_LOCAL = 281,
    PS_GLOBAL = 282,
    PS_STACK = 283,
    PS_MEMORY = 284,
    PS_BIRD = 285,
    PS_BIRD_PLUS = 286,
    PS_BIRD_MINUS = 287,
    PS_PARAMETER = 288,
    PS_FORMULA = 289,
    PS_QUANTIFY = 290,
    PS_SYSTEM = 291,
    PS_INFO = 292,
    PS_CALL = 293,
    PS_RETURN = 294,
    PS_CPLUG = 295,
    PS_CLOCK = 296,
    PS_DENSE = 297,
    PS_DISCRETE = 298,
    PS_FLOAT = 299,
    PS_DOUBLE = 300,
    PS_STREAM = 301,
    PS_ORDERED = 302,
    PS_UNORDERED = 303,
    PS_OPEN = 304,
    PS_CLOSE = 305,
    PS_INPUT = 306,
    PS_OUTPUT = 307,
    PS_FROM_STREAM = 308,
    PS_TO_STREAM = 309,
    PS_FREE = 310,
    PS_MALLOC = 311,
    PS_BOOLEAN = 312,
    PS_SYNCHRONIZER = 313,
    PS_INLINE = 314,
    PS_TCTL = 315,
    PS_DEBUG = 316,
    PS_RISK = 317,
    PS_GOAL = 318,
    PS_MATRIX = 319,
    PS_CHECK = 320,
    PS_DIRTY = 321,
    PS_LEAKS = 322,
    PS_REDLIB = 323,
    PS_SESSION = 324,
    PS_PARAMETRIC = 325,
    PS_SAFETY = 326,
    PS_BRANCHING = 327,
    PS_BISIMULATION = 328,
    PS_SIMULATION = 329,
    PS_P = 330,
    PS_INFINITY = 331,
    PS_BIT_AND = 332,
    PS_BIT_OR = 333,
    PS_AND = 334,
    PS_OR = 335,
    PS_NOT = 336,
    PS_BIT_NOT = 337,
    PS_TRUE = 338,
    PS_FALSE = 339,
    PS_IMPLY = 340,
    PS_RIGHTARROW = 341,
    PS_UNTIL = 342,
    PS_ALWAYS = 343,
    PS_EVENTUALLY = 344,
    PS_EVENT = 345,
    PS_WITH = 346,
    PS_ON = 347,
    PS_RESET = 348,
    PS_THROUGH = 349,
    PS_EVENTS = 350,
    PS_FORALL = 351,
    PS_EXISTS = 352,
    PS_ALMOST = 353,
    PS_OFTEN = 354,
    PS_ASSUME = 355,
    PS_STRONG = 356,
    PS_WEAK = 357,
    PS_EQ = 358,
    PS_NEQ = 359,
    PS_LESS = 360,
    PS_LEQ = 361,
    PS_GREATER = 362,
    PS_GEQ = 363,
    PS_INC = 364,
    PS_DEC = 365,
    PS_CLEAR = 366,
    PS_PLUS = 367,
    PS_MINUS = 368,
    PS_MULTIPLY = 369,
    PS_DIVIDE = 370,
    PS_MODULO = 371,
    PS_SUM = 372,
    PS_LPAR = 373,
    PS_RPAR = 374,
    PS_LBRAC = 375,
    PS_RBRAC = 376,
    PS_LCURLY = 377,
    PS_RCURLY = 378,
    PS_NUMBER = 379,
    PS_HEX_NUMBER = 380,
    PS_FLOAT_NUMBER = 381,
    PS_NULL = 382,
    PS_INITIAL = 383,
    PS_CHANGE = 384,
    PS_SIMULATE = 385,
    PS_DEADLOCK = 386,
    PS_ZENO = 387,
    PS_INDEX = 388,
    PS_PRIMED = 389,
    PS_COMMA = 390,
    PS_DDOTS = 391,
    PS_COLON = 392,
    PS_SEMICOLON = 393,
    PS_EXCLAMATION = 394,
    PS_QUESTION = 395,
    PS_VARIABLE = 396,
    PS_BDD = 397,
    PS_SYNC = 398,
    PS_QFD = 399,
    PS_CONSTRUCT = 400,
    PS_WINDOW = 401,
    PS_POSITION = 402,
    PS_RECTANGLE = 403,
    PS_SHAPE = 404,
    PS_SQUARE = 405,
    PS_OVAL = 406,
    PS_CIRCLE = 407,
    PS_TRIANGLE = 408,
    PS_LEFTWARD = 409,
    PS_RIGHTWARD = 410,
    PS_UPWARD = 411,
    PS_DOWNWARD = 412,
    PS_COLOR = 413,
    PS_RED = 414,
    PS_WHITE = 415,
    PS_BLACK = 416,
    PS_BLUE = 417,
    PS_YELLOW = 418,
    PS_GREEN = 419,
    PS_POINT = 420,
    PS_DISCRETE_INLINE_CALL = 421,
    PS_BOOLEAN_INLINE_CALL = 422,
    PS_MACRO_CONSTANT = 423
  };
#endif
/* Tokens.  */
#define PS_IDENTIFIER 258
#define PS_INLINE_ARGUMENT 259
#define PS_PROCESS 260
#define PS_ROLE 261
#define PS_URGENT 262
#define PS_PROCESS_COUNT 263
#define PS_MODE_COUNT 264
#define PS_XTION_COUNT 265
#define PS_ASSIGNMENT 266
#define PS_GUARD 267
#define PS_ERASE 268
#define PS_GLOBALLY 269
#define PS_MODE 270
#define PS_XTIONS 271
#define PS_ADDRESSES 272
#define PS_RATE 273
#define PS_WHEN 274
#define PS_MAY 275
#define PS_GOTO 276
#define PS_IN 277
#define PS_WHILE 278
#define PS_IF 279
#define PS_ELSE 280
#define PS_LOCAL 281
#define PS_GLOBAL 282
#define PS_STACK 283
#define PS_MEMORY 284
#define PS_BIRD 285
#define PS_BIRD_PLUS 286
#define PS_BIRD_MINUS 287
#define PS_PARAMETER 288
#define PS_FORMULA 289
#define PS_QUANTIFY 290
#define PS_SYSTEM 291
#define PS_INFO 292
#define PS_CALL 293
#define PS_RETURN 294
#define PS_CPLUG 295
#define PS_CLOCK 296
#define PS_DENSE 297
#define PS_DISCRETE 298
#define PS_FLOAT 299
#define PS_DOUBLE 300
#define PS_STREAM 301
#define PS_ORDERED 302
#define PS_UNORDERED 303
#define PS_OPEN 304
#define PS_CLOSE 305
#define PS_INPUT 306
#define PS_OUTPUT 307
#define PS_FROM_STREAM 308
#define PS_TO_STREAM 309
#define PS_FREE 310
#define PS_MALLOC 311
#define PS_BOOLEAN 312
#define PS_SYNCHRONIZER 313
#define PS_INLINE 314
#define PS_TCTL 315
#define PS_DEBUG 316
#define PS_RISK 317
#define PS_GOAL 318
#define PS_MATRIX 319
#define PS_CHECK 320
#define PS_DIRTY 321
#define PS_LEAKS 322
#define PS_REDLIB 323
#define PS_SESSION 324
#define PS_PARAMETRIC 325
#define PS_SAFETY 326
#define PS_BRANCHING 327
#define PS_BISIMULATION 328
#define PS_SIMULATION 329
#define PS_P 330
#define PS_INFINITY 331
#define PS_BIT_AND 332
#define PS_BIT_OR 333
#define PS_AND 334
#define PS_OR 335
#define PS_NOT 336
#define PS_BIT_NOT 337
#define PS_TRUE 338
#define PS_FALSE 339
#define PS_IMPLY 340
#define PS_RIGHTARROW 341
#define PS_UNTIL 342
#define PS_ALWAYS 343
#define PS_EVENTUALLY 344
#define PS_EVENT 345
#define PS_WITH 346
#define PS_ON 347
#define PS_RESET 348
#define PS_THROUGH 349
#define PS_EVENTS 350
#define PS_FORALL 351
#define PS_EXISTS 352
#define PS_ALMOST 353
#define PS_OFTEN 354
#define PS_ASSUME 355
#define PS_STRONG 356
#define PS_WEAK 357
#define PS_EQ 358
#define PS_NEQ 359
#define PS_LESS 360
#define PS_LEQ 361
#define PS_GREATER 362
#define PS_GEQ 363
#define PS_INC 364
#define PS_DEC 365
#define PS_CLEAR 366
#define PS_PLUS 367
#define PS_MINUS 368
#define PS_MULTIPLY 369
#define PS_DIVIDE 370
#define PS_MODULO 371
#define PS_SUM 372
#define PS_LPAR 373
#define PS_RPAR 374
#define PS_LBRAC 375
#define PS_RBRAC 376
#define PS_LCURLY 377
#define PS_RCURLY 378
#define PS_NUMBER 379
#define PS_HEX_NUMBER 380
#define PS_FLOAT_NUMBER 381
#define PS_NULL 382
#define PS_INITIAL 383
#define PS_CHANGE 384
#define PS_SIMULATE 385
#define PS_DEADLOCK 386
#define PS_ZENO 387
#define PS_INDEX 388
#define PS_PRIMED 389
#define PS_COMMA 390
#define PS_DDOTS 391
#define PS_COLON 392
#define PS_SEMICOLON 393
#define PS_EXCLAMATION 394
#define PS_QUESTION 395
#define PS_VARIABLE 396
#define PS_BDD 397
#define PS_SYNC 398
#define PS_QFD 399
#define PS_CONSTRUCT 400
#define PS_WINDOW 401
#define PS_POSITION 402
#define PS_RECTANGLE 403
#define PS_SHAPE 404
#define PS_SQUARE 405
#define PS_OVAL 406
#define PS_CIRCLE 407
#define PS_TRIANGLE 408
#define PS_LEFTWARD 409
#define PS_RIGHTWARD 410
#define PS_UPWARD 411
#define PS_DOWNWARD 412
#define PS_COLOR 413
#define PS_RED 414
#define PS_WHITE 415
#define PS_BLACK 416
#define PS_BLUE 417
#define PS_YELLOW 418
#define PS_GREEN 419
#define PS_POINT 420
#define PS_DISCRETE_INLINE_CALL 421
#define PS_BOOLEAN_INLINE_CALL 422
#define PS_MACRO_CONSTANT 423

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 8435 "redgram.y" /* yacc.c:355  */

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

#line 8908 "redgram.tab.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE redliblval;

int redlibparse (void);

#endif /* !YY_REDLIB_REDGRAM_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 8923 "redgram.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1216

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  169
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  206
/* YYNRULES -- Number of rules.  */
#define YYNRULES  409
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  742

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   423

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154,
     155,   156,   157,   158,   159,   160,   161,   162,   163,   164,
     165,   166,   167,   168
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,  8587,  8587,  8587,  8653,  8658,  8658,  8668,  8678,  8681,
    8703,  8706,  8668,  8796,  8824,  8830,  8824,  8879,  8885,  8879,
    8934,  8938,  8934,  8948,  8951,  8948,  9009,  9014,  9159,  9216,
    9312,  9338,  9531,  9559,  9009,  9574,  9578,  9587,  9587,  9701,
    9708,  9719,  9719,  9738,  9762,  9763,  9768,  9768,  9812,  9812,
    9816,  9820,  9816,  9824,  9824,  9898,  9910,  9898,  9918,  9921,
    9924,  9931,  9934,  9937,  9940,  9948,  9956,  9959,  9962,  9965,
    9968,  9971,  9976,  9979,  9985, 10022, 10063, 10122, 10184, 10184,
   10262, 10294, 10301, 10301, 10312, 10312, 10326, 10330, 10333, 10338,
   10344, 10352, 10355, 10362, 10365, 10369, 10362, 10382, 10385, 10392,
   10398, 10402, 10410, 10430, 10449, 10464, 10470, 10473, 10476, 10479,
   10485, 10531, 10534, 10542, 10547, 10553, 10566, 10572, 10573, 10580,
   10581, 10586, 10639, 10716, 10764, 10768, 10771, 10716, 10817, 10817,
   10826, 10833, 10845, 10851, 10864, 10869, 10888, 10907, 10926, 10950,
   10962, 10962, 10993, 10993, 11015, 11015, 11030, 11090, 11097, 11098,
   11103, 11111, 11122, 11125, 11128, 11131, 11136, 11136, 11166, 11191,
   11212, 11218, 11310, 11323, 11326, 11329, 11332, 11335, 11352, 11366,
   11385, 11437, 11455, 11468, 11477, 11488, 11499, 11512, 11525, 11661,
   11765, 11793, 11826, 11829, 11840, 11843, 11848, 11851, 11856, 11859,
   11878, 11881, 11904, 11911, 11917, 11923, 11959, 11959, 11980, 11983,
   11986, 12001, 12001, 12016, 12030, 12045, 12064, 12067, 12089, 12092,
   12045, 12165, 12184, 12187, 12209, 12212, 12165, 12284, 12284, 12315,
   12327, 12343, 12357, 12368, 12378, 12392, 12403, 12416, 12429, 12444,
   12444, 12469, 12481, 12482, 12487, 12517, 12554, 12554, 12568, 12579,
   12594, 12593, 12638, 12637, 12693, 12707, 12706, 12760, 12773, 12777,
   12800, 12800, 12829, 12827, 12927, 12924, 12964, 12977, 12964, 13023,
   13043, 13043, 13054, 13061, 13065, 13071, 13071, 13145, 13148, 13145,
   13181, 13213, 13256, 13301, 13301, 13339, 13342, 13345, 13348, 13356,
   13356, 13382, 13389, 13401, 13413, 13426, 13443, 13460, 13474, 13489,
   13502, 13517, 13533, 13545, 13557, 13567, 13583, 13599, 13615, 13631,
   13643, 13646, 13653, 13660, 13673, 13660, 13710, 13722, 13734, 13746,
   13754, 13765, 13773, 13780, 13787, 13806, 13830, 13830, 13862, 13867,
   13874, 13928, 13984, 13987, 13990, 13996, 14005, 14018, 14021, 14049,
   14237, 14240, 14248, 14254, 14260, 14266, 14280, 14286, 14292, 14298,
   14304, 14310, 14320, 14324, 14328, 14332, 14336, 14342, 14346, 14356,
   14356, 14378, 14389, 14389, 14412, 14418, 14429, 14432, 14418, 14472,
   14472, 14487, 14491, 14499, 14504, 14504, 14516, 14517, 14524, 14535,
   14524, 14559, 14562, 14570, 14570, 14665, 14665, 14819, 14828, 14832,
   14839, 14843, 14850, 14854, 14861, 14868, 14884, 14884, 14894, 14897,
   14915, 14915, 14949, 14958, 14967, 14974, 14979, 14958, 14983, 14989,
   14992, 15046, 15068, 15073, 15068, 15154, 15161, 15169, 15172, 15175
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "PS_IDENTIFIER", "PS_INLINE_ARGUMENT",
  "PS_PROCESS", "PS_ROLE", "PS_URGENT", "PS_PROCESS_COUNT",
  "PS_MODE_COUNT", "PS_XTION_COUNT", "PS_ASSIGNMENT", "PS_GUARD",
  "PS_ERASE", "PS_GLOBALLY", "PS_MODE", "PS_XTIONS", "PS_ADDRESSES",
  "PS_RATE", "PS_WHEN", "PS_MAY", "PS_GOTO", "PS_IN", "PS_WHILE", "PS_IF",
  "PS_ELSE", "PS_LOCAL", "PS_GLOBAL", "PS_STACK", "PS_MEMORY", "PS_BIRD",
  "PS_BIRD_PLUS", "PS_BIRD_MINUS", "PS_PARAMETER", "PS_FORMULA",
  "PS_QUANTIFY", "PS_SYSTEM", "PS_INFO", "PS_CALL", "PS_RETURN",
  "PS_CPLUG", "PS_CLOCK", "PS_DENSE", "PS_DISCRETE", "PS_FLOAT",
  "PS_DOUBLE", "PS_STREAM", "PS_ORDERED", "PS_UNORDERED", "PS_OPEN",
  "PS_CLOSE", "PS_INPUT", "PS_OUTPUT", "PS_FROM_STREAM", "PS_TO_STREAM",
  "PS_FREE", "PS_MALLOC", "PS_BOOLEAN", "PS_SYNCHRONIZER", "PS_INLINE",
  "PS_TCTL", "PS_DEBUG", "PS_RISK", "PS_GOAL", "PS_MATRIX", "PS_CHECK",
  "PS_DIRTY", "PS_LEAKS", "PS_REDLIB", "PS_SESSION", "PS_PARAMETRIC",
  "PS_SAFETY", "PS_BRANCHING", "PS_BISIMULATION", "PS_SIMULATION", "PS_P",
  "PS_INFINITY", "PS_BIT_AND", "PS_BIT_OR", "PS_AND", "PS_OR", "PS_NOT",
  "PS_BIT_NOT", "PS_TRUE", "PS_FALSE", "PS_IMPLY", "PS_RIGHTARROW",
  "PS_UNTIL", "PS_ALWAYS", "PS_EVENTUALLY", "PS_EVENT", "PS_WITH", "PS_ON",
  "PS_RESET", "PS_THROUGH", "PS_EVENTS", "PS_FORALL", "PS_EXISTS",
  "PS_ALMOST", "PS_OFTEN", "PS_ASSUME", "PS_STRONG", "PS_WEAK", "PS_EQ",
  "PS_NEQ", "PS_LESS", "PS_LEQ", "PS_GREATER", "PS_GEQ", "PS_INC",
  "PS_DEC", "PS_CLEAR", "PS_PLUS", "PS_MINUS", "PS_MULTIPLY", "PS_DIVIDE",
  "PS_MODULO", "PS_SUM", "PS_LPAR", "PS_RPAR", "PS_LBRAC", "PS_RBRAC",
  "PS_LCURLY", "PS_RCURLY", "PS_NUMBER", "PS_HEX_NUMBER",
  "PS_FLOAT_NUMBER", "PS_NULL", "PS_INITIAL", "PS_CHANGE", "PS_SIMULATE",
  "PS_DEADLOCK", "PS_ZENO", "PS_INDEX", "PS_PRIMED", "PS_COMMA",
  "PS_DDOTS", "PS_COLON", "PS_SEMICOLON", "PS_EXCLAMATION", "PS_QUESTION",
  "PS_VARIABLE", "PS_BDD", "PS_SYNC", "PS_QFD", "PS_CONSTRUCT",
  "PS_WINDOW", "PS_POSITION", "PS_RECTANGLE", "PS_SHAPE", "PS_SQUARE",
  "PS_OVAL", "PS_CIRCLE", "PS_TRIANGLE", "PS_LEFTWARD", "PS_RIGHTWARD",
  "PS_UPWARD", "PS_DOWNWARD", "PS_COLOR", "PS_RED", "PS_WHITE", "PS_BLACK",
  "PS_BLUE", "PS_YELLOW", "PS_GREEN", "PS_POINT",
  "PS_DISCRETE_INLINE_CALL", "PS_BOOLEAN_INLINE_CALL", "PS_MACRO_CONSTANT",
  "$accept", "parse_result", "$@1", "result_of_choices", "$@2", "$@3",
  "$@4", "$@5", "$@6", "$@7", "$@8", "$@9", "$@10", "$@11", "$@12", "$@13",
  "$@14", "$@15", "mode_xtion_system", "$@16", "$@17", "$@18", "$@19",
  "$@20", "$@21", "$@22", "$@23", "window_drawing_options", "processes",
  "$@24", "process_count_declaration_tail", "process_names", "$@25",
  "variable_declarations", "variable_declaration", "$@26", "$@27", "$@28",
  "$@29", "$@30", "$@31", "$@32", "var_scope", "optional_memory_use",
  "var_use", "stream_type", "variable_names", "possible_discrete_range",
  "$@33", "inline_exp_declarations", "inline_exp_declaration", "$@34",
  "$@35", "inline_formal_argument_declaration",
  "inline_formal_argument_list", "modes", "mode", "$@36", "$@37", "$@38",
  "mode_start", "mode_drawing_options", "mode_drawing_position_option",
  "mode_drawing_shape_option", "shape_triangle_direction",
  "mode_drawing_color_option", "mode_rules", "rules", "rule", "vrates",
  "vrate", "xtion", "$@39", "$@40", "$@41", "$@42", "xtion_points", "$@43",
  "point_list", "stream_operations", "stream_operation", "$@44", "$@45",
  "actions", "$@46", "trigger_condition", "synchronizations",
  "synchronization", "event_direction", "sync_address", "$@47",
  "statements", "statement", "assignment", "pure_number", "lbrac", "rbrac",
  "lbound", "rbound", "assign_dest", "local_condition", "$@48",
  "multiplicative_op", "initial", "$@49", "specification", "$@50", "$@51",
  "$@52", "$@53", "$@54", "$@55", "$@56", "$@57", "$@58", "$@59", "$@60",
  "task_type", "debug", "$@61", "game_proc_indices",
  "nontrivial_game_proc_indices", "global_condition", "$@62", "formula",
  "fmla_imply", "$@63", "fmla_disjlist", "$@64", "fmla_conjlist", "$@65",
  "fmla_conj", "$@66", "$@67", "$@68", "$@69", "$@70", "optional_event",
  "$@71", "fmla_literal", "$@72", "$@73", "$@74", "$@75",
  "optional_event_direction", "exp_general", "$@76", "sexp_arith",
  "exp_arith", "sexp_multiply", "exp_multiply", "sexp_term",
  "exp_bit_term", "exp_term", "$@77", "$@78", "$@79",
  "inline_actual_arguments", "inline_actual_argument_list",
  "complete_operand", "base_variable", "optional_address", "rel_op",
  "single_modal", "path_quantifier", "fairness", "$@80",
  "global_fairness_sequence", "$@81", "multiple_global_fairness", "$@82",
  "$@83", "$@84", "$@85", "fairness_strength", "global_fairness", "$@86",
  "optional_event_fairness", "event_fairness", "$@87", "$@88",
  "optional_event_postcond", "time_restriction", "$@89", "$@90",
  "lboundary", "rboundary", "count_omega", "token_variable", "token_sync",
  "system_info", "$@91", "name_list", "parties", "$@92",
  "quantify_segments", "$@93", "$@94", "$@95", "$@96", "signed_number",
  "one_var_index", "quantify_restriction", "$@97", "$@98",
  "one_quantify_op_restriction", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,   362,   363,   364,
     365,   366,   367,   368,   369,   370,   371,   372,   373,   374,
     375,   376,   377,   378,   379,   380,   381,   382,   383,   384,
     385,   386,   387,   388,   389,   390,   391,   392,   393,   394,
     395,   396,   397,   398,   399,   400,   401,   402,   403,   404,
     405,   406,   407,   408,   409,   410,   411,   412,   413,   414,
     415,   416,   417,   418,   419,   420,   421,   422,   423
};
# endif

#define YYPACT_NINF -651

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-651)))

#define YYTABLE_NINF -373

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -651,    76,    20,  -651,  -651,  -651,   -12,    -3,  -651,  -651,
     -81,  -651,  -651,  -651,  1048,   -42,  -651,  -651,  -651,    68,
    -651,   -15,    88,  -651,  -651,  -651,  -651,  -651,  -651,     1,
    1048,  1048,   149,   841,  -651,  -651,  -651,  -651,   169,  -651,
    -651,  -651,  -651,  -651,  -651,    32,   238,   109,  -651,    -5,
     413,  -651,    41,  -651,    62,   746,  -651,   746,  -651,  -651,
    -651,  -651,  -651,   746,    74,  -651,     1,    -5,  -651,  -651,
     107,   180,   746,   134,   151,   238,  -651,   109,   102,  -651,
     159,   167,  1048,  1048,  1048,  -651,  -651,  -651,  1048,  1048,
    1048,  1048,  1048,  1048,   168,   190,   220,  -651,   295,  -651,
     306,  -651,  -651,  -651,  -651,   352,   746,   746,  -651,  -651,
    -651,  -651,   256,   279,   282,  -651,   223,  -651,    16,  -651,
    -651,   227,   237,   248,  -651,   264,   387,   102,  -651,  -651,
    -651,   281,   134,  -651,  1048,  1048,  1048,  -651,    79,  -651,
    -651,   260,   238,   238,  -651,   109,  -651,  -651,  -651,  -651,
     218,  1048,  1048,  1048,  -651,  -651,   276,  -651,   285,  -651,
     159,   330,   341,   350,  -651,   407,   416,   317,   592,   310,
     319,  -651,  -651,  -651,  -651,   340,   451,  -651,   887,   337,
     238,   238,   109,  -651,   124,   349,   359,  -651,  -651,   175,
     199,   268,   320,   -42,  1048,   746,   337,  -651,   746,   746,
     746,   452,  -651,  -651,  -651,  -651,  -651,  -651,   841,  -651,
    -651,  -651,  -651,  -651,  -651,   397,  -651,  -651,  -651,   351,
    -651,  -651,   242,    -8,  -651,   887,  -651,   139,  1048,  -651,
    -651,  -651,  -651,  -651,  -651,   280,  -651,  -651,  -651,  -651,
     371,  -651,   887,  -651,   368,  -651,  1048,  -651,  -651,  -651,
     422,  -651,   490,  -651,  -651,  -651,   242,   240,   448,   887,
     887,  -651,   500,  -651,  -651,   382,  -651,  -651,  -651,   388,
     321,  -651,  -651,   114,   368,   217,   418,   -83,   -79,  -651,
    -651,  -651,  -651,   506,  -651,   453,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,   151,   112,   377,  -651,
     139,   421,   167,    78,   378,   222,   376,   384,   385,  1048,
     409,  -651,   321,  1048,   887,   418,  -651,  -651,  -651,  -651,
    -651,   746,  -651,  -651,  -651,   525,   391,  1048,  -651,   113,
    1048,    60,  -651,   506,   506,   395,   841,  -651,  -651,  -651,
    -651,  -651,   393,   396,   411,  -651,   398,  -651,   400,   402,
     399,  -651,  -651,    22,  1048,    31,  -651,   284,   151,   746,
    1048,  1048,   414,  -651,  -651,    68,   401,  -651,  -651,    56,
     535,  -651,    61,   541,   542,   453,   144,   412,   412,  1048,
    -651,   887,   424,   421,  -651,  -651,  -651,    78,   410,   415,
    -651,   496,   497,  -651,   289,  -651,  -651,  -651,  -651,  -651,
    -651,   432,    18,   -90,  -651,   420,  -651,   143,   126,   746,
    -651,  -651,   525,  -651,  -651,  -651,   438,   438,  -651,   544,
    -651,  -651,   144,  -651,   154,   419,   221,   116,   746,   423,
    -651,   167,   441,  -651,  -651,     0,  1048,   510,   445,   545,
    -651,  -651,  1048,   536,   746,  -651,   374,   444,   449,  -651,
      14,  -651,  -651,  -651,   446,  -651,   569,   556,  -651,  -651,
    -651,   887,   454,  -651,  -651,   388,    12,   437,    -5,    63,
       0,  -651,  -651,  -651,   457,   301,     9,  -651,  -651,  -651,
     221,   196,  -651,   265,   447,  -651,   460,   458,   463,  -651,
    -651,  -651,   450,   887,   151,  -651,  -651,  1048,  -651,  -651,
    -651,  -651,   455,   440,  -651,   223,  -651,  -651,  -651,  -651,
    -651,   464,  -651,  -651,  -651,  -651,   583,  -651,   841,   746,
    -651,   148,   442,  -651,   118,   456,   669,   311,  -651,   474,
       0,   591,   479,   481,   566,   601,  -651,   -95,   440,  -651,
    -651,   440,  -651,    37,  -651,  -651,  1048,  -651,  -651,   482,
     485,   471,  -651,  -651,  -651,   -33,   548,    35,  -651,  -651,
     584,  -651,  -651,   493,   502,   465,   887,   262,  -651,  -651,
    -651,  -651,   480,   483,  -651,  -651,  -651,    10,  -651,  -651,
     -95,   499,  -651,   292,   115,   503,   504,   328,  -651,  -651,
    -651,   338,   486,   491,   492,  -651,  -651,  -651,   562,  -651,
     507,  -651,   629,   475,    69,  -651,   515,  -651,  -651,   516,
     517,   634,   635,  -651,   505,  -651,   -95,   509,  -651,  -651,
     968,   512,   513,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,   514,   518,   522,   524,    15,  -651,  -651,   421,   519,
     440,   440,   634,  -651,   520,  -651,   -95,  -651,   568,   526,
     221,  -651,  -651,  1048,  1048,   139,  -651,   530,  -651,   531,
    -651,  -651,  -651,  -651,  -651,   623,  -651,  -651,   521,  -651,
    1014,  -651,  -651,  -651,   543,   538,   -58,   440,  -651,  -651,
     208,   221,   167,   167,  -651,     6,  -651,  -651,   -92,  -651,
    -651,  -651,   527,   528,   532,   523,  -651,   540,   408,  -651,
     549,  -651,  -651,  -651,  -651,   552,  -651,  -651,  -651,   547,
     546,  -651,  -651,  -651,  -651,  1048,  1048,   523,   554,   807,
    -651,  -651,   547,  -651,   841,   887,   151,   167,   167,  -651,
     130,   557,   559,   887,  -651,  -651,   230,   167,   167,  -651,
    -651,  -651
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
       2,     0,    36,     1,     7,     5,     0,     0,    20,    23,
       0,     3,     4,    26,   233,   392,   196,    14,    17,   398,
     236,     0,     0,   318,   311,   312,   313,   330,   314,     0,
       0,     0,     0,     0,   306,   307,   308,   309,     0,   384,
     319,   316,   315,     8,   232,   235,   287,   291,   299,   321,
     335,   331,     0,     6,     0,   278,   236,   278,   347,   348,
     393,    21,    24,   278,     0,    27,     0,   320,   302,   301,
       0,     0,   278,     0,   281,   284,   289,   294,   321,   310,
     324,   351,     0,     0,     0,   198,   199,   200,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   329,     0,    13,
     272,   277,   275,   263,   264,     0,   278,   278,   276,   273,
     197,   238,   239,   244,   247,   259,     0,   265,   351,    15,
      18,     0,     0,     0,   237,     0,     0,     0,   303,   292,
     293,     0,   265,   300,     0,     0,     0,   327,     0,   317,
     349,     0,   285,   286,   234,   290,   297,   298,   296,   295,
       0,     0,     0,     0,   123,   390,     0,   250,     0,   249,
     324,     0,     0,     0,   385,   270,     0,     0,   278,     0,
       0,   401,   394,    22,    25,     0,     0,    28,     0,     0,
     282,   283,   288,   323,   326,     0,     0,     9,   328,     0,
       0,     0,   130,   392,     0,   278,   248,   274,   278,   278,
     278,     0,   336,   337,   338,   339,   340,   341,     0,   256,
     342,   343,   346,   345,   344,     0,   252,    16,    19,     0,
      35,    37,    45,     0,   279,     0,   322,   354,   233,   334,
     332,   333,   128,   124,   391,     0,   251,   241,   243,   246,
       0,   266,     0,   254,   377,   395,     0,    59,    60,    58,
      64,    48,     0,    72,    73,    29,    45,     0,     0,     0,
       0,   325,     0,   361,   362,     0,   352,   359,    10,   132,
     134,   271,   268,     0,   377,     0,   262,   406,    40,    61,
      62,    63,    53,     0,    46,    81,    44,    69,    68,    65,
      66,    67,    70,    71,    55,    50,   304,     0,     0,   350,
     354,   236,   351,     0,     0,     0,     0,     0,     0,     0,
       0,   125,   134,     0,     0,   262,   379,   378,   373,   375,
     260,   278,   402,   405,   396,     0,     0,     0,    75,     0,
       0,     0,    30,     0,     0,     0,     0,   355,   353,   368,
     364,   360,     0,     0,     0,   399,     0,   129,     0,     0,
       0,   140,   142,     0,     0,     0,   133,     0,   257,   278,
       0,     0,     0,   253,   236,   398,    41,    39,    38,     0,
       0,    49,     0,     0,     0,    81,    92,    56,    51,     0,
     280,     0,     0,   367,   363,    11,   400,     0,     0,     0,
     137,     0,     0,   139,     0,   155,   153,   196,   152,   154,
     126,     0,   149,     0,   269,     0,   255,     0,     0,   278,
     403,   397,     0,    54,    74,    47,    88,    88,    80,     0,
      98,    31,    92,    93,     0,     0,   305,     0,   278,     0,
     366,   351,     0,   135,   136,     0,     0,     0,     0,     0,
     196,   148,     0,   160,   278,   374,     0,     0,     0,    42,
       0,    82,    84,    97,     0,    91,     0,    78,    76,    57,
      52,     0,     0,   365,    12,   132,     0,     0,   195,     0,
       0,   147,   144,   127,     0,     0,     0,   150,   258,   383,
     382,     0,   261,     0,    90,    87,     0,     0,     0,   201,
      32,    94,     0,     0,   356,   369,   131,     0,   192,   194,
     141,   143,     0,     0,   146,     0,   158,   156,   159,   381,
     380,     0,   407,   408,   409,   404,     0,    86,     0,   278,
     236,   220,   101,    77,     0,     0,   278,     0,   138,     0,
       0,     0,     0,     0,     0,     0,   173,     0,     0,   163,
     145,   162,   164,     0,   165,   151,     0,   376,    89,     0,
       0,     0,   221,   224,   222,     0,     0,     0,   225,   223,
       0,    33,   217,     0,     0,   105,     0,     0,   371,   370,
     193,   196,     0,     0,   196,   196,   386,     0,   182,   183,
       0,     0,   161,     0,     0,     0,     0,     0,    83,    85,
     202,     0,     0,     0,     0,   226,   227,   228,   231,   236,
       0,   196,     0,   112,     0,   357,     0,   175,   170,     0,
       0,   389,     0,   172,     0,   166,     0,     0,   185,   184,
       0,     0,     0,   157,   205,   211,   203,   204,   219,   229,
      34,     0,     0,     0,     0,     0,    99,    79,   236,     0,
       0,     0,   389,   387,     0,   177,     0,   179,     0,     0,
     189,   180,   181,   233,   233,   354,   218,     0,    95,     0,
     110,   111,   358,   174,   169,   168,   388,   171,     0,   188,
       0,   206,   212,   230,     0,     0,     0,     0,   176,   190,
       0,   191,   351,   351,   100,     0,    96,   103,     0,   167,
     187,   186,     0,     0,     0,     0,   114,     0,   116,   118,
       0,   106,   107,   108,   109,     0,   178,   207,   213,   120,
       0,   113,   115,   102,   104,   233,   233,     0,     0,     0,
     208,   214,   120,   117,     0,     0,   121,   351,   351,   119,
       0,     0,     0,     0,   209,   215,     0,   351,   351,   122,
     210,   216
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,   274,  -651,   431,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,   138,  -651,  -651,   323,
    -651,  -651,  -651,   277,   183,   278,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,  -651,     5,  -651,   -18,
     -10,   610,  -651,  -651,  -651,  -651,  -651,  -651,   246,   403,
    -651,  -651,  -651,  -651,  -651,  -651,   312,  -651,  -651,  -651,
    -651,  -281,  -591,  -651,  -550,    -7,   -23,  -651,  -651,  -375,
    -386,  -651,   645,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,  -651,
    -219,   640,   -16,  -651,   -49,  -651,  -651,   275,  -651,   529,
    -651,   -87,  -651,  -651,  -651,  -651,  -651,   425,  -651,  -651,
    -651,  -651,  -651,  -651,  -651,   -31,  -651,  -135,   -51,  -651,
      49,  -651,   -14,    21,  -651,  -651,  -651,   567,   501,   -28,
    -651,  -651,   459,  -651,    -9,  -112,  -651,  -293,  -651,  -651,
    -651,  -651,  -651,  -651,   161,    92,  -651,  -651,   354,  -651,
    -651,  -651,   461,  -651,  -651,  -651,  -651,  -651,  -650,  -382,
    -651,  -651,    96,   550,  -651,   380,  -651,  -651,  -651,  -651,
     355,  -651,  -651,  -651,  -651,  -651
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,    11,    15,    14,    81,   228,   302,   431,
      56,   169,    57,   170,    19,   122,    20,   123,    12,    22,
     126,   222,   285,   376,   454,   521,   598,    13,   177,   246,
     326,   367,   412,   255,   256,   330,   283,   334,   425,   327,
     333,   424,   257,   282,   294,   258,   329,   459,   493,   332,
     375,   487,   488,   451,   486,   421,   422,   456,   522,   675,
     423,   564,   565,   603,   705,   636,   686,   697,   698,   718,
     709,   699,   192,   270,   355,   439,   233,   269,   304,   311,
     312,   391,   392,   473,   503,   400,   401,   402,   403,   477,
     546,   540,   541,   542,   580,   620,   692,   649,   680,   543,
      54,    55,    88,   490,   520,   561,   653,   682,   715,   727,
     737,   654,   683,   716,   728,   738,   599,   562,   630,   655,
      43,    44,   340,    63,   110,   111,   161,   112,   162,   113,
     163,   114,   195,   244,   274,   242,   405,   321,   362,   115,
     166,   201,   313,   160,   116,   117,   260,    74,    45,    75,
      46,    76,    77,    48,   178,   335,    80,   139,   185,    49,
      50,    97,   208,   216,   118,   141,   186,   265,   300,   266,
     381,   525,   638,   301,   267,   341,   383,   429,   342,   382,
     526,   569,   276,   360,   361,   319,   511,   481,    51,   165,
     544,   611,   643,    53,   193,    61,   121,   219,   277,   365,
     346,   172,   324,   364,   448,   515
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      47,    67,    73,   184,    62,    78,   168,   338,   120,   268,
      60,   438,   506,   612,   124,    27,    27,   484,   660,   167,
     159,   443,    16,   131,   695,   154,     4,    27,   442,   578,
     614,    17,   700,    82,    83,   322,     5,    21,   127,   591,
     119,   132,   150,   223,    78,   710,     6,     7,   583,   664,
     665,    68,    69,   164,   474,     8,   323,   158,   325,   584,
     467,   687,   701,   702,   703,   704,   646,   710,    47,    47,
      47,   395,   396,   579,   145,   132,     3,   688,    78,    47,
       9,   215,    52,    23,   395,   396,   689,    24,    25,    26,
     184,   499,    18,    65,    27,   502,   668,   595,   592,   593,
     189,   190,   191,   373,   134,   135,   596,   273,   236,    64,
     146,   147,   148,   149,   466,    93,   140,   374,    66,    66,
      47,    47,   182,   545,   296,   297,   466,   507,   259,   696,
     497,   142,   143,   485,    82,    83,   498,    47,    47,    47,
     661,    39,    39,   235,    82,    83,   585,   586,   613,   397,
     508,   419,    70,    39,    28,   572,    29,   398,   399,   420,
     393,    30,    89,    90,    58,    59,    10,    84,    82,    83,
     398,   399,    79,    82,    83,    82,    83,   241,    98,   358,
      47,   134,   135,   180,   181,   606,    91,    92,   609,   610,
     343,   344,    71,    31,   413,   278,    32,    33,   183,   415,
      99,   501,   345,    34,    35,    36,    37,   637,   552,   125,
     553,   554,    38,   555,    47,   633,   556,   262,   557,   558,
      39,   137,    93,    40,   134,   135,   134,   135,   134,   135,
     134,   135,    47,   618,   363,   619,   134,   135,    82,    83,
     263,   264,   134,   135,   128,    41,   427,    42,   370,   336,
     314,   371,   461,   133,   566,    82,    83,   581,   353,   225,
     582,   446,   357,   134,   135,   733,   445,   140,   247,   248,
     249,   250,   406,   348,   349,   251,   369,   138,   559,   372,
     252,   287,   288,   289,   290,   291,   151,    82,    83,   253,
     254,   457,   458,   560,   229,    47,    23,   292,   293,    47,
      24,    25,    26,   394,   129,   380,   130,    27,   152,   407,
     408,    82,    83,    47,   154,   509,    47,   510,   230,   464,
     202,   203,   204,   205,   206,   207,   494,   690,   426,   691,
      82,    83,   616,    82,    83,   316,   156,   317,   153,   188,
      47,  -240,   134,   135,   512,   513,    47,    47,   410,   690,
     514,   691,    85,    86,    87,   157,    60,   478,   524,  -242,
     447,  -245,   673,   263,   264,    47,   164,    28,   171,    29,
     305,   306,   307,   308,    30,   173,   309,   310,    23,   462,
      82,    83,    24,    25,    26,   469,   174,   231,   175,    27,
     176,   475,    82,    83,   194,   480,    82,    83,   187,   271,
     179,    82,    83,   404,   196,    71,    31,   468,   437,    32,
      72,   624,   625,    82,    83,   198,    34,    35,    36,    37,
     505,   199,    47,    82,    83,    38,   695,   154,    47,   200,
     570,   604,    47,    39,   671,   672,    40,  -267,   468,   568,
      82,    83,   468,    94,    95,    96,   527,   623,   217,    28,
     479,    29,   529,   530,   209,    27,    30,   218,    41,   220,
      42,   531,   221,   532,   533,   279,   280,   281,   226,    78,
     550,   377,   378,   237,   238,   468,   534,   224,   535,   536,
     537,   227,   240,    47,   243,   232,   245,   549,    31,   272,
     275,    32,    33,   284,   295,   587,   720,   721,    34,    35,
      36,    37,   468,   298,   551,   299,   303,    38,   320,   328,
     468,   339,   331,   468,   337,    39,   347,   350,    40,   202,
     203,   204,   205,   206,   207,   351,   352,   354,   366,   368,
     379,   384,    47,   387,   385,   386,   409,   390,   414,   -43,
      41,   388,    42,   389,   416,   417,   428,   370,   433,   435,
     440,   436,   617,   434,   466,   444,   450,   460,    66,   453,
     465,   463,   538,   470,   471,   472,   476,   482,   483,   650,
     693,   694,   491,   492,   489,   500,   504,   495,   539,   517,
     518,    39,   516,   631,   726,   519,   484,   547,   523,   563,
     730,   567,   571,   528,   573,   100,    23,   574,   736,   575,
      24,    25,    26,   576,   577,   588,    47,    27,   589,   590,
     597,   600,   468,   468,   602,   731,   732,   594,   607,   681,
     601,   608,   615,   629,   626,   740,   741,   621,   622,   627,
     628,   632,   634,   635,   639,   640,   641,   642,   644,    47,
      47,   658,   659,   645,   669,   101,   102,   647,   677,   468,
     651,   652,   656,   657,   674,   676,    47,   663,   667,   678,
     685,   670,   684,   711,    39,   706,   707,    28,   713,    29,
     708,   714,   100,    23,    30,   103,   104,    24,    25,    26,
     210,   211,   717,   719,    27,   105,   449,   286,    58,    59,
     212,   213,   723,    73,   452,   734,    78,   735,   418,   548,
     455,    47,    47,   712,   729,    71,    31,   722,   155,    32,
     106,   496,   725,   739,   441,   356,    34,    35,    36,    37,
     136,   214,   101,   102,   144,    38,   261,   197,   605,   239,
     662,   107,   108,    39,   318,   315,    40,   430,   666,     0,
     359,     0,   432,   234,    28,   411,    29,     0,     0,   100,
      23,    30,   103,   104,    24,    25,    26,     0,    41,   109,
      42,    27,   105,     0,     0,    58,    59,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    71,    31,     0,     0,    32,   106,     0,     0,
       0,     0,     0,    34,    35,    36,    37,     0,     0,   101,
     102,     0,    38,     0,     0,     0,     0,  -372,   107,   108,
      39,    23,     0,    40,     0,    24,    25,    26,     0,     0,
       0,    28,    27,    29,     0,     0,     0,     0,    30,   103,
     104,     0,     0,     0,     0,    41,   109,    42,     0,   105,
       0,     0,    58,    59,     0,    23,     0,     0,     0,    24,
      25,    26,     0,     0,     0,     0,    27,     0,     0,    71,
      31,     0,     0,    32,   106,     0,     0,     0,     0,     0,
      34,    35,    36,    37,     0,     0,     0,     0,     0,    38,
       0,     0,    28,     0,    29,   107,   108,    39,     0,    30,
      40,    23,     0,     0,     0,    24,    25,    26,     0,     0,
       0,     0,    27,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    41,   109,    42,     0,    28,     0,    29,     0,
      71,    31,     0,    30,    32,   724,     0,   619,     0,     0,
       0,    34,    35,    36,    37,     0,     0,     0,     0,     0,
      38,     0,     0,     0,     0,     0,     0,     0,    39,     0,
       0,    40,     0,     0,    71,    31,     0,     0,    32,    72,
       0,     0,    28,     0,    29,    34,    35,    36,    37,    30,
       0,     0,    23,    41,    38,    42,    24,    25,    26,     0,
       0,     0,    39,    27,     0,    40,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      71,    31,     0,     0,    32,    33,     0,    41,     0,    42,
       0,    34,    35,    36,    37,     0,     0,     0,    23,     0,
      38,     0,    24,    25,    26,     0,     0,     0,    39,    27,
       0,    40,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    28,     0,    29,     0,     0,     0,     0,
      30,     0,    23,    41,     0,    42,    24,    25,    26,     0,
       0,     0,     0,    27,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   648,    31,     0,     0,    32,    33,     0,     0,    28,
     679,    29,    34,    35,    36,    37,    30,     0,     0,     0,
       0,    38,     0,     0,     0,     0,     0,     0,     0,    39,
       0,     0,    40,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    28,     0,    29,     0,     0,    31,     0,
      30,    32,    33,     0,    41,     0,    42,     0,    34,    35,
      36,    37,     0,     0,     0,     0,     0,    38,     0,     0,
       0,     0,     0,     0,     0,    39,     0,     0,    40,     0,
       0,     0,    31,     0,     0,    32,    33,     0,     0,     0,
       0,     0,    34,    35,    36,    37,     0,     0,     0,     0,
      41,    38,    42,     0,     0,     0,     0,     0,     0,    39,
       0,     0,    40,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    41,     0,    42
};

static const yytype_int16 yycheck[] =
{
      14,    29,    33,   138,    20,    33,   118,   300,    57,   228,
      19,   397,     3,     3,    63,    15,    15,     3,     3,     3,
     107,   403,    34,    72,    18,    19,     6,    15,   118,   124,
     580,    34,   124,   112,   113,   118,    16,   118,    66,    72,
      56,    72,    93,   178,    72,   695,    26,    27,    11,   640,
     641,    30,    31,   143,   440,    35,   139,   106,   137,    22,
     435,   119,   154,   155,   156,   157,   616,   717,    82,    83,
      84,    53,    54,   168,    88,   106,     0,   135,   106,    93,
      60,   168,   124,     4,    53,    54,   677,     8,     9,    10,
     225,   466,    95,     5,    15,   470,   646,    62,   131,   132,
     151,   152,   153,    43,   112,   113,    71,   242,   195,   124,
      89,    90,    91,    92,   114,   120,   100,    57,   118,   118,
     134,   135,   136,   505,   259,   260,   114,   118,   136,   123,
     118,    82,    83,   119,   112,   113,   124,   151,   152,   153,
     125,   141,   141,   194,   112,   113,   109,   110,   138,   118,
     141,     7,     3,   141,    75,   530,    77,   139,   140,    15,
     138,    82,    53,    54,    96,    97,   146,   135,   112,   113,
     139,   140,     3,   112,   113,   112,   113,   208,   137,   314,
     194,   112,   113,   134,   135,   571,    77,    78,   574,   575,
     302,   113,   113,   114,   138,   246,   117,   118,   119,   138,
     138,   138,   124,   124,   125,   126,   127,   138,    60,   135,
      62,    63,   133,    65,   228,   601,    68,    78,    70,    71,
     141,   119,   120,   144,   112,   113,   112,   113,   112,   113,
     112,   113,   246,   118,   321,   120,   112,   113,   112,   113,
     101,   102,   112,   113,   137,   166,   381,   168,   135,   137,
     136,   138,   136,   119,   136,   112,   113,   538,   309,   135,
     541,   135,   313,   112,   113,   135,   123,   100,    26,    27,
      28,    29,   359,    51,    52,    33,   327,   118,   130,   330,
      38,    41,    42,    43,    44,    45,   118,   112,   113,    47,
      48,   137,   138,   145,   119,   309,     4,    57,    58,   313,
       8,     9,    10,   354,   124,   336,   126,    15,   118,   360,
     361,   112,   113,   327,    19,   119,   330,   121,   119,   431,
     103,   104,   105,   106,   107,   108,   461,   119,   379,   121,
     112,   113,    40,   112,   113,   118,    30,   120,   118,   121,
     354,    85,   112,   113,    79,    80,   360,   361,   364,   119,
      85,   121,   114,   115,   116,     3,   365,   444,   493,    80,
     409,    79,   655,   101,   102,   379,   143,    75,   141,    77,
      49,    50,    51,    52,    82,   138,    55,    56,     4,   428,
     112,   113,     8,     9,    10,   436,   138,   119,   124,    15,
       3,   442,   112,   113,   118,   446,   112,   113,   138,   119,
     119,   112,   113,   119,   119,   113,   114,   435,   119,   117,
     118,    73,    74,   112,   113,    85,   124,   125,   126,   127,
     119,    80,   436,   112,   113,   133,    18,    19,   442,    79,
     119,   566,   446,   141,   653,   654,   144,    30,   466,   526,
     112,   113,   470,    30,    31,    32,   497,   119,   138,    75,
      76,    77,    12,    13,   137,    15,    82,   138,   166,   119,
     168,    21,    11,    23,    24,    43,    44,    45,   119,   497,
     519,   333,   334,   198,   199,   503,    36,   140,    38,    39,
      40,   122,    30,   497,    87,   165,   135,   518,   114,   118,
     122,   117,   118,     3,    46,   546,   715,   716,   124,   125,
     126,   127,   530,     3,   520,   123,   118,   133,    90,     3,
     538,    90,    59,   541,   137,   141,   138,   141,   144,   103,
     104,   105,   106,   107,   108,   141,   141,   118,     3,   138,
     135,   138,   546,   135,   138,   124,   122,   138,     3,   138,
     166,   141,   168,   141,     3,     3,   122,   135,   138,    53,
     118,    54,   583,   138,   114,   135,   118,   138,   118,    15,
     119,   138,   122,    53,   119,    20,    30,   123,   119,   620,
     682,   683,     3,    17,   128,   138,   119,   123,   138,   119,
     122,   141,   135,   599,   719,   122,     3,   123,   138,   147,
     725,   135,   118,   138,     3,     3,     4,   118,   733,   118,
       8,     9,    10,    37,     3,   123,   620,    15,   123,   138,
      26,   118,   640,   641,   149,   727,   728,    69,   138,   670,
     118,   138,   123,    61,   138,   737,   738,   124,   124,   138,
     138,   124,     3,   158,   119,   119,   119,     3,     3,   653,
     654,   119,   118,   138,    76,    53,    54,   138,    25,   677,
     138,   138,   138,   135,   124,   124,   670,   138,   138,   138,
     122,   135,   119,   123,   141,   138,   138,    75,   119,    77,
     138,   119,     3,     4,    82,    83,    84,     8,     9,    10,
      88,    89,   135,   137,    15,    93,   412,   256,    96,    97,
      98,    99,   138,   724,   417,   138,   724,   138,   375,   516,
     422,   715,   716,   698,   722,   113,   114,   717,    98,   117,
     118,   465,   719,   736,   402,   312,   124,   125,   126,   127,
      75,   129,    53,    54,    84,   133,   225,   160,   567,   200,
     638,   139,   140,   141,   275,   274,   144,   383,   642,    -1,
     315,    -1,   387,   193,    75,   365,    77,    -1,    -1,     3,
       4,    82,    83,    84,     8,     9,    10,    -1,   166,   167,
     168,    15,    93,    -1,    -1,    96,    97,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   113,   114,    -1,    -1,   117,   118,    -1,    -1,
      -1,    -1,    -1,   124,   125,   126,   127,    -1,    -1,    53,
      54,    -1,   133,    -1,    -1,    -1,    -1,   138,   139,   140,
     141,     4,    -1,   144,    -1,     8,     9,    10,    -1,    -1,
      -1,    75,    15,    77,    -1,    -1,    -1,    -1,    82,    83,
      84,    -1,    -1,    -1,    -1,   166,   167,   168,    -1,    93,
      -1,    -1,    96,    97,    -1,     4,    -1,    -1,    -1,     8,
       9,    10,    -1,    -1,    -1,    -1,    15,    -1,    -1,   113,
     114,    -1,    -1,   117,   118,    -1,    -1,    -1,    -1,    -1,
     124,   125,   126,   127,    -1,    -1,    -1,    -1,    -1,   133,
      -1,    -1,    75,    -1,    77,   139,   140,   141,    -1,    82,
     144,     4,    -1,    -1,    -1,     8,     9,    10,    -1,    -1,
      -1,    -1,    15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   166,   167,   168,    -1,    75,    -1,    77,    -1,
     113,   114,    -1,    82,   117,   118,    -1,   120,    -1,    -1,
      -1,   124,   125,   126,   127,    -1,    -1,    -1,    -1,    -1,
     133,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   141,    -1,
      -1,   144,    -1,    -1,   113,   114,    -1,    -1,   117,   118,
      -1,    -1,    75,    -1,    77,   124,   125,   126,   127,    82,
      -1,    -1,     4,   166,   133,   168,     8,     9,    10,    -1,
      -1,    -1,   141,    15,    -1,   144,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     113,   114,    -1,    -1,   117,   118,    -1,   166,    -1,   168,
      -1,   124,   125,   126,   127,    -1,    -1,    -1,     4,    -1,
     133,    -1,     8,     9,    10,    -1,    -1,    -1,   141,    15,
      -1,   144,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    75,    -1,    77,    -1,    -1,    -1,    -1,
      82,    -1,     4,   166,    -1,   168,     8,     9,    10,    -1,
      -1,    -1,    -1,    15,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   113,   114,    -1,    -1,   117,   118,    -1,    -1,    75,
      76,    77,   124,   125,   126,   127,    82,    -1,    -1,    -1,
      -1,   133,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   141,
      -1,    -1,   144,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    75,    -1,    77,    -1,    -1,   114,    -1,
      82,   117,   118,    -1,   166,    -1,   168,    -1,   124,   125,
     126,   127,    -1,    -1,    -1,    -1,    -1,   133,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   141,    -1,    -1,   144,    -1,
      -1,    -1,   114,    -1,    -1,   117,   118,    -1,    -1,    -1,
      -1,    -1,   124,   125,   126,   127,    -1,    -1,    -1,    -1,
     166,   133,   168,    -1,    -1,    -1,    -1,    -1,    -1,   141,
      -1,    -1,   144,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   166,    -1,   168
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint16 yystos[] =
{
       0,   170,   171,     0,     6,    16,    26,    27,    35,    60,
     146,   172,   187,   196,   174,   173,    34,    34,    95,   183,
     185,   118,   188,     4,     8,     9,    10,    15,    75,    77,
      82,   114,   117,   118,   124,   125,   126,   127,   133,   141,
     144,   166,   168,   289,   290,   317,   319,   321,   322,   328,
     329,   357,   124,   362,   269,   270,   179,   181,    96,    97,
     333,   364,   291,   292,   124,     5,   118,   328,   322,   322,
       3,   113,   118,   314,   316,   318,   320,   321,   328,     3,
     325,   175,   112,   113,   135,   114,   115,   116,   271,    53,
      54,    77,    78,   120,    30,    31,    32,   330,   137,   138,
       3,    53,    54,    83,    84,    93,   118,   139,   140,   167,
     293,   294,   296,   298,   300,   308,   313,   314,   333,   291,
     293,   365,   184,   186,   293,   135,   189,   328,   137,   124,
     126,   293,   314,   119,   112,   113,   271,   119,   118,   326,
     100,   334,   319,   319,   290,   321,   322,   322,   322,   322,
     317,   118,   118,   118,    19,   240,    30,     3,   293,   300,
     312,   295,   297,   299,   143,   358,   309,     3,   334,   180,
     182,   141,   370,   138,   138,   124,     3,   197,   323,   119,
     319,   319,   321,   119,   316,   327,   335,   138,   121,   317,
     317,   317,   241,   363,   118,   301,   119,   326,    85,    80,
      79,   310,   103,   104,   105,   106,   107,   108,   331,   137,
      88,    89,    98,    99,   129,   300,   332,   138,   138,   366,
     119,    11,   190,   316,   140,   135,   119,   122,   176,   119,
     119,   119,   165,   245,   362,   317,   300,   296,   296,   298,
      30,   314,   304,    87,   302,   135,   198,    26,    27,    28,
      29,    33,    38,    47,    48,   202,   203,   211,   214,   136,
     315,   327,    78,   101,   102,   336,   338,   343,   289,   246,
     242,   119,   118,   316,   303,   122,   351,   367,   317,    43,
      44,    45,   212,   205,     3,   191,   202,    41,    42,    43,
      44,    45,    57,    58,   213,    46,   316,   316,     3,   123,
     337,   342,   177,   118,   247,    49,    50,    51,    52,    55,
      56,   248,   249,   311,   136,   351,   118,   120,   331,   354,
      90,   306,   118,   139,   371,   137,   199,   208,     3,   215,
     204,    59,   218,   209,   206,   324,   137,   137,   336,    90,
     291,   344,   347,   334,   113,   124,   369,   138,    51,    52,
     141,   141,   141,   317,   118,   243,   248,   317,   316,   306,
     352,   353,   307,   300,   372,   368,     3,   200,   138,   317,
     135,   138,   317,    43,    57,   219,   192,   215,   215,   135,
     314,   339,   348,   345,   138,   138,   124,   135,   141,   141,
     138,   250,   251,   138,   317,    53,    54,   118,   139,   140,
     254,   255,   256,   257,   119,   305,   300,   317,   317,   122,
     291,   364,   201,   138,     3,   138,     3,     3,   218,     7,
      15,   224,   225,   229,   210,   207,   317,   316,   122,   346,
     347,   178,   369,   138,   138,    53,    54,   119,   269,   244,
     118,   255,   118,   358,   135,   123,   135,   293,   373,   200,
     118,   222,   222,    15,   193,   224,   226,   137,   138,   216,
     138,   136,   293,   138,   334,   119,   114,   268,   328,   317,
      53,   119,    20,   252,   269,   317,    30,   258,   300,    76,
     317,   356,   123,   119,     3,   119,   223,   220,   221,   128,
     272,     3,    17,   217,   316,   123,   247,   118,   124,   268,
     138,   138,   268,   253,   119,   119,     3,   118,   141,   119,
     121,   355,    79,    80,    85,   374,   135,   119,   122,   122,
     273,   194,   227,   138,   316,   340,   349,   317,   138,    12,
      13,    21,    23,    24,    36,    38,    39,    40,   122,   138,
     260,   261,   262,   268,   359,   358,   259,   123,   223,   314,
     293,   291,    60,    62,    63,    65,    68,    70,    71,   130,
     145,   274,   286,   147,   230,   231,   136,   135,   300,   350,
     119,   118,   268,     3,   118,   118,    37,     3,   124,   168,
     263,   260,   260,    11,    22,   109,   110,   317,   123,   123,
     138,    72,   131,   132,    69,    62,    71,    26,   195,   285,
     118,   118,   149,   232,   316,   343,   269,   138,   138,   269,
     269,   360,     3,   138,   263,   123,    40,   314,   118,   120,
     264,   124,   124,   119,    73,    74,   138,   138,   138,    61,
     287,   291,   124,   269,     3,   158,   234,   138,   341,   119,
     119,   119,     3,   361,     3,   138,   263,   138,   113,   266,
     317,   138,   138,   275,   280,   288,   138,   135,   119,   118,
       3,   125,   344,   138,   261,   261,   361,   138,   263,    76,
     135,   289,   289,   336,   124,   228,   124,    25,   138,    76,
     267,   317,   276,   281,   119,   122,   235,   119,   135,   261,
     119,   121,   265,   334,   334,    18,   123,   236,   237,   240,
     124,   154,   155,   156,   157,   233,   138,   138,   138,   239,
     357,   123,   236,   119,   119,   277,   282,   135,   238,   137,
     289,   289,   239,   138,   118,   264,   316,   278,   283,   238,
     316,   334,   334,   135,   138,   138,   316,   279,   284,   265,
     334,   334
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint16 yyr1[] =
{
       0,   169,   171,   170,   172,   173,   172,   174,   175,   176,
     177,   178,   172,   172,   179,   180,   172,   181,   182,   172,
     183,   184,   172,   185,   186,   172,   188,   189,   190,   191,
     192,   193,   194,   195,   187,   196,   196,   198,   197,   199,
     199,   201,   200,   200,   202,   202,   204,   203,   205,   203,
     206,   207,   203,   208,   203,   209,   210,   203,   211,   211,
     211,   212,   212,   212,   212,   213,   213,   213,   213,   213,
     213,   213,   214,   214,   215,   215,   216,   216,   217,   216,
     218,   218,   220,   219,   221,   219,   222,   222,   222,   223,
     223,   224,   224,   226,   227,   228,   225,   229,   229,   230,
     231,   231,   232,   232,   232,   232,   233,   233,   233,   233,
     234,   234,   234,   235,   235,   236,   236,   237,   237,   238,
     238,   239,   239,   241,   242,   243,   244,   240,   246,   245,
     245,   247,   247,   248,   248,   249,   249,   249,   249,   249,
     250,   249,   251,   249,   253,   252,   254,   254,   255,   255,
     256,   256,   257,   257,   257,   257,   259,   258,   258,   258,
     258,   260,   260,   261,   261,   261,   261,   261,   261,   261,
     262,   262,   262,   262,   262,   262,   262,   262,   262,   262,
     262,   262,   263,   263,   264,   264,   265,   265,   266,   266,
     267,   267,   268,   268,   268,   268,   270,   269,   271,   271,
     271,   273,   272,   274,   274,   275,   276,   277,   278,   279,
     274,   280,   281,   282,   283,   284,   274,   285,   274,   274,
     274,   286,   286,   286,   286,   286,   286,   286,   286,   288,
     287,   287,   289,   289,   290,   290,   292,   291,   293,   293,
     295,   294,   297,   296,   296,   299,   298,   298,   300,   300,
     301,   300,   302,   300,   303,   300,   304,   305,   300,   300,
     307,   306,   306,   308,   308,   309,   308,   310,   311,   308,
     308,   308,   308,   312,   308,   313,   313,   313,   313,   315,
     314,   314,   316,   316,   316,   317,   317,   317,   318,   318,
     319,   319,   320,   320,   320,   321,   321,   321,   321,   321,
     322,   322,   322,   323,   324,   322,   322,   322,   322,   322,
     322,   322,   322,   322,   322,   322,   325,   322,   322,   322,
     322,   322,   326,   326,   326,   327,   327,   328,   328,   328,
     329,   329,   330,   330,   330,   330,   331,   331,   331,   331,
     331,   331,   332,   332,   332,   332,   332,   333,   333,   335,
     334,   334,   337,   336,   336,   339,   340,   341,   338,   342,
     338,   343,   343,   344,   345,   344,   346,   346,   348,   349,
     347,   350,   350,   352,   351,   353,   351,   351,   354,   354,
     355,   355,   356,   356,   357,   358,   360,   359,   361,   361,
     363,   362,   362,   365,   366,   367,   368,   364,   364,   369,
     369,   370,   372,   373,   371,   371,   371,   374,   374,   374
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     2,     1,     0,     3,     0,     0,     0,
       0,     0,    13,     4,     0,     0,     6,     0,     0,     6,
       0,     0,     5,     0,     0,     5,     0,     0,     0,     0,
       0,     0,     0,     0,    17,     6,     0,     0,     6,     2,
       0,     0,     3,     1,     2,     0,     0,     5,     0,     4,
       0,     0,     6,     0,     5,     0,     0,     6,     1,     1,
       1,     1,     1,     1,     0,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     1,     1,     3,     0,     6,
       3,     0,     0,     7,     0,     7,     3,     2,     0,     3,
       1,     2,     0,     0,     0,     0,    10,     2,     1,     3,
       6,     0,     7,     5,     7,     0,     1,     1,     1,     1,
       2,     2,     0,     3,     2,     2,     0,     4,     1,     3,
       0,     3,     7,     0,     0,     0,     0,     9,     0,     4,
       0,     6,     0,     2,     0,     4,     4,     3,     7,     3,
       0,     6,     0,     6,     0,     3,     4,     3,     2,     1,
       3,     5,     1,     1,     1,     1,     0,     5,     2,     2,
       0,     2,     1,     1,     1,     1,     3,     7,     5,     5,
       3,     5,     3,     1,     5,     3,     6,     4,     8,     4,
       4,     4,     1,     1,     1,     1,     1,     1,     2,     1,
       1,     1,     2,     4,     2,     1,     0,     2,     1,     1,
       1,     0,     4,     3,     3,     0,     0,     0,     0,     0,
      15,     0,     0,     0,     0,     0,    15,     0,     4,     3,
       0,     1,     1,     1,     1,     1,     2,     2,     2,     0,
       3,     0,     1,     0,     3,     1,     0,     2,     1,     1,
       0,     4,     0,     4,     1,     0,     4,     1,     3,     2,
       0,     4,     0,     7,     0,     8,     0,     0,    10,     1,
       0,     5,     0,     1,     1,     0,     4,     0,     0,     8,
       2,     5,     1,     0,     3,     1,     1,     1,     0,     0,
       8,     1,     3,     3,     1,     3,     3,     1,     3,     1,
       3,     1,     2,     2,     1,     3,     3,     3,     3,     1,
       3,     2,     2,     0,     0,    10,     1,     1,     1,     1,
       2,     1,     1,     1,     1,     1,     0,     3,     1,     1,
       2,     1,     3,     2,     0,     3,     1,     3,     4,     2,
       1,     1,     4,     4,     4,     0,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     0,
       5,     0,     0,     3,     0,     0,     0,     0,    12,     0,
       3,     1,     1,     2,     0,     4,     1,     0,     0,     0,
       7,     1,     0,     0,     5,     0,     8,     0,     1,     1,
       1,     1,     1,     1,     1,     1,     0,     4,     2,     0,
       0,     5,     0,     0,     0,     0,     0,     9,     0,     1,
       2,     1,     0,     0,     6,     1,     0,     1,     1,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 8587 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 10758 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 8628 "redgram.y" /* yacc.c:1646  */
    {
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
  }
#line 10785 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 8653 "redgram.y" /* yacc.c:1646  */
    {
    TYPE_PARSE_CHOICE = TYPE_PARSE_MODE_XTION_SYSTEM; 
    GSTATUS[INDEX_PARSE] = GSTATUS[INDEX_PARSE] | FLAG_PARSER_MODEL_DONE; 
//    fprintf(RED_OUT, "choice of mode transition system input.\n"); 
  }
#line 10795 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 8658 "redgram.y" /* yacc.c:1646  */
    {
    PARSER_INPUT_SYNC_XTION = (struct parse_redlib_sync_xtion_type *) 
      malloc(sizeof(struct parse_redlib_sync_xtion_type)); 
    PARSER_INPUT_SYNC_XTION->status = 0; 
    PARSER_INPUT_SYNC_XTION->party_count = 0; 
    PARSER_INPUT_SYNC_XTION->party_list = 0; 
  }
#line 10807 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 8665 "redgram.y" /* yacc.c:1646  */
    { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_SYNC_XTION; 
  }
#line 10815 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 8668 "redgram.y" /* yacc.c:1646  */
    {
    int	pi; 
    
    CUR_GAME_ROLE = FLAG_GAME_MODL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      PROCESS[pi].status = PROCESS[pi].status & ~MASK_GAME_ROLES; 
    } 
    setup_game_exp(); 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 10830 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 8678 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 10838 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 8681 "redgram.y" /* yacc.c:1646  */
    {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, (yyvsp[-1].gfair)); 
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
#line 10865 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 8703 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 10873 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 8706 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, (yyvsp[-1].gfair)); 
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
#line 10933 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 8761 "redgram.y" /* yacc.c:1646  */
    { 
    int pi, sxi; 
    
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, (yyvsp[0].gfair)); 
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
#line 10973 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 8800 "redgram.y" /* yacc.c:1646  */
    {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_LOCAL; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** After parsing initia condition.\n"); 
    #endif 
    
    PARSER_INPUT_FORMULA = (yyvsp[-1].sp);
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
#line 11002 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 8824 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "hh\n"); 
    #endif 
  }
#line 11013 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 8830 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "kk\n"); 
    #endif 
  }
#line 11024 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 8836 "redgram.y" /* yacc.c:1646  */
    {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_GLOBAL; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "*** After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = (yyvsp[-2].sp);
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
#line 11072 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 8879 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "hh\n"); 
    #endif 
  }
#line 11083 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 8885 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "kk\n"); 
    #endif 
  }
#line 11094 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 8891 "redgram.y" /* yacc.c:1646  */
    {
    TYPE_PARSE_CHOICE = TYPE_PARSE_FORMULA_GLOBAL_EVENTS; 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "*** After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = (yyvsp[-2].sp);
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
#line 11142 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 8934 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    PARSER_QUANTIFICATION_LIST = NULL;    
  }
#line 11151 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 8938 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
    fprintf(RED_OUT, "After parsing the quantify segments.\n"); 
  }
#line 11160 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 8942 "redgram.y" /* yacc.c:1646  */
    { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_QUANTIFY; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** After parsing quantification exp.\n"); 
    #endif 
  }
#line 11171 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 8948 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL_EVENT); 
  }
#line 11179 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 8951 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
  }
#line 11187 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 8954 "redgram.y" /* yacc.c:1646  */
    { 
    TYPE_PARSE_CHOICE = TYPE_PARSE_TCTL; 
    #ifdef RED_DEBUG_YACC_MODE
    printf("*** yacc tctl: After parsing initia condition.\n"); 
    #endif 

    PARSE_SPEC = (yyvsp[-2].sp);
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
#line 11242 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 9009 "redgram.y" /* yacc.c:1646  */
    { 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_PROCESS_COUNT; 
  }
#line 11252 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 9014 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 11401 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 9159 "redgram.y" /* yacc.c:1646  */
    {
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
#line 11462 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 9216 "redgram.y" /* yacc.c:1646  */
    {
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
#line 11563 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 9312 "redgram.y" /* yacc.c:1646  */
    {    
    struct ps_bunit_type	*bu, *bup;

    declare_inline_exp_list = (yyvsp[0].splist); 
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
#line 11593 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 9338 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 11790 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 9531 "redgram.y" /* yacc.c:1646  */
    { 
    PARSE_INITIAL_EXP = (yyvsp[0].sp); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nAfter parsing initial condition\n");
    pcform(PARSE_INITIAL_EXP);
    fflush(RED_OUT);
    #endif 

    ORIG_PARSE_INITIAL_EXP = (yyvsp[0].sp); 
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
#line 11823 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 9559 "redgram.y" /* yacc.c:1646  */
    { 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_DEBUG_INFOS; 
  }
#line 11833 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 9564 "redgram.y" /* yacc.c:1646  */
    {
    pop_scope(); 
    GSTATUS[INDEX_PARSE] 
    = (GSTATUS[INDEX_PARSE] & ~MASK_GRAM_PHASE) 
    | GRAM_PHASE_UNKNOWN; 
  }
#line 11844 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 9574 "redgram.y" /* yacc.c:1646  */
    { 
    WINDOW_WIDTH = (yyvsp[-3].number); 
    WINDOW_HEIGHT = (yyvsp[-1].number); 
  }
#line 11853 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 9578 "redgram.y" /* yacc.c:1646  */
    { 
    WINDOW_WIDTH = FLAG_WINDOW_SIZE_UNKNOWN; 
    WINDOW_HEIGHT = FLAG_WINDOW_SIZE_UNKNOWN; 
  }
#line 11862 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 9587 "redgram.y" /* yacc.c:1646  */
    { 
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (strcmp((yyvsp[-1].string), "count")) {
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
#line 11898 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 9618 "redgram.y" /* yacc.c:1646  */
    { 
    int	flag, original_pc; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      pop_scope(); 

      original_pc = get_value((yyvsp[-2].sp), 0, &flag); 
      (yyval.number) = original_pc; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn process count valuation with flag %1d from ", 
      	      flag
      	      ); 
        print_parse_subformula((yyvsp[-2].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
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
    (yyval.number) = PROCESS_COUNT; 

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
  }
#line 11981 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 9701 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 0; 
/*
    fprintf(RED_OUT, "\nproc name specification.\n"); 
    fflush(RED_OUT); 
*/
  }
#line 11993 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 9708 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = -1; 
/*
    fprintf(RED_OUT, "\nNO proc name specification.\n"); 
    fflush(RED_OUT); 
*/
  }
#line 12005 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 9719 "redgram.y" /* yacc.c:1646  */
    {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (process_name_index > PROCESS_COUNT) { 
        fprintf(RED_OUT, "\nError: More process names than PROCESS_COUNT at line %1d.\n", lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
        exit(5); 
      }
      else if (name_duplicate((yyvsp[0].string), &name_check_holder)) {
        fprintf(RED_OUT, "\nError: Duplicate process name %s at line %1d.\n", (yyvsp[0].string), lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(9); 
      }
      process_list = add_indexed_structure_count
	  	(process_list, process_name_index, (yyvsp[0].string), &process_name_index);
    } 
  }
#line 12026 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 9735 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.string) = NULL; 
  }
#line 12034 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 9738 "redgram.y" /* yacc.c:1646  */
    {
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      if (process_name_index > PROCESS_COUNT) {
        fprintf(RED_OUT, "\nError: More process names than PROCESS_COUNT at line %1d\n", lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(5); 
      }
      else if (name_duplicate((yyvsp[0].string), &name_check_holder)) {
        fprintf(RED_OUT, "\nError: Duplicate process name %s at line %1d.\n", (yyvsp[0].string), lineno);
        for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
        exit(9); 
      }
      process_list = add_indexed_structure_count(
      	process_list, process_name_index, (yyvsp[0].string), &process_name_index
    	); 
      (yyval.string) = NULL; 
    } 
  }
#line 12057 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 9763 "redgram.y" /* yacc.c:1646  */
    { 
  }
#line 12064 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 9768 "redgram.y" /* yacc.c:1646  */
    { 
    
    if (strcmp((yyvsp[0].string), "depth")) {
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
#line 12089 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 9788 "redgram.y" /* yacc.c:1646  */
    { 
    int	flag, original_dc; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      pop_scope(); 

      original_dc = get_value((yyvsp[-1].sp), 0, &flag); 
      (yyval.number) = original_dc; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn memory size valuation with flag %1d from ", 
      	      flag
      	      ); 
        pcform((yyvsp[-1].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, " at line %1d.\n", lineno); 
        fflush(RED_OUT); 
        exit(0); 
      } 
      DEPTH_CALL = original_dc; 
    }
//    fprintf(RED_OUT, "number 7 is %1d.\n", $5); 
    fflush(RED_OUT); 
    (yyval.number) = DEPTH_CALL; 
  }
#line 12118 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 9812 "redgram.y" /* yacc.c:1646  */
    {
    change_scope(SCOPE_GLOBAL);
    CUR_VAR_TYPE = TYPE_PARAMETER;
  }
#line 12127 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 9816 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope((yyvsp[-1].number)); 
    CUR_VAR_TYPE = TYPE_STREAM;
  }
#line 12136 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 9820 "redgram.y" /* yacc.c:1646  */
    { 
    CUR_VAR_HEAD = (yyvsp[0].pvar); 
  }
#line 12144 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 9824 "redgram.y" /* yacc.c:1646  */
    { 
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
      CUR_VAR_TYPE = (yyvsp[0].number);
    }
  }
#line 12164 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 9839 "redgram.y" /* yacc.c:1646  */
    { 
    int	flag, original_ms; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      struct ps_memory_link_type	*m; 
      
      pop_scope(); 

      original_ms = get_value((yyvsp[-1].sp), 0, &flag); 
      (yyval.number) = original_ms; 
      if (flag == FLAG_ANY_VALUE) { 
        fprintf(RED_OUT, 
      	      "ERROR: unknonwn memory size valuation with flag %1d from ", 
      	      flag
      	      ); 
        pcform((yyvsp[-1].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
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
    (yyval.number) = MEMORY_SIZE; 
  }
#line 12228 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 9898 "redgram.y" /* yacc.c:1646  */
    {
    if ((yyvsp[-1].number) == SCOPE_STACK && (yyvsp[0].number) != TYPE_DISCRETE) { 
      fprintf(RED_OUT, 
        "\nERROR: illegal non-discrete stack variable declaration at line %1d.\n", 
        lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    change_scope((yyvsp[-1].number)); 
    CUR_VAR_TYPE = (yyvsp[0].number); 
  }
#line 12245 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 9910 "redgram.y" /* yacc.c:1646  */
    { 
    CUR_VAR_HEAD = (yyvsp[0].pvar); 
  }
#line 12253 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 9918 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = SCOPE_STACK;
  }
#line 12261 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 9921 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = SCOPE_LOCAL;
  }
#line 12269 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 9924 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = SCOPE_GLOBAL;
  }
#line 12277 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 9931 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_DISCRETE; 
  }
#line 12285 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 9934 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_FLOAT; 
  }
#line 12293 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 9937 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_DOUBLE; 
  }
#line 12301 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 9940 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_DISCRETE;
  }
#line 12309 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 9948 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_DISCRETE; 
  }
#line 12317 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 9956 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_FLOAT; 
  }
#line 12325 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 9959 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_DOUBLE; 
  }
#line 12333 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 9962 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_DENSE; 
  }
#line 12341 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 9965 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_CLOCK;
  }
#line 12349 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 9968 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = TYPE_BDD; 
  }
#line 12357 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 9971 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_SYNCHRONIZER;
  }
#line 12365 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 9976 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = GRAM_STREAM_ORDERED; 
  }
#line 12373 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 9979 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = GRAM_STREAM_UNORDERED; 
  }
#line 12381 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 9985 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      register_variable((yyvsp[0].string));
      (yyval.pvar) = (yyvsp[-2].pvar);   
    } 
    else if (pv = var_search((yyvsp[0].string))) { 
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
          (yyvsp[0].string), lineno
        ); 
        exit(0);   
      } 
      else { 
        fprintf(RED_OUT, "\nAn already declared variable %s at line %1d\n", 
          (yyvsp[0].string), lineno 
        ); 
      } 
    } 
    else { 
      fprintf(RED_OUT, "\nError: new variable %s declared in the new rules at line %1d.\n", 
        (yyvsp[0].string), lineno
      ); 
      fprintf(RED_OUT, "With current implementation, you need to start a new session\n"); 
      fprintf(RED_OUT, "to declare new variables. \n"); 
      bk(0); 
    } 
  }
#line 12423 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 10022 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv; 
    
    if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) { 
      (yyval.pvar) = register_variable((yyvsp[0].string)); 
    } 
    else if (pv = var_search((yyvsp[0].string))) { 
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
          (yyvsp[0].string), lineno
        ); 
        exit(0);   
      } 
      else { 
        fprintf(RED_OUT, "\nAn already declared variable %s at line %1d\n", 
          (yyvsp[0].string), lineno 
        ); 
      } 
    } 
    else { 
      fprintf(RED_OUT, "\nError 2: new variable %s declared in the new rules at line %1d.\n", 
        (yyvsp[0].string), lineno
      ); 
      fprintf(RED_OUT, "With current implementation, you need to start a new session\n"); 
      fprintf(RED_OUT, "to declare new variables. \n"); 
      bk(0); 
    } 
  }
#line 12464 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 10063 "redgram.y" /* yacc.c:1646  */
    {
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
#line 12528 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 10122 "redgram.y" /* yacc.c:1646  */
    {
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
#line 12595 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 10184 "redgram.y" /* yacc.c:1646  */
    {
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 12603 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 10187 "redgram.y" /* yacc.c:1646  */
    {
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
          pv->u.disc.lb = (int) (yyvsp[-3].sp); 
          pv->u.disc.ub = (int) (yyvsp[-1].sp); 
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
          pv->u.disc.lb = (int) (yyvsp[-3].sp); 
          pv->u.disc.ub = (int) (yyvsp[-1].sp); 
        }
        break; 
      case SCOPE_GLOBAL: 
        for (pv = declare_global_discrete_list; 
             pv && pv->index >= CUR_VAR_HEAD->index; 
             pv = pv->next_parse_variable
             ) {
          pv->status = pv->status | FLAG_BOUND_DECLARED | FLAG_VAR_BOUNDS_DELAYED_EVAL; 
          pv->u.disc.lb = (int) (yyvsp[-3].sp); 
          pv->u.disc.ub = (int) (yyvsp[-1].sp); 
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
#line 12679 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 10262 "redgram.y" /* yacc.c:1646  */
    { 
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

    (yyval.splist) = declare_inline_exp_list; 
  }
#line 12716 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 10294 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.splist) = declare_inline_exp_list; 
  }
#line 12724 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 10301 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = (yyvsp[0].nlist); 
  }
#line 12732 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 10304 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
    macro_register(FLAG_INLINE_DISCRETE, (yyvsp[-5].string), 
      CURRENT_INLINE_FORMAL_ARGUMENT_COUNT, 
      (yyvsp[-4].nlist), (yyvsp[-1].sp)
    ); 
  }
#line 12745 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 10312 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = (yyvsp[0].nlist); 
  }
#line 12753 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 10315 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_INLINE_FORMAL_ARGUMENT_LIST = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT = 0; 
    macro_register(FLAG_INLINE_BOOLEAN, (yyvsp[-5].string), 
      CURRENT_INLINE_FORMAL_ARGUMENT_COUNT, 
      (yyvsp[-4].nlist), (yyvsp[-1].sp)
    ); 
  }
#line 12766 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 10326 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.nlist) = (yyvsp[-1].nlist); 
  }
#line 12774 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 10330 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.nlist) = NULL; 
  }
#line 12782 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 10333 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.nlist) = NULL; 
  }
#line 12790 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 10338 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.nlist) = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    (yyval.nlist)->name = (yyvsp[-2].string); 
    (yyval.nlist)->next_name_link = (yyvsp[0].nlist); 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT++; 
  }
#line 12801 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 10344 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.nlist) = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    (yyval.nlist)->name = (yyvsp[0].string); 
    (yyval.nlist)->next_name_link = NULL; 
    CURRENT_INLINE_FORMAL_ARGUMENT_COUNT++; 
  }
#line 12812 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 10352 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.mode) = (yyvsp[-1].mode); 
  }
#line 12820 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 10355 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.mode) = NULL; 
  }
#line 12828 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 10362 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_LOCAL); 
  }
#line 12836 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 10365 "redgram.y" /* yacc.c:1646  */
    { 
    add_mode((yyvsp[-2].number), (yyvsp[0].string)); 
  }
#line 12844 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 10369 "redgram.y" /* yacc.c:1646  */
    { 
    add_mode_invariance(CURRENT_MODE, (yyvsp[-1].sp)); 
    CURRENT_MODE->src_lines = combine_name_cycle(
      &red_src_lines, &count_red_src_lines
    ); 
  }
#line 12855 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 10375 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_MODE->parse_xtion_list = (yyvsp[0].xlist);
    pop_scope(); 
  }
#line 12864 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 10382 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = FLAG_MODE_URGENT;
  }
#line 12872 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 10385 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = 0;
  }
#line 12880 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 10398 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_MODE->position_x = (yyvsp[-3].number); 
    CURRENT_MODE->position_y = (yyvsp[-1].number); 
  }
#line 12889 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 10402 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_MODE->position_x = FLAG_MODE_POSITION_UNKNOWN; 
    CURRENT_MODE->position_y = FLAG_MODE_POSITION_UNKNOWN; 
  }
#line 12898 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 10411 "redgram.y" /* yacc.c:1646  */
    { 
    if (!strcmp((yyvsp[-5].string), "rectangle")) {
      CURRENT_MODE->shape = FLAG_MODE_RECTANGLE; 
      CURRENT_MODE->rectangle_width = (yyvsp[-3].number); 
      CURRENT_MODE->rectangle_height = (yyvsp[-1].number); 
    }
    else if (!strcmp((yyvsp[-5].string), "oval")) {
      CURRENT_MODE->shape = FLAG_MODE_OVAL; 
      CURRENT_MODE->oval_xradius = (yyvsp[-3].number); 
      CURRENT_MODE->oval_yradius = (yyvsp[-1].number); 
    }
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        (yyvsp[-5].string), lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
#line 12922 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 10430 "redgram.y" /* yacc.c:1646  */
    { 
    if (!strcmp((yyvsp[-3].string), "square")) {
      CURRENT_MODE->shape = FLAG_MODE_RECTANGLE; 
      CURRENT_MODE->rectangle_width = (yyvsp[-1].number); 
      CURRENT_MODE->rectangle_height = (yyvsp[-1].number); 
    }
    else if (!strcmp((yyvsp[-3].string), "circle")) { 
      CURRENT_MODE->shape = FLAG_MODE_OVAL; 
      CURRENT_MODE->oval_xradius = (yyvsp[-1].number); 
      CURRENT_MODE->oval_yradius = (yyvsp[-1].number); 
    } 
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        (yyvsp[-3].string), lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
#line 12946 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 10450 "redgram.y" /* yacc.c:1646  */
    { 
    if (!strcmp((yyvsp[-5].string), "triangle")) {
      CURRENT_MODE->shape = FLAG_MODE_TRIANGLE; 
      CURRENT_MODE->triangle_radius = (yyvsp[-3].number); 
      CURRENT_MODE->triangle_direction = (yyvsp[-1].number); 
    }
    else { 
      fprintf(RED_OUT, "\nERROR, illegal mode shape %s at line %1d\n", 
        (yyvsp[-5].string), lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
#line 12965 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 10464 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_MODE->shape = FLAG_MODE_SHAPE_UNKNOWN; 
  }
#line 12973 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 10470 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_TRIANGLE_LEFTWARD; 
  }
#line 12981 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 10473 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_TRIANGLE_RIGHTWARD; 
  }
#line 12989 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 10476 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_TRIANGLE_UPWARD; 
  }
#line 12997 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 10479 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_TRIANGLE_DOWNWARD; 
  }
#line 13005 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 10485 "redgram.y" /* yacc.c:1646  */
    { 
    if (   (!strcmp((yyvsp[0].string), "red")) 
        || (!strcmp((yyvsp[0].string), "RED"))
        || (!strcmp((yyvsp[0].string), "Red"))
        ) {
      CURRENT_MODE->color = 0x000000FF;  
    }
    else if (   (!strcmp((yyvsp[0].string), "white")) 
             || (!strcmp((yyvsp[0].string), "WHITE"))
             || (!strcmp((yyvsp[0].string), "White"))
             ) { 
      CURRENT_MODE->color = 0xFFFFFFFF;  
    }
    else if (   (!strcmp((yyvsp[0].string), "black")) 
             || (!strcmp((yyvsp[0].string), "BLACK"))
             || (!strcmp((yyvsp[0].string), "Black"))
             ) {  
      CURRENT_MODE->color = 0x00000000;  
    }
    else if (   (!strcmp((yyvsp[0].string), "blue")) 
             || (!strcmp((yyvsp[0].string), "BLUE"))
             || (!strcmp((yyvsp[0].string), "Blue"))
             ) { 
      CURRENT_MODE->color = 0x00FF0000;  
    }
    else if (   (!strcmp((yyvsp[0].string), "yellow")) 
             || (!strcmp((yyvsp[0].string), "YELLOW"))
             || (!strcmp((yyvsp[0].string), "Yellow"))
             ) { 
      CURRENT_MODE->color = 0x0000FF00;  
    }
    else if (   (!strcmp((yyvsp[0].string), "green")) 
             || (!strcmp((yyvsp[0].string), "GREEN"))
             || (!strcmp((yyvsp[0].string), "Green"))
             ) { 
      CURRENT_MODE->color = 0x00FFFF00;  
    }
    else { 
      fprintf(RED_OUT, 
        "\nERROR: unsupported symbolic color name %s at line %1d.\n", 
        (yyvsp[0].string), lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
  }
#line 13056 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 10531 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_MODE->color = (yyvsp[-1].number);  
  }
#line 13064 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 10534 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_MODE->color = 0xFFFFFFFF;  
  }
#line 13072 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 10544 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.xlist) = (yyvsp[-1].xlist);
  }
#line 13080 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 10547 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.xlist) = NULL;
  }
#line 13088 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 10553 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_xtion_link_type	*pxl;
    if ((yyvsp[-1].xtion) == NULL)
      (yyval.xlist) = (yyvsp[0].xlist);
    else {
      pxl = (struct parse_xtion_link_type *) malloc(sizeof(struct parse_xtion_link_type));
      pxl->parse_xtion = (yyvsp[-1].xtion);
      pxl->next_parse_xtion_link = (yyvsp[0].xlist);
      CURRENT_MODE->xtion_count++;

      (yyval.xlist) = pxl;
    }
  }
#line 13106 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 10566 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.xlist) = NULL; 
  }
#line 13114 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 10572 "redgram.y" /* yacc.c:1646  */
    { (yyval.xtion) = NULL; }
#line 13120 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 10573 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.xtion) = (yyvsp[0].xtion);
  }
#line 13128 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 10581 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = 0;  
  }
#line 13136 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 10586 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_rate_spec_link_type	*rsl;

    rsl = (struct parse_rate_spec_link_type *) malloc(sizeof(struct parse_rate_spec_link_type));
    rsl->rate_var_name = (yyvsp[-2].pnp)->pvar->name;
    rsl->rate_var = (yyvsp[-2].pnp)->pvar; 
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
	      (yyvsp[-2].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    case TYPE_CLOCK:
      fprintf(RED_OUT, "Syntax error: clock %s with rate specificaiton at line %1d.\n",
	      (yyvsp[-2].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
      break;
    case TYPE_DENSE:
      if (!(rsl->rate_var->status & FLAG_LOCAL_VARIABLE)) {
        fprintf(RED_OUT, "Error: illegal rate specification to global dense variable %s at line %1d.\n",
		(yyvsp[-2].pnp)->pvar->name, lineno
		);
	fflush(RED_OUT);
	exit(0);
      }
      break;
    default:
      fprintf(RED_OUT, "Syntax error: an incompatible variable %s for rate specification at line %1d.\n",
 	      (yyvsp[-2].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }

    rsl->next_parse_rate_spec_link = CURRENT_MODE->parse_rate_spec_list;
    CURRENT_MODE->parse_rate_spec_list = rsl;
    CURRENT_MODE->rate_spec_count++;

    rsl->rate_lb = rsl->rate_ub = (yyvsp[0].sp);
    rsl->status = ~(FLAG_RATE_LB_OPEN | FLAG_RATE_UB_OPEN);
  }
#line 13194 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 10639 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_rate_spec_link_type	*rsl;

    rsl = (struct parse_rate_spec_link_type *) malloc(sizeof(struct parse_rate_spec_link_type));
    rsl->rate_var_name = (yyvsp[-6].pnp)->pvar->name;
    rsl->rate_var = (yyvsp[-6].pnp)->pvar;
    if (rsl->rate_var == NULL) {
      fprintf(RED_OUT, "Syntax error: an undeclared variable %s in rate specification at line %1d.\n",
	      (yyvsp[-6].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    else switch (rsl->rate_var->type) {
    case TYPE_DISCRETE:
    case TYPE_POINTER:
      fprintf(RED_OUT, "Syntax error: an uncontinuous variable %s in rate specification at line %1d.\n",
	      (yyvsp[-6].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    case TYPE_CLOCK:
      fprintf(RED_OUT, "Syntax error: clock %s with rate specification at line %1d.\n",
	      (yyvsp[-6].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
      break;
    case TYPE_DENSE:
      if (!(rsl->rate_var->status & FLAG_LOCAL_VARIABLE)) {
        fprintf(RED_OUT, "Error: illegal rate specification to global dense variable %s at line %1d.\n",
		(yyvsp[-6].pnp)->pvar->name, lineno
		);
	fflush(RED_OUT);
	exit(0);
      }
      break;
    default:
      fprintf(RED_OUT, "Syntax error: an incompatible variable %s for rate specification at line %1d.\n",
 	      (yyvsp[-6].pnp)->pvar->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }

    rsl->next_parse_rate_spec_link = CURRENT_MODE->parse_rate_spec_list;
    CURRENT_MODE->parse_rate_spec_list = rsl;
    CURRENT_MODE->rate_spec_count++;


    if ((yyvsp[-4].number) == INTERVAL_LEFT_OPEN) {
      rsl->status = rsl->status | FLAG_RATE_LB_OPEN;
      fprintf(RED_OUT, "\nError: left open bounds in rate specification at line %1d.\n", lineno);
      fflush(RED_OUT);
      exit(0);
    }
    else
      rsl->status = rsl->status & ~FLAG_RATE_LB_OPEN;

    if ((yyvsp[0].number) == INTERVAL_RIGHT_OPEN) {
      rsl->status = rsl->status | FLAG_RATE_UB_OPEN;
      fprintf(RED_OUT, "\nError: right open bounds in rate specification at line %1d.\n", lineno);
      fflush(RED_OUT);
      exit(0);
    }
    else
      rsl->status = rsl->status & ~FLAG_RATE_UB_OPEN;

    rsl->rate_lb = (yyvsp[-3].sp);
    rsl->rate_ub = (yyvsp[-1].sp);
  }
#line 13270 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 10716 "redgram.y" /* yacc.c:1646  */
    {
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
#line 13323 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 10764 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_XTION->stream_operation_count = 0; 
    CURRENT_XTION->stream_operation_list = NULL; 
  }
#line 13332 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 10768 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_XTION->stream_operation_list = (yyvsp[0].pso); 
  }
#line 13340 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 10771 "redgram.y" /* yacc.c:1646  */
    {
    struct ps_bunit_type	*bunitptr, dummy_bu; 
    struct ps_exp_type		*mode_predicate; 
    
    bunitptr = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*
    fprintf(RED_OUT, "bunitptr = %x in xtion rule for var_mode\n", bunitptr); 
    */
    CURRENT_XTION->orig_trigger_exp = (yyvsp[0].sp);     
    mode_predicate = exp_arith(ARITH_EQ, 
      exp_atom(TYPE_DISCRETE, -1, var_mode->name),  
      exp_atom(TYPE_CONSTANT, CURRENT_MODE->index, NULL)
    ); 
    /*
    fprintf(RED_OUT, "yacc literal 2 : TRIGGERING MODE INEQUALITY\n"); 
    fprintf(RED_OUT, "\noriginal triggering condition :\n"); 
    print_parse_subformula_structure(CURRENT_XTION->trigger_exp, 0); 
    */

    CURRENT_XTION->trigger_exp = exp_boolean(AND, (yyvsp[0].sp), mode_predicate); 
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
#line 13377 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 10803 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_XTION->statement = (yyvsp[0].st); 
    (yyval.xtion) = CURRENT_XTION;
    --TOP_SCOPE; 
    
    if (CURRENT_XTION->index == 9) {
      pst9 = CURRENT_XTION; 
    }
  }
#line 13391 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 10817 "redgram.y" /* yacc.c:1646  */
    { 
    LENGTH_CURRENT_POINT_LIST = 0; 
  }
#line 13399 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 129:
#line 10820 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_XTION->intermediate_point_list = (yyvsp[-1].iplist); 
    CURRENT_XTION->intermediate_point_count = LENGTH_CURRENT_POINT_LIST; 
    fprintf(RED_OUT, "\nyacc: After analyzing point list.\n"); 
    fflush(RED_OUT); 
  }
#line 13410 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 130:
#line 10826 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_XTION->intermediate_point_list = NULL; 
    CURRENT_XTION->intermediate_point_count = 0; 
  }
#line 13419 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 131:
#line 10833 "redgram.y" /* yacc.c:1646  */
    { 
    struct index_pair_link_type	*ip; 

    ip = (struct index_pair_link_type *) 
      malloc(sizeof(struct index_pair_link_type)); 
    ip->next_index_pair_link = (yyvsp[0].iplist); 
    ip->coordinate_x = (yyvsp[-4].number); 
    ip->coordinate_y = (yyvsp[-2].number); 

    LENGTH_CURRENT_POINT_LIST++; 
    (yyval.iplist) = ip; 
  }
#line 13436 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 132:
#line 10845 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.iplist) = NULL; 
  }
#line 13444 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 133:
#line 10851 "redgram.y" /* yacc.c:1646  */
    { 
    (yyvsp[-1].pso)->next_parse_stream_operation = (yyvsp[0].pso); 
    CURRENT_XTION->stream_operation_count++; 
    (yyval.pso) = (yyvsp[-1].pso); 
    #ifdef RED_DEBUG_PARSE_MODE 
    fprintf(RED_OUT, "\nredgram: new xi=%1d, soc=%1d, so-op=%1d\n", 
      CURRENT_XTION->index, 
      CURRENT_XTION->stream_operation_count, 
      (yyval.pso)->operation
    ); 
    fflush(RED_OUT);  
    #endif 
  }
#line 13462 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 134:
#line 10864 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.pso) = NULL; 
  }
#line 13470 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 135:
#line 10869 "redgram.y" /* yacc.c:1646  */
    { 
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
    
    (yyval.pso) = pso; 
  }
#line 13494 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 136:
#line 10888 "redgram.y" /* yacc.c:1646  */
    { 
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
    
    (yyval.pso) = pso; 
  }
#line 13518 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 137:
#line 10907 "redgram.y" /* yacc.c:1646  */
    { 
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
    
    (yyval.pso) = pso; 
  }
#line 13542 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 138:
#line 10926 "redgram.y" /* yacc.c:1646  */
    { 
    switch ((yyvsp[-1].sp)->type) { 
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE: 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nSyntax error: at line %1d, illegal malloc operation destination:\n  ", lineno);
      pcform((yyvsp[-1].sp)); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = NULL; 
    CURRENT_STREAM_OP->operation = OP_MALLOC; 

    CURRENT_STREAM_OP->var = (yyvsp[-1].sp); 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation((yyvsp[-4].sp), 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    (yyval.pso) = CURRENT_STREAM_OP; 
  }
#line 13571 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 139:
#line 10950 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_STREAM_OP = (struct parse_stream_operation_type *) 
      malloc(sizeof(struct parse_stream_operation_type));
    CURRENT_STREAM_OP->stream = NULL; 
    CURRENT_STREAM_OP->operation = OP_FREE; 

    CURRENT_STREAM_OP->var = NULL; 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation((yyvsp[-1].sp), 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    (yyval.pso) = CURRENT_STREAM_OP; 
  }
#line 13588 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 140:
#line 10962 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 13606 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 141:
#line 10975 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_STREAM_OP->var = (yyvsp[-1].sp); 
    switch (CURRENT_STREAM_OP->var->type) { 
    case TYPE_REFERENCE: 
    case TYPE_DISCRETE: 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nSyntax error: at line %1d, illegal stream operation destination:", 
        lineno 
      );
      pcform((yyvsp[-1].sp)); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    CURRENT_STREAM_OP->value_exp = NULL; 
    (yyval.pso) = CURRENT_STREAM_OP; 
  }
#line 13629 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 142:
#line 10993 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 13647 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 143:
#line 11006 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_STREAM_OP->var = NULL; 
    CURRENT_STREAM_OP->value_exp = exp_static_evaluation((yyvsp[-1].sp), 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    (yyval.pso) = CURRENT_STREAM_OP; 
  }
#line 13659 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 144:
#line 11015 "redgram.y" /* yacc.c:1646  */
    {
    change_scope(SCOPE_LOCAL); 
/*
    fprintf(RED_OUT, "\nEntering action parsing:\n"); 
    fflush(RED_OUT); 
*/
  }
#line 13671 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 145:
#line 11022 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.st) = (yyvsp[0].st); 
  }
#line 13679 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 146:
#line 11031 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_xtion_sync_type	*xs; 
    struct ps_exp_type			*addr, *qs, *eq; 
    
    (yyval.sp) = (yyvsp[-1].sp); 
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
        (yyval.sp) = exp_boolean(AND, eq, (yyval.sp)); 
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
#line 13743 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 147:
#line 11091 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[-1].sp); 
  }
#line 13751 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 150:
#line 11103 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_XTION->sync_list 
    = add_parse_xtion_sync(
      CURRENT_XTION_SYNC_COUNT, flag_address_type, 
      (yyvsp[-2].number), (yyvsp[-1].pvar), (struct ps_exp_type *) 1, (yyvsp[0].sp)
    ); 
    CURRENT_XTION_SYNC_COUNT++; 
  }
#line 13764 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 151:
#line 11111 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_XTION->sync_list 
    = add_parse_xtion_sync(
      CURRENT_XTION_SYNC_COUNT++, 
      FLAG_ADDRESS_MULTIPLE, 
      (yyvsp[-4].number), (yyvsp[0].pvar), (yyvsp[-2].sp), NULL
    ); 
  }
#line 13777 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 152:
#line 11122 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = -1; 
  }
#line 13785 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 153:
#line 11125 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = -1; 
  }
#line 13793 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 154:
#line 11128 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 1; 
  }
#line 13801 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 155:
#line 11131 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 1; 
  }
#line 13809 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 156:
#line 11136 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_ADDRESS_ENFORCER); 
  }
#line 13817 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 157:
#line 11139 "redgram.y" /* yacc.c:1646  */
    {
    struct exp_shape_type	*es; 

    switch ((es = exp_shape_check((yyvsp[-1].sp)))->type) { 
    case FLAG_EXP_STATIC: 
      free(es); 
      break; 
    default: 
      fprintf(RED_OUT, 
        "\nERROR: At line %1d, illegal dynamic correspondence: ", 
        lineno
      ); 
      pcform((yyvsp[-1].sp)); 
      fprintf(RED_OUT, 
        "       in synchronization.\n"
      ); 
      free(es); 
      fflush(RED_OUT); 
      exit(0); 
    }
    (yyval.sp) = (yyvsp[-1].sp); 
    CURRENT_TOKEN_VAR = NULL; 
    flag_address_type = FLAG_ADDRESS_ENFORCER; 
    --TOP_SCOPE; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  }
#line 13849 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 158:
#line 11166 "redgram.y" /* yacc.c:1646  */
    {
    int	flag; 
    
    (yyval.sp) = ps_exp_alloc(TYPE_QSYNC_HOLDER); 
/*
    if (CURRENT_XTION->index == 1600) { 
      fprintf(RED_OUT, "Target prehit!\n"); 
      fflush(RED_OUT); 
      for (flag = 1; flag; ); 
    } 
*/
    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    push_scope(SCOPE_LOCAL); 
    (yyval.sp)->u.qsholder.place_index = CURRENT_XTION_SYNC_COUNT; 
    (yyval.sp)->u.qsholder.qsync_var_name = (yyvsp[0].string); 
    (yyval.sp)->u.qsholder.qsync_var = check_register_qfd_sync((yyvsp[0].string)); 
    (yyval.sp)->var_status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
    flag_address_type = FLAG_ADDRESS_HOLDER; 
    pop_scope(); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
    CURRENT_XTION->status = CURRENT_XTION->status | FLAG_XTION_QUANTIFIED_SYNC; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYSTEM_QUANTIFIED_SYNC 
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  }
#line 13879 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 159:
#line 11191 "redgram.y" /* yacc.c:1646  */
    {
    int	flag; 

    check_qfd_sync(CURRENT_TOKEN_VAR); 

    (yyval.sp) = ps_exp_alloc(TYPE_QSYNC_HOLDER); 

    CUR_VAR_TYPE = TYPE_QSYNC_HOLDER; 
    push_scope(SCOPE_LOCAL); 
    (yyval.sp)->u.qsholder.place_index = CURRENT_XTION_SYNC_COUNT; 
    (yyval.sp)->u.qsholder.qsync_var_name = CURRENT_TOKEN_VAR->name; 
    (yyval.sp)->u.qsholder.qsync_var = CURRENT_TOKEN_VAR; 
    (yyval.sp)->var_status = FLAG_LOCAL_VARIABLE | FLAG_QUANTIFIED_SYNC;
    flag_address_type = FLAG_ADDRESS_HOLDER; 
    pop_scope(); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
    CURRENT_XTION->status = CURRENT_XTION->status | FLAG_XTION_QUANTIFIED_SYNC; 
    GSTATUS[INDEX_SYNCHRONIZATION] = GSTATUS[INDEX_SYNCHRONIZATION] 
    | FLAG_SYSTEM_QUANTIFIED_SYNC  
    | FLAG_SYNC_ADDRESS_RESRICTION; 
  }
#line 13905 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 160:
#line 11212 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = NULL; 
    flag_address_type = FLAG_ADDRESS_NULL; 
  }
#line 13914 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 161:
#line 11218 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_link_type	*stl, *stlp; 
    struct parse_statement_type		*er, *e1, *e2; 
        
    e1 = (yyvsp[-1].st); 
    e2 = (yyvsp[0].st); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "sequential statement at line %1d.\n1: ", lineno); 
    print_parse_statement_line(e1); 
    fprintf(RED_OUT, "\n2: "); 
    print_parse_statement_line(e2); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
    
    if ((yyvsp[-1].st) == NULL) 
      (yyval.st) = (yyvsp[0].st); 
    else if ((yyvsp[0].st) == NULL) 
      (yyval.st) = (yyvsp[-1].st); 
    else if ((yyvsp[-1].st)->op == ST_SEQ) 
      if ((yyvsp[0].st)->op == ST_SEQ) { 
        for (stl = (yyvsp[-1].st)->u.seq.statement_list; 
             stl->next_parse_statement_link; 
             stl = stl->next_parse_statement_link
             ) ; 
        stl->next_parse_statement_link = (yyvsp[0].st)->u.seq.statement_list; 
        (yyvsp[-1].st)->u.seq.statement_count 
        = (yyvsp[-1].st)->u.seq.statement_count + (yyvsp[0].st)->u.seq.statement_count; 
        (yyvsp[-1].st)->st_status = ((yyvsp[-1].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        free((yyvsp[0].st)); 
        (yyval.st) = (yyvsp[-1].st); 
      } 
      else {
        for (stl = (yyvsp[-1].st)->u.seq.statement_list; stl->next_parse_statement_link; stl = stl->next_parse_statement_link) ;        
        stl->next_parse_statement_link = (struct parse_statement_link_type *) 
                                         malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link->next_parse_statement_link = NULL; 
        stl->next_parse_statement_link->statement = (yyvsp[0].st); 
        (yyvsp[-1].st)->u.seq.statement_count++; 
        (yyvsp[-1].st)->st_status = ((yyvsp[-1].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        (yyval.st) = (yyvsp[-1].st); 
      }
    else 
      if ((yyvsp[0].st)->op == ST_SEQ) { 
        stl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link = (yyvsp[0].st)->u.seq.statement_list; 
        stl->statement = (yyvsp[-1].st); 
        (yyvsp[0].st)->u.seq.statement_list = stl; 
        (yyvsp[0].st)->u.seq.statement_count++; 
        (yyvsp[0].st)->st_status 
        = ((yyvsp[-1].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        (yyval.st) = (yyvsp[0].st); 
      } 
      else {
        stl = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stlp = (struct parse_statement_link_type *) malloc(sizeof(struct parse_statement_link_type)); 
        stl->next_parse_statement_link = stlp; 
        stl->statement = (yyvsp[-1].st); 
        stlp->next_parse_statement_link = NULL; 
        stlp->statement = (yyvsp[0].st); 
        (yyval.st) = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
        (yyval.st)->op = ST_SEQ; 
        (yyval.st)->st_status 
        = ((yyvsp[-1].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
        | FLAG_STATEMENT_COMPOUND; 
        (yyval.st)->u.seq.statement_list = stl;         
	(yyval.st)->u.seq.statement_count = 2; 
      }
/*
    er = $$; 
*/
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparse seq statements %x, status=%x\n", (yyval.st), (yyval.st)->status); 
    print_parse_statement_line((yyval.st)); 
    fprintf(RED_OUT, "\n"); 
    fprintf(RED_OUT, "\n  1st statement %x, status=%x\n  ", (yyvsp[-1].st), (yyvsp[-1].st)->status); 
    print_parse_statement_line((yyvsp[-1].st)); 
    fprintf(RED_OUT, "\n"); 
    fprintf(RED_OUT, "\n  2nd statement %x, status=%x\n  ", (yyvsp[0].st), (yyvsp[0].st)->status); 
    print_parse_statement_line((yyvsp[0].st)); 
    fprintf(RED_OUT, "\n"); 
    
    fflush(RED_OUT); 
    #endif 
  }
#line 14011 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 162:
#line 11310 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.st) = (yyvsp[0].st); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparse action=%x, status=%x\n", (yyval.st), (yyval.st)->status); 
    print_parse_statement_line((yyval.st)); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 
  }
#line 14025 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 163:
#line 11323 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.st) = NULL; 
  }
#line 14033 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 164:
#line 11326 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.st) = (yyvsp[0].st); 
  }
#line 14041 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 165:
#line 11329 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.st) = NULL; 
  }
#line 14049 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 166:
#line 11332 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.st) = (yyvsp[-1].st); 
  }
#line 14057 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 167:
#line 11335 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*st; 
    
    (yyval.st) = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    (yyval.st)->op = ST_IF; 
    (yyval.st)->st_status 
    = ((yyvsp[-2].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
    | ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
    | FLAG_STATEMENT_COMPOUND
    | FLAG_STATEMENT_ELSE; 
    (yyval.st)->u.branch.cond = (yyvsp[-4].sp); 
    (yyval.st)->u.branch.if_statement = (yyvsp[-2].st); 
    (yyval.st)->u.branch.else_statement = (yyvsp[0].st); 
/*
    print_parse_statement_line(st, 1); 
*/
  }
#line 14079 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 168:
#line 11352 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*st; 
    
    (yyval.st) = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    (yyval.st)->op = ST_IF; 
    (yyval.st)->st_status = ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) 
	       | FLAG_STATEMENT_COMPOUND; 
    (yyval.st)->u.branch.cond = (yyvsp[-2].sp); 
    (yyval.st)->u.branch.if_statement = (yyvsp[0].st); 
    (yyval.st)->u.branch.else_statement = NULL; 
/*
    print_parse_statement_line(st, 1); 
*/
  }
#line 14098 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 169:
#line 11366 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*st; 
    
    (yyval.st) = st = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type)); 
    (yyval.st)->op = ST_WHILE; 
    (yyval.st)->st_status 
    = ((yyvsp[0].st)->st_status & ~MASK_STATEMENT_COMPOUND) | FLAG_STATEMENT_COMPOUND; 
    (yyval.st)->u.loop.cond = (yyvsp[-2].sp); 
    (yyval.st)->u.loop.statement = (yyvsp[0].st); 
/*
    print_parse_statement_line(st, 1); 
*/
  }
#line 14116 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 170:
#line 11385 "redgram.y" /* yacc.c:1646  */
    { 
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
    as->u.act.rhs_exp->u.mode_index.mode_name = (yyvsp[-1].string); 
    as->u.act.rhs_exp->u.mode_index.parse_mode = NULL; 
    as->u.act.rhs_exp 
    = as->u.act.offset 
    = ps_exp_share(as->u.act.rhs_exp); 
    
    (yyval.st) = as;
  }
#line 14173 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 171:
#line 11437 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    if (strcmp((yyvsp[-2].string), "to")) { 
      fprintf(RED_OUT, "\nError: 'to' of procedure calls return mode is missing.\n");
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      exit(0); 
    } 
    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CALL; 
    as->lineno = lineno; 
    as->u.call.call_mode_name = (yyvsp[-3].string); 
    as->u.call.call_mode_index = -1; 
    as->u.call.ret_mode_name = (yyvsp[-1].string); 
    as->u.call.ret_mode_index = -1; 
    (yyval.st) = as;
  }
#line 14196 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 172:
#line 11455 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_RETURN; 
    as->lineno = lineno; 
    as->u.call.call_mode_name = (yyvsp[-1].string); 
    as->u.call.call_mode_index = -1; 
    as->u.call.ret_mode_name = CURRENT_MODE->name; 
    as->u.call.ret_mode_index = -1; 
    (yyval.st) = as;
  }
#line 14214 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 173:
#line 11468 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_RETURN; 
    as->lineno = lineno; 
    (yyval.st) = as;
  }
#line 14228 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 174:
#line 11477 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_GUARD; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.guard.cond = (yyvsp[-2].sp); 
    (yyval.st) = as;
  }
#line 14244 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 175:
#line 11488 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_ERASE; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.erase.var = (yyvsp[-1].sp); 
    (yyval.st) = as;
  }
#line 14260 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 176:
#line 11499 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CPLUG; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.cplug.lhs = (yyvsp[-5].sp); 
    as->u.cplug.cmod_index = (yyvsp[-2].number); 
    as->u.cplug.cproc_index = (yyvsp[-1].number); 
    (yyval.st) = as;
  }
#line 14278 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 177:
#line 11512 "redgram.y" /* yacc.c:1646  */
    { 
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));

    as->op = ST_CPLUG; 
    as->st_status = 0; 
    as->lineno = lineno; 
    as->u.cplug.lhs = NULL; 
    as->u.cplug.cmod_index = (yyvsp[-2].number); 
    as->u.cplug.cproc_index = (yyvsp[-1].number); 
    (yyval.st) = as;
  }
#line 14296 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 178:
#line 11525 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_statement_type	*as;

    as = (struct parse_statement_type *) malloc(sizeof(struct parse_statement_type));
    as->st_status = 0; 
    if (   ((yyvsp[-7].sp)->var_status & FLAG_QUANTIFIED_SYNC) 
        || ((yyvsp[-4].sp) && ((yyvsp[-4].sp)->var_status & FLAG_QUANTIFIED_SYNC)) 
        || ((yyvsp[-2].sp) && ((yyvsp[-2].sp)->var_status & FLAG_QUANTIFIED_SYNC)) 
        ) 
      as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
    if (   ((yyvsp[-7].sp)->exp_status & FLAG_INDIRECTION) 
        || ((yyvsp[-4].sp) && ((yyvsp[-4].sp)->exp_status & FLAG_INDIRECTION)) 
        || ((yyvsp[-2].sp) && ((yyvsp[-2].sp)->exp_status & FLAG_INDIRECTION)) 
        ) 
      as->st_status = as->st_status | FLAG_ACTION_INDIRECTION; 

    if (   check_lhs_pco((yyvsp[-7].sp), (yyvsp[-4].sp)) 
        || check_lhs_pco((yyvsp[-7].sp), (yyvsp[-2].sp)) 
        ) {
      as->st_status = as->st_status | FLAG_ACTION_LHS_RECURSION; 
      as->u.act.lhs = ps_exp_copy((yyvsp[-7].sp));
      as->u.act.lhs = ps_exp_share(as->u.act.lhs); 
    }
    else 
      as->u.act.lhs = (yyvsp[-7].sp);
    
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
    = as->u.act.rhs_exp->u.interval.status | (yyvsp[-5].number);
    as->u.act.rhs_exp->u.interval.lbound_exp = (yyvsp[-4].sp);
    if (!(yyvsp[-4].sp)) {
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
    = as->u.act.rhs_exp->u.interval.status | (yyvsp[-1].number);
    as->u.act.rhs_exp->u.interval.rbound_exp = (yyvsp[-2].sp);
    if (!(yyvsp[-2].sp)) {
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
    (yyval.st) = as;
  }
#line 14436 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 179:
#line 11661 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_statement_type *as;
    int				flag_increment_conversion; 

/*
    fprintf(RED_OUT, "\n%1d%:Testing status %1d of RHS of type %1d.\n", count_debug1++, $4->status, $4->type); 
*/
    if ((yyvsp[-1].sp)->exp_status & FLAG_EXP_MODAL_INSIDE) { 
      fprintf(RED_OUT, 
        "Error: modal operators in process assignment RHS type %1d at line %1d.\n", 
	(yyvsp[-1].sp)->type, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if (   (   (yyvsp[-3].sp)->type == TYPE_DISCRETE 
                 || (yyvsp[-3].sp)->type == TYPE_POINTER 
                 || (yyvsp[-3].sp)->type == TYPE_DENSE 
                 || (yyvsp[-3].sp)->type == TYPE_CLOCK
                 )
             && (yyvsp[-3].sp)->u.atom.var == NULL
             ) {
      fprintf(RED_OUT, 
        "\nError: a null variable or a macro constant %s on LHS at line %1d\n",
	(yyvsp[-3].sp)->u.atom.var_name, lineno
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
    switch ((yyvsp[-1].sp)->type) { 
    case ARITH_ADD:  
      if ((yyvsp[-1].sp)->u.arith.lhs_exp == (yyvsp[-3].sp)) { 
        flag_increment_conversion = TYPE_TRUE; 
        (yyval.st) = add_increment(INCREMENT_BY_CONSTANT, 
          (yyvsp[-3].sp), (yyvsp[-1].sp)->u.arith.rhs_exp
        ); 
      } 
      else if ((yyvsp[-1].sp)->u.arith.rhs_exp == (yyvsp[-3].sp)) { 
        flag_increment_conversion = TYPE_TRUE; 
        (yyval.st) = add_increment(INCREMENT_BY_CONSTANT, 
          (yyvsp[-3].sp), (yyvsp[-1].sp)->u.arith.lhs_exp 
        ); 
      } 
      break; 
    case ARITH_MINUS: 
      if ((yyvsp[-1].sp)->u.arith.lhs_exp == (yyvsp[-3].sp)) { 
        flag_increment_conversion = TYPE_TRUE; 
        (yyval.st) = add_increment(DECREMENT_BY_CONSTANT, 
          (yyvsp[-3].sp), (yyvsp[-1].sp)->u.arith.rhs_exp
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
      if (   ((yyvsp[-3].sp)->var_status & FLAG_QUANTIFIED_SYNC) 
          || ((yyvsp[-1].sp)->var_status & FLAG_QUANTIFIED_SYNC) 
          ) 
        as->st_status = as->st_status | FLAG_ACTION_QUANTIFIED_SYNC; 
      if (   ((yyvsp[-3].sp)->exp_status & FLAG_INDIRECTION) 
          || ((yyvsp[-1].sp)->exp_status & FLAG_INDIRECTION) 
          ) 
        as->st_status = as->st_status | FLAG_ACTION_INDIRECTION; 
      if (check_lhs_pco((yyvsp[-3].sp), (yyvsp[-1].sp))) {
        as->st_status = as->st_status | FLAG_ACTION_LHS_RECURSION; 
        as->u.act.lhs = ps_exp_copy((yyvsp[-3].sp));
        as->u.act.lhs = ps_exp_share(as->u.act.lhs); 
      }
      else 
        as->u.act.lhs = (yyvsp[-3].sp);

      as->u.act.rhs_exp = (yyvsp[-1].sp);
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
      (yyval.st) = as;
    }
  }
#line 14544 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 180:
#line 11767 "redgram.y" /* yacc.c:1646  */
    {
    /*
    fprintf(RED_OUT, "\nvc = %x for y:= c\n", vc);
    */
    if ((yyvsp[-3].sp)->u.atom.var->type != TYPE_DISCRETE && (yyvsp[-3].sp)->u.atom.var->type != TYPE_POINTER) {
      fprintf(RED_OUT,
        "\nError: Increment on a non-discrete variable %s at line %1d.\n", 
        (yyvsp[-3].sp)->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(8);
    }
    else if (!((yyvsp[-3].sp)->u.atom.var->status & FLAG_BOUND_DECLARED)) {
      fprintf(RED_OUT, 
        "\nError: Increment on a discrete variable %s without declared bounds at line %1d\n",
	(yyvsp[-3].sp)->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(9);
    }

    (yyval.st) = add_increment(INCREMENT_BY_CONSTANT, 
      (yyvsp[-3].sp), exp_atom(TYPE_CONSTANT, (yyvsp[-1].number), NULL)
    ); 
  }
#line 14574 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 181:
#line 11795 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_statement_type 	*as;

    /*
    fprintf(RED_OUT, "\nvc = %x for y:= c\n", vc);
    */
    if ((yyvsp[-3].sp)->u.atom.var->type != TYPE_DISCRETE && (yyvsp[-3].sp)->u.atom.var->type != TYPE_POINTER) {
      fprintf(RED_OUT, 
        "\nError: Increment on a non-discrete variable %s at line %1d.\n", 
        (yyvsp[-3].sp)->u.atom.var->name, lineno
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(8);
    }
    else if (!((yyvsp[-3].sp)->u.atom.var->status & FLAG_BOUND_DECLARED)) {
      fprintf(RED_OUT, "\nError: Increment on a discrete variable %s without declared bounds at line %1d\n",
	      (yyvsp[-3].sp)->u.atom.var->name, lineno
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(9);
    }

    (yyval.st) = add_increment(DECREMENT_BY_CONSTANT, 
      (yyvsp[-3].sp), exp_atom(TYPE_CONSTANT, (yyvsp[-1].number), NULL)
    ); 
  }
#line 14605 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 182:
#line 11826 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = (yyvsp[0].number); 
  }
#line 14613 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 183:
#line 11829 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*mc; 
    
    mc = (yyvsp[0].sp)->u.inline_declare.declare_exp; 
    fprintf(RED_OUT, "\nmacro constant parsed: "); 
    pcform(mc); 
    (yyval.number) = (yyvsp[0].sp)->u.inline_declare.declare_exp->u.value; 
  }
#line 14626 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 184:
#line 11840 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = INTERVAL_LEFT_CLOSED;
  }
#line 14634 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 185:
#line 11843 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = INTERVAL_LEFT_OPEN;
  }
#line 14642 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 186:
#line 11848 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = INTERVAL_LEFT_CLOSED;
  }
#line 14650 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 187:
#line 11851 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = INTERVAL_RIGHT_OPEN;
  }
#line 14658 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 188:
#line 11856 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = NULL;
  }
#line 14666 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 189:
#line 11859 "redgram.y" /* yacc.c:1646  */
    {
    if ((yyvsp[0].sp)->var_status & (FLAG_DENSE | FLAG_CLOCK)) { 
      fprintf(RED_OUT, "Error: dense left bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if ((yyvsp[0].sp)->var_status & FLAG_SYNCHRONIZER) { 
      fprintf(RED_OUT, "Error: event left bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    (yyval.sp) = (yyvsp[0].sp);
  }
#line 14688 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 190:
#line 11878 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = NULL;
  }
#line 14696 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 191:
#line 11881 "redgram.y" /* yacc.c:1646  */
    {
    if ((yyvsp[0].sp)->var_status & (FLAG_DENSE | FLAG_CLOCK)) { 
      fprintf(RED_OUT, "Error: dense right bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else if ((yyvsp[0].sp)->var_status & FLAG_SYNCHRONIZER) { 
      fprintf(RED_OUT, "Error: event right bound in interval assignments at line %1d.\n", 
	      lineno
	      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    (yyval.sp) = (yyvsp[0].sp);
  }
#line 14718 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 192:
#line 11904 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_REFERENCE); 
    (yyval.sp)->u.exp = ps_exp_alloc(TYPE_CONSTANT); 
    (yyval.sp)->var_status = FLAG_DISCRETE; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    (yyval.sp)->u.exp->u.value = (yyvsp[0].number); 
  }
#line 14730 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 193:
#line 11911 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_REFERENCE); 
    (yyval.sp)->var_status = (yyvsp[-1].sp)->var_status | FLAG_DISCRETE; 
    (yyval.sp)->exp_status = (yyvsp[-1].sp)->exp_status; 
    (yyval.sp)->u.exp = (yyvsp[-1].sp); 
  }
#line 14741 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 194:
#line 11917 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_REFERENCE); 
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status | FLAG_DISCRETE; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status; 
    (yyval.sp)->u.exp = (yyvsp[0].sp); 
  }
#line 14752 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 195:
#line 11923 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[0].sp);
    if(   (yyvsp[0].sp)->type != TYPE_CLOCK 
       && (yyvsp[0].sp)->type != TYPE_POINTER
       && (yyvsp[0].sp)->type != TYPE_DISCRETE
       && (yyvsp[0].sp)->type != TYPE_FLOAT
       && (yyvsp[0].sp)->type != TYPE_DOUBLE
       && (   (yyvsp[0].sp)->type != TYPE_DENSE 
           || ((yyvsp[0].sp)->u.atom.var->status & FLAG_VAR_STATIC)
           ) 
       && (yyvsp[0].sp)->type != TYPE_REFERENCE 
       ) {
      fprintf(RED_OUT, 
        "Syntax error: a non-variable in the left-hand-side at line %1d.\n", 
        lineno
      ); 
      print_parse_subformula((yyvsp[0].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nget a complete operand %x: ", (yyval.sp)->status); 
    pcform((yyval.sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 14784 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 196:
#line 11959 "redgram.y" /* yacc.c:1646  */
    {
    push_scope(SCOPE_LOCAL); 
  }
#line 14792 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 197:
#line 11962 "redgram.y" /* yacc.c:1646  */
    {  
    pop_scope(); 
    (yyval.sp) = (yyvsp[0].sp);
/*
    fprintf(RED_OUT,"===(Local conditions)=========================\n");
    print_parse_subformula_structure($$, 0);
    fprintf(RED_OUT,"\n");
    fflush(RED_OUT);
    print_parse_subformula($$, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n\n\n"); 
    fflush(RED_OUT); 
*/
  }
#line 14810 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 198:
#line 11980 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = ARITH_MULTIPLY;
  }
#line 14818 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 199:
#line 11983 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = ARITH_DIVIDE;
  }
#line 14826 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 200:
#line 11986 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = ARITH_MODULO;
  }
#line 14834 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 201:
#line 12001 "redgram.y" /* yacc.c:1646  */
    { 
/*
    fprintf(RED_OUT, "************ INITIAL ***************************\n"); 
*/
    spec_size = 0; 
    push_scope(SCOPE_GLOBAL); 
  }
#line 14846 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 202:
#line 12008 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[-1].sp);
    pop_scope(); 
  }
#line 14855 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 203:
#line 12016 "redgram.y" /* yacc.c:1646  */
    {
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
#line 14874 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 204:
#line 12030 "redgram.y" /* yacc.c:1646  */
    {
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
#line 14893 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 205:
#line 12045 "redgram.y" /* yacc.c:1646  */
    {
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
#line 14917 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 206:
#line 12064 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 14925 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 207:
#line 12067 "redgram.y" /* yacc.c:1646  */
    {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, (yyvsp[-1].gfair)); 
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
#line 14952 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 208:
#line 12089 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 14960 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 209:
#line 12092 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, (yyvsp[-1].gfair)); 
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
#line 15014 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 210:
#line 12141 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi; 
  
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, (yyvsp[0].gfair)); 
    GAME_ENVR_EXP = exp_static_evaluation(GAME_ENVR_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_ENVR_EXP = rec_ineq_analyze(GAME_ENVR_EXP); 
    GAME_ENVR_EXP = analyze_tctl(GAME_ENVR_EXP, 0, 0);
    TYPE_PARSE_CHOICE = TYPE_PARSE_GAME_ROLES; 
    GAME_FAIRNESS_EXP = merge_fairness_exps(GAME_MODL_EXP, GAME_SPEC_EXP); 
    GAME_FAIRNESS_EXP = ps_exp_share(GAME_FAIRNESS_EXP); 
    (yyval.sp) = NULL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      if (!(PROCESS[pi].status & MASK_GAME_ROLES))
        PROCESS[pi].status = PROCESS[pi].status | FLAG_GAME_ENVR; 
    } 

    fprintf(RED_OUT, "Sorry that equivalence checking has not been implemented so far.\n"); 
    exit(0); 

  }
#line 15042 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 211:
#line 12165 "redgram.y" /* yacc.c:1646  */
    {
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
#line 15066 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 212:
#line 12184 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 15074 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 213:
#line 12187 "redgram.y" /* yacc.c:1646  */
    {
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_MODL_EXP, (yyvsp[-1].gfair)); 
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
#line 15101 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 214:
#line 12209 "redgram.y" /* yacc.c:1646  */
    { 
    change_scope(SCOPE_GLOBAL); 
  }
#line 15109 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 215:
#line 12212 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi, sxi; 

    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_SPEC_EXP, (yyvsp[-1].gfair)); 
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
#line 15163 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 216:
#line 12261 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi; 
  
    pop_scope(); 
    fillin_game_fairness_assumptions(GAME_ENVR_EXP, (yyvsp[0].gfair)); 
    GAME_ENVR_EXP = exp_static_evaluation(GAME_ENVR_EXP, 
      FLAG_NO_PI_STATIC_EVAL, NULL    
    ); 
    GAME_ENVR_EXP = rec_ineq_analyze(GAME_ENVR_EXP); 
    GAME_ENVR_EXP = analyze_tctl(GAME_ENVR_EXP, 0, 0);
    TYPE_PARSE_CHOICE = TYPE_PARSE_GAME_ROLES; 
    GAME_FAIRNESS_EXP = merge_fairness_exps(GAME_MODL_EXP, GAME_SPEC_EXP); 
    GAME_FAIRNESS_EXP = ps_exp_share(GAME_FAIRNESS_EXP); 
    (yyval.sp) = NULL; 
    for (pi = 1; pi <= PROCESS_COUNT; pi++) { 
      if (!(PROCESS[pi].status & MASK_GAME_ROLES))
        PROCESS[pi].status = PROCESS[pi].status | FLAG_GAME_ENVR; 
    } 

    fprintf(RED_OUT, "Sorry that equivalence checking has not been implemented so far.\n"); 
    exit(0); 

  }
#line 15191 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 217:
#line 12284 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 15217 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 218:
#line 12305 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[-1].sp); 
    
    pop_scope(); 
    switch (GSTATUS[INDEX_TASK] & MASK_TASK) {
    case TASK_MODEL_CHECK: 
      CUR_VAR_TYPE = TYPE_DISCRETE; 
      break; 
    }
  }
#line 15232 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 219:
#line 12315 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 15249 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 220:
#line 12327 "redgram.y" /* yacc.c:1646  */
    {
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
  }
#line 15267 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 221:
#line 12343 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 15285 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 222:
#line 12357 "redgram.y" /* yacc.c:1646  */
    { 
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_GOAL;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "goal";
    } 
  }
#line 15300 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 223:
#line 12368 "redgram.y" /* yacc.c:1646  */
    {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SIMULATE;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "monitored";
    }
  }
#line 15314 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 224:
#line 12378 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 15332 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 225:
#line 12392 "redgram.y" /* yacc.c:1646  */
    {
    if (   (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_DEADLOCK
        && (GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_ZENO
        ) {
      if ((GSTATUS[INDEX_TASK] & MASK_TASK) != TASK_SIMULATE)
        GSTATUS[INDEX_TASK] = (GSTATUS[INDEX_TASK] & ~MASK_TASK) | TASK_SAFETY;
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
      TASK_TYPE_NAME = "safety";
    }
  }
#line 15347 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 226:
#line 12403 "redgram.y" /* yacc.c:1646  */
    {
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
#line 15364 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 227:
#line 12416 "redgram.y" /* yacc.c:1646  */
    {
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
#line 15381 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 228:
#line 12429 "redgram.y" /* yacc.c:1646  */
    {
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
#line 15397 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 229:
#line 12444 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_STRONG; 
  }
#line 15405 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 230:
#line 12448 "redgram.y" /* yacc.c:1646  */
    {
    int					i;
    struct ps_fairness_link_type	*psl, *tpsl;

    DEBUG_RED_COUNT = PARSE_GLOBAL_SEQ_COUNT;
    PARSE_DEBUG_EXP = (struct ps_exp_type **) malloc(DEBUG_RED_COUNT * sizeof(struct ps_exp_type *));
    for (i = 0, psl = (yyvsp[0].gseq);
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
    (yyval.gseq) = (yyvsp[0].gseq);
  }
#line 15431 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 231:
#line 12469 "redgram.y" /* yacc.c:1646  */
    { 
/*
    printf("it is an empty debug sequence\n"); 
*/
    (yyval.gseq) = NULL;
/*
    printf("this should be the end of the input string. \n"); 
*/
  }
#line 15445 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 233:
#line 12482 "redgram.y" /* yacc.c:1646  */
    { 
  }
#line 15452 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 234:
#line 12487 "redgram.y" /* yacc.c:1646  */
    {
    int	pi, flag_addr; 
    
    pi = get_value((yyvsp[-2].sp), 0, &flag_addr); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGet a proc spec index %1d from ", pi); 
    print_parse_subformula((yyvsp[-2].sp), 0); 
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
#line 15487 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 235:
#line 12517 "redgram.y" /* yacc.c:1646  */
    { 
    int	pi, flag_addr; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nexp %1d in proc indices:", ++count_pi_arith); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 

    pi = get_value((yyvsp[0].sp), 0, &flag_addr); 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGet a proc spec index %1d from ", pi); 
    print_parse_subformula((yyvsp[0].sp), 0); 
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
  }
#line 15528 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 236:
#line 12554 "redgram.y" /* yacc.c:1646  */
    {
  }
#line 15535 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 237:
#line 12556 "redgram.y" /* yacc.c:1646  */
    { 
    /* fprintf(RED_OUT, "yacc s1 : imply expression\n");
    print_parse_subformula($2, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    (yyval.sp) = (yyvsp[0].sp);
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  }
#line 15550 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 238:
#line 12568 "redgram.y" /* yacc.c:1646  */
    {
    /* fprintf(RED_OUT, "yacc s1 : imply expression\n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    (yyval.sp) = (yyvsp[0].sp);
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  }
#line 15565 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 239:
#line 12579 "redgram.y" /* yacc.c:1646  */
    { 
    /* fprintf(RED_OUT, "yacc s2 : disj list\n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
    (yyval.sp) = (yyvsp[0].sp);
    /*
    fprintf(RED_OUT,"Specific condition:\n");
    print_parse_subformula_structure($$, 0);
    */
  }
#line 15580 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 240:
#line 12594 "redgram.y" /* yacc.c:1646  */
    { /* fprintf(RED_OUT, "yacc implyexp : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER);
    */
  }
#line 15589 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 241:
#line 12600 "redgram.y" /* yacc.c:1646  */
    { struct ps_bunit_type	*bhead, *btail;

  /*    fprintf(RED_OUT, "yacc implyexp : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER);
  */
    (yyval.sp) = ps_exp_alloc(IMPLY);
    (yyval.sp)->var_status = (yyvsp[-3].sp)->var_status | (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[-3].sp)->exp_status | (yyvsp[0].sp)->exp_status | FLAG_NEGATION_INSIDE | FLAG_DISJUNCTION_INSIDE; 
    spec_size++;
    formula_connector_count++; 
    bhead = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*     fprintf(RED_OUT, "\nbhead = %x\n", bhead);
     */
    bhead->subexp = (yyvsp[-3].sp);
    btail = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*     fprintf(RED_OUT, "\nbtail = %x\n", btail); 
     */
    btail->subexp = (yyvsp[0].sp);
    bhead->bnext = btail;
    btail->bnext = NULL;
    (yyval.sp)->u.bexp.blist = bhead;
    (yyval.sp)->u.bexp.len = 2; 
    /* newpstree($$); */
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/*
    fprintf(RED_OUT, "parsing IMPLY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
  }
#line 15627 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 242:
#line 12638 "redgram.y" /* yacc.c:1646  */
    { /* fprintf(RED_OUT, "yacc disjlist : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    */
  }
#line 15636 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 243:
#line 12644 "redgram.y" /* yacc.c:1646  */
    { struct ps_bunit_type *bunitptr, dummy_bu;

  /*    fprintf(RED_OUT, "yacc disjlist : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  */
    if ((yyvsp[0].sp)->type == OR) { 
      (yyval.sp) = ps_exp_copy((yyvsp[0].sp)); 
      (yyval.sp)->var_status = (yyvsp[-3].sp)->var_status | (yyvsp[0].sp)->var_status; 
      (yyval.sp)->exp_status = (yyvsp[-3].sp)->exp_status | (yyvsp[0].sp)->exp_status | FLAG_DISJUNCTION_INSIDE; 
      dummy_bu.bnext = (yyval.sp)->u.bexp.blist; 
      insert_sorted_blist_dummy_head(OR, 
        (yyvsp[-3].sp), &dummy_bu, &((yyval.sp)->u.bexp.len)
      ); 
      (yyval.sp)->u.bexp.blist = dummy_bu.bnext; 
    }
    else { 
      int	bcount; 
      
      bcount = 0; 
      spec_size++;
      formula_connector_count++;
      dummy_bu.bnext = NULL;  
      insert_sorted_blist_dummy_head(OR, (yyvsp[-3].sp), &dummy_bu, &bcount); 
      insert_sorted_blist_dummy_head(OR, (yyvsp[0].sp), &dummy_bu, &bcount); 
      switch (bcount) { 
      case 0: 
        (yyval.sp) = PS_EXP_FALSE; 
        break; 
      case 1: 
        (yyval.sp) = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        break; 
      case 2: 
        (yyval.sp) = ps_exp_alloc(OR);
        (yyval.sp)->var_status = (yyvsp[-3].sp)->var_status | (yyvsp[0].sp)->var_status; 
        (yyval.sp)->exp_status = (yyvsp[-3].sp)->exp_status | (yyvsp[0].sp)->exp_status | FLAG_DISJUNCTION_INSIDE; 
        (yyval.sp)->u.bexp.blist = dummy_bu.bnext; 
        (yyval.sp)->u.bexp.len = 2; 
      }
    }
    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing OR: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15690 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 244:
#line 12694 "redgram.y" /* yacc.c:1646  */
    { (yyval.sp) = (yyvsp[0].sp);
  /*    fprintf(RED_OUT, "yacc disjlist : (3) \n"); 
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    
    fprintf(RED_OUT, "\nParsing a conjunctive formula!\n");
    print_parse_subformula_structure($$, 0); 
  */
  }
#line 15703 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 245:
#line 12707 "redgram.y" /* yacc.c:1646  */
    { /* fprintf(RED_OUT, "yacc conjlsit : (1) \n");
    print_parse_subformula($1, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    */
  }
#line 15712 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 246:
#line 12713 "redgram.y" /* yacc.c:1646  */
    { struct ps_bunit_type *bunitptr, dummy_bu;

  /*    fprintf(RED_OUT, "yacc disjlist : (2) \n"); 
    print_parse_subformula($4, FLAG_GENERAL_PROCESS_IDENTIFIER); 
  */
    if ((yyvsp[0].sp)->type == AND) { 
      (yyval.sp) = ps_exp_copy((yyvsp[0].sp)); 
      (yyval.sp)->var_status = (yyvsp[-3].sp)->var_status | (yyvsp[0].sp)->var_status; 
      (yyval.sp)->exp_status = (yyvsp[-3].sp)->exp_status | (yyvsp[0].sp)->exp_status | FLAG_CONJUNCTION_INSIDE; 
      dummy_bu.bnext = (yyval.sp)->u.bexp.blist; 
      insert_sorted_blist_dummy_head(AND, (yyvsp[-3].sp), &dummy_bu, &((yyval.sp)->u.bexp.len)); 
      (yyval.sp)->u.bexp.blist = dummy_bu.bnext; 
    }
    else { 
      int	bcount; 
      
      bcount = 0; 
      spec_size++;
      formula_connector_count++;
      dummy_bu.bnext = NULL;  
      insert_sorted_blist_dummy_head(AND, (yyvsp[-3].sp), &dummy_bu, &bcount); 
      insert_sorted_blist_dummy_head(AND, (yyvsp[0].sp), &dummy_bu, &bcount); 
      switch (bcount) { 
      case 0: 
        (yyval.sp) = PS_EXP_TRUE; 
        break; 
      case 1: 
        (yyval.sp) = dummy_bu.bnext->subexp; 
        free(dummy_bu.bnext); 
        break; 
      case 2: 
        (yyval.sp) = ps_exp_alloc(AND);
        (yyval.sp)->var_status = (yyvsp[-3].sp)->var_status | (yyvsp[0].sp)->var_status; 
        (yyval.sp)->exp_status = (yyvsp[-3].sp)->exp_status | (yyvsp[0].sp)->exp_status | FLAG_CONJUNCTION_INSIDE; 
        (yyval.sp)->u.bexp.blist = dummy_bu.bnext; 
        (yyval.sp)->u.bexp.len = 2; 
      }
    }
    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing OR: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15764 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 247:
#line 12761 "redgram.y" /* yacc.c:1646  */
    { /* 
    fprintf(RED_OUT, "yacc conjlist : (4) conj\n"); 
    pcform($1); 
    fflush(RED_OUT); 
    */ 
    (yyval.sp) = (yyvsp[0].sp);
  }
#line 15776 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 248:
#line 12773 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[-1].sp);
    /* newpstree($$); */
  }
#line 15785 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 249:
#line 12777 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(NOT);
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status | FLAG_NEGATION_INSIDE; 
    spec_size++;
    formula_connector_count++; 
    (yyval.sp)->u.bexp.blist = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type));

    /*    fprintf(RED_OUT, "\n$$->u.bexp.blist = %x\n",$$->u.bexp.blist); 
     */
    (yyval.sp)->u.bexp.len = 1;
    (yyval.sp)->u.bexp.blist->subexp = (yyvsp[0].sp);
    (yyval.sp)->u.bexp.blist->bnext = NULL;

    /* newpstree($$); */
/*
    fprintf(RED_OUT, "parsing NOT: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15813 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 250:
#line 12800 "redgram.y" /* yacc.c:1646  */
    { 
    check_choice_formula_global();  
    CUR_VAR_TYPE = TYPE_CLOCK; 
    register_variable((yyvsp[0].string));
  }
#line 15823 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 251:
#line 12805 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(RESET); 

    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status | FLAG_EXP_MODAL_INSIDE; 

    (yyval.sp)->u.reset.var = var_search((yyvsp[-2].string)); 
    (yyval.sp)->u.reset.clock_name = (yyvsp[-2].string); 
    (yyval.sp)->u.reset.child = (yyvsp[0].sp); 
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15849 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 252:
#line 12829 "redgram.y" /* yacc.c:1646  */
    { 
    check_choice_formula_global();  
  }
#line 15857 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 253:
#line 12834 "redgram.y" /* yacc.c:1646  */
    {
    int 				fi; 
    struct ps_fairness_link_type	*fl; 
    struct ps_exp_type			*ag; 
    
    ag = (yyval.sp) = ps_exp_alloc((yyvsp[-6].number)+(yyvsp[-4].number));
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_EXP_MODAL_INSIDE; 
    fillin_game_fairness_assumptions((yyval.sp), (yyvsp[-5].gfair)); 
    (yyval.sp)->u.mexp.time_lb = (yyvsp[-2].gint)->lb; 
    (yyval.sp)->u.mexp.time_ub = (yyvsp[-2].gint)->ub; 
    (yyval.sp)->u.mexp.event_restriction = (yyvsp[-1].sp); 
    free((yyvsp[-2].gint)); 
    
    switch ((yyvsp[-4].number)) { 
    case ALWAYS: 
      switch ((yyvsp[-6].number)) { 
      case FORALL: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL; 
        break; 
      case EXISTS: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
        break; 
      }
      (yyval.sp)->u.mexp.path_child = (yyvsp[0].sp); 
      (yyval.sp)->u.mexp.dest_child = PS_EXP_FALSE; 
      break; 
    case EVENTUALLY: 
      switch ((yyvsp[-6].number)) { 
      case FORALL: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
        break; 
      case EXISTS: 
        GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL; 
        break; 
      }
      (yyval.sp)->u.mexp.dest_child = (yyvsp[0].sp); 
      (yyval.sp)->u.mexp.path_child = PS_EXP_TRUE; 
      break; 
    case OFTEN: 
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
      (yyval.sp)->u.mexp.dest_child = (yyvsp[0].sp); 
      (yyval.sp)->u.mexp.path_child = PS_EXP_TRUE; 
      break; 
    case ALMOST:
      GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EALWAYS; 
      (yyval.sp)->u.mexp.path_child = (yyvsp[0].sp); 
      (yyval.sp)->u.mexp.dest_child = PS_EXP_FALSE; 
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
    (yyval.sp)->u.mexp.time_restriction = PS_EXP_TRUE; 
    free((yyvsp[-5].gfair)); 
    
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15951 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 254:
#line 12927 "redgram.y" /* yacc.c:1646  */
    { 
    check_choice_formula_global();  
  }
#line 15959 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 255:
#line 12932 "redgram.y" /* yacc.c:1646  */
    {
    struct ps_fairness_link_type	*fl; 
    struct ps_exp_type			*eu; 
    
    GSTATUS[INDEX_SPEC] = GSTATUS[INDEX_SPEC] | FLAG_SPEC_W_EUNTIL;
    (yyval.sp) = eu = ps_exp_alloc((yyvsp[-7].number)+UNTIL);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_EXP_MODAL_INSIDE; 
    fillin_game_fairness_assumptions((yyval.sp), (yyvsp[-6].gfair)); 
    (yyval.sp)->u.mexp.time_lb = (yyvsp[-2].gint)->lb;
    (yyval.sp)->u.mexp.time_ub = (yyvsp[-2].gint)->ub; 
    free((yyvsp[-2].gint)); // the time restriction is now stored in $$ and the parsed result 
              // can be released. 
    (yyval.sp)->u.mexp.time_restriction = PS_EXP_TRUE; 
    free((yyvsp[-6].gfair)); 
   
    spec_size++;
    formula_connector_count++; 
    /* newpstree($$); */    
   
    (yyval.sp)->u.mexp.path_child = (yyvsp[-5].sp); 
    (yyval.sp)->u.mexp.event_restriction = (yyvsp[-1].sp); 
    (yyval.sp)->u.mexp.dest_child = (yyvsp[0].sp);

/*
    fprintf(RED_OUT, "parsing EUNTIL: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    pcform($$); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 15996 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 256:
#line 12964 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = (yyvsp[-1].string); 
    if (top_scope() < SCOPE_RANGE_DECLARATION) { 
      push_scope(SCOPE_RANGE_DECLARATION); 
    }
  }
#line 16014 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 257:
#line 12977 "redgram.y" /* yacc.c:1646  */
    {
    if (top_scope() == SCOPE_RANGE_DECLARATION) { 
      pop_scope(); 
    }
  }
#line 16024 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 258:
#line 12982 "redgram.y" /* yacc.c:1646  */
    {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc((yyvsp[-9].number));
    switch ((yyvsp[-9].number)) { 
    case FORALL: 
      (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
      (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status | FLAG_PATH_INSIDE | FLAG_CONJUNCTION_INSIDE; 
      break; 
    case EXISTS: 
      (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
      (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status | FLAG_PATH_INSIDE | FLAG_DISJUNCTION_INSIDE; 
      break; 
    } 
      
    (yyval.sp)->u.qexp.quantifier_name = (yyvsp[-8].string);
    (yyval.sp)->u.qexp.value = 0;

    (yyval.sp)->u.qexp.child = (yyvsp[0].sp);
    (yyval.sp)->u.qexp.lb_exp = (yyvsp[-5].sp);
    (yyval.sp)->u.qexp.ub_exp = (yyvsp[-3].sp);

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16069 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 259:
#line 13023 "redgram.y" /* yacc.c:1646  */
    {

    (yyval.sp) = (yyvsp[0].sp);
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "Got one formula literal.\n"); 
    pcform((yyval.sp)); 
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
#line 16090 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 260:
#line 13043 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL_EVENT); 
  }
#line 16098 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 261:
#line 13046 "redgram.y" /* yacc.c:1646  */
    { 
    int 				fi; 
    struct ps_fairness_link_type	*fl; 
    
    pop_scope(); 
    (yyval.sp) = (yyvsp[-1].sp); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16111 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 262:
#line 13054 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = NULL; 
  }
#line 16119 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 263:
#line 13061 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = PS_EXP_TRUE;  
    spec_size++;
  }
#line 16128 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 264:
#line 13065 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = PS_EXP_FALSE; 
    spec_size++; 
    /*    fprintf(RED_OUT, "yacc literal 2 : FALSE\n"); 
     */
  }
#line 16139 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 265:
#line 13071 "redgram.y" /* yacc.c:1646  */
    {
/*
    fprintf(RED_OUT, "\nexp_general, LHS:\n"); 
    pcform($1); 
    fflush(RED_OUT); 
*/
  }
#line 16151 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 266:
#line 13078 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*psub;
/*    
    fprintf(RED_OUT, "\nexp_general, RHS:\n"); 
    pcform($4); 
    fflush(RED_OUT); 
*/
    psub = ps_exp_alloc((yyvsp[-1].number)); 
    
    compose_rel_status(psub, (yyvsp[-3].sp), (yyvsp[0].sp)); 
  
    psub->u.arith.lhs_exp = (yyvsp[-3].sp); 
    psub->u.arith.rhs_exp = (yyvsp[0].sp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"An arith inequality:\n");
    pcform(psub);
    #endif 
    
    (yyval.sp) = ps_exp_share(psub); 
  }
#line 16177 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 267:
#line 13145 "redgram.y" /* yacc.c:1646  */
    { 
    check_choice_formula_global_event(); 
  }
#line 16185 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 268:
#line 13148 "redgram.y" /* yacc.c:1646  */
    {
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 16193 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 269:
#line 13151 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
    (yyval.sp) = ps_exp_alloc(TYPE_SYNCHRONIZER); 
    (yyval.sp)->u.atom.var = (yyvsp[-6].pvar); 
    (yyval.sp)->u.atom.var_name = (yyvsp[-6].pvar)->name; 
    (yyval.sp)->var_status = (yyvsp[-6].pvar)->status | FLAG_SYNCHRONIZER; 
    switch ((yyvsp[-7].number)) { 
    case 0: 
      (yyval.sp)->exp_status = FLAG_EVENT_XMIT | FLAG_EVENT_RECV; 
      break; 
    case 1: 
      (yyval.sp)->exp_status = FLAG_EVENT_RECV; 
      break; 
    case -1: 
      (yyval.sp)->exp_status = FLAG_EVENT_XMIT; 
      break; 
    } 
//    $$->u.atom.indirect_exp = NULL; 
//    $$->u.atom.indirect_count = 0; 
//    $$->u.atom.indirect_vi = NULL; 

    (yyval.sp)->u.atom.exp_base_proc_index = (yyvsp[-1].sp); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/*
    fprintf(RED_OUT, "\nA constrained event "); 
    print_parse_subformula($$, 0); 
    fprintf(RED_OUT, " detected at line %1d\n", lineno); 
    fflush(RED_OUT); 
*/
  }
#line 16228 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 270:
#line 13181 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*psub; 
    
    check_choice_formula_global_event(); 
    psub = (yyval.sp) = ps_exp_alloc(TYPE_SYNCHRONIZER); 
    (yyval.sp)->u.atom.var = (yyvsp[0].pvar); 
    (yyval.sp)->u.atom.var_name = (yyvsp[0].pvar)->name; 
    (yyval.sp)->var_status = (yyvsp[0].pvar)->status | FLAG_SYNCHRONIZER; 
    switch ((yyvsp[-1].number)) { 
    case 0: 
      (yyval.sp)->exp_status = FLAG_EVENT_XMIT | FLAG_EVENT_RECV; 
      break; 
    case 1: 
      (yyval.sp)->exp_status = FLAG_EVENT_RECV; 
      break; 
    case -1: 
      (yyval.sp)->exp_status = FLAG_EVENT_XMIT; 
      break; 
    } 
//    $$->u.atom.indirect_vi = NULL; 
//    $$->u.atom.indirect_exp = NULL; 
//    $$->u.atom.indirect_count = 0; 
    
    (yyval.sp)->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/*
    fprintf(RED_OUT, "\nAn unconstrainted event "); 
    print_parse_subformula($$, 0); 
    fprintf(RED_OUT, " detected at line %1d\n", lineno); 
    fflush(RED_OUT); 
*/
  }
#line 16265 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 271:
#line 13213 "redgram.y" /* yacc.c:1646  */
    {
    struct  parse_variable_type *pv;
    struct parse_mode_type	*pm; 
    int				mi; 
    struct ps_exp_type		*psub; 

    psub = (yyval.sp) = ps_exp_alloc(ARITH_EQ);
    (yyval.sp)->u.arith.lhs_exp = ps_exp_alloc(var_mode->type);
    (yyval.sp)->u.arith.lhs_exp->u.atom.var = var_mode;
    (yyval.sp)->u.arith.lhs_exp->u.atom.var_index = var_mode->index;
    (yyval.sp)->u.arith.lhs_exp->var_status 
    = FLAG_DISCRETE | exp_var_status_parse_variable(var_mode);  
    (yyval.sp)->u.arith.lhs_exp->exp_status 
    = (yyval.sp)->u.arith.lhs_exp->exp_status | FLAG_LOCAL_IDENTIFIER; 
    
    (yyval.sp)->u.arith.lhs_exp->u.atom.var_name = var_mode->name;
    (yyval.sp)->u.arith.lhs_exp->u.atom.exp_base_proc_index = (yyvsp[-1].sp); 
/*
    $$->u.arith.lhs_exp->u.atom.indirect_count = 0;
    $$->u.arith.lhs_exp->u.atom.indirect_exp = NULL;
    $$->u.arith.lhs_exp->u.atom.indirect_vi = NULL;
*/
    (yyval.sp)->u.arith.lhs_exp = ps_exp_share((yyval.sp)->u.arith.lhs_exp); 
//    tpsubve($$->u.arith.lhs_exp); 
    
    (yyval.sp)->u.arith.rhs_exp = ps_exp_alloc(TYPE_MODE_INDEX); 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.value = 0; 
    (yyval.sp)->u.arith.rhs_exp->var_status = 0; 
    (yyval.sp)->u.arith.rhs_exp->exp_status = 0; 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.mode_name = (yyvsp[-4].string); 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.parse_mode = NULL; 
    (yyval.sp)->u.arith.rhs_exp->lineno = lineno; 
    (yyval.sp)->u.arith.rhs_exp = ps_exp_share((yyval.sp)->u.arith.rhs_exp); 
    
    compose_rel_status((yyval.sp), (yyval.sp)->u.arith.lhs_exp, (yyval.sp)->u.arith.rhs_exp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One local mode literal specific condition:\n");
    pcform((yyval.sp));
    #endif  
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16313 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 272:
#line 13256 "redgram.y" /* yacc.c:1646  */
    {
    struct  parse_variable_type *pv;
    struct parse_mode_type	*pm; 
    int				mi; 
    struct ps_exp_type		*psub; 

    psub = (yyval.sp) = ps_exp_alloc(ARITH_EQ);
    (yyval.sp)->u.arith.lhs_exp = ps_exp_alloc(var_mode->type);
    (yyval.sp)->u.arith.lhs_exp->u.atom.var = var_mode;
    (yyval.sp)->u.arith.lhs_exp->u.atom.var_index = var_mode->index;
    (yyval.sp)->u.arith.lhs_exp->var_status 
    = FLAG_DISCRETE | exp_var_status_parse_variable(var_mode);  
    (yyval.sp)->u.arith.lhs_exp->exp_status 
    = (yyval.sp)->u.arith.lhs_exp->exp_status | FLAG_LOCAL_IDENTIFIER; 
    
    (yyval.sp)->u.arith.lhs_exp->u.atom.var_name = var_mode->name;
    (yyval.sp)->u.arith.lhs_exp->u.atom.exp_base_proc_index 
    = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER); 
/*
    $$->u.arith.lhs_exp->u.atom.indirect_count = 0;
    $$->u.arith.lhs_exp->u.atom.indirect_exp = NULL;
    $$->u.arith.lhs_exp->u.atom.indirect_vi = NULL;
*/
    (yyval.sp)->u.arith.lhs_exp = ps_exp_share((yyval.sp)->u.arith.lhs_exp); 
//    tpsubve($$->u.arith.lhs_exp); 
    exp_mode = (yyval.sp)->u.arith.lhs_exp; 

    (yyval.sp)->u.arith.rhs_exp = ps_exp_alloc(TYPE_MODE_INDEX); 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.value = 0; 
    (yyval.sp)->u.arith.rhs_exp->var_status = 0; 
    (yyval.sp)->u.arith.rhs_exp->exp_status = 0; 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.mode_name = (yyvsp[0].string); 
    (yyval.sp)->u.arith.rhs_exp->u.mode_index.parse_mode = NULL; 
    (yyval.sp)->u.arith.rhs_exp->lineno = lineno; 
    (yyval.sp)->u.arith.rhs_exp = ps_exp_share((yyval.sp)->u.arith.rhs_exp); 
    
    compose_rel_status((yyval.sp), (yyval.sp)->u.arith.lhs_exp, (yyval.sp)->u.arith.rhs_exp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"One local mode literal specific condition:\n");
    pcform((yyval.sp));
    #endif  
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16363 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 273:
#line 13301 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a boolean inline call:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 16375 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 274:
#line 13308 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_bunit_type	*pbu; 
    struct ps_exp_type		*ic; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "an actual argument list in inline boolean call.\n"); 
    print_ps_exp_list((yyvsp[0].splist)); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc(TYPE_INLINE_CALL); 
    (yyval.sp)->u.inline_call.inline_declare = (yyvsp[-2].sp); 
    (yyval.sp)->u.inline_call.inline_exp_name = (yyvsp[-2].sp)->u.inline_declare.inline_exp_name; 
    (yyval.sp)->u.inline_call.actual_argument_list = (yyvsp[0].splist); 
    (yyval.sp)->u.inline_call.instantiated_exp = NULL; 
    ic = (yyval.sp); 
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16408 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 275:
#line 13339 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = -1; 
  }
#line 16416 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 276:
#line 13342 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 1; 
  }
#line 16424 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 277:
#line 13345 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 1; 
  }
#line 16432 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 278:
#line 13348 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 0;
  }
#line 16440 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 279:
#line 13356 "redgram.y" /* yacc.c:1646  */
    {
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nentering conditional arithmetic expression:\n"); 
    pcform((yyvsp[-2].sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 16452 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 280:
#line 13363 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*psub;

    psub = ps_exp_alloc(ARITH_CONDITIONAL);

    psub->var_status = (yyvsp[-6].sp)->var_status | (yyvsp[-2].sp)->var_status | (yyvsp[0].sp)->var_status; 
    psub->exp_status = (yyvsp[-6].sp)->exp_status | (yyvsp[-2].sp)->exp_status | (yyvsp[0].sp)->exp_status; 

    psub->u.arith_cond.cond = (yyvsp[-6].sp); 
    psub->u.arith_cond.if_exp = (yyvsp[-2].sp); 
    psub->u.arith_cond.else_exp = (yyvsp[0].sp); 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT,"A conditional arith exp:\n");
    pcform(psub);
    #endif 

    (yyval.sp) = ps_exp_share(psub); 
  }
#line 16476 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 281:
#line 13382 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[0].sp); 
  }
#line 16484 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 282:
#line 13389 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(ARITH_ADD);
    
    compose_additive_status(ARITH_ADD, (yyvsp[-2].sp), (yyvsp[0].sp), 
      &((yyval.sp)->var_status), &((yyval.sp)->exp_status)
    ); 
    
    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16501 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 283:
#line 13401 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(ARITH_MINUS);
    
    compose_additive_status(ARITH_MINUS, (yyvsp[-2].sp), (yyvsp[0].sp), 
      &((yyval.sp)->var_status), &((yyval.sp)->exp_status)
    ); 
    
    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16518 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 284:
#line 13413 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[0].sp);
/*
    fprintf(RED_OUT, "An sexp_multiply at line %1d:\n", lineno); 
    print_parse_subformula_structure($$, 0); 
    fprintf(RED_OUT, "\n"); 
*/
  }
#line 16531 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 285:
#line 13426 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(ARITH_ADD);
    
    compose_additive_status(ARITH_ADD, (yyvsp[-2].sp), (yyvsp[0].sp), 
      &((yyval.sp)->var_status), &((yyval.sp)->exp_status)
    ); 
    
    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/* 
    fprintf(RED_OUT, "\nAn exp_arith at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  }
#line 16553 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 286:
#line 13443 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(ARITH_MINUS);
    
    compose_additive_status(ARITH_MINUS, (yyvsp[-2].sp), (yyvsp[0].sp), 
      &((yyval.sp)->var_status), &((yyval.sp)->exp_status)
    ); 
    
    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/* 
    fprintf(RED_OUT, "\nAn exp_arith at line %1d:\n", lineno); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  }
#line 16575 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 287:
#line 13460 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[0].sp);
/*    
    fprintf(RED_OUT, "An exp_multiply at line %1d:\n", lineno); 
    pcform($$); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
*/
  }
#line 16589 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 288:
#line 13474 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc((yyvsp[-1].number));
    
    compose_mult_status((yyvsp[-1].number), (yyvsp[-2].sp), (yyvsp[0].sp), &((yyval.sp)->var_status), &((yyval.sp)->exp_status)); 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In multiplication\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16609 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 289:
#line 13489 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[0].sp);
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An sexp_term at line %1d:\n", lineno); 
    pcform((yyval.sp)); 
    #endif 
  }
#line 16622 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 290:
#line 13502 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc((yyvsp[-1].number));
    
    compose_mult_status((yyvsp[-1].number), (yyvsp[-2].sp), (yyvsp[0].sp), &((yyval.sp)->var_status), &((yyval.sp)->exp_status)); 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In multiplication\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16642 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 291:
#line 13517 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[0].sp);
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform((yyval.sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 16656 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 292:
#line 13533 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_CONSTANT);
    (yyval.sp)->u.value = -1 * (yyvsp[0].number);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", (yyval.sp)->u.value, lineno);
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16673 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 293:
#line 13545 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_FLOAT_CONSTANT);
    (yyval.sp)->u.float_value = -1 * (yyvsp[0].number);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", (yyval.sp)->u.value, lineno);
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16690 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 294:
#line 13557 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform((yyval.sp)); 
    #endif 
  }
#line 16703 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 295:
#line 13567 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(BIT_OR);
    
    (yyval.sp)->var_status = (yyvsp[-2].sp)->var_status | (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[-2].sp)->exp_status | (yyvsp[0].sp)->exp_status; 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In bitwise or\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16724 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 296:
#line 13583 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(BIT_AND);
    
    (yyval.sp)->var_status = (yyvsp[-2].sp)->var_status | (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[-2].sp)->exp_status | (yyvsp[0].sp)->exp_status; 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In bitwise and\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16745 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 297:
#line 13599 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(BIT_SHIFT_RIGHT);
    
    (yyval.sp)->var_status = (yyvsp[-2].sp)->var_status | (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[-2].sp)->exp_status | (yyvsp[0].sp)->exp_status; 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In shift right\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16766 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 298:
#line 13615 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(BIT_SHIFT_LEFT);
    
    (yyval.sp)->var_status = (yyvsp[-2].sp)->var_status | (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[-2].sp)->exp_status | (yyvsp[0].sp)->exp_status; 

    (yyval.sp)->u.arith.lhs_exp = (yyvsp[-2].sp);
    (yyval.sp)->u.arith.rhs_exp = (yyvsp[0].sp);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In shift left\n"); 
    pcform((yyval.sp)); 
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16787 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 299:
#line 13631 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[0].sp);
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An exp_term at line %1d:\n", lineno); 
    pcform((yyval.sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 16801 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 300:
#line 13643 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[-1].sp);
  }
#line 16809 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 301:
#line 13646 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_REFERENCE); 
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status | FLAG_DISCRETE; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status; 
    (yyval.sp)->u.exp = (yyvsp[0].sp); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16821 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 302:
#line 13653 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(BIT_NOT); 
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status; 
    (yyval.sp)->u.exp = (yyvsp[0].sp); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16833 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 303:
#line 13660 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = (yyvsp[-1].string); 
    if (top_scope() < SCOPE_RANGE_DECLARATION) { 
      push_scope(SCOPE_RANGE_DECLARATION); 
    }
  }
#line 16851 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 304:
#line 13673 "redgram.y" /* yacc.c:1646  */
    {
    if (top_scope() == SCOPE_RANGE_DECLARATION) { 
      pop_scope(); 
    }
  }
#line 16861 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 305:
#line 13678 "redgram.y" /* yacc.c:1646  */
    {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc(ARITH_SUM);
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status | FLAG_PATH_INSIDE | FLAG_CONJUNCTION_INSIDE; 
      
    (yyval.sp)->u.qexp.quantifier_name = (yyvsp[-8].string);
    (yyval.sp)->u.qexp.value = 0;

    (yyval.sp)->u.qexp.child = (yyvsp[0].sp);
    (yyval.sp)->u.qexp.lb_exp = (yyvsp[-5].sp);
    (yyval.sp)->u.qexp.ub_exp = (yyvsp[-3].sp);

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16898 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 306:
#line 13710 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(TYPE_CONSTANT);
    (yyval.sp)->u.value = (yyvsp[0].number);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", (yyval.sp)->u.value, lineno);
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16915 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 307:
#line 13722 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(TYPE_CONSTANT);
    (yyval.sp)->u.value = (yyvsp[0].number);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", (yyval.sp)->u.value, lineno);
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16932 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 308:
#line 13734 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = ps_exp_alloc(TYPE_FLOAT_CONSTANT);
    (yyval.sp)->u.float_value = (yyvsp[0].number);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\na global constant sexp_term: %1d at lineno %1d\n", (yyval.sp)->u.value, lineno);
    #endif 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16949 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 309:
#line 13746 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_NULL);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    (yyval.sp)->u.value = 0; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16962 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 310:
#line 13754 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_MODE_INDEX); 
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    (yyval.sp)->u.mode_index.mode_name = (yyvsp[0].string); 
    (yyval.sp)->u.mode_index.parse_mode = NULL; 
    (yyval.sp)->u.mode_index.value = 0; 
    (yyval.sp)->lineno = lineno; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16978 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 311:
#line 13765 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_PROCESS_COUNT);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    (yyval.sp)->u.value = PROCESS_COUNT; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 16991 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 312:
#line 13773 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_MODE_COUNT);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17003 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 313:
#line 13780 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_XTION_COUNT);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_CONSTANT; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17015 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 314:
#line 13787 "redgram.y" /* yacc.c:1646  */
    {
    if (   top_scope() != SCOPE_LOCAL 
        && top_scope() != SCOPE_LOCAL_XTION
        && top_scope() != SCOPE_ADDRESS_ENFORCER
        ) {
      fprintf(RED_OUT, "\nError: a process identifier symbol 'P' in a non-local term at line %1d.\n", lineno);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(0);
    }
    (yyval.sp) = ps_exp_alloc(TYPE_LOCAL_IDENTIFIER);
    (yyval.sp)->var_status = 0; 
    (yyval.sp)->exp_status = FLAG_LOCAL_IDENTIFIER; 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
/*    
    fprintf(RED_OUT, "\nP detected\n"); 
    pcform($$); 
    fflush(RED_OUT); 
*/
  }
#line 17039 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 315:
#line 13806 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a discrete inline call:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc(TYPE_MACRO_CONSTANT); 
    (yyval.sp)->u.inline_call.inline_declare = (yyvsp[0].sp); 
    (yyval.sp)->u.inline_call.inline_exp_name = (yyvsp[0].sp)->u.inline_declare.inline_exp_name; 
    (yyval.sp)->u.inline_call.actual_argument_list = NULL; 
    (yyval.sp)->u.inline_call.instantiated_exp = NULL; 
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17068 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 316:
#line 13830 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\ngram: got a discrete inline call:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
  }
#line 17080 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 317:
#line 13837 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_bunit_type	*pbu; 

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "an actual argument list in inline boolean call.\n"); 
    print_ps_exp_list((yyvsp[0].splist)); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc(TYPE_INLINE_CALL); 
    (yyval.sp)->u.inline_call.inline_declare = (yyvsp[-2].sp); 
    (yyval.sp)->u.inline_call.inline_exp_name = (yyvsp[-2].sp)->u.inline_declare.inline_exp_name; 
    (yyval.sp)->u.inline_call.actual_argument_list = (yyvsp[0].splist); 
    (yyval.sp)->u.inline_call.instantiated_exp = NULL; 
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17110 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 318:
#line 13862 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = ps_exp_alloc(TYPE_INLINE_ARGUMENT); 
    (yyval.sp)->u.argument = (yyvsp[0].string); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17120 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 319:
#line 13867 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = CURRENT_TOKEN_QFD; 
    (yyval.sp)->var_status = FLAG_QFD; 
    (yyval.sp)->exp_status = 0; 
    
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17132 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 320:
#line 13874 "redgram.y" /* yacc.c:1646  */
    { 
    /* But you first have to check if the identifier is a macro constant. */
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 1: a variable in a NULL scope at line %1d.\n", lineno);
      fprintf(RED_OUT, "\nGot one complete operand!\n"); 
      pcform((yyvsp[-1].number)); 
      bk(0); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);      
    }
    if(   (yyvsp[0].sp)->type != TYPE_CLOCK 
       && (yyvsp[0].sp)->type != TYPE_POINTER
       && (yyvsp[0].sp)->type != TYPE_DISCRETE
       && (yyvsp[0].sp)->type != TYPE_FLOAT
       && (yyvsp[0].sp)->type != TYPE_DOUBLE
       && (yyvsp[0].sp)->type != TYPE_DENSE 
       ) { 
      fprintf(RED_OUT, 
        "Syntax error: a non-variable as a complete operand at line %1d.\n", 
	lineno
      ); 
      print_parse_subformula((yyvsp[0].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGot one complete operand!\n"); 
    pcform((yyvsp[0].sp)); 
    #endif 
    if (   top_scope() == SCOPE_GLOBAL 
	&& ((yyvsp[0].sp)->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
	&& ((yyvsp[0].sp)->u.atom.var->status & FLAG_LOCAL_VARIABLE)
	) {
      fprintf(RED_OUT, 
        "Syntax error: a non-indexed local variable %s used in global condition", 
        (yyvsp[0].sp)->u.atom.var_name
      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(""); 
      exit(0);
    }
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An complete_operand at line %1d:\n", lineno); 
    pcform((yyval.sp)); 
    #endif 

    (yyval.sp) = ps_exp_alloc(TYPE_DEREFERENCE); 
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status; 
    (yyval.sp)->u.exp = (yyvsp[0].sp); 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17191 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 321:
#line 13928 "redgram.y" /* yacc.c:1646  */
    {
    /* But you first have to check if the identifier is a macro constant. */
    if(   (yyvsp[0].sp)->type != TYPE_CLOCK 
       && (yyvsp[0].sp)->type != TYPE_POINTER
       && (yyvsp[0].sp)->type != TYPE_DISCRETE
       && (yyvsp[0].sp)->type != TYPE_FLOAT
       && (yyvsp[0].sp)->type != TYPE_DOUBLE
       && (yyvsp[0].sp)->type != TYPE_DENSE 
       && (yyvsp[0].sp)->type != TYPE_REFERENCE 
       ) {
      fprintf(RED_OUT, 
        "Syntax error: a non-variable from a complete operand at line %1d.\n", 
        lineno
      ); 
      print_parse_subformula((yyvsp[0].sp), FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, "\n"); 
      fflush(RED_OUT); 
      bk(0); 
    }
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 1: a variable in a NULL scope at line %1d.\n", lineno);
      fprintf(RED_OUT, "\nGot one complete operand!\n"); 
      pcform((yyvsp[0].sp)); 
      bk(0); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);      
    }
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nGot one complete operand!\n"); 
    pcform((yyvsp[0].sp)); 
    #endif 
    if (   top_scope() == SCOPE_GLOBAL 
	&& ((yyvsp[0].sp)->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER)
	&& ((yyvsp[0].sp)->u.atom.var->status & FLAG_LOCAL_VARIABLE)
	) {
      fprintf(RED_OUT, "Syntax error: a non-indexed local variable %s used in global condition", (yyvsp[0].sp)->u.atom.var_name);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(""); 
      exit(0);
    }
    (yyval.sp) = (yyvsp[0].sp);
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "An complete_operand at line %1d, s=%x:\n", 
      lineno, (yyval.sp)->status
    ); 
    pcform((yyval.sp)); 
    #endif 
  }
#line 17246 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 322:
#line 13984 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.splist) = (yyvsp[-1].splist); 
  }
#line 17254 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 323:
#line 13987 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.splist) = NULL; 
  }
#line 17262 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 324:
#line 13990 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.splist) = NULL; 
  }
#line 17270 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 325:
#line 13996 "redgram.y" /* yacc.c:1646  */
    {
    struct ps_bunit_type	*bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = (yyvsp[-2].sp); 
    bu->bnext = (yyvsp[0].splist); 
    
    (yyval.splist) = bu; 
  }
#line 17284 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 326:
#line 14005 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_bunit_type	*bu; 
    
    bu = (struct ps_bunit_type *) malloc(sizeof(struct ps_bunit_type)); 
    bu->subexp = (yyvsp[0].sp); 
    bu->bnext = NULL; 
    
    (yyval.splist) = bu; 
  }
#line 17298 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 327:
#line 14018 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = (yyvsp[-1].sp); 
  }
#line 17306 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 328:
#line 14021 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*add_offset, *ind_operand; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "-- indirection parsed: "); 
    pcform((yyvsp[-1].sp)); 
    fflush(RED_OUT); 
    #endif 
    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, "\nError 2: a variable in a NULL scope at line %1d.\n", lineno);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      bk(0);      
    } 
    add_offset = ps_exp_alloc(ARITH_ADD); 
    compose_additive_status(ARITH_ADD, (yyvsp[-3].sp), (yyvsp[-1].sp), 
      &(add_offset->var_status), &(add_offset->exp_status)
    ); 
   
    add_offset->u.arith.lhs_exp = (yyvsp[-3].sp); 
    add_offset->u.arith.rhs_exp = (yyvsp[-1].sp); 
    add_offset = ps_exp_share(add_offset); 
    
    ind_operand = ps_exp_alloc(TYPE_REFERENCE); 
    ind_operand->var_status = add_offset->var_status | FLAG_DISCRETE; 
    ind_operand->exp_status = add_offset->exp_status; 
    ind_operand->u.exp = add_offset; 
    (yyval.sp) = ps_exp_share(ind_operand); 
  }
#line 17339 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 329:
#line 14049 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type *pv;
    struct ps_exp_type		*tt, *t3; 
    struct parse_indirect_type	*pt, *ppt; 

    if ((yyvsp[-1].pvar)->status & FLAG_VAR_STACK) { 
      if (   (yyvsp[0].addr)->exp_address  
          && (yyvsp[0].addr)->flag_address_type != FLAG_ADDRESS_STACK_PLUS
          && (yyvsp[0].addr)->flag_address_type != FLAG_ADDRESS_STACK_MINUS
          ) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal addressing to stack variable %s at line %1d.\n", 
          (yyvsp[-1].pvar)->name, lineno
        ); 
        fflush(RED_OUT); 
        free((yyvsp[0].addr)); 
        exit(0);
    } }  
    else if (   (yyvsp[0].addr)->exp_address  
             && (   (yyvsp[0].addr)->flag_address_type == FLAG_ADDRESS_STACK_PLUS
                 || (yyvsp[0].addr)->flag_address_type == FLAG_ADDRESS_STACK_MINUS
             )   ) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal relative addressing to non-stack variable %s at line %1d.\n", 
        (yyvsp[-1].pvar)->name, lineno
      ); 
      fflush(RED_OUT); 
      free((yyvsp[0].addr)); 
      exit(0);
    }

    #ifdef RED_DEBUG_YACC_MODE 
    fprintf(RED_OUT, "  token operand at line %1d.\n", lineno); 
    print_parse_subformula_structure((yyvsp[0].addr)->exp_address); 
    fprintf(RED_OUT, "\n"); 
    fflush(RED_OUT); 
    #endif 

    if (top_scope() <= SCOPE_RANGE_DECLARATION) { 
      fprintf(RED_OUT, 
        "\nError 2: a variable in a NULL scope at line %1d.\n", lineno
      );
      fprintf(RED_OUT, "%1d:%s", (yyvsp[-1].pvar)->index, (yyvsp[-1].pvar)->name); 
      if ((yyvsp[0].addr)->exp_address) {
        fprintf(RED_OUT, "@("); 
        print_parse_subformula((yyvsp[0].addr)->exp_address, 1); 
        fprintf(RED_OUT, ")"); 
      } 
/*
      if ($4) 
        pcform($4); 
*/        
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      free((yyvsp[0].addr)); 
      bk(0);      
    }
    else if ((yyvsp[-1].pvar) == NULL) { 
      fprintf(RED_OUT, "Syntax error: an undeclared local variable %s in global condition", (yyvsp[-1].pvar)->name);
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      free((yyvsp[0].addr)); 
      exit(0); 
    } 
    else if ((yyvsp[0].addr)->exp_address != NULL && !((yyvsp[-1].pvar)->status & FLAG_LOCAL_VARIABLE)) {
      fprintf(RED_OUT, 
	      "Syntax error: a global variable %s is indexed ", 
	      (yyvsp[-1].pvar)->name
	      );
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      free((yyvsp[0].addr)); 
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
    (yyval.sp) = tt = ps_exp_alloc((yyvsp[-1].pvar)->type); 
    pv = (yyvsp[-1].pvar); 
    (yyval.sp)->var_status = exp_var_status_parse_variable((yyvsp[-1].pvar));      
    (yyval.sp)->exp_status = 0;      
    (yyval.sp)->u.atom.var_index = (yyvsp[-1].pvar)->index; 
    (yyval.sp)->u.atom.var = (yyvsp[-1].pvar); 
    (yyval.sp)->u.atom.var_name = (yyvsp[-1].pvar)->name; 
    if (!((yyvsp[-1].pvar)->status & FLAG_LOCAL_VARIABLE)) { 
      if ((yyvsp[0].addr)->exp_address != NULL) { 
        fprintf(RED_OUT, 
          "ERROR: Illegal address specification for global variable %s at line %1d.\n", 
          (yyvsp[-1].pvar)->name, lineno 
        ); 
        pcform((yyvsp[0].addr)->exp_address); 
        free((yyvsp[0].addr)); 
        exit(0); 
      } 
      (yyval.sp)->u.atom.exp_base_proc_index = PS_EXP_GLOBAL_IDENTIFIER; 
    } 
    else if ((yyvsp[0].addr)->exp_address == NULL) { 
      if ((yyvsp[-1].pvar)->status & FLAG_VAR_STACK) {
        (yyval.sp)->u.atom.exp_base_proc_index = PS_EXP__SP; 
        (yyval.sp)->var_status = (yyval.sp)->var_status | FLAG_LOCAL_VARIABLE; 
      } 
      else {  
        (yyval.sp)->u.atom.exp_base_proc_index = PS_EXP_LOCAL_IDENTIFIER; 
        (yyval.sp)->var_status = (yyval.sp)->var_status | FLAG_LOCAL_VARIABLE; 
      }
    } 
    else { 
      if ((yyvsp[-1].pvar)->status & FLAG_VAR_STACK) {
        switch ((yyvsp[0].addr)->flag_address_type) { 
        case FLAG_ADDRESS_STACK_PLUS: 
          (yyval.sp)->u.atom.exp_base_proc_index = exp_arith(ARITH_ADD, PS_EXP__SP, (yyvsp[0].addr)->exp_address); 
          break; 
        case FLAG_ADDRESS_STACK_MINUS: 
          (yyval.sp)->u.atom.exp_base_proc_index = exp_arith(ARITH_MINUS, PS_EXP__SP, (yyvsp[0].addr)->exp_address); 
          break; 
        default: 
          fprintf(RED_OUT, "\nERROR: Illegal addressing to stack variable %s at line %1d.\n", 
            (yyvsp[-1].pvar)->name, lineno
          ); 
          fflush(RED_OUT); 
          free((yyvsp[0].addr)); 
          exit(0); 
        } 
      } 
      else {
        (yyval.sp)->u.atom.exp_base_proc_index = (yyvsp[0].addr)->exp_address; 
        (yyval.sp)->var_status = (yyval.sp)->var_status | (yyvsp[0].addr)->exp_address->var_status | FLAG_LOCAL_VARIABLE; 
        if (   (yyvsp[0].addr)->exp_address->type != TYPE_LOCAL_IDENTIFIER  
            && top_scope() != SCOPE_GLOBAL_EVENT 
            && top_scope() != SCOPE_GLOBAL
            ) 
          GSTATUS[INDEX_SYNCHRONIZATION] 
          = GSTATUS[INDEX_SYNCHRONIZATION] | FLAG_POINTER_ARITH; 
    } }

    t3 = (yyvsp[0].addr)->exp_address; 

    switch ((yyval.sp)->type) {
    case TYPE_POINTER: 
      if ((yyvsp[0].addr)->exp_address && ((yyvsp[0].addr)->exp_address->var_status & FLAG_QUANTIFIED_SYNC)) 
        (yyval.sp)->var_status = (yyval.sp)->var_status | FLAG_QUANTIFIED_SYNC; 
      break; 
    case TYPE_CLOCK: 
      (yyval.sp)->exp_status = (yyval.sp)->exp_status | FLAG_ONE_POS_CLOCK; 
      break; 
    case TYPE_DENSE:  
      (yyval.sp)->exp_status = (yyval.sp)->exp_status | FLAG_HYBRID; 
      break; 
    } 
    free((yyvsp[0].addr)); 
    
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
    (yyval.sp) = ps_exp_share((yyval.sp)); 
 
    /* 
    fprintf(RED_OUT,"One literal specific condition:\n");
    print_parse_subformula($$, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, "\n");
    */ 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
    
  }
#line 17528 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 330:
#line 14237 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.pvar) = var_mode; 
  }
#line 17536 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 331:
#line 14240 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.pvar) = (yyvsp[0].pnp)->pvar; 
  }
#line 17544 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 332:
#line 14248 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.addr) = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    (yyval.addr)->exp_address = (yyvsp[-1].sp); 
    (yyval.addr)->flag_address_type = FLAG_ADDRESS_STACK_PLUS; 
  }
#line 17555 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 333:
#line 14254 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.addr) = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    (yyval.addr)->exp_address = (yyvsp[-1].sp); 
    (yyval.addr)->flag_address_type = FLAG_ADDRESS_STACK_MINUS; 
  }
#line 17566 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 334:
#line 14260 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.addr) = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    (yyval.addr)->exp_address = (yyvsp[-1].sp); 
    (yyval.addr)->flag_address_type = FLAG_ADDRESS_ENFORCER; 
  }
#line 17577 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 335:
#line 14266 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.addr) = (struct gram_optional_address_type *) 
      malloc(sizeof(struct gram_optional_address_type)); 
    (yyval.addr)->exp_address = NULL; 
    (yyval.addr)->flag_address_type = FLAG_ADDRESS_NULL; 
  }
#line 17588 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 336:
#line 14280 "redgram.y" /* yacc.c:1646  */
    {
    /*    fprintf(RED_OUT, "An operand %d means '=.'\n", $1);
     */
    (yyval.number) = ARITH_EQ;
  }
#line 17598 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 337:
#line 14286 "redgram.y" /* yacc.c:1646  */
    {
  /*    fprintf(RED_OUT, "An operand %d means '!=.'\n", $1);
   */
    (yyval.number) = ARITH_NEQ;
  }
#line 17608 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 338:
#line 14292 "redgram.y" /* yacc.c:1646  */
    {
    /* fprintf(RED_OUT, "An operand %d means '<.'\n", $1);
     */
    (yyval.number) = ARITH_LESS;
  }
#line 17618 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 339:
#line 14298 "redgram.y" /* yacc.c:1646  */
    {
    /*    fprintf(RED_OUT, "An operand %d means '<=.'\n", $1);
     */
    (yyval.number) = ARITH_LEQ;
  }
#line 17628 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 340:
#line 14304 "redgram.y" /* yacc.c:1646  */
    {
    /*    fprintf(RED_OUT, "An operand %d means '>.'\n", $1);
     */
    (yyval.number) = ARITH_GREATER;
  }
#line 17638 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 341:
#line 14310 "redgram.y" /* yacc.c:1646  */
    {
    /*    fprintf(RED_OUT, "An operand %d means '>=.'\n", $1);
     */
    (yyval.number) = ARITH_GEQ;
  }
#line 17648 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 342:
#line 14320 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = ALWAYS;
  }
#line 17656 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 343:
#line 14324 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = EVENTUALLY;
  }
#line 17664 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 344:
#line 14328 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = CHANGE;
  }
#line 17672 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 345:
#line 14332 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = OFTEN;
  }
#line 17680 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 346:
#line 14336 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = ALMOST;
  }
#line 17688 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 347:
#line 14342 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = FORALL;
  }
#line 17696 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 348:
#line 14346 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = EXISTS;
  }
#line 17704 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 349:
#line 14356 "redgram.y" /* yacc.c:1646  */
    { 
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
#line 17723 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 350:
#line 14370 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_GRAM_FAIRNESS->strong_fairness_list 
    = dummy_strong_fl.next_ps_fairness_link; 
    CURRENT_GRAM_FAIRNESS->weak_fairness_list 
    = dummy_weak_fl.next_ps_fairness_link; 
    (yyval.gfair) = CURRENT_GRAM_FAIRNESS; 
  }
#line 17735 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 351:
#line 14378 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.gfair) = (struct gram_fairness_type *) malloc(sizeof(struct gram_fairness_type));
    (yyval.gfair)->strong_fairness_count = 0;
    (yyval.gfair)->strong_fairness_list = NULL;
    (yyval.gfair)->weak_fairness_count = 0;
    (yyval.gfair)->weak_fairness_list = NULL;
  }
#line 17747 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 352:
#line 14389 "redgram.y" /* yacc.c:1646  */
    {
    struct ps_fairness_link_type	*fl; 
    
    fl = (struct ps_fairness_link_type *) 
      malloc(sizeof(struct ps_fairness_link_type)); 
    if (CURRENT_FAIRNESS_STRENGTH == FLAG_FAIRNESS_STRONG) { 
      fl->fairness = (yyvsp[0].sp); 
      strong_fl_tail->next_ps_fairness_link = fl; 
      fl->next_ps_fairness_link = NULL; 
      strong_fl_tail = fl; 
      CURRENT_GRAM_FAIRNESS->strong_fairness_count++; 
    } 
    else { 
      fl->fairness = (yyvsp[0].sp); 
      weak_fl_tail->next_ps_fairness_link = fl; 
      fl->next_ps_fairness_link = NULL; 
      weak_fl_tail = fl; 
      CURRENT_GRAM_FAIRNESS->weak_fairness_count++; 
    } 
  }
#line 17772 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 353:
#line 14409 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.gseq) = NULL; 
  }
#line 17780 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 354:
#line 14412 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.gseq) = NULL; 
  }
#line 17788 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 355:
#line 14418 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv;
    int				lb, ub, flag; 
    struct name_link_type	*qtop; 

    qtop = (struct name_link_type *) malloc(sizeof(struct name_link_type)); 
    qtop->next_name_link = qfd_stack; 
    qfd_stack = qtop; 
    qtop->name = (yyvsp[-1].string); 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 17804 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 356:
#line 14429 "redgram.y" /* yacc.c:1646  */
    {
    pop_scope(); 
  }
#line 17812 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 357:
#line 14432 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS = ps_exp_alloc(LINEAR_EVENT); 
    CURRENT_FAIRNESS->var_status = 0; 
    CURRENT_FAIRNESS->exp_status = FLAG_EXP_MODAL_INSIDE; 
    CURRENT_FAIRNESS->u.eexp.precond_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = NULL; 
  }
#line 17825 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 358:
#line 14440 "redgram.y" /* yacc.c:1646  */
    {
    struct name_link_type	*qtop;

    qtop = qfd_stack;
    qfd_stack = qfd_stack->next_name_link;
    free(qtop);

    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "In quantified expression:\n"); 
    pcform((yyvsp[0].sp)); 
    fflush(RED_OUT); 
    #endif 
    
    (yyval.sp) = ps_exp_alloc(TYPE_MULTIPLE_FAIRNESS);
    (yyval.sp)->var_status = (yyvsp[0].sp)->var_status; 
    (yyval.sp)->exp_status = (yyvsp[0].sp)->exp_status; 
      
    (yyval.sp)->u.qexp.quantifier_name = (yyvsp[-10].string);
    (yyval.sp)->u.qexp.value = 0;

    (yyval.sp)->u.qexp.child = (yyvsp[0].sp);
    (yyval.sp)->u.qexp.lb_exp = (yyvsp[-7].sp);
    (yyval.sp)->u.qexp.ub_exp = (yyvsp[-5].sp);

/*
    fprintf(RED_OUT, "parsing QUANTIFY: EXP_MODAL_INSIDE, %1x\n", 
	    $$->status & FLAG_EXP_MODAL_INSIDE
	    ); 
    print_parse_subformula_structure($$, 0); 
*/
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17862 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 359:
#line 14472 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS = ps_exp_alloc(LINEAR_EVENT); 
    CURRENT_FAIRNESS->exp_status = FLAG_EXP_MODAL_INSIDE; 
    CURRENT_FAIRNESS->u.eexp.precond_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = NULL; 
  }
#line 17874 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 360:
#line 14479 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.sp) = CURRENT_FAIRNESS; 
  }
#line 17882 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 361:
#line 14487 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_FAIRNESS_STRONG;
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_STRONG;  
  }
#line 17891 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 362:
#line 14491 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = FLAG_FAIRNESS_WEAK; 
    CURRENT_FAIRNESS_STRENGTH = FLAG_FAIRNESS_WEAK;  
  }
#line 17900 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 363:
#line 14499 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[-1].sp); 
    (yyval.sp)->u.eexp.precond_exp = PS_EXP_TRUE; 
    (yyval.sp) = ps_exp_share((yyval.sp)); 
  }
#line 17910 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 364:
#line 14504 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS->u.eexp.precond_exp = (yyvsp[0].sp); 
  }
#line 17918 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 365:
#line 14507 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS = ps_exp_share(CURRENT_FAIRNESS); 
    (yyval.sp) = CURRENT_FAIRNESS; 
  }
#line 17927 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 367:
#line 14517 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_FAIRNESS->u.eexp.event_exp = NULL; 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = PS_EXP_TRUE; 
  }
#line 17936 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 368:
#line 14524 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_GLOBAL_EVENT); 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, 
      "\nPS_EVENT detected in global fairness sequence at line %1d.\n", 
      lineno
    );
    fflush(RED_OUT);  
    #endif 
  }
#line 17952 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 369:
#line 14535 "redgram.y" /* yacc.c:1646  */
    { 
    pop_scope(); 
  }
#line 17960 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 370:
#line 14538 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS->u.eexp.event_exp = (yyvsp[-3].sp); 
    (yyval.sp) = CURRENT_FAIRNESS; 
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
  }
#line 17984 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 371:
#line 14559 "redgram.y" /* yacc.c:1646  */
    {
    CURRENT_FAIRNESS->u.eexp.postcond_exp = (yyvsp[0].sp); 
  }
#line 17992 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 372:
#line 14562 "redgram.y" /* yacc.c:1646  */
    { 
    CURRENT_FAIRNESS->u.eexp.postcond_exp = PS_EXP_TRUE; 
  }
#line 18000 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 373:
#line 14570 "redgram.y" /* yacc.c:1646  */
    {
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 18008 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 374:
#line 14573 "redgram.y" /* yacc.c:1646  */
    {
    struct parse_variable_type	*pv;
    int 			lb, ub, flag; 
    float			flb, fub; 

    pop_scope(); 
    if ((yyvsp[-1].sp)->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    flag = get_integer_range((yyvsp[-1].sp), 0, &lb, &ub, &flb, &fub); 
    if (flag != FLAG_SPECIFIC_VALUE) { 
      fprintf(RED_OUT, 
        "\nERROR: Illegal quantification range type in modal time restriction at line %1d.\n", 
        lineno 
      ); 
      pcform((yyvsp[-1].sp)); 
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
    (yyval.gint) = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));
    switch ((yyvsp[-3].number)) {
    case ARITH_EQ:
      (yyval.gint)->lb = (yyval.gint)->ub = 2*ub;
      break;
    case ARITH_NEQ:
      if ((yyvsp[-3].number)) {
        (yyval.gint)->lb = 2*ub + 1;
        (yyval.gint)->ub = 2*ub - 1;
      }
      else {
        (yyval.gint)->lb = 2*ub + 1;
        (yyval.gint)->ub = CLOCK_POS_INFINITY;
      }
      break;
    case ARITH_LEQ:
      (yyval.gint)->lb = 0;
      (yyval.gint)->ub = 2*ub;
      break;
    case ARITH_GEQ:
      (yyval.gint)->lb = 2*ub;
      (yyval.gint)->ub = CLOCK_POS_INFINITY;
      break;
    case ARITH_GREATER:
      (yyval.gint)->lb = 2*ub + 1;
      (yyval.gint)->ub = CLOCK_POS_INFINITY;
      break;
    case ARITH_LESS:
      if (!ub) {
        fprintf(RED_OUT, "\nSyntax error: negative timing distance in modal operator at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
      (yyval.gint)->lb = 0;
      (yyval.gint)->ub = 2*ub - 1;
      break;
    }
  }
#line 18104 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 375:
#line 14665 "redgram.y" /* yacc.c:1646  */
    { 
    push_scope(SCOPE_RANGE_DECLARATION); 
  }
#line 18112 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 376:
#line 14668 "redgram.y" /* yacc.c:1646  */
    {
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
    if ((yyvsp[-4].sp)->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    else { 
      int	flag; 
      float	flb, fub; 
      
      flag = get_integer_range((yyvsp[-4].sp), 0, &lb, &ub, &flb, &fub); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in modal range lb at line %1d.\n", 
          lineno 
        ); 
        pcform((yyvsp[-4].sp)); 
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
    
    if ((yyvsp[-2].sp) == NULL) { 
      modal_ub = -1; 
    }
    else if ((yyvsp[-2].sp)->var_status & (FLAG_EXP_STATE_INSIDE | FLAG_SYNCHRONIZER)) {
      fprintf(RED_OUT, "\nSyntax error: dynamic timing distance in modal operator at line %1d.\n", 
        lineno
      ); 
      exit(0); 
    } 
    else { 
      int	flag; 
      float	flb, fub; 
      
      flag = get_integer_range((yyvsp[-2].sp), 0, &lb, &ub, &flb, &fub); 
      if (flag != FLAG_SPECIFIC_VALUE) { 
        fprintf(RED_OUT, 
          "\nERROR: Illegal quantification range type in modal range ub at line %1d.\n", 
          lineno 
        ); 
        pcform((yyvsp[-4].sp)); 
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

    (yyval.gint) = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));

    if ((yyvsp[-6].number))
      (yyval.gint)->lb = 2*modal_lb;
    else
      (yyval.gint)->lb = 2*modal_lb + 1;

    if (modal_ub == -1) {
      if ((yyvsp[-1].number)) {
        fprintf(RED_OUT, "\nSyntax error: interval infinity bound with closed interval at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
      (yyval.gint)->ub = CLOCK_POS_INFINITY;
    }
    else {
      if ((yyvsp[-1].number))
        (yyval.gint)->ub = 2*modal_ub;
      else
        (yyval.gint)->ub = 2*modal_ub - 1;

      if ((yyval.gint)->lb > (yyval.gint)->ub) {
        fprintf(RED_OUT, "\nSyntax error: time interval bound reversed at line %1d.\n",
        	lineno
        	);
        exit(0);
      }
    }
  }
#line 18267 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 377:
#line 14819 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.gint) = (struct gram_interval_type *) malloc(sizeof(struct gram_interval_type));
    (yyval.gint)->lb = 0;
    (yyval.gint)->ub = CLOCK_POS_INFINITY;
  }
#line 18277 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 378:
#line 14828 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_TRUE;
  }
#line 18285 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 379:
#line 14832 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_FALSE;
  }
#line 18293 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 380:
#line 14839 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_TRUE;
  }
#line 18301 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 381:
#line 14843 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.number) = TYPE_FALSE;
  }
#line 18309 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 382:
#line 14850 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = (yyvsp[0].sp);
  }
#line 18317 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 383:
#line 14854 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.sp) = NULL;
  }
#line 18325 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 384:
#line 14861 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.pnp) = (struct pnp_var_type *) malloc(sizeof(struct pnp_var_type)); 
    (yyval.pnp)->pvar = CURRENT_TOKEN_VAR; 
    (yyval.pnp)->status = 0; 
  }
#line 18335 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 385:
#line 14868 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.pvar) = CURRENT_TOKEN_VAR; 
  }
#line 18343 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 386:
#line 14884 "redgram.y" /* yacc.c:1646  */
    { 
    CUR_SCOPE[++TOP_SCOPE] = SCOPE_SYSTEM_INFO; 
  }
#line 18351 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 387:
#line 14887 "redgram.y" /* yacc.c:1646  */
    {     
    pop_scope(); 
    system_info_process((yyvsp[0].nlist)); 
  }
#line 18360 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 388:
#line 14894 "redgram.y" /* yacc.c:1646  */
    {
    (yyval.nlist) = push_name((yyvsp[-1].string), (yyvsp[0].nlist)); 
  }
#line 18368 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 389:
#line 14897 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.nlist) = NULL; 
  }
#line 18376 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 390:
#line 14915 "redgram.y" /* yacc.c:1646  */
    {
    struct xtion_type			*old_xtion_table; 
    int					old_xtion_count, pi; 
    struct parse_redlib_party_link_type	*p; 
    
    PARSER_INPUT_SYNC_XTION->party_count++; 
    p = (struct parse_redlib_party_link_type *) 
      malloc(sizeof(struct parse_redlib_party_link_type)); 
    p->proc = (yyvsp[-2].number); 

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
#line 18414 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 392:
#line 14949 "redgram.y" /* yacc.c:1646  */
    { 
    /* empty parties. */ 
  }
#line 18422 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 393:
#line 14958 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_quantify_link_type	*q; 
    
    q = (struct ps_quantify_link_type *) 
      malloc(sizeof(struct ps_quantify_link_type));  
    q->next_ps_quantify_link = PARSER_QUANTIFICATION_LIST; 
    PARSER_QUANTIFICATION_LIST = q; 
    q->op = (yyvsp[0].number); 
  }
#line 18436 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 394:
#line 14967 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing one var index %1d:%s.\n", 
      (yyvsp[0].number), VAR[(yyvsp[0].number)].NAME
    ); 
    #endif 
  }
#line 18448 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 395:
#line 14974 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing a comma ',' \n"); 
    #endif 
  }
#line 18458 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 396:
#line 14979 "redgram.y" /* yacc.c:1646  */
    { 
    PARSER_QUANTIFICATION_LIST->var_index = (yyvsp[-4].number); 
  }
#line 18466 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 398:
#line 14983 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = 0; 
  }
#line 18474 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 399:
#line 14989 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = (yyvsp[0].number); 
  }
#line 18482 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 400:
#line 14992 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = -1 * (yyvsp[0].number); 
  }
#line 18490 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 401:
#line 15046 "redgram.y" /* yacc.c:1646  */
    { 
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
      (yyval.number) = variable_index[CURRENT_TOKEN_VAR->type][0][CURRENT_TOKEN_VAR->index]; 
    } 
  }
#line 18513 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 402:
#line 15068 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing '(' for quantify_restriction.\n"); 
    #endif 
  }
#line 18523 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 403:
#line 15073 "redgram.y" /* yacc.c:1646  */
    { 
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing global condition for quantify_restriction.\n"); 
    pcform((yyvsp[0].sp)); 
    #endif 
  }
#line 18534 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 404:
#line 15079 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*e; 
    
    #ifdef RED_DEBUG_YACC_MODE
    fprintf(RED_OUT, "\nparsing ')' for quantify_restriction.\n"); 
    #endif 

    PARSER_QUANTIFICATION_LIST->exp_restriction = (yyvsp[-3].sp); 
    PARSER_QUANTIFICATION_LIST->op_restriction = (yyvsp[0].number); 
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
#line 18614 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 405:
#line 15154 "redgram.y" /* yacc.c:1646  */
    { 
    struct ps_exp_type	*e; 
    
    PARSER_QUANTIFICATION_LIST->exp_restriction = NULL; 
    PARSER_QUANTIFICATION_LIST->op_restriction = NOT; 
    PARSER_QUANTIFICATION_LIST->red_restriction = NULL; 
  }
#line 18626 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 406:
#line 15161 "redgram.y" /* yacc.c:1646  */
    { 
    PARSER_QUANTIFICATION_LIST->exp_restriction = NULL; 
    PARSER_QUANTIFICATION_LIST->op_restriction = -1; 
    PARSER_QUANTIFICATION_LIST->red_restriction = NULL; 
  }
#line 18636 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 407:
#line 15169 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = AND; 
  }
#line 18644 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 408:
#line 15172 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = OR; 
  }
#line 18652 "redgram.tab.c" /* yacc.c:1646  */
    break;

  case 409:
#line 15175 "redgram.y" /* yacc.c:1646  */
    { 
    (yyval.number) = IMPLY; 
  }
#line 18660 "redgram.tab.c" /* yacc.c:1646  */
    break;


#line 18664 "redgram.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 15179 "redgram.y" /* yacc.c:1906  */


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


 






