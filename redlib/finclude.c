#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include "redbasics.h" 
#include "redbasics.e" 

#include "redbop.h" 

#include "hashman.h" 

/* add for recursive inclusing */
#define	STRING_INCLUDE		"#include"
#define LEN_STRING_INCLUDE	8

FILE	*TARGET_INCLUDE_FILE; 

struct name_link_type	*FILE_NAME_STACK; 
int			include_pos; 

#define	INCLUDE_POS_NONE	0
#define	INCLUDE_POS_POUND	1
#define	INCLUDE_POS_I		2
#define	INCLUDE_POS_N		3
#define	INCLUDE_POS_C		4
#define	INCLUDE_POS_L		5
#define	INCLUDE_POS_U		6
#define	INCLUDE_POS_D		7
#define	INCLUDE_POS_E		8
#define	INCLUDE_POS_END		9

#define INCLUDE_COMMENT_START	11

void	premature_exit_at_EOF(
  char	*cur_file_name 
) { 
  fprintf(RED_OUT, 
    "\nERROR: Premature file end in file inclusion for %s\n", 
    cur_file_name 
  ); 
  fflush(RED_OUT); 
  exit(0); 	
} 
  /*  */ 


void	skip_slash_star_comment(
  FILE	*cur_file, 
  char	*cur_file_name
) { 
  char	c; 
  
  for (c = fgetc(cur_file); TYPE_TRUE; ) { 
    if (c == EOF) { 
      premature_exit_at_EOF(cur_file_name); 
    } 
    fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    if (c == '*') { 
      c = fgetc(cur_file); 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
      if (c == '/') { 
        return; 
      } 
      else if (c != '*') {
      	c = fgetc(cur_file); 
      }	
    }
    else 
      c = fgetc(cur_file); 
  } 
}
  /* skip_slash_star_comment() */ 


void	skip_slash_slash_comment(
  FILE	*cur_file, 
  char	*cur_file_name
) { 
  char	c; 
  
  for (c = fgetc(cur_file); TYPE_TRUE; c = fgetc(cur_file)) { 
    if (c == EOF) { 
      premature_exit_at_EOF(cur_file_name); 
    } 
    fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    if (c == '\n') { 
      return; 
    } 
  } 
}
  /* skip_slash_slash_comment() */ 


#define FLAG_BUFFER_NOT_USED	-1 

int	fgetc_buffer = FLAG_BUFFER_NOT_USED; 


int	fgetc_skipping_comments_between_tokens(
  FILE	*cur_file, 
  char	*cur_file_name 
) { 
  int	c; 
  
  if (fgetc_buffer != FLAG_BUFFER_NOT_USED) {
    c = fgetc_buffer; 
    fgetc_buffer = FLAG_BUFFER_NOT_USED; 
    return(c); 
  }
  for (c = fgetc(cur_file); TYPE_TRUE; c = fgetc(cur_file)) { 
    switch (c) {
    case EOF: 
      premature_exit_at_EOF(cur_file_name); 
      break; 
    case '/': 
      fgetc_buffer = fgetc(cur_file); 
      switch (fgetc_buffer) { 
      case EOF: 
        premature_exit_at_EOF(cur_file_name); 
        break; 
      case '*':      	
        fprintf(TARGET_INCLUDE_FILE, "/*"); 
        skip_slash_star_comment(cur_file, cur_file_name); 
        fgetc_buffer = FLAG_BUFFER_NOT_USED; 
        break; 
      case '/': 
        fprintf(TARGET_INCLUDE_FILE, "//"); 
      	skip_slash_slash_comment(cur_file, cur_file_name); 
      	fgetc_buffer = FLAG_BUFFER_NOT_USED; 
      	break; 
      default: 
        return('/'); 
        break; 
      }	
    default: 
      return(c); 
    }	
  } 
}
  /* fgetc_skipping_comments_between_tokens() */ 



int	try_to_include( 
  FILE	*cur_file, 
  char	*cur_file_name 
) { 
  char	c; 
  char	*file_name; 
  int	len_file_name, fpos; 

  fprintf(TARGET_INCLUDE_FILE, 
    "\n//  Files to be included from the following command.\n"
  ); 
  fprintf(TARGET_INCLUDE_FILE, "//  #include"); 
  for (c = fgetc_skipping_comments_between_tokens(cur_file, cur_file_name); 
       c == ' ' || c == '\t'; 
       c = fgetc_skipping_comments_between_tokens(cur_file, cur_file_name)
       ) {
    fprintf(TARGET_INCLUDE_FILE, "%c", c);
  } 
  if (c != '"') { 
    fprintf(RED_OUT, 
      "\nERROR: Illegal file name specification in included file %s.\n", 
      cur_file_name 
    ); 
    fflush(RED_OUT); 
    fclose(TARGET_INCLUDE_FILE); 
    exit(0); 
  } 
  fprintf(TARGET_INCLUDE_FILE, "%c", c);
  file_name = malloc(32); 
  len_file_name = 31; 
  for (fpos = 0, c = fgetc(cur_file); 
       c != '"' && c != EOF; 
       c = fgetc(cur_file) 
       ) { 
    fprintf(TARGET_INCLUDE_FILE, "%c", c);
    if (len_file_name <= fpos) {
      char	*new_file_name; 
      	  
      new_file_name = malloc(2*(len_file_name+1)); 
      memcpy(new_file_name, file_name, len_file_name-1);  
      free(file_name); 
      file_name = new_file_name; 
      len_file_name = 2*len_file_name+1; 
    } 
    file_name[fpos++] = c; 
  } 
  if (c == EOF) { 
    fprintf(RED_OUT, "\nERROR: premature file inclusion command.\n"); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  file_name[fpos] = '\0'; 
  fprintf(TARGET_INCLUDE_FILE, 
    "\"\n//  To include file \"%s\"\n", 
    file_name
  ); 
  rec_include(file_name); 
  fprintf(TARGET_INCLUDE_FILE, "\n//\n"); 
  fprintf(TARGET_INCLUDE_FILE, "//  File %s inclusion completed.\n\n", file_name); 
  free(file_name); 
}
  /* try_to_include() */ 



int	update_include_status(
  char	c, 
  FILE	*cur_file, 
  char	*cur_file_name   
) { 
  switch (include_pos) { 
  case INCLUDE_POS_NONE: 
    if (c == '#') 
      include_pos = INCLUDE_POS_POUND; 
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    break; 
  case INCLUDE_POS_POUND: 
    if (c == 'i') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_I: 
    if (c == 'n') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#i"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#i%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_N: 
    if (c == 'c') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#in"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#in%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_C: 
    if (c == 'l') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#inc"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#inc%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_L: 
    if (c == 'u') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#incl"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#incl%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_U: 
    if (c == 'd') 
      include_pos++; 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#inclu"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#inclu%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_POS_D: 
    if (c == 'e') { 
      try_to_include(cur_file, cur_file_name); 
      include_pos = INCLUDE_POS_NONE; 
    } 
    else if (c == '#') {
      fprintf(TARGET_INCLUDE_FILE, "#includ"); 
      include_pos = INCLUDE_POS_POUND; 
    }
    else if (c == '/') {
      include_pos = INCLUDE_COMMENT_START; 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
    }
    else {
      fprintf(TARGET_INCLUDE_FILE, "#includ%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  case INCLUDE_COMMENT_START: 
    switch (c) { 
    case '*': 
      fprintf(TARGET_INCLUDE_FILE, "*"); 
      skip_slash_star_comment(cur_file, cur_file_name);
      include_pos = INCLUDE_POS_NONE; 
      break; 
    case '/': 
      fprintf(TARGET_INCLUDE_FILE, "/"); 
      skip_slash_slash_comment(cur_file, cur_file_name); 
      include_pos = INCLUDE_POS_NONE; 
      break; 
    case '#': 
      include_pos = INCLUDE_POS_POUND; 
      break; 
    default: 
      fprintf(TARGET_INCLUDE_FILE, "%c", c); 
      include_pos = INCLUDE_POS_NONE; 
    }
    break; 
  default: 
    fprintf(RED_OUT, "\nSomething must be wrong.\n"); 
    fflush(RED_OUT); 
    exit(0); 
    break; 
  } 
}
  /* update_include_status() */ 




/*  Procedure for recursive file inclusion 
 *  with gcc compile-time command 
 *  #include "xxx"
 */
int     rec_include(
 char  *cur_file_name
) {
  FILE*	cur_file; 
  int 	c;
  int 	repeatFlag  = 0;

  if (check_name_list(cur_file_name, FILE_NAME_STACK)) { 
    fprintf(TARGET_INCLUDE_FILE, 
      "\n//  >> FILE %s ALREADY INCLUDED! <<\n", 
      cur_file_name
    );
    fprintf(RED_OUT, "\n//  File %s already included.\n", 
      cur_file_name
    ); 
    fflush(RED_OUT); 
    include_pos = INCLUDE_POS_NONE; 
    return; 
  } 
  cur_file = fopen(cur_file_name, "r");
  if (cur_file == NULL) { 
    fprintf(RED_OUT, 
      "\nERROR: could not find file %s for inclusion.\n", 
      cur_file_name
    ); 
    fflush(RED_OUT); 
//    bk(0); 
    exit(0); 
  } 
  FILE_NAME_STACK = push_name_stack(cur_file_name, FILE_NAME_STACK); 
  include_pos = INCLUDE_POS_NONE; 
  for (c = fgetc(cur_file); c != EOF; c = fgetc(cur_file)) { 
    update_include_status(c, cur_file, cur_file_name); 
  } 
  include_pos = INCLUDE_POS_NONE; 
  FILE_NAME_STACK = pop_name_stack(FILE_NAME_STACK); 
  fclose(cur_file);
  return (TYPE_TRUE);
}
  /* rec_include() */ 





char	*file_include(
  char	*input_file_name
) { 
  char	*output_file_name; 
  
  output_file_name = malloc(strlen(input_file_name) + 4); 
  sprintf(output_file_name, "%s.ir", input_file_name); 
/*
  fprintf(RED_OUT, "intermediate representation %s.ir should be generated.\n", 
    input_file_name
  ); 
*/
  TARGET_INCLUDE_FILE = fopen(output_file_name, "w+"); 
  if (TARGET_INCLUDE_FILE) { 
    FILE_NAME_STACK = NULL; 
    rec_include(input_file_name); 
    fclose(TARGET_INCLUDE_FILE);
    return(output_file_name); 
  }
  else { 
    free(output_file_name); 
    fprintf(RED_OUT, 
      "\nERROR: failed writing for inductive file inclusion.\n"
    ); 
    fflush(RED_OUT); 
    return(NULL); 
  }
}
  /* file_include() */ 



