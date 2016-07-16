
%{

// The following is to be marked off when the program is used as 
// an independent program. 
 
#define	FLAG_AS_A_LIBRARY	1

#ifndef FLAG_AS_A_LIBRARY 

#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <float.h>

#include <limits.h> 

#endif 

#define TYPE_FALSE		0
#define TYPE_TRUE		1

#define FLAG_MACRO_DEF_FALSE		TYPE_FALSE 
#define	FLAG_MACRO_DEF_LINE_START	1
#define	FLAG_MACRO_DEF_AFTER_KEYWORD	2
#define FLAG_MACRO_DEF_AFTER_NAME	3
#define	FLAG_MACRO_DEF_AFTER_OPT_MINUS	4 	

FILE	*redmacin, *REDMACOUT; 

static int	count_names = 0; 

#define	MAC_LIMIT	1000 
static char	*lex_test, mac_line[MAC_LIMIT]; 

static int	depth_comment = 0; 
static int	lineno = 1, 
		flag_line_start = 1, 
		flag_comment_to_end_of_line = 0; 


// #if RED_DEBUG_LEX_MODE 
int	count_lex = 0; 
// #endif 

struct gm_type	{ 
  char			*mac, *text; 
  struct gm_type	*next_gm; 
}; 

struct gm_type	*gm_stack_top = NULL; 
int		gm_count = 0; 


%}
nl	\n
%%

"#define" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: Commented macro definition.\n"); 
    fflush(REDMACOUT); 
    #endif 
  }
  else if (flag_line_start == FLAG_MACRO_DEF_LINE_START) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "Macro definition of constant\n");
    #endif 
    flag_line_start = FLAG_MACRO_DEF_AFTER_KEYWORD; 
  }
  else {
    fprintf(REDMACOUT, "Error at line %1d: macro definition not at the beginning of a line.\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  }
}

"/*" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: Commented comment starting mark.\n"); 
    fflush(REDMACOUT); 
    #endif 
  } 
  else { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: incrementing comment depth from %1d: %s\n", depth_comment, redmactext); 
    fflush(REDMACOUT); 
    #endif 
    depth_comment=1; 
  }
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
}

"*/" { 
  if (flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: Commented comment end mark.\n"); 
    fflush(REDMACOUT); 
    #endif 
  } 
  else if (depth_comment > 0) {
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, 
	    "\nllex: resetting comment depth from %1d: %s\n", 
	    depth_comment, redmactext
	    ); 
    fflush(REDMACOUT); 
    #endif 
    depth_comment = 0; 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(REDMACOUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  } 
  else {
    fprintf(REDMACOUT, 
	    "\nllex: an unexpected comment end when depth_comment = %1d: %s\n", 
	    depth_comment, redmactext
	    ); 
    fflush(REDMACOUT); 
  }
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
}

"//" { 
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
  flag_comment_to_end_of_line = 1; 
} 








[A-Za-z][A-Za-z0-9_\.]* {
  struct gm_type	*gm; 
  int			i, len=MAC_LIMIT; 

  #if RED_DEBUG_LEX_MODE
  ++count_lex; 
    printf("\ncount lex = %1d, in redmaclex identifier, got a string '%s' at line %1d.\n", 
      count_lex, redmactext, lineno
    ); 
    fflush(REDMACOUT); 
  #endif
  
/*
  fprintf(REDMACOUT, "\nname (%1d) identified: %s\n", 
    ++count_names, redmactext 
  );  
*/
  if (depth_comment || flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "case identifier 0\n"); 
    fflush(REDMACOUT); 
    fprintf(REDMACOUT, "\nllex: commented identifier: %s\n", redmactext); 
    fflush(REDMACOUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "case identifier 1 in macro definition \n"); 
    fflush(REDMACOUT); 
    #endif
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_KEYWORD:  
      gm = (struct gm_type *) malloc(sizeof(struct gm_type)); 
      gm->next_gm = gm_stack_top; 
      gm_stack_top = gm; 
      gm_count++; 
      
      gm->mac = malloc(strlen(redmactext)+1); 
      gm->text = malloc(MAC_LIMIT+1);
       
      sprintf(gm->mac, "%s", redmactext); 

      for (mac_line[0] = input(); 
           mac_line[0] == ' ' || mac_line[0] == '\t'; 
           mac_line[0] = input() 
           ) ;        
      for (unput(mac_line[0]), i = 0; i < MAC_LIMIT; i++) { 
        mac_line[i] = input(); 
        if (mac_line[i] == '\n' || mac_line[i] == EOF) 
          break; 
      } 
      if (mac_line[i] == '\n') {
        lineno++; 
        fprintf(REDMACOUT, "\n"); 
      }
      if (i < MAC_LIMIT) { 
        for (i--; 
             i>=0 && (mac_line[i] == ' ' || mac_line[i] == '\t');  
             i--
             ); 
        mac_line[i+1] = '\0'; 
        gm->text = malloc(i+4); 
        sprintf(gm->text, "%s\0", mac_line); 
      } 
      else { 
        fprintf(REDMACOUT, "\nERROR: macro text too long!\n"); 
        fflush(REDMACOUT); 
        exit(0); 
      } 
//      printf("\nmac %s:[%s]\n", gm->mac, gm->text); 

      flag_line_start = FLAG_MACRO_DEF_LINE_START; 
      flag_comment_to_end_of_line = TYPE_FALSE; 
      break; 
    default: 
      fprintf(REDMACOUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(REDMACOUT); 
      fclose(REDMACOUT); 
      exit(0); 
    }
  } 
  else if (check_macro(redmactext)) { 
    fprintf(REDMACOUT, "%s", redmactext); 
  }
}

[0-9!\?;:,\-=\>\<#@&\|\(\)\[\]\{\}\+\*\/\\\%'~\"] {

// Please be careful about the following special characters. 
// " \ [ ] ^ - ? . * + | ( ) $ / { } % < >

//  printf("redmactext(%1d): %s\n", lineno, redmactext); 
  if (depth_comment || flag_comment_to_end_of_line) {
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: commented exclamation: %s\n", redmactext); 
    fflush(REDMACOUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(REDMACOUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  } 
  else {
    fprintf(REDMACOUT, "%s", redmactext); 
  }
}




" " { 
  fprintf(REDMACOUT, " "); 
  switch (flag_line_start) { 
  case FLAG_MACRO_DEF_LINE_START: 
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    break; 
  case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
    fprintf(REDMACOUT, "Error: floating space in macro syntax at line %1d\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  } 
}

"\.\." { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(REDMACOUT, "\nllex: commented COMMA: %s\n", redmactext); 
    fflush(REDMACOUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(REDMACOUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  } 
  else {
    fprintf(REDMACOUT, "%s", redmactext); 
  }
} 


"\t" { 
  fprintf(REDMACOUT, "\t"); 
  switch (flag_line_start) { 
  case FLAG_MACRO_DEF_LINE_START: 
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    break; 
  case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
    fprintf(REDMACOUT, "Error: floating tab in macro syntax at line %1d\n", lineno); 
    fflush(REDMACOUT); 
    exit(0); 
  } 
}

"\n" { 
  fprintf(REDMACOUT, "\n"); 
  lineno++; 
  #if RED_DEBUG_LEX_MODE
  fprintf(REDMACOUT, "->->new line %1d\n", lineno); 
  #endif
  flag_line_start = FLAG_MACRO_DEF_LINE_START; 
  flag_comment_to_end_of_line = TYPE_FALSE; 
}



%%

int	check_macro(char *text) { 
  struct gm_type	*gm; 
  int 			i; 
  
  for (gm = gm_stack_top; gm; gm = gm->next_gm) { 
    if (!strcmp(text, gm->mac)) { 
//      printf("unput macro %s to %s\n", gm->mac, gm->text); 
      for (i = strlen(gm->text) -1; i >= 0; i--) 
        unput(gm->text[i]); 
      return (0); 
    } 
  } 
//  printf("%s", text);
  return(1);  
} 
  /* check_macro() */ 


redmacwrap() { 

} 
  /* redmacwrap() */ 




#ifdef FLAG_AS_A_LIBRARY 

char	*macro_eliminate(char *f) { 
  char	*outfname; 
  
  redmacin = fopen(f, "r"); 
  if (redmacin == NULL) 
    return(NULL); 
    
  outfname = malloc(strlen(f) + 5); 
  sprintf(outfname, "%s.me\0", f); 
  REDMACOUT = fopen(outfname, "w"); 
  if (REDMACOUT == NULL) 
    return(NULL); 

  redmaclex(); 
  fclose(REDMACOUT); 

  return(outfname); 
} 
  /* macro_eliminate() */ 


#else  

main (int argc, char **argv) { 
  char	*outfname; 
  
  if (argc < 2) { 
    printf("\nToo few arguments!\n"); 
    exit(0); 
  } 
  redmacin = fopen(argv[1], "r"); 
  if (redmacin == NULL) 
    exit(0); 

  outfname = malloc(strlen(argv[1]) + 5); 
  sprintf(outfname, "%s.me\0", argv[1]); 
  REDMACOUT = fopen(outfname, "w"); 
  
  redmaclex(); 
  fclose(REDMACOUT); 
}
  /* main() */ 


#endif 







