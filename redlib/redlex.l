
%{

#define FLAG_MACRO_DEF_FALSE		TYPE_FALSE 
#define	FLAG_MACRO_DEF_LINE_START	1
#define	FLAG_MACRO_DEF_AFTER_KEYWORD	2
#define FLAG_MACRO_DEF_AFTER_NAME	3
#define	FLAG_MACRO_DEF_AFTER_OPT_MINUS	4 	

static int	count_names = 0; 

static char	*lex_test; 

static int	depth_comment = 0; 

static int	src_pos = 0; 
static int	flag_src_line = 0; 

#if RED_DEBUG_LEX_MODE 
int	count_lex = 0; 
#endif 

void	put_src_token() { 
  if (flag_src_line) { 
    strcpy(&(lexbuf[src_pos]), redlibtext); 
    src_pos = src_pos + strlen(redlibtext); 
  } 
}
  /* put_src_token() */ 





%}
nl	\n
%%

"#define" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Commented macro definition.\n"); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start == FLAG_MACRO_DEF_LINE_START) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "Macro definition of constant\n");
    #endif 
    flag_line_start = FLAG_MACRO_DEF_AFTER_KEYWORD; 
  }
  else {
    fprintf(RED_OUT, "Error at line %1d: macro definition not at the beginning of a line.\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  }
}

"/*" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Commented comment starting mark.\n"); 
    fflush(RED_OUT); 
    #endif 
  } 
  else { 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: incrementing comment depth from %1d: %s\n", depth_comment, redlibtext); 
    fflush(RED_OUT); 
    #endif 
    depth_comment=1; 
  }
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
}

"*/" { 
  if (flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Commented comment end mark.\n"); 
    fflush(RED_OUT); 
    #endif 
  } 
  else if (depth_comment > 0) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, 
	    "\nllex: resetting comment depth from %1d: %s\n", 
	    depth_comment, redlibtext
	    ); 
    fflush(RED_OUT); 
    #endif 
    depth_comment = 0; 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    fprintf(RED_OUT, 
	    "\nllex: an unexpected comment end when depth_comment = %1d: %s\n", 
	    depth_comment, redlibtext
	    ); 
    fflush(RED_OUT); 
  }
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
}

"//" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
  } 
  flag_line_start = FLAG_MACRO_DEF_FALSE; 
  flag_comment_to_end_of_line = 1; 
} 


">>RED SRC" { 
  char	*r; 
  
  fprintf(RED_OUT, "\n>>Got src line at line %1d\n", lineno); 
  if (depth_comment || flag_comment_to_end_of_line) {
    if (flag_src_line) { 
      sprintf(&(lexbuf[src_pos]), ">>RED SRC"); 
      src_pos = src_pos + 9; 
    } 
    else { 
      src_pos = 0; 
      flag_src_line = TYPE_TRUE; 
    }
/*
    r = fgets(lexbuf, 999, redlibin); 
    if (strlen(lexbuf) == 999) { 
      fprintf(RED_OUT, 
        "\nERROR: red source comment line in the following is too long at line %1d.\n", 
        lineno
      ); 
      fprintf(RED_OUT, "%s\n", lexbuf); 
      exit(0); 
    } 
     
    lineno++; 
    red_src_lines = insert_name_cycle(red_src_lines, lexbuf, 
      &count_red_src_lines
    ); 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "->->new line %1d in RED SRC\n", lineno); 
    #endif
    flag_line_start = FLAG_MACRO_DEF_LINE_START; 
    flag_comment_to_end_of_line = TYPE_FALSE; 
*/
  } 
  else { 
    fprintf(RED_OUT, "\nError in unexpected red src comment lines %s at line %1d.\n", 
      redlibtext, lineno
    ); 
    fflush(RED_OUT); 
    exit(0); 
  } 
} 

"!" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented exclamation: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Exclamation: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
    return(PS_EXCLAMATION);
  }
}

"?" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented question: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Question: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
    return(PS_QUESTION);
  }
}

";" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented semicolon: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Semicolon: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
    return(PS_SEMICOLON);
  }
}

"->" { 
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented RIGHTARROW: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RIGHTARROW : %s\n", redlibtext); 
    #endif 
    return(PS_RIGHTARROW);
  }
}

"==" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented EQ: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex EQ : %s\n", redlibtext); 
    #endif 
    return(PS_EQ);
  }
}

"!=" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NEQ: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NEQ : %s\n", redlibtext); 
    #endif 
    return(PS_NEQ);
  }
}

"=" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented ASSIGNMENT: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex ASSIGNMENT : %s\n", redlibtext); 
    #endif 
    return(PS_ASSIGNMENT);
  }
} 

"guard" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented GUARD: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex GUARD : %s\n", redlibtext); 
    #endif 
    return(PS_GUARD);
  }
} 

"erase" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented ERASE: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex ERASE : %s\n", redlibtext); 
    #endif 
    return(PS_ERASE);
  }
} 

"globally" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented GLOBALLY: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex GLOBALLY : %s\n", redlibtext); 
    #endif 
    return(PS_GLOBALLY);
  }
} 

":=" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented ASSIGNMENT: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif 
  } 
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    fprintf(RED_OUT, "Message: lex ASSIGNMENT operator ':=' has been changed to '=' at line %1d\n", 
      lineno
    ); 
    fprintf(RED_OUT, "         to comply with C/C++ syntax.\n");                   
    exit(0);
  }
} 

":" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Commented colon: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: Colon: %s\n", redlibtext); 
    #endif 
    return(PS_COLON);
  }
}

"#PS"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented process count: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else if (CUR_SCOPE[TOP_SCOPE] == SCOPE_PROC_DECLARATION) { 
    fprintf(RED_OUT, "Error: cyclic process count reference in process count declaration at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0);                     
  }
  else {
    #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex process count : %s\n", redlibtext); 
    #endif 
    return(PS_PROCESS_COUNT); 
  }
} 

"#ADDRESSES"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented ADDRESSES: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex ADDRESSES : %s\n", redlibtext); 
    #endif 
    return(PS_ADDRESSES); 
  }
} 

"#MS"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented mode count: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex mode count : %s\n", redlibtext); 
    #endif 
    return(PS_MODE_COUNT); 
  }
} 

"#XS"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented xtion count: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex xtion count : %s\n", redlibtext); 
    #endif 
    return(PS_XTION_COUNT); 
  }
} 



"stack" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented stack: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex local : %s\n", redlibtext); 
    #endif 
    return(PS_STACK); 
  }
} 

"local" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented local: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex local : %s\n", redlibtext); 
    #endif 
    return(PS_LOCAL); 
  }
} 

"global" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex: commented global: %s\n", redlibtext); 
      fflush(RED_OUT); 
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: global: %s\n", redlibtext); 
    #endif 
    return(PS_GLOBAL); 
  }
} 

"parameter" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented parameter: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: parameter: %s\n", redlibtext);
    #endif 
    return(PS_PARAMETER);
  }
}

"clock" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented clock: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: clock: %s\n", redlibtext);
    #endif
    return(PS_CLOCK);
  }
}

"dense"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented dense: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: dense: %s\n", redlibtext);
    #endif 
    return(PS_DENSE);
  }
}

"ordered"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented ordered: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: ordered: %s\n", redlibtext);
    #endif 
    return(PS_ORDERED);
  }
}

"unordered"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented unordered: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: unordered: %s\n", redlibtext);
    #endif 
    return(PS_UNORDERED);
  }
}

"stream"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented stream: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: stream: %s\n", redlibtext);
    #endif 
    return(PS_STREAM);
  }
}

"open"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented open: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: open: %s\n", redlibtext);
    #endif 
    return(PS_OPEN);
  }
}

"close"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented close: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: close: %s\n", redlibtext);
    #endif 
    return(PS_CLOSE);
  }
}

"input"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented input: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: input: %s\n", redlibtext);
    #endif 
    return(PS_INPUT);
  }
}

"output"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented output: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: output: %s\n", redlibtext);
    #endif 
    return(PS_OUTPUT);
  }
}

"malloc"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented malloc: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: malloc: %s\n", redlibtext);
    #endif 
    return(PS_MALLOC);
  }
}

"free"  {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented free: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: free: %s\n", redlibtext);
    #endif 
    return(PS_FREE);
  }
}

">>" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented from stream: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex FROM_STREAM: %s\n", redlibtext);  
    #endif
    return(PS_FROM_STREAM);
  }
} 


"<<" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented to stream: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex TO_STREAM: %s\n", redlibtext);  
    #endif
    return(PS_TO_STREAM);
  }
} 


"discrete" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented discrete: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: discrete: %s\n", redlibtext); 
    #endif
    return(PS_DISCRETE); 
  }
} 

"double" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented double: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: double: %s\n", redlibtext); 
    #endif
    return(PS_DOUBLE); 
  }
} 

"float" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented float: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: float: %s\n", redlibtext); 
    #endif
    return(PS_FLOAT); 
  }
} 

"memory"   { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented memory: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: memory: %s\n", redlibtext); 
    #endif
    return(PS_MEMORY); 
  }
} 

"boolean"       { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented boolean: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);  
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: boolean: %s\n", redlibtext); 
    #endif
    return(PS_BOOLEAN); 
  }
} 

"synchronizer"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented pointer: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: pointer: %s\n", redlibtext); 
    #endif
    return(PS_SYNCHRONIZER); 
  }
} 

"xtions"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented xtions: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: xtions: %s\n", redlibtext); 
    #endif
    return(PS_XTIONS); 
  }
} 

"matrix"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented matrix: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: matrix: %s\n", redlibtext); 
    #endif
    return(PS_MATRIX); 
  }
} 

"inline"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented inline: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: inline: %s\n", redlibtext); 
    #endif
    return(PS_INLINE); 
  }
} 


"~" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NOT: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex NOT : %s\n", redlibtext); 
    #endif
    return(PS_BIT_NOT);
  }
}

"urgent" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented mode: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex urgent : %s\n", redlibtext); 
    #endif
    return(PS_URGENT);
  }
}


"check"        { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented check: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex memory : %s\n", redlibtext);
    #endif
    return(PS_CHECK);
  }
}


"mode" 		{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented mode: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex mode : %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif
    return(PS_MODE);
  }
}

"process" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented process: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex process : %s\n", redlibtext); 
    #endif
    return(PS_PROCESS);
  }
}

"role" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented role: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex role : %s\n", redlibtext); 
    #endif
    return(PS_ROLE);
  }
}

"formula" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented formula: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex formula : %s\n", redlibtext); 
    #endif
    return(PS_FORMULA);
  }
}

"quantify" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented quantify: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex quantify : %s\n", redlibtext); 
    #endif
    return(PS_QUANTIFY);
  }
}

"rate" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented rate: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_RATE);
  }
}

"when" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented when: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_WHEN);
  }
}


"while" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented while: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_WHILE);
  }
}

"if" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented if: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_IF);
  }
}

"else" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented else: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_ELSE);
  }
}

"@+" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented bird_plus: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_BIRD_PLUS);
  }
}
"@-" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented bird minus: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_BIRD_MINUS);
  }
}
"@" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented bird: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_BIRD);
  }
}

"may" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented may: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);  
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_MAY);
  }
}

"in" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented in: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_IN);
  }
}
"goto" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented goto: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_GOTO);
  }
}

"oo" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented risk: %s\n", redlibtext);
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_INFINITY);
  }
}

"risk" 		{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented risk: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_RISK);
  }
}

"goal" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented goal: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_GOAL);
  }
}

"safety" 		{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented safety: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_SAFETY);
  }
}


"parametric" {
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented parametric: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: parametric: %s\n", redlibtext);
    #endif
     return(PS_PARAMETRIC);
  }
}

"debug" 	{
  if (depth_comment || flag_comment_to_end_of_line) {
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented debug: %s\n", redlibtext);
    fflush(RED_OUT);
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno);
    fflush(RED_OUT);
    exit(0);
  }
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext);
    #endif
    return(PS_DEBUG);
  }
}
"tctl"	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented specification: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_TCTL);
  }
}
"construct"	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented specification: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_CONSTRUCT);
  }
}
"redlib" 	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented redlib: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_REDLIB);
  }
}
"session" 	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented session: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_SESSION);
  }
}
"branching" 	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented branching: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_BRANCHING);
  }
}
"bisimulation" 	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented bisimulation: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_BISIMULATION);
  }
}
"simulation" 	{
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented simulation: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_SIMULATION);
  }
}
"deadlock" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented specification: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_DEADLOCK);
  }
}
"zeno" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented specification: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_ZENO);
  }
}

"initially" 	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented initial: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_INITIAL);
  }
}

"and" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented and: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex AND : %s\n", redlibtext); 
    #endif
    return(PS_AND);
  }
}
"&&" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented and: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex AND : %s\n", redlibtext); 
    #endif
    return(PS_AND);
  }
}
"&" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented BITWISE and: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex BITWISE AND : %s\n", redlibtext); 
    #endif
    return(PS_BIT_AND);
  }
}
"or" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented or: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex OR : %s\n", redlibtext); 
    #endif
    return(PS_OR);
  }
}
"||" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented or: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex OR : %s\n", redlibtext); 
    #endif
    return(PS_OR);
  }
}
"|" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented BIT or: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex BIT OR : %s\n", redlibtext); 
    #endif
    return(PS_BIT_OR);
  }
}
"until"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented until: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex UNTIL : %s\n", redlibtext); 
    #endif
    return(PS_UNTIL);
  }
}
"always"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented always: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex ALWAYS : %s\n", redlibtext); 
    #endif
    return(PS_ALWAYS);
  }
}
"eventually"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented eventually: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex EVENTUALLY : %s\n", redlibtext); 
    #endif
    return(PS_EVENTUALLY);
  }
}
"event"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented event: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex EVENT : %s\n", redlibtext); 
    #endif
    return(PS_EVENT);
  }
}
		
"events"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented events: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex EVENTS : %s\n", redlibtext); 
    #endif
    return(PS_EVENTS);
  }
}
		
"through"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented through: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex THROUGH : %s\n", redlibtext); 
    #endif
    return(PS_THROUGH);
  }
}
		
"reset"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented eventually: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RESET : %s\n", redlibtext); 
    #endif
    return(PS_RESET);
  }
}
		
"change"  { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented pointer: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    fprintf(RED_OUT, "\nllex: pointer: %s\n", redlibtext); 
    #endif
    return(PS_CHANGE); 
  }
} 

"exists"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented exists: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex EXISTS : %s\n", redlibtext); 
    #endif
    return(PS_EXISTS);
  }
}
"forall"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented forall: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex FORALL : %s\n", redlibtext); 
    #endif
    return(PS_FORALL);
  }
}



"assume"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented assume: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex STRONG : %s\n", redlibtext); 
    #endif
    return(PS_ASSUME);
  }
}


"weak"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented weak: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex WEAK : %s\n", redlibtext); 
    #endif
    return(PS_WEAK);
  }
}


"strong"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented strong: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex STRONG : %s\n", redlibtext); 
    #endif
    return(PS_STRONG);
  }
}


"with"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented forall: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex WITH : %s\n", redlibtext); 
    #endif
    return(PS_WITH);
  }
}


"on"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented forall: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex on : %s\n", redlibtext); 
    #endif
    return(PS_ON);
  }
}


"often"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented forall: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex FORALL : %s\n", redlibtext); 
    #endif
    return(PS_OFTEN);
  }
}


"almost"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented forall: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex FORALL : %s\n", redlibtext); 
    #endif
    return(PS_ALMOST);
  }
}


"true"	{ 
    if (depth_comment || flag_comment_to_end_of_line) { 
      put_src_token();  
      #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nllex: commented true: %s\n", redlibtext); 
      fflush(RED_OUT); 
      #endif
    }
    else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    else {
      #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "lex true : %s\n", redlibtext); 
      fflush(RED_OUT); 
      #endif
      return(PS_TRUE);
    }
  }
"false" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented false: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex false : %s\n", redlibtext); 
    #endif
    return(PS_FALSE);
  }
}
"SYSTEM" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented SYSTEM: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex SYSTEM: %s\n", redlibtext); 
    #endif
    return(PS_SYSTEM);
  }
} 

"INFO" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented INFO: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex INFO: %s\n", redlibtext); 
    #endif
    return(PS_INFO);
  }
} 



"NULL" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NULL: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex null: %s\n", redlibtext); 
    #endif
    return(PS_NULL);
  }
}
"P" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented P: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex P: %s\n", redlibtext); 
    #endif
    return(PS_P);
  }
}
"implies" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented IMPLY: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex IMPLY : %s\n", redlibtext); 
    #endif
    return(PS_IMPLY);
  }
}
"=>" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented IMPLY: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex IMPLY : %s\n", redlibtext); 
    #endif
    return(PS_IMPLY);
  }
}
"(" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented LEFT(: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex LEFT( : %s\n", redlibtext); 
    #endif
    return(PS_LPAR);
  }
}

")" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented RIGHT): %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RIGHT) : %s\n", redlibtext); 
    #endif
    return(PS_RPAR);
  }
}
"[" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented LEFT[: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex : %s\n", redlibtext); 
    #endif
    return(PS_LBRAC);
  }
}
"]" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented RIGHT]: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex right]: %s\n", redlibtext); 
    #endif
    return(PS_RBRAC);
  }
}
"{" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented LEFT{: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex LEFT{: %s\n", redlibtext);  
    #endif
    return(PS_LCURLY);
  }
}
"}" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented RIGHT}: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RIGHT}: %s\n", redlibtext);  
    #endif
    return(PS_RCURLY);
  }
}
".." { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented COMMA: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex DDOTS: %s\n", redlibtext); 
    #endif
    return(PS_DDOTS);
  }
} 

"," { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented COMMA: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex COMMA: %s\n", redlibtext); 
    #endif
    return(PS_COMMA);
  }
} 

"cplug" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented cplug: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex CPLUG: %s\n", redlibtext); 
    #endif
    return(PS_CPLUG);
  }
} 



"call" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented call: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex CALL: %s\n", redlibtext); 
    #endif
    return(PS_CALL);
  }
} 



"return" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented return: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RETURN: %s\n", redlibtext); 
    #endif
    return(PS_RETURN);
  }
} 

"++" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented increment: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex INCREMENT: %s\n", redlibtext); 
    #endif
    return(PS_INC);
  }
} 

"--" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented decrement: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex DECREMENT: %s\n", redlibtext); 
    #endif
    return(PS_DEC);
  }

}

"clear" {
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented clear: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex clear: %s\n", redlibtext); 
    #endif
    return(PS_CLEAR);
  }

}

"+" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented PLUS: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex PLUS: %s\n", redlibtext); 
    #endif
    return(PS_PLUS);
  }
}
"-" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented MINUS: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) { 
    if (flag_line_start == FLAG_MACRO_DEF_AFTER_NAME) { 
      flag_line_start = FLAG_MACRO_DEF_AFTER_OPT_MINUS; 
    } 
    else { 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex MINUS: %s\n", redlibtext); 
    #endif
    return(PS_MINUS);
  }
}
"*" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented MULTIPLY: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex MULTIPLY: %s\n", redlibtext); 
    #endif
    return(PS_MULTIPLY);
  }
}
"/" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented DIVIDE: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex DIVIDE: %s\n", redlibtext); 
    #endif
    return(PS_DIVIDE);
  }
}
"SUM" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented DIVIDE: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex SUM: %s\n", redlibtext); 
    #endif
    return(PS_SUM);
  }
}
"%" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented MODULO: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex MODULO: %s\n", redlibtext); 
    #endif
    return(PS_MODULO);
  }
}
"<" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented LESS: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex LESS : %s\n", redlibtext);  
    #endif
    return(PS_LESS);
  }
}
"<=" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented LEQ: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT);  
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex <=: %s\n", redlibtext);  
    #endif
    return(PS_LEQ);
  }
} 


"=<" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented old LEQ: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    fprintf(RED_OUT, "\nError: an outdated LESS-THAN:''%s'' at line %1d\n", redlibtext, lineno); 
    fprintf(RED_OUT, "Sorry that we've changed the notation to ''<=''\n"); 
    fprintf(RED_OUT, "Please make appropriate changes in your input file.\n"); 
    fflush(RED_OUT); 
    exit(23); 
  }
}

">" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented GREATER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0);
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex GREATER: %s\n", redlibtext);  
    #endif
    return(PS_GREATER);
  }
} 


">=" {  
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented GEQ: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex GEQ : %s\n", redlibtext);  
    #endif
    return(PS_GEQ);
  }
}

"index"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented index: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex INDEX : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_INDEX);
  }
}


"'"	{ 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented primed `'': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex PRIMED : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_PRIMED);
  }
}


"window" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `window': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex WINDOW : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_WINDOW);
  }
}



"position" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `position': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex POSITION : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_POSITION);
  }
}



"shape" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `shape': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex SHAPE : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_SHAPE);
  }
}




"rightward" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `RIGHTWARD': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex RIGHTWARD : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_RIGHTWARD);
  }
}



"leftward" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `LEFTWARD': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex LEFTWARD : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_LEFTWARD);
  }
}



"upward" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `UPWARD': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex UPWARD : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_UPWARD);
  }
}



"downward" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `DOWNWARD': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex DOWNWARD : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_DOWNWARD);
  }
}


"color" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `color': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex COLOR : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_COLOR);
  }
}





"point" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented `point': %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  else {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex point : %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    return(PS_POINT);
  }
}




"0x"[A-Fa-f0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_CONSTANT); 
        gme->u.value = atoi(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_DISCRETE, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    char	*c; 
    int		len, i, v; 
    
    c = &(redlibtext[2]); 
    len = strlen(c); 
    if (len <= 0 || len > 8) { 
      fprintf(RED_OUT, 
        "Error in hexadecimal number length %1d of %s at line %1d\n", 
        len, redlibtext, lineno
      ); 
      fflush(RED_OUT); 
      exit(0); 
    } 
    for (i = 0, v = 0; i < len; i++) { 
      if (c[i] >= '0' && c[i] <= '9') { 
        v = ((v << 4) & (0xFFFFFFF0)) | (((int) (c[i] - '0')) & (0xF)); 
      } 
      else if (c[i] >= 'a' && c[i] <= 'f') { 
        v = ((v << 4) & (0xFFFFFFF0)) | (((int) (c[i] - 'a')) & (0xF)); 
      } 
      else if (c[i] >= 'A' && c[i] <= 'F') { 
        v = ((v << 4) & (0xFFFFFFF0)) | (((int) (c[i] - 'A')) & (0xF)); 
      } 
      else { 
        fprintf(RED_OUT, 
          "Error in hexadecimal number representation %s at line %1d\n", 
          redlibtext, lineno
        ); 
        fflush(RED_OUT); 
        exit(0); 
      } 
    } 
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.number = v;
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex HEX NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_HEX_NUMBER);
  }
}




[0-9]*"."[0-9]+"f" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}





[0-9]*"."[0-9]+"F" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}





[0-9]+"f" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}





[0-9]+"F" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}






[0-9]*"."[0-9]+"E"[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}






[0-9]*"."[0-9]+"e"[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}






'.'[0-9]+'E'[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}






'.'[0-9]+'e'[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}





[0-9]+"E"[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}






[0-9]+"e"[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_FLOAT_NUMBER);
  }
}

[0-9]*"\."[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.float_value = atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_FLOAT_CONSTANT); 
        gme->u.value = -1 * atof(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.float_number = atof(redlibtext);
//    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s, %.4f, %.4E\n", 
      redlibtext, redliblval.float_number, redliblval.float_number
    ); 
//    #endif
    return(PS_FLOAT_NUMBER);
  }
}




[0-9]+ { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "\nllex: commented NUMBER: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    struct ps_exp_type	*gme; 
    
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_NAME:  
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_CONSTANT); 
        gme->u.value = atoi(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
      if (GSTATUS[INDEX_REDLIB_CONTROL] & FLAG_REDLIB_DECLARE_FULL_MODEL) {
        gme = ps_exp_alloc(TYPE_CONSTANT); 
        gme->u.value = -1 * atoi(redlibtext); 
        gme = ps_exp_share(gme); 
        macro_register(FLAG_INLINE_CONSTANT, gram_macro_name, 0, NULL, gme); 
      }
      flag_line_start = FLAG_MACRO_DEF_FALSE; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else {
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    redliblval.number = atoi(redlibtext);
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex NUMBER : %s\n", redlibtext); 
    #endif
    return(PS_NUMBER);
  }
}




[A-Za-z][A-Za-z0-9_\.]* {
  char				*mname; 
  struct ps_exp_type		*gm; 
  struct parse_mode_type	*pm; 

  #if RED_DEBUG_LEX_MODE
  ++count_lex; 
    fprintf(RED_OUT, 
      "\ncount lex = %1d, in redlex identifier, got a string '%s' at line %1d.\n", 
      count_lex, redlibtext, lineno
    ); 
    fflush(RED_OUT); 
  #endif
  
/*
  fprintf(RED_OUT, "\nname (%1d) identified: %s\n", 
    ++count_names, redlibtext 
  );  
*/
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "case identifier 0\n"); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "\nllex: commented identifier: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "case identifier 1 in macro definition \n"); 
    fflush(RED_OUT); 
    #endif
    switch (flag_line_start) {
    case FLAG_MACRO_DEF_AFTER_KEYWORD:  
      mname = (char *) malloc(strlen(redlibtext)+1); 
      sprintf(mname, "%s", redlibtext); 
      gram_macro_name = mname; 
      flag_line_start = FLAG_MACRO_DEF_AFTER_NAME; 
      break; 
    default: 
      fprintf(RED_OUT, "Error in macro syntax at line %1d\n", lineno); 
      fflush(RED_OUT); 
      exit(0); 
    }
  } 
  else if (CUR_SCOPE[TOP_SCOPE] == SCOPE_SYSTEM_INFO) {  
    #if RED_DEBUG_LEX_MODE
    printf("lex case identifier 3: %s\n", redlibtext); 
    fprintf(RED_OUT, "case identifier 5\n"); 
    fflush(RED_OUT); 
    #endif
    redliblval.string = (char *) malloc((unsigned) strlen(redlibtext)+1);
    strcpy(redliblval.string, redlibtext); 
    return(PS_IDENTIFIER); 
  }
  else if (!qfd_var_undefined(redlibtext)) { 
    #if RED_DEBUG_LEX_MODE
    printf("lex case identifier 2, qfd\n"); 
    fprintf(RED_OUT, "case identifier 2, qfd: %s\n", redlibtext); 
    fflush(RED_OUT); 
    #endif
    CURRENT_TOKEN_QFD 
    = (struct ps_exp_type *) malloc(sizeof(struct ps_exp_type)); 
    CURRENT_TOKEN_QFD->type = TYPE_QFD; 
    CURRENT_TOKEN_QFD->u.atom.var = NULL; 
    CURRENT_TOKEN_QFD->u.atom.var_name = (char *) malloc(strlen(redlibtext)+1); 
    CURRENT_TOKEN_QFD->u.atom.exp_base_proc_index = NULL;  
//    CURRENT_TOKEN_QFD->u.atom.indirect_count = 0; 
//    CURRENT_TOKEN_QFD->u.atom.indirect_exp = NULL; 
    strcpy(CURRENT_TOKEN_QFD->u.atom.var_name, redlibtext); 
    redliblval.sp = CURRENT_TOKEN_QFD; 
    return(PS_QFD); 
  } 
  else if (inline_formal_argument_search(redlibtext)) { 
    #if RED_DEBUG_LEX_MODE
    printf("lex case inline formal argument: %s\n", redlibtext); 
    fprintf(RED_OUT, "case inline formal argument\n"); 
    fflush(RED_OUT); 
    #endif
    redliblval.string = (char *) malloc((unsigned) strlen(redlibtext)+1);
    strcpy(redliblval.string, redlibtext); 
    return(PS_INLINE_ARGUMENT); 
  } 
  else if (   (GSTATUS[INDEX_PARSE] & MASK_GRAM_PHASE) != GRAM_PHASE_VAR_DECL
           && (CURRENT_TOKEN_VAR = redliblval.pvar = var_search(redlibtext))
           ) {
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "case identifier 3\n"); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "red lext var %s:len=%1d and pvar name:%s ", 
    	    redlibtext, strlen(redlibtext), redliblval.pvar->name
    	    ); 
    #endif 
    switch (redliblval.pvar->type) {
    case TYPE_SYNCHRONIZER: 
      #if RED_DEBUG_LEX_MODE
      printf("lex case sync: %s\n", redlibtext); 
      fprintf(RED_OUT, "sync\n"); 
      #endif
      return(PS_SYNC); 
    case TYPE_BDD: 
      #if RED_DEBUG_LEX_MODE
      printf("lex case bdd: %s\n", redlibtext); 
      fprintf(RED_OUT, "bdd\n"); 
      #endif     
      return(PS_BDD); 
    default: 
      #if RED_DEBUG_LEX_MODE
      printf("lex case variable: %s\n", redlibtext); 
      fprintf(RED_OUT, "others\n"); 
      #endif     
      return(PS_VARIABLE); 
    }
  }
  else if (gm = macro_search(redlibtext)) { 
    #if RED_DEBUG_LEX_MODE
    fprintf(RED_OUT, "lex case macro constant 4: %s with value:\n", redlibtext); 
    pcform(gm->u.inline_declare.declare_exp); 
    fprintf(RED_OUT, "case identifier 4 as a macro constant.\n"); 
    fflush(RED_OUT); 
    #endif 
    redliblval.sp = gm;
    switch (gm->u.inline_declare.status & MASK_INLINE_TYPE) { 
    case FLAG_INLINE_CONSTANT: 
//      #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nlex: got a discrete %x inline constant %s:\n", 
        gm->u.inline_declare.status, 
        gm->u.inline_declare.inline_exp_name 
      ); 
      pcform(gm); 
      fflush(RED_OUT); 
//      #endif 
      
      return (PS_MACRO_CONSTANT); 

    case FLAG_INLINE_DISCRETE: 
      #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nlex: got a discrete %x inline call %s:\n", 
        gm->u.inline_declare.status, 
        gm->u.inline_declare.inline_exp_name
      ); 
      pcform(gm); 
      fflush(RED_OUT); 
      #endif 
      
      return (PS_DISCRETE_INLINE_CALL); 
    case FLAG_INLINE_BOOLEAN: 
      #if RED_DEBUG_LEX_MODE
      fprintf(RED_OUT, "\nlex: got a boolean %x inline call %s:\n", 
        gm->u.inline_declare.status, 
        gm->u.inline_declare.inline_exp_name
      ); 
      pcform(gm); 
      fflush(RED_OUT); 
      #endif 
      
      return (PS_BOOLEAN_INLINE_CALL); 
    }
  } 
  else {
    #if RED_DEBUG_LEX_MODE 
    printf("lex case identifier 5: %s\n", redlibtext); 
    fprintf(RED_OUT, "case identifier 5\n"); 
    fflush(RED_OUT); 
    #endif 
    redliblval.string = (char *) malloc((unsigned) strlen(redlibtext)+1); 
    strcpy(redliblval.string, redlibtext); 
    return(PS_IDENTIFIER); 
  }
}

" " { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
  }
  switch (flag_line_start) { 
  case FLAG_MACRO_DEF_LINE_START: 
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    break; 
  case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
    fprintf(RED_OUT, "Error: floating space in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}

"\t" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    put_src_token();  
  }
  switch (flag_line_start) { 
  case FLAG_MACRO_DEF_LINE_START: 
    flag_line_start = FLAG_MACRO_DEF_FALSE; 
    break; 
  case FLAG_MACRO_DEF_AFTER_OPT_MINUS: 
    fprintf(RED_OUT, "Error: floating tab in macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
}

"\n" { 
  if (depth_comment || flag_comment_to_end_of_line) { 
    if (flag_src_line) { 
      sprintf(&(lexbuf[src_pos]), "\n\0"); 
      src_pos = 0; 
      flag_src_line = TYPE_FALSE; 
      red_src_lines = insert_name_cycle(red_src_lines, lexbuf, 
        &count_red_src_lines
      ); 
    } 
  }
  else if (flag_line_start > FLAG_MACRO_DEF_LINE_START) { 
    fprintf(RED_OUT, "Error: incomplete macro syntax at line %1d\n", lineno); 
    fflush(RED_OUT); 
    exit(0); 
  } 
  lineno++; 
  #if RED_DEBUG_LEX_MODE
  fprintf(RED_OUT, "->->new line %1d\n", lineno); 
  #endif
  flag_line_start = FLAG_MACRO_DEF_LINE_START; 
  flag_comment_to_end_of_line = TYPE_FALSE; 
}



%%





