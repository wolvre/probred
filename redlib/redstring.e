#if RED_DEBUG_REDSTRING_MODE
extern int	flag_debug_string_diagram; 
#endif 

extern char	sbuf[2000]; 
extern int	size_sbuf, PI_STRING, PI_LENGTH; 

extern char	*file_to_string(); 
extern int	rec_string_diagram(); 
extern char	*string_diagram(); 
extern int 
  rec_string_parse_subformula(
    struct ps_exp_type	*, // *psub 
    int			, // pos
    struct ps_exp_type	* // *parent 
  ); 

#define	FLAG_NO_SUBFORMULA_DEPTH	-1
extern int	SUB_DEPTH; 
extern char	*string_parse_subformula(); 
extern int 	string_parse_action(), 
		rec_string_parse_statement(); 
extern char	*string_parse_statement_instantiate(), 
		*string_mode_name();  
extern int 	string_linear_action(), 
		string_action(), 
		rec_string_statement(); 
extern char	*string_statement_instantiate(), 
		*string_xtion(int, int), 
		*string_sync_xtion_actions(), 
		*string_sync_xtion();  
extern char	*string_sync_list();  




