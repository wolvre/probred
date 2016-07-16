

extern void	check_tctctl_before_shorthand_analysis(
  struct ps_exp_type	*
); 




#define FLAG_SPEC_TCTL		1
#define	FLAG_SPEC_NO_TCTL	0

extern struct ps_exp_type	*shorthand_analysis(
  struct ps_exp_type	* 	// psub 
);

#define	FLAG_ANALYZE_INITIAL	1 

extern void	var_index_fillin(
  struct ps_exp_type	* 
); 

extern struct ps_exp_type	*analyze_tctl(
  struct ps_exp_type	*, 
  int 			, 
  int 
);  

extern void 	print_tctctl_flag(
  struct ps_exp_type	*
); 


