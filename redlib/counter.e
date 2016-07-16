extern struct red_type	**COUNTER_PATH; 
extern int		COUNTER_PATH_TOP, COUNTER_PATH_LIMIT; 

extern void	init_counter_example_management(), 
		conditional_init_counter_example_management(), 
		free_counter_example_record(), 
		add_counter_path(
		  struct red_type	*, // *d, 
		  int			// it
		), 
		print_counter_example();  
		
extern struct counter_example_node_type	
		*generate_counter_example_fwd(), 
		*generate_counter_example_bck(); 

extern struct red_type	
  *locate_one_instance(
    struct red_type		*, // *d, 
    struct path_xtion_type	*, // *counter, 
    int				// current_stage
  ); 
