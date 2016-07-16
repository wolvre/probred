
extern int	SOFTWARE_PROCESS_COUNT, 
		SOFTWARE_START_PI, SOFTWARE_STOP_PI, 
		MEMORY_COUNT, 
		OFFSET_MEM_STATUS; 	

extern struct indexed_structure_link_type	*declared_memory_list; 

extern void	initialize_memory(), init_dmem_management(); 

extern int	memory_leaks(), 
		dirty_pointer_in_trigger_exp(), 
		dirty_pointer_in_action(), 
		dirty_pointer_in_post_invariances(); 

extern struct memory_type	*MEMORY; 

