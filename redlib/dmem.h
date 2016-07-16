
#define	MEM_STATUS_ALLOCATED	1
#define MEM_STATUS_FREED	0

#define POINTER_DIRTY_REFERENCE	-1
#define FLAG_POINTER_DIRTY	-1

#define	POINTER_NULL_REFERENCE	-2


struct memory_type { 
  int			size, start_pi, stop_pi, module_index, 
			xi_alloc, xi_free, offset_status, mode_init; 
  char			*name; 
}; 


