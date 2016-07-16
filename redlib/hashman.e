extern int			hashkey_shared_hrd_exp(); 
extern struct hrd_exp_type	*hrd_exp_share(); 
extern void 			hrd_exp_delete(); 
extern int			hashkey_diagram(); 
extern struct red_type		*red_share(); 
extern void 			hash_red_delete();

extern struct cache1_hash_type	*HASH_CACHE1; 
extern int	COUNT_HASH_CACHE1; 

extern struct cache2_hash_type	*HASH_CACHE2; 
extern int	COUNT_HASH_CACHE2; 

extern struct cache1_hash_entry_type	
  *cache1_check_result_key(); 

extern struct cache2_hash_entry_type	
  *cache2_check_result_key(
    int, 
    struct red_type *, 
    struct red_type *
  ), 
  *cache2_check_result_key_symmetric(
    int, 
    struct red_type *, 
    struct red_type *
  );
  
extern struct cache4_hash_entry_type	
  *cache4_check_result_key(
    int, 
    struct red_type	*, 
    struct hrd_exp_type	*, 
    int, 
    int
  ),  
  *cache4_check_result_key_symmetric(); 

extern struct cache7_hash_entry_type	
  *cache7_check_result_key(
    int			, // op, 
    struct red_type	*, // *d; 
    struct hrd_exp_type	*, // *hr0, 
    int			, // bn0, 
    int			, // bd0, 
    struct hrd_exp_type	*, // *hr1; 
    int			, // bn1, 
    int			// bd1; 
  ); 

extern struct cache10_hash_entry_type	
  *cache10_check_result_key(); 

extern struct cache13_hash_entry_type	
  *cache13_check_result_key(); 

extern struct token_protection_type
  *TOKEN_PROTECTION_LIST, 
  *USER_TOKEN_PROTECTION_LIST; 


/****************************************
 *  The folloiwng are for token-based garbage collection.  
 */
extern int	get_a_new_gc_token(
  struct token_protection_type	** // **tplist_ptr
); 
extern void	release_gc_token(
  int				, // token, 
  struct token_protection_type	** // **tplist_ptr
); 
extern void	protect_from_gc_with_token(
  struct red_type		*, // *d, 
  int				, // token, 
  struct token_protection_type	* // *tplist
);  

  


extern void	init_hash_management(); 

extern int	report_hash_management(); 



extern void  	red_mark(), red_unmark(), red_unmark_all(); 


extern void	print_cache1(), print_cache2(), 
		print_cache1_all(), print_cache2_all(), 
		test_hashman(); 

// extern	garbage_collect_from_red_alloc(
//   int // flag_stage
// ); 

extern 	garbage_collect(
  int // flag_stage
);
  /* garbage_collect() */ 


extern void	release_all_hash_tables(), 
		reset_hash_diagram_status();


extern void
  ps_exp_mark(struct ps_exp_type *, int), 
  red_mark(struct red_type *, int); 


