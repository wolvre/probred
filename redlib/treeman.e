/*===================================================================
*
*       con23tree.e
*
*/


extern int				init_23tree_management();
extern int				report_23tree_management(); 
extern int				init_23tree();
extern struct a23key_type		*search_23tree();
extern int				*membership_23tree();
extern char				*add_23tree();
extern int				rem_23tree();
extern struct a23tree_type		*copy_23tree();
extern int				print_23tree();
extern int				print_beautiful_23tree();


/* old append */
extern int			base_stable_property_count;
 
extern struct a23tree_type	*a23tree_pool;
extern int			a23tree_count, free_a23tree_count;

extern struct a23tree_type	*alloc_23tree();
extern int 			free_23tree();
extern int 			rec_free_entire_23tree();
extern int			free_entire_23tree();
extern int 			rec_free_entire_23tree_without_key();
extern int 			free_entire_23tree_without_key();
extern struct a23key_type	a23_key;
extern struct a23key_type	*search_23tree();
extern int 			add_rebalance_23tree();
extern int 			add_rebalance_23tree_without_parent();
extern char			*itr_add_23tree();
extern int 			add_23tree_without_parent();
extern int			rem_23tree();
extern int 			compare_23tree();
extern struct a23tree_type 	*garbage_collect_23tree();
extern int 			process_23tree();

extern int 
  rec_count, rec3_count, rec5_count, 
  qrec_count, 
  drec_count; 
  
extern struct rec_type	*rec_new(), *check_record();
void			save_record(); 

extern struct rec3_type	*rec3_new(); 
extern struct rec5_type	*rec5_new();  

extern int		rec_free(), rec_print(), rec_comp(), rec_single_comp(), 
			rec_parent_set(), rec_count_inc, rec_nop(), 
			rec3_free(), rec3_print(), rec3_comp(),  
			rec3_parent_set(), rec3_count_inc, rec3_nop(), 
			rec5_free(), rec5_print(), rec5_comp(),  
			rec5_parent_set(), rec5_count_inc, rec5_nop();

extern struct double_rec_type	*drec_new();
extern int		drec_free(), drec_print(), drec_comp(), drec_parent_set(), drec_count_inc, drec_nop();

extern struct qrec_type	*qrec_new();
extern int		qrec_free(), qrec_print(), qrec_comp(), qrec_parent_set(), 
			qrec_count_inc, qrec_nop();













