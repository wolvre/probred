extern struct statement_type 
  *ACTION_SAVE_RETMODE, 
  *ACTION_RESUME_RETMODE; 

extern void 
  discrete_lhs_rhs_setup(
    struct red_type		*, // *red_lazy_space, 
    struct statement_type	*, // *act, 
    int				,  // pi, 

    struct ps_exp_type		**, // **lvar_ptr, 
    int				*, // *lpi_ptr, // if RT[lopd] is returned NULL, 
    int                 	, // lopdi,    // *lpi_ptr is the static lhs process index. 

    int				*, // *offset_lb_ptr, // if RT[offset] is returned NULL,
    int				*, // *offset_ub_ptr, // *offset_lb_ptr and *offset_ub_ptr
    int				// offseti        // are the static range of offset.
  ), 
  clock_assign_setup(
    struct red_type		*, // *red_lazy_space, 
    struct statement_type	*, // *act, 
    int				, // pi, 

    struct ps_exp_type		**, // **lvar_ptr, 
    int				*, // *lpi_ptr, // if RT[lopd] is returned NULL, 
    int                   	, // lopdi,     // *lpi_ptr is the static lhs process index. 

    struct ps_exp_type		**, // **rvar_ptr, // if *rvar_ptr is NULL, 
                                    // then there is no RHS variable.
    int				*, // *rpi_ptr, // if RT[ropd] is returned NULL,
    int				, // ropdi,     // *rpi_ptr is the static rhs process index. 

    int				*, // *offset_lb_ptr, // if RT[offset] is returned NULL,
    int				*, // *offset_ub_ptr, // *offset_lb_ptr and *offset_ub_ptr
    int				// offseti          // are the static range of offset.
  ); 




extern struct red_type	
  *red_action_discrete_value(), 
  *red_effect(), *red_effect_simple(), 

  *red_clock_assign_fwd(), 
  *red_action_clock_assign_fwd(), 
  *red_discrete_assign_fwd(), 
  *red_action_discrete_assign_fwd(),  
  *red_action_discrete_inc_fwd(), 
  *red_action_discrete_dec_fwd(),

  *red_action_fwd(), 
  *red_statement_fwd(
    int				, // src, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				, // flag_polarity, 
    int				// flag_lazy_eval 
  ),
  *red_statement_abstract_fwd(
    int				, // src, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				// flag_lazy_eval
  ),
  *red_statement_untimed_fwd(
    int				, // src, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				// flag_lazy_eval
  ),

  *red_clock_assign_bck(), 
  *red_action_clock_assign_bck(),
  *red_discrete_assign_bck(), 
  *red_action_discrete_assign_bck(),
  *red_action_discrete_inc_bck(),
  *red_action_discrete_dec_bck(),

  *red_action_bck(), 
  *red_daction_bck(), 
  *red_statement_bck(
    int				, // dst, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				, // flag_polarity, 
    int				// flag_lazy_eval 
  ),
  *red_dstatement_bck(),
  *red_statement_untimed_bck(
    int				, // dst, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				// flag_lazy_eval
  ),
  *red_statement_abstract_bck(
    int				, // dst, 
    int				, // pi, 
    struct statement_type	*, // *st, 
    int				// flag_lazy_eval
  );




extern inline struct red_type *red_general_statement_fwd(
  int 			, // source frame index, 
  int 			, // pi, 
  struct statement_type *, // *st, 
  int			, // flag_abstraction 
  int			  // flag_lazy_eval
); 




extern inline struct red_type *red_general_statement_bck(
  int 			, // dest frame index, 
  int 			, // pi, 
  struct statement_type *, // *st, 
  int			, // flag_abstraction 
  int			// flag_lazy_eval
);



