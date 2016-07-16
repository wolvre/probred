
#define	SPLIT		1
#define NO_SPLIT	0

#define	NEW_KEY		0
#define OLD_KEY		1

/*************************************************************
*******************************************************************
*
*	2-3 tree nodes.  We need 
*
*	1. a 23 tree for the frames
*	2. a 23 tree for the formulus set
*	3. a 23 tree for the subformulae 
*	4. a 23 tree for the formulus closure of each tableau node.
*/
struct a23tree_type	{
  struct a23tree_type	*parent, *child1, *child2, *child3;
  /*
  int			id;
  */
  char			*key1, *key2;
};


struct a23key_type      {
  struct a23tree_type	*parent;
  int			self_index;
}; 



/*************************************************************
*******************************************************************
*
*	An example of key types of 23tree.
*	Linked list for frames
*/
/* 
* struct frmhead_type	{
*   
*   struct a23tree_type	*parent;
*   int			count; 
*   
*   int			id, length;
*   struct frm_slice_type	*frmlist; 
* };
*/




struct rec_type {
  struct a23tree_type	*parent;
  int			count;
  struct red_type	*redx, *redy, *result; 
}; 


struct rec3_type {
  struct a23tree_type	*parent;
  int			count;
  struct red_type	*red1, *red2, *red3, *result; 
}; 


struct rec5_type {
  struct a23tree_type	*parent;
  int			count;
  struct red_type	*red1, *red2, *red3, *red4, *red5, *result; 
}; 


struct double_rec_type {
  struct a23tree_type	*parent; 
  int			count; 
  struct red_type	*redx, *redy, *result1, *result2; 
}; 

struct qrec_type {
  struct a23tree_type	*parent;
  int			count;
  struct red_type	*d1, *d2, *d3, *d4, *result; 
}; 








