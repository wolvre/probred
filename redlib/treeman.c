
/*===================================================================
*
*       con23tree.c
*
*/

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <malloc.h>

#include "redbop.h" 
#include "redbop.e" 
#include "redbasics.h" 
#include "redbasics.e" 
#include "treeman.h"
#include "hashman.h" 

#define	FOREVER	1

#define	TRUE	1
#define	FALSE	0

extern	FILE	*RED_OUT; 

struct a23tree_type		*a23tree_pool;
int				a23tree_count, free_a23tree_count;





/*********************************************************************
*
*	Initial routine before calling any other routine in artl23tree.c
*
*/
struct a23tree_type	*tat; 
int 			tac; 

init_23tree_management()
{
  tac = 0; 
  tat = NULL; 
  a23tree_pool = NULL;
  a23tree_count = free_a23tree_count = 0;
}
  /* init_23tree_management() */



int	report_23tree_management(op) 
     int	op; 
{
  if (op == FLAG_GC_REPORT)
    fprintf(RED_OUT, "\na23tree_count = %1d; free_a23tree_count = %1d;\n", a23tree_count, free_a23tree_count); 
   
  return(a23tree_count*sizeof(struct a23tree_type)); 
}
/* report_23tree_management() */ 




/*********************************************************************
*
*	Allocation and deallocation of frame tree nodes
*/

struct a23tree_type	*alloc_23tree()
{
  struct a23tree_type 		*a23t;
  struct addr_check_type	*addr;

  /*
  if (a23tree_pool == NULL) {
  */
    a23t = (struct a23tree_type *) malloc(sizeof(struct a23tree_type));
    if (a23t == NULL) {
      fprintf(RED_OUT, "out of memory!\n"); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
      exit(0);
    }
    /*
    if (a23t == (struct a23tree_type *) 0x809ddb0) {
      tat = a23t; 
      fprintf(RED_OUT, "%1d: target 23tree node allocated %x\n", tac++, a23t); 
      for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
      exit(0); 
    } 
    */
    ++a23tree_count;
    return(a23t);

    /*
    a23t->parent = a23t->child1 = a23t->child2 = a23t->child3 = NULL;
    a23t->key1 = NULL; 
    a23t->key2 = NULL; 
  }
  else {
    a23t = a23tree_pool;
    free_a23tree_count--; 
    a23tree_pool = a23tree_pool->parent;
    a23t->parent = a23t->child1 = a23t->child2 = a23t->child3 = NULL;
    a23t->key1 = a23t->key2 = NULL;
    if (a23t->id > 0){
      fprintf(RED_OUT, "A dirty 23-tree node is going to be used again.\n");
      fflush(stdout); 
      for(;1;);
    }
    else 
      a23t->id = -1 * a23t->id;
    return(a23t);
  }
    */
}
  /* alloc_23tree() */




free_23tree(a23t)
struct a23tree_type	*a23t;
{
  /*
  if (a23t == (struct a23tree_type *) 0x809ddb0) {
    tat = NULL; 
    fprintf(RED_OUT, "%1d: target 23tree node freed %x\n", tac++, a23t); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
  */
  a23tree_count--; 
  free(a23t); 

  /*
  if (a23t->id < 0){
    fprintf(RED_OUT, "A clean 23-tree node is going to be freed again.\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  }
  else 
    a23t->id = -1 * a23t->id;


  a23t->child1 = a23t->child2 = a23t->child3 = NULL;
  a23t->parent = a23tree_pool;
  a23tree_pool = a23t;
  free_a23tree_count++; 
  */
}
  /* free_23tree() */



rec_free_entire_23tree(tree, free_key)
     struct a23tree_type	*tree;
     int			(*free_key)(); 
{
  /*
  fprintf(RED_OUT, "***** free 23-tree addr = %x recursively\n", tree); 
  if (tree->id < 0){
    fprintf(RED_OUT, "A clean 23-tree node is going to be freed again\n");
    fflush(stdout); 
    for(;1;);
  }
  */

  if (tree->child1 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child1 addr=%d\n", 
     *  tree->child1); 
     */
    rec_free_entire_23tree(tree->child1, free_key); 
    tree->child1 = NULL; 
  }
  if (tree->child2 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child2 addr=%d\n", 
     *  tree->child2); 
     */
    rec_free_entire_23tree(tree->child2, free_key); 
    tree->child2 = NULL; 
  }
  if (tree->child3 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child3 addr=%d\n", 
     *  tree->child3); 
     */
    rec_free_entire_23tree(tree->child3, free_key); 
    tree->child3 = NULL; 
  }
  if (tree->key1 != NULL) {
    free_key(tree->key1);
    tree->key1 = NULL;
  }
  if (tree->key2 != NULL) {
    free_key(tree->key2); 
    tree->key2 = NULL;
  }

  free_23tree(tree); 
/*  printf("4. a23tree_pool = %d\n", a23tree_pool); 
 *  if (abs(tree->id) == 4663)
 *   fprintf(RED_OUT, "Old 23-tree id = %d freed at step %d.\n", tree->id, step_count); 
 */
}
  /* rec_free_entire_23tree() */



free_entire_23tree(a23t, free_key)
     struct a23tree_type	*a23t;
     int			(*free_key)(); 
{
  /*
  fprintf(RED_OUT, "***** free 23-tree rooted at addr = %1x\n", a23t); 
  */
  update_memory_usage(); 
  
  if (a23t->child1 != NULL) {
    rec_free_entire_23tree(a23t->child1, free_key); 
    free_key(a23t->key1); 
    a23t->child1 = NULL;
    a23t->key1 = NULL;
  }
  else if (a23t->key1 != NULL) {
    free_key(a23t->key1);
    a23t->key1 = NULL;
  }
  free_23tree(a23t); 
}
  /* free_entire_23tree() */



rec_free_entire_23tree_without_key(tree, keypa_set)
     struct a23tree_type	*tree;
     int			(*keypa_set)(); 
{
  /*
  fprintf(RED_OUT, "***** free 23-tree addr = %d recursively without key\n", tree); 
  if (tree->id < 0){
    fprintf(RED_OUT, "A clean 23-tree node is going to be freed again.\n");
    fflush(stdout); 
    for(;1;);
  }
  else 
    tree->id = -1 * tree->id;
  */

  if (tree->child1 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child1 addr=%d\n", 
     *  tree->child1); 
     */
    rec_free_entire_23tree_without_key(tree->child1, keypa_set); 
    tree->child1 = NULL; 
  }
  if (tree->child2 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child2 addr=%d\n", 
     *  tree->child2); 
     */
    rec_free_entire_23tree_without_key(tree->child2, keypa_set); 
    tree->child2 = NULL; 
  }
  if (tree->child3 != NULL) {
    /* fprintf(RED_OUT, "***** free old 23-tree internal child3 addr=%d\n", 
     *  tree->child3); 
     */
    rec_free_entire_23tree_without_key(tree->child3, keypa_set); 
    tree->child3 = NULL; 
  }
  if (tree->key1 != NULL) {
    keypa_set(tree->key1, NULL); 
    tree->key1 = NULL;
  }
  if (tree->key2 != NULL) {
    keypa_set(tree->key2, NULL); 
    tree->key2 = NULL;
  }
  free_23tree(tree); 

}
  /* rec_free_entire_23tree_without_key() */



free_entire_23tree_without_key(a23t, keypa_set)
     struct a23tree_type	*a23t;
     int			(*keypa_set)(); 
{
  if (a23t->child1 != NULL) {
    fprintf(RED_OUT, 
      "***** free 23-tree rooted at addr = %d\n", 
      (unsigned int) a23t->child1
    ); 

    rec_free_entire_23tree_without_key(a23t->child1, keypa_set); 
    a23t->child1 = NULL;

  }
  a23t->key1 = NULL;
  free_23tree(a23t); 
}
  /* free_entire_23tree_without_key() */



struct a23tree_type	*copy_23tree(t, keycount_inc)
     struct a23tree_type	*t;
     int			(*keycount_inc)();
{
  struct a23tree_type	*ct; 

  ct = alloc_23tree();
  if (t->child1 == NULL)
    ct->child1 = NULL;
  else {
    ct->child1 = copy_23tree(t->child1, keycount_inc); 
    ct->child1->parent = ct;
  }
  if (t->child2 == NULL)
    ct->child2 = NULL;
  else {
    ct->child2 = copy_23tree(t->child2, keycount_inc); 
    ct->child2->parent = ct;
  }
  if (t->child3 == NULL)
    ct->child3 = NULL;
  else {
    ct->child3 = copy_23tree(t->child3, keycount_inc); 
    ct->child3->parent = ct;
  }
  if (t->key1 == NULL) 
    ct->key1 = NULL;
  else {
    ct->key1 = t->key1;
    keycount_inc(ct->key1);
  }
  if (t->key2 == NULL)
    ct->key2 = NULL;
  else {
    ct->key2 = t->key2;
    keycount_inc(ct->key2);
  }
  return(ct);
}
  /* copy_23tree() */



/*********************************************************************
*
*	init_frmtree()
*/

init_23tree(a23treeptr)
struct a23tree_type	**a23treeptr;
{
  (*a23treeptr) = alloc_23tree();
  (*a23treeptr)->child1 = (*a23treeptr)->child2 = (*a23treeptr)->child3 = NULL;
  (*a23treeptr)->key1 = (*a23treeptr)->key2 = NULL;
  (*a23treeptr)->parent = NULL;
}
  /* init_23tree() */




/************************************************************************
*************************************************************************
*
*	struct frmkey_type	*search_23tree(frmhead)
*
*	Routines for searching a frame value.
*	A pointer to the following record is returned.
*	parent is the frame tree node that should contain the search key.
*	self_index = 1 or 2 if the search key is equal to the 1st or 2nd
*	key of the node pointed by parent.
*	self_index = -1, -2, or -3 if the search key does not exist and
*	should be inserted in the 1st, 2nd, or 3rd child subtree of the
*	node pointed by parent.
*/

struct a23key_type	a23_key;

struct a23key_type	*search_23tree(key, root, comp23)
     register char		*key;
     struct a23tree_type	*root;
     register int		(*comp23)();
{
  int				comp1, comp2, childidx; 
  register struct a23tree_type	*toptree, *partree;

/*  fprintf(RED_OUT, "In search 23tree\n"); 
*/
  if (root->key1 == NULL) {
    a23_key.parent = root;
    a23_key.self_index = 0;
    return(&a23_key);
  }
  else if (!(comp1 = comp23(key, root->key1))) {
    a23_key.parent = root;
    a23_key.self_index = 1;
    return(&a23_key);
  }
  else if (comp1 > 0) {
    a23_key.parent = root;
    a23_key.self_index = -2;
    return(&(a23_key));
  }
  else 
    for (partree = root, toptree = root->child1, childidx = -1; 
	 FOREVER; 
	 ) {
      /*
      if ((partree != NULL) && (partree->id < 0)) {
	fprintf(RED_OUT, "A dirty parent 23-tree node in the search: id=%d, addr=%x\n", 
	       partree->id, partree);
	fflush(RED_OUT); 
	for (;1;);
      }
      if ((toptree != NULL) && (toptree->id < 0)) {
	fprintf(RED_OUT, "A dirty top 23-tree node in the search: id=%d, addr=%x\n", 
	       toptree->id, toptree);
	fflush(RED_OUT); 
	for (;1;);
      }
      */
      if (toptree == NULL) {
	a23_key.parent = partree;
	a23_key.self_index = childidx;
	return(&a23_key);
      }
      else if (!(comp1 = comp23(key, toptree->key1))) {
	a23_key.parent = toptree;
	a23_key.self_index = 1;
	return(&a23_key);
      }
      else if (toptree->key2 == NULL)
	comp2 = -1;
      else if (!(comp2 = comp23(key,toptree->key2))) {
	a23_key.parent = toptree;
	a23_key.self_index = 2;
	return(&a23_key);
      }
      
      partree = toptree;
      if (comp1 < 0) {
	childidx = -1;
	toptree = toptree->child1;
      }
      else if (comp2 < 0) {
	childidx = -2; 
	toptree = toptree->child2;
      }
      else  {
	childidx = -3;
	toptree = toptree->child3;
      }
    }
}
  /* search_23tree() */



/****************************************************************
*
*	Routines for element membership
*/
char *membership_23tree(key, root, comp23, print_key)
     char			*key;
     struct a23tree_type	*root;
     int			(*comp23)(), (*print_key)();
{
  int	comp;
  char	*tempkey;
  struct a23key_type	*a23key;

  if (root->key1 == NULL) { 
    return(NULL);
  }
  else if (!(comp = comp23(key, root->key1))) {
    return(root->key1);
  }
  else if (comp>0) {
    return(NULL);
  }
  else {
    /* The first phase tries to allocate the node. */
    a23key = search_23tree(key, root, comp23);
    /* fprintf(RED_OUT, "Self_index : %d\n", a23key->self_index); */

    if (a23key->self_index > 0)
      if (a23key->self_index == 1) 
	return(a23key->parent->key1); 
      else
	return(a23key->parent->key2); 
    else {
      return(NULL);
    }
  }
}
  /* membership_23tree() */








/*******************************************************************
*************************************************************************
*
*	Routines for rebalancing a 2-3 trees after adding a node.
*/  

add_rebalance_23tree(toptree, root, keyparent_set, print_key)
     struct a23tree_type 	*toptree, *root;
     int			(*keyparent_set)(), (*print_key)();
{
  struct a23tree_type	*partree, *newtree;

  /*  fprintf(RED_OUT, "\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++\nBalancing 23tree:\n"); 
  print_23tree(root, 0, print_key); 
  */

  for (partree = toptree->parent; partree != root; toptree = partree, partree = partree->parent) {

    if (partree->key2 == NULL) {
      if (partree->child1 == toptree) {
	partree->key2 = partree->key1;
	partree->child3 = partree->child2;
	partree->key1 = toptree->key1;
	keyparent_set(partree->key1, partree);
	partree->child1 = toptree->child1;
	partree->child2 = toptree->child2;
	if (partree->child2 != NULL) 
	  partree->child1->parent = partree->child2->parent = partree;
	free_23tree(toptree);
      }
      else if (partree->child2 == toptree) {
	partree->key2 = toptree->key1;
	keyparent_set(partree->key2, partree);
	partree->child3 = toptree->child2;
	partree->child2 = toptree->child1;
	if (partree->child2 != NULL) 
	  partree->child2->parent = partree->child3->parent = partree;
	free_23tree(toptree);
      }
      break;
    }
    else if (partree->child1 == toptree) {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key2;
      newtree->key2 = NULL;
      keyparent_set(newtree->key1, newtree);

      newtree->child1 = partree->child2;
      newtree->child2 = partree->child3;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL)
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key2 = NULL;
      partree->child2 = newtree;
      partree->child3 = NULL;
    }
    else if (partree->child2 == toptree) {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key2;
      newtree->key2 = NULL;
      keyparent_set(newtree->key1, newtree);

      newtree->child1 = toptree->child2;
      newtree->child2 = partree->child3;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL) 
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key2 = toptree->key1;
      toptree->key1 = partree->key1;
      partree->key1 = partree->key2;
      partree->key2 = NULL;
      keyparent_set(toptree->key1, toptree);
      keyparent_set(partree->key1, partree);

      toptree->child2 = toptree->child1;
      toptree->child1 = partree->child1;
      if (toptree->child1 != NULL)
	toptree->child1->parent = toptree;

      partree->child1 = toptree;
      partree->child2 = newtree;
      partree->child3 = NULL;
    }
    else /* if (partree->child3 == toptree) */ {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key1;
      newtree->key2 = NULL;
      keyparent_set(newtree->key1, newtree);

      newtree->child1 = partree->child1;
      newtree->child2 = partree->child2;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL) 
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key1 = partree->key2;
      partree->key2 = NULL;
      partree->child1 = newtree;
      partree->child2 = toptree;
      partree->child3 = NULL;
    }
  }
  /* End of for loop */

  /*  fprintf(RED_OUT, "\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++\nAfter balancing 23tree:\n"); 
  print_23tree(root, 0, print_key); 
  fprintf(RED_OUT, "\n\n\n\n"); 
  */
  return; 
}
  /* add_rebalance_23tree() */



/*********************************************************************
*
*	Routine for rebalancing a 2-3 trees after adding a node.
*	except the parent of key will not modified.
*	This routine is only used for adding subforms to formset.  
*/  

add_rebalance_23tree_without_parent(toptree, root, print_key)
     struct a23tree_type 	*toptree, *root;
     int			(*print_key)();
{
  struct a23tree_type	*partree, *newtree;
  int			phase2_code;

  for (phase2_code = SPLIT, partree = toptree->parent; 
       (phase2_code == SPLIT) && (partree != root); 
       toptree = partree, partree = partree->parent) 

    if (partree->key2 == NULL) {
      if (partree->child1 == toptree) {
	partree->key2 = partree->key1;
	partree->child3 = partree->child2;
	partree->key1 = toptree->key1;
	partree->child1 = toptree->child1;
	partree->child2 = toptree->child2;
	if (partree->child2 != NULL) 
	  partree->child1->parent = partree->child2->parent = partree;
	free_23tree(toptree);
      }
      else if (partree->child2 == toptree) {
	partree->key2 = toptree->key1;
	partree->child3 = toptree->child2;
	partree->child2 = toptree->child1;
	if (partree->child2 != NULL) 
	  partree->child2->parent = partree->child3->parent = partree;
	free_23tree(toptree);
      }
      phase2_code = NO_SPLIT;
    }
    else if (partree->child1 == toptree) {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key2;
      newtree->key2 = NULL;

      newtree->child1 = partree->child2;
      newtree->child2 = partree->child3;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL)
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key2 = NULL;
      partree->child2 = newtree;
      partree->child3 = NULL;
    }
    else if (partree->child2 == toptree) {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key2;
      newtree->key2 = NULL;

      newtree->child1 = toptree->child2;
      newtree->child2 = partree->child3;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL) 
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key2 = toptree->key1;
      toptree->key1 = partree->key1;
      partree->key1 = partree->key2;
      partree->key2 = NULL;

      toptree->child2 = toptree->child1;
      toptree->child1 = partree->child1;
      if (toptree->child1 != NULL)
	toptree->child1->parent = toptree;

      partree->child1 = toptree;
      partree->child2 = newtree;
      partree->child3 = NULL;
    }
    else /* if (partree->child3 == toptree) */ {
      newtree = alloc_23tree();
      newtree->parent = partree;

      newtree->key1 = partree->key1;
      newtree->key2 = NULL;

      newtree->child1 = partree->child1;
      newtree->child2 = partree->child2;
      newtree->child3 = NULL;
      if (newtree->child1 != NULL) 
	newtree->child1->parent = newtree->child2->parent = newtree;

      partree->key1 = partree->key2;
      partree->key2 = NULL;
      partree->child1 = newtree;
      partree->child2 = toptree;
      partree->child3 = NULL;
    }
  /* End of for loop */
}
  /* add_rebalance_23tree_without_parent() */



/****************************************************************
*
*	Routines for adding a 23tree node
*/



char 	*add_23tree(
  key, 
  root, 
  comp23, 
  free_key, 
  keycount_inc, 
  keyparent_set, 
  print_key
) 
  char			*key;
  struct a23tree_type	*root;
  int			(*comp23)(), (*free_key)(), 
			(*keycount_inc)(), (*keyparent_set)(),
			(*print_key)();
{
  int			comp;
  char			*tempkey;
  struct a23tree_type	*toptree, *partree; 
  struct a23key_type	*a23key;

  if (root->key1 == key || root->key2 == key) 
    return(key); 
  else if (root->key1 == NULL) { 
    root->key1 = key;
    keyparent_set(key, root);
    keycount_inc(key);
    return(key);
  } 
  else if (!(comp = comp23(key, root->key1))) {
/*    fprintf(RED_OUT, "Compare two keys :\n"); 
*    print_key(key,0);
*    print_key(root->key1,0);
*    fprintf(RED_OUT, "result = %d\n"); 
*/

    keycount_inc(root->key1);
    if (root->key1 != key) 
      free_key(key);
    return(root->key1);
  }
  else if (comp>0) {
    /* Swap the last key in the tree and the search key. */
    tempkey = root->key1;
    root->key1 = key;
    keyparent_set(key, root);

    /* Originally : 
     *    itr_add_23tree(tempkey, root, comp23, keyparent_set, print_key);
     */
    /* The first phase tries to allocate the node. */
    a23key = search_23tree(tempkey, root, comp23);
    /* fprintf(RED_OUT, "Self_index : %d\n", a23key->self_index); */

    toptree = alloc_23tree(); 
    partree = a23key->parent;
    toptree->key1 = tempkey;
    keyparent_set(tempkey, toptree);
    toptree->parent = partree; 
    toptree->key2 = NULL;
    toptree->child1 = toptree->child2 = toptree->child3 = NULL;

    switch (a23key->self_index) {
    case -1 :
      partree->child1 = toptree; 
      break;
    case -2 : 
      partree->child2 = toptree; 
      break;
    case -3 : 
      partree->child3 = toptree; 
    }

    add_rebalance_23tree(toptree, root, keyparent_set, print_key); 
    keycount_inc(root->key1);
    return(root->key1);
  }
  else {
    /* Originally : 
     *    tempkey = itr_add_23tree(key, root,comp23,keyparent_set, print_key);
     */

    /* The first phase tries to allocate the node. */
    a23key = search_23tree(key, root, comp23);
    /* fprintf(RED_OUT, "Self_index : %d\n", a23key->self_index); */

    if (a23key->self_index > 0)
      if (a23key->self_index == 1) {
	/* fprintf(RED_OUT, "Begin freeing an already presented key copy.\n"); */
	/* fprintf(RED_OUT, "End freeing an already presented key copy.\n"); */
	tempkey = a23key->parent->key1;
      }
      else /* if (frmkey->self_index == 2) */  {
	/* fprintf(RED_OUT, "Begin freeing an already presented key copy.\n"); */
	/* fprintf(RED_OUT, "End freeing an already presented key copy.\n"); */ 
	tempkey = a23key->parent->key2;
      }  
    else {
      toptree = alloc_23tree(); 
      partree = a23key->parent;
      toptree->key1 = key;
      keyparent_set(key, toptree);
      toptree->parent = partree; 
      toptree->key2 = NULL;
      toptree->child1 = toptree->child2 = toptree->child3 = NULL;

      switch (a23key->self_index) {
      case -1 :
	partree->child1 = toptree; 
	break;
      case -2 : 
	partree->child2 = toptree; 
	break;
      case -3 : 
	partree->child3 = toptree; 
      }

      add_rebalance_23tree(toptree, root, keyparent_set, print_key); 
      tempkey = key;
    }

    keycount_inc(tempkey);
    if (tempkey != key) 
      free_key(key); 
    return(tempkey);
  }
}
  /* add_23tree() */







/***********************************************************************
*
*	Return OLD_KEY if the key was already in the tree.
*	Return NEW_KEY if the the key was not in the tree.  
*/
add_23tree_without_parent(key, root, comp23, keycount_inc, print_key)
     char			*key;
     struct a23tree_type	*root;
     int			(*comp23)(), (*keycount_inc)(), (*print_key)();
{
  int			comp, newkey_flag; 
  struct a23tree_type	*partree, *toptree; 
  struct a23key_type	*a23key; 
  char			*temp_key; 

  /* Add the formset to formset_tree */
  if (root->key1 == key || root->key2 == key) 
    return(OLD_KEY); 
  else if (root->key1 == NULL) {
    root->key1 = key;
    keycount_inc(key);
    return(NEW_KEY); 
  }

  if (!(comp = comp23(key, root->key1))) 
    return(OLD_KEY);
  else if (comp > 0) {
    /* Swap the last key in the tree and the search key. */
    temp_key = root->key1;
    root->key1 = key;
    keycount_inc(key); 
    newkey_flag = TRUE; 
    key = temp_key; 
  }
  else 
    newkey_flag = FALSE; 

  a23key = search_23tree(key, root, comp23);
  if (a23key->self_index > 0) 
    return(OLD_KEY); 
  else {
    toptree = alloc_23tree(); 
    partree = a23key->parent;
    toptree->key1 = key;
    if (!newkey_flag)
      keycount_inc(key); 
    toptree->parent = partree; 
    toptree->key2 = NULL;
    toptree->child1 = toptree->child2 = toptree->child3 = NULL;
    switch (a23key->self_index) {
    case -1 :
      partree->child1 = toptree; 
      break;
    case -2 : 
      partree->child2 = toptree; 
      break;
    case -3 : 
      partree->child3 = toptree; 
    }
    add_rebalance_23tree_without_parent(toptree, root, print_key); 
    return(NEW_KEY); 
  }
}
  /* add_23tree_without_parent() */




/***********************************************************************
*************************************************************************
*
*	Routines for deleting a key in a 23-tree
*/
rem_23tree(key, del_parent, root, keyparent_set, print_key)
     char			*key;
     struct a23tree_type	*root, *del_parent; 
     int		       	(*keyparent_set)(), (*print_key)();
{
  struct a23tree_type	*parent, *del_son, *grandpa, *uncle, *newparent;

  /* First phase, find a maximal smaller substituting key. */
  if (del_parent->child1 == NULL) 
    if (del_parent->key1 == key) 
      if (del_parent->key2 == NULL)  
	del_son = del_parent;
      else {
	del_parent->key1 = del_parent->key2;
	del_parent->key2 = NULL;
	return;
      }
    else {
      del_parent->key2 = NULL;
      return;
    }
  else if (del_parent->key1 == key) {
    for (del_son = del_parent->child1; del_son->child1 != NULL; )
      if (del_son->child3 != NULL)
	del_son = del_son->child3;
      else if (del_son->child2 != NULL)
	del_son = del_son->child2;
      else 
	del_son = del_son->child1;

    /* Substitute the key */
    if (del_son->key2 != NULL) {
      del_parent->key1 = del_son->key2;
      keyparent_set(del_parent->key1, del_parent);
      del_son->key2 = NULL;
      return;
    }
    else {
    /* Rebalancing needed. */
      del_parent->key1 = del_son->key1;
      keyparent_set(del_parent->key1, del_parent);
    }
  }
  else {
    for (del_son = del_parent->child2; del_son->child1 != NULL; )
      if (del_son->child3 != NULL)
	del_son = del_son->child3;
      else if (del_son->child2 != NULL)
	del_son = del_son->child2;
      else 
	del_son = del_son->child1;

    /* Substitute the key */
    if (del_son->key2 != NULL) {
      del_parent->key2 = del_son->key2;
      keyparent_set(del_parent->key2, del_parent);
      del_son->key2 = NULL;
      return;
    }
    else {
    /* Rebalancing needed. */
      del_parent->key2 = del_son->key1;
      keyparent_set(del_parent->key2, del_parent);
    }
  }

  /* Rebalance the tree */
  if (del_son == root) 
    root->key1 = NULL;
  else if (del_son == root->child1) {
    root->child1 = NULL;
    free_23tree(del_son);
    return;
  }
  else 
    for (parent = del_son, grandpa = parent->parent;
	 FOREVER;
	 parent = grandpa, grandpa = parent->parent){
      /* fprintf(RED_OUT, "deleting, parent : %d, grandpa : %d\n", parent->id, grandpa->id); */

      if (grandpa == root) {
	/* fprintf(RED_OUT, "case 1\n"); */
	if (del_son == del_son->parent->child1)
	  del_son->parent->child1 = NULL;
	else if (del_son == del_son->parent->child2)
	  del_son->parent->child2 = NULL;
	else 
	  del_son->parent->child3 = NULL;
	free_23tree(del_son);
	return;
      }
      else if (parent == grandpa->child3) {
      /* Parent is the third child of grandpa */
      /* No more rebalancing needed. */
	/* fprintf(RED_OUT, "case 2"); */
	uncle = grandpa->child2;
	/* fprintf(RED_OUT, "uncle : %d\n", uncle->id); */
	if (uncle->key2 != NULL) {
	/* The uncle has 3 children.  */
	  /* fprintf(RED_OUT, ".1\n"); */
	  newparent = alloc_23tree();
	  newparent->parent = grandpa;
	  newparent->child1 = uncle->child3;
	  if (newparent->child1 != NULL) 
	    newparent->child1->parent = newparent;
	  newparent->child2 = parent;
	  parent->parent = newparent;
	  newparent->child3 = NULL;
	  newparent->key1 = grandpa->key2;
	  keyparent_set(newparent->key1, newparent);
	  newparent->key2 = NULL;

	  grandpa->child3 = newparent;
	  grandpa->key2 = uncle->key2;
	  keyparent_set(grandpa->key2, grandpa);

	  uncle->key2 = NULL;
	  uncle->child3 = NULL;
	}
	else {
	/* The uncle has only 2 children. */
	  /* fprintf(RED_OUT, ".2\n"); */
	  uncle->child3 = parent;
	  parent->parent = uncle;
	  uncle->key2 = grandpa->key2;
	  keyparent_set(uncle->key2, uncle);
	  grandpa->child3 = NULL;
	  grandpa->key2 = NULL;
	}

	/* Release the initial deleted node. */
	if (del_son == del_son->parent->child1)
	  del_son->parent->child1 = NULL;
	else if (del_son == del_son->parent->child2)
	  del_son->parent->child2 = NULL;
	else 
	  del_son->parent->child3 = NULL;
	free_23tree(del_son);
	return;
      }
      else if (parent == grandpa->child2) {
      /* Parent is the second child of grandpa */
	/* fprintf(RED_OUT, "case 3"); */
	uncle = grandpa->child1;
	/* fprintf(RED_OUT, "uncle : %d\n", uncle->id); */
	if (uncle->key2 != NULL) {
	/* The uncle has 3 children.  No more rebalancing needed. */
	  /* fprintf(RED_OUT, ".1\n"); */
	  newparent = alloc_23tree();
	  newparent->parent = grandpa;
	  newparent->child1 = uncle->child3;
	  if (newparent->child1 != NULL) 
	    newparent->child1->parent = newparent;
	  newparent->child2 = parent;
	  parent->parent = newparent;
	  newparent->child3 = NULL;
	  newparent->key1 = grandpa->key1;
	  keyparent_set(newparent->key1, newparent);
	  newparent->key2 = NULL;

	  grandpa->child2 = newparent;
	  grandpa->key1 = uncle->key2;
	  keyparent_set(grandpa->key1, grandpa);

	  uncle->key2 = NULL;
	  uncle->child3 = NULL;

	  if (del_son == del_son->parent->child1)
	    del_son->parent->child1 = NULL;
	  else if (del_son == del_son->parent->child2)
	    del_son->parent->child2 = NULL;
	  else 
	    del_son->parent->child3 = NULL;
	  free_23tree(del_son);
	  return;
	}
	else if (grandpa->key2 != NULL) {
	/* Grandpa has three children and uncle has only two children. */
	/* No more balancing needed. */
	  /* fprintf(RED_OUT, ".2\n"); */
	  uncle->child3 = parent;
	  parent->parent = uncle;
	  uncle->key2 = grandpa->key1;
	  keyparent_set(uncle->key2, uncle);

	  grandpa->child2 = grandpa->child3;
	  grandpa->child3 = NULL;
	  grandpa->key1 = grandpa->key2;
	  grandpa->key2 = NULL;

	  if (del_son == del_son->parent->child1)
	    del_son->parent->child1 = NULL;
	  else if (del_son == del_son->parent->child2)
	    del_son->parent->child2 = NULL;
	  else 
	    del_son->parent->child3 = NULL;
	  free_23tree(del_son);
	  return;
	}
	else {
	/* Grandpa and uncle both have only two children. */
	/* More rebalancing needed. */
	  /* fprintf(RED_OUT, ".3\n");
	     fprintf(RED_OUT, "***\n");
	     print_frmtree(frm_tree, 0);
	  */
	  grandpa->child3 = parent;
	  grandpa->key2 = grandpa->key1;
	  grandpa->child2 = uncle->child2;
	  grandpa->child1 = uncle->child1;
	  if (grandpa->child2 != NULL) {
	    grandpa->child2->parent = grandpa;
	    grandpa->child1->parent = grandpa;
	  }
	  grandpa->key1 = uncle->key1;
	  keyparent_set(grandpa->key1, grandpa);
	  free_23tree(uncle);
	}
      }
      else {
      /* Parent is the first child of grandpa */
	/* fprintf(RED_OUT, "case 4"); */
	uncle = grandpa->child2;
	/* fprintf(RED_OUT, "uncle : %d\n", uncle->id); */
	if (uncle->key2 != NULL) {
	/* The uncle has 3 children.  No more rebalancing needed. */
	  /* fprintf(RED_OUT, ".1\n"); */
	  newparent = alloc_23tree();
	  newparent->parent = grandpa;
	  newparent->child1 = parent;
	  parent->parent = newparent;
	  newparent->child2 = uncle->child1;
	  if (newparent->child2 != NULL)
	    newparent->child2->parent = newparent;
	  newparent->child3 = NULL;
	  newparent->key1 = grandpa->key1;
	  keyparent_set(newparent->key1, newparent);
	  newparent->key2 = NULL;

	  grandpa->child1 = newparent;
	  grandpa->key1 = uncle->key1;
	  keyparent_set(grandpa->key1, grandpa);

	  uncle->key1 = uncle->key2;
	  uncle->key2 = NULL;
	  uncle->child1 = uncle->child2;
	  uncle->child2 = uncle->child3;
	  uncle->child3 = NULL;

	  if (del_son == del_son->parent->child1)
	    del_son->parent->child1 = NULL;
	  else if (del_son == del_son->parent->child2)
	    del_son->parent->child2 = NULL;
	  else 
	    del_son->parent->child3 = NULL;
	  free_23tree(del_son);
	  return;
	}
	else if (grandpa->key2 != NULL) {
	/* Grandpa has three children and uncle has only two children. */
	/* No more balancing needed. */
	  /* fprintf(RED_OUT, ".2\n"); */
	  uncle->child3 = uncle->child2;
	  uncle->child2 = uncle->child1;
	  uncle->child1 = parent;
	  parent->parent = uncle;
	  uncle->key2 = uncle->key1;
	  uncle->key1 = grandpa->key1;
	  keyparent_set(uncle->key1, uncle);

	  grandpa->child1 = grandpa->child2;
	  grandpa->child2 = grandpa->child3;
	  grandpa->child3 = NULL;
	  grandpa->key1 = grandpa->key2;
	  grandpa->key2 = NULL;

	  if (del_son == del_son->parent->child1)
	    del_son->parent->child1 = NULL;
	  else if (del_son == del_son->parent->child2)
	    del_son->parent->child2 = NULL;
	  else 
	    del_son->parent->child3 = NULL;
	  free_23tree(del_son);
	  return;
	}
	else {
	/* Grandpa and uncle both have only two children. */
	/* More rebalancing needed. */
	  /* fprintf(RED_OUT, ".3\n"); */
	  grandpa->key2 = uncle->key1;
	  keyparent_set(grandpa->key2, grandpa);
	  grandpa->child2 = uncle->child1;
	  grandpa->child3 = uncle->child2;
	  if (grandpa->child2 != NULL) {
	    grandpa->child3->parent = grandpa;
	    grandpa->child2->parent = grandpa;
	  }
	  free_23tree(uncle);
	}
      }
    }
}
  /* rem_23tree() */



/*************************************************************************
**************************************************************************
*
*	Routines for comparing two 23trees. 
*/
compare_23tree(treex, treey, comp23, print_key)
     struct a23tree_type	*treex, *treey;
     int			(*comp23)(), (*print_key)();
{
  struct a23tree_type	*sonx, *sony, *parentx, *parenty, *grandpax, *grandpay;
  int			keyxindex, keyyindex, comp;
  char			*keyx, *keyy;

/*  fprintf(RED_OUT, "The first tree is :\n");
*  print_23tree(treex, 0, print_key);
*  fprintf(RED_OUT, "The second tree is :\n");
*  print_23tree(treey, 0, print_key);
*/
  for (keyxindex = 1, parentx = treex, keyyindex = 1, parenty = treey;
       FOREVER; 
       ) 
    if (parentx == NULL)
      if (parenty == NULL) {
	/* fprintf(RED_OUT, "Identical\n"); */
	return(0);
      }
      else {
	/* fprintf(RED_OUT, "Smaller\n"); */
	return(-1);
      }
    else 
      if (parenty == NULL) {
	/* fprintf(RED_OUT, "Larger\n"); */
  	return(1);
      }
      else {
	/* fprintf(RED_OUT, "Unknown, x:%d, %d; y:%d, %d\n", 
	       parentx->id, keyxindex, parenty->id, keyyindex); */

	if (keyxindex == 1) {
	  sonx = parentx->child1;
	  keyx = parentx->key1;
	}
	else {
	  sonx = parentx->child2;
	  keyx = parentx->key2;
	}

	if (keyyindex == 1) {
	  sony = parenty->child1;
	  keyy = parenty->key1;
	}
	else {
	  sony = parenty->child2;
	  keyy = parenty->key2;
	}

/*	fprintf(RED_OUT, "One iteration :\n");
*	fprintf(RED_OUT, "First key : "); 
*	print_key(keyx, 0);
*	fprintf(RED_OUT, "Second key : "); 
*	print_key(keyy, 0);
*/
	if (comp = comp23(keyx, keyy))
	  if (comp > 0)
	    return(1);
	  else 
	    return(-1);
	else {
	/* So far no difference is seen.  */
	/* Still more comparison is needed. */

	  /* Track the next key to be compared for the first tree. */
	  if (sonx == NULL) 
	    if (keyxindex == 2) 
	      keyxindex = 1;
	    else {
	    /* Upward track is needed. */
	      for (grandpax = parentx->parent; 
		   (grandpax != NULL)&&(parentx == grandpax->child1);
		   parentx = grandpax, grandpax = parentx->parent);

	      if (grandpax == NULL)
		parentx = NULL;
	      else if (grandpax->child2 == parentx) {
		parentx = grandpax;
		keyxindex = 1;
	      }
	      else {
		parentx = grandpax;
		keyxindex = 2;
	      }
	    }
	  else {
	  /* Downward track is needed. */
	    for (; sonx->child1 != NULL;)
	      if (sonx->child3 != NULL) {
		parentx = sonx;
		sonx = parentx->child3;
	      }
	      else {
		parentx = sonx;
		sonx = parentx->child2;
	      }

	    parentx = sonx;
	    if (parentx->key2 != NULL)
	      keyxindex = 2;
	    else 
	      keyxindex = 1;
	  }

	  /* Track the next key to be compared for the second tree. */
	  if (sony == NULL) 
	    if (keyyindex == 2) 
	      keyyindex = 1;
	    else {
	    /* Upward track is needed. */
	      for (grandpay = parenty->parent; 
		   (grandpay != NULL)&&(parenty == grandpay->child1);
		   parenty = grandpay, grandpay = parenty->parent);

	      if (grandpay == NULL)
		parenty = NULL;
	      else if (grandpay->child2 == parenty) {
		parenty = grandpay;
		keyyindex = 1;
	      }
	      else {
		parenty = grandpay;
		keyyindex = 2;
	      }
	    }
	  else {
	  /* Downward track is needed. */
	    for (; sony->child1 != NULL;)
	      if (sony->child3 != NULL) {
		parenty = sony;
		sony = parenty->child3;
	      }
	      else {
		parenty = sony;
		sony = parenty->child2;
	      }

	    parenty = sony;
	    if (parenty->key2 != NULL)
	      keyyindex = 2;
	    else 
	      keyyindex = 1;
	  }
	}
      }
}
  /* compare_23tree() */


/*********************************************************************
***********************************************************************
*
*	Routines for printing the 2-3 trees.
*/
print_23tree(tree, depth, print_key)
     struct a23tree_type	*tree;
     int			depth, (*print_key)();
{
  if (tree->child1 != NULL) 
    print_23tree(tree->child1, depth+1, print_key);
  if (tree->key1 != NULL) {
    fprintf(RED_OUT, "23-addr = %1x; ", (unsigned int) tree);
    print_key(tree->key1, depth);
    fflush(RED_OUT);
  }
  if (tree->child2 != NULL)
    print_23tree(tree->child2, depth+1, print_key);
  if (tree->key2 != NULL) {
    fprintf(RED_OUT, "23-addr = %1x; ", (unsigned int) tree);
    print_key(tree->key2, depth);
    fflush(RED_OUT);
  }
  if (tree->child3 != NULL)
    print_23tree(tree->child3, depth+1, print_key);
}
  /* print_23tree() */




print_beautiful_23tree(tree, depth1, depth2, print_key)
     struct a23tree_type	*tree;
     int			depth1, depth2, (*print_key)();
{
  int 	i;

  for (i = depth1; i; i--)
    fprintf(RED_OUT, "   |");
  for (i = depth2; i; i--)
    fprintf(RED_OUT, "  ##");
  fprintf(RED_OUT, "##{23tree %x}\n", (unsigned int) tree);  
  if (tree->child1 != NULL) 
    print_beautiful_23tree(tree->child1, depth1, depth2+1, print_key);
  if (tree->key1 != NULL) {
    for (i = depth1; i; i--)
      fprintf(RED_OUT, "   |");
    for (i = depth2+1; i; i--)
      fprintf(RED_OUT, "  ##");
    print_key(tree->key1, 0);
  }
  if (tree->child2 != NULL) 
    print_beautiful_23tree(tree->child2, depth1, depth2+1, print_key);
  if (tree->key2 != NULL) {
    for (i = depth1; i; i--)
      fprintf(RED_OUT, "   |");
    for (i = depth2+1; i; i--)
      fprintf(RED_OUT, "  ##");
    print_key(tree->key2, 0);
  }
  if (tree->child3 != NULL)
    print_beautiful_23tree(tree->child3, depth1, depth2+1, print_key);
}
  /* print_beautiful_23tree() */




char	*get_last_key(tree)
     struct a23tree_type	*tree; 
{
  if (tree->child3 != NULL)
    return(get_last_key(tree->child3)); 
  else if (tree->key2 != NULL) 
    return(tree->key2); 
  else if (tree->child2 != NULL) 
    return(get_last_key(tree->child2)); 
  else if (tree->key1 != NULL)
    return(tree->key1); 
  else {
    fprintf(RED_OUT, "\nError: A dummy 23tree node\n"); 
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
    exit(0); 
  } 
}
/* get_last_key() */ 




char	*prevkey_23tree(key, key_get_parent) 
     char	*key; 
     int	(*key_get_parent)(); 
{
  struct a23tree_type	*parent, *grand_parent; 

  key_get_parent(key, &parent); 
  if (key == parent->key2) 
    if (parent->child2 == NULL)
      return(parent->key1); 
    else 
      return(get_last_key(parent->child2)); 
  else if (key == parent->key1) 
    if (parent->child1 == NULL) {
      for (grand_parent = parent->parent; grand_parent; ) 
	if (grand_parent->child3 == parent) 
	  return(grand_parent->key2); 
	else if (grand_parent->child2 == parent) 
	  return(grand_parent->key1); 
	else if (grand_parent->child1 == parent) {
	  parent = grand_parent; 
	  grand_parent = parent->parent; 
	} 
	else {
	  fprintf(RED_OUT, "\nError: parent inconsistent in 23tree\n"); 
	  for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; ); 
	  exit(0); 
	} 
      return(NULL); 
    } 
    else 
      return(get_last_key(parent->child1)); 
      
}
/* prevkey_23tree() */



#define	COUNT_EQUAL	0

struct a23tree_type	*garbage_collect_23tree(tree, free_key, key_count_test, key_parent_set, key_get_parent, print_key)
     struct a23tree_type	*tree; 
     int			(*free_key)(), (*key_count_test)(), 
				(*key_parent_set)(), (*key_get_parent)(), (*print_key)(); 
{
  char			*curkey, *prevkey; 
  struct a23tree_type	*t, *pt; 

  if (key_count_test(tree->key1, 0) == COUNT_EQUAL) {
    for (prevkey = get_last_key(tree->child1); 
	 ((prevkey != NULL) && (key_count_test(prevkey, 0) == COUNT_EQUAL)); 
	 prevkey = get_last_key(tree->child1)
	 ) {
      key_get_parent(prevkey, &pt); 
      rem_23tree(prevkey, pt, tree, key_parent_set, print_key); 
      free_key(prevkey); 
    } 

    free_key(tree->key1); 
    if (!prevkey) {
      tree->key1 = NULL; 
      return(tree); 
    }
    else {
      key_get_parent(prevkey, &pt); 
      rem_23tree(prevkey, pt, tree, key_parent_set, print_key); 
      tree->key1 = prevkey; 
      key_parent_set(prevkey, tree); 
    }
  }
  else 
    prevkey = tree->key1; 

  for (curkey = prevkey; curkey; ) {
    for (prevkey = prevkey_23tree(curkey, key_get_parent); 
	 ((prevkey != NULL) && (key_count_test(prevkey, 0) == COUNT_EQUAL)); 
	 prevkey = prevkey_23tree(curkey, key_get_parent)
	 ) {
      key_get_parent(prevkey, &pt); 
      rem_23tree(prevkey, pt, tree, key_parent_set, print_key); 
      free_key(prevkey); 
    } 
    
    if (prevkey == NULL)
      return(tree); 
    else {
      curkey = prevkey; 
    }
  }
  

  for (; a23tree_pool; ) {
    pt = a23tree_pool; 
    a23tree_pool = pt->parent; 
    free(pt); 
  } 
  a23tree_count = a23tree_count - free_a23tree_count; 
  free_a23tree_count = 0; 
}
/* garbage_collect_23tree() */ 





struct a23tree_type	*new_tree; 

rec_garbage_collect_23tree(tree, comp23, key_test, free_key, keycount_inc, keyparent_set, print_key) 
     struct a23tree_type	*tree; 
     int			(*comp23)(), (*key_test)(), (*free_key)(), 
				(*keycount_inc)(), (*keyparent_set)(), (*print_key)(); 
{
  char	*k1, *k2; 
  struct a23tree_type	*c1, *c2, *c3; 

  k1 = tree->key1; 
  k2 = tree->key2; 
  c1 = tree->child1; 
  c2 = tree->child2; 
  c3 = tree->child3; 

  free_23tree(tree); 

  if (k1) 
    if (key_test(k1))  
      add_23tree(k1, new_tree, comp23, free_key, keycount_inc, keyparent_set, print_key); 
    else 
      free_key(k1); 

  if (k2) 
    if (key_test(k2)) 
      add_23tree(k2, new_tree, comp23, free_key, keycount_inc, keyparent_set, print_key); 
    else 
      free_key(k2); 
  
  if (c1) 
    rec_garbage_collect_23tree(c1, comp23, key_test, free_key, keycount_inc, keyparent_set, print_key); 

  if (c2) 
    rec_garbage_collect_23tree(c2, comp23, key_test, free_key, keycount_inc, keyparent_set, print_key); 

  if (c3) 
    rec_garbage_collect_23tree(c3, comp23, key_test, free_key, keycount_inc, keyparent_set, print_key); 

  /*  fprintf(RED_OUT, "\nTo be freed 23tree garbage %x\n", tree); 
   */
}
/* rec_garbage_collect_23tree() */ 






process_23tree(t, key_process)
     struct a23tree_type	*t; 
     int			(*key_process)(); 
{
  if (t->key1 != NULL)
    key_process(t->key1);

  if (t->key2 != NULL) 
    key_process(t->key2); 

  if (t->child1 != NULL)
    process_23tree(t->child1, key_process); 

  if (t->child2 != NULL)
    process_23tree(t->child2, key_process); 

  if (t->child3 != NULL)
    process_23tree(t->child3, key_process); 
}
/* process_23tree() */ 




/****************************************************************
 *  The following are for the record management in the 23-trees. 
 */
int		rec_count, rec3_count, rec5_count; 


int	drec_count, qrec_count; 


struct rec_type	*rec_new(redx, redy)
     struct red_type	*redx, *redy;
{
  struct rec_type	*rec;
/*
  if (test_rec) {
    fprintf(RED_OUT, "!!!!!!!!!!rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
  rec = (struct rec_type *) malloc(sizeof(struct rec_type));
  rec_count++;
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "++++++++++rec=%1x allocated with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, redx, redy
	    );
    test_rec = rec;
  }
*/
  rec->redx = redx;
  rec->redy = redy;
  rec->result = NULL;
  return(rec);
}
/* rec_new() */




rec_free(rec)
     struct rec_type	*rec;
{
  rec_count--;

/*
  if (test_rec) {
    fprintf(RED_OUT, "??????????rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "----------rec=%1x freed with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, rec->redx, rec->redy
	    );
    fflush(RED_OUT);
    test_rec = NULL;
  }
*/
  if (rec_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  free(rec);
}
/* rec_free() */




int	rec_comp(rec1, rec2)
     struct rec_type	*rec1, *rec2; 
{
  int	comp; 

  if (rec1->redx < rec2->redx)
    return(-1); 
  else if (rec1->redx > rec2->redx)
    return(1);
  else if (rec1->redy < rec2->redy) 
    return(-1); 
  else if (rec1->redy > rec2->redy) 
    return(1); 
  else 
    return(0);     
}
/* rec_comp() */





int	rec_single_comp(rec1, rec2)
     struct rec_type	*rec1, *rec2; 
{
  int	comp; 

  if (rec1->redx < rec2->redx) 
    return(-1); 
  else if (rec1->redx > rec2->redx)
    return(1); 
  else 
    return(0);     
}
/* rec_single_comp() */




rec_parent_set(rec, pa)
     struct rec_type		*rec; 
     struct a23tree_type	*pa;
{
  rec->parent = pa; 
}
/* rec_parent_set() */ 



rec_nop(rec)
     struct rec_type	*rec; 
{

}
/* rec_nop() */ 



rec_count_inc(rec)
     struct rec_type	*rec; 
{
  rec->count++;
}
/* rec_count_inc() */ 





rec_print(rec, depth)
     struct rec_type	*rec;
     int		depth; 
{
  for (; depth; depth--)
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "REC:%x: x=%x, y=%x, r=%x\n", (unsigned int) rec, (unsigned int) rec->redx, (unsigned int) rec->redy, (unsigned int) rec->result); 
}
/* rec_print() */



struct rec3_type	*rec3_new(d1, d2, d3)
     struct red_type	*d1, *d2, *d3;
{
  struct rec3_type	*rec3;
/*
  if (test_rec) {
    fprintf(RED_OUT, "!!!!!!!!!!rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
  rec3 = (struct rec3_type *) malloc(sizeof(struct rec3_type));
  rec3_count++;
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "++++++++++rec=%1x allocated with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, redx, redy
	    );
    test_rec = rec;
  }
*/
  rec3->red1 = d1;
  rec3->red2 = d2;
  rec3->red3 = d3;
  rec3->result = NULL;
  return(rec3);
}
/* rec3_new() */




rec3_free(rec3)
     struct rec3_type	*rec3;
{
  rec3_count--;

/*
  if (test_rec) {
    fprintf(RED_OUT, "??????????rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "----------rec=%1x freed with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, rec->redx, rec->redy
	    );
    fflush(RED_OUT);
    test_rec = NULL;
  }
*/
  if (rec3_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  free(rec3);
}
/* rec3_free() */




int	rec3_comp(recx, recy)
     struct rec3_type	*recx, *recy; 
{
  int	comp; 

  if (recx->red1 < recy->red1)
    return(-1); 
  else if (recx->red1 > recy->red1)
    return(1);
  else if (recx->red2 < recy->red2) 
    return(-1); 
  else if (recx->red2 > recy->red2) 
    return(1); 
  else if (recx->red3 < recy->red3) 
    return(-1); 
  else if (recx->red3 > recy->red3) 
    return(1); 
  else 
    return(0);     
}
/* rec3_comp() */







rec3_parent_set(rec3, pa)
     struct rec3_type		*rec3; 
     struct a23tree_type	*pa;
{
  rec3->parent = pa; 
}
/* rec3_parent_set() */ 



rec3_nop(rec3)
     struct rec3_type	*rec3; 
{

}
/* rec3_nop() */ 



rec3_count_inc(rec3)
     struct rec3_type	*rec3; 
{
  rec3->count++;
}
/* rec3_count_inc() */ 





rec3_print(rec3, depth)
     struct rec3_type	*rec3;
     int		depth; 
{
  for (; depth; depth--)
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "REC3:%x: 1:%x, 2:%x, 3:%x, r=%x\n", 
    (unsigned int) rec3, (unsigned int) rec3->red1, (unsigned int) rec3->red2, (unsigned int) rec3->red3, (unsigned int) rec3->result
  ); 
}
/* rec3_print() */






struct rec5_type	*rec5_new(d1, d2, d3, d4, d5)
     struct red_type	*d1, *d2, *d3, *d4, *d5;
{
  struct rec5_type	*rec5;
/*
  if (test_rec) {
    fprintf(RED_OUT, "!!!!!!!!!!rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
  rec5 = (struct rec5_type *) malloc(sizeof(struct rec5_type));
  rec5_count++;
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "++++++++++rec=%1x allocated with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, redx, redy
	    );
    test_rec = rec;
  }
*/
  rec5->red1 = d1;
  rec5->red2 = d2;
  rec5->red3 = d3;
  rec5->red4 = d4;
  rec5->red5 = d5;
  rec5->result = NULL;
  return(rec5);
}
/* rec5_new() */




rec5_free(rec5)
     struct rec5_type	*rec5;
{
  rec5_count--;

/*
  if (test_rec) {
    fprintf(RED_OUT, "??????????rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "----------rec=%1x freed with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, rec->redx, rec->redy
	    );
    fflush(RED_OUT);
    test_rec = NULL;
  }
*/
  if (rec5_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  free(rec5);
}
/* rec5_free() */




int	rec5_comp(recx, recy)
     struct rec5_type	*recx, *recy; 
{
  int	comp; 

  if (recx->red1 < recy->red1)
    return(-1); 
  else if (recx->red1 > recy->red1)
    return(1);
  else if (recx->red2 < recy->red2) 
    return(-1); 
  else if (recx->red2 > recy->red2) 
    return(1); 
  else if (recx->red3 < recy->red3) 
    return(-1); 
  else if (recx->red3 > recy->red3) 
    return(1); 
  else if (recx->red4 < recy->red4) 
    return(-1); 
  else if (recx->red4 > recy->red4) 
    return(1); 
  else if (recx->red5 < recy->red5) 
    return(-1); 
  else if (recx->red5 > recy->red5) 
    return(1); 
  else 
    return(0);     
}
/* rec5_comp() */







rec5_parent_set(rec5, pa)
     struct rec5_type		*rec5; 
     struct a23tree_type	*pa;
{
  rec5->parent = pa; 
}
/* rec5_parent_set() */ 



rec5_nop(rec5)
     struct rec5_type	*rec5; 
{

}
/* rec5_nop() */ 



rec5_count_inc(rec5)
     struct rec5_type	*rec5; 
{
  rec5->count++;
}
/* rec5_count_inc() */ 





rec5_print(rec5, depth)
     struct rec5_type	*rec5;
     int		depth; 
{
  for (; depth; depth--)
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "REC3:%x: 1:%x, 2:%x, 3:%x, 4:%x, 5:%x, r=%x\n", 
    (unsigned int) rec5, (unsigned int) rec5->red1, (unsigned int) rec5->red2, (unsigned int) rec5->red3, (unsigned int) rec5->red4, (unsigned int) rec5->red5, (unsigned int) rec5->result
  ); 
}
/* rec5_print() */






struct double_rec_type	*drec_new(dx, dy)
     struct red_type	*dx, *dy; 
{
  struct double_rec_type	*drec; 

  drec = (struct double_rec_type *) malloc(sizeof(struct double_rec_type));
  drec_count++; 
  drec->redx = dx; 
  drec->redy = dy; 
  drec->result1 = NULL; 
  drec->result2 = NULL; 
  return(drec); 
}
/* drec_new() */ 




drec_free(drec)
     struct double_rec_type	*drec;
{
  free(drec);
  drec_count--; 
}
/* rec_free() */ 




int	drec_comp(drec1, drec2)
     struct double_rec_type	*drec1, *drec2; 
{
  int	comp; 

  if (drec1->redx < drec2->redx) 
    return(-1); 
  else if (drec1->redx > drec2->redx)
    return(1);
  else if (drec1->redy < drec2->redy) 
    return(-1); 
  else if (drec1->redy > drec2->redy) 
    return(1); 
  else 
    return(0);     
}
/* drec_comp() */




drec_parent_set(drec, pa)
     struct double_rec_type	*drec; 
     struct a23tree_type	*pa;
{
  drec->parent = pa; 
}
/* drec_parent_set() */ 



drec_nop(drec)
     struct double_rec_type	*drec;
{

}
/* drec_nop() */ 



drec_count_inc(drec)
     struct double_rec_type	*drec; 
{
  drec->count++; 
}
/* drec_count_inc() */ 





drec_print(drec, depth)
     struct double_rec_type	*drec;
     int			depth; 
{
  for (; depth; depth--) 
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "REC:%x: x=%x, y=%x, r=%x\n", (unsigned int) drec, (unsigned int) drec->redx, (unsigned int) drec->redy, (unsigned int) drec->result1, (unsigned int) drec->result2); 
}
/* drec_print() */




struct qrec_type	*qrec_new(d1, d2, d3, d4)
     struct red_type	*d1, *d2, *d3, *d4;
{
  struct qrec_type	*qrec;
/*
  if (test_rec) {
    fprintf(RED_OUT, "!!!!!!!!!!rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
  qrec = (struct qrec_type *) malloc(sizeof(struct qrec_type));
  qrec_count++;
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "++++++++++rec=%1x allocated with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, redx, redy
	    );
    test_rec = rec;
  }
*/
  qrec->d1 = d1;
  qrec->d2 = d2;
  qrec->d3 = d3;
  qrec->d4 = d4; 
  return(qrec);
}
/* qrec_new() */




qrec_free(qrec)
     struct qrec_type	*qrec;
{
  qrec_count--;

/*
  if (test_rec) {
    fprintf(RED_OUT, "??????????rec=%1x checked with count = %1d with redx=%x; redy=%x\n",
	  test_rec, rec_count, test_rec->redx, test_rec->redy
	  );
    fflush(RED_OUT);
  }
*/
/*
  if (rec == (struct rec_type *) 0x818ac48) {
    fprintf(RED_OUT, "----------rec=%1x freed with count = %1d with redx=%x; redy=%x\n",
	    rec, rec_count, rec->redx, rec->redy
	    );
    fflush(RED_OUT);
    test_rec = NULL;
  }
*/
  if (qrec_count < 0) {
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  free(qrec);
}
/* qrec_free() */




int	qrec_comp(qrec1, qrec2)
     struct qrec_type	*qrec1, *qrec2; 
{
  int	comp; 

  if (qrec1->d1 < qrec2->d1)
    return(-1); 
  else if (qrec1->d1 > qrec2->d1)
    return(1);
  else if (qrec1->d2 < qrec2->d2) 
    return(-1); 
  else if (qrec1->d2 > qrec2->d2) 
    return(1); 
  else if (qrec1->d3 < qrec2->d3)
    return(-1); 
  else if (qrec1->d3 > qrec2->d3)
    return(1);
  else if (qrec1->d4 < qrec2->d4) 
    return(-1); 
  else if (qrec1->d4 > qrec2->d4) 
    return(1); 
  else 
    return(0);     
}
/* qrec_comp() */






qrec_parent_set(qrec, pa)
     struct qrec_type		*qrec; 
     struct a23tree_type	*pa;
{
  qrec->parent = pa; 
}
/* qrec_parent_set() */ 



qrec_nop(qrec)
     struct qrec_type	*qrec; 
{

}
/* qrec_nop() */ 



qrec_count_inc(qrec)
     struct qrec_type	*qrec; 
{
  qrec->count++;
}
/* qrec_count_inc() */ 





qrec_print(qrec, depth)
     struct qrec_type	*qrec;
     int		depth; 
{
  for (; depth; depth--)
    fprintf(RED_OUT, "    "); 

  fprintf(RED_OUT, "QREC:%x: d1=%x, d2=%x, d3=%x, d4=$x, r=%x\n", (unsigned int) qrec, (unsigned int) qrec->d1, (unsigned int) qrec->d2, (unsigned int) qrec->d3, (unsigned int) qrec->d4, (unsigned int) qrec->result); 
}
/* qrec_print() */



