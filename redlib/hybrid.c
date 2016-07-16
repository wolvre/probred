#include <stdlib.h>
#include <stdio.h>
#include <string.h> 
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
*/
#include "redbop.h"
#include "redbop.e"

#include "redbasics.h"
#include "redbasics.e"

#include "redparse.h"
#include "redparse.e"

#include "fxp.e"

#include "vindex.e"

#include "exp.e" 

#include "redsymmetry.e"

#include "inactive.e"
#include "redparse.e"

#include "hashman.h" 
#include "hashman.e" 

#include "treeman.h" 
#include "treeman.e" 



int	DENSE_COUNT;

#define	FLAG_HYBRID_DELTA_TRANSITIVITY	1

#define	HYBRID_POSITION_DELTA_XTIVITY		1
#define	HYBRID_POSITION_PRIMED_ELIMINATION	2

int 	flag_hybrid, status_hybrid, position_hybrid;

int 	hchild_count, hfchild_count, hchild_link_count, hfchild_link_count, hrd_exp_count, hrd_term_count;

int	*w_hybrid_coeff_numerator, *w_hybrid_coeff_denominator, 
	*w_hybrid_vi,
	w_hybrid_offset_numerator, w_hybrid_offset_denominator;

struct hrd_exp_type	*test_hrd_exp;
struct red_type		*red_test_hybrid;


struct red_type	*hybrid_normalize();

struct action_type	*W_ACT;
struct parse_term_type	*W_TERM;
int			W_TERM_COUNT, W_HYBRID_INEQ_TYPE;

int			MASK_HYBRID_LENGTH,
			MASK_HYBRID_LIFTED_VI,
			MASK_HYBRID_VI_BASE,
			FLAG_DELTA_GENERATED,
			FLAG_HRD_EXP_STATIC,
			FLAG_WITH_PRIMED_VARIABLE,
			FLAG_LOCAL_HYBRID_VARIABLES, 
			FLAG_HEXP_VAR_IN_MODULES;

#define RATE_DONT_CARE	(-1024*1024*1024-1000)

struct variable_rate_type {
  int	lb_numerator, lb_denominator, ub_numerator, ub_denominator;
  struct hrd_exp_type	*primed_umprimed_hrd_exp,
			*umprimed_primed_hrd_exp;
}
  *VRATE;

struct hrd_exp_type	**HE_CLOCK_LB, *HRD_EXP_NULL;

#define	GAUSSIAN_NONSINGULAR	-2
#define	GAUSSIAN_NEGATIVE	-1
#define	GAUSSIAN_ZERO		0
#define	GAUSSIAN_POSITIVE	1


int
	**MG,  			/* to record the equations. */
	MG_ROW_COUNT,		/* to record the row index of the current equation. */
	MG_COL_COUNT,
	*MG_COL_SIGNIFICANT,
	*BITBASE, *BITLEN;

struct Gaussian_hrd_exp_type {
  struct hrd_exp_type	*hrd_exp;
  int			ub_numerator, ub_denominator;
}
  GHE[10];

int	GMultiple[10];

int	(*HRD_EXP_COMP)();


struct hrd_term_link_type	*hrd_term_insert(tlist, vi, cnum, cden, tcptr)
	struct hrd_term_link_type	*tlist;
	int				vi, cnum, cden, *tcptr;
{
  struct hrd_term_link_type	dummy_head, *pt, *nt, *t;

  dummy_head.next_hrd_term_link = tlist;
  for (pt = &dummy_head, t = pt->next_hrd_term_link;
       t != NULL && t->var_index < vi;
       pt = t, t = pt->next_hrd_term_link
       ) ;

  if (t == NULL || t->var_index > vi) {
    nt = (struct hrd_term_link_type *) malloc(sizeof(struct hrd_term_link_type));
    nt->var_index = vi;
    nt->coeff_numerator = cnum;
    nt->coeff_denominator = cden;
    nt->next_hrd_term_link = t;
    pt->next_hrd_term_link = nt;
    (*tcptr)++;
  }
  else /* t->var_index == vi */ {
    t->coeff_numerator = t->coeff_numerator * cden + t->coeff_denominator * cnum;
    t->coeff_denominator = t->coeff_denominator * cden;
    if (t->coeff_numerator == 0) {
      pt->next_hrd_term_link = t->next_hrd_term_link;
      free(t);
    }
    else {
      cden = gcd(t->coeff_numerator, t->coeff_denominator);
      t->coeff_numerator = t->coeff_numerator / cden;
      t->coeff_denominator = t->coeff_denominator / cden;
    }
  }
  return(dummy_head.next_hrd_term_link);
}
  /* hrd_term_insert() */




void	free_hrd_term_list(tlist)
	struct hrd_term_link_type	*tlist;
{
  struct hrd_term_link_type	*t;

  for (; tlist; t = tlist, tlist = tlist->next_hrd_term_link, free(t));
}
  /* free_hrd_term_list() */


int xor(int x, int y)
{    
    return ((x || y) && !(x && y)); 
}



int	rational_comp(nx, dx, ny, dy)
	int	nx, dx, ny, dy;
{
  int res;
  
  if (nx/dx>HYBRID_POS_INFINITY) {
    printf("nx/dx overflow in gybrid.c:rational_comp()");
    exit(0);
  }
  else if (ny/dy>HYBRID_POS_INFINITY) {
    printf("ny/dy overflow in gybrid.c:rational_comp()");
    exit(0);
  }
  else if (nx/dx<HYBRID_NEG_INFINITY) {
    printf("nx/dx underflow in gybrid.c:rational_comp()");
    exit(0);
  }
  else if (ny/dy<HYBRID_NEG_INFINITY) {
    printf("ny/dy underflow in gybrid.c:rational_comp()");
    exit(0);
  }  
    
  if (nx == HYBRID_POS_INFINITY && dx == 1)
    if (ny == HYBRID_POS_INFINITY && dy == 1)
      res=0;
    else
      res=1;
  else if (nx == HYBRID_NEG_INFINITY && dx == 1)
    if (ny == HYBRID_NEG_INFINITY && dy == 1)
      res=0;
    else
      res=-1;
  else
    if (ny == HYBRID_POS_INFINITY && dy == 1)
      res=-1;
    else if (ny == HYBRID_NEG_INFINITY && dy == 1)
      res=1;
    else {
      int a = nx*dy;
      int b = ny*dx;
  
      if(xor((nx>>31)&1,(dy>>31)&1)!=(a>>31&1)) {
        printf("overflow in hybrid.c::rational_comp()\n");
        printf("%d*%d=%d",(nx>>31)&1,(dy>>31)&1,(a>>31)&1);
        exit(0);
        }
      if(xor((ny>>31)&1,(dx>>31)&1)!=(b>>31&1)) {
        printf("overflow in hybrid.c::rational_comp()\n");
        printf("%d*%d=%d",(ny>>31)&1,(dx>>31)&1,(b>>31)&1);
        exit(0);
      }

        
      res=a-b;

      if((a>0 && b<0 && res<0) ||
         (a<0 && b>0 && res>0)) {
        printf("overflow in hybrid.c::rational_comp()\n");
        printf("%d-%d=%d",a,b,res);
        exit(0);
      }
                
    }

  return res;
}
  /* rational_comp() */ 
  
  
  
  
  
void	print_rational(bn, bd)
	int	bn, bd;
{
  if (bd == 1)
    if (bn == HYBRID_POS_INFINITY) {
      fprintf(RED_OUT, "oo");
      return;
    }
    else if (bn == HYBRID_NEG_INFINITY) {
      fprintf(RED_OUT, "-oo");
      return;
    }

  if (bn % 2)
    bn = (bn+1)/2;
  else
    bn = bn / 2;
  fprintf(RED_OUT, "%1d/%1d", bn, bd);
}
  /* print_rational() */




int 	gcd(gnum1, gnum2)
  int	gnum1, gnum2;
{
  gnum1 = abs(gnum1);
  gnum2 = abs(gnum2);

  if (!gnum1)
    if (gnum2)
      return(gnum2);
    else
      return(0);
  else if (!gnum2)
    return(gnum1);
  else while (TYPE_TRUE){
    if(gnum1 > gnum2){
      gnum1 = gnum1 % gnum2;
      if(gnum1==0) return gnum2;
    }
    else{
      gnum2 = gnum2 % gnum1;
      if(gnum2==0) return gnum1;
    }
  }
}
  /* gcd() */



int	lcm(lnum1, lnum2)
	int	lnum1, lnum2;
{
  int	g;

  if (lnum1 == 0)
    return(0);
  else if (lnum2 == 0)
    return(0);

  lnum1 = abs(lnum1);
  lnum2 = abs(lnum2);
  g = gcd(lnum1, lnum2);
  return (lnum1 * (lnum2 / g));
}
  /* lcm() */





int	prime_effect(xptr, yptr)
	int	*xptr, *yptr;
{
  int	sx, sy, mx, my, t;

  if (! *xptr)
    return(*yptr = 1);
  else if (! *yptr)
    return(*xptr = 1);
  else {
    mx = abs(*xptr);
    my = abs(*yptr);

    if (mx > my) {
      t = mx; mx = my; my = t;
    }

    while (mx) {
      t = my % mx; my = mx; mx = t;
    }
    *xptr = *xptr / my;
    *yptr = *yptr / my;

    return(my);
  }
}
/* prime_effect() */



int	bitlen(n)
	int	n;
{
  int	len, i;

  len = 0;
  n = abs(n);
  for (i = 4; i>=0; i--)
    if (n >= BITBASE[i]) {
      len = len + BITLEN[i];
      n = n / BITBASE[i];
    }
  return (len);
}
  /* bitlen() */



void	hybrid_ub_add(nx, dx, ny, dy, nptr, dptr)
	int	nx, dx, ny, dy, *nptr, *dptr;
{
  int	flag_fractional, flag, g, mx, my, lmx, lmy;
/*
  fprintf(RED_OUT, "hybrid_ub_add(%1d/%1d + %1d/%1d)", nx, dx, ny, dy);
  fflush(RED_OUT);
*/
  if (   (nx == HYBRID_POS_INFINITY && dx == 1)
      || (ny == HYBRID_POS_INFINITY && dy == 1)
      ) {
    *nptr = HYBRID_POS_INFINITY;
    *dptr = 1;
    return;
  }
  
  g = gcd(dx, dy); 
  mx = dy/g; 
  my = dx/g; 
  lmx = 29 - bitlen(dy/g); 
  lmy = 29 - bitlen(dx/g); 

  flag_fractional = (nx % 2) || (ny % 2);

  if (nx % 2)
    nx = (nx+1)/2;
  else
    nx = nx / 2;

  if (ny % 2)
    ny = (ny + 1)/2;
  else
    ny = ny / 2;

  if (   bitlen(nx) > lmx 
      || bitlen(dx) > lmx 
      || bitlen(ny) > lmy
      || bitlen(dy) > lmy
      ) {
    fprintf(RED_OUT, "Error: multiplication overflow in %1d/%1d+%1d/%1d.\n", 
	   nx, dx, ny, dy
	   );
    *nptr = HYBRID_POS_INFINITY;
    *dptr = 1;
    bk("xxx"); 
    return; 
    for (flag=1; flag; );
  }
  *nptr = nx * mx + ny * my;
  *dptr = dx * mx;
  if (*nptr)
    prime_effect(nptr, dptr);
  else
    *dptr = 1;

  nx = (*nptr) / (*dptr);
  dx = (*nptr) % (*dptr);
  if (nx > HYBRID_POS_BOUND || (nx == HYBRID_POS_BOUND && dx)) {
    fprintf(RED_OUT, "\nError: Positive overflow %1d/%1d in hybrid upperbound constraint addition.\n",
	    nx, dx
	    );
    *nptr = HYBRID_POS_INFINITY;
    *dptr = 1;
    bk("yyy"); 
    return;
    bk(); 
  }
  else if (nx < HYBRID_NEG_BOUND || (nx == HYBRID_NEG_BOUND && (flag_fractional || dx))) {
    fprintf(RED_OUT, "\nError: Negative overflow %1d/%1d in hybrid upperbound constraint addition.\n",
	    nx, dx
	    );
    *nptr = HYBRID_NEG_INFINITY;
    *dptr = 1;
    return;
    bk(); 
  }

  if (flag_fractional)
    *nptr = 2*(*nptr) - 1;
  else
    *nptr = 2*(*nptr);
/*
  fprintf(RED_OUT, "=%1d/%1d\n", *nptr, *dptr);
*/
}
/* hybrid_ub_add() */



int 	get_list_denominator_lcm(tlist)
  struct hrd_term_link_type	*tlist;
{
  int   m;

  if (tlist == NULL)
    return(0);

  for (m = tlist->coeff_denominator, tlist = tlist->next_hrd_term_link;
       tlist;
       tlist = tlist->next_hrd_term_link
       ) {
    m = m * tlist->coeff_denominator / gcd(m, tlist->coeff_denominator);
  }
  return(m);
}
  /* get_list_denominator_lcm() */




int	get_list_denominator_multiple(tlist)
  struct hrd_term_link_type	*tlist;
{
  int 	m;

  m = get_list_denominator_lcm(tlist);
  for (; tlist; tlist = tlist->next_hrd_term_link) {
    tlist->coeff_numerator = tlist->coeff_numerator * (m / tlist->coeff_denominator);
    tlist->coeff_denominator = 1;
  }

  return (m);
}
  /* get_list_denominator_factor() */





int 	get_list_numerator_gcd(tlist)
  struct hrd_term_link_type	*tlist;
{
  int   g;

  if (tlist == NULL)
    return(0);

  for (g = abs(tlist->coeff_numerator), tlist = tlist->next_hrd_term_link;
       tlist && g != 1;
       tlist = tlist->next_hrd_term_link
       ) {
    g = gcd(g, tlist->coeff_numerator);
  }
  return(g);
}
  /* get_list_numerator_gcd() */




int	get_list_numerator_factor(tlist)
  struct hrd_term_link_type	*tlist;
{
  int 	g;

  g = get_list_numerator_gcd(tlist);
  for (; tlist; tlist = tlist->next_hrd_term_link) {
    tlist->coeff_numerator = tlist->coeff_numerator / g;
    tlist->coeff_denominator = 1;
  }

  return (g);
}
  /* get_list_numerator_factor() */



void	rational_lift(nptr, dptr, m)
	int	*nptr, *dptr, m;
{
  if (!m) {
    *nptr = 0;
    *dptr = 1;
  }
  else if (*dptr == 1 && (*nptr == HYBRID_POS_INFINITY || *nptr == HYBRID_NEG_INFINITY))
    return;
  else if ((*nptr) % 2) {
    *nptr = ((*nptr) + 1) / 2;
    if (*nptr >= HYBRID_POS_BOUND / m) {
      *nptr = HYBRID_POS_INFINITY;
      *dptr = 1;
      return;
    }
    else if (*nptr <= HYBRID_NEG_BOUND / m) {
      *nptr = HYBRID_NEG_INFINITY;
      *dptr = 1;
      return;
    }
    *nptr = (*nptr) * m;
    prime_effect(nptr, dptr);
    *nptr = (*nptr)*2 - 1;
  }
  else {
    *nptr = (*nptr) / 2;
    if (*nptr >= HYBRID_POS_BOUND / m) {
      *nptr = HYBRID_POS_INFINITY;
      *dptr = 1;
      return;
    }
    else if (*nptr <= HYBRID_NEG_BOUND / m) {
      *nptr = HYBRID_NEG_INFINITY;
      *dptr = 1;
      return;
    }
    *nptr = (*nptr) * m;
    prime_effect(nptr, dptr);
    *nptr = 2*(*nptr);
  }
}
  /* rational_lift() */



void	rational_lower(nptr, dptr, m)
	int	*nptr, *dptr, m;
{
  if (!m) {
    fprintf(RED_OUT, "\nThere is something wrong with zero multiple solution.\n");
    bk(); 
  }
  else if (*dptr == 1 && (*nptr == HYBRID_POS_INFINITY || *nptr == HYBRID_NEG_INFINITY))
    return;
  else if ((*nptr) % 2) {
    *nptr = ((*nptr) + 1) / 2;
    *dptr = (*dptr) * m;
    prime_effect(nptr, dptr);
    *nptr = (*nptr)*2 - 1;
  }
  else {
    *nptr = (*nptr) / 2;
    *dptr = (*dptr) * m;
    prime_effect(nptr, dptr);
    *nptr = 2*(*nptr);
  }
}
  /* rational_lower() */



int	 hrd_exp_nop(he)
  struct hrd_exp_type	*he;
{
}
  /* hrd_exp_nop() */





int	hrd_exp_comp_normalized_magnitudes(he1, he2)
	struct hrd_exp_type	*he1, *he2;
{
  int	comp, len;

  if (comp = (he1->status & MASK_HYBRID_LENGTH) - (he2->status & MASK_HYBRID_LENGTH))
    return(comp);
  else if ((len = (he1->status & MASK_HYBRID_LENGTH)) > 0) {
    int	s1, s2, i, c1, c2;

    s1 = he1->hrd_term[0].coeff / abs(he1->hrd_term[0].coeff);
    s2 = he2->hrd_term[0].coeff / abs(he2->hrd_term[0].coeff);
    for (i = 0; i < len ; i++) {
      if (comp = he1->hrd_term[i].var_index - he2->hrd_term[i].var_index)
        return(comp);
      c1 = abs(s1*he1->hrd_term[i].coeff);
      c2 = abs(s2*he2->hrd_term[i].coeff);
      if (comp = c1 - c2)
        return(comp);
      else if (comp = s1*he1->hrd_term[i].coeff - s2*he2->hrd_term[i].coeff)
        return(comp);
    }
    return (s1 - s2);
  }
  else
    return(0);
}
  /* hrd_exp_comp_normalized_magnitudes() */





int	hrd_exp_comp_normalized_coefficients(he1, he2)
	struct hrd_exp_type	*he1, *he2;
{
  int	comp, len;

  if (comp = (he1->status & MASK_HYBRID_LENGTH) - (he2->status & MASK_HYBRID_LENGTH))
    return(comp);
  else if ((len = (he1->status & MASK_HYBRID_LENGTH)) > 0) {
    int	s1, s2, i, c1, c2;

    s1 = he1->hrd_term[0].coeff / abs(he1->hrd_term[0].coeff);
    s2 = he2->hrd_term[0].coeff / abs(he2->hrd_term[0].coeff);
    for (i = 0; i < len ; i++) {
      if (comp = he1->hrd_term[i].var_index - he2->hrd_term[i].var_index)
        return(comp);
      c1 = s1*he1->hrd_term[i].coeff;
      c2 = s2*he2->hrd_term[i].coeff;
      if (comp = c1 - c2)
        return(comp);
    }
    return (s1 - s2);
  }
  else
    return(0);
}
  /* hrd_exp_comp_normalized_coefficients() */




int	hrd_exp_comp_string(he1, he2)
	struct hrd_exp_type	*he1, *he2;
{
  int	comp, len;

  if (comp = (he1->status & MASK_HYBRID_LENGTH) - (he2->status & MASK_HYBRID_LENGTH))
    return(comp);
  else if ((len = (he1->status & MASK_HYBRID_LENGTH)) > 0) {
    int	s1, s2, i;

    s1 = strlen(he1->name);
    s2 = strlen(he2->name);
    for (i = 0; i < s1 && i < s2; i++)
      if (comp = (he1->name[i] - he2->name[i]))
        return (comp);
    if (i < s1)
      return(1);
    else if (i < s2)
      return(-1);
    else
      return(0);
  }
  else
    return(0);
}
  /* hrd_exp_comp_normalized_coefficients() */





struct hrd_exp_type	*hrd_exp_alloc(term_count)
  int	term_count;
{
  struct hrd_exp_type	*he;
  int			flag;

/*        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );

  fprintf(RED_OUT, "\nhrd_exp_alloc: %1d\n", ++flag_hybrid);
  if (flag_hybrid == 77755) {
    fprintf(RED_OUT, "77755 hit\n");
    fflush(RED_OUT);
    for (flag = 1; flag; );
  }
*/
  he = (struct hrd_exp_type *) malloc(sizeof(struct hrd_exp_type));
  he->status = term_count; 
  he->name = NULL; 
  he->hrd_term = (struct hrd_term_type *) malloc(term_count * sizeof(struct hrd_term_type));
  hrd_exp_count++; 
  hrd_term_count = hrd_term_count + term_count; 
  return(he);
}
  /* hrd_exp_alloc() */




void	hrd_exp_free(he)
  struct hrd_exp_type	*he;
{
  hrd_term_count = hrd_term_count - (he->status & MASK_HYBRID_LENGTH); 
  free(he->name); 
  free(he->hrd_term);
  hrd_exp_count--;
  free(he);
}
  /* hrd_exp_free() */



void	hrd_exp_print(he, depth)
  struct hrd_exp_type	*he;
  int			depth;
{
  int	i;

  for (i = depth; i; i--)
    fprintf(RED_OUT, "  ");
  if (!he) {
    fprintf(RED_OUT, "null\n");
    fflush(RED_OUT); 
    return;
  }
  else if (!(he->status & MASK_HYBRID_LENGTH)) {
    fprintf(RED_OUT, "NULL\n");
    fflush(RED_OUT); 
    return;
  }
  if (he->hrd_term[0].coeff == 1)
    fprintf(RED_OUT, "%s", VAR[he->hrd_term[0].var_index].NAME);
  else if (he->hrd_term[0].coeff == -1)
    fprintf(RED_OUT, "-%s", VAR[he->hrd_term[0].var_index].NAME);
  else
    fprintf(RED_OUT, "%1d%s", he->hrd_term[0].coeff, VAR[he->hrd_term[0].var_index].NAME);
  for (i = 1; i < (he->status & MASK_HYBRID_LENGTH); i++) {
    if (he->hrd_term[i].coeff < 0)
      if (he->hrd_term[i].coeff == -1)
        fprintf(RED_OUT, "-%s", VAR[he->hrd_term[i].var_index].NAME);
      else
        fprintf(RED_OUT, "%1d%s", he->hrd_term[i].coeff, VAR[he->hrd_term[i].var_index].NAME);
    else if (he->hrd_term[i].coeff == 1)
      fprintf(RED_OUT, "+%s", VAR[he->hrd_term[i].var_index].NAME);
    else
      fprintf(RED_OUT, "+%1d%s", he->hrd_term[i].coeff, VAR[he->hrd_term[i].var_index].NAME);
  }
  fprintf(RED_OUT, "\n");
  fflush(RED_OUT); 
}
  /* hrd_exp_print() */



void	name_fillin(string, ccp, name)
	char	*string, *name;
	int	*ccp;
{
  int	i;

  for (i = 0; name[i] != '\0'; i++, (*ccp)++)
    string[*ccp] = name[i];
}
  /* name_fillin() */


char	tmp_name[256];
char	*linear_name(term, term_count)
	struct hrd_term_type	*term;
	int			term_count;
{
  int	i, cc;
  char	*name;

  cc = 1;
  if (term[0].coeff == -1)
    cc++;
  else if (term[0].coeff != 1)
    cc = cc + intlen(term[0].coeff);

  cc = cc + strlen(VAR[term[0].var_index].NAME);
/*
  fprintf(RED_OUT, "Linear name with 0:%1d:%s>%1d", term[0].coeff, VAR[term[0].var_index].NAME, cc);
*/
  for (i = 1; i < term_count; i++) {
    if (term[i].coeff < 0)
      if (term[i].coeff == -1)
        cc = cc + 1 + strlen(VAR[term[i].var_index].NAME);
      else
        cc = cc + intlen(term[i].coeff) + strlen(VAR[term[i].var_index].NAME);
    else if (term[i].coeff == 1)
      cc = cc + 1 + strlen(VAR[term[i].var_index].NAME);
    else
      cc = cc + 1 + intlen(term[i].coeff) + strlen(VAR[term[i].var_index].NAME);
/*
    fprintf(RED_OUT, ", %1d:%1d:%s>%1d", i, term[i].coeff, VAR[term[i].var_index].NAME, cc);
*/
  }
/*
  fprintf(RED_OUT, "\ntotal cc = %1d.\n", cc);
*/
  name = (char *) malloc(cc);
  cc = 0;
  if (term[0].coeff == 1)
    sprintf(tmp_name, "%s", VAR[term[0].var_index].NAME);
  else if (term[0].coeff == -1)
    sprintf(tmp_name, "-%s", VAR[term[0].var_index].NAME);
  else
    sprintf(tmp_name, "%1d%s", term[0].coeff, VAR[term[0].var_index].NAME);
  name_fillin(name, &cc, tmp_name);

  for (i = 1; i < term_count; i++) {
    if (term[i].coeff < 0)
      if (term[i].coeff == -1)
        sprintf(tmp_name, "-%s", VAR[term[i].var_index].NAME);
      else
        sprintf(tmp_name, "%1d%s", term[i].coeff, VAR[term[i].var_index].NAME);
    else if (term[i].coeff == 1)
      sprintf(tmp_name, "+%s", VAR[term[i].var_index].NAME);
    else
      sprintf(tmp_name, "+%1d%s", term[i].coeff, VAR[term[i].var_index].NAME);
    name_fillin(name, &cc, tmp_name);
  }
  name[cc] = '\0';
  return(name);
}
/* linear_name() */




struct hrd_exp_type	*hrd_exp_fillin(he, flag_static)
	struct hrd_exp_type	*he;
	int			flag_static;
{
  struct hrd_exp_type	*the;
  char			*name;

  if ((GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
    == FLAG_HYBRID_ENCODING_NORMALIZED_STRING
  )
    he->name = name = linear_name(he->hrd_term, he->status & MASK_HYBRID_LENGTH);
  the = hrd_exp_share(he);
  if (the == he) {
    if ((GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
      != FLAG_HYBRID_ENCODING_NORMALIZED_STRING
    )
      he->name = linear_name(he->hrd_term, he->status & MASK_HYBRID_LENGTH);
    he->status = (hybrid_variable_index(he) * MASK_HYBRID_VI_BASE)
	       | (he->status & ~MASK_HYBRID_LIFTED_VI);
    he->status = he->status | flag_static;
/*
      fprintf(RED_OUT, "A new static hrd expression %s: %x\n", newhe->name, newhe->status);
*/
/*
    else
      fprintf(RED_OUT, "A new non-static hrd expression %s: %x\n", newhe->name, newhe->status);
*/
  }
  else if (
    (GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
    == FLAG_HYBRID_ENCODING_NORMALIZED_STRING
  )
    free(name);
/*    print_23tree(hrd_exp_tree, 0, hrd_exp_print);
*/
  return(the);
}
  /* hrd_exp_fillin() */




#define	FLAG_DELTA_GENERATED_PATTERN_FALSE	0
#define	FLAG_DELTA_GENERATED_PATTERN_FOUND	-1

int count_hrd_exp_new = 0; 

struct hrd_exp_type	*hrd_exp_new(tlist, tc, lcmptr, gcdptr)
	struct hrd_term_link_type	*tlist;
	int				tc, *lcmptr, *gcdptr;
{
  struct hrd_exp_type	*newhe, *the;
  int			ti, g, flag_static;
  char			*name;

  if (tc == 0)
    return(NULL);
/*
  fprintf(RED_OUT, 
    "\n=====[Before hrd_exp_new(), %1d]==================================\n", 
    ++count_hrd_exp_new
  );
  if (count_hrd_exp_new == 17) { 
    fprintf(RED_OUT, "Caught ahead!\n"); 	
  } 
  fflush(RED_OUT); 
*/ 
/*
  for (; count_hrd_exp_new == 72; ); 
  print_23tree(hrd_exp_tree, 0, hrd_exp_print);
*/
  newhe = hrd_exp_alloc(tc);
  *lcmptr = get_list_denominator_multiple(tlist);
  *gcdptr = get_list_numerator_factor(tlist);
  g = gcd(*lcmptr, *gcdptr);
  *lcmptr = *lcmptr / g;
  *gcdptr = *gcdptr / g;
  g = FLAG_DELTA_GENERATED_PATTERN_FALSE;

  flag_static = TYPE_TRUE;
  for (ti = 0; tlist; ti++, tlist = tlist->next_hrd_term_link) {
    newhe->hrd_term[ti].var_index = tlist->var_index;
    newhe->hrd_term[ti].coeff = tlist->coeff_numerator;
    if (   g != FLAG_DELTA_GENERATED_PATTERN_FOUND
	&& tlist->var_index == g+1
	&& (VAR[tlist->var_index].STATUS & FLAG_VAR_PRIMED)
	)
      g = FLAG_DELTA_GENERATED_PATTERN_FOUND;
    else
      g = tlist->var_index;
    if (   VAR[tlist->var_index].TYPE != TYPE_DENSE 
        || !(VAR[tlist->var_index].STATUS & FLAG_VAR_STATIC)
        ){
/*
      fprintf(RED_OUT, "a non-static %s\n", VAR[tlist->var_index].NAME);
*/
      flag_static = TYPE_FALSE;
    }
  }
  if ((GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
    == FLAG_HYBRID_ENCODING_NORMALIZED_STRING
  )
    newhe->name = name = linear_name(newhe->hrd_term, tc);
  the = hrd_exp_share(newhe);
  if (the == newhe) {
    if ((GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
      != FLAG_HYBRID_ENCODING_NORMALIZED_STRING)
      newhe->name = linear_name(newhe->hrd_term, tc);
    newhe->status = (hybrid_variable_index(newhe) * MASK_HYBRID_VI_BASE)
		  | (newhe->status & ~MASK_HYBRID_LIFTED_VI);

    if (g == FLAG_DELTA_GENERATED_PATTERN_FOUND)
      newhe->status = newhe->status | FLAG_DELTA_GENERATED;
    if (flag_static) {
      newhe->status = newhe->status | FLAG_HRD_EXP_STATIC;
/*
      fprintf(RED_OUT, "A new static hrd expression %s: %x\n", newhe->name, newhe->status);
*/
    }
/*
    else
      fprintf(RED_OUT, "A new non-static hrd expression %s: %x\n", newhe->name, newhe->status);
*/
  }
  else if ((GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) 
    == FLAG_HYBRID_ENCODING_NORMALIZED_STRING
  )
    free(name);
/*
  fprintf(RED_OUT, "Generating a new hrd exp: "); 
  hrd_exp_print(the, 0); 
*/
/*    print_23tree(hrd_exp_tree, 0, hrd_exp_print);
*/
  return(the);
}
  /* hrd_exp_new() */




struct hrd_exp_type	*hrd_exp_array_new(vip, coeffp, tc, lcmptr, gcdptr)
	int				*vip, *coeffp, tc, *lcmptr, *gcdptr;
{
  struct hrd_exp_type		*newhe, *the;
  int				ti, tip, g, flag_static, 
				new_tc, redundancy_count, 
				copy_count, copy_dst_start, copy_src_start;
  char				*name;
  struct hrd_term_link_type	dummy_head, *tail, *t;

  if (tc == 0)
    return(NULL);

  /* sort according to the variable indices. */     
  for (ti = 0; ti < tc; ti++) 
    for (tip = ti+1; tip < tc; tip++) 
      if (vip[ti] > vip[tip]) { 
        g = vip[ti]; vip[ti] = vip[tip]; vip[tip] = g; 
        g = coeffp[ti]; coeffp[ti] = coeffp[tip]; coeffp[tip] = g; 
      } 
  /* merge redundant variable indices. */ 
  for (ti = 0; ti < tc-1; ti++) {
    for (redundancy_count = 0, tip = ti+1; tip < tc; tip++) 
      if (vip[ti] == vip[ti+1]) { 
        coeffp[ti] = coeffp[ti] + coeffp[tip]; 
        redundancy_count++; 
      } 
    /* check if there is any redundancy */ 
    if (redundancy_count == 0) 
      continue; 
    /* check if the redundancy makes the coefficients sum up to zero. */  
    if (coeffp[ti] == 0) { 
      redundancy_count++; 
      copy_dst_start = ti; 
      ti--; /* since ti is to be removed. */ 
    }
    else 
      copy_dst_start = ti+1; 
    copy_src_start = tip; 
    
    /* move the tail to cover the redundant elements. */ 
    for (; copy_src_start < tc; copy_dst_start++, copy_src_start++) { 
      vip[copy_dst_start] = vip[copy_src_start]; 
      coeffp[copy_dst_start] = coeffp[copy_src_start];       	
    } 
    tc = tc - redundancy_count; 
  } 
  
  for (dummy_head.next_hrd_term_link = NULL, tail = &dummy_head, ti = 0; 
       ti < tc; 
       ti++
       ) { 
    t = (struct hrd_term_link_type *) malloc(sizeof(struct hrd_term_link_type)); 
    t->var_index = vip[ti];
    t->coeff_numerator = coeffp[ti]; 
    t->coeff_denominator = 1; 
    t->next_hrd_term_link = NULL; 
    tail->next_hrd_term_link = t; 
    tail = t; 
  } 

  return(hrd_exp_new(dummy_head.next_hrd_term_link, tc, lcmptr, gcdptr)); 
}
  /* hrd_exp_array_new() */





init_hybrid_management() {
  int 				exp, ci, tlcm, tgcd, vi;
  struct hrd_term_link_type	thead;
  struct hrd_exp_type		*newhe;

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) != FLAG_SYSTEM_HYBRID)
    return;

  flag_hybrid = status_hybrid = position_hybrid = 0;

  hchild_count = 0;
  hfchild_count = 0;
  hchild_link_count = 0;
  hfchild_link_count = 0;
  hrd_exp_count = 0;
  hrd_term_count = 0;
  
  #if RED_DEBUG_HYBRID_MODE
  fprintf(RED_OUT, "hybrid variable encoding:%x/%x\n", 
    GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING, 
    MASK_HYBRID_ENCODING
  ); 
  fflush(RED_OUT); 
  #endif 
  
  switch (GSTATUS[INDEX_HYBRID_ENCODING] & MASK_HYBRID_ENCODING) {
  case FLAG_HYBRID_ENCODING_NORMALIZED_STRING:
    HRD_EXP_COMP = hrd_exp_comp_string;
    break;
  case FLAG_HYBRID_ENCODING_NORMALIZED_MAGNITUDES:
    HRD_EXP_COMP = hrd_exp_comp_normalized_magnitudes;
    break;
  case FLAG_HYBRID_ENCODING_NORMALIZED_COEFFICIENTS:
    HRD_EXP_COMP = hrd_exp_comp_normalized_coefficients;
    break;
  }

  for (exp = 1; exp <= VARIABLE_COUNT+1; exp = exp*2) ;
  MASK_HYBRID_VI_BASE = exp;
  MASK_HYBRID_LENGTH = exp-1;
  for (MASK_HYBRID_LIFTED_VI = exp, exp = 1;
       exp <= VARIABLE_COUNT+1;
       exp = exp*2, MASK_HYBRID_LIFTED_VI = MASK_HYBRID_LIFTED_VI * 2
       ) ;
  FLAG_HEXP_VAR_IN_MODULES = exp * exp * 2; 
  
  FLAG_DELTA_GENERATED = MASK_HYBRID_LIFTED_VI;
  FLAG_HRD_EXP_STATIC = 2*FLAG_DELTA_GENERATED;
  FLAG_WITH_PRIMED_VARIABLE = 4*FLAG_DELTA_GENERATED; 
  FLAG_LOCAL_HYBRID_VARIABLES = 8*FLAG_DELTA_GENERATED; 
  MASK_HYBRID_LIFTED_VI = (MASK_HYBRID_LIFTED_VI - 1) & ~MASK_HYBRID_LENGTH;

  #if RED_DEBUG_HYBRID_MODE
  fprintf(RED_OUT, "==[HYBRID CONSTANTS]==========================\n");
  fprintf(RED_OUT, "  MASK_HYBRID_LENGTH:        %x\n", MASK_HYBRID_LENGTH);
  fprintf(RED_OUT, "  MASK_HYBRID_VI_BASE:       %x\n", MASK_HYBRID_VI_BASE);
  fprintf(RED_OUT, "  MASK_HYBRID_LIFTED_VI:     %x\n", MASK_HYBRID_LIFTED_VI);
  fprintf(RED_OUT, "  FLAG_DELTA_GENERATED:      %x\n", FLAG_DELTA_GENERATED);
  fprintf(RED_OUT, "  FLAG_HRD_EXP_STATIC:       %x\n", FLAG_HRD_EXP_STATIC);
  fprintf(RED_OUT, "  FLAG_WITH_PRIMED_VARIABLE: %x\n\n", FLAG_WITH_PRIMED_VARIABLE);
  #endif 

  VRATE = (struct variable_rate_type *) malloc(VARIABLE_COUNT*sizeof(struct variable_rate_type));
  for (vi = 8; vi < VARIABLE_COUNT; vi++)
    if (   VAR[vi].TYPE == TYPE_DENSE
	&& !(VAR[vi].STATUS & FLAG_VAR_PRIMED)
	) {
      newhe = hrd_exp_alloc(2);
      newhe->hrd_term[0].var_index = vi;
      newhe->hrd_term[0].coeff = 1;
      newhe->hrd_term[1].var_index = VAR[vi].PRIMED_VI;
      newhe->hrd_term[1].coeff = -1;
      newhe->name = linear_name(newhe->hrd_term, 2);
      newhe = hrd_exp_share(newhe);
      switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
        & MASK_DISCRETE_DENSE_INTERLEAVING
      ) { 
      case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING: 
      case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING: 
        newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI)
		      | (  variable_index[TYPE_HRD][VAR[vi].PROC_INDEX][0]
		         * MASK_HYBRID_VI_BASE
		         );
        break; 
      case FLAG_DISCRETE_DENSE_BOTTOM: 
        newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI)
		      | (  variable_index[TYPE_HRD][PROCESS_COUNT][0]
		         * MASK_HYBRID_VI_BASE
		         );
	break; 
      } 
      
      VRATE[vi].umprimed_primed_hrd_exp = newhe;
      newhe->status = newhe->status | FLAG_DELTA_GENERATED;

      newhe = hrd_exp_alloc(2);
      newhe->hrd_term[0].var_index = vi;
      newhe->hrd_term[0].coeff = -1;
      newhe->hrd_term[1].var_index = VAR[vi].PRIMED_VI;
      newhe->hrd_term[1].coeff = 1;
      newhe->name = linear_name(newhe->hrd_term, 2);
      newhe = hrd_exp_share(newhe);
      switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
        & MASK_DISCRETE_DENSE_INTERLEAVING
      ) { 
      case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING: 
      case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING: 
        newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI)
		      | (  variable_index[TYPE_HRD][VAR[vi].PROC_INDEX][0]
		         * MASK_HYBRID_VI_BASE
		         );
        break; 
      case FLAG_DISCRETE_DENSE_BOTTOM: 
        newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI)
		      | (  variable_index[TYPE_HRD][PROCESS_COUNT][0]
		         * MASK_HYBRID_VI_BASE
		         ); 
	break; 
      } 

      VRATE[vi].primed_umprimed_hrd_exp = newhe;
      newhe->status = newhe->status | FLAG_DELTA_GENERATED;
    }

  w_hybrid_vi = (int *) malloc((DENSE_COUNT+CLOCK_COUNT) * sizeof(int));
  w_hybrid_coeff_numerator = (int *) malloc((DENSE_COUNT+CLOCK_COUNT) * sizeof(int));
  w_hybrid_coeff_denominator = (int *) malloc((DENSE_COUNT+CLOCK_COUNT) * sizeof(int));

  if ((GSTATUS[INDEX_SYSTEM_TYPE] & MASK_SYSTEM_TYPE) == FLAG_SYSTEM_HYBRID) {
    HE_CLOCK_LB = (struct hrd_exp_type **) malloc(CLOCK_COUNT * sizeof(struct hrd_exp_type *));
    for (ci = 1; ci < CLOCK_COUNT; ci++) {
      thead.var_index = CLOCK[ci];
      thead.coeff_numerator = -1;
      thead.coeff_denominator = 1;
      thead.next_hrd_term_link = NULL;

      HE_CLOCK_LB[ci] = hrd_exp_new(&thead, 1, &tlcm, &tgcd);
    }
    for (vi = 0; vi < VARIABLE_COUNT; vi++) {
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, " >> vi:%1d:%s\n", vi, VAR[vi].NAME); 
      #endif 
      
      if (!(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
        switch (VAR[vi].TYPE) {
        case TYPE_CLOCK:
          VAR[vi].U.CLOCK.HE_LB = hrd_exp_alloc(1);
	  VAR[vi].U.CLOCK.HE_LB->hrd_term[0].var_index = vi;
	  VAR[vi].U.CLOCK.HE_LB->hrd_term[0].coeff = -1;
	  VAR[vi].U.CLOCK.HE_LB = hrd_exp_fillin(VAR[vi].U.CLOCK.HE_LB, 0);
          VAR[vi].U.CLOCK.HE_UB = hrd_exp_alloc(1);
	  VAR[vi].U.CLOCK.HE_UB->hrd_term[0].var_index = vi;
	  VAR[vi].U.CLOCK.HE_UB->hrd_term[0].coeff = 1;
	  VAR[vi].U.CLOCK.HE_UB = hrd_exp_fillin(VAR[vi].U.CLOCK.HE_UB, 0);
	  break;
        case TYPE_DENSE:
          VAR[vi].U.DENSE.HE_LB = hrd_exp_alloc(1);
	  VAR[vi].U.DENSE.HE_LB->hrd_term[0].var_index = vi;
	  VAR[vi].U.DENSE.HE_LB->hrd_term[0].coeff = -1;
	  if (VAR[vi].PROC_INDEX)
	    VAR[vi].U.DENSE.HE_LB = hrd_exp_fillin(VAR[vi].U.DENSE.HE_LB, 0);
	  else
	    VAR[vi].U.DENSE.HE_LB = hrd_exp_fillin(VAR[vi].U.DENSE.HE_LB, FLAG_HRD_EXP_STATIC);
          VAR[vi].U.DENSE.HE_UB = hrd_exp_alloc(1);
	  VAR[vi].U.DENSE.HE_UB->hrd_term[0].var_index = vi;
	  VAR[vi].U.DENSE.HE_UB->hrd_term[0].coeff = 1;
	  if (VAR[vi].PROC_INDEX)
	    VAR[vi].U.DENSE.HE_UB = hrd_exp_fillin(VAR[vi].U.DENSE.HE_UB, 0);
	  else
	    VAR[vi].U.DENSE.HE_UB = hrd_exp_fillin(VAR[vi].U.DENSE.HE_UB, FLAG_HRD_EXP_STATIC);
          break;
        }
      }
    }
  }

  HRD_EXP_NULL = hrd_exp_new(NULL, 0, &tlcm, &tgcd);

  MG = (int **) malloc(2*(DENSE_COUNT + CLOCK_COUNT)*sizeof(int *));
  for (ci = 0; ci < 2*(DENSE_COUNT+CLOCK_COUNT); ci++)
    MG[ci] = (int *) malloc(10*sizeof(int));
  MG_COL_SIGNIFICANT = (int *) malloc((DENSE_COUNT+CLOCK_COUNT)*sizeof(int));
/*
  test_Gaussian_solution();
*/
  flag_hybrid = 0;

  BITBASE = (int *) malloc(5*sizeof(int));
  BITLEN = (int *) malloc(5*sizeof(int));
  BITBASE[4] = 64*1024;
  BITLEN[4] = 16;
  BITBASE[3] = 256;
  BITLEN[3] = 8;
  BITBASE[2] = 16;
  BITLEN[2] = 4;
  BITBASE[1] = 4;
  BITLEN[1] = 2;
  BITBASE[0] = 2;
  BITLEN[0] = 1;
/*
  ci = HYBRID_POS_BOUND;
  fprintf(RED_OUT, "\nHybrid rational overflow test multiplication %1d=%1d*%1d.\n",
  	  ci * ci, ci, ci
	  );
  fflush(RED_OUT);
  exit(0);
*/
}
  /* init_hybrid_management() */



struct red_type	*hrd_lone_subtree(d, vi, hrd_exp, ub_numerator, ub_denominator)
	struct red_type		*d;
	int			vi, ub_numerator, ub_denominator;
	struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*newd;
  int			bd;

  if (VAR[vi].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "Error: A non hybrid inequality in red_lone_ineq_subtree(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    bk(0);
  }
  else if (   d != NORM_FALSE
	   && d != NORM_NO_RESTRICTION
	   && (   vi > d->var_index
	       /* || (vi == d->var_index && HRD_EXP_COMP(d->u.hrd.hrd_exp, hrd_exp) <= 0) */
	       )
	   ) {
    fprintf(RED_OUT, "Error: hybrid lone subtree violating variable-ordering.\n");
    fflush(RED_OUT);
    for (bd = TYPE_TRUE; bd; );
  }
  if (d == NORM_FALSE)
    return(d);

  bd = ub_numerator / ub_denominator;
  if (bd == HYBRID_POS_INFINITY) {
    return(d);
  }
  else if (bd > HYBRID_POS_INFINITY) {
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hrd_lone_subtree().\n", ub_numerator, ub_denominator);
    fflush(RED_OUT);
    exit(0);
  }
  else if (bd < HYBRID_NEG_INFINITY) {
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hrd_lone_subtree().\n", ub_numerator, ub_denominator);
    fflush(RED_OUT);
    exit(0);
  }
  newd = red_alloc(vi);
  newd->u.hrd.hrd_exp = hrd_exp;
  newd->u.hrd.child_count = 1;
  hchild_count++;
  newd->u.hrd.arc = (struct hrd_child_type *) malloc(sizeof(struct hrd_child_type));
  newd->u.hrd.arc[0].child = d;
  newd->u.hrd.arc[0].ub_numerator = ub_numerator;
  newd->u.hrd.arc[0].ub_denominator = ub_denominator;
  return(red_share(newd));
}
/* hrd_lone_subtree() */





int	APC_VI;



struct hrd_exp_type	*hrd_exp_switch_vi(he, vi, vj)
  struct hrd_exp_type	*he;
  int			vi, vj;
{
  int			ti, len, *via, *coeffa, dx, dy;
  struct hrd_exp_type	*newhe;

  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++)
    if (   vi == he->hrd_term[ti].var_index
        || vj == he->hrd_term[ti].var_index
        )
      break;

  if (ti >= len)
    return(he);

  for (ti = 0; ti < len; ti++) {
    if (he->hrd_term[ti].var_index == vi)
      w_hybrid_vi[ti] = vj;
    else if (he->hrd_term[ti].var_index == vj)
      w_hybrid_vi[ti] = vi;
    else
      w_hybrid_vi[ti] = he->hrd_term[ti].var_index;

    w_hybrid_coeff_numerator[ti] = he->hrd_term[ti].coeff;
  }
  newhe = hrd_exp_array_new(
    w_hybrid_vi, w_hybrid_coeff_numerator, 
    len, &dx, &dy
  ); 
  return(newhe);
}
  /* hrd_exp_switch_vi() */



struct hrd_exp_type	*hrd_exp_given_prime_replace(he, vi)
	struct hrd_exp_type	*he;
	int			vi;
{
  int			ti, len;
  struct hrd_exp_type	*newhe;

  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++)
    if (vi == he->hrd_term[ti].var_index)
      break;

  if (ti >= len)
    return(NULL);

  newhe = hrd_exp_alloc(len);
  for (ti = 0; ti < len; ti++) {
    if (he->hrd_term[ti].var_index == vi)
      newhe->hrd_term[ti].var_index 
      = VAR[newhe->hrd_term[ti].var_index].PRIMED_VI /* it was vi+1*/;
    else
      newhe->hrd_term[ti].var_index = he->hrd_term[ti].var_index;

    newhe->hrd_term[ti].coeff = he->hrd_term[ti].coeff;
  }
  newhe->name = linear_name(newhe->hrd_term, len);
  newhe = hrd_exp_share(newhe);
/*
  newhe->status = newhe->status | FLAG_DELTA_GENERATED;
*/
  newhe->status = he->status;
  return(newhe);
}
  /* hrd_exp_given_prime_replace() */




struct red_type	*rec_hybrid_add_primed_constraints(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  struct hrd_exp_type		*newhe;
  struct ddd_child_type		*ic;
  int				ci, dn, dd;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(OP_HYBRID_ADD_PRIMED_CONSTRAINTS, d, 
    (struct red_type *) APC_VI
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    newhe = hrd_exp_given_prime_replace(d->u.hrd.hrd_exp, APC_VI);
    if (newhe) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_add_primed_constraints(d->u.hrd.arc[ci].child);
	conj = hrd_lone_subtree(conj, d->var_index, newhe,
	  d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
	conj = hrd_lone_subtree(conj, d->var_index, d->u.hrd.hrd_exp,
	  d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
	result = red_bop(OR, result, conj);
      }
    }
    else
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_add_primed_constraints(d->u.hrd.arc[ci].child);
	conj = hrd_lone_subtree(conj, d->var_index, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
	result = red_bop(OR, result, conj);
      }

    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_lone_subtree(
        rec_hybrid_add_primed_constraints(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_lone_subtree(
        rec_hybrid_add_primed_constraints(d->u.dfdd.arc[ci].child),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX == VAR[APC_VI].PROC_INDEX
	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      int	mi, ri, vi, pi;

      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    pi = VAR[d->var_index].PROC_INDEX;
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (VAR[vi].PROC_INDEX)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    if (vi == APC_VI) {
	      if (   MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
		     != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
		  || MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
		     != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
		  )
	        conj = rec_hybrid_add_primed_constraints(d->u.ddd.arc[ci].child);
	      else
	        conj = d->u.ddd.arc[ci].child;
	      break;
	    }
	  }
	  if (ri >= MODE[mi].rate_spec_count) {
	    conj = d->u.ddd.arc[ci].child;
/*
	    fprintf(RED_OUT, "\nError ....\n");
	    bk(); 
*/
	  }
	  conj = ddd_lone_subtree(conj, d->var_index, mi, mi);
	  result = red_bop(OR, result, conj);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_lone_subtree(rec_hybrid_add_primed_constraints(d->u.ddd.arc[ci].child),
				     d->var_index, d->u.ddd.arc[ci].lower_bound,
				     d->u.ddd.arc[ci].upper_bound
				     );
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_add_primed_constraints() */










int	hybrid_variable_index(he)
  struct hrd_exp_type	*he;
{
  int 	pi, ti;
/*
  if (he == (struct hrd_exp_type *) 0x8157778) {
    fprintf(RED_OUT, "\nCaught:\n");
    fflush(RED_OUT);
    for (pi = 1; pi; );
  }
*/
  switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
    & MASK_DISCRETE_DENSE_INTERLEAVING
  ) { 
  case FLAG_DISCRETE_DENSE_BOTTOM: 
    return(variable_index[TYPE_HRD][PROCESS_COUNT][0]);
  case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING: 
  case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING: 
    for (pi = 0, ti = 0; ti < (he->status & MASK_HYBRID_LENGTH); ti++) {
      if (pi < VAR[he->hrd_term[ti].var_index].PROC_INDEX)
        pi = VAR[he->hrd_term[ti].var_index].PROC_INDEX;
    }
    return (variable_index[TYPE_HRD][pi][0]);
  } 
}
  /* hybrid_variable_index() */



struct red_type	*hrd_atom(hrd_exp, ub_numerator, ub_denominator)
	struct hrd_exp_type	*hrd_exp;
	int			ub_numerator, ub_denominator;
{
  struct red_type	*d;
  struct hrd_child_type	*mhc, *phc;
  int			vi, pi, ti;

  ti = ub_numerator / ub_denominator;
  if (ti == HYBRID_POS_INFINITY) {
    return(NORM_NO_RESTRICTION);
  }
  else if (ti > HYBRID_POS_INFINITY) {
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hrd_atom().\n", ub_numerator, ub_denominator);
    bk(); 
  }
  else if (ti < HYBRID_NEG_INFINITY) {
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hrd_atom().\n", ub_numerator, ub_denominator);
    bk(); 
  }
  vi = (hrd_exp->status & MASK_HYBRID_LIFTED_VI) / MASK_HYBRID_VI_BASE;  
  d = red_alloc(vi);
    /*
      lb = ub;
    */
  d->u.hrd.child_count = 1;
  d->u.hrd.hrd_exp = hrd_exp;
  d->u.hrd.arc = (struct hrd_child_type *) malloc(sizeof(struct hrd_child_type));
  hchild_count = hchild_count + d->u.hrd.child_count;
  d->u.hrd.arc[0].ub_numerator = ub_numerator;
  d->u.hrd.arc[0].ub_denominator = ub_denominator;
  d->u.hrd.arc[0].child = NORM_TRUE;

  return(red_share(d));
/*
  red_print_graph(new);
  fflush(RED_OUT);
*/
}
  /* hrd_atom() */





int	hrd_comp(hx, hcx, hy, hcy)
  struct hrd_type	*hx, *hy;
  int			hcx, hcy;
{
  int	ci;

  if (ci = HRD_EXP_COMP(hx->hrd_exp, hy->hrd_exp))
    return(ci);
  else if (ci = hcx - hcy)
    return(ci);
  else for (ci = 0; ci < hcx; ci++)
    if (hx->arc[ci].ub_numerator < hy->arc[ci].ub_numerator)
      return(-1);
    else if (hx->arc[ci].ub_numerator > hy->arc[ci].ub_numerator)
      return(1);
    else if (hx->arc[ci].ub_denominator < hy->arc[ci].ub_denominator)
      return(-1);
    else if (hx->arc[ci].ub_denominator > hy->arc[ci].ub_denominator)
      return(1);
    else if (hx->arc[ci].child < hy->arc[ci].child)
      return(-1);
    else if (hx->arc[ci].child > hy->arc[ci].child)
      return(1);

  return(0);
}
  /* hrd_comp() */


int	hrd_term_coeff_extract(he, vi)
	struct hrd_exp_type	*he;
	int			vi;
{
  int 	ti;

  for (ti = 0; ti < (he->status & MASK_HYBRID_LENGTH); ti++)
    if (he->hrd_term[ti].var_index == vi)
      return(he->hrd_term[ti].coeff);
    else if (he->hrd_term[ti].var_index > vi)
      return(0);
  return(0);
}
/* hrd_term_coeff_extract() */






int	hrd_exp_converse_test(hex, dy)
	struct hrd_exp_type	*hex;
	struct red_type		*dy;
{
  int	i;

/*
  fprintf(RED_OUT, "\n--(hrd_exp_converse_test)-----------------\n");
*/
  if (   VAR[dy->var_index].TYPE != TYPE_HRD
      || (hex->status & MASK_HYBRID_LENGTH) != (dy->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)
      ) {
/*
    fprintf(RED_OUT, "comp = %1d\n", FALSE);
    fflush(RED_OUT);
*/
    return(TYPE_FALSE);
  }
  else {
/*
    hrd_exp_print(hex, 0);
    hrd_exp_print(dy->u.hrd.hrd_exp, 0);
*/
    for (i = 0; i < (hex->status & MASK_HYBRID_LENGTH); i++) {
      if (hex->hrd_term[i].var_index != dy->u.hrd.hrd_exp->hrd_term[i].var_index) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
      else if (hex->hrd_term[i].coeff + dy->u.hrd.hrd_exp->hrd_term[i].coeff) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
    }
/*
    fprintf(RED_OUT, "comp = %1d\n", TYPE_TRUE);
    fflush(RED_OUT);
*/
    return(TYPE_TRUE);
  }
}
/* hrd_exp_converse_test() */



int	hexp_converse_test(hex, hey)
	struct hrd_exp_type	*hex, *hey;
{
  int	i;

/*
  fprintf(RED_OUT, "\n--(hexp_converse_test)-----------------\n");
  hrd_exp_print(hex, 0);
  hrd_exp_print(hey, 0);
*/
  if ((hex->status & MASK_HYBRID_LENGTH) != (hey->status & MASK_HYBRID_LENGTH)) {
/*
    fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
    fflush(RED_OUT);
*/
    return(TYPE_FALSE);
  }
  else {
    for (i = 0; i < (hex->status & MASK_HYBRID_LENGTH); i++) {
      if (hex->hrd_term[i].var_index != hey->hrd_term[i].var_index) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
      else if (hex->hrd_term[i].coeff + hey->hrd_term[i].coeff) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
    }
/*
    fprintf(RED_OUT, "comp = %1d\n", TYPE_TRUE);
    fflush(RED_OUT);
*/
    return(TYPE_TRUE);
  }
}
/* hexp_converse_test() */



int	hrd_converse_test(dx, dy)
	struct red_type	*dx, *dy;
{
  int	i;

/*
  fprintf(RED_OUT, "\n--(hrd_converse_test)-----------------\n");
*/
  if (   VAR[dx->var_index].TYPE != TYPE_HRD
      || VAR[dy->var_index].TYPE != TYPE_HRD
      || (dx->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)
	 != (dy->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH)
      ) {
/*
    fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
    fflush(RED_OUT);
*/
    return(TYPE_FALSE);
  }
  else {
/*
    hrd_exp_print(dx->u.hrd.hrd_exp, 0);
    hrd_exp_print(dy->u.hrd.hrd_exp, 0);
*/
    for (i = 0; i < (dx->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH); i++) {
      if (dx->u.hrd.hrd_exp->hrd_term[i].var_index != dy->u.hrd.hrd_exp->hrd_term[i].var_index) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
      else if (dx->u.hrd.hrd_exp->hrd_term[i].coeff + dy->u.hrd.hrd_exp->hrd_term[i].coeff) {
/*
        fprintf(RED_OUT, "comp = %1d\n", TYPE_FALSE);
	fflush(RED_OUT);
*/
        return(TYPE_FALSE);
      }
    }
/*
    fprintf(RED_OUT, "comp = %1d\n", TYPE_TRUE);
    fflush(RED_OUT);
*/
    return(TYPE_TRUE);
  }
}
/* hrd_converse_test() */






#define	NULL_VARIABLE	-1
int count_rec_hybrid_ineq = 0; 


struct red_type *rec_hybrid_ineq(ti)
     int	ti;
{
  int				g, ppi, vi, tc, ci, tlcm, tgcd, vpi, 
				offset_numerator, offset_denominator;
  struct red_type		*result, *leq_hybrid, *geq_hybrid, *less_hybrid, *greater_hybrid,
				*rconj, *rchild;
  struct hrd_term_link_type	*t, *tlist;
  struct hrd_exp_type		*newhe;

  if (ti == W_TERM_COUNT) {
    /* now we have reached decision on all term variables
     * now we have to construct the HRD atom
     */
    /* initialize the term coeffs and variables to the working arrays
    */
    /* sort the sequence of the variables in the term array
     */
    switch (W_HYBRID_INEQ_TYPE) {
    case LEQ:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], w_hybrid_coeff_numerator[ti],
          w_hybrid_coeff_denominator[ti], &tc
        );
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      return (hrd_atom(newhe, 2*offset_numerator/g, offset_denominator/g));

    case LESS:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], w_hybrid_coeff_numerator[ti],
	  w_hybrid_coeff_denominator[ti], &tc
	);
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      return (hrd_atom(newhe,(2*offset_numerator/g)-1, offset_denominator/g));

    case EQ:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], w_hybrid_coeff_numerator[ti],
	  w_hybrid_coeff_denominator[ti], &tc
	);
      }
      /* do leq_hybrid */
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      leq_hybrid = hrd_atom(newhe, (2*offset_numerator/g), offset_denominator/g);
      /* do guq_hybrid */
      for (t = tlist; t; t = t->next_hrd_term_link) {
        t->coeff_numerator = -1 * t->coeff_numerator;
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      geq_hybrid = hrd_atom(newhe, (-2*offset_numerator/g), offset_denominator/g);
      return(red_bop(AND, leq_hybrid, geq_hybrid));
    case NEQ:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], w_hybrid_coeff_numerator[ti],
	  w_hybrid_coeff_denominator[ti], &tc
	);
      }
      /* do leq_hybrid */
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      less_hybrid = hrd_atom(newhe, (2*offset_numerator/g)-1, offset_denominator/g);
      /* do guq_hybrid */
      for (t = tlist; t; t = t->next_hrd_term_link) {
        t->coeff_numerator = -1 * t->coeff_numerator;
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      greater_hybrid = hrd_atom(newhe,(-2*offset_numerator/g)-1, offset_denominator/g);
      return(red_bop(OR, less_hybrid, greater_hybrid));
    case GREATER:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], -1*w_hybrid_coeff_numerator[ti],
	  w_hybrid_coeff_denominator[ti], &tc
	);
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      return(hrd_atom(newhe, (-2*offset_numerator/g)-1, offset_denominator/g));

    case GEQ:
      for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--) {
        tlist = hrd_term_insert(tlist, 
          w_hybrid_vi[ti], -1*w_hybrid_coeff_numerator[ti],
	  w_hybrid_coeff_denominator[ti], &tc
	);
      }
      newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      offset_numerator = tlcm * w_hybrid_offset_numerator;
      offset_denominator = w_hybrid_offset_denominator * tgcd;
      g = gcd(offset_numerator, offset_denominator);
      return(hrd_atom(newhe, (-2*offset_numerator/g), offset_denominator/g));
    }
  }
/* 
  else if (W_TERM[ti].operand->u.atom.indirect_count == 0) {
  	fprintf(RED_OUT, "count rec_hybrid_ineq:%1d, ti=%1d\n", ++count_rec_hybrid_ineq, ti); 
  	fflush(RED_OUT); 
  	for (; count_rec_hybrid_ineq == 83; ) ; 
    w_hybrid_vi[ti] = get_variable_index(W_TERM[ti].operand, W_PI); 
    return(rec_hybrid_ineq(ti+1));
  }
*/
  vi = W_TERM[ti].operand->u.atom.var_index; 
  rconj = red_operand_indirection(W_TERM[ti].operand, W_PI); 
  result = NORM_FALSE;
  for (ci = 0; ci < rconj->u.ddd.child_count; ci++) {
    rchild = rconj->u.ddd.arc[ci].child;
    if (rchild == NORM_FALSE) 
      continue; 
    for (vi = rconj->u.ddd.arc[ci].lower_bound; 
         vi <= rconj->u.ddd.arc[ci].upper_bound; 
         vi++
         ) { 
      w_hybrid_vi[ti] = vi; 

      rchild = red_bop(AND, rchild, rec_hybrid_ineq(ti+1));
      result = red_bop(OR, result, rchild);
  } }
  return(result);
}
/* rec_hybrid_ineq() */



struct red_type	*red_hybrid_ineq(
  struct ps_exp_type	*psub, 
  int			pi 
) {
  struct red_type	*result;
  int			i;
/*
  	  fprintf(RED_OUT, "count rec_hybrid_ineq:%1d\n", ++count_rec_hybrid_ineq); 
  	  fflush(RED_OUT); 
  	  for (; count_rec_hybrid_ineq == 6; ) ; 
*/
  rec_get_rationals(psub->u.ineq.offset, &w_hybrid_offset_numerator, &w_hybrid_offset_denominator);
  if (psub->u.ineq.term_count == 0) {
    switch (psub->type) {
    case LEQ:
      if (0 <= w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    case LESS:
      if (0 < w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    case EQ:
      if (0 == w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    case NEQ:
      if (0 != w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    case GREATER:
      if (0 > w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    case GEQ:
      if (0 >= w_hybrid_offset_numerator)
        return (NORM_NO_RESTRICTION);
      else
        return(NORM_FALSE);
    }
  }
  W_TERM_COUNT = psub->u.ineq.term_count;
  W_TERM = psub->u.ineq.term;
  W_HYBRID_INEQ_TYPE = psub->type;
  W_PI = pi;
  for (i = 0 ; i <W_TERM_COUNT;i++)
    rec_get_rationals(psub->u.ineq.term[i].coeff,&(w_hybrid_coeff_numerator[i]),
                     &(w_hybrid_coeff_denominator[i])
                     );
/*
  fprintf(RED_OUT, "red_hybrid_ineq() for process %1d:\n", pi);
  print_parse_subformula_structure(psub, 0);
  fprintf(RED_OUT, "\n");
*/
  result = rec_hybrid_ineq(0);
/*
  red_print_graph(result);
*/
  return(result);
}
/* red_hybrid_ineq() */




struct red_type	*hybrid_root_restrict(d, ub_numerator, ub_denominator)
	struct red_type	*d;
	int		ub_numerator, ub_denominator;
{
  struct red_type	*result, *child;
  int			ci;

  if (ub_numerator == HYBRID_POS_INFINITY && ub_denominator == 1)
    return(d);

  result = NORM_FALSE;
  for (ci = 0; ci < d->u.hrd.child_count; ci++)
    if (   (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    )
	&& (   (   d->u.hrd.arc[ci].ub_numerator == HYBRID_NEG_INFINITY
	        && d->u.hrd.arc[ci].ub_denominator == 1
	        )
	    || d->u.hrd.arc[ci].ub_numerator * ub_denominator
	       < ub_numerator * d->u.hrd.arc[ci].ub_denominator
	    )
	) {
      child = hrd_lone_subtree(d->u.hrd.arc[ci].child,
	d->var_index, d->u.hrd.hrd_exp,
	d->u.hrd.arc[ci].ub_numerator,
	d->u.hrd.arc[ci].ub_denominator
      );
      result = red_bop(OR, result, child);
    }
    else
      break;
  for (child = NORM_FALSE; ci < d->u.hrd.child_count; ci++) {
    child = red_bop(OR, child, d->u.hrd.arc[ci].child);
  }
  child = hrd_lone_subtree(child,
    d->var_index, d->u.hrd.hrd_exp,
    ub_numerator, ub_denominator
  );
  result = red_bop(OR, result, child);
  return (result);
}
/* hybrid_root_restrict() */




struct red_type	*hybrid_root_extract_upperhalf(d, lb_numerator, lb_denominator)
	struct red_type	*d;
	int		lb_numerator, lb_denominator;
{
  struct red_type	*result, *child;
  int			ci;

  if (lb_numerator == HYBRID_NEG_INFINITY && lb_denominator == 1)
    return(d);

  result = NORM_FALSE;
  ci = d->u.hrd.child_count-1;
  if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
      && d->u.hrd.arc[ci].ub_denominator == 1
      ) {
    result = red_bop(OR, result, d->u.hrd.arc[ci].child);
    ci--;
  }
  for (; ci>=0; ci--) {
    if (   (   d->u.hrd.arc[ci].ub_numerator != HYBRID_NEG_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    )
        && lb_numerator * d->u.hrd.arc[ci].ub_denominator
	   <= d->u.hrd.arc[ci].ub_numerator * lb_denominator
	) {
      child = hrd_lone_subtree(d->u.hrd.arc[ci].child,
	d->var_index, d->u.hrd.hrd_exp,
	d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator
      );
      result = red_bop(OR, result, child);
    }
    else
      break;
  }
  return (result);
}
/* hybrid_root_extract_upperhalf() */



char	*hchild_stack_push(d, ub_numerator, ub_denominator)
     struct red_type	*d;
     int		ub_numerator, ub_denominator;
{
  int	i; 
  /*
  if (ub > CLOCK_POS_INFINITY) {
    fprintf(RED_OUT, "\nError: overbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub < CLOCK_NEG_INFINITY) {
    fprintf(RED_OUT, "\nError: underbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  if (d == NORM_FALSE)
    return;

  for (i = TOP_CHILD_STACK;
       i >= 0 && CHILD_STACK[i].level == TOP_LEVEL_CHILD_STACK;
       i--
       )
    if (d == CHILD_STACK[i].d)
      return;

  child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub = ub_numerator; 
  CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den = ub_denominator;
}
/* hchild_stack_push() */




char	*hchild_stack_restrict(he, d, ub_numerator, ub_denominator)
     struct hrd_exp_type	*he; 
     struct red_type		*d;
     int			ub_numerator, ub_denominator;
{
  if (   d == NORM_FALSE
      || (   TOP_CHILD_STACK >= 0 
          && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK 
          && CHILD_STACK[TOP_CHILD_STACK].d == d
	  && ub_numerator * CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den 
	     <= CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub * ub_denominator
	  )
      )
    return;

  if (hrd_exp_converse_test(he, d)) {
    /* Simple binary negative cycles can happen. */
    d = hybrid_root_extract_upperhalf(d, -1*ub_numerator, ub_denominator);
    if (d == NORM_FALSE)
      return;
  }

  if (   TOP_CHILD_STACK >= 0 
      && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK 
      && CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub == ub_numerator 
      && CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den == ub_denominator
      ) {
    CHILD_STACK[TOP_CHILD_STACK].d 
    = red_bop(OR, d, CHILD_STACK[TOP_CHILD_STACK].d);
  }
  else {
    child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
    CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
    CHILD_STACK[TOP_CHILD_STACK].d = d; 
    CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub = ub_numerator; 
    CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den = ub_denominator;
  }
}
/* hchild_stack_restrict() */








char	*hchild_stack_checkpush(d, ub_numerator, ub_denominator)
     struct red_type	*d;
     int		ub_numerator, ub_denominator;
{
  int	i; 
  
  if (d == NORM_FALSE) {
    return;
  }

  for (i = TOP_CHILD_STACK; 
       i >= 0 && CHILD_STACK[TOP_CHILD_STACK].level == TOP_LEVEL_CHILD_STACK; 
       i--
       ) {
    d = red_exclude_with_reduction(d, CHILD_STACK[TOP_CHILD_STACK].d);
    if (d == NORM_FALSE)
      return;
  }

  child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub = ub_numerator; 
  CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den = ub_denominator;
}
/* hchild_stack_checkpush() */




struct red_type	*hrd_new(var_index, hrd_exp)
	int			var_index;
	struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*d;
  int			flag, i, bd;

  /*
  if (red_pool == NULL && free_red_count != 0) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  if (red_pool != NULL && free_red_count == 0) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  get_to_next_valid_child(); 
  switch (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]) {
  case 0: 
    child_stack_level_pop(); 
    return(NORM_FALSE);
  case 1:
    bd = CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub 
       / CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den;
    if (bd == HYBRID_POS_INFINITY) {
      d = CHILD_STACK[TOP_CHILD_STACK].d;
      child_stack_pop(); 
      get_to_next_valid_child(); 
      child_stack_level_pop(); 
      return(d);
    }
  default:
    d = red_alloc(var_index); 
    d->status = 0; 
    d->u.hrd.hrd_exp = hrd_exp;
    d->u.hrd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK];
    hchild_count = hchild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK];
    d->u.hrd.arc = (struct hrd_child_type *) 
      malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] * sizeof(struct hrd_child_type));
    for (i = 0; i < d->u.hrd.child_count; i++) { 
      bd = CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub 
      / CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den;
      if (bd > HYBRID_POS_INFINITY) {
        fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hrd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub, 
		CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den
		);
        fflush(RED_OUT);
        exit(0);
      }
      else if (bd < HYBRID_NEG_INFINITY) {
        fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hrd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub, 
		CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den
		);
        fflush(RED_OUT);
        exit(0);
      }

      d->u.hrd.arc[i].ub_numerator = CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub;
      d->u.hrd.arc[i].ub_denominator = CHILD_STACK[TOP_CHILD_STACK].u.hrd.ub_den;
      d->u.hrd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d; 
      if (   d->u.hrd.arc[i].child != NORM_NO_RESTRICTION 
          && (   var_index > d->u.hrd.arc[i].child->var_index
              || (   var_index == d->u.hrd.arc[i].child->var_index
                  && HRD_EXP_COMP(d->u.hrd.hrd_exp, 
                       d->u.hrd.arc[i].child->u.hrd.hrd_exp
                     ) >= 0
          )   )   ) { 
      	fprintf(RED_OUT, 
      	  "\nOOO detected in hrd_new():vi:%1d:%s-->vj:%1d:%s\nparent exp:\n", 
      	  var_index, VAR[var_index].NAME, 
      	  d->u.hrd.arc[i].child->var_index, 
      	  VAR[d->u.hrd.arc[i].child->var_index].NAME 
      	); 
      	hrd_exp_print(hrd_exp, 0); 
      	fprintf(RED_OUT, "\n"); 
      	if (var_index == d->u.hrd.arc[i].child->var_index) { 
      	  fprintf(RED_OUT, "child exp:\n"); 
      	  hrd_exp_print(d->u.hrd.arc[i].child->u.hrd.hrd_exp, 0); 
      	  fprintf(RED_OUT, "\n"); 
      	} 
      	fflush(RED_OUT); 
      	bk(0); 
      } 
      d->status = d->status | (d->u.hrd.arc[i].child->status & FLAG_RED_LAZY); 
      child_stack_pop(); 
      get_to_next_valid_child(); 
    }
    child_stack_level_pop(); 
    return(red_share(d));
  }
}
  /* hrd_new() */



struct red_type		*ONE_HYBRID_CONSTRAINT_ATOM; 
struct hrd_exp_type	*ONE_HYBRID_CONSTRAINT_EXP;
int			ONE_HYBRID_CONSTRAINT_INDEX,
			ONE_HYBRID_CONSTRAINT_LB_NUMERATOR,
			ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
			ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
			ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR;



struct red_type	*rec_hrd_one_constraint_ascending(d)
     struct red_type	*d;
{
  int				b, ci;
  struct red_type		*new_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(ONE_HYBRID_CONSTRAINT_ATOM);
  else if (d->var_index > ONE_HYBRID_CONSTRAINT_INDEX) {
    return(hrd_lone_subtree(d, 
      ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
      ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
      ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
    ) );
  }
  else if (d->var_index == ONE_HYBRID_CONSTRAINT_INDEX) {
    b = HRD_EXP_COMP(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP);
    if (b > 0) {
      if (hexp_converse_test(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP))
        d = hybrid_root_extract_upperhalf(d, 
          -1*ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	  ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
	);
      return(hrd_lone_subtree(d, 
        ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
	ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
      ) );
    }
    else if (b == 0) {
      return(hybrid_root_restrict(d, ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
				  ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
				  )
	     );
    }
  }
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(AND, d, ONE_HYBRID_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_ascending(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    return(ce->result = crd_new(d->var_index));
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_ascending(d->u.hrd.arc[ci].child);
      hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
    }
    return(ce->result = hrd_new(d->var_index, d->u.hrd.hrd_exp));
    break;

  case TYPE_LAZY_EXP: 
    new_child = lazy_subtree(
      rec_hrd_one_constraint_ascending(d->u.lazy.false_child), 
      rec_hrd_one_constraint_ascending(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_ascending(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child,
      	d->u.fdd.arc[ci].lower_bound,
      	d->u.fdd.arc[ci].upper_bound
      );
    }

    return(ce->result = fdd_new(d->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_ascending(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child,
      	d->u.dfdd.arc[ci].lower_bound,
      	d->u.dfdd.arc[ci].upper_bound
      );
    }

    return(ce->result = dfdd_new(d->var_index));
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_ascending(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child,
      			d->u.ddd.arc[ci].lower_bound,
      			d->u.ddd.arc[ci].upper_bound
      			);
    }

    return(ce->result = ddd_new(d->var_index));
  }
}
  /* rec_hrd_one_constraint_ascending() */




int	count_rhocd = 0; 

struct red_type	*rec_hrd_one_constraint_descending(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*new_child;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(ONE_HYBRID_CONSTRAINT_ATOM);
  else if (d->var_index > ONE_HYBRID_CONSTRAINT_INDEX) {
    return(hrd_lone_subtree(
      d, ONE_HYBRID_CONSTRAINT_INDEX, 
      ONE_HYBRID_CONSTRAINT_EXP,
      ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
      ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
    ) );
  }
  else if (d->var_index == ONE_HYBRID_CONSTRAINT_INDEX) {
    int b;

    b = HRD_EXP_COMP(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP);
    if (b > 0) {
      return(hrd_lone_subtree(d, 
        ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
	ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
      ) );
    }
    else if (b == 0) {
      return(hybrid_root_restrict(d, ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
      ) );
    }
    else if (hexp_converse_test(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP)) {
      struct hrd_exp_type	*old_hrd_exp; 
      
      old_hrd_exp = d->u.hrd.hrd_exp; 
/*
      fprintf(RED_OUT, "\n>>> rhocd %1d, VI%1d:%s, vi%1d:%s, old hrd %x: ", 
        ++count_rhocd, ONE_HYBRID_CONSTRAINT_INDEX, 
        VAR[ONE_HYBRID_CONSTRAINT_INDEX].NAME, 
        d->var_index, VAR[d->var_index].NAME, 
        old_hrd_exp
      ); 
      hrd_exp_print(old_hrd_exp, 0);
*/
      d = hybrid_root_extract_upperhalf(
        d, -1*ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
      );
/*
      fprintf(RED_OUT, "\n    rhocd %1d, VI%1d:%s, vi%1d:%s, hrd %x: ", 
        count_rhocd, ONE_HYBRID_CONSTRAINT_INDEX, 
        VAR[ONE_HYBRID_CONSTRAINT_INDEX].NAME, 
        d->var_index, VAR[d->var_index].NAME, 
        d->u.hrd.hrd_exp 
      ); 
      hrd_exp_print(d->u.hrd.hrd_exp, 0); 
      if (count_rhocd == -1) {
      	fprintf(RED_OUT, "Caught!\n"); 
      }
      fflush(RED_OUT); 
*/
      if (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX 
	  && d->u.hrd.hrd_exp == ONE_HYBRID_CONSTRAINT_EXP
	  )
        return(hybrid_root_restrict(d, ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
				    ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
				    )
	       );
      else if (   d->var_index > ONE_HYBRID_CONSTRAINT_INDEX 
	       || (   VAR[d->var_index].TYPE == TYPE_HRD
	           && d->u.hrd.hrd_exp != old_hrd_exp
	       )   )
        return(hrd_lone_subtree(d, ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
	  ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
	  ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
	) );
    }
  }
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  if (d == NORM_NO_RESTRICTION || d->var_index > ONE_HYBRID_CONSTRAINT_INDEX)
    return(hrd_lone_subtree(d, ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
			       ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
			       ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
			       )
	   );
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(AND, d, ONE_HYBRID_CONSTRAINT_ATOM); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_descending(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    return(ce->result = crd_new(d->var_index));
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_descending(d->u.hrd.arc[ci].child);
      hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    }
    return(ce->result = hrd_new(d->var_index, d->u.hrd.hrd_exp));
    break;

  case TYPE_LAZY_EXP: 
    new_child = lazy_subtree(
      rec_hrd_one_constraint_descending(d->u.lazy.false_child), 
      rec_hrd_one_constraint_descending(d->u.lazy.true_child), 
      VAR[d->var_index].PROC_INDEX, 
      d->u.lazy.exp
    ); 
    break; 

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_descending(
        d->u.fdd.arc[ci].child
      );
      fchild_stack_push(new_child,
      	d->u.fdd.arc[ci].lower_bound,
      	d->u.fdd.arc[ci].upper_bound
      );
    }

    return(ce->result = fdd_new(d->var_index));
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_descending(
        d->u.dfdd.arc[ci].child
      );
      dfchild_stack_push(new_child,
      	d->u.dfdd.arc[ci].lower_bound,
      	d->u.dfdd.arc[ci].upper_bound
      );
    }

    return(ce->result = dfdd_new(d->var_index));
    break; 

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hrd_one_constraint_descending(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child,
      			d->u.ddd.arc[ci].lower_bound,
      			d->u.ddd.arc[ci].upper_bound
      			);
    }

    return(ce->result = ddd_new(d->var_index));
  }
}
  /* rec_one_constraint_descending() */




struct red_type	*hrd_one_constraint(d, hrd_exp, ub_numerator, ub_denominator)
     struct red_type		*d;
     struct hrd_exp_type	*hrd_exp;
     int			ub_numerator, ub_denominator;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

  ONE_HYBRID_CONSTRAINT_INDEX 
  = (hrd_exp->status & MASK_HYBRID_LIFTED_VI) / MASK_HYBRID_VI_BASE;  
  ONE_HYBRID_CONSTRAINT_EXP = hrd_exp;
  ONE_HYBRID_CONSTRAINT_UB_NUMERATOR = ub_numerator;
  ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR = ub_denominator;
  ONE_HYBRID_CONSTRAINT_ATOM 
  = hrd_atom(hrd_exp, ub_numerator, ub_denominator); 
    
  if (hrd_exp->hrd_term[0].coeff < 0) {
    result = rec_hrd_one_constraint_ascending(d);
  }
  else {
    result = rec_hrd_one_constraint_descending(d);
  }
  return(result);
}
/* hrd_one_constraint() */






int			HVI_ELM;
struct hrd_exp_type	*HEXP_ELM;


struct red_type	*rec_hybrid_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (d->var_index > HVI_ELM)
    return(d);

  ce = cache2_check_result_key(OP_HYBRID_ELIMINATE, d, 
    (struct red_type *) HEXP_ELM
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    for (ci = 0; ci < d->u.crd.child_count; ci++) {
      conj = rec_hybrid_eliminate(d->u.crd.arc[ci].child);
      conj = crd_lone_subtree(conj, d->var_index, d->u.crd.arc[ci].upper_bound);
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_HRD:
    if (d->var_index == HVI_ELM && d->u.hrd.hrd_exp == HEXP_ELM) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	result = red_bop(OR, result, d->u.hrd.arc[ci].child);
      }
    }
    else {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_eliminate(d->u.hrd.arc[ci].child);
	conj = hrd_lone_subtree(conj, d->var_index, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
	result = red_bop(OR, result, conj);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = rec_hybrid_eliminate(d->u.fdd.arc[ci].child);
      conj = fdd_lone_subtree(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = rec_hybrid_eliminate(d->u.dfdd.arc[ci].child);
      conj = dfdd_lone_subtree(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = rec_hybrid_eliminate(d->u.ddd.arc[ci].child);
      conj = ddd_lone_subtree(conj, d->var_index, d->u.ddd.arc[ci].lower_bound,
				   d->u.ddd.arc[ci].upper_bound
				   );
      result = red_bop(OR, result, conj);
    }
    break;
  }
  return(ce->result = result); 
}
/* rec_hybrid_eliminate() */



struct red_type	*hybrid_eliminate(d, vi, hrd_exp)
     struct red_type		*d;
     int			vi;
     struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*result;

  if (VAR[vi].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "Warning: you use red_hybrid_eliminate() to eliminate non-hybrids.\n");
    fflush(RED_OUT);
    for (; 1; );
  }
  HVI_ELM = vi;
  HEXP_ELM = hrd_exp;

  result = rec_hybrid_eliminate(d);

  return(result);
}
/* hybrid_eliminate() */



struct red_type 	*HYBRID_EXTRACT_LOWERHALF_ATOM; 


struct red_type	*rec_hybrid_extract_lowerhalf(d)
  struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child, *result;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (   d->var_index == TYPE_TRUE
	   || d->var_index > ONE_HYBRID_CONSTRAINT_INDEX
	   || (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	       && HRD_EXP_COMP(ONE_HYBRID_CONSTRAINT_EXP, d->u.hrd.hrd_exp) < 0
	       )
	   )
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_HYBRID_EXTRACT_LOWERHALF, 
    d, ONE_HYBRID_CONSTRAINT_EXP, 
    ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, 
    ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_lowerhalf(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;
  case TYPE_HRD:
    child_stack_level_push();
    if (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	&& !HRD_EXP_COMP(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP)
	) {
      new_child = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	if (   (   d->u.hrd.arc[ci].ub_numerator == HYBRID_NEG_INFINITY
		&& d->u.hrd.arc[ci].ub_denominator == 1
		)
	    || ONE_HYBRID_CONSTRAINT_LB_NUMERATOR * d->u.hrd.arc[ci].ub_denominator
	       >= d->u.hrd.arc[ci].ub_numerator * ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
	    )
	  hchild_stack_push(d->u.hrd.arc[ci].child,
			    d->u.hrd.arc[ci].ub_numerator,
			    d->u.hrd.arc[ci].ub_denominator
			    );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        new_child = rec_hybrid_extract_lowerhalf(d->u.hrd.arc[ci].child);
        hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_lowerhalf(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }

    result = fdd_new(d->var_index); 
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_lowerhalf(d->u.dfdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index); 
    break;
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_lowerhalf(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
/* rec_hybrid_extract_lowerhalf() */





struct red_type	*hybrid_extract_lowerhalf(d, hvi, hrd_exp, lb_numerator, lb_denominator)
     struct red_type		*d;
     int			hvi, lb_numerator, lb_denominator;
     struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*result;

  if (VAR[hvi].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "\nError: a non-hybrid_inequality in hybrid_extract_upperhalf()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (lb_numerator == HYBRID_POS_INFINITY && lb_denominator == 1)
    return(d);

  ONE_HYBRID_CONSTRAINT_INDEX = hvi;
  ONE_HYBRID_CONSTRAINT_EXP = hrd_exp;
  ONE_HYBRID_CONSTRAINT_LB_NUMERATOR = lb_numerator;
  ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR = lb_denominator;
  HYBRID_EXTRACT_LOWERHALF_ATOM = hrd_atom(
    hrd_exp, lb_numerator, lb_denominator
  );
  result = rec_hybrid_extract_lowerhalf(d);

  return(result);
}
/* hybrid_extract_lowerhalf() */





struct red_type 	*HYBRID_EXTRACT_UPPERHALF_ATOM; 

struct red_type	*rec_hybrid_extract_upperhalf(d)
  struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child, *result;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (   d->var_index == TYPE_TRUE
	   || d->var_index > ONE_HYBRID_CONSTRAINT_INDEX
	   || (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	       && HRD_EXP_COMP(ONE_HYBRID_CONSTRAINT_EXP, d->u.hrd.hrd_exp) < 0
	       )
	   )
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_EXTRACT_UPPERHALF, 
    d, ONE_HYBRID_CONSTRAINT_EXP, 
    ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, 
    ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_upperhalf(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;
  case TYPE_HRD:
    child_stack_level_push();
    if (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	&& !HRD_EXP_COMP(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP)
	) {
      new_child = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	if (   (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
		&& d->u.hrd.arc[ci].ub_denominator == 1
		)
	    || ONE_HYBRID_CONSTRAINT_LB_NUMERATOR * d->u.hrd.arc[ci].ub_denominator
		<= d->u.hrd.arc[ci].ub_numerator * ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
	    )
	  hchild_stack_push(d->u.hrd.arc[ci].child,
			    d->u.hrd.arc[ci].ub_numerator,
			    d->u.hrd.arc[ci].ub_denominator
			    );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        new_child = rec_hybrid_extract_upperhalf(d->u.hrd.arc[ci].child);
        hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_upperhalf(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }

    result = fdd_new(d->var_index);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_upperhalf(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index);
    break;
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_extract_upperhalf(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
/* rec_hybrid_extract_upperhalf() */





struct red_type	*hybrid_extract_upperhalf(d, hvi, hrd_exp, lb_numerator, lb_denominator)
     struct red_type		*d;
     int			hvi, lb_numerator, lb_denominator;
     struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*result;

  if (VAR[hvi].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "\nError: a non-hybrid_inequality in hybrid_extract_upperhalf()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (lb_numerator == HYBRID_NEG_INFINITY && lb_denominator == 1)
    return(d);

  ONE_HYBRID_CONSTRAINT_INDEX = hvi;
  ONE_HYBRID_CONSTRAINT_EXP = hrd_exp;
  ONE_HYBRID_CONSTRAINT_LB_NUMERATOR = lb_numerator;
  ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR = lb_denominator;
  HYBRID_EXTRACT_UPPERHALF_ATOM = hrd_atom(
    hrd_exp, lb_numerator, lb_denominator
  );
  result = rec_hybrid_extract_upperhalf(d);

  return(result);
}
/* hybrid_extract_upperhalf() */




struct red_type	*HYBRID_SUBTRACT_UPPERHALF_ATOM; 

struct red_type	*rec_hybrid_subtract_upperhalf(d)
  struct red_type	*d;
{
  int				ci, lb, ub;
  struct red_type		*new_child, *result;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);
  else if (   d->var_index == TYPE_TRUE
	   || d->var_index > ONE_HYBRID_CONSTRAINT_INDEX
	   || (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	       && HRD_EXP_COMP(ONE_HYBRID_CONSTRAINT_EXP, d->u.hrd.hrd_exp) < 0
	       )
	   )
    return(NORM_FALSE);

  ce = cache4_check_result_key(OP_HYBRID_SUBTRACT_UPPERHALF, 
    d, ONE_HYBRID_CONSTRAINT_EXP, 
    ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, 
    ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_subtract_upperhalf(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;
  case TYPE_HRD:
    child_stack_level_push();
    if (   d->var_index == ONE_HYBRID_CONSTRAINT_INDEX
	&& !HRD_EXP_COMP(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP)
	) {
      new_child = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	if (ONE_HYBRID_CONSTRAINT_LB_NUMERATOR * d->u.hrd.arc[ci].ub_denominator
	    > d->u.hrd.arc[ci].ub_numerator * ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR
	    )
	  hchild_stack_push(d->u.hrd.arc[ci].child,
			    d->u.hrd.arc[ci].ub_numerator,
			    d->u.hrd.arc[ci].ub_denominator
			    );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        new_child = rec_hybrid_subtract_upperhalf(d->u.hrd.arc[ci].child);
        hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_subtract_upperhalf(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
			d->u.fdd.arc[ci].upper_bound
			);
    }

    result = fdd_new(d->var_index);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_subtract_upperhalf(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index);
    break;
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_subtract_upperhalf(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
/* rec_hybrid_subtract_upperhalf() */





struct red_type	*hybrid_subtract_upperhalf(d, hvi, hrd_exp, lb_numerator, lb_denominator)
     struct red_type		*d;
     int			hvi, lb_numerator, lb_denominator;
     struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*result;

  if (VAR[hvi].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError: a non-hybrid_inequality in hybrid_extract_upperhalf()\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  ONE_HYBRID_CONSTRAINT_INDEX = hvi;
  ONE_HYBRID_CONSTRAINT_EXP = hrd_exp;
  ONE_HYBRID_CONSTRAINT_LB_NUMERATOR = lb_numerator;
  ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR = lb_denominator;
  HYBRID_SUBTRACT_UPPERHALF_ATOM = hrd_atom(
    hrd_exp, lb_numerator, lb_denominator
  );
  result = rec_hybrid_subtract_upperhalf(d);

  return(result);
}
/* hybrid_subtract_upperhalf() */






struct red_type	*rec_hybrid_eliminate_relative(d)
  struct red_type	*d;
{
  int				ci;
  struct red_type		*new_child, *result;
  struct cache1_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE) {
    return(d);
  }

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_RELATIVE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (VAR[d->var_index].U.CRD.CLOCK1 && VAR[d->var_index].U.CRD.CLOCK2) {
      new_child = NORM_FALSE;
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	new_child = red_bop(OR, new_child, rec_hybrid_eliminate_relative(d->u.crd.arc[ci].child));
      }
      result = new_child;
    }
    else {
      child_stack_level_push();
      for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
	new_child = rec_hybrid_eliminate_relative(d->u.crd.arc[ci].child);
	bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
      }
      result = crd_new(d->var_index);
    }
    break;

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1) {
      new_child = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	new_child = red_bop(OR, new_child,
			    rec_hybrid_eliminate_relative(d->u.hrd.arc[ci].child)
			    );
      } 
      result = new_child;
    }
    else {
      child_stack_level_push();
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	new_child = rec_hybrid_eliminate_relative(d->u.hrd.arc[ci].child);
	hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			  d->u.hrd.arc[ci].ub_denominator
			  );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    }
    break;
  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_eliminate_relative(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child, d->u.fdd.arc[ci].lower_bound,
			d->u.fdd.arc[ci].upper_bound
			);
    }
    result = fdd_new(d->var_index);
    break;
  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_eliminate_relative(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child, d->u.dfdd.arc[ci].lower_bound,
			d->u.dfdd.arc[ci].upper_bound
			);
    }
    result = dfdd_new(d->var_index);
    break;
  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hybrid_eliminate_relative(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound
			);
    }
    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
/* rec_hybrid_eliminate_relative() */





struct red_type	*hybrid_eliminate_relative(d)
     struct red_type	*d;
{
  struct red_type	*result;

  result = rec_hybrid_eliminate_relative(d);

  return(result);
}
/* hybrid_eliminate_relative() */






struct red_type	*rec_hybrid_eliminate_simple_negative_cycles(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*child, *result;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_SIMPLE_NEGATIVE_CYCLES, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_simple_negative_cycles(d->u.crd.arc[ci].child);
      bchild_stack_push(child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    if (d->u.hrd.hrd_exp->hrd_term[0].coeff < 0) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	if (   d->u.hrd.arc[ci].ub_numerator < HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator > 1
	    )
	  child = hybrid_extract_upperhalf(d->u.hrd.arc[ci].child, d->var_index,
					  d->u.hrd.hrd_exp,
					  -d->u.hrd.arc[ci].ub_numerator,
					  d->u.hrd.arc[ci].ub_denominator
					  );
	else
	  child = d->u.hrd.arc[ci].child;

	child = rec_hybrid_eliminate_simple_negative_cycles(child);
	hchild_stack_push(child, d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_eliminate_simple_negative_cycles(d->u.hrd.arc[ci].child);
	hchild_stack_push(child, d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      }
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_simple_negative_cycles(
        d->u.fdd.arc[ci].child
      );
      fchild_stack_push(child, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }

    result = fdd_new(d->var_index);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_simple_negative_cycles(
        d->u.dfdd.arc[ci].child
      );
      dfchild_stack_push(child, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }

    result = dfdd_new(d->var_index);
    break;

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_simple_negative_cycles(d->u.ddd.arc[ci].child);
      ichild_stack_push(child, d->u.ddd.arc[ci].lower_bound,
				 d->u.ddd.arc[ci].upper_bound
				 );
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_simple_negative_cycles() */





struct red_type	*hybrid_eliminate_simple_negative_cycles(w)
     int	w;
{
  struct red_type	*result;

  result = rec_hybrid_eliminate_simple_negative_cycles(RT[w]);

  return(RT[w] = result);
}
/* hybrid_eliminate_simple_negative_cycles() */






/******************************************************************
 * magnitude maintenance with downward split techniques
 */
struct hrd_exp_type	*hrd_exp_add(
  hex, nx, dx, hey, ny, dy, hvi_ptr, divider_ptr
)
	struct hrd_exp_type	*hex, *hey;
	int			nx, dx, ny, dy, *hvi_ptr, *divider_ptr;
{
  int				vi, lx, ly, tc, coeff;
  struct hrd_term_link_type	*tlist;
  struct hrd_exp_type		*newhe;

  lx = (hex->status & MASK_HYBRID_LENGTH) - 1;
  ly = (hey->status & MASK_HYBRID_LENGTH) - 1;

  switch (GSTATUS[INDEX_DISCRETE_DENSE_INTERLEAVING] 
    & MASK_DISCRETE_DENSE_INTERLEAVING
  ) { 
  case FLAG_DISCRETE_DENSE_BOTTOM: 
    for (tc = 0, tlist = NULL; lx >= 0 && ly >= 0; ) {
      if (hex->hrd_term[lx].var_index > hey->hrd_term[ly].var_index) {
        vi = hex->hrd_term[lx].var_index;
        tlist = hrd_term_insert(tlist, vi, hex->hrd_term[lx].coeff * dx * ny, 1, &tc);
        lx--;
      }
      else if (hex->hrd_term[lx].var_index < hey->hrd_term[ly].var_index) {
        vi = hey->hrd_term[ly].var_index;
        tlist = hrd_term_insert(tlist, vi, hey->hrd_term[ly].coeff * dy * nx, 1, &tc);
        ly--;
      }
      else {
        vi = hex->hrd_term[lx].var_index;
        coeff = hex->hrd_term[lx].coeff * dx * ny + hey->hrd_term[ly].coeff * dy * nx;
        if (coeff) {
          tlist = hrd_term_insert(tlist, vi, coeff, 1, &tc);
        }
        lx--;
        ly--;
      }
    }
    for (; lx >= 0; lx--) {
      vi = hex->hrd_term[lx].var_index;
      tlist = hrd_term_insert(tlist, vi, hex->hrd_term[lx].coeff * dx * ny, 1, &tc);
    }
    for (; ly >= 0; ly--) {
      vi = hey->hrd_term[ly].var_index;
      tlist = hrd_term_insert(tlist, vi, hey->hrd_term[ly].coeff * dy * nx, 1, &tc);
    }
    *hvi_ptr = variable_index[TYPE_HRD][PROCESS_COUNT][0];
    break; 
  case FLAG_DISCRETE_DENSE_HALF_INTERLEAVING: 
  case FLAG_DISCRETE_DENSE_FULL_INTERLEAVING: 
    *hvi_ptr = 0;
    for (tc = 0, tlist = NULL; lx >= 0 && ly >= 0; ) {
      if (hex->hrd_term[lx].var_index > hey->hrd_term[ly].var_index) {
        vi = hex->hrd_term[lx].var_index;
        tlist = hrd_term_insert(tlist, vi, hex->hrd_term[lx].coeff * dx * ny, 1, &tc);
        if (VAR[vi].PROC_INDEX > *hvi_ptr)
          *hvi_ptr = VAR[vi].PROC_INDEX;
        lx--;
      }
      else if (hex->hrd_term[lx].var_index < hey->hrd_term[ly].var_index) {
        vi = hey->hrd_term[ly].var_index;
        tlist = hrd_term_insert(tlist, vi, hey->hrd_term[ly].coeff * dy * nx, 1, &tc);
        if (VAR[vi].PROC_INDEX > *hvi_ptr)
          *hvi_ptr = VAR[vi].PROC_INDEX;
        ly--;
      }
      else {
        vi = hex->hrd_term[lx].var_index;
        coeff = hex->hrd_term[lx].coeff * dx * ny + hey->hrd_term[ly].coeff * dy * nx;
        if (coeff) {
          tlist = hrd_term_insert(tlist, vi, coeff, 1, &tc);
	  if (VAR[vi].PROC_INDEX > *hvi_ptr)
            *hvi_ptr = VAR[vi].PROC_INDEX;
        }
        lx--;
        ly--;
      }
    }
    for (; lx >= 0; lx--) {
      vi = hex->hrd_term[lx].var_index;
      tlist = hrd_term_insert(tlist, vi, hex->hrd_term[lx].coeff * dx * ny, 1, &tc);
      if (VAR[vi].PROC_INDEX > *hvi_ptr)
        *hvi_ptr = VAR[vi].PROC_INDEX;
    }
    for (; ly >= 0; ly--) {
      vi = hey->hrd_term[ly].var_index;
      tlist = hrd_term_insert(tlist, vi, hey->hrd_term[ly].coeff * dy * nx, 1, &tc);
      if (VAR[vi].PROC_INDEX > *hvi_ptr)
        *hvi_ptr = VAR[vi].PROC_INDEX;
    }
    *hvi_ptr = variable_index[TYPE_HRD][*hvi_ptr][0]; 
    break; 
  }
  *divider_ptr = get_list_numerator_factor(tlist);
  newhe = hrd_exp_new(tlist, tc, &lx, &ly); /* lx and ly are not used. */
  free_hrd_term_list(tlist);
/*
  if (ITERATION_COUNT == 1 && ITERATE_SXI == 0) {
    fprintf(RED_OUT, "\n------(HRD EXP ADDITION)----------------\n");
    fprintf(RED_OUT, "%1d/%1d * ", nx, dx);
    hrd_exp_print(hex, 0);
    fprintf(RED_OUT, "%1d/%1d * ", ny, dy);
    hrd_exp_print(hey, 0);
    fprintf(RED_OUT, "result:");
    hrd_exp_print(newhe, 0);
    fflush(RED_OUT);
  }

  if (ITERATION_COUNT == 2 && ITERATE_SXI == 23 && newhe == test_hrd_exp) {
    fprintf(RED_OUT, "Gotcha in hrd_exp_add()!\n");
    fprintf(RED_OUT, "%1d/%1d * ", nx, dx);
    hrd_exp_print(hex, 0);
    fprintf(RED_OUT, "%1d/%1d * ", ny, dy);
    hrd_exp_print(hey, 0);
    fprintf(RED_OUT, " = ");
    hrd_exp_print(newhe, 0);
    fflush(RED_OUT);
    for (lx = 1; lx; );

  }
*/
  return(newhe);
}
/* hrd_exp_add() */





int			HVI_DOWNWARD, COEFF_DOWNWARD, UB_NUMERATOR_DOWNWARD, UB_DENOMINATOR_DOWNWARD;
struct hrd_exp_type	*EXP_DOWNWARD; 

struct red_type	*rec_hybrid_bypass_given_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*result, *child;
#if RED_MECH_CACHE7 == RED_MECH_CACHE_HASH 
  struct cache7_hash_entry_type	*ce; 
#endif 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

#if RED_MECH_CACHE7 == RED_MECH_CACHE_STACK 
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
#endif 

#if RED_MECH_CACHE7 == RED_MECH_CACHE_HASH 
  ce = cache7_check_result_key(OP_HYBRID_BYPASS_GIVEN_DOWNWARD, d, 
    EXP_DOWNWARD, 
    HVI_DOWNWARD, 
    COEFF_DOWNWARD, 
    NULL, 
    UB_NUMERATOR_DOWNWARD, 
    UB_DENOMINATOR_DOWNWARD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 
#endif 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_given_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    ci = hrd_term_coeff_extract(d->u.hrd.hrd_exp, HVI_DOWNWARD);
    if (ci * COEFF_DOWNWARD < 0) {
      int			coeff, coeffD, hrd_vi, divider, ub_numerator, ub_denominator;
      struct hrd_exp_type	*hrd_exp;

      coeff = ci;
      if (coeff < 0) {
        coeff = -coeff;
	coeffD = COEFF_DOWNWARD;
      }
      else
        coeffD = -COEFF_DOWNWARD;
      hrd_exp = hrd_exp_add(d->u.hrd.hrd_exp, coeff, 1, EXP_DOWNWARD, coeffD, 1,
			    &hrd_vi, &divider
			    );
      if (hrd_exp == NULL) /* a totally cancelled inequality. */ {
        for (ci = d->u.hrd.child_count - 1; ci >= 0; ci--) {
	  int	bn, bd, BN, BD;

	  bn = d->u.hrd.arc[ci].ub_numerator;
	  bd = d->u.hrd.arc[ci].ub_denominator;
	  if (bn != HYBRID_POS_INFINITY || bd != 1) {
	    rational_lift(&bn, &bd, abs(coeffD));

	    BN = UB_NUMERATOR_DOWNWARD;
	    BD = UB_DENOMINATOR_DOWNWARD;
	    rational_lift(&BN, &BD, abs(coeff));
	    hybrid_ub_add(bn, bd, BN, BD, &ub_numerator, &ub_denominator);
	    if (ub_numerator >= 0) {
	      child = rec_hybrid_bypass_given_DOWNWARD(d->u.hrd.arc[ci].child);
	      child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				            d->u.hrd.arc[ci].ub_numerator,
				            d->u.hrd.arc[ci].ub_denominator
				            );
	    }
	    else
	      break;
	  }
	  else
	    child = rec_hybrid_bypass_given_DOWNWARD(d->u.hrd.arc[ci].child);
	  result = red_bop(OR, result, child);
        }
      }
      else {
        for (ci = d->u.hrd.child_count - 1; ci >= 0; ci--) {
	  child = rec_hybrid_bypass_given_DOWNWARD(d->u.hrd.arc[ci].child);

	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
	    int	bn, bd, BN, BD;

	    bn = d->u.hrd.arc[ci].ub_numerator;
	    bd = d->u.hrd.arc[ci].ub_denominator * divider;
	    rational_lift(&bn, &bd, coeffD);

	    BN = UB_NUMERATOR_DOWNWARD;
	    BD = UB_DENOMINATOR_DOWNWARD * divider;
	    rational_lift(&BN, &BD, coeff);

	    hybrid_ub_add(bn, bd, BN, BD, &ub_numerator, &ub_denominator);
	    child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				          d->u.hrd.arc[ci].ub_numerator,
				          d->u.hrd.arc[ci].ub_denominator
				          );
	    if (ub_numerator != HYBRID_POS_INFINITY || ub_denominator != 1) {
	      child = hrd_one_constraint(child, hrd_exp, ub_numerator, ub_denominator);
/*
	      if (ITERATION_COUNT == 2 && ITERATE_SXI == 6) {
	        fprintf(RED_OUT, "==={bypass %s with}===\n", VAR[HVI_DOWNWARD].NAME);
	        hrd_exp_print(d->u.hrd.hrd_exp, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n", d->u.hrd.arc[ci].ub_numerator,
		        d->u.hrd.arc[ci].ub_denominator
		        );
	        hrd_exp_print(EXP_DOWNWARD, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n", UB_NUMERATOR_DOWNWARD, UB_DENOMINATOR_DOWNWARD);
	        fprintf(RED_OUT, "  generating ");
	        hrd_exp_print(hrd_exp, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n\n", ub_numerator, ub_denominator);
	      }
*/
	    }
	  }
	  result = red_bop(OR, result, child);
        }
      }
    }
    else {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = rec_hybrid_bypass_given_DOWNWARD(d->u.hrd.arc[ci].child);
	child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
      		(child, d->var_index, d->u.ddd.arc[ci].lower_bound,
		 d->u.ddd.arc[ci].upper_bound
		 );
      result = red_bop(OR, result, child);
    }
  }
#if RED_MECH_CACHE7 == RED_MECH_CACHE_STACK 
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
#endif 

#if RED_MECH_CACHE7 == RED_MECH_CACHE_HASH 
  return(ce->result = result); 
#endif 
}
  /* rec_hybrid_bypass_given_DOWNWARD() */




struct red_type	*rec_hybrid_bypass_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_HYBRID_BYPASS_DOWNWARD, d, 
    (struct red_type *) HVI_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (local_coeff = hrd_term_coeff_extract(d->u.hrd.hrd_exp, HVI_DOWNWARD)) {
      local_exp = d->u.hrd.hrd_exp;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_bypass_DOWNWARD(d->u.hrd.arc[ci].child);
	if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          EXP_DOWNWARD = local_exp;
	  COEFF_DOWNWARD = local_coeff;
	  UB_NUMERATOR_DOWNWARD = d->u.hrd.arc[ci].ub_numerator;
	  UB_DENOMINATOR_DOWNWARD = d->u.hrd.arc[ci].ub_denominator;

#if RED_MECH_CACHE7 == RED_MECH_CACHE_STACK
	  red_init_result(child);  
#endif 

	  grown_child = rec_hybrid_bypass_given_DOWNWARD(child);

#if RED_MECH_CACHE7 == RED_MECH_CACHE_STACK
	  red_clear_result(child); 
#endif 
	  child = grown_child;
	  child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	}
	result = red_bop(OR, result, child);
      }
      UB_NUMERATOR_DOWNWARD = HYBRID_POS_INFINITY;
      UB_DENOMINATOR_DOWNWARD = 1;
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_bypass_DOWNWARD(d->u.hrd.arc[ci].child);
	child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  } 
/*
  fprintf(RED_OUT, "\nrec_hybrid_bypass_downward(HVI_DOWNWARD=%1d)\nd:\n", 
    HVI_DOWNWARD
  ); 
  red_print_graph(d); 
  fprintf(RED_OUT, "result:\n"); 
  red_print_graph(result); 
*/  
  return(ce->result = result); 
}
  /* rec_hybrid_bypass_DOWNWARD() */






struct red_type	*hybrid_bypass_DOWNWARD(w, vi)
     int	w, vi;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  HVI_DOWNWARD = vi;
  result = rec_hybrid_bypass_DOWNWARD(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_bypass_DOWNWARD() */








#define FLAG_HYBRID_UNIT_BYPASS_DOWNWARD	0 

struct red_type	*rec_hybrid_bypass_unit_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_HYBRID_BYPASS_DOWNWARD, d, 
    (struct red_type *) FLAG_HYBRID_UNIT_BYPASS_DOWNWARD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1) {
      local_exp = d->u.hrd.hrd_exp;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_bypass_unit_DOWNWARD(d->u.hrd.arc[ci].child);
	if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          EXP_DOWNWARD = local_exp;
	  COEFF_DOWNWARD = d->u.hrd.hrd_exp->hrd_term[0].coeff;
	  UB_NUMERATOR_DOWNWARD = d->u.hrd.arc[ci].ub_numerator;
	  UB_DENOMINATOR_DOWNWARD = d->u.hrd.arc[ci].ub_denominator;
	  grown_child = rec_hybrid_bypass_given_DOWNWARD(child);
	  child = grown_child;
	  child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
	    d->u.hrd.arc[ci].ub_numerator,
	    d->u.hrd.arc[ci].ub_denominator
	  );
	}
	result = red_bop(OR, result, child);
      }
      UB_NUMERATOR_DOWNWARD = HYBRID_POS_INFINITY;
      UB_DENOMINATOR_DOWNWARD = 1;
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_bypass_unit_DOWNWARD(d->u.hrd.arc[ci].child);
	child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_bypass_unit_DOWNWARD(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_bypass_unit_DOWNWARD(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_bypass_unit_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  } 
/*
  fprintf(RED_OUT, "\nrec_hybrid_bypass_downward(HVI_DOWNWARD=%1d)\nd:\n", 
    HVI_DOWNWARD
  ); 
  red_print_graph(d); 
  fprintf(RED_OUT, "result:\n"); 
  red_print_graph(result); 
*/  
  return(ce->result = result); 
}
  /* rec_hybrid_bypass_unit_DOWNWARD() */






struct red_type	*hybrid_bypass_unit_DOWNWARD(w)
     int	w;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  HVI_DOWNWARD = FLAG_HYBRID_UNIT_BYPASS_DOWNWARD;

  result = rec_hybrid_bypass_unit_DOWNWARD(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
} 
/* hybrid_bypass_unit_DOWNWARD() */




/**********************************************************************
*  Specifically designed to bypass primed variables with interval rates.
*/
int	hrd_term_coeff_extract_UMPRIMED_WATCH(he, vi, flag_umprimed_also_ptr)
	struct hrd_exp_type	*he;
	int			vi, *flag_umprimed_also_ptr;
{
  int 	ti, len;

  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++)
    if (he->hrd_term[ti].var_index == vi) {
      break;
    }
    else if (he->hrd_term[ti].var_index > vi) {
      ti = len;
      break;
    }

  if (ti >= len)
    return(0);
  else if (ti) {
    if (   he->hrd_term[ti-1].var_index + 1 == vi
	&& !(he->hrd_term[ti-1].coeff + he->hrd_term[ti].coeff)
	)
      *flag_umprimed_also_ptr = TYPE_TRUE;
    else
      *flag_umprimed_also_ptr = TYPE_FALSE;
  }
  else
    *flag_umprimed_also_ptr = TYPE_FALSE;
  return(he->hrd_term[ti].coeff);
}
/* hrd_term_coeff_extract_UMPRIMED_WATCH() */




struct red_type	*rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, flag_umprimed_also;
  struct red_type		*result, *child;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(d);

  ce = cache7_check_result_key(
    OP_HYBRID_BYPASS_GIVEN_DOWNWARD_FOR_PRIMED, d, 
    EXP_DOWNWARD, 
    HVI_DOWNWARD, 
    COEFF_DOWNWARD, 
    NULL, 
    UB_NUMERATOR_DOWNWARD, 
    UB_DENOMINATOR_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_given_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    ci = hrd_term_coeff_extract_UMPRIMED_WATCH(d->u.hrd.hrd_exp, HVI_DOWNWARD, &flag_umprimed_also);
    if ((!flag_umprimed_also) && ci * COEFF_DOWNWARD < 0) {
      int			coeff, coeffD, hrd_vi, divider, ub_numerator, ub_denominator;
      struct hrd_exp_type	*hrd_exp;

      coeff = ci;
      if (coeff < 0) {
        coeff = -coeff;
	coeffD = COEFF_DOWNWARD;
      }
      else
        coeffD = -COEFF_DOWNWARD;
      hrd_exp = hrd_exp_add(d->u.hrd.hrd_exp, coeff, 1, EXP_DOWNWARD, coeffD, 1,
			    &hrd_vi, &divider
			    );
      if (hrd_exp == NULL) /* a totally cancelled inequality. */ {
        for (ci = d->u.hrd.child_count - 1; ci >= 0; ci--) {
	  int	bn, bd, BN, BD;

	  bn = d->u.hrd.arc[ci].ub_numerator;
	  bd = d->u.hrd.arc[ci].ub_denominator;
	  if (bn != HYBRID_POS_INFINITY || bd != 1) {
	    rational_lift(&bn, &bd, abs(coeffD));

	    BN = UB_NUMERATOR_DOWNWARD;
	    BD = UB_DENOMINATOR_DOWNWARD;
	    rational_lift(&BN, &BD, abs(coeff));
	    hybrid_ub_add(bn, bd, BN, BD, &ub_numerator, &ub_denominator);
	    if (ub_numerator >= 0) {
	      child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	      child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				            d->u.hrd.arc[ci].ub_numerator,
				            d->u.hrd.arc[ci].ub_denominator
				            );
	    }
	    else
	      break;
	  }
	  else
	    child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	  result = red_bop(OR, result, child);
        }
      }
      else {
        for (ci = d->u.hrd.child_count - 1; ci >= 0; ci--) {
	  child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);

	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
	    int	bn, bd, BN, BD;

	    bn = d->u.hrd.arc[ci].ub_numerator;
	    bd = d->u.hrd.arc[ci].ub_denominator * divider;
	    rational_lift(&bn, &bd, coeffD);

	    BN = UB_NUMERATOR_DOWNWARD;
	    BD = UB_DENOMINATOR_DOWNWARD * divider;
	    rational_lift(&BN, &BD, coeff);

	    hybrid_ub_add(bn, bd, BN, BD, &ub_numerator, &ub_denominator);
	    child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				          d->u.hrd.arc[ci].ub_numerator,
				          d->u.hrd.arc[ci].ub_denominator
				          );
	    if (ub_numerator != HYBRID_POS_INFINITY || ub_denominator != 1) {
	      child = hrd_one_constraint(child, hrd_exp, ub_numerator, ub_denominator);
/*
	      if (ITERATION_COUNT == 7 && ITERATE_SXI == 1) {
	        fprintf(RED_OUT, "==={bypass %s with}===\n", VAR[HVI_DOWNWARD].NAME);
	        hrd_exp_print(d->u.hrd.hrd_exp, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n", d->u.hrd.arc[ci].ub_numerator,
		        d->u.hrd.arc[ci].ub_denominator
		        );
	        hrd_exp_print(EXP_DOWNWARD, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n", UB_NUMERATOR_DOWNWARD, UB_DENOMINATOR_DOWNWARD);
	        fprintf(RED_OUT, "  generating ");
	        hrd_exp_print(hrd_exp, 0);
	        fprintf(RED_OUT, "  at %1d/%1d\n\n", ub_numerator, ub_denominator);
	      }
*/
	    }
	  }
	  result = red_bop(OR, result, child);
        }
      }
    }
    else {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
      		(child, d->var_index, d->u.ddd.arc[ci].lower_bound,
		 d->u.ddd.arc[ci].upper_bound
		 );
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED() */





struct red_type	*rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff, flag_umprimed_also;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache2_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache2_check_result_key(OP_HYBRID_BYPASS_DOWNWARD_FOR_PRIMED, d, 
    (struct red_type *) HVI_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (local_coeff = hrd_term_coeff_extract_UMPRIMED_WATCH(
          d->u.hrd.hrd_exp, HVI_DOWNWARD, &flag_umprimed_also
        )) {
      local_exp = d->u.hrd.hrd_exp;
      if (flag_umprimed_also) {
        for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	  child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
            EXP_DOWNWARD = local_exp;
	    COEFF_DOWNWARD = local_coeff;
	    UB_NUMERATOR_DOWNWARD = d->u.hrd.arc[ci].ub_numerator;
	    UB_DENOMINATOR_DOWNWARD = d->u.hrd.arc[ci].ub_denominator;
	    grown_child = rec_hybrid_bypass_given_DOWNWARD_FOR_PRIMED(child);
	    child = grown_child;
	    child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				          d->u.hrd.arc[ci].ub_numerator,
				          d->u.hrd.arc[ci].ub_denominator
				          );
	  }
	  result = red_bop(OR, result, child);
        }
      }
      else {
        for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	  child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
            EXP_DOWNWARD = local_exp;
	    COEFF_DOWNWARD = local_coeff;
	    UB_NUMERATOR_DOWNWARD = d->u.hrd.arc[ci].ub_numerator;
	    UB_DENOMINATOR_DOWNWARD = d->u.hrd.arc[ci].ub_denominator;
	    /* since there is no corresponding umprimed variable, we don't have
	     * to watch for the unwanted matchup of x-x' with -x+x'
	     */
	    grown_child = rec_hybrid_bypass_given_DOWNWARD(child);
	    child = grown_child;
	    child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				          d->u.hrd.arc[ci].ub_numerator,
				          d->u.hrd.arc[ci].ub_denominator
				          );
	  }
	  result = red_bop(OR, result, child);
        }
      }
      UB_NUMERATOR_DOWNWARD = HYBRID_POS_INFINITY;
      UB_DENOMINATOR_DOWNWARD = 1;
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
	child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
	child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(
        child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(
        child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_bypass_DOWNWARD_FOR_PRIMED() */






struct red_type	*hybrid_bypass_DOWNWARD_FOR_PRIMED(w, vi)
     int	w, vi;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  HVI_DOWNWARD = vi;
  result = rec_hybrid_bypass_DOWNWARD_FOR_PRIMED(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_bypass_DOWNWARD_FOR_PRIMED() */





struct hrd_exp_type	*hrd_exp_negative(he)
	struct hrd_exp_type	*he;
{
  struct hrd_exp_type	*newhe;
  int			ti;

  newhe = hrd_exp_alloc(he->status & MASK_HYBRID_LENGTH);
  for (ti = 0; ti < (he->status & MASK_HYBRID_LENGTH); ti++) {
    newhe->hrd_term[ti].var_index = he->hrd_term[ti].var_index;
    newhe->hrd_term[ti].coeff = -1*he->hrd_term[ti].coeff;
  }
  newhe->name = linear_name(newhe->hrd_term, (he->status & MASK_HYBRID_LENGTH));
  newhe = hrd_exp_share(newhe);
  newhe->status = he->status;
  return(newhe);
}
/* hrd_exp_negative() */



#define	TIME_BACKWARD	1

struct hrd_exp_type	*hrd_exp_permute(he, viptr, pi, pj)
	struct hrd_exp_type	*he;
	int			*viptr, pi, pj;
{
  int			len, vi, vj, pm;
  struct hrd_exp_type	*newhe;

  len = he->status & MASK_HYBRID_LENGTH;
  newhe = hrd_exp_alloc(len);
  for (vj = 0; vj < len; vj++) {
    newhe->hrd_term[vj].coeff = he->hrd_term[vj].coeff;
    newhe->hrd_term[vj].var_index = he->hrd_term[vj].var_index;
  }

  pm = 0;
  for (vj = 0; vj < len; vj++) {
    vi = newhe->hrd_term[vj].var_index;
    if (VAR[vi].PROC_INDEX == pi)
      newhe->hrd_term[vj].var_index = variable_index[VAR[vi].TYPE][pj][VAR[vi].OFFSET];
    else if (VAR[vi].PROC_INDEX == pj)
      newhe->hrd_term[vj].var_index = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];

    if (VAR[newhe->hrd_term[vj].var_index].PROC_INDEX > pm)
      pm = VAR[newhe->hrd_term[vj].var_index].PROC_INDEX;
  }
  *viptr = variable_index[TYPE_HRD][pm][0];

  for (vi = 0; vi < len-1; vi++)
    for (vj = vi+1; vj < len; vj++)
      if (newhe->hrd_term[vi].var_index > newhe->hrd_term[vj].var_index) {
        int	t;

	t = newhe->hrd_term[vi].var_index;
	newhe->hrd_term[vi].var_index = newhe->hrd_term[vj].var_index;
	newhe->hrd_term[vj].var_index = t;

	t = newhe->hrd_term[vi].coeff;
	newhe->hrd_term[vi].coeff = newhe->hrd_term[vj].coeff;
	newhe->hrd_term[vj].coeff = t;
      }

  newhe->name = linear_name(newhe->hrd_term, len);
  newhe = hrd_exp_share(newhe);
  newhe->status = (hybrid_variable_index(newhe) * MASK_HYBRID_VI_BASE)
		| (newhe->status & ~MASK_HYBRID_LIFTED_VI);

  newhe->status = newhe->status | (he->status & FLAG_DELTA_GENERATED);
  return(newhe);
}
/* hrd_exp_permute() */




int	HB_CONSTANT_REPLACE_VI, HB_CONSTANT_REPLACE_BN, HB_CONSTANT_REPLACE_BD;


struct hrd_exp_type	*hrd_exp_constant_replace(he, vi, bn, bd, abn_ptr, abd_ptr, divider_ptr)
	struct hrd_exp_type	*he;
	int			vi, bn, bd, *abn_ptr, *abd_ptr, *divider_ptr;
{
  int	len, ti;

  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++) {
    if (he->hrd_term[ti].var_index == vi)
      break;
  }

  if (ti >= len) {
    *abn_ptr = 0;
    *abd_ptr = 1;
    *divider_ptr = 1;
    return(he);
  }
  else {
    struct hrd_term_link_type	*tlist;
    int				tc;
    struct hrd_exp_type		*newhe;

    for (tlist = NULL, tc = 0, ti = len-1; ti >= 0; ti--)
      if (he->hrd_term[ti].var_index != vi) {
        tlist = hrd_term_insert(tlist, he->hrd_term[ti].var_index,
				he->hrd_term[ti].coeff, 1, &tc
				);
      }
      else {
	*abn_ptr = he->hrd_term[ti].coeff * -1 * bn;
      }
    len = gcd(*abn_ptr, bd);
    *abn_ptr = (*abn_ptr) / len;
    *abd_ptr = bd / len;
    newhe = hrd_exp_new(tlist, tc, &ti, divider_ptr);
    free_hrd_term_list(tlist);
/*
    if (!newhe)
      bk(); 
*/
/*
    if (newhe == test_hrd_exp) {
      fprintf(RED_OUT, "Gotcha in hrd_exp_constant_replace()!\n");
      hrd_exp_print(he, 0);
      fprintf(RED_OUT, "with %1d:%s=%1d/%1d\n = ", vi, VAR[vi].NAME, bn, bd);
      hrd_exp_print(newhe, 0);
      fflush(RED_OUT);
      for (tc = 1; tc; );
    }
*/
    return(newhe);
  }
}
  /* hrd_exp_constant_replace() */




struct red_type	*rec_hybrid_specific_constant_replace(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, abn, abd, vi, bn, bd, divider, flag_hybrid_count;
  struct hrd_exp_type		*he;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_HYBRID_SPECIFIC_CONSTANT_REPLACE, d, 
    (struct hrd_exp_type *) HB_CONSTANT_REPLACE_VI, 
    HB_CONSTANT_REPLACE_BN, 
    HB_CONSTANT_REPLACE_BD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
/*
    flag_hybrid_count = ++flag_hybrid;
    fprintf(RED_OUT, "flag_hybrid_count = %1d in rec_hybrid_specific_constant_replace()\n",
	    flag_hybrid_count
	    );
    fflush(RED_OUT);

    if (flag_hybrid_count == 92) {
      fprintf(RED_OUT, "Caught!\n");
      fflush(RED_OUT);
      for (ci = 1; ci; );
    }
*/
    he = hrd_exp_constant_replace(d->u.hrd.hrd_exp, HB_CONSTANT_REPLACE_VI,
				  HB_CONSTANT_REPLACE_BN, HB_CONSTANT_REPLACE_BD,
				  &abn, &abd, &divider
				  );
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      conj = rec_hybrid_specific_constant_replace(d->u.hrd.arc[ci].child);
      bn = d->u.hrd.arc[ci].ub_numerator;
      bd = d->u.hrd.arc[ci].ub_denominator;
      if (bn != HYBRID_POS_INFINITY || bd != 1) {
        hybrid_ub_add(bn, bd, abn, abd, &bn, &bd);
	if (divider > 1) {
	  int	g;

          if (bn % 2) {
	    bn = (bn+1) / 2;
	    bd = bd * divider;
            g = gcd(bn, bd);
	    if (g > 1) {
	      bn = bn / g;
	      bd = bd / g;
	    }
	    bn = bn * 2 - 1;
          }
	  else {
	    bn = bn / 2;
	    bd = bd * divider;
	    g = gcd(bn, bd);
	    if (g > 1) {
	      bn = bn / g;
	      bd = bd / g;
	    }
	    bn = bn * 2;
	  }
	}
        conj = hrd_one_constraint(conj, he, bn, bd);
      }
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_hybrid_specific_constant_replace(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_hybrid_specific_constant_replace(d->u.dfdd.arc[ci].child),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_one_constraint(rec_hybrid_specific_constant_replace(d->u.ddd.arc[ci].child),
				     d->var_index, d->u.ddd.arc[ci].lower_bound,
				     d->u.ddd.arc[ci].upper_bound
				     );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_specific_constant_replace() */



struct red_type	*hybrid_specific_constant_replace(d, vi, bn, bd)
     struct red_type		*d;
{
  struct red_type	*result;

  if (VAR[vi].TYPE != TYPE_DENSE && VAR[vi].TYPE != TYPE_CLOCK) { 
    fprintf(RED_OUT, 
      "ERROR: a non-dense variable %1d:%s is in hybrid_specific_constant_repalce().\n", 
      vi, VAR[vi].NAME
    ); 
    bk(0); 
  } 
  
  HB_CONSTANT_REPLACE_VI = vi;
  HB_CONSTANT_REPLACE_BN = bn;
  HB_CONSTANT_REPLACE_BD = bd;
  result = rec_hybrid_specific_constant_replace(d);

  return(result);
}
/* hybrid_specific_constant_replace() */




struct red_type	*rec_hybrid_constant_replace(); 

struct red_type	*rec_hybrid_one_constant_replace(d, bn, bd)
     struct red_type	*d;
     int		bn, bd;
{
  struct red_type	*result, *conj;
  int			ti, vi, ci, flag_hybrid_count;
  struct hrd_exp_type	*ohe;

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  result = NORM_FALSE;
  for (ci = 0; ci < d->u.hrd.child_count; ci++) {
    if (   d->u.hrd.arc[ci].ub_numerator + bn == 0
	&& d->u.hrd.arc[ci].ub_denominator == bd
	)
      conj = hybrid_specific_constant_replace(
        d->u.hrd.arc[ci].child,
	d->u.hrd.hrd_exp->hrd_term[0].var_index,
	-1*bn, bd
      );
    else
      conj = d->u.hrd.arc[ci].child;
    conj = rec_hybrid_constant_replace(conj);
    conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				 d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
    result = red_bop(OR, result, conj);
  }
  return(result);
}
/* rec_hybrid_one_constant_replace() */




struct red_type	*rec_hybrid_constant_replace(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ti, vi, ci;
  struct hrd_exp_type		*ohe;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_HYBRID_CONSTANT_REPLACE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    ohe = d->u.hrd.hrd_exp;
    if (   (ohe->status & MASK_HYBRID_LENGTH) == 1 
        && ohe->hrd_term[0].coeff == -1
        ) {
      struct hrd_exp_type	*she;

      result = NORM_FALSE;
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        if (   !(d->u.hrd.arc[ci].ub_numerator % 2)
	    &&  VAR[d->u.hrd.arc[ci].child->var_index].TYPE == TYPE_HRD
	    && ((she = d->u.hrd.arc[ci].child->u.hrd.hrd_exp)->status & MASK_HYBRID_LENGTH) == 1
	    && she->hrd_term[0].var_index == ohe->hrd_term[0].var_index
	    && she->hrd_term[0].coeff == 1
	    ) {
          conj = rec_hybrid_one_constant_replace(d->u.hrd.arc[ci].child,
						 d->u.hrd.arc[ci].ub_numerator,
						 d->u.hrd.arc[ci].ub_denominator
						 );
	}
	else
	  conj = rec_hybrid_constant_replace(d->u.hrd.arc[ci].child);
	conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
        result = red_bop(OR, result, conj);
      }
    }
    else {
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = rec_hybrid_constant_replace(d->u.hrd.arc[ci].child);
        conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
        result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_FLOAT:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_hybrid_constant_replace(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_hybrid_constant_replace(d->u.dfdd.arc[ci].child),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    result = NORM_FALSE;
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_one_constraint(rec_hybrid_constant_replace(d->u.ddd.arc[ci].child),
				     d->var_index, d->u.ddd.arc[ci].lower_bound,
				     d->u.ddd.arc[ci].upper_bound
				     );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_constant_replace() */



struct red_type	*hybrid_constant_replace(d)
     struct red_type		*d;
{
  struct red_type	*result;

/*
  fprintf(RED_OUT, "\n***************************************\n"); 
  fprintf(RED_OUT, "hybrid_constant_replace() with input:\n"); 
  red_print_graph(d); 
*/  
  result = rec_hybrid_constant_replace(d);
/*
  fprintf(RED_OUT, "hybrid_constant_replace() with output:\n"); 
  red_print_graph(result); 
*/
  return(result);
}
/* hybrid_constant_replace() */




void	hybrid_delta_coeff_without_interval_rate(he, delta_numerator_ptr, delta_denominator_ptr)
	struct hrd_exp_type	*he;
	int			*delta_numerator_ptr, *delta_denominator_ptr;
{
  int	i, vi, pi, coeff, dn, dd, len;

  *delta_numerator_ptr = 0;
  *delta_denominator_ptr = 1;

  len = he->status & MASK_HYBRID_LENGTH;
  for (i = 0; i < len; i++) {
    vi = he->hrd_term[i].var_index;
    if (VRATE[vi].lb_denominator == RATE_DONT_CARE) {
      fprintf(RED_OUT, "Error 1: how come you are using an unspecified rate of variable %s.\n",
	      VAR[vi].NAME
	      );
      bk("a"); 
      fflush(RED_OUT);
      exit(0);
    }
    else if (   (   VRATE[vi].lb_numerator != VRATE[vi].ub_numerator
                 || VRATE[vi].lb_denominator != VRATE[vi].ub_denominator
		 )
	     && ( i+1 >= len
	         || he->hrd_term[i+1].var_index != vi+1
		 )
	     ) {
      *delta_numerator_ptr = 0;
      *delta_denominator_ptr = 1;
      return;
    }
    else /* if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
	     && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
	     )
	 */ {
      coeff = he->hrd_term[i].coeff;
      dn = *delta_numerator_ptr;
      dd = *delta_denominator_ptr;
      if (coeff > 0) {
        *delta_numerator_ptr
	= dn * VRATE[vi].ub_denominator
	+ coeff * VRATE[vi].ub_numerator * dd;
        *delta_denominator_ptr = dd * VRATE[vi].ub_denominator;
      }
      else {
        *delta_numerator_ptr
	= dn * VRATE[vi].lb_denominator
	+ coeff * VRATE[vi].lb_numerator * dd;
        *delta_denominator_ptr = dd * VRATE[vi].lb_denominator;
      }
      prime_effect(delta_numerator_ptr, delta_denominator_ptr);
    }
  }
/*
  if (ITERATION_COUNT == 1 && ITERATE_SXI == 0) {
    fprintf(RED_OUT, "\nin hybrid_delta_coeff for: ");
    hrd_exp_print(he, 0);
    fprintf(RED_OUT, "delta coeff = %1d/%1d.\n", *delta_numerator_ptr, *delta_denominator_ptr);
    fflush(RED_OUT);
  }
*/
}
/* hybrid_delta_coeff_without_interval_rate() */



void	hybrid_delta_coeff(he, delta_numerator_ptr, delta_denominator_ptr)
	struct hrd_exp_type	*he;
	int			*delta_numerator_ptr, *delta_denominator_ptr;
{
  int	i, vi, pi, coeff, dn, dd, len;

  *delta_numerator_ptr = 0;
  *delta_denominator_ptr = 1;

  len = he->status & MASK_HYBRID_LENGTH;
  for (i = 0; i < len; i++) {
    vi = he->hrd_term[i].var_index;
    if (VRATE[vi].lb_denominator == RATE_DONT_CARE) {
      fprintf(RED_OUT, "Error 2: how come you are using an unspecified rate of variable %s.\n",
	      VAR[vi].NAME
	      );
      bk("a"); 
      fflush(RED_OUT);
      exit(0);
    }
    else /* if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
	     && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
	     )
	 */ {
      coeff = he->hrd_term[i].coeff;
      dn = *delta_numerator_ptr;
      dd = *delta_denominator_ptr;
      if (coeff > 0) {
        *delta_numerator_ptr
	= dn * VRATE[vi].ub_denominator
	+ coeff * VRATE[vi].ub_numerator * dd;
        *delta_denominator_ptr = dd * VRATE[vi].ub_denominator;
      }
      else {
        *delta_numerator_ptr
	= dn * VRATE[vi].lb_denominator
	+ coeff * VRATE[vi].lb_numerator * dd;
        *delta_denominator_ptr = dd * VRATE[vi].lb_denominator;
      }
      prime_effect(delta_numerator_ptr, delta_denominator_ptr);
    }
  }
/*
  if (ITERATION_COUNT == 1 && ITERATE_SXI == 0) {
    fprintf(RED_OUT, "\nin hybrid_delta_coeff for: ");
    hrd_exp_print(he, 0);
    fprintf(RED_OUT, "delta coeff = %1d/%1d.\n", *delta_numerator_ptr, *delta_denominator_ptr);
    fflush(RED_OUT);
  }
*/
}
/* hybrid_delta_coeff() */




struct red_type	*rec_hybrid_relative_eliminate(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_HYBRID_RELATIVE_ELIMINATE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: This should not happen in a hybrid_relative_eliminate() with hybrid systems.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
    break;
  case TYPE_HRD:
    ci = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    if (ci > 1 && VAR[d->u.hrd.hrd_exp->hrd_term[ci-2].var_index].PROC_INDEX) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_relative_eliminate(d->u.hrd.arc[ci].child);
	result = red_bop(OR, result, conj);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_relative_eliminate(d->u.hrd.arc[ci].child);
	hchild_stack_push(conj, d->u.hrd.arc[ci].ub_numerator,
		       d->u.hrd.arc[ci].ub_denominator
		       );
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break;

  case TYPE_FLOAT:
    child_stack_level_push(); 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = rec_hybrid_relative_eliminate(d->u.fdd.arc[ci].child); 
      fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound 
      );
    } 
    result = fdd_new(d->var_index); 
    break;

  case TYPE_DOUBLE:
    child_stack_level_push(); 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = rec_hybrid_relative_eliminate(d->u.dfdd.arc[ci].child); 
      dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound 
      );
    } 
    result = dfdd_new(d->var_index); 
    break;

  default:
    child_stack_level_push(); 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = rec_hybrid_relative_eliminate(d->u.ddd.arc[ci].child); 
      ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			d->u.ddd.arc[ci].upper_bound 
			);
    } 
    result = ddd_new(d->var_index); 
  }
  return(ce->result = result); 
}
/* rec_hybrid_relative_eliminate() */





struct red_type	*hybrid_relative_eliminate(d)
     struct red_type		*d;
{
  struct red_type	*result;

  result = rec_hybrid_relative_eliminate(d);

  return(result);
}
/* hybrid_relative_eliminate() */





/***********************************************************************
*
*	Note that to contain the proliferation of the constraints,
*	normal crossing of a constraint exp with ax-bx'+E or -ax+bx'+E is forbidden.
*	Crossing of such literals is only administered at mode processing.
*/
struct hrd_exp_type	*DELTA_HRD_EXP;
int			DELTA_NUMERATOR, DELTA_DENOMINATOR,
			DELTA_BN_NUMERATOR, DELTA_BN_DENOMINATOR;
int			DELTA_DIRECTION;


struct red_type	*rec_hybrid_time_cross_given(d, e)
     struct red_type	*d, *e;
{
  struct red_type		*result, *conj, *ne;
  int				ci, dn, dd;
  struct cache10_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache10_check_result_key(
    OP_HYBRID_TIME_CROSS_GIVEN, 
    d, 
    DELTA_HRD_EXP, 
    DELTA_BN_NUMERATOR, 
    DELTA_BN_DENOMINATOR, 
    (struct hrd_exp_type *) e, 
    DELTA_NUMERATOR,  
    DELTA_DENOMINATOR, 
    (struct hrd_exp_type *) DELTA_DIRECTION, 
    0, 0 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    hybrid_delta_coeff_without_interval_rate(d->u.hrd.hrd_exp, &dn, &dd);
    if (dn * DELTA_NUMERATOR < 0) {
      int			hrd_vi, divider, bn, bd, BN, BD, new_n, new_d;
      struct hrd_exp_type	*newhe;

      newhe = hrd_exp_add(DELTA_HRD_EXP, abs(DELTA_NUMERATOR), DELTA_DENOMINATOR,
			  d->u.hrd.hrd_exp, abs(dn), dd, &hrd_vi, &divider
			  );
      if (newhe == NULL) {
        for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
          bn = d->u.hrd.arc[ci].ub_numerator;
	  bd = d->u.hrd.arc[ci].ub_denominator;
	  if (bn != HYBRID_POS_INFINITY || bd != 1) {
	    rational_lift(&bn, &bd, abs(DELTA_NUMERATOR * dd));

	    BN = DELTA_BN_NUMERATOR;
	    BD = DELTA_BN_DENOMINATOR;
	    rational_lift(&BN, &BD, abs(dn * DELTA_DENOMINATOR));

	    hybrid_ub_add(bn, bd, BN, BD, &new_n, &new_d);
            if (new_n >= 0) {
	      conj = rec_hybrid_time_cross_given(d->u.hrd.arc[ci].child, e);
	      conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	      result = red_bop(OR, result, conj);
	    }
	    else
	      break;
	  }
	  else {
	    conj = rec_hybrid_time_cross_given(d->u.hrd.arc[ci].child, e);
	    result = red_bop(OR, result, conj);
	  }
	}
      }
      else {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	  conj = rec_hybrid_time_cross_given(d->u.hrd.arc[ci].child, e);
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
	    bn = d->u.hrd.arc[ci].ub_numerator;
	    bd = d->u.hrd.arc[ci].ub_denominator * divider;
	    rational_lift(&bn, &bd, abs(DELTA_NUMERATOR * dd));

	    BN = DELTA_BN_NUMERATOR;
	    BD = DELTA_BN_DENOMINATOR * divider;
	    rational_lift(&BN, &BD, abs(dn * DELTA_DENOMINATOR));

	    hybrid_ub_add(bn, bd, BN, BD, &new_n, &new_d);
/*
              if (ITERATION_COUNT == 6 && ITERATE_SXI == 3) {
	        fprintf(RED_OUT, "\n===[Delta transitivity]========\n");
	        fprintf(RED_OUT, "hex: ");
	        hrd_exp_print(DELTA_HRD_EXP, 0);
		fprintf(RED_OUT, "%1d/%1d lifted to %1d/%1d.\n",
			DELTA_BN_NUMERATOR,
			DELTA_BN_DENOMINATOR,
			BN, BD
			);
	        fprintf(RED_OUT, "hey: ");
	        hrd_exp_print(d->u.hrd.hrd_exp, 0);
		fprintf(RED_OUT, "%1d/%1d lifted to %1d/%1d.\n",
			d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator,
			bn, bd
			);
	        fprintf(RED_OUT, "generates: ");
	        hrd_exp_print(newhe, 0);
		fprintf(RED_OUT, "new bound %1d/%1d\n", new_n, new_d);
	        fflush(RED_OUT);
	      }
*/
	    conj = hrd_one_constraint(conj, newhe, new_n, new_d);
/*
	      if (ITERATION_COUNT == 6 && ITERATE_SXI == 3) {
	        fprintf(RED_OUT, "\n-----------------------------\nCrossing :\n");
	        hrd_exp_print(DELTA_HRD_EXP, 0);
	        fprintf(RED_OUT, "at %1d/%1d with delta coeff =%1d/%1d\n",
		    DELTA_BN_NUMERATOR, DELTA_BN_DENOMINATOR, DELTA_NUMERATOR, DELTA_DENOMINATOR
		    );
	        hrd_exp_print(d->u.hrd.hrd_exp, 0);
	        fprintf(RED_OUT, "at %1d/%1d with delta coeff =%1d/%1d\n",
		    d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator,
		    dn, dd
		    );
	        fprintf(RED_OUT, "generating: \n");
	        hrd_exp_print(newhe, 0);
	        fprintf(RED_OUT, "at %1d/%1d\n\n", new_n, new_d);
	      }
*/
	    conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
	  }
	  result = red_bop(OR, result, conj);
	}
      }
    }
    else for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      conj = rec_hybrid_time_cross_given(d->u.hrd.arc[ci].child, e);
      conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) { 
      conj = fdd_one_constraint(
        rec_hybrid_time_cross_given(d->u.fdd.arc[ci].child, e),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) { 
      conj = dfdd_one_constraint(
        rec_hybrid_time_cross_given(d->u.dfdd.arc[ci].child, e),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      int			mi, ri, vi, pi;
      struct hrd_exp_type	*newhe;

      pi = VAR[d->var_index].PROC_INDEX;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (pi)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    if (   VRATE[vi].lb_denominator != RATE_DONT_CARE
	        && (   VRATE[vi].lb_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
		    || VRATE[vi].lb_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
		    || VRATE[vi].ub_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
		    || VRATE[vi].ub_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
		    )
		) {
	      fprintf(RED_OUT, "\nError: a dense variable rate conflict !\n");
	      bk(); 
	    }
	    switch (DELTA_DIRECTION) {
	    case TIME_FORWARD:
	      VRATE[vi].lb_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      VRATE[vi].ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      break;
	    case TIME_BACKWARD:
	      VRATE[vi].lb_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      VRATE[vi].ub_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      break;
	    }
	  }
	  ne = ddd_lone_subtree(e, 
	    variable_index[TYPE_DISCRETE][PROCESS_COUNT-VAR[d->var_index].PROC_INDEX+1][VAR[d->var_index].OFFSET], 
	    mi, mi 
	  ); 
	  conj = rec_hybrid_time_cross_given(d->u.ddd.arc[ci].child, ne);
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (pi)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    VRATE[vi].lb_numerator = RATE_DONT_CARE;
	    VRATE[vi].lb_denominator = RATE_DONT_CARE;
	    VRATE[vi].ub_numerator = RATE_DONT_CARE;
	    VRATE[vi].ub_denominator = RATE_DONT_CARE;
	  }
	  conj = ddd_one_constraint(conj, d->var_index, mi, mi);

          result = red_bop(OR, result, conj);
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_one_constraint(
          rec_hybrid_time_cross_given(d->u.ddd.arc[ci].child, e),
	  d->var_index, d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_time_cross_given() */





struct red_type	*red_hybrid_time_cross_given(d, he, bn, bd, dn, dd)
     struct red_type		*d;
     struct hrd_exp_type	*he;
     int			dn, dd;
{
  struct red_type	*result;

  DELTA_HRD_EXP = he; 
  DELTA_BN_NUMERATOR = bn; 
  DELTA_BN_DENOMINATOR = bd; 
  DELTA_NUMERATOR = dn; 
  DELTA_DENOMINATOR = dd; 
  result = rec_hybrid_time_cross_given(d, NORM_NO_RESTRICTION); 

  return(result);
}
/* red_hybrid_time_cross_given() */




int	HAW;

struct red_type	*red_action_hybrid_nonrecursive() {
  int				ha_result, tlcm, tgcd, tc, ti, g;
  struct hrd_term_link_type	*tlist, *t;
  struct hrd_exp_type		*newhe;
  struct red_type		*leq_hybrid, *geq_hybrid;

  RT[ha_result = RT_TOP++] = RT[HAW];
  if (!(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)) {
    RT[ha_result] = hybrid_bypass_DOWNWARD(ha_result, w_hybrid_vi[0]);
    RT[ha_result] = red_variable_eliminate(RT[ha_result], w_hybrid_vi[0]);
  }
  /* do leq_hybrid */
  for (tlist = NULL, tc = 0, ti = W_TERM_COUNT-1; ti >= 0; ti--)
    tlist = hrd_term_insert(tlist, w_hybrid_vi[ti], w_hybrid_coeff_numerator[ti],
			    w_hybrid_coeff_denominator[ti], &tc
			    );
  newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
  leq_hybrid = hrd_atom(newhe,
			   2*tlcm*w_hybrid_offset_numerator, tgcd * w_hybrid_offset_denominator
			   );
  /* do geq_hybrid */
  for (t = tlist; t; t = t->next_hrd_term_link) {
    t->coeff_numerator = -1 * t->coeff_numerator;
  }
  newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
  free_hrd_term_list(tlist);

  geq_hybrid = hrd_atom(
    newhe,
    (-2*tlcm*w_hybrid_offset_numerator/g), 
    tgcd * w_hybrid_offset_denominator/g
  );
  RT[ha_result] = red_bop(AND, RT[ha_result], red_bop(AND, leq_hybrid, geq_hybrid));
  if (GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS) {
    RT[ha_result] = hybrid_bypass_DOWNWARD(ha_result, w_hybrid_vi[0]);
    RT[ha_result] = red_variable_eliminate(RT[ha_result], w_hybrid_vi[0]);
  }
  if (VAR[w_hybrid_vi[0]].TYPE == TYPE_CLOCK) {
    RT[ha_result] = hrd_one_constraint(
      RT[ha_result],
      HE_CLOCK_LB[VAR[w_hybrid_vi[0]].U.CLOCK.CLOCK_INDEX], 0, 1
    );
  }
  RT_TOP--; /* ha_result */
  return(RT[ha_result]);
}
  /* red_action_hybrid_nonrecursive() */




/* replace every occurrence of w_sum_vi[0] by
 * (w_sum_coeff_denominator[0]/w_sum_coeff_numerator[0])*
	(w_offset_numerator / w_offset_denominator
	- sum_{i>=1} w_sum_coeff_numerator[i]*w_sum_vi[i]/w_sum_coeff_denominator[i]
	)
 */


struct hrd_exp_type	*HYBRID_REPLACE_HE; 
int			HYBRID_REPLACE_LCM, HYBRID_REPLACE_GCD; 

struct red_type	*rec_hybrid_replace(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  struct ddd_child_type		*ic;
  int				ci, num, den, tc, ti, tj, tlcm, tgcd, new_tc;
  struct hrd_term_link_type	*tlist;
  struct hrd_exp_type		*newhe;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_HYBRID_REPLACE, d, 
    HYBRID_REPLACE_HE, 
    HYBRID_REPLACE_LCM, 
    HYBRID_REPLACE_GCD 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    for (tc = (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH), ti = 0; ti < tc; ti++)
      if (d->u.hrd.hrd_exp->hrd_term[ti].var_index == w_hybrid_vi[0])
        break;
    if (ti == tc) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_replace(d->u.hrd.arc[ci].child);
	conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
	result = red_bop(OR, result, conj);
      }
    }
    else {
      for (tlist = NULL, new_tc = 0, tj = tc-1; tj >= 0; tj--)
        if (tj != ti) {
	  tlist = hrd_term_insert(tlist,
				  d->u.hrd.hrd_exp->hrd_term[tj].var_index,
				  d->u.hrd.hrd_exp->hrd_term[tj].coeff,
				  1,
				  &new_tc
				  );
	}
      for (tj = W_TERM_COUNT-1; tj >= 1; tj--) {
        tlist = hrd_term_insert(
          tlist, w_hybrid_vi[tj],
	  -1*w_hybrid_coeff_numerator[tj]*w_hybrid_coeff_denominator[0],
	  w_hybrid_coeff_denominator[tj]*w_hybrid_coeff_numerator[0],
	  &new_tc
	);
      }
      newhe = hrd_exp_new(tlist, new_tc, &tlcm, &tgcd);
      free_hrd_term_list(tlist);

      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_replace(d->u.hrd.arc[ci].child);
	conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
	hybrid_ub_add(d->u.hrd.arc[ci].ub_numerator,
		      d->u.hrd.arc[ci].ub_denominator,
		      -2 * w_hybrid_coeff_denominator[0] * W_ACT->offset_numerator[W_PI],
		      w_hybrid_coeff_numerator[0] * W_ACT->offset_denominator[W_PI]
		      &num, &den
		      );
	if (num % 2) {
	  num = (num+1)*tlcm - 1;
	}
	else
	  num = num*tlcm;
	den = den * tgcd;

	tgcd = gcd(num, den);
	num = num / tgcd;
	den = den / tgcd;

	conj = hrd_one_constraint(conj, newhe, num, den);
	result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_hybrid_replace(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_hybrid_replace(d->u.dfdd.arc[ci].child),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_one_constraint(rec_hybrid_replace(d->u.ddd.arc[ci].child),
				     d->var_index, d->u.ddd.arc[ci].lower_bound,
				     d->u.ddd.arc[ci].upper_bound
				     );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_replace() */



struct red_type	*red_action_hybrid_recursive(rhs_ti)
  int	rhs_ti;
{
  struct red_type		*result;
  struct hrd_exp_type		*newhe; 
  int				tj, tlcm, tgcd, new_tc;
  struct hrd_term_link_type	*tlist;

  /* Be reminded that the coeff of 1, ..., W_TERM_COUNT-1 has all been negated. */
  if (!(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)) {
    w_hybrid_coeff_numerator[0] = w_hybrid_coeff_numerator[rhs_ti];
    w_hybrid_coeff_denominator[0] = w_hybrid_coeff_denominator[rhs_ti];
    w_hybrid_coeff_numerator[rhs_ti] = 1;
    w_hybrid_coeff_denominator[rhs_ti] = 1;
  }
  tlist = NULL; 
  new_tc = 0; 
  for (tj = W_TERM_COUNT-1; tj >= 1; tj--) {
    tlist = hrd_term_insert(
      tlist, w_hybrid_vi[tj],
      w_hybrid_coeff_denominator[tj],
      w_hybrid_coeff_numerator[tj],
      &new_tc
    );
  }
  tlist = hrd_term_insert(tlist, VI_DELTA, rhs_ti); 
  HYBRID_REPLACE_HE = hrd_exp_new(
    tlist, new_tc, &HYBRID_REPLACE_LCM, &HYBRID_REPLACE_GCD
  );
  free_hrd_term_list(tlist); 
  
  result = rec_hybrid_replace(RT[HAW]);

  if (!(GSTATUS[INDEX_INFERENCE_DIRECTION] & FLAG_BCK_ANALYSIS)) {
    w_hybrid_coeff_numerator[rhs_ti] = w_hybrid_coeff_numerator[0];
    w_hybrid_coeff_denominator[rhs_ti] = w_hybrid_coeff_denominator[0];
    w_hybrid_coeff_numerator[0] = 1;
    w_hybrid_coeff_denominator[0] = 1;
  }
  if (VAR[w_hybrid_vi[0]].TYPE == TYPE_CLOCK) {
    result = hrd_one_constraint(
      result, HE_CLOCK_LB[VAR[w_hybrid_vi[0]].U.CLOCK.CLOCK_INDEX], 0, 1
    );
  }
  return(result);
}
  /* red_action_hybrid_recursive() */




struct hrd_exp_type	*hrd_exp_given_primed_replace(he, vi)
	struct hrd_exp_type	*he;
	int			vi;
{
  int			ti, tj, len;
  struct hrd_exp_type	*newhe;

  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++) {
    if (vi == he->hrd_term[ti].var_index)
      break;
  }
  if (ti >= len)
    return(he);

  newhe = hrd_exp_alloc(len);
  for (tj = 0; tj < len; tj++) {
    if (ti == tj)
      newhe->hrd_term[tj].var_index = vi+1;
    else
      newhe->hrd_term[tj].var_index = he->hrd_term[tj].var_index;

    newhe->hrd_term[tj].coeff = he->hrd_term[tj].coeff;
  }
  newhe->name = linear_name(newhe->hrd_term, len);
  newhe = hrd_exp_share(newhe);
/*
  newhe->status = newhe->status | FLAG_DELTA_GENERATED;
*/
  newhe->status = he->status;
  return(newhe);
}
  /* hrd_exp_given_primed_replace() */






struct red_type	*rec_hybrid_given_primed_replace(d)
     struct red_type	*d;
{
  struct red_type		*result, *conj;
  int				ci, dn, dd;
  struct hrd_exp_type		*newhe;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(
    OP_HYBRID_GIVEN_PRIMED_REPLACE, d, 
    (struct red_type *) HVI_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: This should not happen in a hybrid_relative_eliminate() with hybrid systems.\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
    break;
  case TYPE_HRD:
    newhe = hrd_exp_given_primed_replace(d->u.hrd.hrd_exp, HVI_DOWNWARD);
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      conj = rec_hybrid_given_primed_replace(d->u.hrd.arc[ci].child);
      conj = hrd_lone_subtree(conj, d->var_index, newhe,
				 d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_lone_subtree(
        rec_hybrid_given_primed_replace(d->u.fdd.arc[ci].child),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_lone_subtree(
        rec_hybrid_given_primed_replace(d->u.dfdd.arc[ci].child),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = ddd_lone_subtree(rec_hybrid_given_primed_replace(d->u.ddd.arc[ci].child),
				   d->var_index, d->u.ddd.arc[ci].lower_bound,
				   d->u.ddd.arc[ci].upper_bound
				   );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_given_primed_replace() */





struct red_type	*hybrid_given_primed_replace(d, vi)
     int		vi;
     struct red_type	*d;
{
  struct red_type	*result;

  HVI_DOWNWARD = vi;
  result = rec_hybrid_given_primed_replace(d);

  return(result);
}
/* hybrid_given_primed_replace() */








struct red_type	*rec_hybrid_delta_extend(d, e)
     struct red_type	*d, *e;
{
  struct red_type		*result, *conj, *ne;
  struct ddd_child_type		*ic;
  int				ci, dn, dd /*, tlcs, tcs */;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
  tlcs = TOP_LEVEL_CHILD_STACK; 
  tcs = TOP_CHILD_STACK; 
*/
  if (d->var_index == TYPE_TRUE) {
/*
    fprintf(RED_OUT, "----[entering rec_hybrid_delta_extend]----\n"); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	tlcs, tcs
    ); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK
    ); 
    red_print_graph(d); 
*/
    return(NORM_TRUE);
  }
  else if (d->var_index == TYPE_FALSE) {
/*
    fprintf(RED_OUT, "----[entering rec_hybrid_delta_extend]----\n"); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	tlcs, tcs
    ); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK
    ); 
    red_print_graph(d); 
*/
    return(NORM_FALSE);
  }
  ce = cache4_check_result_key(OP_HYBRID_DELTA_EXTEND, d, 
    (struct hrd_exp_type *) e, 
    DELTA_DIRECTION, 0
  ); 
  if (ce->result) {
/*
    fprintf(RED_OUT, "----[entering rec_hybrid_delta_extend, cached]----\n"); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	tlcs, tcs
    ); 
    fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
    	TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK
    ); 
    red_print_graph(d); 
*/
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    hybrid_delta_coeff(d->u.hrd.hrd_exp, &dn, &dd);
    if (dn > 0) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_delta_extend(d->u.hrd.arc[ci].child, e);
	result = red_bop(OR, result, conj);
      }
      if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1
	  && VAR[d->u.hrd.hrd_exp->hrd_term[0].var_index].TYPE == TYPE_CLOCK
	  && d->u.hrd.hrd_exp->hrd_term[0].coeff == -1
	  ) {
	result = hrd_lone_subtree(result, d->var_index, d->u.hrd.hrd_exp, 0, 1);
      }
    }
    else {
      child_stack_level_push(); 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	conj = rec_hybrid_delta_extend(d->u.hrd.arc[ci].child, e);
	hchild_stack_push(
	  conj, d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
	result = red_bop(OR, result, conj);
      }
      result = hrd_new(d->var_index, d->u.hrd.hrd_exp); 
    }
    break; 

  case TYPE_FLOAT:
    child_stack_level_push(); 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = rec_hybrid_delta_extend(d->u.fdd.arc[ci].child, e); 
      fchild_stack_push(conj, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
    }
    result = fdd_new(d->var_index);  
    break; 

  case TYPE_DOUBLE:
    child_stack_level_push(); 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = rec_hybrid_delta_extend(d->u.dfdd.arc[ci].child, e); 
      dfchild_stack_push(conj, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
    }
    result = dfdd_new(d->var_index);  
    break; 

  default:
    child_stack_level_push(); 
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      int		mi, ri, vi, pi;
      struct red_type	*ne; 

      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    pi = VAR[d->var_index].PROC_INDEX;
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (VAR[vi].PROC_INDEX)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    if (   VRATE[vi].lb_denominator != RATE_DONT_CARE
	        && (   VRATE[vi].lb_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
		    || VRATE[vi].lb_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
		    || VRATE[vi].ub_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
		    || VRATE[vi].ub_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
		    )
		) {
	      fprintf(RED_OUT, "\nError: a dense variable rate conflict !\n");
	      bk(); 
	    }
	    switch (DELTA_DIRECTION) {
	    case TIME_FORWARD:
	      VRATE[vi].lb_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      VRATE[vi].ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      break;
	    case TIME_BACKWARD:
	      VRATE[vi].lb_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      VRATE[vi].ub_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      break;
	    }
	  }
	  ne = ddd_lone_subtree(e, 
	    variable_index[TYPE_DISCRETE][PROCESS_COUNT-VAR[d->var_index].PROC_INDEX+1][VAR[d->var_index].OFFSET], 
	    mi, mi 
	  ); 
	  conj = rec_hybrid_delta_extend(d->u.ddd.arc[ci].child, ne); 
	  ichild_stack_push(conj, mi, mi);
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (pi)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    VRATE[vi].lb_numerator = RATE_DONT_CARE;
	    VRATE[vi].lb_denominator = RATE_DONT_CARE;
	    VRATE[vi].ub_numerator = RATE_DONT_CARE;
	    VRATE[vi].ub_denominator = RATE_DONT_CARE;
	  }
	}
      }
      result = ddd_new(d->var_index); 
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = rec_hybrid_delta_extend(d->u.ddd.arc[ci].child, e); 
	ichild_stack_push(conj, d->u.ddd.arc[ci].lower_bound,
			  d->u.ddd.arc[ci].upper_bound
			  );
      }
      result = ddd_new(d->var_index);  
    }
  }
/*
  fprintf(RED_OUT, "----[entering rec_hybrid_delta_extend]----\n"); 
  fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
  	tlcs, tcs
  ); 
  fprintf(RED_OUT, "top_level_child_stack=%1d, top_child_stack=%1d\n", 
  	TOP_LEVEL_CHILD_STACK, TOP_CHILD_STACK
  ); 
  red_print_graph(d); 
*/
  return(ce->result = result); 
}
/* rec_hybrid_delta_extend() */



struct red_type	*hybrid_delta_extend(d, direction)
	struct red_type	*d;
	int		direction;
{
  int			vi;
  struct red_type	*result;

  DELTA_DIRECTION = direction;
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    switch (VAR[vi].TYPE) {
    case TYPE_DENSE:
      if (VAR[vi].PROC_INDEX && !(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
        VRATE[vi].lb_numerator = RATE_DONT_CARE;
        VRATE[vi].lb_denominator = RATE_DONT_CARE;
        VRATE[vi].ub_numerator = RATE_DONT_CARE;
        VRATE[vi].ub_denominator = RATE_DONT_CARE;
      }
      else {
        VRATE[vi].lb_numerator = 0;
        VRATE[vi].lb_denominator = 1;
        VRATE[vi].ub_numerator = 0;
        VRATE[vi].ub_denominator = 1;
      }
      break;

    case TYPE_CLOCK:
      VRATE[vi].lb_numerator = -1*DELTA_DIRECTION;
      VRATE[vi].lb_denominator = 1;
      VRATE[vi].ub_numerator = -1*DELTA_DIRECTION;
      VRATE[vi].ub_denominator = 1;
      break;

    default:
      VRATE[vi].lb_numerator = 0;
      VRATE[vi].lb_denominator = 0;
      VRATE[vi].ub_numerator = 0;
      VRATE[vi].ub_denominator = 0;
    }
  }
  result = rec_hybrid_delta_extend(d, NORM_NO_RESTRICTION);

  return(result);
}
  /* hybrid_delta_extend() */








struct red_type	*rec_hybrid_delta_transitivity_for_umprimed_variables(d, e)
     struct red_type	*d, *e; 
{
  struct red_type		*result, *conj, *ne;
  struct ddd_child_type		*ic;
  int				ci, dn, dd;
  struct cache4_hash_entry_type	*ce; 

  if (d->var_index == TYPE_TRUE) 
    return(NORM_TRUE); 
  else if (d->var_index == TYPE_FALSE) 
    return(NORM_FALSE); 

  ce = cache4_check_result_key(
    OP_HYBRID_DELTA_TRANSITIVITY_FOR_UMPRIMED_VARIABLES, d, 
    (struct hrd_exp_type *) e, 
    DELTA_DIRECTION, 0 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:

    if (!(d->u.hrd.hrd_exp->status & FLAG_DELTA_GENERATED)) {
      hybrid_delta_coeff_without_interval_rate(d->u.hrd.hrd_exp, &dn, &dd);
      if (dn) {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	  conj = rec_hybrid_delta_transitivity_for_umprimed_variables(
	    d->u.hrd.arc[ci].child, e
	  );
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      ) {
	    conj = red_hybrid_time_cross_given(
	      conj, d->u.hrd.hrd_exp,
	      d->u.hrd.arc[ci].ub_numerator,
	      d->u.hrd.arc[ci].ub_denominator,
	      dn, dd
	    );
	    conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				         d->u.hrd.arc[ci].ub_numerator,
				         d->u.hrd.arc[ci].ub_denominator
				         );
	  }
	  result = red_bop(OR, result, conj);
        }
	break;
      }
    }

    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      conj = rec_hybrid_delta_transitivity_for_umprimed_variables(
        d->u.hrd.arc[ci].child, e
      );
      conj = hrd_one_constraint(conj, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[ci].ub_numerator,
				   d->u.hrd.arc[ci].ub_denominator
				   );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_one_constraint(
        rec_hybrid_delta_transitivity_for_umprimed_variables(
          d->u.fdd.arc[ci].child, e
        ),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_one_constraint(
        rec_hybrid_delta_transitivity_for_umprimed_variables(
          d->u.dfdd.arc[ci].child, e
        ),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX
	&& VAR[d->var_index].OFFSET == OFFSET_MODE
	) {
      int	mi, ri, vi, pi;

      pi = VAR[d->var_index].PROC_INDEX;
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (pi)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    if (   VRATE[vi].lb_denominator != RATE_DONT_CARE
	        && (   VRATE[vi].lb_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
		    || VRATE[vi].lb_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
		    || VRATE[vi].ub_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
		    || VRATE[vi].ub_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
		    )
		) {
	      fprintf(RED_OUT, "\nError: a dense variable rate conflict !\n");
	      bk(); 
	    }
	    switch (DELTA_DIRECTION) {
	    case TIME_FORWARD:
	      VRATE[vi].lb_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      VRATE[vi].ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      break;
	    case TIME_BACKWARD:
	      VRATE[vi].lb_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
	      VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
	      VRATE[vi].ub_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
	      VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
	      break;
	    }
	  } 
	  ne = ddd_lone_subtree(e, 
	    variable_index[TYPE_DISCRETE][PROCESS_COUNT-VAR[d->var_index].PROC_INDEX+1][VAR[d->var_index].OFFSET], 
	    mi, mi 
	  ); 
	  conj = rec_hybrid_delta_transitivity_for_umprimed_variables(
	    d->u.ddd.arc[ci].child, ne
	  );
	  conj = ddd_one_constraint(conj, d->var_index, mi, mi);

	  result = red_bop(OR, result, conj);
	  for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
	    vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
	    if (pi)
	      vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
	    VRATE[vi].lb_numerator = RATE_DONT_CARE;
	    VRATE[vi].lb_denominator = RATE_DONT_CARE;
	    VRATE[vi].ub_numerator = RATE_DONT_CARE;
	    VRATE[vi].ub_denominator = RATE_DONT_CARE;
          }
	}
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_one_constraint(
          rec_hybrid_delta_transitivity_for_umprimed_variables(
            d->u.ddd.arc[ci].child, e
          ),
	  d->var_index, d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_delta_transitivity_for_umprimed_variables() */




struct red_type	*hybrid_delta_transitivity_for_umprimed_variables(d, direction)
	struct red_type	*d;
	int		direction;
{
  int			vi;
  struct red_type	*result;

  DELTA_DIRECTION = direction;
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    switch (VAR[vi].TYPE) {
    case TYPE_DENSE:
      if (VAR[vi].PROC_INDEX && !(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
        VRATE[vi].lb_numerator = RATE_DONT_CARE;
        VRATE[vi].lb_denominator = RATE_DONT_CARE;
        VRATE[vi].ub_numerator = RATE_DONT_CARE;
        VRATE[vi].ub_denominator = RATE_DONT_CARE;
      }
      else {
        VRATE[vi].lb_numerator = 0;
        VRATE[vi].lb_denominator = 1;
        VRATE[vi].ub_numerator = 0;
        VRATE[vi].ub_denominator = 1;
      }
      break;

    case TYPE_CLOCK:
      VRATE[vi].lb_numerator = -1*DELTA_DIRECTION;
      VRATE[vi].lb_denominator = 1;
      VRATE[vi].ub_numerator = -1*DELTA_DIRECTION;
      VRATE[vi].ub_denominator = 1;
      break;

    default:
      VRATE[vi].lb_numerator = 0;
      VRATE[vi].lb_denominator = 0;
      VRATE[vi].ub_numerator = 0;
      VRATE[vi].ub_denominator = 0;
    }
  }
  result = rec_hybrid_delta_transitivity_for_umprimed_variables(
    d, NORM_NO_RESTRICTION
  );

  return(result);
}
  /* hybrid_delta_transitivity_for_umprimed_variables() */















struct red_type *rec_action_hybrid(ti)
     int	ti;
{
  int			offset, ppi, vi, vpi, tc, rppi, tj, tmp, tlcm,
			offset_numerator, offset_denominator;
  struct red_type	*result, *leq_hybrid, *geq_hybrid, *less_hybrid, *greater_hybrid,
			*rconj, *rchild;
  struct hrd_exp_type	*newhe , *newhe_leq , *newhe_geq , *newhe_less , *newhe_greater;

  if (ti == W_TERM_COUNT) {
    /* now we have reached decision on all term variables
     * now we have to construct the HRD atom
     */
    /* initialize the term coeffs and variables to the working arrays
    */
    for (tj = 0, ti = 0; ti < W_TERM_COUNT; ti++) {
      if (tj == 0 && ti > 0 && w_hybrid_vi[ti] == w_hybrid_vi[0])
        tj = ti;
    }
    /* sort the sequence of the variables in the term array
     */
    if (tj) {
      return(red_action_hybrid_recursive(tj));
    }
    else {
      return(red_action_hybrid_nonrecursive());
    }
  }
  else /* if (W_TERM[ti].operand->u.atom.indirect_count == 0) */ {
    w_hybrid_vi[ti] = get_variable_index(W_TERM[ti].operand, W_PI); 
    return(rec_action_hybrid(ti+1));
  }
/*
  else {
    rconj = red_operand_indirection(W_TERM[ti].operand, W_PI); 
    result = NORM_FALSE;
    for (ppi = 1; ppi <= PROCESS_COUNT; ppi++) {
      vpi = variable_index[W_TERM[ti].operand->type]
        [ppi][VAR[W_TERM[ti].operand->u.atom.var_index].OFFSET]; 
      rchild = red_bop(AND, rconj, ddd_atom(RHS_PI, vpi, vpi));
      rchild = red_variable_eliminate(rchild, RHS_PI);
      vi = W_TERM[ti].operand->u.atom.var_index;
      w_hybrid_vi[ti] = variable_index[VAR[vi].TYPE][ppi][VAR[vi].OFFSET];

      rchild = red_bop(AND, rchild, rec_action_hybrid(ti+1));
      result = red_bop(OR, result, rchild);
    }
    return(result);
  }
*/
}
/* rec_action_hybrid() */





struct red_type	*red_action_hybrid(W, act, pi)
     int		W, pi;
     struct action_type	*act;
{
  struct red_type	*result;
  int			i;

  W_ACT = act;
  W_TERM_COUNT = act->term_count;
  W_TERM = act->term;
  W_PI = pi;
  HAW = W;

  for (i = 0 ; i <W_TERM_COUNT;i++)
    rec_get_rationals(act->term[i].coeff, &(w_hybrid_coeff_numerator[i]),
                      &(w_hybrid_coeff_denominator[i])
                      );
  rec_get_rationals(act->offset, &w_hybrid_offset_numerator, &w_hybrid_offset_denominator);
  result = rec_action_hybrid(0);
/*
  fprintf(RED_OUT, "red_hybrid_action() for process %1d:\n", pi);
  print_parse_subformula_structure(act->lhs, 0);
  fprintf(RED_OUT, ":=");
  print_parse_subformula_structure(act->rhs_exp, 0);
  fprintf(RED_OUT, ";\nthe new red:\n");
  red_print_graph(result);
  fflush(RED_OUT);
*/
  return(result);
}
/* red_action_hybrid() */




/**************************************************************************
 *
 * 	Normalization routine by Gaussian elimination
 */

int	print_gaussian(s, M, rc, cc)
	char	*s;
	int	**M, rc, cc;
{
  int	row, col;

  fprintf(RED_OUT, "\n%s:\n", s);
  for (row = 0; row < rc; row++) {
    fprintf(RED_OUT, "|");
    for (col = 0; col < cc; col++) {
      fprintf(RED_OUT, " %3d", M[row][col]);
    }
    fprintf(RED_OUT, " |\n");
  }
  fflush(RED_OUT);
}
  /* print_gaussian() */


#define	GAUSSIAN_COMPOSE_REDUNDANCY	-1 /* for redundancy checking */
#define	GAUSSIAN_CANCEL_INCONSISTENCY	1  /* for inconsistency checking */


void	Gaussian_diagonalization(mg, row_count_ptr, column_count)
	int	**mg, *row_count_ptr, column_count;
{
  int	prow, pcol,
	col, row, true_row,
	ci,
	pivot, ocolvalue,
	tmp, g;

  /* solve the equations */
  for (prow = 0, pcol = 0; prow < *row_count_ptr && pcol < column_count; prow++, pcol++) {
    /* detect the first row with nonzero coefficient at variable i. */
    for (; pcol < column_count; pcol++) {
      true_row = -1; /* used to record the row to be used as the pivot row. */
      for (row = prow; row < *row_count_ptr; row++)
        if (mg[row][pcol] && (true_row == -1 || abs(mg[true_row][pcol]) > abs(mg[row][pcol])))
	  true_row = row;
      if (true_row != -1)
        break;
    }

    /* No more pivot available. */
    if (pcol >= column_count) {
      *row_count_ptr = prow;
      return;
    }

    /* The new pivot is at (row, pcol). */
    if (mg[true_row][pcol] < 0) {
      for (col = pcol; col < column_count; col++) {
        tmp = -1*mg[true_row][col]; mg[true_row][col] = mg[prow][col]; mg[prow][col] = tmp;
      }
    }
    else {
      for (col = pcol; col < column_count; col++) {
        tmp = mg[true_row][col]; mg[true_row][col] = mg[prow][col]; mg[prow][col] = tmp;
      }
    }

    /* use pivot to eliminate elements at column pcol of all other rows. */
    pivot = mg[prow][pcol];
    for (row = 0; row < prow; row++) {
      if (mg[row][pcol]) {
	ocolvalue = mg[row][pcol];
	g = 0; /* used to record the gcd of all coefficients. */
	for (col = 0; col < column_count; col++) {
	  mg[row][col] = mg[row][col] * pivot - mg[prow][col] * ocolvalue;
	  g = gcd(g, mg[row][col]);
	}
	if ((g = abs(g)) > 1)
	  for (g = abs(g), col = 0; col < column_count; col++)
	    mg[row][col] = mg[row][col]/g;
      }
    }
    for (row = prow+1; row < *row_count_ptr; row++) {
      if (mg[row][pcol]) {
	ocolvalue = mg[row][pcol];
	g = 0; /* used to record the gcd of all coefficients. */
	for (col = pcol; col < column_count; col++) {
	  mg[row][col] = mg[row][col] * pivot - mg[prow][col] * ocolvalue;
	  g = gcd(g, mg[row][col]);
	}
	if ((g = abs(g)) > 1)
	  for (g = abs(g), col = 0; col < column_count; col++)
	    mg[row][col] = mg[row][col]/g;
      }
    }
  }

  *row_count_ptr = prow;

  /* The diagonalized matrix. */
/*
  if (flag_hybrid == 1283403)
    print_gaussian("The diagonalized matrix", MG, MG_ROW_COUNT, MG_COL_COUNT);
*/
}
  /* Gaussian_triangularization() */



int	GCOL_TERM_INDEX[10], GCOL_TERM_COUNT[10];

int	ti_valid(ti, le, cc)
	int	*ti, *le, cc;
{
  int	col;

  for (col = 0; col < cc; col++)
    if (GCOL_TERM_INDEX[col] < GCOL_TERM_COUNT[col])
      return(TYPE_TRUE);
  return(TYPE_FALSE);
}
  /* ti_valid() */






/**********************************************************************
*
*	A valid solution is one with all nonnegatives such that
*	when flag_zcoeff is GAUSSIAN_COMPOSE_REDUNDANCY or GAUSSIAN_CANCEL_REDUNDANCY
*/

int	Gaussian_matrix_solution(ghrd_exp, ghrd_exp_count, solution, flag_zcoeff)
  struct Gaussian_hrd_exp_type	*ghrd_exp;
  int				ghrd_exp_count, *solution, flag_zcoeff;
{
  int	mvi, col, colp, ghrd_exp_max_index, g, m1, m2;
/*
  fprintf(RED_OUT, "\nGM solution: %1d.\n", ++flag_hybrid);
  fflush(RED_OUT);
*/

  for (col = 0; col < ghrd_exp_count; col++)
    GCOL_TERM_COUNT[col] = ghrd_exp[col].hrd_exp->status & MASK_HYBRID_LENGTH;

/*
  fprintf(RED_OUT, "\n===[In Gaussian matrix solution]===================\n");
  hrd_exp_print(hex, 0);
  hrd_exp_print(hey, 0);
  hrd_exp_print(hez, 0);
*/
  /* fill in the equations. */
  MG_COL_COUNT = ghrd_exp_count;
  ghrd_exp_max_index = ghrd_exp_count-1;
  /* ti is to record the current term index of the many hrd_exp.
  */
  for (col = 0; col < ghrd_exp_count; col++)
    GCOL_TERM_INDEX[col] = 0;

  /* In each iteration of the following cycle, we shall get the next smallest variable index
   * to fill in array MG.
   */
  for (MG_ROW_COUNT = 0; ti_valid(GCOL_TERM_INDEX, GCOL_TERM_COUNT, ghrd_exp_count); MG_ROW_COUNT++) {
    /* get the current working variable index in mvi */
    mvi = VARIABLE_COUNT + 1;
    /* After the completion of the following cycle, we shall get the next smallest variable index
     * yet to fill in array MG.
     */
    for (col = 0; col < ghrd_exp_count; col++)
      if (GCOL_TERM_INDEX[col] < GCOL_TERM_COUNT[col])
        if (mvi > ghrd_exp[col].hrd_exp->hrd_term[GCOL_TERM_INDEX[col]].var_index)
          mvi = ghrd_exp[col].hrd_exp->hrd_term[GCOL_TERM_INDEX[col]].var_index;

    /* Get the coefficients of the current column in the matrix.
     * colp is used to record the number of hrd_expressions participating in the
     * definition of variable mvi.
     */
    g = 0; /* used to record the gcd of all coefficients */
    for (colp = 0, col = 0; col < ghrd_exp_max_index; col++)
      if (GCOL_TERM_INDEX[col] < GCOL_TERM_COUNT[col] && mvi == ghrd_exp[col].hrd_exp->hrd_term[GCOL_TERM_INDEX[col]].var_index) {
        MG[MG_ROW_COUNT][col] = ghrd_exp[col].hrd_exp->hrd_term[GCOL_TERM_INDEX[col]].coeff;
        GCOL_TERM_INDEX[col]++;
	colp++;
	g = gcd(g, MG[MG_ROW_COUNT][col]);
      }
      else
        MG[MG_ROW_COUNT][col] = 0;

    if (   GCOL_TERM_INDEX[ghrd_exp_max_index] < GCOL_TERM_COUNT[ghrd_exp_max_index]
	&& ghrd_exp_max_index >= 0
	&& mvi == ghrd_exp[ghrd_exp_max_index].hrd_exp->hrd_term[GCOL_TERM_INDEX[ghrd_exp_max_index]].var_index
	) {
      MG[MG_ROW_COUNT][ghrd_exp_max_index] = flag_zcoeff*ghrd_exp[ghrd_exp_max_index].hrd_exp->hrd_term[GCOL_TERM_INDEX[ghrd_exp_max_index]].coeff;
      GCOL_TERM_INDEX[ghrd_exp_max_index]++;
      colp++;
      g = gcd(g, MG[MG_ROW_COUNT][ghrd_exp_max_index]);
    }
    else
      MG[MG_ROW_COUNT][ghrd_exp_max_index] = 0;
    if (colp < 2)
      return(GAUSSIAN_ZERO);

    if ((g = abs(g)) > 1)
      for (col = 0; col < ghrd_exp_count; col++)
        MG[MG_ROW_COUNT][col] = MG[MG_ROW_COUNT][col] / g;
  }

/*
  fprintf(RED_OUT, "=========[Gaussian solution]===================\n");
  for (col = 0; col < ghrd_exp_count; col++)
    hrd_exp_print(ghrd_exp[col].hrd_exp, 0);
  print_gaussian("The initial matrix", MG, MG_ROW_COUNT, ghrd_exp_count);
  if (ITERATION_COUNT == 8 && ITERATE_SXI == 12) {
  }
*/
  Gaussian_diagonalization(MG, &MG_ROW_COUNT, ghrd_exp_count);
/*
  print_gaussian("The diagonal matrix", MG, MG_ROW_COUNT, MG_COL_COUNT);
  fflush(RED_OUT);
  if (ITERATION_COUNT == 8 && ITERATE_SXI == 12) {
  }
*/

  for (col = 0; col < ghrd_exp_max_index; col++)
    if (!MG[col][col])
      return(GAUSSIAN_NONSINGULAR);
    else if (!MG[col][ghrd_exp_max_index])
      return(GAUSSIAN_ZERO);
    else if (   (MG[col][col] > 0 && MG[col][ghrd_exp_max_index] > 0)
	     || (MG[col][col] < 0 && MG[col][ghrd_exp_max_index] < 0)
	     )
      return(GAUSSIAN_NEGATIVE);
  if (ghrd_exp_max_index < MG_ROW_COUNT && MG[ghrd_exp_max_index][ghrd_exp_max_index])
    return(GAUSSIAN_ZERO);

  solution[ghrd_exp_max_index] = 1;
  for (col = 0; col < ghrd_exp_max_index; col++) {
    MG[col][col] = abs(MG[col][col]);
    MG[col][ghrd_exp_max_index] = abs(MG[col][ghrd_exp_max_index]);
    prime_effect(&(MG[col][col]), &(MG[col][ghrd_exp_max_index]));
    solution[ghrd_exp_max_index] = lcm(solution[ghrd_exp_max_index], MG[col][col]);
  }
/*
  fprintf(RED_OUT, "POSITIVE: ");
*/
  for (col = 0; col < ghrd_exp_max_index; col++) {
    solution[col] = MG[col][ghrd_exp_max_index] * (solution[ghrd_exp_max_index] / MG[col][col]);
/*
    fprintf(RED_OUT, "sol[%1d]=%1d; ", col, solution[col]);
*/
  }
/*
  fprintf(RED_OUT, "sol[%1d]=%1d;\n", ghrd_exp_max_index, solution[ghrd_exp_max_index]);
*/
  return(GAUSSIAN_POSITIVE);
}
  /* Gaussian_matrix_solution() */




int	test_Gaussian_solution() {
  struct hrd_exp_type	hex, hey, hez;
  struct hrd_term_type	xterm[4], yterm[4], zterm[4];
  int			result, mx, my, mz;

  hex.status = 2;
  hex.hrd_term = xterm;
  hex.hrd_term[0].var_index = variable_index[TYPE_DENSE][0][1];
  hex.hrd_term[0].coeff = -4;
  hex.hrd_term[1].var_index = variable_index[TYPE_CLOCK][2][0];
  hex.hrd_term[1].coeff = 1;
  hex.name = linear_name(hex.hrd_term, 2);

  hey.status = 2;
  hey.hrd_term = yterm;
  hey.hrd_term[0].var_index = variable_index[TYPE_DENSE][0][1];
  hey.hrd_term[0].coeff = -1;
  hey.hrd_term[1].var_index = variable_index[TYPE_CLOCK][2][0];
  hey.hrd_term[1].coeff = 1;
  hey.name = linear_name(hey.hrd_term, 2);

  hrd_exp_print(&hex, 0);
  hrd_exp_print(&hey, 0);
  fprintf(RED_OUT, "comp = %1d.\n", HRD_EXP_COMP(&hex, &hey));

  exit(0);

  hez.status = 2;
  hez.hrd_term = zterm;
  hez.hrd_term[0].var_index = variable_index[TYPE_DENSE][0][0];
  hez.hrd_term[0].coeff = -3;
  hez.hrd_term[1].var_index = variable_index[TYPE_DENSE][0][1];
  hez.hrd_term[1].coeff = 5;
  hez.name = linear_name(hez.hrd_term, 2);

  fprintf(RED_OUT, "Test Gaussian matrix solution with: \n");
  fprintf(RED_OUT,"hex: ");
  hrd_exp_print(&hex, 0);
  fprintf(RED_OUT, "\n");

  fprintf(RED_OUT,"hey: ");
  hrd_exp_print(&hey, 0);
  fprintf(RED_OUT, "\n");

  fprintf(RED_OUT,"hez: ");
  hrd_exp_print(&hez, 0);
  fprintf(RED_OUT, "\n");

  result = Gaussian_matrix_solution(&hex, &hey, &hez, &mx, &my, &mz);
  fprintf(RED_OUT, "\nThe answer is '%1d' with %1d hex + %1d hey = %1d hez.\n",
	  result, mx, my, mz
	  );
  fflush(RED_OUT);
  exit(0);
}
  /* test_Gaussian_solution() */






struct red_type	*rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, mx, my, mz, nx, dx, ny, dy, bn, bd, nz, dz, flag;
  struct red_type		*result, *child, *grown_child;
/*
  struct cache7_hash_entry_type	*ce; 
*/
  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);
  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return(d->result_stack->result);

/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) { 
    ce = cache7_check_result_key( 
      OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENXY_DOWNWARD, d, 
      GHE[0].hrd_exp, 
      GHE[0].ub_numerator, 
      GHE[0].ub_denominator, 
      GHE[1].hrd_exp, 
      GHE[1].ub_numerator, 
      GHE[1].ub_denominator 
    ); 
    if (ce->result) {
      return(ce->result); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[2].hrd_exp = d->u.hrd.hrd_exp;
    if (Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_CANCEL_INCONSISTENCY) == GAUSSIAN_POSITIVE) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/
      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);

      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);

      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);

      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        nz = d->u.hrd.arc[ci].ub_numerator;
        dz = d->u.hrd.arc[ci].ub_denominator;
	if (nz != HYBRID_POS_INFINITY || dz != 1) {
          rational_lift(&nz, &dz, GMultiple[2]);
	  hybrid_ub_add(bn, bd, nz, dz, &nz, &dz);
	  if (nz < 0)
	    break;
	}
        child = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(d->u.hrd.arc[ci].child);
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				 d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
        result = red_bop(OR, result, child);
      }
/*
      if (flag) {
        fprintf(RED_OUT, "result:\n");
	red_print_graph(result);
	fflush(RED_OUT);
      }
*/
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(d->u.hrd.arc[ci].child);
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) 
    return(ce->result = result); 
  else 
    return(result); 
*/
}
  /* rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD() */




struct red_type	*rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
/*
  struct cache4_hash_entry_type	*ce; 
*/
  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return(d->result_stack->result);

/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) { 
    ce = cache4_check_result_key(
      OP_HYBRID_ELIMINATE_INCONSISTENCY_GIVENX_DOWNWARD, d, 
      GHE[0].hrd_exp,
      GHE[0].ub_numerator, 
      GHE[0].ub_denominator
    ); 
    if (ce->result) {
      return(ce->result); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        red_init_result(child);
        grown_child 
        = rec_hybrid_eliminate_inconsistency_givenXY_DOWNWARD(child);
        red_clear_result(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				 d->u.hrd.arc[ci].ub_numerator,
				 d->u.hrd.arc[ci].ub_denominator
				 );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) 
    return(ce->result = result); 
  else 
    return(result); 
*/
}
  /* rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD() */




struct red_type	*rec_hybrid_eliminate_inconsistency_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
/*
  struct cache1_hash_entry_type	*ce; 
*/
  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      ) 
    return(d->result_stack->result);
/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) { 
    ce = cache1_check_result_key(
      OP_HYBRID_ELIMINATE_INCONSISTENCY_DOWNWARD, d
    ); 
    if (ce->result) {
      return(ce->result); 
    }
  } 
*/
  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_inconsistency_DOWNWARD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        red_init_result(child);
        grown_child = rec_hybrid_eliminate_inconsistency_givenX_DOWNWARD(child);
        red_clear_result(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_inconsistency_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) 
    return(d->result_stack->result = result); 
  else 
    return(result); 
}
  /* rec_hybrid_eliminate_inconsistency_DOWNWARD() */






struct red_type	*hybrid_eliminate_inconsistency_DOWNWARD(w)
     int	w;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  red_init_result(RT[w]); 
  result = rec_hybrid_eliminate_inconsistency_DOWNWARD(RT[w]);
  red_clear_result(RT[w]); 
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_eliminate_inconsistency_DOWNWARD() */



/*	Note that this reduction procedure is not supposed to be used in the presence of
* 	primed variables.
*/


struct red_type	*rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, mx, my, mz, nx, dx, ny, dy, bn, bd, nz, dz, flag;
  struct red_type		*result, *child, *grown_child;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache7_check_result_key(
    OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXY_DOWNWARD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator, 
    GHE[1].hrd_exp, 
    GHE[1].ub_numerator, 
    GHE[1].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[2].hrd_exp = d->u.hrd.hrd_exp;
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1
	&& Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(d->u.hrd.arc[ci].child);
        nz = d->u.hrd.arc[ci].ub_numerator;
        dz = d->u.hrd.arc[ci].ub_denominator;
	if (nz != HYBRID_POS_INFINITY || dz != 1) {
          rational_lift(&nz, &dz, GMultiple[2]);
/*
          if (ITERATION_COUNT == 8 && ITERATE_SXI == 12) {
            fprintf(RED_OUT, "\n===[in redundunacy elimination]=======================\n");
            fprintf(RED_OUT, "%1d * ", mx);
            hrd_exp_print(RHEX, 0);
            fprintf(RED_OUT, "%1d * ", my);
	    hrd_exp_print(RHEY, 0);
            fflush(RED_OUT);
	      fprintf(RED_OUT, "= %1d * ", mz);
	    hrd_exp_print(d->u.hrd.hrd_exp, 0);
	    fflush(RED_OUT);
          }
	  fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
	  fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
	  fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
	  fprintf(RED_OUT, "Z: %1d/%1d lifted to %1d/%1d\n", d->u.hrd.arc[ci].ub_numerator,
		  d->u.hrd.arc[ci].ub_denominator, nz, dz
		  );
*/
	  if (nz * bd < bn * dz) {
/*
	    fprintf(RED_OUT, "Not a redundancy!\n");
*/
            child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	  }
/*
	  else {
	    fprintf(RED_OUT, "A redundancy detected!\n");
	  }
*/
	}
        result = red_bop(OR, result, child);
      }
/*
      if (flag) {
        fprintf(RED_OUT, "result:\n");
	red_print_graph(result);
	fflush(RED_OUT);
      }
*/
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(d->u.hrd.arc[ci].child);
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD() */



struct red_type *HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_ATOM; 

struct red_type	*rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_givenX_DOWNWARD() */





struct red_type	*rec_hybrid_eliminate_redundancy_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_REDUNDANCY_GIVEN_DOWNWARD, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_DOWNWARD() */






struct red_type	*hybrid_eliminate_redundancy_DOWNWARD(w)
     int	w;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  result = rec_hybrid_eliminate_redundancy_DOWNWARD(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_eliminate_redundancy_DOWNWARD() */




/******************************************************************************************
*  Note only the following reduction procedures can be used to reduce HRD in the
*  presence of primed variables.
*  It is special in that it avoids to cut redundancy caused by -x+x'+... and x-x'+...
*  since such pair is not considered in the bypass_DOWNWARD_FOR_PRIMED
*  either.
*/
int	hrd_exp_pair_with_reversed_differences(hex, hey)
	struct hrd_exp_type	*hex, *hey;
{
  int	lenx, leny, tix, tiy, vix, viy;

  lenx = hex->status & MASK_HYBRID_LENGTH;
  leny = hey->status & MASK_HYBRID_LENGTH;
  for (tix = 0, tiy = 0; tix < lenx && tiy < leny; ) {
    vix = hex->hrd_term[tix].var_index;
    viy = hey->hrd_term[tiy].var_index;
    if (vix < viy)
      tix++;
    else if (vix > viy)
      tiy++;
    else if (!VAR[vix].PROC_INDEX || (VAR[vix].STATUS & FLAG_VAR_PRIMED)) {
      tix++; tiy++;
    }
    else if (tix+1 == lenx)
      return(TYPE_FALSE);
    else if (tiy+1 == leny)
      return(TYPE_FALSE);
    else if (vix+1 != hex->hrd_term[tix+1].var_index)
      tix = tix + 2;
    else if (viy+1 != hey->hrd_term[tiy+1].var_index)
      tiy = tiy + 2;
    else if (   hex->hrd_term[tix].coeff + hey->hrd_term[tiy].coeff
	     || hex->hrd_term[tix+1].coeff + hey->hrd_term[tiy+1].coeff
	     ) {
      tix = tix+2;
      tiy = tiy+2;
    }
    else
      return(TYPE_TRUE);
  }
  return(TYPE_FALSE);
}
  /* hrd_exp_pair_with_reversed_differences() */






struct red_type	*HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED_ATOM; 

struct red_type	*rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator, 
    GHE[0].ub_denominator
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (hrd_exp_pair_with_reversed_differences(GHE[0].hrd_exp, d->u.hrd.hrd_exp))
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }

    else
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[1].hrd_exp = d->u.hrd.hrd_exp;
          GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child 
          = rec_hybrid_eliminate_redundancy_givenXY_DOWNWARD(child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED() */






struct red_type	*rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_REDUNDANCY_DOWNWARD_FOR_PRIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child 
        = rec_hybrid_eliminate_redundancy_givenX_DOWNWARD_FOR_PRIMED(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED() */






struct red_type	*hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(w)
     int	w;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  result = rec_hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_eliminate_redundancy_DOWNWARD_FOR_PRIMED() */







/*	Note that this reduction procedure is not supposed to be used in the presence of
* 	primed variables.
*/
struct red_type	*ZRED_LOOKAHEAD;

struct red_type	*rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(d)
     struct red_type	*d;
{
  int				ci, mx, my, mz, nx, dx, ny, dy, bn, bd, nz, dz, flag;
  struct red_type		*result, *child, *grown_child;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(ZRED_LOOKAHEAD);
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache7_check_result_key(
    OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENXZ_LOOKAHEAD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator, 
    GHE[1].hrd_exp, 
    GHE[1].ub_numerator, 
    GHE[1].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[1].hrd_exp = d->u.hrd.hrd_exp;
    if (Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
      nz = GHE[2].ub_numerator;
      dz = GHE[2].ub_denominator;
      rational_lift(&nz, &dz, GMultiple[2]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(d->u.hrd.arc[ci].child);
	if (   child->var_index
		 == (GHE[2].hrd_exp->status & MASK_HYBRID_LIFTED_VI)/MASK_HYBRID_VI_BASE
	    && child->u.hrd.hrd_exp == GHE[2].hrd_exp
	    ) {
          ny = d->u.hrd.arc[ci].ub_numerator;
          dy = d->u.hrd.arc[ci].ub_denominator;
	  if (ny != HYBRID_POS_INFINITY || dy != 1) {
            rational_lift(&ny, &dy, GMultiple[1]);
            hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
/*
          if (ITERATION_COUNT == 8 && ITERATE_SXI == 12) {
            fprintf(RED_OUT, "\n===[in redundunacy elimination]=======================\n");
            fprintf(RED_OUT, "%1d * ", mx);
            hrd_exp_print(RHEX, 0);
            fprintf(RED_OUT, "%1d * ", my);
	    hrd_exp_print(RHEY, 0);
            fflush(RED_OUT);
	      fprintf(RED_OUT, "= %1d * ", mz);
	    hrd_exp_print(d->u.hrd.hrd_exp, 0);
	    fflush(RED_OUT);
          }
	  fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
	  fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
	  fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
	  fprintf(RED_OUT, "Z: %1d/%1d lifted to %1d/%1d\n", d->u.hrd.arc[ci].ub_numerator,
		  d->u.hrd.arc[ci].ub_denominator, nz, dz
		  );
*/
	    if (nz * bd >= bn * dz) {
/*
	      fprintf(RED_OUT, "A redundancy!\n");
*/
	      if (child->u.hrd.child_count == 1) {
		child = d->u.hrd.arc[0].child;
	      }
	      else {
		child = red_bop(OR, d->u.hrd.arc[0].child, d->u.hrd.arc[1].child);
	      }
	    }
            child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	  }
	}
        result = red_bop(OR, result, child);
      }
/*
      if (flag) {
        fprintf(RED_OUT, "result:\n");
	red_print_graph(result);
	fflush(RED_OUT);
      }
*/
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(d->u.hrd.arc[ci].child);
        child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD() */




struct red_type	*rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_ELIMINATE_REDUNDANCY_GIVENX_LOOKAHEAD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1)
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[2].hrd_exp = d->u.hrd.hrd_exp;
          GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child = rec_hybrid_eliminate_redundancy_givenXZ_LOOKAHEAD(child);
          child = grown_child;
        }
        result = red_bop(OR, result, child);
      }
    else
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
	  child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
					d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
        }
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD() */






struct red_type	*rec_hybrid_eliminate_redundancy_LOOKAHEAD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_REDUNDANCY_LOOKAHEAD, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_redundancy_LOOKAHEAD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child = rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD(child);
        child = grown_child;

        child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_LOOKAHEAD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_LOOKAHEAD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_LOOKAHEAD(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_redundancy_LOOKAHEAD() */






struct red_type	*hybrid_eliminate_redundancy_LOOKAHEAD(w)
     int	w;
{
  struct red_type	*result;
/*
  report_status("hybrid eliminate redundancy LOOKAHEAD () with input:");
  red_print_graph(RT[w]);
*/
  result = rec_hybrid_eliminate_redundancy_LOOKAHEAD(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
/*
  fprintf(RED_OUT, "\nhybrid eliminate redundancy LOOKAHEAD () with output:\n");
  red_print_graph(RT[w]);
  fprintf(RED_OUT, "\n\n\n");
*/
  return(RT[w]);
}
/* hybrid_eliminate_redundancy_LOOKAHEAD() */









/*****************************************************************
*
* 	Elimination of redundancy created by aX+bY+cE
*	Note that this reduction procedure is not supposed to be used in the presence of
* 	primed variables.
*/
int	LENX_3REDUNDANCY;
struct red_type *HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD_ATOM; 

struct red_type	*rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, ntarget, dtarget, bn, bd, flag, nx, dx, ny, dy, nz, dz;
  struct red_type		*result, *child, *grown_child;
  struct cache10_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache10_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXYZ_DOWNWARD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator, 
    GHE[1].hrd_exp, 
    GHE[1].ub_numerator, 
    GHE[1].ub_denominator,  
    GHE[2].hrd_exp, 
    GHE[2].ub_numerator, 
    GHE[2].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[3].hrd_exp = d->u.hrd.hrd_exp;
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1
	&& Gaussian_matrix_solution(GHE, 4, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
      nz = GHE[2].ub_numerator;
      dz = GHE[2].ub_denominator;
      rational_lift(&nz, &dz, GMultiple[2]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
      hybrid_ub_add(bn, bd, nz, dz, &bn, &bd);
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(d->u.hrd.arc[ci].child);
        ntarget = d->u.hrd.arc[ci].ub_numerator;
        dtarget = d->u.hrd.arc[ci].ub_denominator;
	if (ntarget != HYBRID_POS_INFINITY || dtarget != 1) {
          rational_lift(&ntarget, &dtarget, GMultiple[3]);
/*
          if (ITERATION_COUNT == 8 && ITERATE_SXI == 12) {
            fprintf(RED_OUT, "\n===[in redundunacy elimination]=======================\n");
            fprintf(RED_OUT, "%1d * ", mx);
            hrd_exp_print(RHEX, 0);
            fprintf(RED_OUT, "%1d * ", my);
	    hrd_exp_print(RHEY, 0);
            fflush(RED_OUT);
	      fprintf(RED_OUT, "= %1d * ", mz);
	    hrd_exp_print(d->u.hrd.hrd_exp, 0);
	    fflush(RED_OUT);
          }
	  fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
	  fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
	  fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
	  fprintf(RED_OUT, "Z: %1d/%1d lifted to %1d/%1d\n", d->u.hrd.arc[ci].ub_numerator,
		  d->u.hrd.arc[ci].ub_denominator, nz, dz
		  );
*/
	  if (ntarget * bd < bn * dtarget) {
/*
	    fprintf(RED_OUT, "Not a redundancy!\n");
*/
            child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	  }
/*
	  else {
	    fprintf(RED_OUT, "A redundancy detected!\n");
	  }
*/
	}
        result = red_bop(OR, result, child);
      }
/*
      if (flag) {
        fprintf(RED_OUT, "result:\n");
	red_print_graph(result);
	fflush(RED_OUT);
      }
*/
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(d->u.hrd.arc[ci].child);
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD() */




struct red_type	*HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_ATOM; 

struct red_type	*rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache7_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator, 
    GHE[1].hrd_exp, 
    GHE[1].ub_numerator, 
    GHE[1].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[2].hrd_exp = d->u.hrd.hrd_exp;
        GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(child);
        child = grown_child;
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD() */





struct red_type	*HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_ATOM;

struct red_type	*rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
/*
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1
	&& d->u.hrd.hrd_exp->hrd_term[0].var_index != GHE[0].hrd_exp->hrd_term[0].var_index
	) {
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[1].hrd_exp = d->u.hrd.hrd_exp;
          GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD(child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
/*
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
*/
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD() */






struct red_type	*rec_hybrid_eliminate_3redundancy_DOWNWARD(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache2_hash_entry_type	*ce; 
  
  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return(d);

  ce = cache2_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD, d, 
    (struct red_type *) LENX_3REDUNDANCY 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == LENX_3REDUNDANCY) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_DOWNWARD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[0].hrd_exp = d->u.hrd.hrd_exp;
          GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	  GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD(child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_DOWNWARD(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_DOWNWARD() */





struct red_type	*hybrid_eliminate_3redundancy_DOWNWARD(w, len)
     int	w, len;
{
  struct red_type	*result;

  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */  
  LENX_3REDUNDANCY = len; 
  result = rec_hybrid_eliminate_3redundancy_DOWNWARD(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_eliminate_3redundancy_DOWNWARD() */






/*************************************************************************
*
*	This one is especially designed to be used in the presence of primed variables.
*/

struct red_type	*rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache7_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENXY_DOWNWARD_FOR_PRIMED, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator, 
    GHE[1].hrd_exp, 
    GHE[1].ub_numerator, 
    GHE[1].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (hrd_exp_pair_with_reversed_differences(GHE[1].hrd_exp, d->u.hrd.hrd_exp))
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }

    else
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[2].hrd_exp = d->u.hrd.hrd_exp;
          GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child = rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD(child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED() */






struct red_type	*rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_ELIMINATE_3REDUNDANCY_GIVENX_DOWNWARD_FOR_PRIMED, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator,
    GHE[0].ub_denominator 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
/*
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1
	&& d->u.hrd.hrd_exp->hrd_term[0].var_index != GHE[0].hrd_exp->hrd_term[0].var_index
	) {
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[1].hrd_exp = d->u.hrd.hrd_exp;
          GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child = rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_FOR_PRIMED(child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
/*
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
*/
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED() */






struct red_type	*rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ELIMINATE_3REDUNDANCY_DOWNWARD_FOR_PRIMED, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[0].hrd_exp = d->u.hrd.hrd_exp;
          GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	  GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          grown_child 
          = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_FOR_PRIMED
          (child);
          child = grown_child;
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
      child = ddd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED() */






struct red_type	*hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(w)
     int	w;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  result = rec_hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED(RT[w]);
  RT[w] = result;
  garbage_collect(FLAG_GC_SILENT);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(RT[w]);
}
/* hybrid_eliminate_3redundancy_DOWNWARD_FOR_PRIMED() */






/*************************************************************************************
*	WITH COLLECTIVE REDUNDANCY ELIMINATION IN THE 2nd PASS.
*/


struct redundancy_composition_type {
  int					component_count;
  struct redundancy_collection_type	**component;
  struct redundancy_composition_type	*next_redundancy_composition;
};

struct redundancy_collection_type {
  int					vi_redundancy, depth,
					ub_numerator, ub_denominator,
					composition_count;
  struct hrd_exp_type			*hrd_exp_redundancy;
  struct redundancy_composition_type	*composition_list;
  struct redundancy_collection_type	*next_redundancy_collection;
}
  *LIST_REDUNDANCY;

int	REDUNDANCY_COLLECTION_COUNT;



struct redundancy_component_type {
  struct hrd_exp_type			*hrd_exp;
  int					vi, ub_numerator, ub_denominator;
  struct redundancy_collection_type	*redundancy_collection;
}
  REDUNDANCY_COMPONENT[10];

int	REDUNDANCY_COMPONENT_COUNT;

struct hrd_exp_type	*HE_ARD[10];
int			B_ARD[10], D_ARD[10];

int	component_compare(cc, rc, cm)
	int	cc;
	struct redundancy_component_type	*rc;
	struct redundancy_composition_type	*cm;
{
  int	ci, comp;

  if (!cm)
    return(-1);
  else if (comp = cc - cm->component_count)
    return(comp);
  else for (ci = 0; ci < cc; ci++)
    if (comp = rc[ci].redundancy_collection - cm->component[ci])
      return(comp);
  return(0);
}
  /* component_compare() */

int	rc_compare(rcmp, rc)
	struct redundancy_component_type	*rcmp;
	struct redundancy_collection_type	*rc;
{
  int	comp;

  if (!rc)
    return(-1);
  else if (comp = rcmp->vi - rc->vi_redundancy)
    return(comp);
  else if (comp = HRD_EXP_COMP(rcmp->hrd_exp, rc->hrd_exp_redundancy))
    return(comp);
  else
    return(rcmp->ub_numerator * rc->ub_denominator - rc->ub_numerator * rcmp->ub_denominator);
}
  /* rc_compare() */



/* REDUNDANCY_COMPONENT[] is only used in add_redundancy to compare 
 * the duplication of redundancy components. 
 * he[], b[], d[] together record cc components.  
 * Of the cc components, one of them is the redundancy. 
 * The redundancy is indexed with ci_redundancy.  
 * Thus ci_redundancy < cc.
 *
 * The components in the arrays are recorded according to the 
 * variable ordering. 
 */ 
void	add_redundancy(ci_redundancy, cc, he, b, d)
	int			ci_redundancy, cc, *b, *d;
	struct hrd_exp_type	**he;
{
  struct redundancy_collection_type	*trc, *lrc, *nrc;
  struct redundancy_composition_type	*cm, *cmp, dummy_head, *rcm;
  int					flag, ci, comp;

  /* First we record all redundancy components. 
   */
  REDUNDANCY_COMPONENT_COUNT = cc;
  for (ci = 0; ci < cc; ci++) {
    REDUNDANCY_COMPONENT[ci].hrd_exp = he[ci];
    REDUNDANCY_COMPONENT[ci].ub_numerator = b[ci];
    REDUNDANCY_COMPONENT[ci].ub_denominator = d[ci];
    REDUNDANCY_COMPONENT[ci].vi = (he[ci]->status & MASK_HYBRID_LIFTED_VI) / MASK_HYBRID_VI_BASE;
    REDUNDANCY_COMPONENT[ci].redundancy_collection = NULL;
  }

  /* Now we record which components have happend before in LIST_REDUNDANCY. 
   * If a component has not happend, then we create a slot in 
   * LIST_REDUNDANCY for it. 
   */
  for (lrc = LIST_REDUNDANCY, nrc = lrc->next_redundancy_collection, ci = 0;
       ci < cc;
       )
    if ((comp = rc_compare(&(REDUNDANCY_COMPONENT[ci]), nrc)) == 0) { 
    /* It has happened before, so we record it in the component array and 
     * skip to the next component. 
     */
      REDUNDANCY_COMPONENT[ci].redundancy_collection = nrc; // record the component. 
      ci++; // skip to the next component. 
      lrc = nrc; nrc = nrc->next_redundancy_collection; 
    } 
    else if (comp < 0) { 
    /* It has not happened before for sure since elements in 
     * LIST_REDUNDANCY are recorded according to the variable ordering. 
     */ 	
      /* Insert an empty redundancy collection. */ 
      trc = (struct redundancy_collection_type *) malloc(sizeof(struct redundancy_collection_type));
      trc->next_redundancy_collection = nrc;
      lrc->next_redundancy_collection = trc;
      lrc = trc;
      REDUNDANCY_COLLECTION_COUNT++;

      /* Fill in the information in the redundancy collection. 
       */
      trc->vi_redundancy = REDUNDANCY_COMPONENT[ci].vi;
      trc->hrd_exp_redundancy = REDUNDANCY_COMPONENT[ci].hrd_exp;
      trc->ub_numerator =REDUNDANCY_COMPONENT[ci].ub_numerator;
      trc->ub_denominator =REDUNDANCY_COMPONENT[ci].ub_denominator;

      /* It has not been composed yet.  
       * So we write the composition list as empty. 
       * In this procedure, only component ci_redundancy will receive 
       * any compostion information. 
       */
      trc->depth = 0;
      trc->composition_count = 0;
      trc->composition_list = NULL; 
      REDUNDANCY_COMPONENT[ci].redundancy_collection = trc;
      ci++;
    }
    else { 
    /* Not yet seen, so go to the next element in LIST_REDUNDANCY. 
     */ 
      lrc = nrc; nrc = nrc->next_redundancy_collection;
    }

  /* Now we want to add the composition information to 
   * the composition list for component ci_redundancy. 
   * We first search for identical redundancy composition. 
   * We certainly don't want the new redundancy composition information 
   * redundant. 
   *
   * Note that in the composition list of each element in LIST_REDUNDANCY, 
   * the elements in the component list are in turn elements in turn 
   * elements in LIST_REDUNDANCY.  
   */
  for (dummy_head.next_redundancy_composition
       = REDUNDANCY_COMPONENT[ci_redundancy].redundancy_collection->composition_list,
       cm = &dummy_head,
       cmp = cm->next_redundancy_composition;
       (comp = component_compare(cc, REDUNDANCY_COMPONENT, cmp)) > 0;
       cm = cmp, cmp = cmp->next_redundancy_composition
       ) ;

  /* Check if the same composition record is there. 
   */
  if (comp < 0) {
  /* The composition information is not there.  
   * So we have to insert a new composition record. 
   */
    REDUNDANCY_COMPONENT[ci_redundancy].redundancy_collection->composition_count++;
    rcm = (struct redundancy_composition_type *) 
      malloc(sizeof(struct redundancy_composition_type));
    rcm->next_redundancy_composition = cmp;
    cm->next_redundancy_composition = rcm;
    REDUNDANCY_COMPONENT[ci_redundancy].redundancy_collection->composition_list
    = dummy_head.next_redundancy_composition;

    rcm->component_count = cc;
    rcm->component = (struct redundancy_collection_type **)
      malloc(cc*sizeof(struct redundancy_collection_type));
    for (ci = 0; ci < cc; ci++) {
      rcm->component[ci] = REDUNDANCY_COMPONENT[ci].redundancy_collection;
    }
  }
}
  /* add_redundancy() */



void	add_2redundancy(ci, he0, b0, d0, he1, b1, d1, he2, b2, d2)
	struct hrd_exp_type	*he0, *he1, *he2;
	int			ci, b0, d0, b1, d1, b2, d2;
{
  HE_ARD[0] = he0;
  B_ARD[0] = b0;
  D_ARD[0] = d0;

  HE_ARD[1] = he1;
  B_ARD[1] = b1;
  D_ARD[1] = d1;

  HE_ARD[2] = he2;
  B_ARD[2] = b2;
  D_ARD[2] = d2;

  add_redundancy(ci, 3, HE_ARD, B_ARD, D_ARD);
}
  /* add_2redundancy() */





int	count_2red; 

void	rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci, ntarget, dtarget, bn, bd, flag, nx, dx, ny, dy, nz, dz;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
/*
  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else { 
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
*/
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[2].hrd_exp = d->u.hrd.hrd_exp;
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1
	&& Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	) {
      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", 
        GHE[0].ub_numerator, GHE[0].ub_denominator, nx, dx
      );
      #endif 
      
      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", 
        GHE[1].ub_numerator, GHE[1].ub_denominator, ny, dy
      );
      #endif 
      
      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", 
        GMultiple[0], GMultiple[1], bn, bd
      );
      #endif 
      
      ci = d->u.hrd.child_count-1;
      ntarget = d->u.hrd.arc[ci].ub_numerator;
      dtarget = d->u.hrd.arc[ci].ub_denominator;
      if (ntarget == HYBRID_POS_INFINITY && dtarget == 1) {
	ci--;
        ntarget = d->u.hrd.arc[ci].ub_numerator;
        dtarget = d->u.hrd.arc[ci].ub_denominator;
      }
      rational_lift(&ntarget, &dtarget, GMultiple[2]);
      if (ntarget * bd >= bn * dtarget) {
        #if RED_DEBUG_HYBRID_MODE
	fprintf(RED_OUT, "Not a redundancy!\n");
        #endif 
        
	rational_lower(&bn, &bd, GMultiple[2]);
 
        #if RED_DEBUG_HYBRID_MODE	
	fprintf(RED_OUT, "===(detected a 2-redundancy %1d)=========\n", 
	  ++count_2red
	); 
	hrd_exp_print(GHE[0].hrd_exp, 0); 
	fprintf(RED_OUT, "UB:%1d/%1d\n", GHE[0].ub_numerator, GHE[0].ub_denominator); 
	hrd_exp_print(GHE[1].hrd_exp, 0); 
	fprintf(RED_OUT, "UB:%1d/%1d\n", GHE[1].ub_numerator, GHE[1].ub_denominator); 
	hrd_exp_print(GHE[2].hrd_exp, 0); 
	fprintf(RED_OUT, "UB:%1d/%1d\n", bn, bd); 
	#endif 
	
        add_2redundancy(2,
			GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			GHE[1].hrd_exp, GHE[1].ub_numerator, GHE[1].ub_denominator,
			GHE[2].hrd_exp, bn, bd
			);
      }
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE() */


inline void	hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d)
	struct red_type	*d; 
{ 
  red_init_result(d); 
  rec_hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d);
  red_clear_result(d); 
}
  /* hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE() */ 
  
  
  


void	rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct hrd_exp_type		*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
/*
  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
*/
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
          ) {
        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE() */




inline	void	hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d) 
	struct red_type	*d; 
{ 
  red_init_result(d); 
  rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d);
  red_clear_result(d); 
}
  /* hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE() */ 
  
  
  


void	rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int				ci;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
/*
  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
*/  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE() */



inline	void	hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(d) 
	struct red_type	*d; 
{ 
  red_init_result(d); 
  rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(d); 
  red_clear_result(d); 
}
  /* hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE() */ 
  
  
  
  

void	rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct hrd_exp_type		*local_exp;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    if (hrd_exp_pair_with_reversed_differences(GHE[0].hrd_exp, d->u.hrd.hrd_exp)) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[1].hrd_exp = d->u.hrd.hrd_exp;
          GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          hybrid_eliminate_2redundancy_givenXY_DOWNWARD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
        }
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED() */



inline void	hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d) 
  struct red_type	*d; 
{ 
  red_init_result(d); 
  rec_hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d);
  red_clear_result(d); 
}
  /* hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED() */ 


void	rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        hybrid_eliminate_2redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED() */



void	add_3redundancy(ci, he0, b0, d0, he1, b1, d1, he2, b2, d2, he3, b3, d3)
	struct hrd_exp_type	*he0, *he1, *he2, *he3;
	int			ci, b0, d0, b1, d1, b2, d2, b3, d3;
{
  HE_ARD[0] = he0;
  B_ARD[0] = b0;
  D_ARD[0] = d0;

  HE_ARD[1] = he1;
  B_ARD[1] = b1;
  D_ARD[1] = d1;

  HE_ARD[2] = he2;
  B_ARD[2] = b2;
  D_ARD[2] = d2;

  HE_ARD[3] = he3;
  B_ARD[3] = b3;
  D_ARD[3] = d3;

  add_redundancy(ci, 4, HE_ARD, B_ARD, D_ARD);
}
  /* add_3redundancy() */






void	rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci, ntarget, dtarget, bn, bd, flag, nx, dx, ny, dy, nz, dz;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[3].hrd_exp = d->u.hrd.hrd_exp;
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1
	&& Gaussian_matrix_solution(GHE, 4, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
      nz = GHE[2].ub_numerator;
      dz = GHE[2].ub_denominator;
      rational_lift(&nz, &dz, GMultiple[2]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
      hybrid_ub_add(bn, bd, nz, dz, &bn, &bd);
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      ci = d->u.hrd.child_count-1;
      ntarget = d->u.hrd.arc[ci].ub_numerator;
      dtarget = d->u.hrd.arc[ci].ub_denominator;
      if (ntarget == HYBRID_POS_INFINITY && dtarget == 1) {
	ci--;
        ntarget = d->u.hrd.arc[ci].ub_numerator;
        dtarget = d->u.hrd.arc[ci].ub_denominator;
      }
      rational_lift(&ntarget, &dtarget, GMultiple[3]);
      if (ntarget * bd >= bn * dtarget) {
/*
	    fprintf(RED_OUT, "Not a redundancy!\n");
*/
	rational_lower(&bn, &bd, GMultiple[3]);
	if (!GMultiple[0]) {
          add_2redundancy(2,
			  GHE[1].hrd_exp, GHE[1].ub_numerator, GHE[1].ub_denominator,
			  GHE[2].hrd_exp, GHE[2].ub_numerator, GHE[2].ub_denominator,
			  GHE[3].hrd_exp, bn, bd
			  );
	}
	else if (!GMultiple[1]) {
          add_2redundancy(2,
			  GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			  GHE[2].hrd_exp, GHE[2].ub_numerator, GHE[2].ub_denominator,
			  GHE[3].hrd_exp, bn, bd
			  );

	}
	else if (!GMultiple[2]) {
          add_2redundancy(2,
			  GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			  GHE[1].hrd_exp, GHE[1].ub_numerator, GHE[1].ub_denominator,
			  GHE[3].hrd_exp, bn, bd
			  );
	}
	else
          add_3redundancy(3,
			  GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			  GHE[1].hrd_exp, GHE[1].ub_numerator, GHE[1].ub_denominator,
			  GHE[2].hrd_exp, GHE[2].ub_numerator, GHE[2].ub_denominator,
			  GHE[3].hrd_exp, bn, bd
			  );
      }
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE() */





void	rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return; 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[2].hrd_exp = d->u.hrd.hrd_exp;
        GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE() */






void	rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
/*
    if (   (d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) == 1
	&& d->u.hrd.hrd_exp->hrd_term[0].var_index != GHE[0].hrd_exp->hrd_term[0].var_index
	) {
*/
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[1].hrd_exp = d->u.hrd.hrd_exp;
          GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
/*
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
*/
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE() */






void	rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci;

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return;

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return;
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) <= LENX_3REDUNDANCY) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[0].hrd_exp = d->u.hrd.hrd_exp;
          GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	  GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
	  red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    d->result_stack->result = NORM_NO_RESTRICTION;
}
  /* rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE() */







void	rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct hrd_exp_type		*local_exp;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (hrd_exp_pair_with_reversed_differences(GHE[1].hrd_exp, d->u.hrd.hrd_exp)) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[2].hrd_exp = d->u.hrd.hrd_exp;
          GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_3redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED() */






void	rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
         || d->u.hrd.arc[ci].ub_denominator != 1
	 ) {
        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_3redundancy_givenXY_DOWNWARD_COLLECTIVE_FOR_PRIMED(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED() */






void	rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d)
     struct red_type	*d;
{
  int	ci;

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) <= LENX_3REDUNDANCY) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[0].hrd_exp = d->u.hrd.hrd_exp;
          GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	  GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
	  red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_3redundancy_givenX_DOWNWARD_COLLECTIVE_FOR_PRIMED(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED() */




void	add_4redundancy(ci, he0, b0, d0, he1, b1, d1, he2, b2, d2, he3, b3, d3, he4, b4, d4)
	struct hrd_exp_type	*he0, *he1, *he2, *he3, *he4;
	int			ci, b0, d0, b1, d1, b2, d2, b3, d3, b4, d4;
{
  HE_ARD[0] = he0;
  B_ARD[0] = b0;
  D_ARD[0] = d0;

  HE_ARD[1] = he1;
  B_ARD[1] = b1;
  D_ARD[1] = d1;

  HE_ARD[2] = he2;
  B_ARD[2] = b2;
  D_ARD[2] = d2;

  HE_ARD[3] = he3;
  B_ARD[3] = b3;
  D_ARD[3] = d3;

  HE_ARD[4] = he4;
  B_ARD[4] = b4;
  D_ARD[4] = d4;

  add_redundancy(ci, 5, HE_ARD, B_ARD, D_ARD);
}
  /* add_4redundancy() */




struct red_type	*HYBRID_ELIMINATE_4REDUNDANCY_GIVENXYZU_DOWNWARD_COLLECTIVE_ATOM; 

void	rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci, ntarget, dtarget, bn, bd, flag, len, nx, dx, ny, dy, nz, dz, nu, du;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;
  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[4].hrd_exp = d->u.hrd.hrd_exp;
    len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH;
    if (   len > 3
    	&& VAR[d->u.hrd.hrd_exp->hrd_term[len-3].var_index].PROC_INDEX
	&& Gaussian_matrix_solution(GHE, 5, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	&& GMultiple[0] > 0
	&& GMultiple[1] > 0
	&& GMultiple[2] > 0
	&& GMultiple[3] > 0
	&& GMultiple[4] > 0
	) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", GHE[0].ub_numerator, GHE[0].ub_denominator, nx, dx);
*/
      ny = GHE[1].ub_numerator;
      dy = GHE[1].ub_denominator;
      rational_lift(&ny, &dy, GMultiple[1]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", GHE[1].ub_numerator, GHE[1].ub_denominator, ny, dy);
*/
      nz = GHE[2].ub_numerator;
      dz = GHE[2].ub_denominator;
      rational_lift(&nz, &dz, GMultiple[2]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", GHE[2].ub_numerator, GHE[2].ub_denominator, nz, dz);
*/
      nu = GHE[3].ub_numerator;
      du = GHE[3].ub_denominator;
      rational_lift(&nu, &du, GMultiple[3]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", GHE[3].ub_numerator, GHE[3].ub_denominator, nu, du);
*/
      hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
      hybrid_ub_add(bn, bd, nz, dz, &bn, &bd);
      hybrid_ub_add(bn, bd, nu, du, &bn, &bd);
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      ci = d->u.hrd.child_count-1;
      ntarget = d->u.hrd.arc[ci].ub_numerator;
      dtarget = d->u.hrd.arc[ci].ub_denominator;
      if (ntarget == HYBRID_POS_INFINITY && dtarget == 1) {
	ci--;
        ntarget = d->u.hrd.arc[ci].ub_numerator;
        dtarget = d->u.hrd.arc[ci].ub_denominator;
      }
      rational_lift(&ntarget, &dtarget, GMultiple[4]);
      if (ntarget * bd >= bn * dtarget) {
/*
	    fprintf(RED_OUT, "Not a redundancy!\n");
*/
	rational_lower(&bn, &bd, GMultiple[4]);
        add_4redundancy(4,
			GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			GHE[1].hrd_exp, GHE[1].ub_numerator, GHE[1].ub_denominator,
			GHE[2].hrd_exp, GHE[2].ub_numerator, GHE[2].ub_denominator,
			GHE[3].hrd_exp, GHE[3].ub_numerator, GHE[3].ub_denominator,
			GHE[4].hrd_exp, bn, bd
			);
      }
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE() */





void	rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[3].hrd_exp = d->u.hrd.hrd_exp;
        GHE[3].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[3].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_4redundancy_givenXYZU_DOWNWARD_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE() */






void	rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[2].hrd_exp = d->u.hrd.hrd_exp;
        GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_4redundancy_givenXYZ_DOWNWARD_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE() */






void	rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);
  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_4redundancy_givenXY_DOWNWARD_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE() */






void	rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci;

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) <= LENX_3REDUNDANCY) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[0].hrd_exp = d->u.hrd.hrd_exp;
          GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
	  GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
	  red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_4redundancy_givenX_DOWNWARD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(d->u.hrd.arc[ci].child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE() */







struct red_type	*rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci, mx, my, mz, nx, dx, ny, dy, bn, bd, ntarget, dtarget, flag;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    GHE[1].hrd_exp = d->u.hrd.hrd_exp;
    if (   Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE
	&& GMultiple[0] > 0
	&& GMultiple[1] > 0
	&& GMultiple[2] > 0
	) {
/*
      if (flag_hybrid == 3892) {
        fprintf(RED_OUT, "d: NX=%1d/DX=%1d; NY=%1d/DY=%1d\n",
		RHEX_NUMERATOR, RHEX_DENOMINATOR,
		RHEY_NUMERATOR, RHEY_DENOMINATOR
		);
	red_print_graph(d);
	flag = TRUE;
      }
      else
        flag = FALSE;
*/

      nx = GHE[0].ub_numerator;
      dx = GHE[0].ub_denominator;
      rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
      ntarget = GHE[2].ub_numerator;
      dtarget = GHE[2].ub_denominator;
      rational_lift(&ntarget, &dtarget, GMultiple[2]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
      for (ci = d->u.hrd.child_count-1; ci>=0; ci--) {
        ny = d->u.hrd.arc[ci].ub_numerator;
        dy = d->u.hrd.arc[ci].ub_denominator;
        rational_lift(&ny, &dy, GMultiple[1]);
        hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);

        if (ntarget * bd >= bn * dtarget)
	  break;
      }
/*
	    fprintf(RED_OUT, "Not a redundancy!\n");
*/
      if (ci >= 0) {
        rational_lower(&bn, &bd, GMultiple[2]);
        add_2redundancy(1,
			GHE[0].hrd_exp, GHE[0].ub_numerator, GHE[0].ub_denominator,
			GHE[2].hrd_exp, bn, bd,
			GHE[1].hrd_exp, ny, dy
			);
      }
    }
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(d->u.hrd.arc[ci].child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE() */





struct red_type	*rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(d)
     struct red_type	*d;
{
  int	ci, local_coeff;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) > 1)
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(d->u.hrd.arc[ci].child);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
            || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          GHE[2].hrd_exp = d->u.hrd.hrd_exp;
          GHE[2].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
          GHE[2].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
          red_init_result(d->u.hrd.arc[ci].child); 
          rec_hybrid_eliminate_2redundancy_givenXZ_LOOKAHEAD_COLLECTIVE(
            d->u.hrd.arc[ci].child
          );
          red_clear_result(d->u.hrd.arc[ci].child); 
        }
      }
    else
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(d->u.hrd.arc[ci].child);
      }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_redundancy_givenX_LOOKAHEAD_COLLECTIVE() */





struct red_type	*rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(d)
     struct red_type	*d;
{
  int			ci, local_coeff;
  struct hrd_exp_type	*local_exp;

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return;

  if (d->status & MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]) {
    return;
  } 
  else {
    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    d->status = d->status & ~MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]; 
  }
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_LOOKAHEAD_COLLECTIVE().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator; 
        red_init_result(d->u.hrd.arc[ci].child); 
        rec_hybrid_eliminate_2redundancy_givenX_LOOKAHEAD_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        red_clear_result(d->u.hrd.arc[ci].child); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(d->u.ddd.arc[ci].child);
    }
  }
}
  /* rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE() */







int			VI_XRB, UBN_XRB, UBD_XRB;
struct hrd_exp_type	*HE_XRB;
struct red_type		*HYBRID_EXTRACT_BOUND_REDUNDANCY_COLLECTIVE_AOTM; 


struct red_type	*rec_hybrid_extract_bound_redundancy_COLLECTIVE(d)
     struct red_type	*d;
{
  int				ci, comp;
  struct red_type		*result, *child, *redundant_children;
  struct cache4_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      || d->var_index > VI_XRB
      || (   d->var_index == VI_XRB 
          && (comp = HRD_EXP_COMP(d->u.hrd.hrd_exp, HE_XRB)) > 0
          )
      )
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_HYBRID_EXTRACT_BOUND_REDUNDANCY_COLLECTIVE, d, 
    HE_XRB, UBN_XRB, UBD_XRB 
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (d->var_index < VI_XRB || comp < 0) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_extract_bound_redundancy_COLLECTIVE(
          d->u.hrd.arc[ci].child
        );
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
        }
        result = red_bop(OR, result, child);
      }
    }
    else {
      ci = d->u.hrd.child_count-1;
      if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	  && d->u.hrd.arc[ci].ub_denominator == 1
	  )
	ci--;
      for (; ci >= 0; ci--) {
	if (d->u.hrd.arc[ci].ub_numerator * UBD_XRB
	    >= UBN_XRB * d->u.hrd.arc[ci].ub_denominator
	    ) {
          child = hrd_lone_subtree(d->u.hrd.arc[ci].child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
          result = red_bop(OR, result, child);
        }
	else
	  break;
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_extract_bound_redundancy_COLLECTIVE(
        d->u.fdd.arc[ci].child
      );
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_extract_bound_redundancy_COLLECTIVE(
        d->u.dfdd.arc[ci].child
      );
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_extract_bound_redundancy_COLLECTIVE(
        d->u.ddd.arc[ci].child
      );
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result);
}
  /* rec_hybrid_extract_bound_redundancy_COLLECTIVE() */


void	print_redundancy_composition(cm) 
  struct redundancy_composition_type	*cm;
{	
  int	cmi; 
  
  fprintf(RED_OUT, "  [%x", (unsigned int) cm->component[0]);
  for (cmi = 1; cmi < cm->component_count; cmi++)
    fprintf(RED_OUT, ",%x", (unsigned int) cm->component[cmi]);
  fprintf(RED_OUT, "];\n");
  fflush(RED_OUT);
}
  /*print_redundancy_composition() */ 
  
  
  
void	print_redundancy_compositions(rc) 
	struct redundancy_collection_type	*rc; 
{ 
  struct redundancy_composition_type	*cm;

  fprintf(RED_OUT, "+++(%x, vi=%1d, d=%1d, ub=%1d/%1d, %1d compositions)+++++++\n",
   (unsigned int) rc, rc->vi_redundancy, rc->depth, rc->ub_numerator, rc->ub_denominator, rc->composition_count
  );
  hrd_exp_print(rc->hrd_exp_redundancy, 0);
  fprintf(RED_OUT, "  Compositions:\n");
  for (cm = rc->composition_list; cm; cm = cm->next_redundancy_composition) {
    print_redundancy_composition(cm);
  }
  fprintf(RED_OUT, "\n");
}
  /* print_redundancy_compositions() */ 
  
  
  
  
void	print_redundancy_collection(s)
	char	*s;
{
  struct redundancy_collection_type	*rc;
  fprintf(RED_OUT, "\n%s of %1d redundancy collections:\n", s, REDUNDANCY_COLLECTION_COUNT);
  for (rc = LIST_REDUNDANCY->next_redundancy_collection;
       rc;
       rc = rc->next_redundancy_collection
       ) {
    print_redundancy_compositions(rc); 
  }
}
  /* print_redundancy_collection() */






struct redundancy_collection_type	**COMPONENT_COLLECTION;
int	TARGET_COMPONENT_INDEX, 
	COMPONENT_COLLECTION_MAX, 
	COMPONENT_COLLECTION_COUNT,
	UBN_REDUNDANCY, UBD_REDUNDANCY;


/* 
 * This procedure is called to eliminate lookahead constraints. 
 * It is called when TARGET_COMPONENT_INDEX has been visited before 
 * COMPONENT_COLLECTION_MAX. 
 * Thus it is not possible to see TARGET_COMPONENT_INDEX in this procedure. 
 */

struct red_type	*rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
  d, component_index
)
     struct red_type	*d;
     int		component_index;
{
  int			ci, comp, j;
  struct red_type	*result, *child, *redundant_children;

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      || d->var_index > COMPONENT_COLLECTION[component_index]->vi_redundancy
      || (   d->var_index == COMPONENT_COLLECTION[component_index]->vi_redundancy
	  && (comp = HRD_EXP_COMP(d->u.hrd.hrd_exp,
			          COMPONENT_COLLECTION[component_index]->hrd_exp_redundancy
			          )
	      ) > 0
	  )
      ) 
    return(hrd_lone_subtree
	   (d, COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->vi_redundancy,
	    COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->hrd_exp_redundancy,
	    UBN_REDUNDANCY, UBD_REDUNDANCY
	    )
	   );

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return(d->result_stack->result);

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    comp = HRD_EXP_COMP(
      d->u.hrd.hrd_exp,
      COMPONENT_COLLECTION[component_index]->hrd_exp_redundancy
    ); 
    if (comp > 0) { 
//      red_mark(d, MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]);     	
      result = NORM_FALSE; 
    } 
    else if (comp < 0) {
      d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
          d->u.hrd.arc[ci].child,
	  component_index
	);
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
        }
        result = red_bop(OR, result, child);
      }
    }
    else if (component_index == TARGET_COMPONENT_INDEX) { 
      fprintf(RED_OUT, "Note that this is impossible since this procedure \n"); 
      fprintf(RED_OUT, "is only called when we have seen the TARGET_COMPONENT_INDEX.\n"); 
      exit(0); 
    }
    else if (component_index == COMPONENT_COLLECTION_MAX) {
//      red_mark(d, MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]); 
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        if (   (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	        || d->u.hrd.arc[ci].ub_denominator != 1
		)
	    && d->u.hrd.arc[ci].ub_numerator
	       * COMPONENT_COLLECTION[component_index]->ub_denominator
		 <= COMPONENT_COLLECTION[component_index]->ub_numerator
		    * d->u.hrd.arc[ci].ub_denominator
	    ) {
          child = hrd_lone_subtree(d->u.hrd.arc[ci].child, 
            d->var_index, d->u.hrd.hrd_exp,
	    d->u.hrd.arc[ci].ub_numerator,
	    d->u.hrd.arc[ci].ub_denominator
	  );
	  result = red_bop(OR, result, child);
	}
	else 
	  break; 
      }
    }
    else /* component_index < REDUNDANY_COMPONENT_MAX, LOOKAHEAD, THAT IS!!! */ {
//      d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
      result = NORM_FALSE;
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = d->u.hrd.arc[ci].child;
        if (   (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	        || d->u.hrd.arc[ci].ub_denominator != 1
		)
	    && d->u.hrd.arc[ci].ub_numerator
	       * COMPONENT_COLLECTION[component_index]->ub_denominator
		 <= COMPONENT_COLLECTION[component_index]->ub_numerator
		    * d->u.hrd.arc[ci].ub_denominator
	    ) {
	  child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
	    child, component_index+1
	  );
          child = hrd_one_constraint(
            child, d->u.hrd.hrd_exp,
	    d->u.hrd.arc[ci].ub_numerator,
	    d->u.hrd.arc[ci].ub_denominator
	  );
          result = red_bop(OR, child, result);
	} 
	else 
	  break; 
      }
/*
      for (; ci < d->u.hrd.child_count; ci++) { 
      	red_mark(d->u.hrd.arc[ci].child, 
      	         MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]
      	         );
      } 
*/
    }
    break;
  case TYPE_FLOAT:
//    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
        d->u.fdd.arc[ci].child, component_index
      );
      child = fdd_one_constraint(
        child, d->var_index, d->u.fdd.arc[ci].lower_bound, 
        d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
//    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
        d->u.dfdd.arc[ci].child, component_index
      );
      child = dfdd_one_constraint(
        child, d->var_index, d->u.dfdd.arc[ci].lower_bound, 
        d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
//    d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
        d->u.ddd.arc[ci].child, component_index
      );
      child = ddd_one_constraint(
        child, d->var_index, d->u.ddd.arc[ci].lower_bound, 
        d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
  }
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
/*
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK]) 
    return(d->result_stack->result = result);
*/
}
  /* rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE() */
  
  
  
#if RED_DEBUG_HYBRID_MODE
int	count_lherc = 0; 
#endif 

struct red_type	*rec_hybrid_eliminate_redundancy_COLLECTIVE(
  d, component_index
)
     struct red_type	*d;
     int		component_index;
{
  int			ci, comp, j, lhc;
  struct red_type	*result, *child, *redundant_children;

  #if RED_DEBUG_HYBRID_MODE
  lhc = ++count_lherc; 
  for (; lhc == -1; ); 
  #endif 
  
  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      || d->var_index > COMPONENT_COLLECTION[component_index]->vi_redundancy
      || (   d->var_index == COMPONENT_COLLECTION[component_index]->vi_redundancy
	  && (comp = HRD_EXP_COMP(d->u.hrd.hrd_exp,
			          COMPONENT_COLLECTION[component_index]->hrd_exp_redundancy
			          )
	      ) > 0
	  )
      )
    return(d);

  if (   (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
      && d->result_stack->result
      )
    return(d->result_stack->result);

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD: 
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (   d->var_index 
           < COMPONENT_COLLECTION[component_index]->vi_redundancy 
        || comp < 0
        ) {
    // This is not yet the component that we are looking for. 
//      d->status = d->status | MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]; 
      for (ci = 0; ci < d->u.hrd.child_count; ci++) { 
        child = rec_hybrid_eliminate_redundancy_COLLECTIVE(
          d->u.hrd.arc[ci].child, component_index 
	);
        #if RED_DEBUG_HYBRID_MODE
      	fprintf(RED_OUT, "herc_count=%1d\n", lhc); 
      	fflush(RED_OUT); 
      	#endif 
      	
        if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	    || d->u.hrd.arc[ci].ub_denominator != 1
	    ) {
          child = hrd_one_constraint(
            child, d->u.hrd.hrd_exp,
	    d->u.hrd.arc[ci].ub_numerator,
	    d->u.hrd.arc[ci].ub_denominator
	  );
        }
        result = red_bop(OR, result, child);
      }
    }
    else if (component_index == TARGET_COMPONENT_INDEX) { 
    // This is the redundancy that we are looking for 
    // since the > 0 cases are already handled in the beginning. 
      if (component_index == COMPONENT_COLLECTION_MAX) { 
      // This is not a lookahead.  
      // This is a terminal case.  
      // We do recursive procedure call no more. 
//        red_mark(d, MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]); 
        redundant_children = NORM_FALSE;
        for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
          if (   (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	          && d->u.hrd.arc[ci].ub_denominator == 1
		  )
	      || d->u.hrd.arc[ci].ub_numerator
	         * COMPONENT_COLLECTION[component_index]->ub_denominator
		   >= COMPONENT_COLLECTION[component_index]->ub_numerator
		      * d->u.hrd.arc[ci].ub_denominator
	      ) {
	    redundant_children = red_bop(OR, redundant_children, 
	      d->u.hrd.arc[ci].child
	    );
	  }
	  else {
            child = hrd_lone_subtree(d->u.hrd.arc[ci].child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
            result = red_bop(OR, result, child);
	  }
        } 
	result = red_bop(OR, redundant_children, result);
      }
      else /* component_index < REDUNDANY_COMPONENT_MAX, LOOKAHEAD, THAT IS!!! */ {
      // This is also a terminal case. 
      // No more recursive procedure call. 
        for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
          if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	      && d->u.hrd.arc[ci].ub_denominator == 1
	      )
	    child = d->u.hrd.arc[ci].child;
	  else if (d->u.hrd.arc[ci].ub_numerator
		   * COMPONENT_COLLECTION[component_index]->ub_denominator
		     >= COMPONENT_COLLECTION[component_index]->ub_numerator
		        * d->u.hrd.arc[ci].ub_denominator
		   ) {
	    UBN_REDUNDANCY = d->u.hrd.arc[ci].ub_numerator;
	    UBD_REDUNDANCY = d->u.hrd.arc[ci].ub_denominator;
	    red_init_result(d->u.hrd.arc[ci].child);
	    child = rec_hybrid_eliminate_redundancy_given_target_COLLECTIVE(
	      d->u.hrd.arc[ci].child,
	      component_index+1
	    );
	    red_clear_result(d->u.hrd.arc[ci].child);
	  }
	  else {
            child = hrd_lone_subtree(d->u.hrd.arc[ci].child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
	  }
          result = red_bop(OR, result, child);
        }
      }
    }
    else { 
    // Well we have skipped the component that we are looking for. 
      if (component_index == COMPONENT_COLLECTION_MAX) { 
      	fprintf(RED_OUT, "This is a bug. \n"); 
      	fprintf(RED_OUT, "See that we have not visited the target yet. \n"); 
      	fprintf(RED_OUT, "But this is impossible. \n"); 
      	exit(0); 
      } 
      
      redundant_children = NORM_FALSE;
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
	child = d->u.hrd.arc[ci].child;
        if (   (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	        || d->u.hrd.arc[ci].ub_denominator != 1
	        )
	    && d->u.hrd.arc[ci].ub_numerator
	       * COMPONENT_COLLECTION[component_index]->ub_denominator
		 <= COMPONENT_COLLECTION[component_index]->ub_numerator
		    * d->u.hrd.arc[ci].ub_denominator
	    ) {      	  
	  child = rec_hybrid_eliminate_redundancy_COLLECTIVE(
	    child, component_index+1
	  );
        }      	  
        child = hrd_one_constraint(
          child, d->u.hrd.hrd_exp,
	  d->u.hrd.arc[ci].ub_numerator,
	  d->u.hrd.arc[ci].ub_denominator
	);
	result = red_bop(OR, child, result); 
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_COLLECTIVE(
        d->u.fdd.arc[ci].child, component_index
      );
      child = fdd_one_constraint(
        child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_COLLECTIVE(
        d->u.dfdd.arc[ci].child, component_index
      );
      child = dfdd_one_constraint(
        child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_eliminate_redundancy_COLLECTIVE(
        d->u.ddd.arc[ci].child, component_index
      );
      child = ddd_one_constraint(
        child, d->var_index, 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
  } 
  
  #if RED_DEBUG_HYBRID_MODE
  fprintf(RED_OUT, "\n***[lhc=%1d]*************************************\n", 
    lhc
  ); 
  fprintf(RED_OUT, "In rec_hybrid_eliminate_redundancy_COLLECTIVE(d=%x)\n", 
    d
  ); 
  red_print_graph(d); 
  fprintf(RED_OUT, "result=%x\n", result); 
  red_print_graph(result); 
  #endif 
  
  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    return(d->result_stack->result = result);
  else
    return(result);
}
  /* rec_hybrid_eliminate_redundancy_COLLECTIVE() */







/*****************************************************************
 *  The following procedure tries to remove all redundancies collected 
 *  by the above-mentioned routines. 
 */
struct red_type	*old_hybrid_eliminate_all_redundancy_compositions(w)
	int	w;
{
  struct red_type			*result;
  struct redundancy_collection_type	dummy_rc, *nrc, *hprc, *hrc, *prc, *rc, *max_rc, *max_prc;
  struct redundancy_composition_type	*cm, dummy_cm, *pcm;
  int					flag_change, lic, cmi, rci;

  /* First we need to sort the redundancy collections into a
   * topological order.  
   * The reason is that if rc is used as a component of the redundancy 
   * of another rc', then it is better that we eliminate rc' before rc. 
   * If we do it the other way around, then it is likely that after 
   * eliminating rc, we no longer have the necessary component information 
   * to eliminate rc'.  
   
   * In the following, we first calculate the depth of each rc. 
   * The depth of an rc is one plus the maximum depth of its components. 
   *
   * Note that there could be cyclic redundancy in component referencing. 
   * For example, rc1 and rc2 may be used to prove that rc3 is redundant. 
   * But at the same time, rc1 and rc3 may also prove that rc2 is 
   * redundant. 
   * To avoid the cyclic non-terminating calculation of depths, 
   * we only do this REDUNDANCY_COLLECTION_COUNT number of times. 
   */ 
  for (flag_change = TYPE_TRUE, lic = 0; 
       flag_change && lic <= REDUNDANCY_COLLECTION_COUNT; 
       lic++
       ) {
    flag_change = TYPE_FALSE;
    for (rc = LIST_REDUNDANCY->next_redundancy_collection;
         rc;
         rc = rc->next_redundancy_collection
         ) { 
      for (cm = rc->composition_list; 
           cm; 
           cm = cm->next_redundancy_composition
           ) {
        for (cmi = 0; cmi < cm->component_count; cmi++)
          if (   cm->component[cmi] != rc 
              && rc->depth <= cm->component[cmi]->depth
              ) {
	    rc->depth = cm->component[cmi]->depth+1;
	    flag_change = TYPE_TRUE;
          }
      }
    }
  }

  /* After figuring out the depths of the redundancy collections, 
   * we now sort them in their decreasing order of the depths.   
   */
  for (hprc = LIST_REDUNDANCY, hrc = hprc->next_redundancy_collection;
       hrc ;
       ) {
    for (max_prc = prc = hprc, max_rc = rc = hrc;
	 rc;
	 prc = rc, rc = rc->next_redundancy_collection
	 )
      if (max_rc->depth < rc->depth) {
        max_prc = prc;
        max_rc = rc;
      }

    if (max_rc == hrc->next_redundancy_collection) {
      hrc->next_redundancy_collection = max_rc->next_redundancy_collection;
      max_rc->next_redundancy_collection = hrc;
      hprc->next_redundancy_collection = max_rc;
      hprc = max_rc;
    }
    else if (max_rc != hrc) {
      rc = max_rc->next_redundancy_collection;
      max_rc->next_redundancy_collection = hrc->next_redundancy_collection;
      hrc->next_redundancy_collection = rc;

      hprc->next_redundancy_collection = max_rc;
      max_prc->next_redundancy_collection = hrc;

      hprc = max_rc;
      hrc = max_rc->next_redundancy_collection;
    }
    else {
      hprc = hrc;
      hrc = hrc->next_redundancy_collection;
    }
  }

  /* Now we want to eliminate those potential cyclic redundancy references. 
   * 
   */
  for (hrc = LIST_REDUNDANCY->next_redundancy_collection;
       hrc;
       hrc = hrc->next_redundancy_collection
       ) {
    for (dummy_cm.next_redundancy_composition = hrc->composition_list,
	 pcm = &dummy_cm,
	 cm = hrc->composition_list;
	 cm;
	 ) {
      for (cmi = 0; cmi < cm->component_count; cmi++)
        /* If a true component (!= hrc) has a no smaller depth than hrc, 
         * this is cyclic. 
         * We decide to eliminate the composition.  
         */ 
        if (cm->component[cmi] != hrc && cm->component[cmi]->depth >= hrc->depth)
	  break;

      if (cmi < cm->component_count) {
	pcm->next_redundancy_composition = cm->next_redundancy_composition;
	free(cm->component); 
	free(cm);
	cm = pcm->next_redundancy_composition;
	hrc->composition_count--;
      }
      else {
        pcm = cm;
	cm = pcm->next_redundancy_composition;
      }
    }
    hrc->composition_list = dummy_cm.next_redundancy_composition;
  }

  for (rc = LIST_REDUNDANCY->next_redundancy_collection, lic = 0; 
       rc && rc->depth; 
       lic++
       ) {
    for (cm = rc->composition_list, cmi = 0; cm; cmi++) {
      struct redundancy_composition_type	*ncm;
      int					redundancy;

      COMPONENT_COLLECTION_COUNT = cm->component_count;
      COMPONENT_COLLECTION_MAX = cm->component_count-1;
      COMPONENT_COLLECTION = cm->component;
      for (rci = COMPONENT_COLLECTION_MAX; rci >= 0; rci--)
        if (COMPONENT_COLLECTION[rci] == rc) {
          TARGET_COMPONENT_INDEX = rci;
	  break;
	}

      VI_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->vi_redundancy;
      HE_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->hrd_exp_redundancy;
      UBN_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->ub_numerator;
      UBD_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->ub_denominator;

      red_init_result(RT[w]);
      RT[redundancy = RT_TOP++] // Note here we reuse (overload) variable 
                                // redundancy. 
      = rec_hybrid_extract_bound_redundancy_COLLECTIVE(RT[w]);
      red_clear_result(RT[w]);

      if (RT[redundancy] == NORM_FALSE) {
        RT_TOP--; /* redundancy */
	for (; cm; ncm = cm, cm = cm->next_redundancy_composition, free(ncm->component), free(ncm));
	break;
      }

      RT[w] = red_bop(EXCLUDE, RT[w], RT[redundancy]);

      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "before init result for red:\n"); 
      red_print_graph(RT[redundancy]); 
      #endif 
      
      red_init_result(RT[redundancy]); 
      result = rec_hybrid_eliminate_redundancy_COLLECTIVE(RT[redundancy], 0);
      red_clear_result(RT[redundancy]); 
       
      RT[w] = red_bop(OR, RT[w], result); 
      RT_TOP--; /* redundancy */
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "after eliminate redundancy collective:\n"); 
      red_print_graph(RT[w]); 
      #endif 

      ncm = cm;
      cm = cm->next_redundancy_composition;
      free(ncm->component);
      free(ncm);
    }
    nrc = rc;
    rc = rc->next_redundancy_collection;
    free(nrc);
    garbage_collect(FLAG_GC_SILENT); 
  }
  for (; rc; ) {
    nrc = rc;
    rc = rc->next_redundancy_collection;
    free(nrc);
  }
  return(RT[w]);
}
  /* old_hybrid_eliminate_all_redundancy_compositions() */



struct red_type	*hybrid_eliminate_all_redundancy_compositions(w)
	int	w;
{
  struct red_type			*result;
  struct redundancy_collection_type	dummy_rc, *nrc, *hprc, *hrc, *prc, *rc, *max_rc, *max_prc;
  struct redundancy_composition_type	*cm, dummy_cm, *pcm;
  int					flag_change, lic, cmi;
/*
*/
  for (flag_change = TYPE_TRUE, lic = 0; flag_change && lic <= REDUNDANCY_COLLECTION_COUNT; lic++) {
    flag_change = TYPE_FALSE;
    for (rc = LIST_REDUNDANCY->next_redundancy_collection;
         rc;
         rc = rc->next_redundancy_collection
         ) {
      for (cm = rc->composition_list; cm; cm = cm->next_redundancy_composition) {
        for (cmi = 0; cmi < cm->component_count; cmi++)
          if (cm->component[cmi] != rc && rc->depth <= cm->component[cmi]->depth) {
	    rc->depth = cm->component[cmi]->depth+1;
	    flag_change = TYPE_TRUE;
          }
      }
    }
  }
/*
*/
  for (hprc = LIST_REDUNDANCY, hrc = hprc->next_redundancy_collection;
       hrc ;
       ) {
    for (max_prc = prc = hprc, max_rc = rc = hrc;
	 rc;
	 prc = rc, rc = rc->next_redundancy_collection
	 )
      if (max_rc->depth < rc->depth) {
        max_prc = prc;
        max_rc = rc;
      }

    if (max_rc == hrc->next_redundancy_collection) {
      hrc->next_redundancy_collection = max_rc->next_redundancy_collection;
      max_rc->next_redundancy_collection = hrc;
      hprc->next_redundancy_collection = max_rc;
      hprc = max_rc;
    }
    else if (max_rc != hrc) {
      rc = max_rc->next_redundancy_collection;
      max_rc->next_redundancy_collection = hrc->next_redundancy_collection;
      hrc->next_redundancy_collection = rc;

      hprc->next_redundancy_collection = max_rc;
      max_prc->next_redundancy_collection = hrc;

      hprc = max_rc;
      hrc = max_rc->next_redundancy_collection;
    }
    else {
      hprc = hrc;
      hrc = hrc->next_redundancy_collection;
    }
  }
  #if RED_DEBUG_HYBRID_MODE
  print_redundancy_collection("The 3rd round collection after sorting");
  #endif 
  
  for (hrc = LIST_REDUNDANCY->next_redundancy_collection;
       hrc;
       hrc = hrc->next_redundancy_collection
       ) {
    for (dummy_cm.next_redundancy_composition = hrc->composition_list,
	 pcm = &dummy_cm,
	 cm = hrc->composition_list;
	 cm;
	 ) {
      for (cmi = 0; cmi < cm->component_count; cmi++)
        if (   cm->component[cmi] != hrc 
            && cm->component[cmi]->depth >= hrc->depth
            )
	  break;

      if (cmi < cm->component_count) {
	pcm->next_redundancy_composition = cm->next_redundancy_composition;
	free(cm->component); 
	free(cm);
	cm = pcm->next_redundancy_composition;
	hrc->composition_count--;
      }
      else {
        pcm = cm;
	cm = pcm->next_redundancy_composition;
      }
    }
    hrc->composition_list = dummy_cm.next_redundancy_composition;
  }
  #if RED_DEBUG_HYBRID_MODE
  print_redundancy_collection("The 4th round after cycle elimination");
  #endif 

  for (rc = LIST_REDUNDANCY->next_redundancy_collection, lic=0; 
       rc && rc->depth; 
       lic++
       ) {
    for (cm = rc->composition_list, cmi=0; cm; cmi++) {
      struct redundancy_composition_type	*ncm;
      int					redundancy;

      COMPONENT_COLLECTION_COUNT = cm->component_count;
      COMPONENT_COLLECTION_MAX = cm->component_count-1;
      COMPONENT_COLLECTION = cm->component;
      for (redundancy = COMPONENT_COLLECTION_MAX; redundancy >= 0; redundancy--)
        if (COMPONENT_COLLECTION[redundancy] == rc) {
          TARGET_COMPONENT_INDEX = redundancy;
	  break;
	}

      VI_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->vi_redundancy;
      HE_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->hrd_exp_redundancy;
      UBN_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->ub_numerator;
      UBD_XRB = COMPONENT_COLLECTION[TARGET_COMPONENT_INDEX]->ub_denominator;

      red_init_result(RT[w]);
      RT[redundancy = RT_TOP++] 
      = rec_hybrid_extract_bound_redundancy_COLLECTIVE(RT[w]);
      red_clear_result(RT[w]);

      if (RT[redundancy] == NORM_FALSE) {
        RT_TOP--; /* redundancy */
	for (; cm; ncm = cm, cm = cm->next_redundancy_composition, free(ncm->component), free(ncm));
	break;
      }

      RT[w] = red_bop(EXCLUDE, RT[w], RT[redundancy]);

      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, lic:%d, cmi:%d, before stack composition elm", 
        ITERATION_COUNT, ITERATE_SXI, lic, cmi 
      );
      red_print_graph(RT[redundancy]); 
      #endif 
      
      red_init_result(RT[redundancy]);
      result = rec_hybrid_eliminate_redundancy_COLLECTIVE(RT[redundancy], 0);
      red_clear_result(RT[redundancy]);

      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, lic:%d, cmi:%d, after stack composition elm", 
        ITERATION_COUNT, ITERATE_SXI, lic, cmi 
      );
      red_print_graph(result); 
      #endif 

      RT[w] = red_bop(OR, RT[w], result);
      RT_TOP--; /* redundancy */

      ncm = cm;
      cm = cm->next_redundancy_composition;
      free(ncm->component);
      free(ncm);
    }
    nrc = rc;
    rc = rc->next_redundancy_collection;
    free(nrc);
    garbage_collect(FLAG_GC_SILENT);
  }
  for (; rc; ) {
    nrc = rc;
    rc = rc->next_redundancy_collection;
    free(nrc);
  }
  return(RT[w]);
}
  /* hybrid_eliminate_all_redundancy_compositions() */




struct red_type	*rec_hybrid_check_long(d)
     struct red_type	*d;
{
  int				ci, len;
  struct red_type		*result, *child;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_HYBRID_CHECK_LONG, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (   (len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) >= 3
	&& VAR[d->u.hrd.hrd_exp->hrd_term[len-3].var_index].PROC_INDEX
	) {
      result = hrd_lone_subtree(d->u.hrd.arc[0].child, d->var_index, d->u.hrd.hrd_exp,
				   d->u.hrd.arc[0].ub_numerator,
				   d->u.hrd.arc[0].ub_denominator
				   );
    }
    else {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_check_long(d->u.hrd.arc[ci].child);
	if (child != NORM_FALSE) {
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      )
            child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
          result = child;
	  break;
        }
      }
    }
    break;
  case TYPE_FLOAT:
    result = NORM_FALSE;
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_check_long(d->u.fdd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = fdd_lone_subtree(child, d->var_index,
	  d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound
	);
        result = child;
        break;
      }
    }
    break;
  case TYPE_DOUBLE:
    result = NORM_FALSE;
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_check_long(d->u.dfdd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = dfdd_lone_subtree(child, d->var_index,
	  d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound
	);
        result = child;
        break;
      }
    }
    break;
  default:
    result = NORM_FALSE;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_check_long(d->u.ddd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = ddd_lone_subtree(child, d->var_index,
				      d->u.ddd.arc[ci].lower_bound,
				      d->u.ddd.arc[ci].upper_bound
				      );
        result = child;
        break;
      }
    }
  }
  return(ce->result = result);
}
  /* rec_hybrid_check_long() */





struct red_type	*rec_hybrid_extract_long(d)
     struct red_type	*d;
{
  int				ci, len;
  struct red_type		*result, *child;
  struct cache1_hash_entry_type	*ce; 

  if (   d == NORM_NO_RESTRICTION
      || d == NORM_FALSE
      )
    return(NORM_FALSE);

  ce = cache1_check_result_key(OP_HYBRID_EXTRACT_LONG, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (   (len = d->u.hrd.hrd_exp->status & MASK_HYBRID_LENGTH) >= 3
	&& VAR[d->u.hrd.hrd_exp->hrd_term[len-3].var_index].PROC_INDEX
	) {
      ci = d->u.hrd.child_count-1;
      if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	  && d->u.hrd.arc[ci].ub_denominator == 1
	  ) {
	result = rec_hybrid_extract_long(d->u.hrd.arc[ci].child);
        for (ci--; ci >= 0; ci--) {
          child = hrd_lone_subtree(d->u.hrd.arc[ci].child, d->var_index, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
          result = red_bop(OR, child, result);
        }
      }
      else
        result = d;
    }
    else {
      result = NORM_FALSE;
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_extract_long(d->u.hrd.arc[ci].child);
	if (child != NORM_FALSE) {
	  if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	      || d->u.hrd.arc[ci].ub_denominator != 1
	      )
            child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				        d->u.hrd.arc[ci].ub_numerator,
				        d->u.hrd.arc[ci].ub_denominator
				        );
          result = red_bop(OR, result, child);
        }
      }
    }
    break;
  case TYPE_FLOAT:
    result = NORM_FALSE;
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_extract_long(d->u.fdd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = fdd_lone_subtree(child, d->var_index,
	  d->u.fdd.arc[ci].lower_bound,
	  d->u.fdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_DOUBLE:
    result = NORM_FALSE;
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_extract_long(d->u.dfdd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = dfdd_lone_subtree(child, d->var_index,
	  d->u.dfdd.arc[ci].lower_bound,
	  d->u.dfdd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, child);
      }
    }
    break;
  default:
    result = NORM_FALSE;
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_extract_long(d->u.ddd.arc[ci].child);
      if (child != NORM_FALSE) {
        child = ddd_lone_subtree(child, d->var_index,
				      d->u.ddd.arc[ci].lower_bound,
				      d->u.ddd.arc[ci].upper_bound
				      );
        result = red_bop(OR, result, child);
      }
    }
  }
  return(ce->result = result);
}
  /* rec_hybrid_extract_long() */








#define	FLAG_PRIMED	1
#define	FLAG_UMPRIMED	0

struct red_type	*hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(
  w, flag_primed
)
     int	w, flag_primed;
{
  struct red_type			*result;
  struct redundancy_collection_type	dummy_rc, *nrc, *hprc, *hrc, *prc, *rc, *max_rc, *max_prc;
  struct redundancy_composition_type	*cm;
  int					flag_change, lic, cmi;

  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  LIST_REDUNDANCY = &dummy_rc;
  LIST_REDUNDANCY->next_redundancy_collection = NULL;
  REDUNDANCY_COLLECTION_COUNT = 0;
  switch (flag_primed) {
  case FLAG_UMPRIMED:
    if (GSTATUS[INDEX_NORM_HYBRID] 
    	& FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_DOWNWARD
    	) {
      red_init_result(RT[w]); 
      count_2red = 0; 
      rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE(RT[w]);
      red_clear_result(RT[w]); 
      
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after collecting 2 redundancy\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      #endif 
    }
    if (GSTATUS[INDEX_NORM_HYBRID] 
    	& FLAG_NORM_HYBRID_3REDUNDANCY_ELIMINATION_DOWNWARD
        ) {
      LENX_3REDUNDANCY = 2;
      red_init_result(RT[w]); 
      rec_hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(RT[w]);
      red_clear_result(RT[w]); 

      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after collecting 3 redundancy\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      #endif 
    }
    if (GSTATUS[INDEX_NORM_HYBRID] 
    	& FLAG_NORM_HYBRID_2REDUNDANCY_ELIMINATION_LOOKAHEAD
    	) {
      red_init_result(RT[w]); 
      rec_hybrid_eliminate_2redundancy_LOOKAHEAD_COLLECTIVE(RT[w]);
      red_clear_result(RT[w]); 
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after collecting 2 lookahead redundancy\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      #endif 
    }
    break;
  case FLAG_PRIMED:
    red_init_result(RT[w]); 
    rec_hybrid_eliminate_2redundancy_DOWNWARD_COLLECTIVE_FOR_PRIMED(RT[w]);
    red_clear_result(RT[w]); 
    LENX_3REDUNDANCY = 2;
    #if RED_DEBUG_HYBRID_MODE
    print_cpu_time("IT:%d, SXI:%d:, after collecting 2 lookahead redundancy for primed\n", 
      ITERATION_COUNT, ITERATE_SXI 
    );
    #endif 
  }

  RT[w] = hybrid_eliminate_all_redundancy_compositions(w);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("IT:%d, SXI:%d:, after 1st composition elimination\n", 
    ITERATION_COUNT, ITERATE_SXI 
  );
/*
  print_cpu_time("after 1st composition elimination");
  fprintf(RED_OUT, "\nIn 3 redundancy collective elimination, before 4-redundancy check:\n");
*/
  red_print_graph(RT[w]);
  #endif 
  
  if (   flag_primed == FLAG_UMPRIMED
      && (GSTATUS[INDEX_NORM_HYBRID] 
      	  & FLAG_NORM_HYBRID_4REDUNDANCY_ELIMINATION_DOWNWARD
      	  )
      ) {
    int	redundancy;

    RT[redundancy = RT_TOP++] = rec_hybrid_extract_long(RT[w]);
    #if RED_DEBUG_HYBRID_MODE
    print_cpu_time("IT:%d, SXI:%d:, after extract long\n", 
      ITERATION_COUNT, ITERATE_SXI 
    );
    #endif 
    
    if (RT[redundancy] != NORM_FALSE) {

      #if RED_DEBUG_HYBRID_MODE
      printf("\n** Caught a long hybrid inequality after collective reduction at I:%1d, SXI=%1d.\n",
	     ITERATION_COUNT, ITERATE_SXI
	     );
      fprintf(RED_OUT,
	      "\n** Caught a long hybrid inequality after collective reduction at I:%1d, SXI=%1d.\n",
	      ITERATION_COUNT, ITERATE_SXI
	      );
      red_print_graph(RT[redundancy]);
      #endif 
     
      RT[w] = red_bop(EXCLUDE, RT[w], RT[redundancy]);
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after 1st redundancy exclusion\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      #endif 

      LIST_REDUNDANCY = &dummy_rc;
      LIST_REDUNDANCY->next_redundancy_collection = NULL;
      REDUNDANCY_COLLECTION_COUNT = 0;
      LENX_3REDUNDANCY = 2;

      red_init_result(RT[redundancy]); 
      rec_hybrid_eliminate_4redundancy_DOWNWARD_COLLECTIVE(RT[redundancy]);
      red_clear_result(RT[w]); 
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after collection at level 4\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      #endif 
      
      RT[redundancy] = hybrid_eliminate_all_redundancy_compositions(
        redundancy
      );
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("IT:%d, SXI:%d:, after reduction at level 4\n", 
        ITERATION_COUNT, ITERATE_SXI 
      );
      fprintf(RED_OUT, "\nAfter reduction at level 4:\n");
      red_print_graph(RT[redundancy]);
      #endif 
      
      RT[w] = red_bop(OR, RT[w], RT[redundancy]);
/*
      bk();
*/
    }
    RT_TOP--; /* redundancy */
  }
  return(RT[w]);
}
/* hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE() */








/*****************************************************************************
*  The difficult reduction routine.
*/

struct proof_obligation_type {
  int				var_index,
				lb_numerator, lb_denominator,
				ub_numerator, ub_denominator;
  struct hrd_exp_type		*hrd_exp;
  struct proof_obligation_type	*next_proof_obligation, *prev_proof_obligation;
};
struct proof_obligation_type	PO_HEAD;



void	rec_collect_proof_obligations(d, prev_po)
	struct red_type			*d;
	struct proof_obligation_type	*prev_po;
{
  struct proof_obligation_type	*cur_po;
  int				comp, ci;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_FALSE || d == NORM_NO_RESTRICTION)
    return;
  for (cur_po = prev_po->next_proof_obligation;
	  cur_po
       && (   d->var_index > cur_po->var_index
	   || (   VAR[d->var_index].TYPE == TYPE_HRD
	       && (comp = HRD_EXP_COMP(d->u.hrd.hrd_exp, cur_po->hrd_exp)) > 0
	       )
	   );
       prev_po = cur_po, cur_po = cur_po->next_proof_obligation
       ) {
    cur_po->ub_numerator = HYBRID_POS_INFINITY;
    cur_po->ub_denominator = 1;
  }
  if (VAR[d->var_index].TYPE == TYPE_HRD) {
    if (cur_po == NULL || comp < 0) {
      struct proof_obligation_type	*new_po;

      new_po = (struct proof_obligation_type *) malloc(sizeof(struct proof_obligation_type));
      new_po->var_index = d->var_index;
      new_po->hrd_exp = d->u.hrd.hrd_exp;
      new_po->lb_numerator = d->u.hrd.arc[0].ub_numerator;
      new_po->lb_denominator = d->u.hrd.arc[0].ub_denominator;
      new_po->ub_numerator = d->u.hrd.arc[d->u.hrd.child_count-1].ub_numerator;
      new_po->ub_denominator = d->u.hrd.arc[d->u.hrd.child_count-1].ub_denominator;

      new_po->next_proof_obligation = cur_po;
      new_po->prev_proof_obligation = prev_po;
      if (cur_po)
        cur_po->prev_proof_obligation = new_po;
      prev_po->next_proof_obligation = new_po;

      prev_po = new_po;
    }
    else /* must be the case that cur_po != NULL && comp == 0 */ {
      if (rational_comp(d->u.hrd.arc[0].ub_numerator,
			d->u.hrd.arc[0].ub_denominator,
			cur_po->lb_numerator,
			cur_po->lb_denominator
			) < 0
	  ) {
        cur_po->lb_numerator = d->u.hrd.arc[0].ub_numerator;
        cur_po->lb_denominator = d->u.hrd.arc[0].ub_denominator;
      }
      if (rational_comp(d->u.hrd.arc[d->u.hrd.child_count-1].ub_numerator,
			d->u.hrd.arc[d->u.hrd.child_count-1].ub_denominator,
			cur_po->ub_numerator,
			cur_po->ub_denominator
			) > 0
	  ) {
        cur_po->ub_numerator = d->u.hrd.arc[d->u.hrd.child_count-1].ub_numerator;
        cur_po->ub_denominator = d->u.hrd.arc[d->u.hrd.child_count-1].ub_denominator;
      }
      prev_po = cur_po;
    }
  }

  ce = cache1_check_result_key(OP_COLLECT_PROOF_OBLIGATIONS, d); 
  if (ce->result) {
    return; 
  } 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      rec_collect_proof_obligations(d->u.hrd.arc[ci].child, prev_po);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_collect_proof_obligations(d->u.fdd.arc[ci].child, prev_po);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_collect_proof_obligations(d->u.dfdd.arc[ci].child, prev_po);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_collect_proof_obligations(d->u.ddd.arc[ci].child, prev_po);
    }
  }
}
  /* rec_collect_proof_obligation() */



void	collect_proof_obligations(d)
	struct red_type			*d;
{
  cache1_clear(OP_COLLECT_PROOF_OBLIGATIONS); 
  rec_collect_proof_obligations(d, &PO_HEAD);
}
  /* collect_proof_obligation() */






struct red_type	*rec_hybrid_proof_obligation_givenX(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*child;
  struct cache4_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache4_check_result_key(
    OP_HYBRID_PROOF_OBLIGATION_GIVENX, d, 
    GHE[0].hrd_exp, 
    GHE[0].ub_numerator, 
    GHE[0].ub_denominator
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  ce->result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_proof_obligation_givenX(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
          || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
	struct proof_obligation_type 	*cur_po;

        GHE[1].hrd_exp = d->u.hrd.hrd_exp;
        GHE[1].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[1].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
	for (cur_po = PO_HEAD.next_proof_obligation;
	     cur_po && cur_po->var_index <= d->var_index;
	     cur_po = cur_po->next_proof_obligation
	     ) {
	  if (cur_po->hrd_exp == GHE[0].hrd_exp || cur_po->hrd_exp == GHE[1].hrd_exp)
	    continue;
	  GHE[2].hrd_exp = cur_po->hrd_exp;
	  if (Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY) == GAUSSIAN_POSITIVE) {
	    int	nx, dx, ny, dy, bn, bd;

	    nx = GHE[0].ub_numerator;
	    dx = GHE[0].ub_denominator;
	    rational_lift(&nx, &dx, GMultiple[0]);
/*
      fprintf(RED_OUT, "X: %1d/%1d lifted to %1d/%1d\n", RHEX_NUMERATOR, RHEX_DENOMINATOR, nx, dx);
*/
	    ny = GHE[1].ub_numerator;
	    dy = GHE[1].ub_denominator;
	    rational_lift(&ny, &dy, GMultiple[1]);
/*
      fprintf(RED_OUT, "Y: %1d/%1d lifted to %1d/%1d\n", RHEY_NUMERATOR, RHEY_DENOMINATOR, ny, dy);
*/
	    hybrid_ub_add(nx, dx, ny, dy, &bn, &bd);
/*
      fprintf(RED_OUT, "%1d * X + %1d * Y = %1d/%1d\n", mx, my, bn, bd);
*/
	    if (bn != HYBRID_POS_INFINITY || bd != 1) {
	      rational_lower(&bn, &bd, GMultiple[2]);
/*
	      fprintf(RED_OUT, "\n*** One obligation fulfilled ***\n");
	      hrd_exp_print(GHE[0].hrd_exp, 0);
	      fprintf(RED_OUT, "<=%1d/%1d\n", GHE[0].ub_numerator, GHE[0].ub_denominator);
	      hrd_exp_print(GHE[1].hrd_exp, 0);
	      fprintf(RED_OUT, "<=%1d/%1d\n", GHE[1].ub_numerator, GHE[1].ub_denominator);
	      hrd_exp_print(cur_po->hrd_exp, 0);
	      fprintf(RED_OUT, "<=%1d/%1d\n\n", bn, bd);
*/
	      child = hrd_one_constraint(child, cur_po->hrd_exp, bn, bd);
	    }
	  }
	}
        child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				      d->u.hrd.arc[ci].ub_numerator,
				      d->u.hrd.arc[ci].ub_denominator
				      );
      }
      ce->result = red_bop(OR, ce->result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_proof_obligation_givenX(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      ce->result = red_bop(OR, ce->result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_proof_obligation_givenX(d->u.dfdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      ce->result = red_bop(OR, ce->result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_proof_obligation_givenX(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      ce->result = red_bop(OR, ce->result, child);
    }
  }
}
  /* rec_hybrid_proof_obligation_givenX() */





struct red_type	*rec_hybrid_proof_obligation(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_PROOF_OBLIGATION, d); 
  if (ce->result) {
    return(ce->result); 
  } 
  else 
    ce->result = NORM_NO_RESTRICTION; 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD_FOR_PRIMED().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_proof_obligation(d->u.hrd.arc[ci].child);
      if (   d->u.hrd.arc[ci].ub_numerator != HYBRID_POS_INFINITY
	  || d->u.hrd.arc[ci].ub_denominator != 1
	  ) {
        GHE[0].hrd_exp = d->u.hrd.hrd_exp;
        GHE[0].ub_numerator = d->u.hrd.arc[ci].ub_numerator;
        GHE[0].ub_denominator = d->u.hrd.arc[ci].ub_denominator;
        grown_child = rec_hybrid_proof_obligation_givenX(child);
        child = grown_child;
        child = hrd_one_constraint(child, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_proof_obligation(d->u.fdd.arc[ci].child);
      child = fdd_one_constraint(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_proof_obligation(d->u.dfdd.arc[ci].child);
      child = dfdd_one_constraint(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_proof_obligation(d->u.ddd.arc[ci].child);
      child = ddd_one_constraint
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
}
  /* rec_hybrid_proof_obligation() */




struct red_type	*hybrid_proof_obligation(d)
	struct red_type	*d;
{
  struct red_type	*result;

  cache4_clear(OP_HYBRID_PROOF_OBLIGATION_GIVENX); 
  cache1_clear(OP_HYBRID_PROOF_OBLIGATION); 
  result = rec_hybrid_proof_obligation(d);
  return(result);
}
  /* hybrid_proof_obligation() */




struct red_type	*hybrid_subsume(new, old)
	int	new, old;
{
  int	tmp;
  struct proof_obligation_type	*cur_po, *prev_po;

  if (!(GSTATUS[INDEX_NORM_HYBRID] & FLAG_NORM_HYBRID_PROOF_OBLIGATIONS))
    return(RT[new]);
/*
  fprintf(RED_OUT, "\n\n====[Collecting proof obligations for:\nRT[new=%1d]:\n", new);
  red_print_graph(RT[new]);
  fprintf(RED_OUT, "RT[old=%1d]:\n", old);
  red_print_graph(RT[old]);
*/
  PO_HEAD.var_index = 0;
  PO_HEAD.hrd_exp = NULL;
  PO_HEAD.next_proof_obligation = PO_HEAD.prev_proof_obligation = NULL;
  collect_proof_obligations(RT[new], &PO_HEAD);
  collect_proof_obligations(RT[old], &PO_HEAD);
/*
  fprintf(RED_OUT, "\nThe proof obligations\n");
  for (cur_po = PO_HEAD.next_proof_obligation;
       cur_po;
       cur_po = cur_po->next_proof_obligation
       )
    hrd_exp_print(cur_po->hrd_exp, 0);
*/

  RT[tmp = RT_TOP++] = rec_hybrid_proof_obligation(RT[new]);
/*
  fprintf(RED_OUT, "\nRT[tmp=%1d] with fulfilled proof obligations.\n", tmp);
  red_print_graph(RT[tmp]);
*/
  for (prev_po = &PO_HEAD, cur_po = PO_HEAD.next_proof_obligation;
       cur_po;
       prev_po = cur_po, cur_po = cur_po->next_proof_obligation, free(prev_po)
       );

  RT[tmp] = red_bop(OR, RT[tmp], RT[old]);
  RT[tmp] = red_subsume(RT[tmp]);
  if (ITERATION_COUNT >= 1)
    RT[tmp] = red_bop(EXCLUDE, RT[tmp], RT[old]);
  RT[new] = red_super_intersect_self(RT[new], RT[tmp]);
  RT_TOP--; /* tmp */

  return(RT[new]);
}
  /* hybrid_subsume() */



int	count_hybrid_normalize = 0; 
extern void	cgt(); 

struct red_type	*hybrid_normalize(w)
	int	w;
{
  struct red_type	*result;
  int			old_w; 

  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HN %1d, IT:%d, SXI:%d, entering\n", 
    ++count_hybrid_normalize, ITERATION_COUNT, ITERATE_SXI 
  ); 
  red_print_graph(RT[w]);
/*
  cgt(RT[w]); 
  for (; count_hybrid_normalize == -1; ) ; 
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  print_cpu_time("entering hybrid normalization");
  report_red_management();
  */
  #endif 
  
/*
  for (RT[old_w = RT_TOP++] = NORM_FALSE; 
       RT[old_w] != RT[w]; 
       ) { 
    RT[old_w] = RT[w]; 
*/
//    RT[w] = hybrid_bypass_unit_DOWNWARD(w); 
/*
  }
  RT_TOP--; // old_w 
*/  
  RT[w] = hybrid_constant_replace(RT[w]); 

  red_init_result(RT[w]); 
  result = rec_hybrid_eliminate_inconsistency_DOWNWARD(RT[w]);
  RT[w] = result;
  red_unmark(RT[w], MASK_STACK_REFERENCED[TOP_LEVEL_RESULT_STACK]); 
  red_clear_result(RT[w]); 
  garbage_collect(FLAG_GC_SILENT);
/*
  fprintf(RED_OUT, "\nHN %1d, after inconsistency elimination:\n", count_hybrid_normalize);
  red_print_graph(RT[w]);
  print_cpu_time("hybrid normalization: after inconsistency elimination");
  fprintf(RED_OUT, "IT:%1d, SXI:%1d, hybrid_normalize:%1d, after inconsistency elm\n", 
    ITERATION_COUNT, ITERATE_SXI, count_hybrid_normalize
  ); 
  cgt(RT[w]); 
  report_red_management();
  */
/*
#define	MASK_HYBRID_STRATEGY					(0xFFC00)
#define	FLAG_HYBRID_STRATEGY_PARAMETER_PRUNING			(0x400)
#define FLAG_HYBRID_DOUBLE_REDUNDANCY_ELIMINATION_DOWNWARD	(0x800)
#define FLAG_HYBRID_REDUNDANCY_ELIMINATION_LOOKAHEAD		(0x1000)
*/
  RT[w] = hybrid_subsume(w, REACHABLE);
/*
  fprintf(RED_OUT, "\nHN %1d, after reduction:\n", count_hybrid_normalize);
  red_print_graph(RT[w]);

  print_cpu_time("hybrid normalization: after subsume");
  fprintf(RED_OUT, "IT:%1d, SXI:%1d, hybrid_normalize:%1d, after subsumption\n", 
    ITERATION_COUNT, ITERATE_SXI, count_hybrid_normalize
  ); 
  cgt(RT[w]); 
*/

  RT[w] = hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(w, FLAG_UMPRIMED);
/*
  fprintf(RED_OUT, "\nHN %1d, after 3 redundancy collective:\n", count_hybrid_normalize);
  red_print_graph(RT[w]);
*/

  
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("IT:%d, SXI:%d, hybrid_normalize:%d, after 3 redundancy collective\n", 
    ITERATION_COUNT, ITERATE_SXI, count_hybrid_normalize
  ); 
/*
  cgt(RT[w]); 
      RT[w] = result;
    print_cpu_time("after 3 redundancy elimination");
    report_red_management();
    fprintf(RED_OUT, "\nred_grow() with output:\n");
    red_print_graph(result);
    */
/*
  }

  garbage_collect(FLAG_GC_SILENT);

*/
  #endif 
  
  return(RT[w]);
}
  /* hybrid_normalize() */




#define	FLAG_HYBRID_COMPLICATE	-1

int	hybrid_complicate_constraint(he)
	struct hrd_exp_type	*he;
{
  int	len, b, ti;

  b = 0;
  len = he->status & MASK_HYBRID_LENGTH;
  for (ti = 0; ti < len; ti++)
    if (abs(he->hrd_term[ti].coeff) > ALL_RATE_BOUND)
      return(FLAG_HYBRID_COMPLICATE);
    else {
      b = b + abs(he->hrd_term[ti].coeff) * ALL_CLOCK_TIMING_BOUND;
    }
  b = b * 2 + 1;
  return(b);
}
  /* hybrid_complicate_constraint() */




struct red_type	*rec_hybrid_abstract_precision(d)
     struct red_type	*d;
{
  int				ci, b;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ABSTRACT_PRECISION, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if ((b = hybrid_complicate_constraint(d->u.hrd.hrd_exp)) == FLAG_HYBRID_COMPLICATE) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_abstract_precision(d->u.hrd.arc[ci].child);
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_abstract_precision(d->u.hrd.arc[ci].child);
        if (abs(d->u.hrd.arc[ci].ub_numerator) <= b * d->u.hrd.arc[ci].ub_denominator) {
          child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        }
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_abstract_precision(d->u.fdd.arc[ci].child);
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_abstract_precision(d->u.dfdd.arc[ci].child);
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_abstract_precision(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_abstract_precision() */






struct red_type	*hybrid_abstract_precision(d)
     struct red_type	*d;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  result = rec_hybrid_abstract_precision(d);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(result);
}
/* hybrid_abstract_precision() */




struct red_type	*rec_hybrid_abstract_magnitude(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_ABSTRACT_MAGNITUDE, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_abstract_magnitude(d->u.hrd.arc[ci].child);
      if (abs(d->u.hrd.arc[ci].ub_numerator) <= 2 * ALL_CLOCK_TIMING_BOUND * d->u.hrd.arc[ci].ub_denominator + 1) {
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
      }
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_abstract_magnitude(d->u.fdd.arc[ci].child);
      child = fdd_lone_subtree(child, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_abstract_magnitude(d->u.dfdd.arc[ci].child);
      child = dfdd_lone_subtree(child, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_abstract_magnitude(d->u.ddd.arc[ci].child);
      child = ddd_lone_subtree
		(child, d->var_index, d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_abstract_magnitude() */






struct red_type	*hybrid_abstract_magnitude(d)
     struct red_type	*d;
{
  struct red_type	*result;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  result = rec_hybrid_abstract_magnitude(d);
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */
  return(result);
}
/* hybrid_abstract_magnitude() */











struct hrd_exp_type	*hrd_exp_delta_coeff_counting_interval_rates(he, common_raise_ptr, common_divider_ptr)
	struct hrd_exp_type	*he;
	int			*common_raise_ptr, *common_divider_ptr;
{
  int			i, vi, pi, ci, ti, coeff, dn, dd, len, new_len, interval_rate_count,
			delta_numerator, delta_denominator;
  struct hrd_exp_type	*newhe;

  delta_numerator = 0;
  delta_denominator = 1;

  interval_rate_count = 0;
  len = he->status & MASK_HYBRID_LENGTH;
  for (i = 0; i < len; i++) {
    vi = he->hrd_term[i].var_index;
    if (VRATE[vi].lb_denominator == RATE_DONT_CARE) {
      fprintf(RED_OUT, "Error 3: how come you are using an unspecified rate of variable %s.\n",
	      VAR[vi].NAME
	      );
      bk("a"); 
      fflush(RED_OUT);
      exit(0);
    }
    else if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
             && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
             ) {
      coeff = he->hrd_term[i].coeff;
      dn = delta_numerator;
      dd = delta_denominator;
      delta_numerator = dn * VRATE[vi].ub_denominator + coeff * VRATE[vi].ub_numerator * dd;
      delta_denominator = dd * VRATE[vi].ub_denominator;
      prime_effect(&delta_numerator, &delta_denominator);
    }
    else
      interval_rate_count++;
  }
/*
  if (ITERATION_COUNT == 1 && ITERATE_SXI == 0) {
    fprintf(RED_OUT, "\nin hybrid_delta_coeff for: ");
    hrd_exp_print(he, 0);
    fprintf(RED_OUT, "delta coeff = %1d/%1d.\n", *delta_numerator_ptr, *delta_denominator_ptr);
    fflush(RED_OUT);
  }
*/
  if (interval_rate_count || delta_numerator) {
    if (delta_numerator) {
      newhe = hrd_exp_alloc(new_len = len + interval_rate_count + 1);
      for (ci = 0, ti = 0; ti < len && VI_DELTA > (vi = he->hrd_term[ti].var_index); ti++) {
        vi = he->hrd_term[ti].var_index;
        if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
            && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
            ) {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
        else {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
          newhe->hrd_term[ci].var_index = VAR[vi].PRIMED_VI;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
      }
      newhe->hrd_term[ci].var_index = VI_DELTA;
      newhe->hrd_term[ci].coeff = delta_numerator;
      ci++;
      for (; ti < len; ti++) {
        vi = he->hrd_term[ti].var_index;
        if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
            && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
            ) {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
        else {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
          newhe->hrd_term[ci].var_index = VAR[vi].PRIMED_VI;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
      }
    }
    else {
      newhe = hrd_exp_alloc(new_len = len + interval_rate_count);
      for (ci = 0, ti = 0; ti < len; ti++) {
        vi = he->hrd_term[ti].var_index;
        if (   VRATE[vi].lb_numerator == VRATE[vi].ub_numerator
            && VRATE[vi].lb_denominator == VRATE[vi].ub_denominator
            ) {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
        else {
          newhe->hrd_term[ci].var_index = vi;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
          newhe->hrd_term[ci].var_index = VAR[vi].PRIMED_VI;
          newhe->hrd_term[ci].coeff = delta_denominator * he->hrd_term[ti].coeff;
          ci++;
        }
      }
    }
    *common_divider_ptr = newhe->hrd_term[0].coeff;
    for (ti = 1; ti < new_len; ti++)
      *common_divider_ptr = gcd(*common_divider_ptr, newhe->hrd_term[ti].coeff);
    if (*common_divider_ptr != 1)
      for (ci = abs(ci), ti = 0; ti < new_len; ti++)
        newhe->hrd_term[ti].coeff = newhe->hrd_term[ti].coeff / *common_divider_ptr;
    newhe->name = linear_name(newhe->hrd_term, new_len);
    newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI) | (he->status & MASK_HYBRID_LIFTED_VI); 
    newhe = hrd_exp_share(newhe);
    *common_raise_ptr = delta_denominator;
  }
  else {
    *common_raise_ptr = 1;
    *common_divider_ptr = 1;
    newhe = he;
  }
  prime_effect(common_raise_ptr, common_divider_ptr);
  return(newhe);
}
/* hrd_exp_delta_coeff_counting_interval_rates() */





struct hrd_exp_type	*hrd_exp_pair(vi1, cf1, vi2, cf2)
	int	vi1, cf1, vi2, cf2;
{
  struct hrd_exp_type	*newhe;
  int                 pi; 

  if (cf1)
    if (cf2) {
      prime_effect(&cf1, &cf2);
      newhe = hrd_exp_alloc(2);
      newhe->hrd_term[0].var_index = vi1;
      newhe->hrd_term[0].coeff = cf1;
      newhe->hrd_term[1].var_index = vi2;
      newhe->hrd_term[1].coeff = cf2;
      newhe->name = linear_name(newhe->hrd_term, 2);
      if (VAR[vi1].PROC_INDEX > VAR[vi2].PROC_INDEX) 
      	pi = VAR[vi1].PROC_INDEX; 
      else 
      	pi = VAR[vi2].PROC_INDEX; 
      newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI) 
                    | (variable_index[TYPE_HRD][pi][0] * MASK_HYBRID_VI_BASE); 
      newhe = hrd_exp_share(newhe);
      return(newhe);
    }
    else {
      newhe = hrd_exp_alloc(1);
      newhe->hrd_term[0].var_index = vi1;
      newhe->hrd_term[0].coeff = cf1;
      newhe->name = linear_name(newhe->hrd_term, 1);
     	pi = VAR[vi1].PROC_INDEX; 
      newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI) 
                    | (variable_index[TYPE_HRD][pi][0] * MASK_HYBRID_VI_BASE); 
      newhe = hrd_exp_share(newhe);
      return(newhe);
    }
  else
    if (cf2) {
      newhe = hrd_exp_alloc(1);
      newhe->hrd_term[0].var_index = vi2;
      newhe->hrd_term[0].coeff = cf2;
      newhe->name = linear_name(newhe->hrd_term, 1);
      newhe->name = linear_name(newhe->hrd_term, 1);
     	pi = VAR[vi2].PROC_INDEX; 
      newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI) 
                    | (variable_index[TYPE_HRD][pi][0] * MASK_HYBRID_VI_BASE); 
      newhe = hrd_exp_share(newhe);
      return(newhe);
    }
    else
      return(NULL);
}
  /* hrd_exp_pair() */






struct red_type	*rec_hybrid_delta_expression(d, e)
     struct red_type	*d, *e;
{
  struct hrd_exp_type		*newhe;
  struct red_type		*result, *conj, *ne;
  struct ddd_child_type		*ic;
  int				ci, ti, dn, dd, common_raise, common_divider;
  struct cache4_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache4_check_result_key(
    OP_HYBRID_DELTA_EXPRESSION, d, 
    (struct hrd_exp_type *) e, 
    DELTA_DIRECTION, 0
  ); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    newhe = hrd_exp_delta_coeff_counting_interval_rates
            (d->u.hrd.hrd_exp, &common_raise, &common_divider);
    if (common_raise == 1) {
      if (common_divider == 1) {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          conj = rec_hybrid_delta_expression(d->u.hrd.arc[ci].child, e);
          conj = hrd_one_constraint(conj, newhe,
                                       d->u.hrd.arc[ci].ub_numerator,
                                       d->u.hrd.arc[ci].ub_denominator
                                       );
          result = red_bop(OR, result, conj);
        }
      }
      else {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          conj = rec_hybrid_delta_expression(d->u.hrd.arc[ci].child, e);
          dn = d->u.hrd.arc[ci].ub_numerator;
          dd = d->u.hrd.arc[ci].ub_denominator;
          rational_lower(&dn, &dd, common_divider);
          conj = hrd_one_constraint(conj, newhe, dn, dd);
          result = red_bop(OR, result, conj);
        }
      }
    }
    else {
      if (common_divider == 1) {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          conj = rec_hybrid_delta_expression(d->u.hrd.arc[ci].child, e);
          dn = d->u.hrd.arc[ci].ub_numerator;
          dd = d->u.hrd.arc[ci].ub_denominator;
          rational_lift(&dn, &dd, common_raise);
          conj = hrd_one_constraint(conj, newhe, dn, dd);
          result = red_bop(OR, result, conj);
        }
      }
      else {
        for (ci = 0; ci < d->u.hrd.child_count; ci++) {
          conj = rec_hybrid_delta_expression(d->u.hrd.arc[ci].child, e);
          dn = d->u.hrd.arc[ci].ub_numerator;
          dd = d->u.hrd.arc[ci].ub_denominator;
          rational_lower(&dn, &dd, common_divider);
          rational_lift(&dn, &dd, common_raise);
          conj = hrd_one_constraint(conj, newhe, dn, dd);
          result = red_bop(OR, result, conj);
        }
      }
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = fdd_lone_subtree(
        rec_hybrid_delta_expression(d->u.fdd.arc[ci].child, e),
	d->var_index, d->u.fdd.arc[ci].lower_bound,
	d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = dfdd_lone_subtree(
        rec_hybrid_delta_expression(d->u.dfdd.arc[ci].child, e),
	d->var_index, d->u.dfdd.arc[ci].lower_bound,
	d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
        && VAR[d->var_index].PROC_INDEX
        && VAR[d->var_index].OFFSET == OFFSET_MODE
        ) {
      int	mi, ri, vi, pi;

      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        for (mi = d->u.ddd.arc[ci].lower_bound; mi <= d->u.ddd.arc[ci].upper_bound; mi++) {
          for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
            pi = VAR[d->var_index].PROC_INDEX;
            vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
            if (pi)
              vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
            if (   VRATE[vi].lb_denominator != RATE_DONT_CARE
                && (   VRATE[vi].lb_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator
                    || VRATE[vi].lb_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator
                    || VRATE[vi].ub_numerator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator
                    || VRATE[vi].ub_denominator != MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator
                    )
                ) {
              fprintf(RED_OUT, "\nError: a dense variable rate conflict !\n");
              bk(); 
            }
            switch (DELTA_DIRECTION) {
            case TIME_BACKWARD: /* FOR the old_hybrid_time_progress(), the following two items are revsersed.
	    			*/
              VRATE[vi].lb_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
              VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
              VRATE[vi].ub_numerator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
              VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
              break;
            case TIME_FORWARD:
              VRATE[vi].lb_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_numerator;
              VRATE[vi].lb_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].ub_denominator;
              VRATE[vi].ub_numerator = -1*MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_numerator;
              VRATE[vi].ub_denominator = MODE[mi].process_rate_spec[pi].rate_spec[ri].lb_denominator;
              break;
            }
          }
	  ne = ddd_lone_subtree(e, 
	    variable_index[TYPE_DISCRETE][PROCESS_COUNT-VAR[d->var_index].PROC_INDEX+1][VAR[d->var_index].OFFSET], 
	    mi, mi 
	  ); 
          conj = ddd_lone_subtree(
            rec_hybrid_delta_expression(d->u.ddd.arc[ci].child, ne),
            d->var_index, mi, mi
          );
          for (ri = 0; ri < MODE[mi].rate_spec_count; ri++) {
            vi = MODE[mi].process_rate_spec[pi].rate_spec[ri].var_index;
            if (pi)
              vi = variable_index[VAR[vi].TYPE][pi][VAR[vi].OFFSET];
            if (   VRATE[vi].lb_numerator != VRATE[vi].ub_numerator
               || VRATE[vi].lb_denominator != VRATE[vi].ub_denominator
               ) {
              if (VRATE[vi].lb_numerator != HYBRID_NEG_INFINITY || VRATE[vi].lb_denominator != 1) {
              	newhe = hrd_exp_pair(
              	  VI_DELTA, 
              	  VRATE[vi].lb_numerator, 
              	  VAR[vi].PRIMED_VI, 
              	  -1*VRATE[vi].lb_denominator
              	);
                conj = hrd_one_constraint(conj, newhe, 0, 1);
              }
              if (VRATE[vi].ub_numerator != HYBRID_POS_INFINITY || VRATE[vi].ub_denominator != 1) {
                newhe = hrd_exp_pair(
                  VI_DELTA, 
                  -1*VRATE[vi].ub_numerator, 
                  VAR[vi].PRIMED_VI, 
                  VRATE[vi].ub_denominator
                );
                conj = hrd_one_constraint(conj, newhe, 0, 1);
              }
            }
            VRATE[vi].lb_numerator = RATE_DONT_CARE;
            VRATE[vi].lb_denominator = RATE_DONT_CARE;
            VRATE[vi].ub_numerator = RATE_DONT_CARE;
            VRATE[vi].ub_denominator = RATE_DONT_CARE;
          }
          result = red_bop(OR, result, conj);
        }
      }
    }
    else {
      for (ci = 0; ci < d->u.ddd.child_count; ci++) {
        conj = ddd_lone_subtree(
          rec_hybrid_delta_expression(d->u.ddd.arc[ci].child, e),
	  d->var_index, d->u.ddd.arc[ci].lower_bound,
	  d->u.ddd.arc[ci].upper_bound
	);
        result = red_bop(OR, result, conj);
      }
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_delta_expression() */



struct red_type	*hybrid_delta_expression(d, direction)
	struct red_type	*d;
	int		direction;
{
  int			vi;
  struct red_type	*result;

  DELTA_DIRECTION = direction;
  for (vi = 0; vi < VARIABLE_COUNT; vi++) {
    switch (VAR[vi].TYPE) {
    case TYPE_DENSE:
      if (VAR[vi].PROC_INDEX && !(VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
        VRATE[vi].lb_numerator = RATE_DONT_CARE;
        VRATE[vi].lb_denominator = RATE_DONT_CARE;
        VRATE[vi].ub_numerator = RATE_DONT_CARE;
        VRATE[vi].ub_denominator = RATE_DONT_CARE;
      }
      else {
        VRATE[vi].lb_numerator = 0;
        VRATE[vi].lb_denominator = 1;
        VRATE[vi].ub_numerator = 0;
        VRATE[vi].ub_denominator = 1;
      }
      break;

    case TYPE_CLOCK:
      VRATE[vi].lb_numerator = DELTA_DIRECTION;
      VRATE[vi].lb_denominator = 1;
      VRATE[vi].ub_numerator = DELTA_DIRECTION;
      VRATE[vi].ub_denominator = 1;
      break;

    default:
      VRATE[vi].lb_numerator = 0;
      VRATE[vi].lb_denominator = 0;
      VRATE[vi].ub_numerator = 0;
      VRATE[vi].ub_denominator = 0;
    }
  }
  result = rec_hybrid_delta_expression(d, NORM_NO_RESTRICTION);
  result = hrd_one_constraint(result, hrd_exp_pair(VI_DELTA, -1, 0, 0), 0, 1);

  return(result);
}
  /* hybrid_delta_expression() */





struct hrd_exp_type	*hrd_exp_inactive_change_back(he, vi, common_divider_ptr)
	struct hrd_exp_type	*he;
	int			vi, *common_divider_ptr;
{
  int			timax, new_len, ti, oti;
  struct hrd_exp_type	*newhe;

  timax = (he->status & MASK_HYBRID_LENGTH) - 1;
  if (   he->hrd_term[timax].var_index != vi 
      && he->hrd_term[timax].var_index != VAR[vi].PRIMED_VI
      ) {
    *common_divider_ptr = 1;
    return(he);
  }
  else if (   (   timax == 0 
               && he->hrd_term[0].var_index == VAR[vi].PRIMED_VI
               )
	   || (   timax == 1
	       && he->hrd_term[0].var_index == VI_DELTA
	       && he->hrd_term[1].var_index == VAR[vi].PRIMED_VI
	       )
	   ) {
    return(NULL);
  }

  new_len = he->status & MASK_HYBRID_LENGTH;
  if (he->hrd_term[0].var_index == VI_DELTA) {
    new_len--;
    oti = 1;
  }
  else {
    oti = 0;
  }
  if (he->hrd_term[0].var_index == VAR[vi].PRIMED_VI)
    new_len--;

  newhe = hrd_exp_alloc(new_len);
  newhe->status = (newhe->status & ~MASK_HYBRID_LIFTED_VI) 
                | (he->status & MASK_HYBRID_LIFTED_VI); 
  for (ti = 0; ti < new_len; ti++, oti++) {
    newhe->hrd_term[ti].var_index = he->hrd_term[oti].var_index;
    newhe->hrd_term[ti].coeff = he->hrd_term[oti].coeff;
  }
  *common_divider_ptr = newhe->hrd_term[0].coeff;
  for (ti = 1; ti < new_len; ti++)
    *common_divider_ptr = gcd(*common_divider_ptr, newhe->hrd_term[ti].coeff);
  *common_divider_ptr = abs(*common_divider_ptr);
  if (*common_divider_ptr != 1)
    for (ti = 0; ti < new_len; ti++)
      newhe->hrd_term[ti].coeff = newhe->hrd_term[ti].coeff / *common_divider_ptr;
  newhe->name = linear_name(newhe->hrd_term, new_len);
  newhe = hrd_exp_share(newhe);
  return(newhe);
}
  /* hrd_exp_inactive_change_back() */





struct red_type	*rec_hybrid_delta_expression_inactive_change_back(d)
     struct red_type	*d;
{
  struct hrd_exp_type		*newhe;
  struct red_type		*result, *conj;
  struct ddd_child_type		*ic;
  int				ci, ti, dn, dd, common_divider;
  struct cache2_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE)
    return(NORM_TRUE);
  else if (d->var_index == TYPE_FALSE)
    return(NORM_FALSE);

  ce = cache2_check_result_key(
    OP_HYBRID_DELTA_EXPRESSION_INACTIVE_CHANGE_BACK, d, 
    (struct red_type *) HVI_DOWNWARD
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    newhe = hrd_exp_inactive_change_back(d->u.hrd.hrd_exp, HVI_DOWNWARD, &common_divider);
    if (!newhe) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = rec_hybrid_delta_expression_inactive_change_back(d->u.hrd.arc[ci].child);
	result = red_bop(OR, result, conj);
      }
    }
    else if (common_divider == 1) {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = rec_hybrid_delta_expression_inactive_change_back(d->u.hrd.arc[ci].child);
        conj = hrd_one_constraint(conj, newhe,
				     d->u.hrd.arc[ci].ub_numerator,
				     d->u.hrd.arc[ci].ub_denominator
				     );
	result = red_bop(OR, result, conj);
      }
    }
    else {
      for (ci = 0; ci < d->u.hrd.child_count; ci++) {
        conj = rec_hybrid_delta_expression_inactive_change_back(d->u.hrd.arc[ci].child);
        dn = d->u.hrd.arc[ci].ub_numerator;
        dd = d->u.hrd.arc[ci].ub_denominator;
	rational_lower(&dn, &dd, common_divider);
        conj = hrd_one_constraint(conj, newhe, dn, dd);
	result = red_bop(OR, result, conj);
      }
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      conj = rec_hybrid_delta_expression_inactive_change_back(
        d->u.fdd.arc[ci].child
      );
      conj = fdd_lone_subtree(conj, d->var_index, 
        d->u.fdd.arc[ci].lower_bound, d->u.fdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      conj = rec_hybrid_delta_expression_inactive_change_back(
        d->u.dfdd.arc[ci].child
      );
      conj = dfdd_lone_subtree(conj, d->var_index, 
        d->u.dfdd.arc[ci].lower_bound, d->u.dfdd.arc[ci].upper_bound
      );
      result = red_bop(OR, result, conj);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      conj = rec_hybrid_delta_expression_inactive_change_back(d->u.ddd.arc[ci].child);
      conj = ddd_lone_subtree(conj, d->var_index, d->u.ddd.arc[ci].lower_bound,
				   d->u.ddd.arc[ci].upper_bound
				   );
      result = red_bop(OR, result, conj);
    }
  }
  return(ce->result = result); 
}
/* rec_hybrid_delta_expression_inactive_change_back() */



struct red_type	*hybrid_delta_expression_inactive_change_back(d, vi)
	struct red_type	*d;
	int		vi;
{
  struct red_type	*result;

  HVI_DOWNWARD = vi;
  result = rec_hybrid_delta_expression_inactive_change_back(d);

  return(result);
}
  /* hybrid_delta_expression_inactive_change_back() */






struct index_link_type	*all_pv_list; 

void	rec_hybrid_collect_all_primed(d) 
     struct red_type	*d;
{
  int				ti, vi, ci;
  struct hrd_exp_type		*ohe;
  struct cache1_hash_entry_type	*ce; 

/*  if (mbug_flag)
    fprintf(RED_OUT, "In rec_reset_clock(%1x) d->var_index = %1d\n",
	    d, d->var_index
	    );
*/
  if (d->var_index == TYPE_TRUE || d->var_index == TYPE_FALSE)
    return;

  if (d->status & MASK_STACK_MULTIPLE[TOP_LEVEL_RESULT_STACK])
    if (d->result_stack->result)
      return;
    else
      d->result_stack->result = NORM_NO_RESTRICTION;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_HRD:
    ohe = d->u.hrd.hrd_exp;
    ci = 0; /* as a flag for primed variables */
    for (ti = 0; ti < (ohe->status & MASK_HYBRID_LENGTH); ti++) {
      vi = ohe->hrd_term[ti].var_index;
      if (VAR[vi].TYPE == TYPE_DENSE && (VAR[vi].STATUS & FLAG_VAR_PRIMED)) {
	all_pv_list = add_index(all_pv_list, vi); 
      }
    }
    for (ci = 0; ci < d->u.hrd.child_count; ci++) {
      rec_hybrid_collect_all_primed(d->u.hrd.arc[ci].child);
    }
    break;

  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      rec_hybrid_collect_all_primed(d->u.fdd.arc[ci].child);
    }
    break;

  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      rec_hybrid_collect_all_primed(d->u.dfdd.arc[ci].child);
    }
    break;

  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      rec_hybrid_collect_all_primed(d->u.ddd.arc[ci].child);
    }
  }
}
/* rec_hybrid_collect_all_primed() */



struct index_link_type	*hybrid_collect_all_primed(
  struct red_type	*d
) { 
  all_pv_list = NULL; 
  
  red_init_result(d); 
  rec_hybrid_collect_all_primed(d); 
  red_clear_result(); 
  
  return(all_pv_list); 
}
  /* hybrid_collect_all_primed() */ 
  
  
  

int	count_hybrid_time_progress = 0; 

struct red_type	*hybrid_time_progress(w, path, direction)
     int	w, path, direction;
{
  int				vi, pi, inactive;
  struct red_type		*result;
  struct index_link_type	*pv_list, *ppv; 
  
  if (   RT[path] == NORM_NO_RESTRICTION
      || RT[path] == RT[DECLARED_GLOBAL_INVARIANCE]
      )  
    path = REFINED_GLOBAL_INVARIANCE; 
    
  #if RED_DEBUG_HYBRID_MODE 
  switch (direction) { 
  case TIME_BACKWARD: 
    if (ITERATE_SXI < SYNC_XTION_COUNT) {
      print_cpu_time("HT %1d, BK %d, SXI %d, entering hybrid time progress()\n", 
        ++count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
      ); 
      print_sync_xtion(ITERATE_SXI, SYNC_XTION);
    }
    else 
      print_cpu_time("HT %1d, BK %d, SX BULK, entering hybrid time progress()\n", 
        ++count_hybrid_time_progress, ITERATION_COUNT 
      ); 
    break; 
  case TIME_FORWARD: 
    if (ITERATE_SXI < SYNC_XTION_COUNT) {
      print_cpu_time("HT %1d, FW %d, SXI %d, entering hybrid time progress()\n", 
        ++count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
      ); 
      print_sync_xtion(ITERATE_SXI, SYNC_XTION);
    }
    else 
      print_cpu_time("HT %1d, FW %d, SX BULK, entering hybrid time progress()\n", 
        ++count_hybrid_time_progress, ITERATION_COUNT 
      ); 
    break; 
  }
  red_print_graph(RT[w]);
  #endif 

  status_hybrid = status_hybrid | FLAG_HYBRID_DELTA_TRANSITIVITY;
  position_hybrid = HYBRID_POSITION_DELTA_XTIVITY;
  RT[w] = hybrid_delta_expression(RT[w], direction);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, after hybrid delta expression\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  
  /* We shall replace constant-rate inactives 
   * for their primed copies so that they
   * can be avoided of delta-transitivity 
   * in the first pass for umprimed variables.
   * They will be changed back to umprimed copies 
   * before the delta-transitivity for primed variables.
   * Hopefully, this can give us some control of the complexity.
   */
  for (vi = 0; vi < VARIABLE_COUNT; vi++)
    if (   VAR[vi].PROC_INDEX
	&& (VAR[vi].TYPE == TYPE_CLOCK || VAR[vi].TYPE == TYPE_DENSE)
	&& !(VAR[vi].STATUS & FLAG_VAR_PRIMED)
	) {
      int	umprimed;

      HVI_DOWNWARD = VAR[vi].PRIMED_VI; 
      RT[inactive = RT_TOP++] = red_var_absence(RT[w], vi); 
      RT[w] = red_var_presence(RT[w], vi); 
      RT[inactive] = red_bop(OR, RT[inactive], 
        red_bop(EXTRACT, RT[w], VAR[vi].RED_INACTIVE)
      );
      RT[inactive] = red_bop(OR, RT[inactive],
	red_bop(AND, RT[w], VAR[vi].RED_TIMED_INACTIVE)
      );
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "vi=%1d:%s, HVI_DOWNWARD=%1d:%s\n", 
        vi, VAR[vi].NAME, HVI_DOWNWARD, VAR[HVI_DOWNWARD].NAME
      ); 
/*
      fprintf(RED_OUT, "vi:%1d:%s RED_INACTIVE:\n", vi, VAR[vi].NAME); 
      red_print_graph(VAR[vi].RED_INACTIVE); 
      fprintf(RED_OUT, "vi:%1d:%s RED_ACTIVE:\n", vi, VAR[vi].NAME); 
      red_print_graph(VAR[vi].RED_ACTIVE); 
      fprintf(RED_OUT, "vi:%1d:%s RED_TIMED_INACTIVE:\n", vi, VAR[vi].NAME); 
      red_print_graph(VAR[vi].RED_TIMED_INACTIVE); 
      fprintf(RED_OUT, "vi:%1d:%s RED_TIMED_ACTIVE:\n", vi, VAR[vi].NAME); 
      red_print_graph(VAR[vi].RED_TIMED_ACTIVE); 
*/
      print_cpu_time("timed inactive extraction for VAR[vi=%1d].NAME:%s\n", vi, VAR[vi].NAME);
//      red_print_graph(RT[inactive]);
      #endif 

      RT[w] = red_bop(EXTRACT, RT[w], VAR[vi].RED_ACTIVE);
      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "active restriction for VAR[vi=%1d].NAME:%s\n", vi, VAR[vi].NAME);
//      red_print_graph(RT[w]);
      print_cpu_time("IT %d, SXI %d, before inactive for vi:%d:%s\n", 
        ITERATION_COUNT, ITERATE_SXI, vi, VAR[vi].NAME 
      ); 
      #endif 
      RT[w] = red_bop(AND, RT[w], VAR[vi].RED_TIMED_ACTIVE);

      #if RED_DEBUG_HYBRID_MODE
      fprintf(RED_OUT, "after timed active restriction for VAR[vi=%1d].NAME:%s\n", vi, VAR[vi].NAME);
//      red_print_graph(RT[w]);
      print_cpu_time("IT %d, SXI %d, before inactive for vi:%d:%s\n", 
        ITERATION_COUNT, ITERATE_SXI, vi, VAR[vi].NAME 
      ); 
      #endif 
      
      RT[inactive] = hybrid_delta_expression_inactive_change_back(
        RT[inactive], vi
      );
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("HT %1d, after inactive change backs for VAR[vi=%1d].NAME:%s\n", 
        count_hybrid_time_progress, vi, VAR[vi].NAME
      );
      red_print_graph(RT[inactive]);
      #endif 
      
      RT[w] = red_bop(OR, RT[w], RT[inactive]);
      RT_TOP--; /* inactive */
      #if RED_DEBUG_HYBRID_MODE
      print_cpu_time("HT %1d, final inactive unioning for VAR[vi=%1d].NAME:%s\n", 
        count_hybrid_time_progress, vi, VAR[vi].NAME
      );
      red_print_graph(RT[w]);
      #endif 
    }
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("IT %d, SXI %d, after inactive()\n", 
    ITERATION_COUNT, ITERATE_SXI
  ); 
//  red_print_graph(RT[w]);
  #endif 
  
  garbage_collect(FLAG_GC_SILENT);

  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("IT %d, SXI %d, after 1st garbage collection()\n", 
    ITERATION_COUNT, ITERATE_SXI
  ); 
  #endif 
  
  pv_list = hybrid_collect_all_primed(RT[w]); 

  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, after collect all primed\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  for (; pv_list; ppv = pv_list, pv_list = ppv->next_index_link, free(ppv)) {
    vi = pv_list->index;  
    HVI_DOWNWARD = vi;
    #if RED_DEBUG_HYBRID_MODE
    fprintf(RED_OUT, "-----------------------------------------\nHT %1d, eliminating delta variable %1d, %s\n", 
      count_hybrid_time_progress, vi, VAR[vi].NAME
    );
    red_print_graph(RT[w]);
    #endif 

    RT[w] = hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(w, FLAG_UMPRIMED);
    garbage_collect(FLAG_GC_SILENT);

    #if RED_DEBUG_HYBRID_MODE
    print_cpu_time("HT %1d, IT %d, SXI %d, vi=%d:%s, after 3redundancy collection\n", 
      count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI, vi, VAR[vi].NAME 
    ); 
    red_print_graph(RT[w]);
    #endif 
      
    result = rec_hybrid_bypass_DOWNWARD(RT[w]);
    RT[w] = result;

    #if RED_DEBUG_HYBRID_MODE
    print_cpu_time("HT %1d, IT %d, SXI %d, vi=%d:%s, after bypassing\n", 
      count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI, vi, VAR[vi].NAME 
    ); 
    red_print_graph(RT[w]);
    #endif 
      
    RT[w] = red_variable_eliminate(RT[w], vi);

    #if RED_DEBUG_HYBRID_MODE
    print_cpu_time("HT %1d, IT %d, SXI %d, vi=%d:%s, after var elim\n", 
      count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI, vi, VAR[vi].NAME 
    ); 
    red_print_graph(RT[w]);
    #endif 
  } 
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, all bypassing\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]); 
  #endif 

  HVI_DOWNWARD = vi = VI_DELTA;

  RT[w] = red_bop(AND, RT[w], RT[path]);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, VI_DELTA, right before eliminate 3redundancy\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  RT[w] = hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(w, FLAG_UMPRIMED);

  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, VI_DELTA, after eliminate 3redundancy\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  
  garbage_collect(FLAG_GC_SILENT);
  result = rec_hybrid_bypass_DOWNWARD(RT[w]);
  RT[w] = result; 
  
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, VI_DELTA, after bypassing\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  
  RT[w] = red_variable_eliminate(RT[w], HVI_DOWNWARD);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, VI_DELTA, after var elim\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
  
  RT[w] = red_bop(AND, RT[w], RT[path]);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, IT %d, SXI %d, after path conjunction\n", 
    count_hybrid_time_progress, ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]);
  #endif 
/*
  RT[w] = hybrid_eliminate_3redundancy_DOWNWARD(w, 2);
*/
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("In hybrid_time_progress before 3 redundancy collective");
  #endif 
  
  RT[w] = hybrid_eliminate_3redundancy_DOWNWARD_COLLECTIVE(w, FLAG_UMPRIMED);
  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("HT %1d, In hybrid_time_progress after final 3 redundancy collective", count_hybrid_time_progress);
  red_print_graph(RT[w]);
  #endif 
  
  status_hybrid = status_hybrid & ~FLAG_HYBRID_DELTA_TRANSITIVITY;

  #if RED_DEBUG_HYBRID_MODE
  print_cpu_time("IT %d, SXI %d, after 3redundancy and leaving hybrid time progress\n", 
    ITERATION_COUNT, ITERATE_SXI
  ); 
  red_print_graph(RT[w]); 
  #endif 
  
  return(RT[w]);
}
/* hybrid_time_progress() */










/************************************************************************
*
*/


struct red_type	*rec_hybrid_parameter_extract(d)
     struct red_type	*d;
{
  int				ci, local_coeff;
  struct red_type		*result, *child, *grown_child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_PARAMETER_EXTRACT, d); 
  if (ce->result) { 
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    if (d->u.hrd.hrd_exp->status & FLAG_HRD_EXP_STATIC) {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_parameter_extract(d->u.hrd.arc[ci].child);
        child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				    d->u.hrd.arc[ci].ub_numerator,
				    d->u.hrd.arc[ci].ub_denominator
				    );
        result = red_bop(OR, result, child);
      }
    }
    else {
      for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
        child = rec_hybrid_parameter_extract(d->u.hrd.arc[ci].child);
        result = red_bop(OR, result, child);
      }
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_parameter_extract(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_parameter_extract(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_parameter_extract(d->u.ddd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_parameter_extract() */





struct red_type	*rec_hybrid_remove_all_discretes(d)
     struct red_type	*d;
{
  int				ci;
  struct red_type		*result, *child;
  struct hrd_exp_type		*local_exp;
  struct cache1_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION || d == NORM_FALSE)
    return(d);

  ce = cache1_check_result_key(OP_HYBRID_REMOVE_ALL_DISCRETES, d); 
  if (ce->result) {
    return(ce->result); 
  } 

  result = NORM_FALSE;
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    fprintf(RED_OUT, "\nError: a clock inequality in hybrid_bypass_DOWNWARD().\n");
    fflush(RED_OUT);
    for (; 1; );
    exit(0);

  case TYPE_HRD:
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      child = rec_hybrid_remove_all_discretes(d->u.hrd.arc[ci].child);
      child = hrd_lone_subtree(child, d->var_index, d->u.hrd.hrd_exp,
				  d->u.hrd.arc[ci].ub_numerator,
				  d->u.hrd.arc[ci].ub_denominator
				  );
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_FLOAT:
    for (ci = 0; ci < d->u.fdd.child_count; ci++) {
      child = rec_hybrid_remove_all_discretes(d->u.fdd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
    break;
  case TYPE_DOUBLE:
    for (ci = 0; ci < d->u.dfdd.child_count; ci++) {
      child = rec_hybrid_remove_all_discretes(d->u.dfdd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
    break;
  default:
    for (ci = 0; ci < d->u.ddd.child_count; ci++) {
      child = rec_hybrid_remove_all_discretes(d->u.ddd.arc[ci].child);
      result = red_bop(OR, result, child);
    }
  }
  return(ce->result = result); 
}
  /* rec_hybrid_remove_all_discretes() */






struct red_type	*hybrid_parameter_extract(d)
     struct red_type	*d;
{
  int			vi, w;
  /*
  fprintf(RED_OUT, "\nred_grow() with input:\n");
  red_print_graph(RT[w]);
  */

  RT[w = RT_TOP++] = rec_hybrid_remove_all_discretes(d);

  for (vi = 7; vi < VARIABLE_COUNT; vi++)
    switch (VAR[vi].TYPE) {
    case TYPE_DENSE:
      if (VAR[vi].PROC_INDEX == 0 && (VAR[vi].STATUS & FLAG_VAR_STATIC))
        break;
    case TYPE_CLOCK:
      RT[w] = hybrid_bypass_DOWNWARD(w, vi);
      RT[w] = red_variable_eliminate(RT[w], vi);
      break;
    }
  /*
  fprintf(RED_OUT, "\nred_grow() with output:\n");
  red_print_graph(RT[w]);
  */

  d = RT[w];
  RT_TOP--; /* w */
  return(d);
}
/* hybrid_parameter_extract() */






/************************************************************************************
*  hybrid_complement()
*/
struct hrd_exp_type	*hrd_exp_converse(he)
	struct hrd_exp_type	*he;
{
  int			ti, len;
  struct hrd_exp_type		*newhe;

  len = he->status & MASK_HYBRID_LENGTH;
  newhe = hrd_exp_alloc(len);
  for (ti = 0; ti < len; ti++) {
    newhe->hrd_term[ti].var_index = he->hrd_term[ti].var_index;
    newhe->hrd_term[ti].coeff = -1 * he->hrd_term[ti].coeff;
  }
  newhe->name = linear_name(newhe->hrd_term, len);
  newhe = hrd_exp_share(newhe);
  newhe->status = he->status;
/*    print_23tree(hrd_exp_tree, 0, hrd_exp_print);
*/
  return(newhe);
}
/* hrd_exp_converse() */







struct red_type	*hybrid_parameter_reduce(w)
	int	w;
{
  int	conj, result, tmp;

  RT[result = RT_TOP++] = NORM_FALSE;
  RT[conj = RT_TOP++] = NORM_FALSE;
  tmp = RT_TOP++;
  for (; RT[w] != NORM_FALSE; ) {
    RT[conj] = extract_one_instance(w);
    RT[tmp] = red_bop(AND, RT[conj], red_complement(red_bop(OR, RT[w], RT[result])));
    if (hybrid_eliminate_inconsistency_DOWNWARD(tmp) != NORM_FALSE)
      RT[result] = red_bop(OR, RT[conj], RT[result]);
  }
  RT_TOP = RT_TOP - 2; /* tmp, conj */
  RT[w] = RT[result];
  RT_TOP--;
  return(RT[w]);
}
  /* hybrid_parameter_reduce() */






/* This routine test with input grc-syn2.d
*/
void	test_hybrid() {
  struct hrd_exp_type	*he0, *he1, *he2, *he3, *he4, *he5, *he6, *he7, *he8, *he9, *he10;
  struct red_type	*conj, *result;
  int			w, hi;

  fprintf(RED_OUT, "\nTEST HYBRID:\n");
  for (hi = 0; hi < DEBUG_RED_COUNT; hi++) {
    fprintf(RED_OUT, "\nDEBUG_RED[%1d]:\n", hi);
    red_print_graph(DEBUG_RED[hi]);
  }
  fprintf(RED_OUT, "\nDEBUG_RED[0] excludes DEBUG_RED[1]\n");
  red_print_graph(red_bop(EXCLUDE, DEBUG_RED[0], DEBUG_RED[1])); 
  exit(0);
/*
  RT[w = RT_TOP++] = conj;
  fprintf(RED_OUT, "test hybrid RT[w]:\n");
  red_print_graph(RT[w]);

  RT[w] = hybrid_reduce(w, REACHABLE);
  fprintf(RED_OUT, "the collective reduction result:\n");
  red_print_graph(RT[w]);

  exit(0);
*/
}
  /* test_hybrid() */





void	test_hybrid_time_progress1()
{
  struct hrd_exp_type	*he0, *he1, *he2, *he3, *he4, *he5, *he6, *he7, *he8, *he9, *he10;
  struct red_type	*conj, *result;
  int			w;

  fprintf(RED_OUT, "\nTEST HYBRID TIME PROGRESS:\n");

  /* based on grc-syn3.d */
/*
0<=CUTOFF<=40
     (2)V=24:mode[1];81a9e40;1000;IC=1;[g_lowering]81a9e10;
       (3)V=28:(-x[1]);81a9e10;1000;IC=1;<=0:81a9de0;
         (4)V=28:(x[1]);81a9de0;1000;IC=1;<=90:81a5670;
           (5)V=32:mode[2];81a5670;1000;IC=1;[down]8210720;
             (6)V=40:mode[3];8210720;1000;IC=1;[R1]82106f0;
               (7)V=44:(-x[3]);82106f0;1000;IC=1;<=-20:819a7d0;
                 (8)V=44:(x[3]);819a7d0;1000;IC=1;<=40:8194178;
                     (10)V=44:(-x[1]-9x[3]);818d3d8;1000;IC=1;<=-270:818d3a8;
                       (11)V=48:mode[4];818d3a8;1000;IC=1;[far2]81923a0;
                         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
                           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
                             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
                               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  /* -CUTOFF */
  he0 = hrd_exp_alloc(1);
  he0->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he0->hrd_term[0].coeff = -1;
  he0->name = linear_name(he0->hrd_term, 1);
  he0 = hrd_exp_share(he0);
  he0->status = (hybrid_variable_index(he0) * MASK_HYBRID_VI_BASE)
	      | (he0->status & ~MASK_HYBRID_LIFTED_VI);

  /* CUTOFF */
  he1 = hrd_exp_alloc(1);
  he1->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he1->hrd_term[0].coeff = 1;
  he1->name = linear_name(he1->hrd_term, 1);
  he1 = hrd_exp_share(he1);
  he1->status = (hybrid_variable_index(he1) * MASK_HYBRID_VI_BASE)
	      | (he1->status & ~MASK_HYBRID_LIFTED_VI);

/*
       (3)V=28:(-x[1]);81a9e10;1000;IC=1;<=0:81a9de0;
         (4)V=28:(x[1]);81a9de0;1000;IC=1;<=90:81a5670;
           (5)V=32:mode[2];81a5670;1000;IC=1;[down]8210720;
             (6)V=40:mode[3];8210720;1000;IC=1;[R1]82106f0;
               (7)V=44:(-x[3]);82106f0;1000;IC=1;<=-20:819a7d0;
                 (8)V=44:(x[3]);819a7d0;1000;IC=1;<=40:8194178;
                     (10)V=44:(-x[1]-9x[3]);818d3d8;1000;IC=1;<=-270:818d3a8;
                       (11)V=48:mode[4];818d3a8;1000;IC=1;[far2]81923a0;
                         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
                           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
                             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
                               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/

  /* -x1 */
  he2 = hrd_exp_alloc(1);
  he2->hrd_term[0].var_index = variable_index[TYPE_DENSE][1][0];
  he2->hrd_term[0].coeff = -1;
  he2->name = linear_name(he2->hrd_term, 1);
  he2 = hrd_exp_share(he2);
  he2->status = (hybrid_variable_index(he2) * MASK_HYBRID_VI_BASE)
	      | (he2->status & ~MASK_HYBRID_LIFTED_VI);

  /* x1 */
  he3 = hrd_exp_alloc(1);
  he3->hrd_term[0].var_index = variable_index[TYPE_DENSE][1][0];
  he3->hrd_term[0].coeff = 1;
  he3->name = linear_name(he3->hrd_term, 1);
  he3 = hrd_exp_share(he3);
  he3->status = (hybrid_variable_index(he3) * MASK_HYBRID_VI_BASE)
	      | (he3->status & ~MASK_HYBRID_LIFTED_VI);

/*
 (7)V=44:(-x[3]);82106f0;1000;IC=1;<=-20:819a7d0;
   (8)V=44:(x[3]);819a7d0;1000;IC=1;<=40:8194178;
     (10)V=44:(-x[1]-9x[3]);818d3d8;1000;IC=1;<=-270:818d3a8;
       (11)V=48:mode[4];818d3a8;1000;IC=1;[far2]81923a0;
         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  he4 = hrd_exp_alloc(1);
  he4->hrd_term[0].var_index = variable_index[TYPE_DENSE][3][0];
  he4->hrd_term[0].coeff = -1;
  he4->name = linear_name(he4->hrd_term, 1);
  he4 = hrd_exp_share(he4);
  he4->status = (hybrid_variable_index(he4) * MASK_HYBRID_VI_BASE)
	      | (he4->status & ~MASK_HYBRID_LIFTED_VI);

  he5 = hrd_exp_alloc(1);
  he5->hrd_term[0].var_index = variable_index[TYPE_DENSE][3][0];
  he5->hrd_term[0].coeff = 1;
  he5->name = linear_name(he5->hrd_term, 1);
  he5 = hrd_exp_share(he5);
  he5->status = (hybrid_variable_index(he5) * MASK_HYBRID_VI_BASE)
	      | (he5->status & ~MASK_HYBRID_LIFTED_VI);
/*
     (10)V=44:(-x[1]-9x[3]);818d3d8;1000;IC=1;<=-270:818d3a8;
       (11)V=48:mode[4];818d3a8;1000;IC=1;[far2]81923a0;
         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  /* -x1-9x3 */
  he6 = hrd_exp_alloc(2);
  he6->hrd_term[0].var_index = variable_index[TYPE_DENSE][1][0];
  he6->hrd_term[0].coeff = -1;
  he6->hrd_term[1].var_index = variable_index[TYPE_DENSE][3][0];
  he6->hrd_term[1].coeff = -9;
  he6->name = linear_name(he6->hrd_term, 2);
  he6 = hrd_exp_share(he6);
  he6->status = (hybrid_variable_index(he6) * MASK_HYBRID_VI_BASE)
	      | (he6->status & ~MASK_HYBRID_LIFTED_VI);


/*
         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  he7 = hrd_exp_alloc(1);
  he7->hrd_term[0].var_index = variable_index[TYPE_DENSE][4][0];
  he7->hrd_term[0].coeff = 1;
  he7->name = linear_name(he7->hrd_term, 1);
  he7 = hrd_exp_share(he7);
  he7->status = (hybrid_variable_index(he7) * MASK_HYBRID_VI_BASE)
	      | (he7->status & ~MASK_HYBRID_LIFTED_VI);


/*
             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  he8 = hrd_exp_alloc(1);
  he8->hrd_term[0].var_index = variable_index[TYPE_DENSE][5][0];
  he8->hrd_term[0].coeff = -1;
  he8->name = linear_name(he8->hrd_term, 1);
  he8 = hrd_exp_share(he8);
  he8->status = (hybrid_variable_index(he8) * MASK_HYBRID_VI_BASE)
	      | (he8->status & ~MASK_HYBRID_LIFTED_VI);

  he9 = hrd_exp_alloc(1);
  he9->hrd_term[0].var_index = variable_index[TYPE_DENSE][5][0];
  he9->hrd_term[0].coeff = 1;
  he9->name = linear_name(he9->hrd_term, 1);
  he9 = hrd_exp_share(he9);
  he9->status = (hybrid_variable_index(he9) * MASK_HYBRID_VI_BASE)
	      | (he9->status & ~MASK_HYBRID_LIFTED_VI);

  /* CUTOFF-x5 */
  he10 = hrd_exp_alloc(2);
  he10->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he10->hrd_term[0].coeff = 1;
  he10->hrd_term[1].var_index = variable_index[TYPE_DENSE][5][0];
  he10->hrd_term[1].coeff = -1;
  he10->name = linear_name(he10->hrd_term, 2);
  he10 = hrd_exp_share(he10);
  he10->status = (hybrid_variable_index(he10) * MASK_HYBRID_VI_BASE)
	      | (he10->status & ~MASK_HYBRID_LIFTED_VI);

/*
0<=CUTOFF<=40
     (2)V=24:mode[1];81a9e40;1000;IC=1;[g_lowering]81a9e10;
       (3)V=28:(-x[1]);81a9e10;1000;IC=1;<=0:81a9de0;
         (4)V=28:(x[1]);81a9de0;1000;IC=1;<=90:81a5670;
           (5)V=32:mode[2];81a5670;1000;IC=1;[down]8210720;
             (6)V=40:mode[3];8210720;1000;IC=1;[R1]82106f0;
               (7)V=44:(-x[3]);82106f0;1000;IC=1;<=-20:819a7d0;
                 (8)V=44:(x[3]);819a7d0;1000;IC=1;<=40:8194178;
                     (10)V=44:(-x[1]-9x[3]);818d3d8;1000;IC=1;<=-270:818d3a8;
                       (11)V=48:mode[4];818d3a8;1000;IC=1;[far2]81923a0;
                         (12)V=52:(x[4]);81923a0;1000;IC=1;<=0:818e1a8;
                           (13)V=56:mode[5];818e1a8;3000;IC=1;[R3]818e178;
                             (14)V=60:(-x[5]);818e178;1000;IC=1;<=-30:818b500;
                               (15)V=60:(x[5]);818b500;1082;IC=1;<=40:817c1c0;
                                 (16)V=60:(CUTOFF-x[5]);817c1c0;1092;IC=1;<=0:TRUE;
*/
  conj = NORM_NO_RESTRICTION;
  conj = hrd_one_constraint(conj, he0, 0, 1);
  conj = hrd_one_constraint(conj, he1, 80, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][1][0], 3, 3);
  conj = hrd_one_constraint(conj, he2, 0, 1);
  conj = hrd_one_constraint(conj, he3, 180, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][2][0], 5, 5);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][3][0], 8, 8);
  conj = hrd_one_constraint(conj, he4, -40, 1);
  conj = hrd_one_constraint(conj, he5, 80, 1);
  conj = hrd_one_constraint(conj, he6, -540, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][4][0], 10, 10);
  conj = hrd_one_constraint(conj, he7, 0, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][5][0], 14, 14);
  conj = hrd_one_constraint(conj, he8, -60, 1);
  conj = hrd_one_constraint(conj, he9, 80, 1);
  conj = hrd_one_constraint(conj, he10, 0, 1);

  red_test_hybrid = conj;
  red_mark(conj, FLAG_GC_STABLE);

  fprintf(RED_OUT, "\n\nin test hybrid time progress \n");
  fprintf(RED_OUT, "conj:\n");
  red_print_graph(conj);
  RT[w = RT_TOP++] = conj;

  result = hybrid_time_progress(w, TIME_BACKWARD);
  fprintf(RED_OUT, "\nbackward progressed result:\n");
  red_print_graph(result);
  fflush(RED_OUT);

  exit(0);
}
  /* test_hybrid_time_progress() */






void	test_hybrid_time_progress()
{
  struct hrd_exp_type	*he0, *he1, *he2, *he3, *he4, *he5, *he6, *he7, *he8, *he9, *he10;
  struct red_type	*conj, *result;
  int			w;

  fprintf(RED_OUT, "\nTEST HYBRID TIME PROGRESS:\n");

  /* based on grc-syn3.d */
/*
 (0)V=8:k;8195c40;1000;IC=1;[2,2]81a1b60;
   (1)V=18:(-a);81a1b60;1000;IC=1;<=0:8190ea8;
     (2)V=22:mode[1];8190ea8;1000;IC=1;[p1_loc_2]817dcb0;
       (3)V=26:(-x[1]);817dcb0;1000;IC=1;<=0:819caa8;
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
 */
  he0 = hrd_exp_alloc(1);
  he0->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he0->hrd_term[0].coeff = -1;
  he0->name = linear_name(he0->hrd_term, 1);
  he0 = hrd_exp_share(he0);
  he0->status = (hybrid_variable_index(he0) * MASK_HYBRID_VI_BASE)
	      | (he0->status & ~MASK_HYBRID_LIFTED_VI);
/*
       (3)V=26:(-x[1]);817dcb0;1000;IC=1;<=0:819caa8;
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/
  he1 = hrd_exp_alloc(1);
  he1->hrd_term[0].var_index = variable_index[TYPE_DENSE][1][0];
  he1->hrd_term[0].coeff = -1;
  he1->name = linear_name(he1->hrd_term, 1);
  he1 = hrd_exp_share(he1);
  he1->status = (hybrid_variable_index(he1) * MASK_HYBRID_VI_BASE)
	      | (he1->status & ~MASK_HYBRID_LIFTED_VI);

/*
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/

  /* -x1 */
  he2 = hrd_exp_alloc(2);
  he2->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he2->hrd_term[0].coeff = -1;
  he2->hrd_term[1].var_index = variable_index[TYPE_DENSE][1][0];
  he2->hrd_term[1].coeff = 1;
  he2->name = linear_name(he2->hrd_term, 2);
  he2 = hrd_exp_share(he2);
  he2->status = (hybrid_variable_index(he2) * MASK_HYBRID_VI_BASE)
	      | (he2->status & ~MASK_HYBRID_LIFTED_VI);

/*
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/
  he3 = hrd_exp_alloc(1);
  he3->hrd_term[0].var_index = variable_index[TYPE_DENSE][2][0];
  he3->hrd_term[0].coeff = -1;
  he3->name = linear_name(he3->hrd_term, 1);
  he3 = hrd_exp_share(he3);
  he3->status = (hybrid_variable_index(he3) * MASK_HYBRID_VI_BASE)
	      | (he3->status & ~MASK_HYBRID_LIFTED_VI);

/*
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/
  he4 = hrd_exp_alloc(4);
  he4->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he4->hrd_term[0].coeff = -11;
  he4->hrd_term[1].var_index = variable_index[TYPE_DENSE][0][4];
  he4->hrd_term[1].coeff = 8;
  he4->hrd_term[2].var_index = variable_index[TYPE_DENSE][1][0];
  he4->hrd_term[2].coeff = 11;
  he4->hrd_term[3].var_index = variable_index[TYPE_DENSE][2][0];
  he4->hrd_term[3].coeff = -8;
  he4->name = linear_name(he4->hrd_term, 4);
  he4 = hrd_exp_share(he4);
  he4->status = (hybrid_variable_index(he4) * MASK_HYBRID_VI_BASE)
	      | (he4->status & ~MASK_HYBRID_LIFTED_VI);

  he5 = hrd_exp_alloc(1);
  he5->hrd_term[0].var_index = variable_index[TYPE_DENSE][3][0];
  he5->hrd_term[0].coeff = -1;
  he5->name = linear_name(he5->hrd_term, 1);
  he5 = hrd_exp_share(he5);
  he5->status = (hybrid_variable_index(he5) * MASK_HYBRID_VI_BASE)
	      | (he5->status & ~MASK_HYBRID_LIFTED_VI);
/*
*/
  /* -x1-9x3 */
  he6 = hrd_exp_alloc(2);
  he6->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][4];
  he6->hrd_term[0].coeff = 1;
  he6->hrd_term[1].var_index = variable_index[TYPE_DENSE][3][0];
  he6->hrd_term[1].coeff = -1;
  he6->name = linear_name(he6->hrd_term, 2);
  he6 = hrd_exp_share(he6);
  he6->status = (hybrid_variable_index(he6) * MASK_HYBRID_VI_BASE)
	      | (he6->status & ~MASK_HYBRID_LIFTED_VI);


/*
 (0)V=8:k;8195c40;1000;IC=1;[2,2]81a1b60;
   (1)V=18:(-a);81a1b60;1000;IC=1;<=0:8190ea8;
     (2)V=22:mode[1];8190ea8;1000;IC=1;[p1_loc_2]817dcb0;
       (3)V=26:(-x[1]);817dcb0;1000;IC=1;<=0:819caa8;
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
 */
  conj = NORM_NO_RESTRICTION;
  conj = ddd_one_constraint(conj, variable_index[TYPE_POINTER][0][0], 2, 2);
  conj = hrd_one_constraint(conj, he0, 0, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][1][0], 1, 1);
  conj = hrd_one_constraint(conj, he1, 0, 1);
  conj = hrd_one_constraint(conj, he2, 0, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][2][0], 6, 6);
  conj = hrd_one_constraint(conj, he3, 0, 1);
  conj = hrd_one_constraint(conj, he4, 0, 1);
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][3][0], 4, 4);
/*   conj = hrd_one_constraint(conj, he5, 0, 1);
  conj = hrd_one_constraint(conj, he6, 0, 1);
*/
  conj = ddd_one_constraint(conj, variable_index[TYPE_DISCRETE][4][0], 4, 4);

  red_test_hybrid = conj;
  red_mark(conj, FLAG_GC_STABLE);

  fprintf(RED_OUT, "\n\nin test hybrid time progress \n");
  fprintf(RED_OUT, "conj:\n");
  red_print_graph(conj);
  RT[w = RT_TOP++] = conj;

  RT[w] = hybrid_time_progress(w, TIME_BACKWARD);
  fprintf(RED_OUT, "\n1st backward progressed result:\n");
  red_print_graph(RT[w]);
  fflush(RED_OUT);

  RT[w] = hybrid_time_progress(w, TIME_BACKWARD);
  fprintf(RED_OUT, "\n2nd backward progressed result:\n");
  red_print_graph(RT[w]);
  fflush(RED_OUT);

  RT[w] = hybrid_time_progress(w, TIME_BACKWARD);
  fprintf(RED_OUT, "\n3rd backward progressed result:\n");
  red_print_graph(RT[w]);
  fflush(RED_OUT);


  exit(0);
}
  /* test_hybrid_time_progress() */





void	test_hybrid_time_progress3()
{
  struct hrd_exp_type	*he0, *he1, *he2, *he3, *he4, *he5, *he6, *he7, *he8, *he9, *he10;
  struct red_type	*conj, *result;
  int			w;

  fprintf(RED_OUT, "\nTEST HYBRID TIME PROGRESS:\n");

  /* based on grc-syn3.d */
/*
 (0)V=8:k;8195c40;1000;IC=1;[2,2]81a1b60;
   (1)V=18:(-a);81a1b60;1000;IC=1;<=0:8190ea8;
     (2)V=22:mode[1];8190ea8;1000;IC=1;[p1_loc_2]817dcb0;
       (3)V=26:(-x[1]);817dcb0;1000;IC=1;<=0:819caa8;
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
 */
  he0 = hrd_exp_alloc(3);
  he0->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][0];
  he0->hrd_term[0].coeff = 4;
  he0->hrd_term[1].var_index = variable_index[TYPE_DENSE][0][2];
  he0->hrd_term[1].coeff = -5;
  he0->hrd_term[2].var_index = variable_index[TYPE_DENSE][1][0];
  he0->hrd_term[2].coeff = 5;
  he0->name = linear_name(he0->hrd_term, 3);
  he0 = hrd_exp_share(he0);
  he0->status = (hybrid_variable_index(he0) * MASK_HYBRID_VI_BASE)
	      | (he0->status & ~MASK_HYBRID_LIFTED_VI);
/*
       (3)V=26:(-x[1]);817dcb0;1000;IC=1;<=0:819caa8;
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/
  he1 = hrd_exp_alloc(4);
  he1->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][0];
  he1->hrd_term[0].coeff = -44;
  he1->hrd_term[1].var_index = variable_index[TYPE_DENSE][0][2];
  he1->hrd_term[1].coeff = -55;
  he1->hrd_term[2].var_index = variable_index[TYPE_DENSE][0][4];
  he1->hrd_term[2].coeff = 40;
  he1->hrd_term[3].var_index = variable_index[TYPE_DENSE][2][0];
  he1->hrd_term[3].coeff = -40;
  he1->name = linear_name(he1->hrd_term, 4);
  he1 = hrd_exp_share(he1);
  he1->status = (hybrid_variable_index(he1) * MASK_HYBRID_VI_BASE)
	      | (he1->status & ~MASK_HYBRID_LIFTED_VI);

/*
         (4)V=26:(-a+x[1]);819caa8;1000;IC=1;<=0:81a2930;
           (5)V=30:mode[2];81a2930;1000;IC=1;[p2_loc_3]8188de8;
             (6)V=34:(-x[2]);8188de8;1000;IC=1;<=0:8179e00;
               (7)V=34:(-11a+8b+11x[1]-8x[2]);8179e00;1000;IC=1;<=0:8186010;
                 (8)V=38:mode[3];8186010;1000;IC=1;[p2_loc_3]8196af8;
                   (9)V=42:(-x[3]);8196af8;1000;IC=1;<=0:8174788;
                     (10)V=46:mode[4];8174788;1013;IC=1;[p2_loc_1]TRUE;
*/

  /* -x1 */
  he2 = hrd_exp_alloc(4);
  he2->hrd_term[0].var_index = variable_index[TYPE_DENSE][0][2];
  he2->hrd_term[0].coeff = -11;
  he2->hrd_term[1].var_index = variable_index[TYPE_DENSE][0][4];
  he2->hrd_term[1].coeff = 8;
  he2->hrd_term[2].var_index = variable_index[TYPE_DENSE][1][0];
  he2->hrd_term[2].coeff = 11;
  he2->hrd_term[3].var_index = variable_index[TYPE_DENSE][2][0];
  he2->hrd_term[3].coeff = -8;
  he2->name = linear_name(he2->hrd_term, 4);
  he2 = hrd_exp_share(he2);
  he2->status = (hybrid_variable_index(he2) * MASK_HYBRID_VI_BASE)
	      | (he2->status & ~MASK_HYBRID_LIFTED_VI);


  GHE[0].hrd_exp = he0;
  GHE[0].ub_numerator = 0;
  GHE[0].ub_denominator = 1;

  GHE[1].hrd_exp = he1;
  GHE[1].ub_numerator = 0;
  GHE[1].ub_denominator = 1;

  GHE[2].hrd_exp = he2;
  GHE[2].ub_numerator = 0;
  GHE[2].ub_denominator = 1;

  fprintf(RED_OUT, "solution status = %1d\n",
	  Gaussian_matrix_solution(GHE, 3, GMultiple, GAUSSIAN_COMPOSE_REDUNDANCY)
	  );


  exit(0);
}
  /* test_hybrid_time_progress() */


/*****************************************************/
//start of HDD
//2004.9
/*****************************************************/
struct hrd_exp_type* converse_hrd_exp(struct hrd_exp_type* he)
{
  int len, ti, tc, tlcm, tgcd;
  struct hrd_exp_type* newhe;
  struct hrd_term_link_type	*tlist;
  
  len = he->status & MASK_HYBRID_LENGTH;
  for (tlist = NULL, tc = 0, ti = len-1; ti >= 0; ti--) {
    tlist = hrd_term_insert(tlist, he->hrd_term[ti].var_index, -1*he->hrd_term[ti].coeff, 1, &tc);
  }
  newhe = hrd_exp_new(tlist, tc, &tlcm, &tgcd);
  free_hrd_term_list(tlist);
  
  return(newhe);	
}
  /* converse_hrd_exp() */ 


struct red_type	*hdd_atom(vi, hrd_exp, lb_numerator, lb_denominator, ub_numerator, ub_denominator)
	struct hrd_exp_type	*hrd_exp;
	int			vi, ub_numerator, ub_denominator, lb_numerator, lb_denominator;
{
  struct red_type	*d;
  int			pi, ti;

  ti = ub_numerator / ub_denominator;
  pi = lb_numerator / lb_denominator;
  
  if (ti == HYBRID_POS_INFINITY && pi == HYBRID_NEG_INFINITY) {
    return(NORM_NO_RESTRICTION);
  }
  else if (ti > HYBRID_POS_INFINITY || pi > HYBRID_POS_INFINITY) {
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_atom().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_atom().\n", lb_numerator, lb_denominator);
    bk(); 
  }
  else if (ti < HYBRID_NEG_INFINITY || pi < HYBRID_NEG_INFINITY) {
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_atom().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_atom().\n", lb_numerator, lb_denominator);
    bk(); 
  }

  d = red_alloc(vi);
    /*
      lb = ub;
    */
  d->u.hdd.child_count = 1;
  d->u.hdd.hrd_exp = hrd_exp;
  d->u.hdd.arc = (struct hdd_child_type *) malloc(sizeof(struct hdd_child_type));
  hfchild_count = hfchild_count + d->u.hdd.child_count;
  d->u.hdd.arc[0].ub_numerator = ub_numerator;
  d->u.hdd.arc[0].ub_denominator = ub_denominator;
  d->u.hdd.arc[0].lb_numerator = lb_numerator;
  d->u.hdd.arc[0].lb_denominator = lb_denominator;  
  d->u.hdd.arc[0].child = NORM_TRUE;

  d = red_share(d);
/*
  red_print_graph(new);
  fflush(RED_OUT);
*/
  return(d);
}
  /* hrd_atom() */

struct red_type	*hdd_lone_subtree(d, vi, hrd_exp, lb_numerator, lb_denominator, ub_numerator, ub_denominator)
	struct red_type		*d;
	int			vi, ub_numerator, ub_denominator, lb_numerator, lb_denominator;
	struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*newd;
  int			ti,pi;

  if (VAR[vi].TYPE != TYPE_HDD) {
    fprintf(RED_OUT, "Error: A non hybrid inequality filter in hdd_lone_subtree(vi=%1d)\n", vi);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (   d != NORM_FALSE
	   && d != NORM_NO_RESTRICTION
	   && (   vi > d->var_index
	       /* || (vi == d->var_index && HRD_EXP_COMP(d->u.hrd.hrd_exp, hrd_exp) <= 0) */
	       )
	   ) {
    fprintf(RED_OUT, "Error: hybrid lone subtree violating variable-ordering.\n");
    fflush(RED_OUT);
    //for (bd = TYPE_TRUE; bd; );
  }
  if (d == NORM_FALSE)
    return(d);
  
  
  ti = ub_numerator / ub_denominator;
  pi = lb_numerator / lb_denominator;  
  if (ti == HYBRID_POS_INFINITY && pi == HYBRID_NEG_INFINITY) {
    return(d);
  }
  else if (ti > HYBRID_POS_INFINITY || pi > HYBRID_POS_INFINITY) {
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_lone_subtree().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_lone_subtree().\n", lb_numerator, lb_denominator);
    bk(); 
  }
  else if (ti < HYBRID_NEG_INFINITY || pi < HYBRID_NEG_INFINITY) {
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_lone_subtree().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_lone_subtree().\n", lb_numerator, lb_denominator);
    bk(); 
  }
  
  
  newd = red_alloc(vi);
  newd->u.hdd.hrd_exp = hrd_exp;
  newd->u.hdd.child_count = 1;
  hfchild_count++;
  newd->u.hdd.arc = (struct hdd_child_type *) malloc(sizeof(struct hdd_child_type));
  newd->u.hdd.arc[0].child = d;
  newd->u.hdd.arc[0].ub_numerator = ub_numerator;
  newd->u.hdd.arc[0].ub_denominator = ub_denominator;
  newd->u.hdd.arc[0].lb_numerator = lb_numerator;
  newd->u.hdd.arc[0].lb_denominator = lb_denominator;  
  return(red_share(newd));
  
}
/* hrd_lone_subtree() */



struct red_type	*hdd_root_restrict(d, lb_numerator, lb_denominator, ub_numerator, ub_denominator)
	struct red_type	*d;
	int		ub_numerator, ub_denominator, lb_numerator, lb_denominator;
{
  struct red_type	*result, *child;
  int			ci;
  int			pi, ti;



  ti = ub_numerator / ub_denominator;
  pi = lb_numerator / lb_denominator;
  
  if (ti == HYBRID_POS_INFINITY && pi == HYBRID_NEG_INFINITY) {
    return(d);
  }
  else if (ti > HYBRID_POS_INFINITY || pi > HYBRID_POS_INFINITY) {
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_root_restrict().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: positive overflow %1d/%1d in hdd_root_restrict().\n", lb_numerator, lb_denominator);
    bk(); 
  }
  else if (ti < HYBRID_NEG_INFINITY || pi < HYBRID_NEG_INFINITY) {
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_root_restrict().\n", ub_numerator, ub_denominator);
    fprintf(RED_OUT, "Error: negative overflow %1d/%1d in hdd_root_restrict().\n", lb_numerator, lb_denominator);
    bk(); 
  }

  result = NORM_FALSE;
  for (ci = 0; ci < d->u.hrd.child_count; ci++)
  {
    //check if ub < d->u.hdd.arc[ci].ub
    if (   (   d->u.hdd.arc[ci].ub_numerator != HYBRID_NEG_INFINITY
	    || d->u.hdd.arc[ci].ub_denominator != 1
	    )
	&& (   (   d->u.hdd.arc[ci].ub_numerator == HYBRID_POS_INFINITY
	        && d->u.hdd.arc[ci].ub_denominator == 1
	        )
	    || ub_numerator * d->u.hdd.arc[ci].ub_denominator
	       < d->u.hdd.arc[ci].ub_numerator * ub_denominator
	    )
	)
    {
    	d->u.hdd.arc[ci].ub_numerator = ub_numerator;
    	d->u.hdd.arc[ci].ub_denominator = ub_denominator;
    }    
    
    //check if lb > d->u.hdd.arc[ci].lb
    if (   (   d->u.hdd.arc[ci].lb_numerator != HYBRID_POS_INFINITY
	    || d->u.hdd.arc[ci].lb_denominator != 1
	    )
	&& (   (   d->u.hdd.arc[ci].lb_numerator == HYBRID_NEG_INFINITY
	        && d->u.hdd.arc[ci].lb_denominator == 1
	        )
	    || lb_numerator * d->u.hdd.arc[ci].lb_denominator
	       > d->u.hdd.arc[ci].lb_numerator * lb_denominator
	    )
	)
    {
    	d->u.hdd.arc[ci].lb_numerator = lb_numerator;
    	d->u.hdd.arc[ci].lb_denominator = lb_denominator;
    }    
        
    //union child with result
    child = hdd_lone_subtree(d->u.hdd.arc[ci].child,
			  d->var_index, d->u.hdd.hrd_exp,
			  d->u.hdd.arc[ci].lb_numerator,
			  d->u.hdd.arc[ci].lb_denominator, 
			  d->u.hdd.arc[ci].ub_numerator,
			  d->u.hdd.arc[ci].ub_denominator
			  );
    result = red_bop(OR, result, child);    
  }
  return result;
}
/* hybrid_root_restrict() */








char	*hfchild_stack_push(d, lb_numerator, lb_denominator, ub_numerator, ub_denominator, hfc_count_ptr)
     struct red_type	*d;
     int		lb_numerator, lb_denominator, 
			ub_numerator, ub_denominator;
{
  int	i; 
  /*
  if (ub > CLOCK_POS_INFINITY) {
    fprintf(RED_OUT, "\nError: overbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub < CLOCK_NEG_INFINITY) {
    fprintf(RED_OUT, "\nError: underbound clock inequality bound: %1d\n", ub);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  if (d == NORM_FALSE)
    return;

  for (i = TOP_CHILD_STACK; 
       i >= 0 && CHILD_STACK[i].level == TOP_LEVEL_CHILD_STACK; 
       i--
       )
    if (d == CHILD_STACK[i].d)
      return;

  child_stack_epush(); //LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]++;
  CHILD_STACK[TOP_CHILD_STACK].level = TOP_LEVEL_CHILD_STACK; 
  CHILD_STACK[TOP_CHILD_STACK].d = d; 
  CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb = lb_numerator; 
  CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den = lb_denominator; 
  CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub = ub_numerator; 
  CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den = ub_denominator;
}
/* hfchild_stack_push() */






struct red_type	*hdd_new(var_index, hrd_exp)
	int			var_index;
	struct hrd_exp_type	*hrd_exp;
{
  struct red_type	*d;
  int			flag, i, lb, ub;

  /*
  if (red_pool == NULL && free_red_count != 0) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }

  if (red_pool != NULL && free_red_count == 0) {
    fprintf(RED_OUT, "\nwhack!\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  */

  get_to_next_valid_child(); 
  switch (LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK]) {
  case 0: 
    child_stack_level_pop(); 
    return(NORM_FALSE);
  
  case 1:
  /*check: why return new only when bd==HYBRID_POS_INFINITY*/
    ub = CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub 
    / CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den;
    lb = CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb 
    / CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den;
    if (lb == HYBRID_NEG_INFINITY && ub == HYBRID_POS_INFINITY) {
      d = CHILD_STACK[TOP_CHILD_STACK].d;
      child_stack_pop();
      get_to_next_valid_child(); 
      child_stack_level_pop(); 
      return(d);
    }
  default:
    d = red_alloc(var_index);
    d->u.hdd.hrd_exp = hrd_exp;
    d->u.hdd.child_count = LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK];
    hfchild_count = hfchild_count + LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK];
    d->u.hdd.arc = (struct hdd_child_type *) 
      malloc(LEVEL_CHILD_COUNT[TOP_LEVEL_CHILD_STACK] * sizeof(struct hdd_child_type));
    for (i = 0; i < d->u.hdd.child_count; i++) {
      lb = CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb 
      / CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den;
      if (lb > HYBRID_POS_INFINITY) {
        fprintf(RED_OUT, "Error:lb positive overflow %1d/%1d in hdd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb, 
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den
		);
        fflush(RED_OUT);
        exit(0);
      }
      else if (lb < HYBRID_NEG_INFINITY) {
        fprintf(RED_OUT, "Error:lb negative overflow %1d/%1d in hdd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb, 
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den
		);
        fflush(RED_OUT);
        exit(0);
      }      
      
      ub = CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub 
      / CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den;
      if (ub > HYBRID_POS_INFINITY) {
        fprintf(RED_OUT, "Error:ub positive overflow %1d/%1d in hdd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub, 
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den
		);
        fflush(RED_OUT);
        exit(0);
      }
      else if (ub < HYBRID_NEG_INFINITY) {
        fprintf(RED_OUT, "Error:ub negative overflow %1d/%1d in hdd_new().\n",
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub, 
		CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den
		);
        fflush(RED_OUT);
        exit(0);
      }

      d->u.hdd.arc[i].lb_numerator 
      = CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb;
      d->u.hdd.arc[i].lb_denominator 
      = CHILD_STACK[TOP_CHILD_STACK].u.hdd.lb_den;
      d->u.hdd.arc[i].ub_numerator 
      = CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub;
      d->u.hdd.arc[i].ub_denominator 
      = CHILD_STACK[TOP_CHILD_STACK].u.hdd.ub_den;
      d->u.hdd.arc[i].child = CHILD_STACK[TOP_CHILD_STACK].d;
      child_stack_pop(); 
      get_to_next_valid_child(); 
    }
    child_stack_level_pop(); 
    return(red_share(d));
  }
}
  /* hdd_new() */



struct red_type	*rec_hdd_one_constraint_ascending(d)
     struct red_type	*d;
{
  int				b, ci;
  struct red_type		*new_child, *result;
  struct cache7_hash_entry_type	*ce; 

  if (d == NORM_NO_RESTRICTION)
    return(hdd_atom(ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,		       
		       ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
		       ONE_HYBRID_CONSTRAINT_UB_NUMERATOR, ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
		       )
	   );
  else if (d->var_index > ONE_HYBRID_CONSTRAINT_INDEX) {
    return(hdd_lone_subtree(d, ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,			       
			       ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
			       ONE_HYBRID_CONSTRAINT_UB_NUMERATOR, ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
			       )
	   );
  }
  else if (d->var_index == ONE_HYBRID_CONSTRAINT_INDEX) {
//todo:point HRD_EXP_COMP to function for HDD
    b = HRD_EXP_COMP(d->u.hdd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP); 
    if (b > 0) {
      /*it will never happen in HDD
      if (hexp_converse_test(d->u.hrd.hrd_exp, ONE_HYBRID_CONSTRAINT_EXP))
        d = hybrid_filter_root_extract_upperhalf(d, -1*ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
				          ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
				          );
			*/
      return(hdd_lone_subtree(d, ONE_HYBRID_CONSTRAINT_INDEX, ONE_HYBRID_CONSTRAINT_EXP,
			         ONE_HYBRID_CONSTRAINT_LB_NUMERATOR,
			         ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
			         ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
			         ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR		         
			         )
	     );
    }
    else if (b == 0) {
      return(hdd_root_restrict(d,
				ONE_HYBRID_CONSTRAINT_LB_NUMERATOR,
			    	  ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
			    	  ONE_HYBRID_CONSTRAINT_UB_NUMERATOR,
				  		ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
				  		)
	     );
    }
  }
  else if (d == NORM_FALSE)
    return(NORM_FALSE);

  ce = cache7_check_result_key(
    OP_HDD_ONE_CONSTRAINT_ASCENDING, d, 
    ONE_HYBRID_CONSTRAINT_EXP,		       
    ONE_HYBRID_CONSTRAINT_LB_NUMERATOR, ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR,
    NULL, 
    ONE_HYBRID_CONSTRAINT_UB_NUMERATOR, ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR
  ); 
  if (ce->result) {
    return(ce->result); 
  } 

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    child_stack_level_push();
    for (ci = d->u.crd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.crd.arc[ci].child);
      bchild_stack_push(new_child, d->u.crd.arc[ci].upper_bound);
    }
    result = crd_new(d->var_index);
    break;

  case TYPE_HRD:
    child_stack_level_push();
    for (ci = d->u.hrd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.hrd.arc[ci].child);
      hchild_stack_push(new_child, d->u.hrd.arc[ci].ub_numerator,
			d->u.hrd.arc[ci].ub_denominator
			);
    }
    result = hrd_new(d->var_index, d->u.hrd.hrd_exp);
    break;

  case TYPE_HDD:
    child_stack_level_push();
    for (ci = d->u.hdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.hdd.arc[ci].child);
      hfchild_stack_push(new_child, d->u.hdd.arc[ci].lb_numerator,
			 d->u.hdd.arc[ci].lb_denominator,
			 d->u.hdd.arc[ci].ub_numerator,
			 d->u.hdd.arc[ci].ub_denominator
			 );
    }
    result = hdd_new(
      d->var_index, d->u.hdd.hrd_exp
    );
    break;

  case TYPE_FLOAT:
    child_stack_level_push();
    for (ci = d->u.fdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.fdd.arc[ci].child);
      fchild_stack_push(new_child,
      			d->u.fdd.arc[ci].lower_bound,
      			d->u.fdd.arc[ci].upper_bound
      			);
    }

    result = fdd_new(d->var_index);
    break;

  case TYPE_DOUBLE:
    child_stack_level_push();
    for (ci = d->u.dfdd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.dfdd.arc[ci].child);
      dfchild_stack_push(new_child,
      			d->u.dfdd.arc[ci].lower_bound,
      			d->u.dfdd.arc[ci].upper_bound
      			);
    }

    result = dfdd_new(d->var_index);
    break;

  default:
    child_stack_level_push();
    for (ci = d->u.ddd.child_count-1; ci >= 0; ci--) {
      new_child = rec_hdd_one_constraint_ascending(d->u.ddd.arc[ci].child);
      ichild_stack_push(new_child,
      			d->u.ddd.arc[ci].lower_bound,
      			d->u.ddd.arc[ci].upper_bound
      			);
    }

    result = ddd_new(d->var_index);
  }
  return(ce->result = result); 
}
  /* rec_hdd_one_constraint_ascending() */


struct red_type	*hdd_one_constraint(d, hvi, hrd_exp, lb_numerator, lb_denominator, ub_numerator, ub_denominator)
     struct red_type		*d;
     struct hrd_exp_type	*hrd_exp;
     int			hvi, ub_numerator, ub_denominator, lb_numerator, lb_denominator;
{
  struct red_type	*result;

  if (d == NORM_FALSE)
    return(d);

  ONE_HYBRID_CONSTRAINT_INDEX = hvi;
  ONE_HYBRID_CONSTRAINT_EXP = hrd_exp;
  ONE_HYBRID_CONSTRAINT_UB_NUMERATOR = ub_numerator;
  ONE_HYBRID_CONSTRAINT_UB_DENOMINATOR = ub_denominator;
  ONE_HYBRID_CONSTRAINT_LB_NUMERATOR = lb_numerator;
  ONE_HYBRID_CONSTRAINT_LB_DENOMINATOR = lb_denominator;
  result = rec_hdd_one_constraint_ascending(d);  
  return(result);
}
/* hdd_one_constraint() */




int	hdd_comp(hx, hcx, hy, hcy)
  struct hdd_type	*hx, *hy;
  int			hcx, hcy;
{
  int	ci;

  if (ci = HRD_EXP_COMP(hx->hrd_exp, hy->hrd_exp))
    return(ci);
  else if (ci = hcx - hcy)
    return(ci);
  else for (ci = 0; ci < hcx; ci++)
    if (hx->arc[ci].ub_numerator < hy->arc[ci].ub_numerator)
      return(-1);
    else if (hx->arc[ci].ub_numerator > hy->arc[ci].ub_numerator)
      return(1);
    else if (hx->arc[ci].ub_denominator < hy->arc[ci].ub_denominator)
      return(-1);
    else if (hx->arc[ci].ub_denominator > hy->arc[ci].ub_denominator)
      return(1);
    else if (hx->arc[ci].lb_numerator < hy->arc[ci].lb_numerator)
      return(-1);
    else if (hx->arc[ci].lb_numerator > hy->arc[ci].lb_numerator)
      return(1);
    else if (hx->arc[ci].lb_denominator < hy->arc[ci].lb_denominator)
      return(-1);
    else if (hx->arc[ci].lb_denominator > hy->arc[ci].lb_denominator)
      return(1);      
    else if (hx->arc[ci].child < hy->arc[ci].child)
      return(-1);
    else if (hx->arc[ci].child > hy->arc[ci].child)
      return(1);

  return(0);
}
  /* hrd_comp() */

//end of HDD
/*****************************************************/

 








