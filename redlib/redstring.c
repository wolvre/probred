#include <stdlib.h>
#include <string.h> 
#include <stdio.h>
#include <ctype.h>
#include <malloc.h>
/*
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
*/

#include "hashman.h" 
#include "redmaclex.e" 
#include "redparse.h" 
#include "redparse.e" 
#include "exp.e" 
#include "redbop.h" 
#include "redbop.e" 
#include "redbasics.h" 
#include "redbasics.e" 


#define	FLAG_NO_SUBFORMULA_DEPTH	-1

char	sbuf[20000]; 
int	size_sbuf = 20000, 
	PI_STRING, PI_LENGTH, SUB_DEPTH = -1; 

int	rec_string_parse_subformula(
  struct ps_exp_type	*, // *psub, 
  int			, // pos, 
  struct ps_exp_type	* // *parent 
); 
  
struct string_link_type { 
  char	str[256]; 
  struct string_link_type	*next_string_link; 
};  
  /* string_link_type() */ 



char	*file_to_string(f)
	char	*f; 
{
  FILE				*fp; 
  struct string_link_type	*top, *nt, *b; 
  int				count_string_link, len; 
  char				*result; 

  fprintf(RED_OUT, "\nMacro elimination from file:%s\n", f); 
  f = macro_eliminate(f); 
  fprintf(RED_OUT, "\nMacro elimination to file:%s\n", f); 
  fflush(RED_OUT); 
  
  if ((fp = fopen(f, "r")) == NULL) {
    printf("Cannot open file %s.\n", f);
    exit(1);
  }

  top = NULL; 
  count_string_link = len = 0; 
  while(!feof(fp)) { 
    nt = (struct string_link_type *) malloc(sizeof(struct string_link_type)); 
    if(fgets(nt->str, 254, fp)) {
/* 
      printf("%s", nt->str); 
*/
      count_string_link++; 
      len = len + strlen(nt->str); 
      nt->next_string_link = top; 
      top = nt; 
    } 
    else { 
      free(nt);  
    } 
  }

  fclose(fp); 

  // reverse the list of top. 
  for (nt = top, top = NULL; nt; ) { 
    b = nt; 
    nt = b->next_string_link; 
    b->next_string_link = top; 
    top = b; 	
  } 
  result = malloc(len+1); 
  for (len = 0; top; ) { 
    sprintf(&(result[len]), "%s", top->str); 
    len = len + strlen(top->str); 
    nt = top; 
    top = top->next_string_link; 
    free(nt); 
  }
  
  return (result);
} 
  /* file_to_string() */ 
  
  
  
  

// The following routines are for converting red diagrams to strings.  
// We first define a set of procedures that calculate the length of 
// strings for a diagram. 
// Then we have procedures that allocate string spaces and fill in 
// the strings.  

int 	strlen_atom(d, lb, ub)
     struct red_type	*d;
     int		lb, ub;
{
  int			ci, mi, result;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
  case TYPE_HRD:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  default:
    if (lb == ub)
      if (   d->var_index >= MEMORY_START_VI 
          && d->var_index < VARIABLE_COUNT
          ) 
        return(2 /*==*/ + strlen(VAR[d->var_index].NAME) + 2 + hexlen(ub));
      else 
        return(2 /*==*/ + strlen(VAR[d->var_index].NAME) + intlen(ub));
    else
      if (   d->var_index >= MEMORY_START_VI 
          && d->var_index < VARIABLE_COUNT
          ) 
        return(4 
               + 2 + hexlen(lb) + 2*strlen(VAR[d->var_index].NAME) 
               + 2 + hexlen(ub)
               );
      else 
        return(4 + intlen(lb) + 2*strlen(VAR[d->var_index].NAME) + intlen(ub));
  }
}
/* strlen_atom() */



char	fbuf[100]; 

int	fltlen_sci(float f) { 
  float	a; 
  
  if (f < 0) 
    a = -1 * f; 
  if (a < 100000.0 && a > 0.0001) {
    sprintf(fbuf, "%.4f", f); 
  }
  else { 
    sprintf(fbuf, "%.4E", f); 
  }
  return(strlen(fbuf));
}
  /* fltlen_sci() */ 



int	fltlen_dcm(float f) { 
  sprintf(fbuf, "%.4f", f); 
  return(strlen(fbuf));
}
  /* fltlen_dcm() */ 


int	fltlen(float f) { 
  switch (  GSTATUS[INDEX_FLOATING_DISPLAY] 
          & MASK_FLOATING_DISPLAY_FORMAT
          ) {
  case FLAG_FLOATING_DISPLAY_SCIENTIFIC:  
    return(fltlen_sci(f)); 
  case FLAG_FLOATING_DISPLAY_DECIMAL:  
    return(fltlen_dcm(f)); 
  case FLAG_FLOATING_DISPLAY_SHORTEST: {
    int	r1, r2; 
    
    r1 = fltlen_sci(f); 
    r2 = fltlen_dcm(f); 
    if (r1 <= r2) 
      return(r1); 
    else 
      return(r2); 
  }
  default: 
    fprintf(RED_OUT, 
      "\nERROR: unspecified display format of floating-points.\n"
    );  
    bk(0); 
  }
}
  /* fltlen() */ 




int 	strlen_fatom(d, lb, ub)
     struct red_type	*d;
     float		lb, ub;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_FLOAT: 
    break; 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  }
  if (lb == ub) { 
    return(2/*==*/ + strlen(VAR[d->var_index].NAME) + fltlen(lb));
  } 
  else { 
    return(4 + fltlen(lb) + strlen(VAR[d->var_index].NAME) + fltlen(ub));
  } 
}
/* strlen_fatom() */


int	dbllen_sci(double d) { 
  double	a; 
  
  if (d < 0) 
    a = -1 * d; 
  if (a < 100000.0 && a > 0.0001) {
    sprintf(fbuf, "%.4f", d); 
  }
  else { 
    sprintf(fbuf, "%.4E", d); 
  } 
  return(strlen(fbuf));
}
  /* dbllen_sci() */ 



int	dbllen_dcm(double d) { 
  sprintf(fbuf, "%.4f", d); 
  return(strlen(fbuf));
}
  /* dbllen_dcm() */ 
  


int	dbllen(double f) { 
  switch (  GSTATUS[INDEX_FLOATING_DISPLAY] 
          & MASK_FLOATING_DISPLAY_FORMAT
          ) {
  case FLAG_FLOATING_DISPLAY_SCIENTIFIC:  
    return(dbllen_sci(f)); 
  case FLAG_FLOATING_DISPLAY_DECIMAL:  
    return(dbllen_dcm(f)); 
  case FLAG_FLOATING_DISPLAY_SHORTEST: {
    int r1, r2; 
    
    r1 = dbllen_sci(f); 
    r2 = dbllen_dcm(f); 
    if (r1 <= r2) 
      return(r1); 
    else 
      return(r2); 
  }
  default: 
    fprintf(RED_OUT, 
      "\nERROR: unspecified display format of floating-points.\n"
    );  
    bk(0); 
  }
}
  /* dbllen() */ 






int 	strlen_dfatom(d, lb, ub)
     struct red_type	*d;
     double		lb, ub;
{
  switch (VAR[d->var_index].TYPE) {
  case TYPE_DOUBLE: 
    break; 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  }
  if (lb == ub) { 
    return(2/*==*/ + strlen(VAR[d->var_index].NAME) + dbllen(lb));
  } 
  else { 
    return(4 + dbllen(lb) + strlen(VAR[d->var_index].NAME) + dbllen(ub));
  } 
}
/* strlen_dfatom() */



int 	strlen_ineq(d, ub)
     struct red_type	*d;
     int		ub;
{
  if (VAR[d->var_index].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub != CLOCK_POS_INFINITY) {
    if (VAR[d->var_index].U.CRD.CLOCK1 == 0) {
      if (ub == CLOCK_NEG_INFINITY)
	return(  1 
	       + intlen(-(ub+1)/2) 
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME)
	       );
      else if (ub % 2)
	return(  1 
	       + intlen(-(ub+1)/2)  
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME)
	       );
      else
	return(  2 
	       + intlen(-ub/2)  
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME)
	       );
    }
    else if (VAR[d->var_index].U.CRD.CLOCK2 == 0) {
      if (ub == CLOCK_NEG_INFINITY)
	return(  2 
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME)  
	       + intlen(ub/2)
	       );
      else if (ub % 2)
	return(  1 
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME)  
	       + intlen((ub+1)/2) 
	       );
      else
	return(  2 
	       + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME)  
	       + intlen(ub/2) 
	       );
    }
    else if (ub == CLOCK_NEG_INFINITY)
      return (  2 
              + strlen(VAR[d->var_index].NAME) 
              + intlen(ub/2)
              );
    else if (ub % 2)
      return (  1 
              + strlen(VAR[d->var_index].NAME)
              + intlen((ub+1)/2)
              );
    else
      return(   2 
             + strlen(VAR[d->var_index].NAME)
             + intlen(ub/2)
             );
  }
}
/* strlen_ineq() */




int	strlen_hybrid_ineq(d, ub_numerator, ub_denominator)
     struct red_type	*d;
     int		ub_numerator, ub_denominator;
{
  if (VAR[d->var_index].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub_denominator == 1) {
    if (ub_numerator % 2)
      return (  1 
              + strlen(d->u.hrd.hrd_exp->name)
              + intlen((ub_numerator+1)/2)
              );
    else
      return (  2 
              + strlen(d->u.hrd.hrd_exp->name)
              + intlen(ub_numerator/2)
              );
  }
  else {
    if (ub_numerator % 2)
      return(  2 
             + strlen(d->u.hrd.hrd_exp->name) 
             + intlen((ub_numerator+1)/2) 
             + intlen(ub_denominator)
             );
    else
      return(  3 
             + strlen(d->u.hrd.hrd_exp->name) 
             + intlen(ub_numerator/2)
             + intlen(ub_denominator)
             );
  }
}
/* strlen_hybrid_ineq() */





/*********************************************
 * The following procedures construct the strings of floating point numbers.
 */ 
int	count_string_flt_sci = 0; 
int	string_flt_sci(float f, int pos) { 
  float	a; 
  
//  fprintf(RED_OUT, "\n%1d, float %f\n", ++count_string_flt_sci, f); 
  if (f < 0) 
    a = -1 * f; 
  else 
    a = f; 
  if (a < 100000.0 && a > 0.0001) {
    sprintf(&(sbuf[pos]), "%.4f", f); 
  }
  else { 
    sprintf(&(sbuf[pos]), "%.4E", f); 
  }
  return(pos + strlen(&(sbuf[pos])));
}
  /* string_flt_sci() */ 



int	string_flt_dcm(float f, int pos) { 
  sprintf(&(sbuf[pos]), "%.4f", f); 
  return(pos + strlen(&(sbuf[pos])));
}
  /* string_flt_dcm() */ 


int	string_flt(float f, int pos) { 
  switch (  GSTATUS[INDEX_FLOATING_DISPLAY] 
          & MASK_FLOATING_DISPLAY_FORMAT
          ) {
  case FLAG_FLOATING_DISPLAY_SCIENTIFIC:  
    return(string_flt_sci(f, pos)); 
  case FLAG_FLOATING_DISPLAY_DECIMAL:  
    return(string_flt_dcm(f, pos)); 
  case FLAG_FLOATING_DISPLAY_SHORTEST: {
    int	r1, r2; 

    r1 = string_flt_sci(f, pos); 
    r2 = string_flt_dcm(f, pos); 
    if (r1 <= r2) { 
      return(string_flt_sci(f, pos)); 
    }
    else 
      return(r2); 
  }
  default: 
    fprintf(RED_OUT, 
      "\nERROR: unspecified display format of floating-points.\n"
    );  
    bk(0); 
  }
}
  /* string_flt() */ 



int	count_string_fatom2 = 0; 
int 	string_fatom(
  struct red_type	*d, 
  float			lb, 
  float			ub, 
  int			pos
) {
  switch (VAR[d->var_index].TYPE) {
  case TYPE_FLOAT: 
    break; 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  }
  if (lb == ub) { 
    sprintf(&(sbuf[pos]), "%s==", VAR[d->var_index].NAME); 
    pos = pos + 2 + strlen(VAR[d->var_index].NAME);
/*
    fprintf(RED_OUT, "\n'%1d, printing fatom %1d:%s == %f\n", 
      ++count_string_fatom2, d->var_index, VAR[d->var_index].NAME, 
      lb 
    ); 
*/
    return(string_flt(lb, pos)); 
  } 
  else { 
    pos = string_flt(lb, pos); 
    sprintf(&(sbuf[pos]), "<=%s&&%s<=", 
      VAR[d->var_index].NAME, VAR[d->var_index].NAME
    ); 
    pos = pos + 6 + 2*strlen(VAR[d->var_index].NAME);
    return(string_flt(ub, pos));
  } 
}
/* string_fatom() */


int	string_dbl_sci(double d, int pos) { 
  double	a; 

  if (d < 0) 
    a = -1 * d; 
  if (a < 100000.0 && a > 0.0001) { 
    sprintf(&(sbuf[pos]), "%.4f", d); 
  } 
  else { 
    sprintf(&(sbuf[pos]), "%.4E", d); 
  } 
  return(pos+strlen(&(sbuf[pos]))); 
} 
  /* string_dbl_sci() */ 



int	string_dbl_dcm(double d, int pos) { 
  sprintf(&(sbuf[pos]), "%.4f", d); 
  return(pos+strlen(&(sbuf[pos])));
} 
  /* string_dbl_dcm() */ 
  


int	string_dbl(double f, int pos) { 
  switch (  GSTATUS[INDEX_FLOATING_DISPLAY] 
          & MASK_FLOATING_DISPLAY_FORMAT
          ) {
  case FLAG_FLOATING_DISPLAY_SCIENTIFIC:  
    return(string_dbl_sci(f, pos)); 
  case FLAG_FLOATING_DISPLAY_DECIMAL:  
    return(string_dbl_dcm(f, pos)); 
  case FLAG_FLOATING_DISPLAY_SHORTEST: {
    int	r1, r2; 
    
    r1 = string_dbl_sci(f, pos); 
    r2 = string_dbl_dcm(f, pos); 
    if (r1 <= r2) 
      return(string_dbl_sci(f, pos)); 
    else 
      return(r2); 
  }
  default: 
    fprintf(RED_OUT, 
      "\nERROR: unspecified display format of floating-points.\n"
    );  
    bk(0); 
  }
}
  /* string_dbl() */ 



int 	string_dfatom(
  struct red_type	*d, 
  double		lb, 
  double		ub, 
  int			pos
) {
  switch (VAR[d->var_index].TYPE) {
  case TYPE_DOUBLE: 
    break; 
  default:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  }
  if (lb == ub) { 
    sprintf(&(sbuf[pos]), "%s==", VAR[d->var_index].NAME); 
    pos = pos+2+strlen(VAR[d->var_index].NAME); 
    return(string_dbl(lb, pos)); 
  } 
  else { 
    pos = string_dbl(lb, pos); 
    sprintf(&(sbuf[pos]), "<=%s&&%s<=", 
      VAR[d->var_index].NAME, VAR[d->var_index].NAME
    ); 
    pos = pos+6+2*strlen(VAR[d->var_index].NAME); 
    return(string_dbl(ub, pos));
  } 
}
/* string_dfatom() */





int 	strlen_diagram();

int	strlen_conj(
  struct red_type	*d, 
  int			ci
) {
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->u.crd.arc[ci].upper_bound == CLOCK_POS_INFINITY) 
      return(strlen_diagram(d->u.crd.arc[ci].child)); 
    else if (d->u.crd.arc[ci].child == NORM_TRUE)
      return(strlen_ineq(d, d->u.crd.arc[ci].upper_bound));
    else {
      return(  4 
             + strlen_ineq(d, d->u.crd.arc[ci].upper_bound)
             + strlen_diagram(d->u.crd.arc[ci].child)
             );
    }
    break;
  case TYPE_HRD:
    if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY 
        && d->u.hrd.arc[ci].ub_denominator == 1
        )
      return(strlen_diagram(d->u.hrd.arc[ci].child));
    else if (d->u.hrd.arc[ci].child == NORM_TRUE)
      return(strlen_hybrid_ineq(
      		d, 
      		d->u.hrd.arc[ci].ub_numerator, 
      		d->u.hrd.arc[ci].ub_denominator
      		)
      	     );
    else {
      return (  4 
              + strlen_hybrid_ineq(
              		d, 
              		d->u.hrd.arc[ci].ub_numerator, 
              		d->u.hrd.arc[ci].ub_denominator
              		)
      	      + strlen_diagram(d->u.hrd.arc[ci].child)
      	      );
    }
    break;
  case TYPE_FLOAT:
    if (d->u.fdd.arc[ci].child == NORM_TRUE)
      return(strlen_fatom(d, 
      	d->u.fdd.arc[ci].lower_bound, 
      	d->u.fdd.arc[ci].upper_bound
      ) );
    else {
      return (  4 
      + strlen_fatom(d, 
          d->u.fdd.arc[ci].lower_bound, 
      	  d->u.fdd.arc[ci].upper_bound
      	) 
      + strlen_diagram(d->u.fdd.arc[ci].child)
      );
    }
    break;
  case TYPE_DOUBLE:
    if (d->u.dfdd.arc[ci].child == NORM_TRUE)
      return(strlen_dfatom(d, 
      	d->u.dfdd.arc[ci].lower_bound, 
      	d->u.dfdd.arc[ci].upper_bound
      ) );
    else {
      return (  4 
      + strlen_dfatom(d, 
          d->u.dfdd.arc[ci].lower_bound, 
      	  d->u.dfdd.arc[ci].upper_bound
      	) 
      + strlen_diagram(d->u.dfdd.arc[ci].child)
      );
    }
    break;
  default:
    if (d->u.ddd.arc[ci].child == NORM_TRUE)
      return(strlen_atom(
      		d, 
      		d->u.ddd.arc[ci].lower_bound, 
      		d->u.ddd.arc[ci].upper_bound
      		)
      	     );
    else {
      return (  4 
      	      + strlen_atom(
      	      		d, 
      	      		d->u.ddd.arc[ci].lower_bound, 
      	      		d->u.ddd.arc[ci].upper_bound
      	      		) 
      	      + strlen_diagram(d->u.ddd.arc[ci].child)
      	      );
    }
  }
}
/* strlen_conj() */



int	strlen_diagram(
  struct red_type	*d
) {
  struct index_link_type	*pil, *pi_list, *xil, *xi_list;
  int				result, ci;

  if (VAR[d->var_index].TYPE == TYPE_FALSE)
    return(5);
  else if (VAR[d->var_index].TYPE == TYPE_TRUE)
    return(4);
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_BDD: 
    if (d->u.bdd.zero_child == d->u.bdd.one_child) { 
      fprintf(RED_OUT, "Error: Something wrong, both children of a bdd node are the same.\n"); 
      exit(0); 
    } 
    else if (d->u.bdd.zero_child == NORM_FALSE) {
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION)  
        return(strlen(VAR[d->var_index].NAME)); 
      else { 
        return (  4 
                + strlen(VAR[d->var_index].NAME)
		+ strlen_diagram(d->u.bdd.one_child)
		); 
      } 
    }
    else if (d->u.bdd.one_child == NORM_FALSE) { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION)  
        return (6 + strlen(VAR[d->var_index].NAME)); 
      else { 
        return (  10 
        	+ strlen(VAR[d->var_index].NAME) 
        	+ strlen_diagram(d->u.bdd.zero_child)
        	); 
      } 
    } 
    else { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION) { 
        result = 9 + strlen(VAR[d->var_index].NAME); 
      } 
      else { 
        result = 12 
               + strlen(VAR[d->var_index].NAME); 
               + strlen_diagram(d->u.bdd.zero_child); 
      } 
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION) { 
        return (result + 1 + strlen(VAR[d->var_index].NAME)); 
      } 
      else { 
        return (  result + 5 + strlen(VAR[d->var_index].NAME)  
                + strlen_diagram(d->u.bdd.one_child)
                ); 
      } 
    } 
    break; 
  case TYPE_CRD:
    if (d->u.crd.child_count == 1) {    
      result = strlen_ineq(d, d->u.crd.arc[0].upper_bound);
      if (d->u.crd.arc[0].child != NORM_NO_RESTRICTION) {
	if (d->u.crd.arc[0].upper_bound != CLOCK_POS_INFINITY)
	  result == 2 + result; 
	return (result + strlen_diagram(d->u.crd.arc[0].child));
      }
      else 
        return (result); 
    }
    else {
      result = 2 + strlen_conj(d, 0);
      for (ci = 1; ci < d->u.crd.child_count; ci++) {
        result = 2 + strlen_conj(d, ci);
      } 
      return (result); 
    }
    break;
  case TYPE_HRD:
    if (d->u.hrd.child_count == 1) {    
      result = strlen_hybrid_ineq(d, d->u.hrd.arc[0].ub_numerator, d->u.hrd.arc[0].ub_denominator);
      if (d->u.hrd.arc[0].child != NORM_NO_RESTRICTION) {
        return (result + 2 + strlen_diagram(d->u.hrd.arc[0].child));
      }
      else 
        return (result); 
    }
    else {
      result = 2 + strlen_conj(d, 0);
      for (ci = 1; ci < d->u.hrd.child_count; ci++) {
        result = 2 + strlen_conj(d, ci);
      } 
      return (result); 
    }
    break;
  case TYPE_FLOAT:
    if (d->u.fdd.child_count == 1) {    
      result = strlen_fatom(d, d->u.fdd.arc[0].lower_bound, d->u.fdd.arc[0].upper_bound);
      if (d->u.fdd.arc[0].child != NORM_NO_RESTRICTION) {
	return (2 + strlen_diagram(d->u.fdd.arc[0].child));
      }
      else 
        return (result); 
    }
    else {
      result = 2 + strlen_conj(d, 0);
      for (ci = 1; ci < d->u.fdd.child_count; ci++) {
        result = 2 + strlen_conj(d, ci);
      } 
      return (result); 
    }
    break;
  case TYPE_DOUBLE:
    if (d->u.dfdd.child_count == 1) {    
      result = strlen_dfatom(d, d->u.dfdd.arc[0].lower_bound, d->u.dfdd.arc[0].upper_bound);
      if (d->u.dfdd.arc[0].child != NORM_NO_RESTRICTION) {
	return (2 + strlen_diagram(d->u.dfdd.arc[0].child));
      }
      else 
        return (result); 
    }
    else {
      result = 2 + strlen_conj(d, 0);
      for (ci = 1; ci < d->u.dfdd.child_count; ci++) {
        result = 2 + strlen_conj(d, ci);
      } 
      return (result); 
    }
    break;
  default:
    if (d->u.ddd.child_count == 1) {    
      result = strlen_atom(d, d->u.ddd.arc[0].lower_bound, d->u.ddd.arc[0].upper_bound);
      if (d->u.ddd.arc[0].child != NORM_NO_RESTRICTION) {
	return (2 + strlen_diagram(d->u.ddd.arc[0].child));
      }
      else 
        return (result); 
    }
    else {
      result = 2 + strlen_conj(d, 0);
      for (ci = 1; ci < d->u.ddd.child_count; ci++) {
        result = 2 + strlen_conj(d, ci);
      } 
      return (result); 
    }
  }
}
/* strlen_diagram() */





int	string_atom(
  struct red_type	*d, 
  int			lb, 
  int			ub, 
  int			pos
) {
  int			ci, mi;
  struct ddd_child_type	*ic;

  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
  case TYPE_HRD:
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
    break;
  case TYPE_FLOAT:
    if (lb == ub) {
      sprintf(&(sbuf[pos]), "%s==", VAR[d->var_index].NAME); 
      pos = pos + 2 + strlen(VAR[d->var_index].NAME); 
      pos = string_flt(ub, pos); 
    }
    else {
      pos = string_flt(lb, pos); 
      sprintf(&(sbuf[pos]), "<=%s&&%s<=", 
        VAR[d->var_index].NAME, VAR[d->var_index].NAME
      );
      pos = pos + 6 + 2*strlen(VAR[d->var_index].NAME); 
      pos = string_flt(ub, pos); 
    }
    break;
  case TYPE_DOUBLE:
    if (lb == ub) {
      sprintf(&(sbuf[pos]), "%s==", VAR[d->var_index].NAME); 
      pos = pos + 2 + strlen(VAR[d->var_index].NAME); 
      pos = string_dbl(ub, pos); 
    }
    else {
      pos = string_dbl(lb, pos); 
      sprintf(&(sbuf[pos]), "<=%s&&%s<=", 
        VAR[d->var_index].NAME, VAR[d->var_index].NAME
      );
      pos = pos + 6 + 2*strlen(VAR[d->var_index].NAME); 
      pos = string_dbl(ub, pos); 
    }
    break;
  default:
    if (lb == ub) {
      if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
          && VAR[d->var_index].PROC_INDEX > 0
          && VAR[d->var_index].OFFSET == OFFSET_MODE
          ) { 
        sprintf(&(sbuf[pos]), "%s@(%1d)", 
          MODE[lb].name, VAR[d->var_index].PROC_INDEX  	
        ); 
        pos = pos + 3 + strlen(MODE[lb].name) +intlen(VAR[d->var_index].PROC_INDEX); 
      }
      else if (   d->var_index >= MEMORY_START_VI 
               && d->var_index < VARIABLE_COUNT
               ) { 
        sprintf(&(sbuf[pos]), 
         "%s==0x%x", VAR[d->var_index].NAME, ub
        ); 
        pos = pos + 2 + strlen(VAR[d->var_index].NAME) + 2 + hexlen(ub); 
      }
      else { 
        sprintf(&(sbuf[pos]), 
         "%s==%1d", VAR[d->var_index].NAME, ub
        ); 
        pos = pos + 2 + strlen(VAR[d->var_index].NAME) + intlen(ub); 
      }
    }
    else {
      if (   VAR[d->var_index].TYPE == TYPE_DISCRETE
          && VAR[d->var_index].PROC_INDEX > 0
          && VAR[d->var_index].OFFSET == OFFSET_MODE
          ) {
        sprintf(&(sbuf[pos]), "("); 
        pos++; 
        mi = lb; 
        sprintf(&(sbuf[pos]), "%s@(%1d)", 
          MODE[mi].name, VAR[d->var_index].PROC_INDEX  	
        ); 
        pos = pos + 3 + strlen(MODE[mi].name) +intlen(VAR[d->var_index].PROC_INDEX); 
        for (mi++; mi <= ub; mi++) { 
          sprintf(&(sbuf[pos]), "||%s@(%1d)", 
            MODE[mi].name, VAR[d->var_index].PROC_INDEX  	
          ); 
          pos = pos + 4 + strlen(MODE[mi].name) +intlen(VAR[d->var_index].PROC_INDEX); 
        }
        sprintf(&(sbuf[pos]), ")"); 
        pos++; 
      }
      else if (   d->var_index >= MEMORY_START_VI 
               && d->var_index < VARIABLE_COUNT
               ) { 
        sprintf(&(sbuf[pos]), "0x%x<=%s&&%s<=0x%x", 
          lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
        );
        pos = pos + 6 + 4 + 2*strlen(VAR[d->var_index].NAME) 
        + hexlen(lb) + hexlen(ub); 
      } 
      else { 
        sprintf(&(sbuf[pos]), "%1d<=%s&&%s<=%1d", 
          lb, VAR[d->var_index].NAME, VAR[d->var_index].NAME, ub
        );
        pos = pos + 6 + 2*strlen(VAR[d->var_index].NAME) 
        + intlen(lb) + intlen(ub); 
      }
    }
  }
  return(pos); 
}
/* string_atom() */



int	rec_string_ineq( 
  struct red_type	*d, 
  int			ub, 
  int			pos 
) {
  if (VAR[d->var_index].TYPE != TYPE_CRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (   ub < CLOCK_POS_INFINITY
           || VAR[d->var_index].U.CRD.CLOCK1 == TIME 
           ) {
    if (VAR[d->var_index].U.CRD.CLOCK1 == 0) {
      if (ub == CLOCK_NEG_INFINITY) {
	sprintf(&(sbuf[pos]), "%1d<%s", -(ub+1)/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		); 
        pos 
        = pos 
        + 1 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME) 
        + intlen(-(ub+1)/2); 
      } 
      else if (ub % 2) {
	sprintf(&(sbuf[pos]), "%1d<%s", -(ub+1)/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		); 
        pos 
        = pos 
        + 1 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME) 
        + intlen(-(ub+1)/2); 
      } 
      else {
	sprintf(&(sbuf[pos]), "%1d<=%s", -ub/2, 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME
		);
        pos 
        = pos 
        + 2 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK2]].NAME) 
        + intlen(-ub/2); 
      } 
    }
    else if (VAR[d->var_index].U.CRD.CLOCK2 == 0) {
      if (ub == CLOCK_NEG_INFINITY) {
	sprintf(&(sbuf[pos]), "%s<-%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		ub/2
		); 
        pos 
        = pos 
        + 2 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME) 
        + intlen(ub/2); 
      } 
      else if (ub % 2) {
	sprintf(&(sbuf[pos]), "%s<%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		(ub+1)/2
		); 
        pos 
        = pos 
        + 1 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME) 
        + intlen((ub+1)/2); 
      } 
      else {
	sprintf(&(sbuf[pos]), "%s<=%1d", 
		VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME, 
		ub/2
		);
        pos 
        = pos 
        + 2 
        + strlen(VAR[CLOCK[VAR[d->var_index].U.CRD.CLOCK1]].NAME) 
        + intlen(ub/2); 
      } 
    }
    else if (   ub == CLOCK_NEG_INFINITY
             && VAR[d->var_index].U.CRD.CLOCK2 != TIME
             ) {
      sprintf(&(sbuf[pos]), "%s<-%1d", VAR[d->var_index].NAME, ub/2);
      pos = pos + 2 + strlen(VAR[d->var_index].NAME) + intlen(ub/2); 
    }
    else if (ub % 2) {
      sprintf(&(sbuf[pos]), "%s<%1d", VAR[d->var_index].NAME, (ub+1)/2);
      pos = pos + 1 + strlen(VAR[d->var_index].NAME) + intlen((ub+1)/2); 
    } 
    else {
      sprintf(&(sbuf[pos]), "%s<=%1d", VAR[d->var_index].NAME, ub/2);
      pos = pos + 2 + strlen(VAR[d->var_index].NAME) + intlen(ub/2); 
    }
  } 
  return(pos); 
}
/* rec_string_ineq() */





int	rec_string_hybrid_ineq( 
  struct red_type	*d, 
  int			ub_numerator, 
  int			ub_denominator, 
  int			pos 
) {
  if (VAR[d->var_index].TYPE != TYPE_HRD) {
    fprintf(RED_OUT, "\nError:\n");
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  else if (ub_denominator == 1) {
    if (ub_numerator % 2) {
      sprintf(&(sbuf[pos]), "%s<%1d", 
      	d->u.hrd.hrd_exp->name, (ub_numerator+1)/2
      ); 
      pos = pos 
      	+ 1 
      	+ strlen(d->u.hrd.hrd_exp->name)
      	+ intlen((ub_numerator+1)/2); 
    } 
    else {
      sprintf(&(sbuf[pos]), "%s<=%1d", 
      	d->u.hrd.hrd_exp->name, ub_numerator/2
      );
      pos = pos 
      	+ 2 
      	+ strlen(d->u.hrd.hrd_exp->name)
      	+ intlen(ub_numerator/2); 
    } 
  }
  else {
    if (ub_numerator % 2) { 
      sprintf(&(sbuf[pos]), "%s<%1d/%1d", 
      	d->u.hrd.hrd_exp->name, (ub_numerator+1)/2, ub_denominator
      );
      pos = pos 
      	+ 2 
      	+ strlen(d->u.hrd.hrd_exp->name)
      	+ intlen((ub_numerator+1)/2) 
	+ intlen(ub_denominator); 
    }
    else {
      sprintf(&(sbuf[pos]), "%s<=%1d/%1d", 
      	d->u.hrd.hrd_exp->name, ub_numerator/2, ub_denominator
      );
      pos = pos 
      	+ 3 
      	+ strlen(d->u.hrd.hrd_exp->name)
      	+ intlen(ub_numerator/2) 
	+ intlen(ub_denominator); 
    } 
  }
  return(pos); 
}
/* rec_string_hybrid_ineq() */





int	rec_string_diagram(); 

int	rec_string_conj( 
  struct red_type	*d, 
  int			ci, 
  int			pos 
) {
  switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (   d->u.crd.arc[ci].upper_bound >= CLOCK_POS_INFINITY
        && VAR[d->var_index].U.CRD.CLOCK1 != TIME 
        ) 
      return(rec_string_diagram(d->u.crd.arc[ci].child, pos)); 
    if (d->u.crd.arc[ci].child == NORM_TRUE)
      return(rec_string_ineq(d, d->u.crd.arc[ci].upper_bound, pos));
    else {
      sprintf(&(sbuf[pos]), "("); pos++; 
      pos = rec_string_ineq(d, d->u.crd.arc[ci].upper_bound, pos);
      sprintf(&(sbuf[pos]), "&&"); pos = pos + 2; 
      pos = rec_string_diagram(d->u.crd.arc[ci].child, pos);
      sprintf(&(sbuf[pos]), ")"); pos++; 
      return(pos); 
    }
    break;
  case TYPE_HRD:
    if (   d->u.hrd.arc[ci].ub_numerator == HYBRID_POS_INFINITY 
        && d->u.hrd.arc[ci].ub_denominator == 1
        )
      return(rec_string_diagram(d->u.hrd.arc[ci].child, pos));
    else if (d->u.hrd.arc[ci].child == NORM_TRUE)
      return(rec_string_hybrid_ineq(d, 
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator, 
        pos 
      ));
    else {
      sprintf(&(sbuf[pos]), "("); pos++; 
      pos = rec_string_hybrid_ineq(d, 
        d->u.hrd.arc[ci].ub_numerator, d->u.hrd.arc[ci].ub_denominator, 
        pos
      );
      sprintf(&(sbuf[pos]), "&&"); pos = pos + 2; 
      pos = rec_string_diagram(d->u.hrd.arc[ci].child, pos);
      sprintf(&(sbuf[pos]), ")"); pos++; 
      return(pos); 
    }
    break;
  case TYPE_LAZY_EXP: 
    sprintf(&(sbuf[pos]), "(((~("); 
    pos = pos + 5; 
    pos = rec_string_parse_subformula(d->u.lazy.exp, pos, NULL); 
    sprintf(&(sbuf[pos]), "))&&("); 
    pos = pos + 5; 
    pos = rec_string_diagram(d->u.lazy.false_child, pos); 
    sprintf(&(sbuf[pos]), "))||(("); 
    pos = pos + 6; 
    
    pos = rec_string_parse_subformula(d->u.lazy.exp, pos, NULL); 
    sprintf(&(sbuf[pos]), ")&&("); 
    pos = pos + 4; 
    pos = rec_string_diagram(d->u.lazy.true_child, pos); 
    sprintf(&(sbuf[pos]), ")))"); 
    pos = pos + 3; 
    break; 
  default:
    if (d->u.ddd.arc[ci].child == NORM_TRUE)
      return(string_atom(d, d->u.ddd.arc[ci].lower_bound, 
        d->u.ddd.arc[ci].upper_bound, pos
      ) );
    else {
      sprintf(&(sbuf[pos]), "("); pos++; 
      pos = string_atom(d, 
        d->u.ddd.arc[ci].lower_bound, d->u.ddd.arc[ci].upper_bound, 
        pos
      );
      sprintf(&(sbuf[pos]), "&&"); pos = pos + 2; 
      pos = rec_string_diagram(d->u.ddd.arc[ci].child, pos);
      sprintf(&(sbuf[pos]), ")"); pos++; 
      return(pos); 
    }
  }
}
/* rec_string_conj() */



#if RED_DEBUG_REDSTRING_MODE
int	flag_debug_string_diagram = 0; 
#endif 

int	count_string_fatom = 0; 

int	rec_string_diagram(
  struct red_type	*d, 
  int			pos
) {
  struct index_link_type	*pil, *pi_list, *xil, *xi_list;
  struct red_type		*result;
  int				ci;

  #if RED_DEBUG_REDSTRING_MODE
  if (flag_debug_string_diagram) { 
    fprintf(RED_OUT, "\n********************\nIn rec_string_diagram(d=%x, pos=%1d) for\n", 
      d, pos
    ); 
    red_print_graph(d); 
    fflush(RED_OUT); 
    fprintf(RED_OUT, "\n    for XTION[xi=17].red_trigger[pi=1]:\n"); 
    red_print_graph(XTION[17].red_trigger[1]); 
  } 
  #endif 
  
  if (VAR[d->var_index].TYPE == TYPE_FALSE) {
    sprintf(&(sbuf[pos]), "FALSE");
    pos = pos + 5; 
  }
  else if (VAR[d->var_index].TYPE == TYPE_TRUE) {
    sprintf(&(sbuf[pos]), "TRUE"); 
    pos = pos + 4; 
  } 
  else if (VAR[d->var_index].TYPE == TYPE_BDD) { 
    if (d->u.bdd.zero_child == d->u.bdd.one_child) { 
      fprintf(RED_OUT, "Error: Something wrong, both children of a bdd node are the same.\n"); 
      exit(0); 
    } 
    else if (d->u.bdd.zero_child == NORM_FALSE) { 
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION) {
        sprintf(&(sbuf[pos]), "%s", VAR[d->var_index].NAME); 
	pos = pos + strlen(VAR[d->var_index].NAME); 
      } 
      else { 
        sprintf(&(sbuf[pos]), "(%s&&", VAR[d->var_index].NAME); 
	pos = pos + 3 + strlen(VAR[d->var_index].NAME); 
        pos = rec_string_diagram(d->u.bdd.one_child, pos); 
        sprintf(&(sbuf[pos]), ")"); 
        pos++; 
      } 
    }
    else if (d->u.bdd.one_child == NORM_FALSE) { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION) {
        sprintf(&(sbuf[pos]), "(not %s)", VAR[d->var_index].NAME); 
	pos = pos + 6 + strlen(VAR[d->var_index].NAME); 
      } 
      else { 
        sprintf(&(sbuf[pos]), "((not %s)&&", VAR[d->var_index].NAME); 
	pos = pos + 9 + strlen(VAR[d->var_index].NAME); 
        pos = rec_string_diagram(d->u.bdd.zero_child, pos); 
        sprintf(&(sbuf[pos]), ")"); 
        pos++; 
      } 
    } 
    else { 
      if (d->u.bdd.zero_child == NORM_NO_RESTRICTION) { 
        sprintf(&(sbuf[pos]), "((not %s)", VAR[d->var_index].NAME); 
	pos = pos + 7 + strlen(VAR[d->var_index].NAME); 
      } 
      else { 
        sprintf(&(sbuf[pos]), "(((not %s)&&", VAR[d->var_index].NAME); 
	pos = pos + 10 + strlen(VAR[d->var_index].NAME); 
        pos = rec_string_diagram(d->u.bdd.zero_child, pos); 
        sprintf(&(sbuf[pos]), ")"); 
	pos++; 
      } 
      sprintf(&(sbuf[pos]), "||"); 
      pos = pos + 2; 
      if (d->u.bdd.one_child == NORM_NO_RESTRICTION) { 
        sprintf(&(sbuf[pos]), "%s)", VAR[d->var_index].NAME); 
	pos = pos + 1 + strlen(VAR[d->var_index].NAME); 
      } 
      else { 
        sprintf(&(sbuf[pos]), "(%s&&", VAR[d->var_index].NAME); 
	pos = pos + 3 + strlen(VAR[d->var_index].NAME); 
        pos = rec_string_diagram(d->u.bdd.one_child, pos); 
        sprintf(&(sbuf[pos]), "))"); 
	pos = pos + 2; 
      } 
    } 
  }
  else switch (VAR[d->var_index].TYPE) {
  case TYPE_CRD:
    if (d->u.crd.child_count == 1) {
      pos = rec_string_ineq(d, d->u.crd.arc[0].upper_bound, pos);
      if (d->u.crd.arc[0].child != NORM_NO_RESTRICTION) {
	if (   d->u.crd.arc[0].upper_bound != CLOCK_POS_INFINITY
	    || VAR[d->var_index].U.CRD.CLOCK1 == TIME
	    ) {
	  sprintf(&(sbuf[pos]), "&&");
	  pos = pos + 2; 
	} 
	pos = rec_string_diagram(d->u.crd.arc[0].child, pos);
      }
    }
    else {
      sprintf(&(sbuf[pos]), "(");
      pos++;  
      pos = rec_string_conj(d, 0, pos);
      for (ci = 1; ci < d->u.crd.child_count; ci++) {
        sprintf(&(sbuf[pos]), "||");
        pos = pos + 2; 
        pos = rec_string_conj(d, ci, pos);
      }
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
    break;
  case TYPE_HRD:
    if (d->u.hrd.child_count == 1) {
      pos = rec_string_hybrid_ineq(d, d->u.hrd.arc[0].ub_numerator, 
        d->u.hrd.arc[0].ub_denominator, pos
      );
      if (d->u.hrd.arc[0].child != NORM_NO_RESTRICTION) {
        sprintf(&(sbuf[pos]), "&&");
	pos = pos + 2; 
	pos = rec_string_diagram(d->u.hrd.arc[0].child, pos);
      }
    }
    else {
      sprintf(&(sbuf[pos]), "(");
      pos++;  
      pos = rec_string_conj(d, 0, pos);
      for (ci = 1; ci < d->u.hrd.child_count; ci++) {
        sprintf(&(sbuf[pos]), "||");
        pos = pos + 2; 
        pos = rec_string_conj(d, ci, pos);
      }
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
    break;
  case TYPE_LAZY_EXP: 
    sprintf(&(sbuf[pos]), "(((~("); 
    pos = pos + 5; 
    pos = rec_string_parse_subformula(d->u.lazy.exp, pos, NULL); 
    sprintf(&(sbuf[pos]), "))&&("); 
    pos = pos + 5; 
    pos = rec_string_diagram(d->u.lazy.false_child, pos); 
    sprintf(&(sbuf[pos]), "))||(("); 
    pos = pos + 6; 
    
    pos = rec_string_parse_subformula(d->u.lazy.exp, pos, NULL); 
    sprintf(&(sbuf[pos]), ")&&("); 
    pos = pos + 4; 
    pos = rec_string_diagram(d->u.lazy.true_child, pos); 
    sprintf(&(sbuf[pos]), ")))"); 
    pos = pos + 3; 
    break; 

  case TYPE_FLOAT:
    if (d->u.fdd.child_count == 1) {
/*
      fprintf(RED_OUT, "\n%1d, printing fatom %1d:%s in [%f,%f]\n", 
        ++count_string_fatom, d->var_index, VAR[d->var_index].NAME, 
        d->u.fdd.arc[0].lower_bound, d->u.fdd.arc[0].upper_bound
      ); 
*/
      pos = string_fatom(d, 
        d->u.fdd.arc[0].lower_bound, d->u.fdd.arc[0].upper_bound, pos
      );
      if (d->u.fdd.arc[0].child != NORM_NO_RESTRICTION) {
	sprintf(&(sbuf[pos]), "&&");
	pos = pos + 2; 
	pos = rec_string_diagram(d->u.fdd.arc[0].child, pos);
      }
    }
    else {
      sprintf(&(sbuf[pos]), "(");
      pos++;  
      pos = rec_string_conj(d, 0, pos);
      for (ci = 1; ci < d->u.fdd.child_count; ci++) {
        sprintf(&(sbuf[pos]), "||");
        pos = pos + 2; 
        pos = rec_string_conj(d, ci, pos);
      }
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
    break; 

  case TYPE_DOUBLE:
    if (d->u.dfdd.child_count == 1) {
      pos = string_dfatom(d, 
        d->u.dfdd.arc[0].lower_bound, d->u.dfdd.arc[0].upper_bound, pos
      );
      if (d->u.dfdd.arc[0].child != NORM_NO_RESTRICTION) {
	sprintf(&(sbuf[pos]), "&&");
	pos = pos + 2; 
	pos = rec_string_diagram(d->u.dfdd.arc[0].child, pos);
      }
    }
    else {
      sprintf(&(sbuf[pos]), "(");
      pos++;  
      pos = rec_string_conj(d, 0, pos);
      for (ci = 1; ci < d->u.dfdd.child_count; ci++) {
        sprintf(&(sbuf[pos]), "||");
        pos = pos + 2; 
        pos = rec_string_conj(d, ci, pos);
      }
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
    break; 

  default:
    if (d->u.ddd.child_count == 1) {
      pos = string_atom(d, 
        d->u.ddd.arc[0].lower_bound, d->u.ddd.arc[0].upper_bound, pos
      );
      if (d->u.ddd.arc[0].child != NORM_NO_RESTRICTION) {
	sprintf(&(sbuf[pos]), "&&");
	pos = pos + 2; 
	pos = rec_string_diagram(d->u.ddd.arc[0].child, pos);
      }
    }
    else {
      sprintf(&(sbuf[pos]), "(");
      pos++;  
      pos = rec_string_conj(d, 0, pos);
      for (ci = 1; ci < d->u.ddd.child_count; ci++) {
        sprintf(&(sbuf[pos]), "||");
        pos = pos + 2; 
        pos = rec_string_conj(d, ci, pos);
      }
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
  } 
  return(pos); 
}
/* rec_string_diagram() */



char	*string_diagram(
  struct red_type	*d 
) { 
  int	len; 
  char	*tmp_buf_diagram; 

  len = rec_string_diagram(d, 0); 
  if (len >= size_sbuf) { 
    fprintf(RED_OUT, 
      "Uh! the string buffer has overflown, len:%1d>size_sbuf:%1d.\n", 
      len, size_sbuf 
    ); 
    fflush(RED_OUT); 
    bk(0); 	
  } 
  sbuf[len] = '\0'; 
  tmp_buf_diagram = malloc(len+1); 
  sprintf(tmp_buf_diagram, "%s", sbuf); 
  
  return(tmp_buf_diagram); 
}
  /* string_diagram() */  





/***********************************************************************
*  The following procedure are for converting parse subformulas to 
*  strings. 
*/
time_interval_length(lb, ub)
	int	lb, ub;
{
  int	len; 
  
  if (lb == 0 && ub == CLOCK_POS_INFINITY) 
    len = 0; 
  else {
    // not an NEQ
    if (lb <= ub) { 
      len = 2 + intlen(lb/2);
      if (ub == CLOCK_POS_INFINITY) 
        len = len + 3; 
      else if (ub % 2) 
        len = len + 1 + intlen((ub+1)/2);
      else 
        len = len + 1 + intlen(ub/2);
    }
    // an NEQ
    else if (ub == -1) { 
      len = 5 + intlen(lb/2); 
    } 
    else if (lb-1==ub+1 && lb%2) { 
      len = 4 + intlen(lb/2);
    }
    else { 
      ub = ub+1;
      lb = lb-1; 
      len = 3 + intlen(ub/2);
      if (lb % 2)
        len = len + 1 + intlen((lb+1)/2); 
      else
        len = len + 1 + intlen(lb/2); 

    }
  }
  return (len); 
}
/* time_interval_length() */




int	sop_fairness_length(qstring, mstring, psub) 
	char			*qstring, *mstring;
	struct ps_exp_type	*psub; 
{
  struct ps_fairness_link_type	*fl;
  int				len; 
  
  len = strlen(qstring) + 1; 
  if (psub->u.mexp.strong_fairness_count) {
    len = len + 19;  
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      len = len + length_parse_subformula(fl->fairness) + 1; 
    } 
  } 
  if (psub->u.mexp.weak_fairness_count) { 
    len = len + 17; 
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      len = len + length_parse_subformula(fl->fairness) + 1;
    }
  } 

  return (len + 1 + strlen(mstring)); 
}
/* sop_fairness_length() */ 








int	eop_fairness_length(qstring, estring, psub) 
	char			*qstring, *estring;
	struct ps_exp_type	*psub; 
{
  struct ps_fairness_link_type	*fl;
  int				len; 
  
  len = strlen(qstring) + 1; 
  return (len + 1 + strlen(estring)); 
}
/* eop_fairness_length() */ 










int	length_parse_subformula(psub)
     struct ps_exp_type	*psub;
{
  int				i, jj, len;
  struct ps_bunit_type		*pbu;
  struct ps_fairness_link_type	*fl;

  switch(psub->type) {
  case TYPE_FALSE :
/*
    fprintf(RED_OUT, "TYPE_FALSE");
*/
    return (5);
  case TYPE_TRUE :
/*
    fprintf(RED_OUT, "TYPE_TRUE");
*/
    return (4); 

// QQ1 

  case TYPE_REFERENCE: 
    if (psub->u.exp->type == ARITH_ADD) { 
      return(2 + length_parse_subformula(psub->u.exp->u.arith.lhs_exp) 
      + length_parse_subformula(psub->u.exp->u.arith.rhs_exp)
      ); 
    }
  case TYPE_DEREFERENCE: 
    return(3+length_parse_subformula(psub->u.exp));

  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_SYNCHRONIZER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
    len = strlen(psub->u.atom.var_name); 
    if (psub->u.atom.var && (psub->u.atom.var->status & FLAG_VAR_STACK)) { 
      if (psub->u.atom.exp_base_proc_index != NULL) { 
      	if (psub->u.atom.exp_base_proc_index == PS_EXP__SP) 
      	  break; 
      	else if (   psub->u.atom.exp_base_proc_index == PS_EXP__SP_PLUS
      	         || psub->u.atom.exp_base_proc_index == PS_EXP__SP_MINUS
      	         ) { 
      	  len = len + 5; 
      	  break; 
        } 
        else switch (psub->u.atom.exp_base_proc_index->type) {
        case TYPE_NULL:
        case 0: 
          len = len + 5; 
          break;
        default:
          len = 4+length_parse_subformula(psub->u.atom.exp_base_proc_index); 
          break;
        }
      }
    }
    else if (   psub->u.atom.var
             && (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)
             && psub->u.atom.exp_base_proc_index != NULL 
             && psub->u.atom.exp_base_proc_index != PS_EXP_LOCAL_IDENTIFIER
             ) { 
      switch (psub->u.atom.exp_base_proc_index->type) {
      case TYPE_NULL:
      case 0: 
        len = len + 4; 
        break;
      case TYPE_LOCAL_IDENTIFIER: 
        if (PI_STRING == INDEX_LOCAL_IDENTIFIER) { 
          break; 
        } 
      default:
        len = 3+length_parse_subformula(psub->u.atom.exp_base_proc_index); 
        break;
      }
    }
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) {
      len = len + 2 + length_parse_subformula(psub->u.atom.indirect_exp[i]); 
    }
*/
    return(len); 
    break;
  case TYPE_QFD:
    return(strlen(psub->u.atom.var_name)); 
  case TYPE_QSYNC_HOLDER: 
    return (strlen(psub->u.qsholder.qsync_var_name)); 
  case TYPE_NULL:
/*
    fprintf(RED_OUT, "NULL");
*/
    return(4); 
    break;
  case TYPE_LOCAL_IDENTIFIER:
/* 
    fprintf(RED_OUT, "P");
*/
    if (PI_STRING > 0 && PI_STRING <= PROCESS_COUNT) 
      return(PI_LENGTH); 
    else 
      return(1); 
    break;
  case TYPE_PEER_IDENTIFIER:
/*
    fprintf(RED_OUT, "~P");
*/
    if (PI_STRING > 0 && PI_STRING <= PROCESS_COUNT) {
      fprintf(RED_OUT, "Sorry that we did not implement the peer process \n"); 
      fprintf(RED_OUT, "identifier constraint length calculation.\n"); 
      exit(0); 
    }
    else 
      return(2); 
    break;
  case TYPE_TRASH:
/*
    fprintf(RED_OUT, "?");
*/
    return(1); 
    break;
  case TYPE_CONSTANT:
/*
    fprintf(RED_OUT, "%1d", psub->u.value);
*/
    return(intlen(psub->u.value)); 
    break;

  case TYPE_FLOAT_CONSTANT:
/*
    fprintf(RED_OUT, "%1d", psub->u.value);
*/
    return(fltlen(psub->u.float_value)); 
    break;
  case TYPE_MACRO_CONSTANT: 
    return(strlen(psub->u.inline_call.inline_exp_name));
  case TYPE_INTERVAL:
    if (psub->u.interval.status & INTERVAL_LEFT_UNBOUNDED)
/*
      fprintf(RED_OUT, "(-oo,");
*/
      len = 5; 
    else {
/*
      if (psub->u.interval.status & INTERVAL_LEFT_OPEN)
        fprintf(RED_OUT, "(");
      else
        fprintf(RED_OUT, "[");
      print_parse_subformula(psub->u.interval.lbound_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
      fprintf(RED_OUT, ",");
*/
      len = 3 + length_parse_subformula(psub->u.interval.lbound_exp); 
    }
    if (psub->u.interval.status & INTERVAL_RIGHT_UNBOUNDED)
/*
      fprintf(RED_OUT, "oo)");
*/
      len = len + 3; 
    else {
/* 
      print_parse_subformula(psub->u.interval.rbound_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
      if (psub->u.interval.status & INTERVAL_RIGHT_OPEN)
        fprintf(RED_OUT, ")");
      else
        fprintf(RED_OUT, "]");
*/
      len = len + 1 + length_parse_subformula(psub->u.interval.rbound_exp); 
    }
    break;
  case TYPE_MODE_INDEX: 
  	return(strlen(psub->u.atom.var_name)); 
  	break; 
  case BIT_NOT: 
    return (3+length_parse_subformula(psub->u.exp)); 
    break; 
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  
/*
    fprintf(RED_OUT, "(");
    print_parse_subformula(psub->u.arith.lhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    print_op(psub->type);
    print_parse_subformula(psub->u.arith.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ")");
*/
    return (2+op_length(psub->type)
	     +length_parse_subformula(psub->u.arith.lhs_exp)
	     +length_parse_subformula(psub->u.arith.rhs_exp)
	    ); 
    break; 

// QQ2 

  case ARITH_EQ :
    if (   psub->u.arith.lhs_exp->type == TYPE_DISCRETE 
        && psub->u.arith.lhs_exp->u.atom.var == var_mode
//        && psub->u.arith.lhs_exp->u.atom.indirect_count == 0 
        ) { 
      if (psub->u.arith.rhs_exp->type == TYPE_MODE_INDEX) { 
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (PI_STRING == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            return(4+strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name));
          }
          else {
            return(3
            + strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name)
            + intlen(PI_STRING)  
            ); 
          }
        else { 
          return(3
          + strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name) 
          + length_parse_subformula(
              psub->u.arith.lhs_exp->u.atom.exp_base_proc_index  
          ) ); 
        }
        break; 
      }
      else if (psub->u.arith.rhs_exp->type == TYPE_CONSTANT) { 
      	char	*mname; 
      	
      	mname = flexible_parse_mode_name(psub->u.arith.rhs_exp->u.value); 
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER  
            ) 
          if (PI_STRING == FLAG_GENERAL_PROCESS_IDENTIFIER) {
            return(4+strlen(mname)); 
          }
          else {
            return(3+strlen(mname)+intlen(PI_STRING)); 
          }
        else { 
          return(3
          + strlen(mname) 
          + length_parse_subformula(
              psub->u.arith.lhs_exp->u.atom.exp_base_proc_index 
          ) ); 
        }
        break; 
      }
    }

  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
/*
    fprintf(RED_OUT, "%x:", psub->status);
    print_parse_subformula(psub->u.arith.lhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    print_op(psub->type);
    print_parse_subformula(psub->u.arith.rhs_exp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    return ( op_length(psub->type)
	    +length_parse_subformula(psub->u.arith.lhs_exp)
	    +length_parse_subformula(psub->u.arith.rhs_exp)
	    );

// QQ3 
  case EQ :
    if (   psub->u.ineq.term_count == 1
        && psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT  
        && psub->u.ineq.term[0].coeff->u.value == 1  
        && psub->u.ineq.term[0].operand->type == TYPE_DISCRETE 
        && psub->u.ineq.term[0].operand->u.atom.var == var_mode
//        && psub->u.ineq.term[0].operand->u.atom.indirect_count == 0 
        && psub->u.ineq.term[0].operand->u.atom.exp_base_proc_index->type 
           == TYPE_LOCAL_IDENTIFIER  
        && psub->u.ineq.offset->type == TYPE_CONSTANT
        && psub->u.ineq.offset->u.value >= 0
        && psub->u.ineq.offset->u.value < MODE_COUNT
        ) { 
      if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
        return( 
            strlen(MODE[psub->u.ineq.offset->u.value].name) 
          + intlen(PI_STRING) 
          + 2
        ); 
      } 
      else { 
        return(strlen(MODE[psub->u.ineq.offset->u.value].name) + 3); 
      }
      break; 
    }

  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ :
/*
    fprintf(RED_OUT, "%x:", psub->status);
*/
    len = 0; 
    for (i = 0; i < psub->u.ineq.term_count; i++)  {
      if (psub->u.ineq.term[i].coeff->type == TYPE_CONSTANT) {
        if (psub->u.ineq.term[i].coeff->u.value < 0)
	  if (psub->u.ineq.term[i].coeff->u.value == -1)
/* 	  
	    fprintf(RED_OUT, "-");
*/
	    len = len+1; 
	  else
/*
	    fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
*/
	    len = len + 1 + intlen(psub->u.ineq.term[i].coeff->u.value); 
	else
	  if (psub->u.ineq.term[i].coeff->u.value == 1) {
	    if (i)
/* 
	      fprintf(RED_OUT, "+");
*/
	      len = len + 1; 
	  }
	  else {
	    if (i)
/*
	      fprintf(RED_OUT, "%1d ", psub->u.ineq.term[i].coeff->u.value);
*/
	      len = len + 1 + intlen(psub->u.ineq.term[i].coeff->u.value); 
	    else
/*
	      fprintf(RED_OUT, "+%1d ", psub->u.ineq.term[i].coeff->u.value);
*/
	      len = len + 2 + intlen(psub->u.ineq.term[i].coeff->u.value); 
	  }
      }
      else {
        if (i) {
/*
          fprintf(RED_OUT, "+(");
*/
	  len = len + 2; 
	}
	else
/*
	  fprintf(RED_OUT, "(");
*/
	  len = len + 1; 
/*
	print_parse_subformula(psub->u.ineq.term[i].coeff, FLAG_GENERAL_PROCESS_IDENTIFIER);
	fprintf(RED_OUT, ")");
*/
	len = len + 1 + length_parse_subformula(psub->u.ineq.term[i].coeff); 
      }
/*
      print_parse_subformula(psub->u.ineq.term[i].operand, FLAG_GENERAL_PROCESS_IDENTIFIER);
*/
      len = len + length_parse_subformula(psub->u.ineq.term[i].operand);
    }
/*
    print_op(psub->type);
    print_parse_subformula(psub->u.ineq.offset, FLAG_GENERAL_PROCESS_IDENTIFIER);
*/
    return (len + op_length(psub->type) + length_parse_subformula(psub->u.ineq.offset));
  case ARITH_CONDITIONAL: 
    len = 0; 
    len = len + 7 
    + length_parse_subformula(psub->u.arith_cond.cond)
    + length_parse_subformula(psub->u.arith_cond.if_exp)   
    + length_parse_subformula(psub->u.arith_cond.else_exp);  
    return(len); 

  case AND :
    pbu = psub->u.bexp.blist;
/* 
    fprintf(RED_OUT, "("); 
    print_parse_subformula(pbu->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ")");
*/
    len = 2 + length_parse_subformula(pbu->subexp);
    for (jj = psub->u.bexp.len-1, pbu = pbu->bnext;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
/*
      fprintf(RED_OUT, "&&(");
      print_parse_subformula(pbu->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER);
      fprintf(RED_OUT, ")");
*/
      len = len + 4 + length_parse_subformula(pbu->subexp);
    }
    return (len);
  case OR :
    pbu = psub->u.bexp.blist;
/*
    fprintf(RED_OUT, "(");
    print_parse_subformula(pbu->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER);
    fprintf(RED_OUT, ")");
*/
    len = 2 + length_parse_subformula(pbu->subexp);
    for (jj = psub->u.bexp.len-1, pbu = pbu->bnext;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
/*
      fprintf(RED_OUT, "||("); 
      print_parse_subformula(pbu->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
      fprintf(RED_OUT, ")"); 
*/
      len = len + 4 + length_parse_subformula(pbu->subexp);
    }
    return (len); 
  case NOT :
/*
    fprintf(RED_OUT, "~(");
    print_parse_subformula(psub->u.bexp.blist->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, ")"); 
*/
    return (3+length_parse_subformula(psub->u.bexp.blist->subexp));
  case IMPLY :
/*
    fprintf(RED_OUT, "("); 
    print_parse_subformula(psub->u.bexp.blist->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, ")->(");
    print_parse_subformula(psub->u.bexp.blist->bnext->subexp, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    fprintf(RED_OUT, ")");
*/
    return (6+length_parse_subformula(psub->u.bexp.blist->subexp)
	    + length_parse_subformula(psub->u.bexp.blist->bnext->subexp)
	    );
  case FORALL: 
/*
    fprintf(RED_OUT, "FORALL %s ", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    return(8+strlen(psub->u.qexp.quantifier_name)+length_parse_subformula(psub->u.qexp.child)); 
  case EXISTS: 
/*
    fprintf(RED_OUT, "EXISTS %s ", psub->u.qexp.quantifier_name); 
    print_parse_subformula(psub->u.qexp.child, FLAG_GENERAL_PROCESS_IDENTIFIER);
*/
    return(8+strlen(psub->u.qexp.quantifier_name)+length_parse_subformula(psub->u.qexp.child)); 
  case RESET:
/*
    fprintf(RED_OUT, "RESET %s ", psub->u.reset.clock_name); 
    print_parse_subformula(psub->u.reset.child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    return (7+strlen(psub->u.reset.clock_name)
	    +length_parse_subformula(psub->u.reset.child)
	    ); 
  case FORALL_ALWAYS: 
/*
    print_sop_fairness("FORALL", "ALWAYS", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    return (  sop_fairness_length("FORALL", "ALWAYS", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1
	    + length_parse_subformula(psub->u.mexp.path_child) 
	    ); 
  case FORALL_EVENTUALLY:
/*
    print_sop_fairness("FORALL", "EVENTUALLY", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " ");
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
    return; 
*/
    return (  sop_fairness_length("FORALL", "EVENTUALLY", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1
	    + length_parse_subformula(psub->u.mexp.path_child) 
	    ); 
  case EXISTS_ALWAYS: 
/*
    print_sop_fairness("EXISTS", "ALWAYS", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
    return; 
*/
    return (  sop_fairness_length("EXISTS", "ALWAYS", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1
	    + length_parse_subformula(psub->u.mexp.path_child) 
	    ); 
  case EXISTS_EVENTUALLY:
/*
    print_sop_fairness("EXISTS", "EVENTUALLY", psub);
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    return; 
*/
    return (  sop_fairness_length("EXISTS", "EVENTUALLY", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1
	    + length_parse_subformula(psub->u.mexp.path_child) 
	    ); 
  case EXISTS_UNTIL: 
    len = 7; 
/*
    fprintf(RED_OUT, "EXISTS "); 
*/
    if (psub->u.mexp.strong_fairness_count) {
/*
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
*/
      len = len + 18;       
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
/*
        print_parse_subformula(fl->child, FLAG_GENERAL_PROCESS_IDENTIFIER);
        fprintf(RED_OUT, ";"); 
*/
	len = len + length_parse_subformula(fl->fairness) + 1; 
      }
/* 
      fprintf(RED_OUT, "}"); 
*/
      len = len + 1; 
    } 
    if (psub->u.mexp.weak_fairness_count) {
/*
      fprintf(RED_OUT, "WEAK FAIRNESS: {"); 
*/
      len = len + 16; 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
/*
        print_parse_subformula(fl->child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, ";");
*/
	len = len + length_parse_subformula(fl->fairness) + 1; 
      }
/*
      fprintf(RED_OUT, "}"); 
*/
      len = len + 1; 
    }
/*
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    len = len + length_parse_subformula(psub->u.mexp.path_child); 
/* 
    fprintf(RED_OUT, "UNTIL"); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.dest_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
*/
    return (  len + 6 
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub) 
	    + length_parse_subformula(psub->u.mexp.dest_child)
	    );
  case FORALL_UNTIL: 
/*
    fprintf(RED_OUT, "FORALL "); 
*/
    len = 7; 
    if (psub->u.mexp.strong_fairness_count) {
/*
      fprintf(RED_OUT, "STRONG FAIRNESS: {"); 
*/
      len = len + 18;       
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
/*
        print_parse_subformula(fl->child, FLAG_GENERAL_PROCESS_IDENTIFIER);
        fprintf(RED_OUT, ";"); 
*/
	len = len + length_parse_subformula(fl->fairness) + 1; 
      }
/* 
      fprintf(RED_OUT, "}"); 
*/
      len = len + 1; 
    } 
    if (psub->u.mexp.weak_fairness_count) {
/*
      fprintf(RED_OUT, "WEAK FAIRNESS: {"); 
*/
      len = len + 16; 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
/*
        print_parse_subformula(fl->child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
        fprintf(RED_OUT, ";");
*/
	len = len + length_parse_subformula(fl->fairness) + 1; 
      }
/*
      fprintf(RED_OUT, "}"); 
*/
      len = len + 1; 
    }
/*
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    len = len + length_parse_subformula(psub->u.mexp.path_child); 
/* 
    fprintf(RED_OUT, "UNTIL"); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.dest_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
*/
    return (  len + 6 
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub) 
	    + length_parse_subformula(psub->u.mexp.dest_child)
	    );
  case EXISTS_CHANGE:
/*
    print_sop_fairness("EXISTS", "CHANGE", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub);
    fprintf(RED_OUT, " ");
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
*/
    return (  sop_fairness_length("EXISTS", "CHANGE", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1 
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 
  case FORALL_CHANGE: 
/*
    print_sop_fairness("FORALL", "CHANGE", psub); 
    print_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub); 
    fprintf(RED_OUT, " "); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
    return; 
*/
    return (  sop_fairness_length("FORALL", "CHANGE", psub)
	    + time_interval_length(psub->u.mexp.time_lb, psub->u.mexp.time_ub)
	    + 1 
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 
  case EXISTS_OFTEN: 
/*
    print_sop_fairness("EXISTS", "OFTEN ", psub); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
    return;
*/
    return (  sop_fairness_length("EXISTS", "OFTEN", psub)
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 
  case EXISTS_ALMOST: 
/*
    print_sop_fairness("EXISTS", "ALMOST ", psub); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    return; 
*/
    return (  sop_fairness_length("EXISTS", "ALMOST", psub)
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 
  case FORALL_OFTEN:
/*
    print_sop_fairness("FORALL", "OFTEN ", psub); 
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER);
    return; 
*/
    return (  sop_fairness_length("FORALL", "OFTEN", psub)
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 
  case FORALL_ALMOST: 
/*
    print_sop_fairness("FORALL", "ALMOST ", psub);
    print_parse_subformula(psub->u.mexp.path_child, FLAG_GENERAL_PROCESS_IDENTIFIER); 
    return; 
*/
    return (  sop_fairness_length("FORALL", "ALMOST", psub)
	    + length_parse_subformula(psub->u.mexp.path_child)
	    ); 

  case RED: 
    return (4); 
/*
    red_print_line(psub->u.rpred.red);
*/
    break; 
  }
}
  /* length_parse_subformula() */ 





int	string_sop_fairness(qstring, mstring, psub, pos) 
	char			*qstring, *mstring;
	struct ps_exp_type	*psub; 
	int			pos; 
{
  struct ps_fairness_link_type	*fl;
  
  sprintf(&(sbuf[pos]), "%s ", qstring); 
  pos = pos + 1 + strlen(qstring); 
  
  if (psub->u.mexp.strong_fairness_count) {
    sprintf(&(sbuf[pos]), "STRONG FAIRNESS: {"); 
    pos = pos + 18; 
    for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      rec_string_parse_subformula(fl->fairness, pos, psub); 
      sprintf(&(sbuf[pos]), ";"); 
      pos = pos + 1; 
    }
    sprintf(&(sbuf[pos]), "}"); 
    pos = pos + 1; 
  } 
  if (psub->u.mexp.weak_fairness_count) { 
    sprintf(&(sbuf[pos]), "WEAK FAIRNESS: {"); 
    pos = pos + 16; 
    for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
      rec_string_parse_subformula(fl->fairness, pos, psub);
      sprintf(&(sbuf[pos]), ";");
      pos = pos + 1; 
    }
    sprintf(&(sbuf[pos]), "}"); 
    pos = pos + 1; 
  } 

  sprintf(&(sbuf[pos]), " %s", mstring);
  pos = pos + 1 + strlen(mstring); 
  return(pos);  
}
/* string_sop_fairness() */ 





string_eop_fairness(qstring, estring, psub, pos) 
	char			*qstring, *estring;
	struct ps_exp_type	*psub; 
	int			pos; 
{
  struct ps_fairness_link_type	*fl;
  
  sprintf(&(sbuf[pos]), "%s ", qstring); 
  pos = pos + 1 + strlen(qstring); 
  
  sprintf(&(sbuf[pos]), " %s", estring);
  pos = pos + 1 + strlen(estring); 
  return(pos);  
}
/* string_eop_fairness() */ 





string_time_interval(lb, ub, pos)
	int	lb, ub, pos;
{
  if (lb != 0 || ub != CLOCK_POS_INFINITY) {
    if (lb <= ub) { 
    // Not an NEQ 
      if (lb % 2) 
      	sprintf(&(sbuf[pos]), "(%1d,", lb/2);
      else
      	sprintf(&(sbuf[pos]), "[%1d,", lb/2);
      pos = pos + 2 + intlen(lb/2); 
      if (ub == CLOCK_POS_INFINITY) {
        sprintf(&(sbuf[pos]), "oo)"); 
        pos = pos + 3; 
      }  
      else if (ub % 2) {
        sprintf(&(sbuf[pos]), "%1d)", (ub+1)/2);
        pos = pos + 1 + intlen((ub+1)/2); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d]", ub/2);
        pos = pos + 1 + intlen(ub/2); 
      }
    }
    // The following are NEQs. 
    else if (ub == -1) { 
      if (lb % 2)
      	sprintf(&(sbuf[pos]), "(%1d,oo)", lb/2); 
      else
      	sprintf(&(sbuf[pos]), "[%1d,oo)", lb/2);
      pos = pos + 5 + intlen(lb/2); 
    } 
    else if (lb-1==ub+1 && lb%2) { 
      sprintf(&(sbuf[pos]), "{!=%1d}", lb/2);
      pos = pos + 4 + intlen(lb/2); 
    }
    else { 
      ub = ub+1;
      lb = lb-1; 
      if (ub % 2)
      	sprintf(&(sbuf[pos]), "~(%1d,", ub/2);
      else 
      	sprintf(&(sbuf[pos]), "~[%1d,", ub/2);
      pos = pos + 3 + intlen(ub/2); 
      if (lb % 2) {
        sprintf(&(sbuf[pos]), "%1d)", (lb+1)/2); 
        pos = pos + 1 + intlen((lb+1)/2);   
      }
      else {
        sprintf(&(sbuf[pos]), "%1d]", lb/2); 
        pos = pos + 1 + intlen(lb/2); 
      }
    }
  }
 
  return (pos); 
}
  /* string_time_interval() */




int	string_op(op, pos) 
  int	op, pos; 
{
  switch (op) {
  case LESS: 
  case ARITH_LESS: 
    sprintf(&(sbuf[pos]), "<"); 
    pos = pos + 1; 
    break;
  case LEQ: 
  case ARITH_LEQ: 
    sprintf(&(sbuf[pos]), "<="); 
    pos = pos + 2; 
    break; 
  case EQ: 
  case ARITH_EQ: 
    sprintf(&(sbuf[pos]), "=="); 
    pos = pos + 2; 
    break; 
  case NEQ: 
  case ARITH_NEQ: 
    sprintf(&(sbuf[pos]), "!="); 
    pos = pos + 2; 
    break;
  case GEQ:
  case ARITH_GEQ: 
    sprintf(&(sbuf[pos]), ">="); 
    pos = pos + 2; 
    break;
  case GREATER:
  case ARITH_GREATER: 
    sprintf(&(sbuf[pos]), ">"); 
    pos = pos + 1; 
    break;
  case ARITH_ADD: 
    sprintf(&(sbuf[pos]), "+"); 
    pos = pos + 1; 
    break; 
  case ARITH_MINUS: 
    sprintf(&(sbuf[pos]), "-"); 
    pos = pos + 1; 
    break;
  case ARITH_MULTIPLY: 
    sprintf(&(sbuf[pos]), "*"); 
    pos = pos + 1; 
    break; 
  case ARITH_DIVIDE: 
    sprintf(&(sbuf[pos]), "/"); 
    pos = pos + 1; 
    break;
  case ARITH_MODULO: 
    sprintf(&(sbuf[pos]), "%%"); 
    pos = pos + 1; 
    break;
  case BIT_NOT: 
    sprintf(&(sbuf[pos]), "~"); 
    pos = pos + 1; 
    break;
  case BIT_OR: 
    sprintf(&(sbuf[pos]), "|"); 
    pos = pos + 1; 
    break;
  case BIT_AND:  
    sprintf(&(sbuf[pos]), "&"); 
    pos = pos + 1; 
    break;
  case BIT_SHIFT_RIGHT: 
    sprintf(&(sbuf[pos]), ">>"); 
    pos = pos + 2; 
    break;
  case BIT_SHIFT_LEFT: 
    sprintf(&(sbuf[pos]), "<<"); 
    pos = pos + 2; 
    break;
  case TYPE_FALSE: 
    sprintf(&(sbuf[pos]), "TYPE_FALSE"); 
    pos = pos + 5; 
    break; 
  case TYPE_TRUE: 
    sprintf(&(sbuf[pos]), "TYPE_TRUE"); 
    pos = pos + 4; 
    break; 
  case TYPE_CONSTANT: 
    sprintf(&(sbuf[pos]), "CONSTANT"); 
    pos = pos + 8; 
    break; 
  case TYPE_INDIRECT_PI: 
    sprintf(&(sbuf[pos]), "INDIRECT_PI"); 
    pos = pos + 11; 
    break;
  case TYPE_PATH_ENDPOINT: 
    sprintf(&(sbuf[pos]), "PATH ENDPOINT"); 
    pos = pos + 13; 
    break; 
  case TYPE_VALUE:
    sprintf(&(sbuf[pos]), "VALUE");
    pos = pos + 5; 
    break; 
  case TYPE_OP: 
    sprintf(&(sbuf[pos]), "OP");
    pos = pos + 2; 
    break; 
  case TYPE_REFERENCE: 
    sprintf(&(sbuf[pos]), "REF");
    pos = pos + 3; 
    break; 
  case TYPE_DEREFERENCE: 
    sprintf(&(sbuf[pos]), "DEREF");
    pos = pos + 5; 
    break; 
  case TYPE_XTION_INSTANCE: 
    sprintf(&(sbuf[pos]), "XTION_INS"); 
    pos = pos + 9; 
    break; 
  case TYPE_ACTION_INSTANCE: 
    sprintf(&(sbuf[pos]), "ACTION_INS");
    pos = pos + 10; 
    break; 
  case TYPE_CLOCK:
    sprintf(&(sbuf[pos]), "CLOCK");
    pos = pos + 5; 
    break;
  case TYPE_DENSE:
    sprintf(&(sbuf[pos]), "DENSE");
    pos = pos + 5; 
    break;
  case TYPE_POINTER:
    sprintf(&(sbuf[pos]), "POINTER");
    pos = pos + 7; 
    break; 
  case TYPE_SYNCHRONIZER: 
    sprintf(&(sbuf[pos]), "SYNC"); 
    pos = pos + 4; 
    break; 
  case TYPE_DISCRETE: 
    sprintf(&(sbuf[pos]), "DISCRETE");
    pos = pos + 8; 
    break; 
  case TYPE_FLOAT: 
    sprintf(&(sbuf[pos]), "FLOAT");
    pos = pos + 5; 
    break; 
  case TYPE_DOUBLE: 
    sprintf(&(sbuf[pos]), "DOUBLE");
    pos = pos + 6; 
    break; 
  case TYPE_QSYNC_HOLDER: 
    sprintf(&(sbuf[pos]), "QSYNC HOLDER");
    pos = pos + 12; 
    break; 
  case TYPE_CRD:
    sprintf(&(sbuf[pos]), "CLOCK INEQ");
    pos = pos + 10; 
    break;
  case TYPE_CDD:
    sprintf(&(sbuf[pos]), "FILTER INEQ");
    pos = pos + 11; 
    break; 
  case TYPE_HRD:
    sprintf(&(sbuf[pos]), "HYBRID INEQ");
    pos = pos + 11; 
    break;
  case TYPE_HDD:
    sprintf(&(sbuf[pos]), "HYBRID FILTER");
    pos = pos + 13; 
    break;
  default:
    fprintf(RED_OUT, "\nError: wrong inequality operator op = %1d\n", op);
    for (fflush(RED_OUT); GSTATUS[INDEX_DEBUG] & FLAG_DEBUG_INITIAL; );
    exit(0);
  }
  return(pos); 
}
/* string_op() */



char	*string_mode_name(int mi) { 
  struct parse_mode_type	*pm; 
  
  if (MODE) 
    return(MODE[mi].name); 
  else for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
    if (pm->index == mi) 
      return(pm->name); 	
  }
}
  /* string_mode_name() */ 
  
  
  

/*********************************************************************
 *  080831
 *  We changed the print mode references to mode_name[i]. 
 *  We also omitted the process identifiers with 
 *  local variable references when PI_STRING is not within 
 *  1 to #PS.  
 */ 
 
#if RED_DEBUG_REDSTRING_MODE
int count_string_parse_subformula = 0; 
#endif 

int	rec_string_parse_subformula(
  struct ps_exp_type	*psub, 
  int			pos, 
  struct ps_exp_type	*parent  
) {
  int				i, jj, len;
  struct ps_bunit_type		*pbu;
  struct ps_fairness_link_type	*fl;
  struct name_link_type		*nl; 
      
  #if RED_DEBUG_REDSTRING_MODE
  fprintf(RED_OUT, "count string parse subformula %1d:\n", 
    ++count_string_parse_subformula
  ); 
  pcform(psub); 
  fflush(RED_OUT); 
  #endif 
  
  switch(psub->type) {
  case TYPE_FALSE :
    sprintf(&(sbuf[pos]), "false"); 
    return (pos + 5);
  case TYPE_TRUE :
    sprintf(&(sbuf[pos]), "true");
    return (pos + 4);
  case TYPE_MACRO_CONSTANT: 
    sprintf(&(sbuf[pos]), "%s", psub->u.inline_call.inline_exp_name); 
    return(pos + strlen(psub->u.inline_call.inline_exp_name));
  case TYPE_REFERENCE: 
    if (psub->u.exp->type == ARITH_ADD) { 
      sprintf(&(sbuf[pos]), "*("); 
      pos = pos + 2;  
      pos = rec_string_parse_subformula(
        psub->u.exp, pos, psub 
      ); 
      sprintf(&(sbuf[pos]), ")");
      pos++; 
    }
    else { 
      pos = rec_string_parse_subformula(
        psub->u.exp->u.arith.lhs_exp, pos, psub 
      ); 
      sprintf(&(sbuf[pos]), "["); 
      pos++;  
      pos = rec_string_parse_subformula(
        psub->u.exp->u.arith.rhs_exp, pos, psub 
      ); 
      sprintf(&(sbuf[pos]), "]"); 
      pos++;  
    } 
    return(pos); 
    break; 
  case TYPE_DEREFERENCE: 
    sprintf(&(sbuf[pos]), "&("); 
    pos = pos + 2;  
    pos = rec_string_parse_subformula(
      psub->u.exp, pos, psub 
    ); 
    sprintf(&(sbuf[pos]), ")");
    pos++; 
    return(pos); 
    break; 

  case TYPE_DISCRETE:
  case TYPE_FLOAT: 
  case TYPE_DOUBLE: 
  case TYPE_SYNCHRONIZER:
  case TYPE_CLOCK:
  case TYPE_DENSE:
  case TYPE_POINTER:
  case TYPE_BDD: 
    sprintf(&(sbuf[pos]), "%s", psub->u.atom.var_name);
    pos = pos + strlen(psub->u.atom.var_name); 
    if (   (   psub->u.atom.var 
            && (psub->u.atom.var->status & FLAG_LOCAL_VARIABLE)
            )
        && psub->u.atom.exp_base_proc_index != NULL 
        && psub->u.atom.exp_base_proc_index != PS_EXP_LOCAL_IDENTIFIER
        ) { 
      switch (psub->u.atom.exp_base_proc_index->type) {
      case TYPE_NULL:
      case 0: 
        sprintf(&(sbuf[pos]), "@(0)");
        pos = pos + 4;  
        break;
      case TYPE_LOCAL_IDENTIFIER: 
        if (   (!(psub->u.atom.var->status & FLAG_VAR_STACK)) 
            && PI_STRING == INDEX_LOCAL_IDENTIFIER
            ) {
	  break; 
        } 
      default: 
        if (psub->u.atom.var->status & FLAG_VAR_STACK) { 
      	  if (psub->u.atom.exp_base_proc_index == PS_EXP__SP) 
      	    break; 
      	  sprintf(&(sbuf[pos]), "@"); 
      	  pos = pos + 1; 
      	
      	  if (psub->u.atom.exp_base_proc_index == PS_EXP__SP_PLUS) {
      	    sprintf(&(sbuf[pos]), "+(1)"); 
      	    pos = pos + 4; 
      	    break; 
          }
          else if (psub->u.atom.exp_base_proc_index == PS_EXP__SP_MINUS) { 
      	    sprintf(&(sbuf[pos]), "-(1)"); 
      	    pos = pos + 4; 
      	    break; 
          } 
          else { 
      	    sprintf(&(sbuf[pos]), "+("); 
      	    pos = pos + 2; 
          } 
        }
        else {
          sprintf(&(sbuf[pos]), "@("); 
          pos = pos + 2;  
        }
        pos = rec_string_parse_subformula(
          psub->u.atom.exp_base_proc_index, pos, psub 
        ); 
        sprintf(&(sbuf[pos]), ")");
        pos++; 
        break; 
    } }
/*
    for (i = 0; i < psub->u.atom.indirect_count; i++) { 
      sprintf(&(sbuf[pos]), "["); 
      pos++; 
      pos = rec_string_parse_subformula(
        psub->u.atom.indirect_exp[i], pos, psub
      );
      sprintf(&(sbuf[pos]), "]"); 
      pos++; 
    }
*/
    return (pos); 
    break;

  case TYPE_QFD:
    sprintf(&(sbuf[pos]), "%s", psub->u.atom.var_name);
    return (pos + strlen(psub->u.atom.var_name)); 
  case TYPE_QSYNC_HOLDER: 
    sprintf(&(sbuf[pos]), "%s", psub->u.qsholder.qsync_var_name);
    return (pos + strlen(psub->u.qsholder.qsync_var_name)); 
  case TYPE_NULL:
    sprintf(&(sbuf[pos]), "NULL");
    return(pos + 4); 
    break;
  case TYPE_LOCAL_IDENTIFIER:
    if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
      sprintf(&(sbuf[pos]), "%1d", PI_STRING);
      return(pos+PI_LENGTH); 
    }
    else { 
      sprintf(&(sbuf[pos]), "P");
      return(pos + 1); 
    }
    break;
  case TYPE_PROCESS_COUNT: 
    sprintf(&(sbuf[pos]), "#PS"); 
    return(pos + 3); 
    break; 
  case TYPE_PEER_IDENTIFIER:
    sprintf(&(sbuf[pos]), "~P");
    return(pos + 2); 
    break;
  case TYPE_TRASH:
    sprintf(&(sbuf[pos]), "?");
    return(pos + 1); 
    break;
  case TYPE_CONSTANT:
    sprintf(&(sbuf[pos]), "%1d", psub->u.value);
    return(pos + intlen(psub->u.value)); 
    break;
  case TYPE_FLOAT_CONSTANT:
    return(string_flt(psub->u.float_value, pos));
    break;
  case TYPE_INTERVAL:
    if (psub->u.interval.status & INTERVAL_LEFT_UNBOUNDED) {
      sprintf(&(sbuf[pos]), "(-oo,");
      pos = pos + 5; 
    }
    else {
      if (psub->u.interval.status & INTERVAL_LEFT_OPEN)
        sprintf(&(sbuf[pos]), "(");
      else
        sprintf(&(sbuf[pos]), "[");
      pos = pos + 1; 
      pos = rec_string_parse_subformula(
        psub->u.interval.lbound_exp, pos, psub
      );
      sprintf(&(sbuf[pos]), ",");
      pos = pos + 1; 
    }
    if (psub->u.interval.status & INTERVAL_RIGHT_UNBOUNDED) {
      sprintf(&(sbuf[pos]), "oo)");
      pos = pos + 3; 
    }
    else {
      pos = rec_string_parse_subformula(
        psub->u.interval.rbound_exp, pos, psub
      );
      if (psub->u.interval.status & INTERVAL_RIGHT_OPEN)
        sprintf(&(sbuf[pos]), ")");
      else
        sprintf(&(sbuf[pos]), "]");
      pos = pos + 1; 
      pos = rec_string_parse_subformula(psub->u.interval.rbound_exp, pos, psub);  
    }
    return(pos); 
    break;
  case TYPE_MODE_INDEX:
    sprintf(&(sbuf[pos]), "index %s", psub->u.mode_index.mode_name);
    return(pos = pos + 6 + strlen(psub->u.mode_index.mode_name)); 
    break; 
  case BIT_NOT: 
    sprintf(&(sbuf[pos]), "~(");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.exp, pos, psub); 
    sprintf(&(sbuf[pos]), ")");
    pos = pos+1; 
    return (pos); 
    break; 
  
  case BIT_OR: 
  case BIT_AND:  
  case BIT_SHIFT_RIGHT: 
  case BIT_SHIFT_LEFT: 

  case ARITH_ADD:
  case ARITH_MINUS:
  case ARITH_MULTIPLY:
  case ARITH_DIVIDE:
  case ARITH_MODULO: 
    sprintf(&(sbuf[pos]), "(");
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.arith.lhs_exp, pos, psub); 
    pos = string_op(psub->type, pos);
    pos = rec_string_parse_subformula(psub->u.arith.rhs_exp, pos, psub); 
    sprintf(&(sbuf[pos]), ")");
    pos = pos+1; 
    return (pos); 
    break; 

  case ARITH_EQ :
    if (   psub->u.arith.lhs_exp->type == TYPE_DISCRETE 
        && psub->u.arith.lhs_exp->u.atom.var == var_mode
//        && psub->u.arith.lhs_exp->u.atom.indirect_count == 0 
        ) { 
      if (psub->u.arith.rhs_exp->type == TYPE_MODE_INDEX) { 
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER
            ) 
          if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
            sprintf(&(sbuf[pos]), "%s@(%1d)", 
              psub->u.arith.rhs_exp->u.mode_index.mode_name, PI_STRING 
            ); 
            return(pos 
              + strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name)
              + intlen(PI_STRING)
              + 3
            ); 
          } 
          else { 
            sprintf(&(sbuf[pos]), "%s", 
              psub->u.arith.rhs_exp->u.mode_index.mode_name
            );
            return(pos 
              + strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name)
            ); 
          }
        else { 
          sprintf(&(sbuf[pos]), "%s@(", 
            psub->u.arith.rhs_exp->u.mode_index.mode_name 
          ); 
          pos = pos 
          + strlen(psub->u.arith.rhs_exp->u.mode_index.mode_name) 
          + 2;
          pos = rec_string_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pos, 
            psub->u.arith.lhs_exp  
          ); 
          sprintf(&(sbuf[pos]), ")"); 
          return(pos + 1); 
        } 
        break; 
      }
      else if (   psub->u.arith.rhs_exp->type == TYPE_CONSTANT
               && psub->u.arith.rhs_exp->u.value >= 0
               && psub->u.arith.rhs_exp->u.value < MODE_COUNT
               ) { 
        struct parse_mode_type	*pm; 
        char			*mname; 
        
        if (MODE) 
          mname = MODE[psub->u.arith.rhs_exp->u.value].name; 
        else for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
          if (pm->index == psub->u.arith.rhs_exp->u.value) {
            mname = pm->name; 
            break; 
          } 
        }
        if (psub->u.arith.lhs_exp->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER
            ) 
          if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
            sprintf(&(sbuf[pos]), "%s@(%1d)", mname, PI_STRING); 
            return(pos + strlen(mname) + intlen(PI_STRING) + 3); 
          } 
          else { 
            sprintf(&(sbuf[pos]), "%s", mname);
            return(pos + strlen(mname)); 
          }
        else { 
          sprintf(&(sbuf[pos]), "%s@(", mname); 
          pos = pos + strlen(mname) + 2;
          pos = rec_string_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pos, 
            psub->u.arith.lhs_exp 
          ); 
          sprintf(&(sbuf[pos]), ")"); 
          return(pos + 1); 
        } 
        break; 
      }
    }
  case ARITH_NEQ :
  case ARITH_LEQ :
  case ARITH_LESS :
  case ARITH_GREATER :
  case ARITH_GEQ :
    pos = rec_string_parse_subformula(psub->u.arith.lhs_exp, pos, psub); 
    pos = string_op(psub->type, pos);
    pos = rec_string_parse_subformula(psub->u.arith.rhs_exp, pos, psub);  
    return (pos); 
    
  case EQ :
    if (   psub->u.ineq.term_count == 1
        && psub->u.ineq.term[0].coeff->type == TYPE_CONSTANT  
        && psub->u.ineq.term[0].coeff->u.value == 1  
        && psub->u.ineq.term[0].operand->type == TYPE_DISCRETE
        && psub->u.ineq.term[0].operand->u.atom.var == var_mode
//        && psub->u.ineq.term[0].operand->u.atom.indirect_count == 0 
        ) { 
      if (psub->u.ineq.offset->type == TYPE_MODE_INDEX) { 
        if (psub->u.ineq.term[0].operand->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER 
            )  
          if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
            sprintf(&(sbuf[pos]), "%s[%1d]", 
              psub->u.ineq.offset->u.mode_index.mode_name, PI_STRING 
            ); 
            return(pos 
              + strlen(psub->u.ineq.offset->u.mode_index.mode_name) 
              + intlen(PI_STRING) 
              + 2
            ); 
          } 
          else { 
            sprintf(&(sbuf[pos]), "%s", 
              psub->u.ineq.offset->u.mode_index.mode_name 
            );
            return(pos 
              + strlen(psub->u.ineq.offset->u.mode_index.mode_name)  
            ); 
          }
        else { 
          sprintf(&(sbuf[pos]), "%s[", 
            psub->u.ineq.offset->u.mode_index.mode_name 
          ); 
          pos = pos + strlen(psub->u.ineq.offset->u.mode_index.mode_name) + 1;
          pos = rec_string_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pos, 
            psub->u.arith.lhs_exp
          ); 
          sprintf(&(sbuf[pos]), "]"); 
          return(pos + 1); 
        } 
        break; 
      }
      else if (   psub->u.ineq.offset->type == TYPE_CONSTANT
               && psub->u.ineq.offset->u.value >= 0
               && psub->u.ineq.offset->u.value < MODE_COUNT
               ) { 
        struct parse_mode_type	*pm; 
        char			*mname; 
        
        if (MODE) 
          mname = MODE[psub->u.ineq.offset->u.value].name; 
        else for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
          if (pm->index == psub->u.ineq.offset->u.value) {
            mname = pm->name; 
            break; 
          } 
        }
        if (psub->u.ineq.term[0].operand->u.atom.exp_base_proc_index->type 
            == TYPE_LOCAL_IDENTIFIER 
            )  
          if (PI_STRING >= 1 && PI_STRING <= PROCESS_COUNT) {
            sprintf(&(sbuf[pos]), "%s[%1d]", mname, PI_STRING); 
            return(pos + strlen(mname) + intlen(PI_STRING) + 2); 
          } 
          else { 
            sprintf(&(sbuf[pos]), "%s", mname);
            return(pos + strlen(mname)); 
          }
        else { 
          sprintf(&(sbuf[pos]), "%s[", 
            mname 
          ); 
          pos = pos + strlen(mname) + 1;
          pos = rec_string_parse_subformula(
            psub->u.arith.lhs_exp->u.atom.exp_base_proc_index, pos, 
            psub->u.arith.lhs_exp 
          ); 
          sprintf(&(sbuf[pos]), "]"); 
          return(pos + 1); 
        } 
        break; 
      }
    }
  case NEQ :
  case LEQ :
  case LESS :
  case GREATER :
  case GEQ : 
    if (psub->u.ineq.term_count == 0) { 
      sprintf(&(sbuf[pos]), "0");
      pos = pos + 1; 
    } 
    else for (i = 0; i < psub->u.ineq.term_count; i++)  {
      if (psub->u.ineq.term[i].coeff->type == TYPE_CONSTANT) {
        if (psub->u.ineq.term[i].coeff->u.value < 0)
	  if (psub->u.ineq.term[i].coeff->u.value == -1) { 
	    sprintf(&(sbuf[pos]), "-");
	    pos = pos + 1; 
	  }
	  else {
	    sprintf(&(sbuf[pos]), "%1d ", psub->u.ineq.term[i].coeff->u.value);
	    pos = pos + 1 + intlen(psub->u.ineq.term[i].coeff->u.value); 
	  }
	else
	  if (psub->u.ineq.term[i].coeff->u.value == 1) {
	    if (i) {
	      sprintf(&(sbuf[pos]), "+");
	      pos = pos + 1; 
	    }
	  }
	  else {
	    if (i) {
	      sprintf(&(sbuf[pos]), "%1d ", psub->u.ineq.term[i].coeff->u.value);
	      pos = pos + 1 + intlen(psub->u.ineq.term[i].coeff->u.value); 
	    }
	    else {
	      sprintf(&(sbuf[pos]), "+%1d ", psub->u.ineq.term[i].coeff->u.value);
	      pos = pos + 2 + intlen(psub->u.ineq.term[i].coeff->u.value);
	    }  
	  }
      }
      else {
        if (i) {
          sprintf(&(sbuf[pos]), "+(");
	  pos = pos + 2; 
	}
	else {
	  sprintf(&(sbuf[pos]), "(");
	  pos = pos + 1; 
	}
	pos = rec_string_parse_subformula(psub->u.ineq.term[i].coeff, pos, psub); 
	sprintf(&(sbuf[pos]), ")");
	pos = pos + 1; 
      }
      pos = rec_string_parse_subformula(psub->u.ineq.term[i].operand, pos, psub); 
    }
    pos = string_op(psub->type, pos);
    pos = rec_string_parse_subformula(psub->u.ineq.offset, pos, psub); 
    return(pos); 
  case ARITH_CONDITIONAL: 
    sprintf(&(sbuf[pos]), "(("); 
    pos=pos+2; 
    pos = rec_string_parse_subformula(psub->u.arith_cond.cond, pos, psub);  
    sprintf(&(sbuf[pos]), ")? "); 
    pos = pos+3; 
    pos = rec_string_parse_subformula(psub->u.arith_cond.if_exp, pos, psub);  
    sprintf(&(sbuf[pos]), ":"); 
    pos++; 
    pos = rec_string_parse_subformula(psub->u.arith_cond.else_exp, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos++; 
    return(pos); 
  case TYPE_INLINE_BOOLEAN_DECLARE: 
    sprintf(&(sbuf[pos]), "inline boolean %s", 
      psub->u.inline_declare.inline_exp_name
    ); 
    pos = pos + 15 + strlen(psub->u.inline_declare.inline_exp_name); 
    if (nl = psub->u.inline_declare.formal_argument_list) { 
      sprintf(&(sbuf[pos]), "(%s", nl->name); 
      pos = pos + 1 + strlen(nl->name); 
      for (nl = nl->next_name_link; nl; nl = nl->next_name_link) { 
        sprintf(&(sbuf[pos]), ", %s", nl->name); 
        pos = pos + 2 + strlen(nl->name); 
      } 
      sprintf(&(sbuf[pos]), ")"); 
      pos++; 
    } 
    sprintf(&(sbuf[pos]), " {\n  "); 
    pos = pos + 5; 
    pos = rec_string_parse_subformula(psub->u.inline_declare.declare_exp, pos, psub);  
    sprintf(&(sbuf[pos]), "\n} /* %s() */\n", 
      psub->u.inline_declare.inline_exp_name
    ); 
    pos=pos+6+strlen(psub->u.inline_declare.inline_exp_name)+6; 
    return(pos); 
    
  case TYPE_INLINE_DISCRETE_DECLARE: 
    sprintf(&(sbuf[pos]), "inline discrete %s", 
      psub->u.inline_declare.inline_exp_name
    ); 
    pos = pos + 16 + strlen(psub->u.inline_declare.inline_exp_name); 
    if (nl = psub->u.inline_declare.formal_argument_list) { 
      sprintf(&(sbuf[pos]), "(%s", nl->name); 
      pos = pos + 1 + strlen(nl->name); 
      for (nl = nl->next_name_link; nl; nl = nl->next_name_link) { 
        sprintf(&(sbuf[pos]), ", %s", nl->name); 
        pos = pos + 2 + strlen(nl->name); 
      } 
      sprintf(&(sbuf[pos]), ")"); 
      pos++; 
    } 
    sprintf(&(sbuf[pos]), " {\n  "); 
    pos = pos + 5; 
    pos = rec_string_parse_subformula(psub->u.inline_declare.declare_exp, pos, psub);  
    sprintf(&(sbuf[pos]), "\n} /* %s() */\n", 
      psub->u.inline_declare.inline_exp_name
    ); 
    pos=pos+6+strlen(psub->u.inline_declare.inline_exp_name)+6; 
    return(pos); 
    
  case TYPE_INLINE_CALL: 
    sprintf(&(sbuf[pos]), "%s", psub->u.inline_call.inline_exp_name); 
    pos = pos + strlen(psub->u.inline_call.inline_exp_name);
    if (pbu = psub->u.inline_call.actual_argument_list) { 
      sprintf(&(sbuf[pos]), "("); 
      pos++; 
      pos = rec_string_parse_subformula(pbu->subexp, pos, psub);  
      for (pbu = pbu->bnext; pbu; pbu = pbu->bnext) { 
      	sprintf(&(sbuf[pos]), ", "); 
      	pos = pos + 2; 
        pos = rec_string_parse_subformula(pbu->subexp, pos, psub);  
      }
      sprintf(&(sbuf[pos]), ")"); 
      pos = pos + 1; 
    } 
    return (pos); 
     
  case TYPE_INLINE_ARGUMENT: 
    sprintf(&(sbuf[pos]), "%s", psub->u.argument);
    pos = pos + strlen(psub->u.argument); 
    return(pos); 
  case AND :
    pbu = psub->u.bexp.blist;
    sprintf(&(sbuf[pos]), "("); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(pbu->subexp, pos, psub); 
    for (jj = psub->u.bexp.len-1, pbu = pbu->bnext;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      sprintf(&(sbuf[pos]), "&&");
      pos = pos + 2; 
      pos = rec_string_parse_subformula(pbu->subexp, pos, psub); 
    }
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos);
  case OR :
    pbu = psub->u.bexp.blist;
    sprintf(&(sbuf[pos]), "(");
    pos = pos + 1; 
    pos = rec_string_parse_subformula(pbu->subexp, pos, psub); 
    for (jj = psub->u.bexp.len-1, pbu = pbu->bnext;
	 jj;
	 jj--, pbu = pbu->bnext
	 ) {
      sprintf(&(sbuf[pos]), "||"); 
      pos = pos + 2; 
      pos = rec_string_parse_subformula(pbu->subexp, pos, psub);  
    }
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case NOT :
    sprintf(&(sbuf[pos]), "not(");
    pos = pos + 4; 
    pos = rec_string_parse_subformula(psub->u.bexp.blist->subexp, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos);
  case IMPLY :
    sprintf(&(sbuf[pos]), "("); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.bexp.blist->subexp, pos, psub);  
    sprintf(&(sbuf[pos]), "=>");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.bexp.blist->bnext->subexp, pos, psub);  
    sprintf(&(sbuf[pos]), ")");
    pos = pos + 1; 
    return (pos);
  case FORALL: 
    sprintf(&(sbuf[pos]), "forall %s:", psub->u.qexp.quantifier_name); 
    pos = pos + 8 + strlen(psub->u.qexp.quantifier_name); 
    pos = rec_string_parse_subformula(psub->u.qexp.lb_exp, pos, psub);  
    sprintf(&(sbuf[pos]), " .. "); 
    pos = pos + 4; 
    pos = rec_string_parse_subformula(psub->u.qexp.ub_exp, pos, psub);  
    sprintf(&(sbuf[pos]), ","); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.qexp.child, pos, psub);  
    return(pos); 
  case EXISTS: 
    sprintf(&(sbuf[pos]), "exists %s:", psub->u.qexp.quantifier_name); 
    pos = pos + 8 + strlen(psub->u.qexp.quantifier_name); 
    pos = rec_string_parse_subformula(psub->u.qexp.lb_exp, pos, psub);  
    sprintf(&(sbuf[pos]), " .. "); 
    pos = pos + 4; 
    pos = rec_string_parse_subformula(psub->u.qexp.ub_exp, pos, psub);  
    sprintf(&(sbuf[pos]), ","); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.qexp.child, pos, psub);  
    return(pos); 

  case PROJECT: 
    sprintf (&(sbuf[pos]), "eliminate %s(", 
      VAR[psub->u.project.variable_index].NAME
    ); 
    pos = pos + 11 + strlen(VAR[psub->u.project.variable_index].NAME); 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 
  case PROJECT_TIME:  
    sprintf (&(sbuf[pos]), "eliminate time("); 
    pos = pos + 15; 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 
  case PROJECT_QSYNC:  
    sprintf (&(sbuf[pos]), "eliminate qsync("); 
    pos = pos + 16; 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 
  case PROJECT_TYPE:  
    sprintf (&(sbuf[pos]), "eliminate type %1d(", 
      psub->u.project.variable_index
    ); 
    pos = pos + 16 + intlen(psub->u.project.variable_index); 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 
  case PROJECT_CLOCK_LOWER_EXTEND:  
    sprintf (&(sbuf[pos]), "extend clock lower-bounds("); 
    pos = pos + 26; 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 

  case PROJECT_CLOCK_UPPER_EXTEND:  
    sprintf (&(sbuf[pos]), "extend clock upper-bounds("); 
    pos = pos + 26; 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 

  case PROJECT_PEER:  
    sprintf (&(sbuf[pos]), "eliminate peer of %1d(", 
      psub->u.project.variable_index
    ); 
    pos = pos + 19 + intlen(psub->u.project.variable_index); 
    pos = rec_string_parse_subformula(psub->u.project.child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    return(pos+1); 
    break; 

  case RESET:
    sprintf(&(sbuf[pos]), "RESET %s (", psub->u.reset.clock_name); 
    pos = pos + 8 + strlen(psub->u.reset.clock_name); 
    pos = rec_string_parse_subformula(psub->u.reset.child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case FORALL_ALWAYS: 
    pos = string_sop_fairness("FORALL", "ALWAYS", psub, pos); 
    pos = string_time_interval(
      psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos
    ); 
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case FORALL_EVENTUALLY:
    pos = string_sop_fairness("FORALL", "EVENTUALLY", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos); 
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case EXISTS_ALWAYS: 
    pos = string_sop_fairness("EXISTS", "ALWAYS", psub, pos);
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos); 
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case EXISTS_EVENTUALLY:
    pos = string_sop_fairness("EXISTS", "EVENTUALLY", psub, pos);
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos); 
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case EXISTS_UNTIL: 
    sprintf(&(sbuf[pos]), "EXISTS "); 
    pos = pos + 7; 
    if (psub->u.mexp.strong_fairness_count) {
      sprintf(&(sbuf[pos]), "STRONG FAIRNESS: {"); 
      pos = pos + 18; 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        pos = rec_string_parse_subformula(fl->fairness, pos, psub); 
        sprintf(&(sbuf[pos]), ";"); 
        pos = pos + 1; 
      }
      sprintf(&(sbuf[pos]), "}"); 
      pos = pos + 1; 
    } 
    if (psub->u.mexp.weak_fairness_count) {
      sprintf(&(sbuf[pos]), "WEAK FAIRNESS: {"); 
      pos = pos + 16; 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        pos = rec_string_parse_subformula(fl->fairness, pos, psub);  
        sprintf(&(sbuf[pos]), ";");
	pos = pos + 1;  
      }
      sprintf(&(sbuf[pos]), "}"); 
      pos = pos + 1; 
    }
    sprintf(&(sbuf[pos]), "("); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    sprintf(&(sbuf[pos]), "UNTIL"); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.dest_child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos);
  case FORALL_UNTIL: 
    sprintf(&(sbuf[pos]), "FORALL "); 
    pos = pos + 7; 
    if (psub->u.mexp.strong_fairness_count) {
      sprintf(&(sbuf[pos]), "STRONG FAIRNESS: {"); 
      pos = pos + 18; 
      for (fl = psub->u.mexp.strong_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        pos = rec_string_parse_subformula(fl->fairness, pos, psub); 
        sprintf(&(sbuf[pos]), ";"); 
        pos = pos + 1; 
      }
      sprintf(&(sbuf[pos]), "}"); 
      pos = pos + 1; 
    } 
    if (psub->u.mexp.weak_fairness_count) {
      sprintf(&(sbuf[pos]), "WEAK FAIRNESS: {"); 
      pos = pos + 16; 
      for (fl = psub->u.mexp.weak_fairness_list; fl; fl = fl->next_ps_fairness_link) {
        pos = rec_string_parse_subformula(fl->fairness, pos, psub);  
        sprintf(&(sbuf[pos]), ";");
	pos = pos + 1;  
      }
      sprintf(&(sbuf[pos]), "}"); 
      pos = pos + 1; 
    }
    sprintf(&(sbuf[pos]), "("); 
    pos = pos + 1; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    sprintf(&(sbuf[pos]), "UNTIL"); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " ("); 
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.dest_child, pos, psub); 
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos);
  case EXISTS_CHANGE:
    pos = string_sop_fairness("EXISTS", "CHANGE", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case FORALL_CHANGE: 
    pos = string_sop_fairness("FORALL", "CHANGE", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case EXISTS_OFTEN: 
    pos = string_sop_fairness("EXISTS", "OFTEN", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case EXISTS_ALMOST: 
    pos = string_sop_fairness("EXISTS", "ALMOST", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case FORALL_OFTEN:
    pos = string_sop_fairness("FORALL", "OFTEN", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 
  case FORALL_ALMOST: 
    pos = string_sop_fairness("FORALL", "ALMOST", psub, pos); 
    pos = string_time_interval(psub->u.mexp.time_lb, psub->u.mexp.time_ub, pos);
    sprintf(&(sbuf[pos]), " (");
    pos = pos + 2; 
    pos = rec_string_parse_subformula(psub->u.mexp.path_child, pos, psub);  
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return (pos); 

  case RED: 
//    sprintf(&(sbuf[pos]), " RED ");
    sprintf(&(sbuf[pos]), "("); 
    pos = pos + 1; 
    pos = rec_string_diagram(psub->u.rpred.red, pos); 
    sprintf(&(sbuf[pos]), ")"); 
    pos = pos + 1; 
    return(pos); 
/*
    red_print_line(psub->u.rpred.red);
*/
    break; 
  default: 
    fprintf(RED_OUT, 
      "\nERROR: Unexpected exp type %1d in rec_string_parse_subformula().\n", 
      psub->type
    ); 
    fflush(RED_OUT); 
    bk(0); 
  }
  fprintf(RED_OUT, 
    "\nERROR: You might have forget to return the write-head position %1d.\n", 
    pos
  ); 
  bk(0); 
}
  /* rec_string_parse_subformula() */ 



char	*tmp_buf_subexp; 

char	*string_parse_subformula(psub, pi, depth)
     struct ps_exp_type	*psub;
     int		pi, 
			depth; // -1 for no depth calculation. 
{
  int	len; 

  PI_STRING = pi; 
  PI_LENGTH = intlen(pi); 
  SUB_DEPTH = depth; 
  len = rec_string_parse_subformula(psub, 0, NULL); 
  SUB_DEPTH = FLAG_NO_SUBFORMULA_DEPTH; 

  sbuf[len] = '\0'; 
  tmp_buf_subexp = malloc(len+1); 
  sprintf(tmp_buf_subexp, "%s", sbuf); 

  return(tmp_buf_subexp); 
}
  /* string_parse_subformula() */ 




char	*string_stream_operations(int xi) { 
  int	ai, len; 
  
  if (XTION[xi].stream_operation_count == 0) { 
    tmp_buf_subexp = malloc(1);
    tmp_buf_subexp[0] = '\0'; 
    return(tmp_buf_subexp); 
  } 

  PI_STRING = INDEX_LOCAL_IDENTIFIER; 
  PI_LENGTH = 0; 
  len = 0; 
  for (ai = 0; ai < XTION[xi].stream_operation_count; ai++) { 
    switch (XTION[xi].stream_operation[ai].operation) {
    case OP_STREAM_OPEN_INPUT: 
      sprintf(&(sbuf[len]), " open input %s;", 
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      len = len + 12 
      + strlen(VAR[XTION[xi].stream_operation[ai].stream].NAME) + 1; 
      break; 

    case OP_STREAM_OPEN_OUTPUT: 
      sprintf(&(sbuf[len]), " open output %s;", 
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      len = len + 13 
      + strlen(VAR[XTION[xi].stream_operation[ai].stream].NAME) + 1; 
      break; 

    case OP_STREAM_CLOSE: 
      sprintf(&(sbuf[len]), " close %s;", 
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      len = len + 7 
      + strlen(VAR[XTION[xi].stream_operation[ai].stream].NAME) + 1; 
      break; 

    case OP_STREAM_INPUT: 
      sprintf(&(sbuf[len]), " input %s >> ",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      len = len + 7 
      + strlen(VAR[XTION[xi].stream_operation[ai].stream].NAME) + 4; 
      len = rec_string_parse_subformula(
        XTION[xi].stream_operation[ai].var, len, NULL
      ); 
      sprintf(&(sbuf[len]), ";"); 
      len = len + 1; 
      break; 
    case OP_STREAM_OUTPUT: 
      sprintf(&(sbuf[len]), " output %s << ",  
        VAR[XTION[xi].stream_operation[ai].stream].NAME
      ); 
      len = len + 8 
      + strlen(VAR[XTION[xi].stream_operation[ai].stream].NAME) + 4; 
      len = rec_string_parse_subformula(
        XTION[xi].stream_operation[ai].value_exp, len, NULL
      ); 
      sprintf(&(sbuf[len]), ";"); 
      len = len + 1; 
      break; 
  } }

  sbuf[len] = '\0'; 
  tmp_buf_subexp = malloc(len+1); 
  sprintf(tmp_buf_subexp, "%s", sbuf); 
/*
  fprintf(RED_OUT, "\nleaving string_sync_list() with %s:\n", tmp_buf_subexp); 
*/
  return(tmp_buf_subexp); 
}
  /* string_stream_operations() */ 




char	*string_sync_type(int s) { 
  switch (s) { 
  case FLAG_ACCESS_WRITE: 
    return("!"); 
  case FLAG_ACCESS_READ: 
    return("?"); 
  default: 
    return(NULL); 
  }
} 
  /* string_sync_type() */ 
  
  
  
  
char	*string_sync_list(
  struct parse_xtion_sync_type	*sl 
) { 
  struct parse_xtion_sync_type	*xs; 
  int				len; 
  
  if (sl == NULL) {
    tmp_buf_subexp = malloc(1);
    tmp_buf_subexp[0] = '\0'; 
    return(tmp_buf_subexp); 
  }
  
  PI_STRING = INDEX_LOCAL_IDENTIFIER; 
  PI_LENGTH = 0; 
  len = 0; 
  for (xs = sl; xs; xs = xs->next_parse_xtion_sync) { 
    switch (xs->status) { 
    case FLAG_ADDRESS_NULL: 
      sprintf(&(sbuf[len]), "%s%s ", 
        string_sync_type(xs->type), 
        xs->sync_var->name
      ); 
      len = len + 1 + strlen(xs->sync_var->name) + 1; 
      break; 
    case FLAG_ADDRESS_HOLDER: 
      sprintf(&(sbuf[len]), "%s%s@%s ", 
        string_sync_type(xs->type), 
        xs->sync_var->name, 
        xs->qsync_var->name 
      ); 
      len = len 
      + 1 // for ! or ? 
      + strlen(xs->sync_var->name) 
      + 1 // for @ 
      + strlen(xs->qsync_var->name) 
      + 1; 
      break; 
    case FLAG_ADDRESS_ENFORCER: 
      sprintf(&(sbuf[len]), "%s%s@(", 
        string_sync_type(xs->type), 
        xs->sync_var->name
      ); 
      len = len 
      + 1 // for ! or ? 
      + strlen(xs->sync_var->name) 
      + 3; // for @( 
      len = rec_string_parse_subformula(xs->exp_quantification, len, NULL); 
      sprintf(&(sbuf[len]), ") "); 
      len = len + 2; 
      break; 
    case FLAG_ADDRESS_MULTIPLE: 
      sprintf(&(sbuf[len]), "%s(", string_sync_type(xs->type)); 
      len = len + 2; 
      len = rec_string_parse_subformula(xs->exp_multiplicity, len, NULL), 
      sprintf(&(sbuf[len]), ")%s ",  xs->sync_var->name); 
      len = len + 1 + strlen(xs->sync_var->name) + 1;  
      break; 
    case FLAG_ADDRESS_DUPLICATE: 
      break; 
    }  
  } 

  sbuf[len-1] = '\0'; 
  tmp_buf_subexp = malloc(len); 
  sprintf(tmp_buf_subexp, "%s", sbuf); 
/*
  fprintf(RED_OUT, "\nleaving string_sync_list() with %s:\n", tmp_buf_subexp); 
*/
  return(tmp_buf_subexp); 
}
  /* string_sync_list() */   


char	*string_xtion_sync(
  int	xi, 
  int	si  
) { 
  struct parse_xtion_sync_type	*sl, *xs; 
  int				len; 
  
  sl = XTION[xi].parse_xtion->sync_list; 
  if (sl == NULL) {
    tmp_buf_subexp = malloc(1);
    tmp_buf_subexp[0] = '\0'; 
    return(tmp_buf_subexp); 
  }
  
  PI_STRING = INDEX_LOCAL_IDENTIFIER; 
  PI_LENGTH = 0; 
  len = 0; 
  for (xs = sl; si > 0; xs = xs->next_parse_xtion_sync, si--) ; 
  switch (xs->status) { 
  case FLAG_ADDRESS_NULL: 
    sprintf(&(sbuf[len]), "%s%s ", 
      string_sync_type(xs->type), 
      xs->sync_var->name
    ); 
    len = len + 1 + strlen(xs->sync_var->name) + 1; 
    break; 
  case FLAG_ADDRESS_HOLDER: 
    sprintf(&(sbuf[len]), "%s%s@%s ", 
      string_sync_type(xs->type), 
      xs->sync_var->name, 
      xs->qsync_var->name 
    ); 
    len = len 
    + 1 // for ! or ? 
    + strlen(xs->sync_var->name) 
    + 1 // for @ 
    + strlen(xs->qsync_var->name) 
    + 1; 
    break; 
  case FLAG_ADDRESS_ENFORCER: 
    sprintf(&(sbuf[len]), "%s%s@(", 
      string_sync_type(xs->type), 
      xs->sync_var->name
    ); 
    len = len 
    + 1 // for ! or ? 
    + strlen(xs->sync_var->name) 
    + 2; // for @( 
    len = rec_string_parse_subformula(xs->exp_quantification, len, NULL); 
    sprintf(&(sbuf[len]), ") "); 
    len = len + 2; 
    break; 
  case FLAG_ADDRESS_MULTIPLE: 
    sprintf(&(sbuf[len]), "%s(", string_sync_type(xs->type)); 
    len = len + 2; 
    len = rec_string_parse_subformula(xs->exp_multiplicity, len, NULL), 
    sprintf(&(sbuf[len]), ")%s ",  xs->sync_var->name); 
    len = len + 1 + strlen(xs->sync_var->name) + 1;  
    break; 
  case FLAG_ADDRESS_DUPLICATE: 
    break; 
  }  

  sbuf[len-1] = '\0'; 
  tmp_buf_subexp = malloc(len); 
  sprintf(tmp_buf_subexp, "%s", sbuf); 
/*
  fprintf(RED_OUT, "\nleaving string_sync_list() with %s:\n", tmp_buf_subexp); 
*/
  return(tmp_buf_subexp); 
}
  /* string_sync_list() */   



/************************************************************************
 *  The following procedures are for converting parse statements to strings. 
 */
 
int	string_parse_action(st, pos)
     struct parse_statement_type	*st; 
     int				pos;
{
  int 	len, i, numerator, denominator; 
  char	*mn; 

//  fprintf(RED_OUT, "      "); 
  
  switch (st->op) {
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    if (   st->u.act.lhs->type == TYPE_DISCRETE
        && st->u.act.lhs->u.atom.var == var_mode
        && st->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER
        ) { 
      if (st->u.act.rhs_exp->type == TYPE_MODE_INDEX) { 
        sprintf(&(sbuf[pos]), "goto %s;", 
          st->u.act.rhs_exp->u.mode_index.mode_name
        ); 
        pos = pos + 5 + strlen(st->u.act.rhs_exp->u.mode_index.mode_name) + 1; 
        break; 
      }
      else if (   st->u.act.rhs_exp->type == TYPE_CONSTANT 
               && st->u.act.rhs_exp->u.value >= 0
               && st->u.act.rhs_exp->u.value < MODE_COUNT
               ) { 
        struct parse_mode_type	*pm; 
        char			*mname; 
        
        if (MODE) 
          mname = MODE[st->u.act.rhs_exp->u.value].name; 
        else for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
          if (pm->index == st->u.act.rhs_exp->u.value) {
            mname = pm->name; 
            break; 
          } 
        }
        sprintf(&(sbuf[pos]), "goto %s;", mname); 
        pos = pos + 5 + strlen(mname) + 1; 
        break; 
      } 
    }
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
  case ASSIGN_HYBRID_EXP:
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL); 
    sprintf(&(sbuf[pos]), "="); pos++; 
    pos = rec_string_parse_subformula(st->u.act.rhs_exp, pos, NULL);
    sprintf(&(sbuf[pos]), ";"); pos++; 
    break;
  case INCREMENT_BY_CONSTANT:
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    sprintf(&(sbuf[pos]), "++%1d;", st->u.act.rhs_exp->u.value);
    pos = pos + 3 + intlen(st->u.act.rhs_exp->u.value);
    break;
  case DECREMENT_BY_CONSTANT:
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    sprintf(&(sbuf[pos]), "--%1d;", st->u.act.rhs_exp->u.value);
    pos = pos + 3 + intlen(st->u.act.rhs_exp->u.value);
    break;
  case ASSIGN_TRASH: 
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    sprintf(&(sbuf[pos]), "=?;"); 
    pos = pos + 3; 
    break;
  }
  return(pos); 
}
/* string_parse_action() */




int	rec_string_parse_statement(st, pos) 
	struct parse_statement_type	*st; 
	int				pos; 
{ 
  int					i; 
  struct parse_statement_link_type	*stl; 
  
  if (!st) {
    sprintf(&(sbuf[pos]), ";"); 
    return (++pos); 
  }  
  switch (st->op) { 
  case UNCHANGED: 
    sprintf(&(sbuf[pos]), ";"); 
    pos++; 
    break; 
  case ST_IF: 
    sprintf(&(sbuf[pos]), "if ("); pos = pos+4; 
    pos = rec_string_parse_subformula(st->u.branch.cond, pos, NULL); 
    sprintf(&(sbuf[pos]), ")"); pos++; 
    if (st->u.branch.if_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      sprintf(&(sbuf[pos]), "{"); pos++; 
      pos = rec_string_parse_statement(st->u.branch.if_statement, pos); 
      sprintf(&(sbuf[pos]), "}"); pos++; 
    }
    else 
      pos = rec_string_parse_statement(st->u.branch.if_statement, pos); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      sprintf(&(sbuf[pos]), " else "); 
      pos = pos + 6; 
      if (st->u.branch.else_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
        sprintf(&(sbuf[pos]), "{"); pos++; 
        pos = rec_string_parse_statement(st->u.branch.else_statement, pos); 
        sprintf(&(sbuf[pos]), "}"); pos++; 
      }
      else 
        pos = rec_string_parse_statement(st->u.branch.else_statement, pos); 
    } 
    break; 
  case ST_WHILE: 
    sprintf(&(sbuf[pos]), "while ("); pos = pos + 7; 
    pos = rec_string_parse_subformula(st->u.loop.cond, pos, NULL); 
    sprintf(&(sbuf[pos]), ")"); pos++; 
    if (st->u.loop.statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      sprintf(&(sbuf[pos]), "{"); pos++; 
      pos = rec_string_parse_statement(st->u.loop.statement, pos); 
      sprintf(&(sbuf[pos]), "}"); pos++; 
    }
    else 
      pos = rec_string_parse_statement(st->u.loop.statement, pos); 
    break; 
  case ST_SEQ: 
    for (stl = st->u.seq.statement_list; 
         stl; 
         stl = stl->next_parse_statement_link
         ) { 
      pos = rec_string_parse_statement(stl->statement, pos); 
    } 
    break; 
  case ST_CALL: 
    sprintf(&(sbuf[pos]), "call %s to %s;", 
      st->u.call.call_mode_name, 
      st->u.call.ret_mode_name
    ); 
    pos = pos + 10 
    + strlen(st->u.call.call_mode_name) 
    + strlen(st->u.call.ret_mode_name); 
    break; 
  case ST_RETURN: 
    sprintf(&(sbuf[pos]), "return;"); 
    pos = pos + 7; 
    break; 
    
  case ST_CPLUG: 
    sprintf(&(sbuf[pos]), "Cplug %1d %1d;", 
      st->u.cplug.cmod_index, st->u.cplug.cproc_index
    ); 
    pos = pos + 8 
    + intlen(st->u.cplug.cmod_index) 
    + intlen(st->u.cplug.cproc_index); 
    break; 
    
  default: 
    pos = string_parse_action(st, pos); 
    break; 	
  } 
  return(pos); 
}
  /* rec_string_parse_statement() */ 






char	*tmp_buf_statement; 

char	*string_parse_statement_instantiate(st, pi) 
	struct parse_statement_type	*st; 
	int				pi; 
{
  int	len; 
  
  PI_STRING = pi; 
  PI_LENGTH = intlen(pi); 
  len = rec_string_parse_statement(st, 0); 
  
  if (len >= size_sbuf) { 
    fprintf(RED_OUT, "Uh-Oh, the string is longer than the processing buffer.\n"); 
    exit(0); 	
  } 
  sbuf[len] = '\0'; 
  tmp_buf_statement = malloc(len+1); 
  sprintf(tmp_buf_statement, "%s", sbuf); 
  
  return(tmp_buf_statement); 
}
  /* string_parse_statement_instantiate() */ 
  
  
  
 

/* The following procedure is adapted from print_linear_action_line(). 
 * The length does not include the last null char.
 */

int 	string_linear_action(st, pos)
     struct statement_type	*st; 
     int 			pos;
{
  int   		len, i, numerator, denominator;
  struct red_type	*red_offset; 

  #if RED_DEBUG_REDSTRING_MODE
  fprintf(RED_OUT, "\n=== In string_linear_action:%x ========\n", st); 
  print_statement_line(st); 
  fprintf(RED_OUT, "\n"); 
  fflush(RED_OUT); 
  #endif 
  
  pos = rec_string_parse_subformula(st->u.act.term[0].operand, pos, NULL); 
  sprintf(&(sbuf[pos]), "="); 
  pos++; // fprintf (RED_OUT, "=");
  if (st->u.act.term_count == 2) {
    if (st->u.act.term[1].coeff->type == TYPE_CONSTANT) {
      numerator = -1*st->u.act.term[1].coeff->u.value;
      denominator = 1;
    }
    else {
      numerator = -1*st->u.act.single_coeff_numerator[PI_STRING];
      denominator = st->u.act.single_coeff_denominator[PI_STRING];
    }
    if (denominator != 1){
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "-(%1d/%1d)", abs(numerator), denominator);
        pos = pos + 4 + intlen(abs(numerator)) + intlen(denominator);
      }
      else if(i>1) {
        sprintf(&(sbuf[pos]), "+(%1d/%1d)", numerator, denominator);
        pos = pos + 4 + intlen(numerator) + intlen(denominator);
      }
      else {
        sprintf(&(sbuf[pos]), "%1d/%1d", numerator, denominator);
        pos = pos + 1 + intlen(numerator) + intlen(denominator);
      }
    }
    else if(numerator !=1){
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "%1d*", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
      else if(i>1) {
        sprintf(&(sbuf[pos]), "+%1d*", numerator);
        pos = pos + 2 + intlen(numerator); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d*", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
    }
    // print_parse_subformula(st->u.act.term[1].operand, FLAG_GENERAL_PROCESS_IDENTIFIER);
    pos = rec_string_parse_subformula(st->u.act.term[1].operand, pos, NULL);
  }
  else for (i = 1; i < st->u.act.term_count; i++) {
    if (st->u.act.term[i].coeff->type == TYPE_CONSTANT) {
      numerator = -1*st->u.act.term[i].coeff->u.value;
      denominator = 1;
    }
    else {
      rec_get_rationals(st->u.act.term[i].coeff, &numerator, &denominator);
      numerator = -1 * numerator;
    }
    if (denominator != 1){
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "-(%1d/%1d)", abs(numerator), denominator);
        pos = pos + 4 + intlen(abs(numerator)) + intlen(denominator); 
      }
      else if(i>1) {
        sprintf(&(sbuf[pos]), "+(%1d/%1d)", numerator, denominator);
        pos = pos + 4 + intlen(numerator) + intlen(denominator); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d/%1d", numerator, denominator);
        pos = pos + 1 + intlen(numerator) + intlen(denominator); 
      }
    }
    else if(numerator !=1){
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "%1d*", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
      else if(i>1) {
        sprintf(&(sbuf[pos]), "+%1d*", numerator);
        pos = pos + 2 + intlen(numerator); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d*", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
    }
    pos = rec_string_parse_subformula(st->u.act.term[i].operand, pos, NULL);
  }

  if (st->u.act.offset->type == TYPE_CONSTANT) {
/*    if (mode_index_value(st)) {
      fprintf(RED_OUT, "%s", MODE[st->u.act.offset->u.value].name); 
    }
    else if (pointer_dirty_value(st)) { 
      fprintf(RED_OUT, "DIRTY"); 
    } 
    else 
*/
    if (st->u.act.offset->u.value <= 0) {
      sprintf(&(sbuf[pos]), "%1d;", st->u.act.offset->u.value);
      pos = pos + 1 + intlen(st->u.act.offset->u.value); 
    }
    else /* (st->u.act.offset->u.value > 0) */
         if (st->u.act.term_count >= 2) {
      sprintf(&(sbuf[pos]), "+%1d;", st->u.act.offset->u.value);
      pos = pos + 2 + intlen(st->u.act.offset->u.value); 
    } 
    else { 
      sprintf(&(sbuf[pos]), "%1d;", st->u.act.offset->u.value);
      pos = pos + 1 + intlen(st->u.act.offset->u.value);     	
    } 
  }
  else if (st->u.act.offset->type == TYPE_INTERVAL) { 
    // for outputting the lower-bound of the interval. 
    if (st->u.act.offset->u.interval.status & INTERVAL_LEFT_UNBOUNDED) {
      sprintf(&(sbuf[pos]), "+(-oo,");
      pos = pos + 6; 
    }
    else {
      if (st->u.act.offset->u.interval.status & INTERVAL_LEFT_OPEN) {
        sprintf(&(sbuf[pos]), "(");
        pos = pos + 1; 
      }
      else {
        sprintf(&(sbuf[pos]), "[");
        pos = pos + 1; 
      }
      get_rationals(st->u.act.offset->u.interval.lbound_exp, PI_STRING, 
      	&numerator, &denominator
      );
      if (denominator == 1 || numerator == 0) {
        sprintf(&(sbuf[pos]), "%1d,", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d/%1d,", numerator, denominator);
        pos = pos + 2 + intlen(numerator) + intlen(denominator);
      }
    }

    // for outputting the upper-bound of the interval. 
    if (st->u.act.offset->u.interval.status & INTERVAL_RIGHT_UNBOUNDED) {
      sprintf(&(sbuf[pos]), "oo);");
      pos = pos + 4; 
    }
    else {
      get_rationals(st->u.act.offset->u.interval.rbound_exp, PI_STRING, 
        &numerator, &denominator
      );
      if (denominator == 1 || numerator == 0) {
        sprintf(&(sbuf[pos]), "%1d,", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
      else {
        sprintf(&(sbuf[pos]), "%1d/%1d,", numerator, denominator);
        pos = pos + 2 + intlen(numerator) + intlen(denominator); 
      }
      if (st->u.act.offset->u.interval.status & INTERVAL_RIGHT_OPEN) {
        sprintf(&(sbuf[pos]), ");");
        pos = pos+2; 
      }
      else {
        sprintf(&(sbuf[pos]), "];");
        pos = pos+2; 
      }
    }
  }
  else if (st->u.act.offset->var_status & FLAG_QUANTIFIED_SYNC) { 
    pos = rec_string_parse_subformula(st->u.act.offset, pos, NULL); 
    sprintf(&(sbuf[pos]), ";");
    pos++; 
  } 
  else if (st->u.act.offset_numerator[PI_STRING] != 0){
    numerator = st->u.act.offset_numerator[PI_STRING];
    denominator = st->u.act.offset_denominator[PI_STRING];
    if (denominator !=1){
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "-(%1d/%1d);", abs(numerator), denominator);
        pos = pos + 5 + intlen(abs(numerator)) + intlen(denominator); 
      }
      else {
        sprintf(&(sbuf[pos]), "+(%1d/%1d);", numerator, denominator);
        pos = pos + 5 + intlen(numerator) + intlen(denominator);
      }
    }
    else{
      if (numerator < 0) {
        sprintf(&(sbuf[pos]), "%1d;", numerator);
        pos = pos + 1 + intlen(numerator); 
      }
      else if(i>0) {
        sprintf(&(sbuf[pos]), "+%1d;", numerator);
        pos = pos + 2 + intlen(numerator); 
      }
    }
  } 
  return(pos); 
}
/* string_linear_action() */



    
#if RED_DEBUG_REDSTRING_MODE
int	count_string_action = 0; 
#endif 

int	string_action(st, pos)
     struct statement_type	*st; 
     int			pos;
{
  int 	len, i, numerator, denominator;

//  fprintf(RED_OUT, "      "); 
  
  switch (st->op) {
  case ASSIGN_DISCRETE_CONSTANT: 
  case ASSIGN_DISCRETE_POLYNOMIAL: 
    if (   st->u.act.lhs->type == TYPE_DISCRETE
        && st->u.act.lhs->u.atom.var == var_mode
        && st->u.act.lhs->u.atom.exp_base_proc_index->type == TYPE_LOCAL_IDENTIFIER
        ) { 
      if (st->u.act.rhs_exp->type == TYPE_MODE_INDEX) { 
        sprintf(&(sbuf[pos]), "goto %s;", 
          st->u.act.rhs_exp->u.mode_index.mode_name
        ); 
        pos = pos + 5 + strlen(st->u.act.rhs_exp->u.mode_index.mode_name) + 1; 
        break; 
      }
      else if (   st->u.act.rhs_exp->type == TYPE_CONSTANT 
               && st->u.act.rhs_exp->u.value >= 0 
               && st->u.act.rhs_exp->u.value < MODE_COUNT
               ) { 
        struct parse_mode_type	*pm; 
        char			*mname; 
        
        if (MODE) 
          mname = MODE[st->u.act.rhs_exp->u.value].name; 
        else for (pm = declare_mode_list; pm; pm = pm->next_parse_mode) { 
          if (pm->index == st->u.act.rhs_exp->u.value) {
            mname = pm->name; 
            break; 
          } 
        }
        sprintf(&(sbuf[pos]), "goto %s;", mname); 
        pos = pos + 5 + strlen(mname) + 1; 
        break; 
      } 
    } 
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL); 
    sprintf(&(sbuf[pos]), "="); pos++; 
    
    #if RED_DEBUG_REDSTRING_MODE
    fprintf(RED_OUT, "\ncount_string_action=%1d\n", ++count_string_action); 
    fflush(RED_OUT); 
    #endif 
    
    pos = rec_string_parse_subformula(st->u.act.rhs_exp, pos, NULL);
    sprintf(&(sbuf[pos]), ";"); pos++; 
    break;
  case INCREMENT_BY_CONSTANT:
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    if (st->u.act.rhs_exp->type == TYPE_CONSTANT) { 
      sprintf(&(sbuf[pos]), "++%1d;", st->u.act.rhs_exp->u.value);
      pos = pos + 3 + intlen(st->u.act.rhs_exp->u.value);
    }
    else { 
      sprintf(&(sbuf[pos]), "++("); 
      pos = pos + 3; 
      pos = rec_string_parse_subformula(st->u.act.rhs_exp, pos, NULL);
      sprintf(&(sbuf[pos]), ");");
      pos = pos + 2;
    } 
    break;
  case DECREMENT_BY_CONSTANT:
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    if (st->u.act.rhs_exp->type == TYPE_CONSTANT) { 
      sprintf(&(sbuf[pos]), "--%1d;", st->u.act.rhs_exp->u.value);
      pos = pos + 3 + intlen(st->u.act.rhs_exp->u.value);
    }
    else { 
      sprintf(&(sbuf[pos]), "--("); 
      pos = pos + 3; 
      pos = rec_string_parse_subformula(st->u.act.rhs_exp, pos, NULL);
      sprintf(&(sbuf[pos]), ");");
      pos = pos + 2;
    } 
    break;
  case ASSIGN_TRASH: 
    pos = rec_string_parse_subformula(st->u.act.lhs, pos, NULL);
    sprintf(&(sbuf[pos]), "=?;"); 
    pos = pos + 3; 
    break;
  case ASSIGN_CLOCK_CONSTANT: 
  case ASSIGN_CLOCK_MIXED: 
  case ASSIGN_CLOCK_DIFFERENCE: 
  case ASSIGN_CLOCK_DIFFERENCE_MIXED: 
    return(string_linear_action(st, pos));
    break;
  case ASSIGN_HYBRID_EXP:
    return(string_linear_action(st, pos));
    break;
  }
  return(pos); 
}
/* string_action() */




int	rec_string_statement(st, pos) 
	struct statement_type	*st; 
	int			pos; 
{ 
  int	i; 
  
  if (!st) {
    sprintf(&(sbuf[pos]), ";"); 
    return (++pos); 
  }  
  switch (st->op) { 
  case UNCHANGED: 
    sprintf(&(sbuf[pos]), ";"); 
    pos++; 
    break; 
  case ST_IF: 
    sprintf(&(sbuf[pos]), "if ("); pos = pos+4; 
/*
    pos = rec_string_diagram(st->u.branch.red_cond[PI_STRING], pos); 
*/
    pos = rec_string_parse_subformula(st->u.branch.parse_cond_exp, pos, NULL); 
    sprintf(&(sbuf[pos]), ")"); pos++; 
    if (st->u.branch.if_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      sprintf(&(sbuf[pos]), "{"); pos++; 
      pos = rec_string_statement(st->u.branch.if_statement, pos); 
      sprintf(&(sbuf[pos]), "}"); pos++; 
    }
    else 
      pos = rec_string_statement(st->u.branch.if_statement, pos); 
    if (st->st_status & FLAG_STATEMENT_ELSE) { 
      sprintf(&(sbuf[pos]), " else "); 
      pos = pos + 6; 
      if (st->u.branch.else_statement->st_status & FLAG_STATEMENT_COMPOUND) { 
        sprintf(&(sbuf[pos]), "{"); pos++; 
        pos = rec_string_statement(st->u.branch.else_statement, pos); 
        sprintf(&(sbuf[pos]), "}"); pos++; 
      }
      else 
        pos = rec_string_statement(st->u.branch.else_statement, pos); 
    } 
    break; 
  case ST_WHILE: 
    sprintf(&(sbuf[pos]), "while ("); pos = pos + 7; 
/*
    pos = rec_string_diagram(st->u.loop.red_cond[PI_STRING], pos); 
*/
    pos = rec_string_parse_subformula(st->u.loop.parse_cond_exp, pos, NULL); 
    sprintf(&(sbuf[pos]), ")"); pos++; 
    if (st->u.loop.statement->st_status & FLAG_STATEMENT_COMPOUND) { 
      sprintf(&(sbuf[pos]), "{"); pos++; 
      pos = rec_string_statement(st->u.loop.statement, pos); 
      sprintf(&(sbuf[pos]), "}"); pos++; 
    }
    else 
      pos = rec_string_statement(st->u.loop.statement, pos); 
    break; 
  case ST_SEQ: 
    for (i = 0; i < st->u.seq.count; i++) { 
      pos = rec_string_statement(st->u.seq.statement[i], pos); 
    } 
    break; 
  case ST_CALL: 
    sprintf(&(sbuf[pos]), "call %s to %s;", 
      MODE[st->u.call.call_mode_index].name, 
      MODE[st->u.call.ret_mode_index].name
    ); 
    pos = pos + 10 
    + strlen(MODE[st->u.call.call_mode_index].name) 
    + strlen(MODE[st->u.call.ret_mode_index].name); 
    break; 
  case ST_RETURN: 
    sprintf(&(sbuf[pos]), "return;"); 
    pos = pos + 7; 
    break; 
    
  case ST_CPLUG: 
    sprintf(&(sbuf[pos]), "Cplug %1d %1d;", 
      st->u.cplug.cmod_index, st->u.cplug.cproc_index
    ); 
    pos = pos + 8 
    + intlen(st->u.cplug.cmod_index) 
    + intlen(st->u.cplug.cproc_index); 
    break; 
    
  default: 
    pos = string_action(st, pos); 
    break; 	
  } 
  return(pos); 
}
  /* rec_string_statement() */ 







char	*string_statement_instantiate(st, pi) 
	struct statement_type	*st; 
	int			pi; 
{
  int	len; 
  
  PI_STRING = pi; 
  PI_LENGTH = intlen(pi); 
  len = rec_string_statement(st, 0); 
  
  if (len >= size_sbuf) { 
    fprintf(RED_OUT, "Uh-Oh, the string is longer than the processing buffer.\n"); 
    exit(0); 	
  } 
  sbuf[len] = '\0'; 
  tmp_buf_statement = malloc(len+1); 
  sprintf(tmp_buf_statement, "%s", sbuf); 
  
  return(tmp_buf_statement); 
}
  /* string_statement_instantiate() */ 
  

int count_string_xtion = 0; 

char	*string_xtion(int xi, int pi) {
  char	*stream, *sc, *tr, *st, *ans; 
  
  stream = string_stream_operations(xi); 
  
  sc = string_sync_list(XTION[xi].parse_xtion->sync_list); 
/*
  fprintf(RED_OUT, 
    "\n************************\n=(%1d, sx %1d)= sx sync: %s\n", 
    ++count_string_xtion, xi, sc
  ); 
*/
  if (red_path_threshold(XTION[xi].red_trigger[pi], 6)) 
    tr = string_parse_subformula(XTION[xi].parse_xtion->trigger_exp, pi, 0); 
  else 
    tr = string_diagram(XTION[xi].red_trigger[pi]); 
//  fprintf(RED_OUT, "=(sx %1d)= sx trigger: %s\n", xi, tr); 
  st = string_statement_instantiate(XTION[xi].statement, pi); 
//  fprintf(RED_OUT, "=(sx %1d)= sx stmt: %s\n\n", xi, st); 
  
  ans = malloc(
    5 + strlen(stream) 
  + 1 + strlen(sc) 
  + 2 + strlen(tr) 
  + 6 + strlen(st) 
  + 1/*for \0*/
  ); 
  sprintf(ans, "when%s %s (%s) may %s", stream, sc, tr, st);  
  free(sc); 
  free(tr); 
  free(st); 
  
  return(ans); 
}
  /* string_xtion() */  
  
  
  

char    *string_sync_xtion_actions(sxi) 
	int 	sxi; 
{ 
  char	**ps, *s; 
  int	ipi, len; 

  check_sxi(sxi, "red_sync_xtion_action_string"); 
  ps = (char **) malloc(SYNC_XTION[sxi].party_count * sizeof(char *)); 
  len = 0; 
  for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) { 
    ps[ipi] = string_statement_instantiate(
      SYNC_XTION[sxi].party[ipi].statement, 
      SYNC_XTION[sxi].party[ipi].proc
    ); 
    len = len + strlen(ps[ipi]); 
  } 
  s = malloc(len); 
  len = 0; 
  for (ipi = 0; ipi < SYNC_XTION[sxi].party_count; ipi++) { 
    sprintf(&(s[len]), "%s", ps[ipi]); 
    len = len + strlen(ps[ipi]); 
    free(ps[ipi]); 
  } 
  free(ps); 
  
  return(s); 
}
  /* string_sync_xtion_actions() */  



char    *string_sync_xtion(sxi) 
	int 	sxi; 
{
  char	*ss, *ts, *ans; 
  int	sl, tl; 
  
  check_sxi(sxi, "red_sync_xtion_string"); 
  ss = string_sync_xtion_actions(sxi); 
  ts = string_diagram(SYNC_XTION[sxi].red_trigger); 
  sl = strlen(ss); 
  tl = strlen(ts); 
  ans = malloc(sl+tl+2); 
  sprintf(ans, "%s %s", ts, ss); 
  free(ss); 
  free(ts); 
  
  return(ans); 
}
  /* string_sync_xtion() */ 
  
  



