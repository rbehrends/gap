/****************************************************************************
**
*W  listfunc.c                  GAP source                   Martin Schönert
**
*H  @(#)$Id: listfunc.c,v 4.67 2010/09/17 05:09:23 sal Exp $
**
*Y  Copyright (C)  1996,  Lehrstuhl D für Mathematik,  RWTH Aachen,  Germany
*Y  (C) 1998 School Math and Comp. Sci., University of St Andrews, Scotland
*Y  Copyright (C) 2002 The GAP Group
**
**  This file contains the functions for generic lists.
*/
#include        "system.h"              /* Ints, UInts                     */

const char * Revision_listfunc_c =
   "@(#)$Id: listfunc.c,v 4.67 2010/09/17 05:09:23 sal Exp $";


#include        "gasman.h"              /* garbage collector               */
#include        "objects.h"             /* objects                         */
#include        "scanner.h"             /* scanner                         */

#include        "gap.h"                 /* error handling, initialisation  */

#include        "gvars.h"               /* global variables                */

#include        "calls.h"               /* generic call mechanism          */
#include        "opers.h"               /* generic operations              */

#include        "ariths.h"              /* basic arithmetic                */

#include        "records.h"             /* generic records                 */
#include        "precord.h"             /* plain records                   */

#include        "lists.h"               /* generic lists                   */
#include        "string.h"              /* strings                         */

#include        "bool.h"                /* booleans                        */

#include        "permutat.h"            /* permutations                    */

#define INCLUDE_DECLARATION_PART
#include        "listfunc.h"            /* functions for generic lists     */
#undef  INCLUDE_DECLARATION_PART

#include        "plist.h"               /* plain lists                     */
#include        "set.h"                 /* plain sets                      */
#include        "range.h"               /* ranges                          */
#include	"code.h"
#include	"thread.h"
#include	"tls.h"

#include		<string.h>
#include                <stdlib.h> 

/****************************************************************************
**

*F  AddList(<list>,<obj>) . . . . . . . .  add an object to the end of a list
**
**  'AddList' adds the object <obj> to the end  of  the  list  <list>,  i.e.,
**  it is equivalent to the assignment '<list>[ Length(<list>)+1 ] := <obj>'.
**  The  list is  automatically extended to   make room for  the new element.
**  'AddList' returns nothing, it is called only for its sideeffect.
*/
void            AddList (
    Obj                 list,
    Obj                 obj )
{
    Int                 pos;            /* position to assign to           */
    pos = LEN_LIST( list ) + 1;
    ASS_LIST( list, pos, obj );
}

extern Obj FuncADD_LIST(
    Obj                 self,
    Obj                 list,
    Obj                 obj );

void            AddPlist (
    Obj                 list,
    Obj                 obj )
{
    Int                 pos;            /* position to assign to           */

    if ( ! IS_MUTABLE_PLIST(list) ) {
        list = ErrorReturnObj(
                "Lists Assignment: <list> must be a mutable list",
                0L, 0L,
                "you may replace <list> via 'return <list>;'" );
        FuncADD_LIST( 0, list, obj );
        return;
    }
    /* in order to be optimistic when building list call assignment        */
    pos = LEN_PLIST( list ) + 1;
    if ( pos == 1 ) {
        AssPlistEmpty( list, pos, obj );
    }
    else {
      ASS_LIST( list, pos, obj);
      /*  The code below is commented out and replaced by the line above, so
	  as, at the cost of one extra dispatch, to take advantage of the
	  special code in AssPlist<things> which maintain as much information
	  about denseness homogeneity, etc as possible */
      /*        RetypeBag( list, T_PLIST );
		GROW_PLIST( list, pos );
		SET_LEN_PLIST( list, pos );
		SET_ELM_PLIST( list, pos, obj );
		CHANGED_BAG( list ); */
    }
}

Obj AddListOper;

Obj FuncADD_LIST (
    Obj                 self,
    Obj                 list,
    Obj                 obj )
{
    /* dispatch                                                            */
    if ( T_PLIST          <= TNUM_OBJ( list )
      && TNUM_OBJ( list ) <= T_PLIST_CYC_SSORT ) {
        AddPlist( list, obj );
    }
    else if ( TNUM_OBJ( list ) < FIRST_EXTERNAL_TNUM ) {
        AddList( list, obj );
    }
    else {
        DoOperation2Args( self, list, obj );
    }

    /* return nothing                                                      */
    return (Obj)0;
}


/****************************************************************************
**
*F  FuncAPPEND_LIST_INTR(<list1>,<list2>)  . . . . . append elements to a list
**
**  'FuncAPPEND_LIST_INTR' implements the function 'AppendList'.
**
**  'AppendList(<list1>,<list2>)'
**
**  'AppendList' adds (see "Add") the elements of the list <list2> to the end
**  of the list <list1>. It is allowed that <list2> contains empty positions,
**  in which case the corresponding positions  will be left empty in <list1>.
**  'AppendList' returns nothing, it is called only for its side effect.
*/
Obj             FuncAPPEND_LIST_INTR (
    Obj                 self,
    Obj                 list1,
    Obj                 list2 )
{
    UInt                len1;           /* length of the first list        */
    UInt                len2;           /* length of the second list       */
    Obj *               ptr1;           /* pointer into the first list     */
    Obj *               ptr2;           /* pointer into the second list    */
    Obj                 elm;            /* one element of the second list  */
    Int                i;              /* loop variable                   */
    Obj e1,e2;

    /* check the mutability of the first argument */
    while ( !IS_MUTABLE_OBJ( list1) )
      list1 = ErrorReturnObj (
		"Append: <list1> must be a mutable list",
		0L, 0L,
		"you can replace <list1> via 'return <list1>;'");
    

    /* handle the case of strings now */
    if ( IS_STRING_REP(list1) && IS_STRING_REP(list2))
      {
	len1 = GET_LEN_STRING(list1);
	len2 = GET_LEN_STRING(list2);
	GROW_STRING(list1, len1 + len2);
	SET_LEN_STRING(list1, len1 + len2);
	memcpy( (void *)(CHARS_STRING(list1) + len1), 
		(void *)CHARS_STRING(list2), len2 + 1);
        /* ensure trailing zero */
        *(CHARS_STRING(list1) + len1 + len2) = 0;    
	return (Obj) 0;
      }
    
    /* check the type of the second argument                               */
    if ( !IS_PLIST(list2)) {
        while ( ! IS_SMALL_LIST( list2 ) ) {
            list2 = ErrorReturnObj(
                "AppendList: <list2> must be a small list (not a %s)",
                (Int)TNAM_OBJ(list2), 0L,
                "you can replace <list2> via 'return <list2>;'"  );
        }
        len2 = LEN_LIST( list2 );
    }
    else {
        len2 = LEN_PLIST( list2 );
    }

    if (len2 == 0)
      return (Obj) 0;

    /* check the type of the first argument                                */
    if ( !IS_PLIST(list1)) {
        while ( ! IS_SMALL_LIST( list1 ) ) {
            list1 = ErrorReturnObj(
                "AppendList: <list1> must be a small list (not a %s)",
                (Int)TNAM_OBJ(list1), 0L,
                "you can replace <list1> via 'return <list1>;'" );
        }
        PLAIN_LIST( list1 );
        RetypeBag( list1, T_PLIST );
    }
    len1 = LEN_PLIST( list1 );

    
    /* if the list has no room at the end, enlarge it                      */
    GROW_PLIST( list1, len1+len2 );
    SET_LEN_PLIST( list1, len1+len2 );

    /* add the elements                                                    */
    if ( IS_PLIST(list2) ) {
      memcpy((void *)(ADDR_OBJ(list1) + len1+1),
	     (void *)(ADDR_OBJ(list2)+1),
	     sizeof(Obj)*len2);
        CHANGED_BAG( list1 );
	/* Sort out the type */

	switch (TNUM_OBJ(list1)) {
	case T_PLIST:
	case T_PLIST_NDENSE:
	  break;
	case T_PLIST_DENSE_NHOM_SSORT:
	case T_PLIST_DENSE_NHOM_NSORT:
	  RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  /* fall through into the next case deliberately */
	case T_PLIST_DENSE:
	case T_PLIST_DENSE_NHOM:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    {
	      if (IS_MUTABLE_PLIST(list2))
		RetypeBag(list1, TNUM_OBJ(list2));
	      else
		RetypeBag(list2, TNUM_OBJ(list2) - IMMUTABLE);
	    }
	  break;
	case T_PLIST_EMPTY:
	  if (IS_MUTABLE_PLIST(list2))
	    RetypeBag(list1, TNUM_OBJ(list2));
	  else
	    RetypeBag(list2, TNUM_OBJ(list2) - IMMUTABLE);
	  break;
	case T_PLIST_HOM_NSORT:
	case T_PLIST_HOM_SSORT:
	  RetypeBag(list1, T_PLIST_HOM);
	  /* fall through */
	case T_PLIST_HOM:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    RetypeBag(list1, T_PLIST);
	  else if (TNUM_OBJ(list2) < T_PLIST_HOM)
	    RetypeBag(list1, T_PLIST_DENSE);
	  else {
	    if (FAMILY_OBJ(ELM_PLIST(list1,1)) != 
		FAMILY_OBJ(ELM_PLIST(list2,1)))
	      RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  }
	  break;

	case T_PLIST_TAB_NSORT:
	case T_PLIST_TAB_SSORT:
	  RetypeBag(list1, T_PLIST_TAB);
	  /* fall through */
	case T_PLIST_TAB:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    RetypeBag(list1, T_PLIST);
	  else if (TNUM_OBJ(list2) < T_PLIST_HOM)
	    RetypeBag(list1, T_PLIST_DENSE);
	  else if (FAMILY_OBJ(ELM_PLIST(list1,1)) != 
		   FAMILY_OBJ(ELM_PLIST(list2,1)))
	    RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  break;

	case T_PLIST_TAB_RECT_NSORT:
	case T_PLIST_TAB_RECT_SSORT:
	  RetypeBag(list1, T_PLIST_TAB_RECT);
	  /* fall through */
	case T_PLIST_TAB_RECT:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    RetypeBag(list1, T_PLIST);
	  else if (TNUM_OBJ(list2) < T_PLIST_HOM)
	    RetypeBag(list1, T_PLIST_DENSE);
	  else { 
	    e1 = ELM_PLIST(list1,1);
	    e2 = ELM_PLIST(list2,1);
	    if (FAMILY_OBJ(e1) != FAMILY_OBJ(e2))
	      RetypeBag(list1, T_PLIST_DENSE_NHOM);
	    else if (LENGTH(e1) != LENGTH(e2))
	      RetypeBag(list1, T_PLIST_TAB);
	  }
	  break;

	case T_PLIST_CYC_NSORT:
	case T_PLIST_CYC_SSORT:
	  RetypeBag(list1, T_PLIST_CYC);
	  /* fall through */
	case T_PLIST_CYC:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    RetypeBag(list1, T_PLIST);
	  else if (TNUM_OBJ(list2) < T_PLIST_HOM)
	    RetypeBag(list1, T_PLIST_DENSE);
	  else if (TNUM_OBJ(ELM_PLIST(list2,1)) > T_CYC)
	      RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  break;
	  
	case T_PLIST_FFE:
	  if (TNUM_OBJ(list2) < T_PLIST_DENSE)
	    RetypeBag(list1, T_PLIST);
	  else if (TNUM_OBJ(list2) < T_PLIST_HOM)
	    RetypeBag(list1, T_PLIST_DENSE);
	  else if (TNUM_OBJ(ELM_PLIST(list2,1)) != T_FFE)
	    RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  else if (CharFFE(ELM_PLIST(list2,1)) != CharFFE(ELM_PLIST(list1,1)))
	    RetypeBag(list1, T_PLIST_DENSE_NHOM);
	  else if (DegreeFFE(ELM_PLIST(list2,1)) != DegreeFFE(ELM_PLIST(list1,1)))
	    RetypeBag(list1, T_PLIST_HOM);
	  break;
	}

    }
    else {
        for ( i = 1; i <= len2; i++ ) {
            elm = ELMV0_LIST( list2, i );
            SET_ELM_PLIST( list1, i+len1, elm );
            CHANGED_BAG( list1 );
	    
        }
    }

    /* return void                                                         */
    return (Obj)0;
}

Obj             AppendListOper;

Obj             FuncAPPEND_LIST (
    Obj                 self,
    Obj                 list,
    Obj                 obj )
{
    /* dispatch                                                            */
    if ( TNUM_OBJ( list ) < FIRST_EXTERNAL_TNUM ) {
        FuncAPPEND_LIST_INTR( 0, list, obj );
    }
    else {
        DoOperation2Args( self, list, obj );
    }

    /* return nothing                                                      */
    return (Obj)0;
}

/****************************************************************************
**
*F  POSITION_SORTED_LIST(<list>,<obj>)  . . . . find an object in a sorted list
*F  PositionSortedDensePlist(<list>,<obj>)  . find an object in a sorted list
**
**  'POSITION_SORTED_LIST' returns the position of the  object <obj>, which may
**  be an object of any type, with respect to the sorted list <list>.
**
**  'POSITION_SORTED_LIST' returns  <pos>  such that  '<list>[<pos>-1] < <obj>'
**  and '<obj> <= <list>[<pos>]'.  That means if <obj> appears once in <list>
**  its position is returned.  If <obj> appears several  times in <list>, the
**  position of the first occurrence is returned.  If <obj> is not an element
**  of <list>, the index where <obj> must be inserted to keep the list sorted
**  is returned.
*/
UInt            POSITION_SORTED_LIST (
    Obj                 list,
    Obj                 obj )
{
    UInt                l;              /* low                             */
    UInt                h;              /* high                            */
    UInt                m;              /* mid                             */
    Obj                 v;              /* one element of the list         */

    /* perform the binary search to find the position                      */
    l = 0;  h = LEN_LIST( list ) + 1;
    while ( l+1 < h ) {                 /* list[l] < obj && obj <= list[h] */
        m = (l + h) / 2;                /* l < m < h                       */
        v = ELMV_LIST( list, m );
        if ( LT( v, obj ) ) { l = m; }
        else                { h = m; }
    }

    /* return the position                                                 */
    return h;
}

UInt            PositionSortedDensePlist (
    Obj                 list,
    Obj                 obj )
{
    UInt                l;              /* low                             */
    UInt                h;              /* high                            */
    UInt                m;              /* mid                             */
    Obj                 v;              /* one element of the list         */

    /* perform the binary search to find the position                      */
    l = 0;  h = LEN_PLIST( list ) + 1;
    while ( l+1 < h ) {                 /* list[l] < obj && obj <= list[h] */
        m = (l + h) / 2;                /* l < m < h                       */
        v = ELM_PLIST( list, m );
        if ( LT( v, obj ) ) { l = m; }
        else                { h = m; }
    }

    /* return the position                                                 */
    return h;
}

Obj             FuncPOSITION_SORTED_LIST (
    Obj                 self,
    Obj                 list,
    Obj                 obj )
{
    UInt                h;              /* position, result                */

    /* check the first argument                                            */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "POSITION_SORTED_LIST: <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE  <= TNUM_OBJ(list)
      && TNUM_OBJ(list) <= T_PLIST_CYC_SSORT ) {
        h = PositionSortedDensePlist( list, obj );
    }
    else {
        h = POSITION_SORTED_LIST( list, obj );
    }

    /* return the result                                                   */
    return INTOBJ_INT( h );
}


/****************************************************************************
**
*F  POSITION_SORTED_LISTComp(<list>,<obj>,<func>)  . . find an object in a list
*F  PositionSortedDensePlistComp(<list>,<obj>,<func>)find an object in a list
**
**  'POSITION_SORTED_LISTComp' returns the position of the  object <obj>, which
**  may be an object of any type, with respect to the list <list>,  which  is
**  sorted with respect to the comparison function <func>.
**
**  'POSITION_SORTED_LISTComp' returns <pos> such that '<list>[<pos>-1] < <obj>'
**  and '<obj> <= <list>[<pos>]'.  That means if <obj> appears once in <list>
**  its position is returned.  If <obj> appears several  times in <list>, the
**  position of the first occurrence is returned.  If <obj> is not an element
**  of <list>, the index where <obj> must be inserted to keep the list sorted
**  is returned.
*/
UInt            POSITION_SORTED_LISTComp (
    Obj                 list,
    Obj                 obj,
    Obj                 func )
{
    UInt                l;              /* low                             */
    UInt                h;              /* high                            */
    UInt                m;              /* mid                             */
    Obj                 v;              /* one element of the list         */

    /* perform the binary search to find the position                      */
    l = 0;  h = LEN_LIST( list ) + 1;
    while ( l+1 < h ) {                 /* list[l] < obj && obj <= list[h] */
        m = (l + h) / 2;                /* l < m < h                       */
        v = ELMV_LIST( list, m );
        if ( CALL_2ARGS( func, v, obj ) == True ) { l = m; }
        else                                      { h = m; }
    }

    /* return the position                                                 */
    return h;
}

UInt            PositionSortedDensePlistComp (
    Obj                 list,
    Obj                 obj,
    Obj                 func )
{
    UInt                l;              /* low                             */
    UInt                h;              /* high                            */
    UInt                m;              /* mid                             */
    Obj                 v;              /* one element of the list         */

    /* perform the binary search to find the position                      */
    l = 0;  h = LEN_PLIST( list ) + 1;
    while ( l+1 < h ) {                 /* list[l] < obj && obj <= list[h] */
        m = (l + h) / 2;                /* l < m < h                       */
        v = ELM_PLIST( list, m );
        if ( CALL_2ARGS( func, v, obj ) == True ) { l = m; }
        else                                      { h = m; }
    }

    /* return the position                                                 */
    return h;
}

Obj             FuncPOSITION_SORTED_COMP (
    Obj                 self,
    Obj                 list,
    Obj                 obj,
    Obj                 func )
{
    UInt                h;              /* position, result                */

    /* check the first argument                                            */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "POSITION_SORTED_LISTComp: <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }

    /* check the third argument                                            */
    while ( TNUM_OBJ( func ) != T_FUNCTION ) {
        func = ErrorReturnObj(
            "POSITION_SORTED_LISTComp: <func> must be a function (not a %s)",
            (Int)TNAM_OBJ(func), 0L,
            "you can replace <func> via 'return <func>;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE  <= TNUM_OBJ(list)
      && TNUM_OBJ(list) <= T_PLIST_CYC_SSORT ) {
        h = PositionSortedDensePlistComp( list, obj, func );
    }
    else {
        h = POSITION_SORTED_LISTComp( list, obj, func );
    }

    /* return the result                                                   */
    return INTOBJ_INT( h );
}


Obj             FuncPOSITION_FIRST_COMPONENT_SORTED (
    Obj                 self,
    Obj                 list,
    Obj                 obj)
{
  UInt top, bottom,middle;
  Obj x;
  Obj l;
  bottom = 1;
  top = LEN_PLIST(list);
  while (bottom <= top) {
    middle = (top + bottom)/2;
    l = ELM_PLIST(list,middle);
    if (!IS_PLIST(l))
      return TRY_NEXT_METHOD;
    x = ELM_PLIST(l,1);
    if (LT(x,obj)) {
      bottom = middle+1;
    } else if (LT(obj,x)) {
      top = middle -1;
    } else {
      return INTOBJ_INT(middle);
    }
  }
  return INTOBJ_INT(bottom);
}
      



/****************************************************************************
**
*F  SORT_LIST( <list> )  . . . . . . . . . . . . . . . . . . . .  sort a list
*F  SortDensePlist( <list> ) . . . . . . . . . . . . . . . . . .  sort a list
**
**  'SORT_LIST' sorts the list <list> in increasing  order.
**
**  'Sort' uses Shell's diminishing increment sort, which extends bubblesort.
**  The bubble sort works by  running  through  the  list  again  and  again,
**  each time exchanging pairs of adjacent elements which are out  of  order.
**  Thus large elements ``bubble'' to the top, hence the name of the  method.
**  However elements need many moves to come close to their  final  position.
**  In shellsort the first passes do not compare element j with its  neighbor
**  but with the element j+h, where h is larger than one.  Thus elements that
**  are not at their final position make large moves towards the destination.
**  This increment h is diminished, until during the last  pass  it  is  one.
**  A good sequence of incremements is given by Knuth:  (3^k-1)/2,... 13,4,1.
**  For this sequence shellsort uses on average  approximatly  N^1.25  moves.
**
**  Shellsort is the method of choice to  sort  lists  for  various  reasons:
**  Shellsort is quite easy to get right, much easier than,  say,  quicksort.
**  It runs as fast as quicksort for lists with  less  than  ~5000  elements.
**  It handles both  almost  sorted  and  reverse  sorted  lists  very  good.
**  It works well  in  the  presence  of  duplicate  elements  in  the  list.
**  Says Sedgewick: ``In short, if you have a sorting problem,  use the above
**  program, then determine whether the extra effort required to  replace  it
**  with a sophisticated method will be worthwile.''
**
**  Donald Knuth, The Art of Computer Programming, Vol.3, AddWes 1973, 84-95
**  Donald Shell, CACM 2, July 1959, 30-32
**  Robert Sedgewick, Algorithms 2nd ed., AddWes 1988, 107-123
*/

static void BubbleDown(Obj list, UInt pos, UInt len)
{
  UInt lcpos, rcpos;
  Obj lco, rco,x;

  lcpos = 2*pos;
  rcpos = 2*pos+1;
  if (lcpos > len)
    return;
  lco = ELM_PLIST(list, lcpos);
  x = ELM_PLIST(list,pos);
  if (rcpos > len)
    {
      if (LT(x,lco))
	{
	  SET_ELM_PLIST(list, pos, lco);
	  SET_ELM_PLIST(list, lcpos, x);
	}
      return;
    }
  rco = ELM_PLIST(list, rcpos);
  if (LT(lco, rco)){
    if (LT(x,rco)) {
      SET_ELM_PLIST(list, pos, rco);
      SET_ELM_PLIST(list, rcpos, x);
      BubbleDown(list, rcpos, len);
    }
  }  else {
    if (LT(x,lco)) {
      SET_ELM_PLIST(list, pos, lco);
      SET_ELM_PLIST(list, lcpos, x);
      BubbleDown(list, lcpos, len);
    }
  }
  return;
}

Obj HEAP_SORT_PLIST ( Obj self, Obj list )
{
  UInt len = LEN_LIST(list);
  UInt i;
  for (i = (len/2); i > 0 ; i--)
    BubbleDown(list, i, len);
  for (i = len; i > 0; i--)
    {
      Obj x = ELM_PLIST(list, i);
      Obj y = ELM_PLIST(list, 1);
      SET_ELM_PLIST(list, i, y);
      SET_ELM_PLIST(list, 1, x);
      BubbleDown(list, 1, i-1);
    }
  return (Obj) 0;
}
  

void SORT_LIST (
    Obj                 list )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v, w;           /* two element of the list         */
    UInt                i, k;           /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_LIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v = ELMV_LIST( list, i );
            k = i;
            w = ELMV_LIST( list, k-h );
            while ( h < k && LT( v, w ) ) {
                ASS_LIST( list, k, w );
                k -= h;
                if ( h < k )  w = ELMV_LIST( list, k-h );
            }
            ASS_LIST( list, k, v );
        }
        h = h / 3;
    }
    if (FIRST_PLIST_TNUM <= TNUM_OBJ(list) &&
	TNUM_OBJ(list) <= LAST_PLIST_TNUM)
      RESET_FILT_LIST(list, FN_IS_NSORT);
}

void SortDensePlist (
    Obj                 list )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v, w;           /* two element of the list         */
    UInt                i, k;           /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_PLIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v = ELM_PLIST( list, i );
            k = i;
            w = ELM_PLIST( list, k-h );
            while ( h < k && LT( v, w ) ) {
                SET_ELM_PLIST( list, k, w );
                k -= h;
                if ( h < k )  w = ELM_PLIST( list, k-h );
            }
            SET_ELM_PLIST( list, k, v );
        }
        h = h / 3;
    }
    RESET_FILT_LIST(list, FN_IS_NSORT);
}


/****************************************************************************
**
*F  SORT_LISTComp(<list>,<func>)  . . . . . . . . . . . . . . . . sort a list
*F  SortDensePlistComp(<list>,<func>) . . . . . . . . . . . . . . sort a list
**
**  'SORT_LISTComp' sorts the list <list> in increasing order, with respect to
**  comparison function <func>.
*/
void SORT_LISTComp (
    Obj                 list,
    Obj                 func )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v, w;           /* two element of the list         */
    UInt                i, k;           /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_LIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v = ELMV_LIST( list, i );
            k = i;
            w = ELMV_LIST( list, k-h );
            while ( h < k && CALL_2ARGS( func, v, w ) == True ) {
                ASS_LIST( list, k, w );
                k -= h;
                if ( h < k )  w = ELMV_LIST( list, k-h );
            }
            ASS_LIST( list, k, v );
        }
        h = h / 3;
    }
    /* list is not necc. sorted wrt. \< (any longer) */
    RESET_FILT_LIST(list, FN_IS_SSORT);
    RESET_FILT_LIST(list, FN_IS_NSORT);
}






void SortDensePlistComp (
    Obj                 list,
    Obj                 func )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v, w;           /* two element of the list         */
    UInt                i, k;           /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_PLIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v = ELM_PLIST( list, i );
            k = i;
            w = ELM_PLIST( list, k-h );
            while ( h < k && CALL_2ARGS( func, v, w ) == True ) {
                SET_ELM_PLIST( list, k, w );
                k -= h;
                if ( h < k )  w = ELM_PLIST( list, k-h );
            }
            SET_ELM_PLIST( list, k, v );
        }
        h = h / 3;
    }
    /* list is not necc. sorted wrt. \< (any longer) */
    RESET_FILT_LIST(list, FN_IS_SSORT);
    RESET_FILT_LIST(list, FN_IS_NSORT);
}

/****************************************************************************
**
*F  SORT_PARA_LIST( <list> )  . . . . . . . . . . .  sort a lists with shadow
*F  SortParaDensePlistPara( <list> )  . . . . . . .  sort a lists with shadow
*F  SORT_PARA_LISTComp(<list>,<func>) . . . . . . .  sort a lists with shadow
*F  SortParaDensePlistComp(<list>,<func>) . . . . .  sort a lists with shadow
**
**  The following suite of functions mirrors the sort functions above.  They
**  sort the first list given and perform the same operations on the second
**  list, the shadow list.  All functions assume that shadow list has (at
**  least) the length of the first list. 
**
**  The code here is a duplication of the code above with the operations on
**  the second list added in.
*/

void SORT_PARA_LIST (
    Obj                 list,
    Obj               shadow )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v,  w;          /* two element of the list         */
    Obj                 vs, ws;         /* two element of the shadow list  */
    UInt                i,  k;          /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_LIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v  = ELMV_LIST( list,   i ); 
            vs = ELMV_LIST( shadow, i );
            k  = i;
            w  = ELMV_LIST( list,   k-h );
            ws = ELMV_LIST( shadow, k-h );
            while ( h < k && LT( v, w ) ) {
              ASS_LIST( list,   k, w  );
              ASS_LIST( shadow, k, ws );
                k -= h;
                if ( h < k ) {
                    w  = ELMV_LIST( list,   k-h );
                    ws = ELMV_LIST( shadow, k-h );
                }
            }
            ASS_LIST( list,   k, v  ); 
            ASS_LIST( shadow, k, vs );
        }
        h = h / 3;
    }
    /* if list was ssorted, then it still will be,
       but, we don't know anything else any more */
    RESET_FILT_LIST(list, FN_IS_NSORT);
    RESET_FILT_LIST(shadow, FN_IS_SSORT);
    RESET_FILT_LIST(shadow, FN_IS_NSORT);
}

void SortParaDensePlist (
    Obj                 list,
    Obj               shadow )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v,  w;          /* two element of the list         */
    Obj                 vs, ws;         /* two element of the shadow list  */
    UInt                i,  k;          /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_PLIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v  = ELM_PLIST( list,   i );
            vs = ELM_PLIST( shadow, i );
            k  = i;
            w  = ELM_PLIST( list,   k-h );
            ws = ELM_PLIST( shadow, k-h );
            while ( h < k && LT( v, w ) ) {
                SET_ELM_PLIST( list,   k, w  );
                SET_ELM_PLIST( shadow, k, ws );
                k -= h;
                if ( h < k ) {
                    w  = ELM_PLIST( list,   k-h );
                    ws = ELM_PLIST( shadow, k-h );
                }
            }
            SET_ELM_PLIST( list,   k, v  );
            SET_ELM_PLIST( shadow, k, vs );
        }
        h = h / 3;
    }

    /* if list was ssorted, then it still will be,
       but, we don't know anything else any more */
    RESET_FILT_LIST(list, FN_IS_NSORT);
    RESET_FILT_LIST(shadow, FN_IS_SSORT);
    RESET_FILT_LIST(shadow, FN_IS_NSORT);
}

void SORT_PARA_LISTComp (
    Obj                 list,
    Obj               shadow,
    Obj                 func )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v,  w;          /* two element of the list         */
    Obj                 vs, ws;         /* two element of the shadow list  */
    UInt                i,  k;          /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_LIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v  = ELMV_LIST( list,   i );    
            vs = ELMV_LIST( shadow, i );
            k  = i;
            w  = ELMV_LIST( list,   k-h );
            ws = ELMV_LIST( shadow, k-h );
            while ( h < k && CALL_2ARGS( func, v, w ) == True ) {
                ASS_LIST( list,   k, w );
                ASS_LIST( shadow, k, ws );
                k -= h;
                if ( h < k ) {
                    w  = ELMV_LIST( list,   k-h );
                    ws = ELMV_LIST( shadow, k-h );
                }
            }
            ASS_LIST( list,   k, v  );
            ASS_LIST( shadow, k, vs );
        }
        h = h / 3;
    }
    /* list is not necc. sorted wrt. \< (any longer) */
    RESET_FILT_LIST(list, FN_IS_SSORT);
    RESET_FILT_LIST(list, FN_IS_NSORT);
    RESET_FILT_LIST(shadow, FN_IS_NSORT);
    RESET_FILT_LIST(shadow, FN_IS_SSORT);
}

void SortParaDensePlistComp (
    Obj                 list,
    Obj               shadow,
    Obj                 func )
{
    UInt                len;            /* length of the list              */
    UInt                h;              /* gap width in the shellsort      */
    Obj                 v,  w;          /* two element of the list         */
    Obj                 vs, ws;         /* two element of the shadow list  */
    UInt                i,  k;          /* loop variables                  */

    /* sort the list with a shellsort                                      */
    len = LEN_PLIST( list );
    h = 1;
    while ( 9*h + 4 < len ) { h = 3*h + 1; }
    while ( 0 < h ) {
        for ( i = h+1; i <= len; i++ ) {
            v  = ELM_PLIST( list,   i );
            vs = ELM_PLIST( shadow, i );
            k  = i;
            w  = ELM_PLIST( list,   k-h );
            ws = ELM_PLIST( shadow, k-h );
            while ( h < k && CALL_2ARGS( func, v, w ) == True ) {
                SET_ELM_PLIST( list,   k, w  );
                SET_ELM_PLIST( shadow, k, ws );
                k -= h;
                if ( h < k ) {
                    w  = ELM_PLIST( list,   k-h );  
                    ws = ELM_PLIST( shadow, k-h );
                }
            }
            SET_ELM_PLIST( list,   k, v  );
            SET_ELM_PLIST( shadow, k, vs );
        }
        h = h / 3;
    }
    RESET_FILT_LIST(list, FN_IS_NSORT);
    RESET_FILT_LIST(list, FN_IS_SSORT);
    RESET_FILT_LIST(shadow, FN_IS_NSORT);
    RESET_FILT_LIST(shadow, FN_IS_SSORT);
}



/****************************************************************************
**
*F  RemoveDupsDensePlist(<list>)  . . . . remove duplicates from a plain list
**
**  'RemoveDupsDensePlist' removes duplicate elements from the dense
**  plain list <list>.  <list> must be sorted.  'RemoveDupsDensePlist'
**  returns 0 if <list> contains mutable elements, 1 if not and 2 if
**  the list contains immutable elements all lying in the same family.
*/
UInt            RemoveDupsDensePlist (
    Obj                 list )
{
    UInt                mutable;        /* the elements are mutable        */
    UInt                homog;          /* the elements all lie in the same family */
    Int                 len;            /* length of the list              */
    Obj                 v, w;           /* two elements of the list        */
    UInt                l, i;           /* loop variables                  */
    Obj                 fam;

    /* get the length, nothing to be done for empty lists                  */
    len = LEN_PLIST( list );
    if ( len == 0 ) { return 0; }

    /* select the first element as the first representative                */
    l = 1;
    v = ELM_PLIST( list, l );
    mutable = IS_MUTABLE_OBJ(v);
    homog = 1;
    fam = FAMILY_OBJ(v);

    /* loop over the other elements, compare them with the current rep.    */
    for ( i = 2; i <= len; i++ ) {
        w = ELM_PLIST( list, i );
	mutable = (mutable || IS_MUTABLE_OBJ(w));
        if ( ! EQ( v, w ) ) {
            if ( l+1 != i ) {
                SET_ELM_PLIST( list, l+1, w );
                SET_ELM_PLIST( list, i, (Obj)0 );
            }
            l += 1;
            v = w;
	    homog = (!mutable && homog && fam == FAMILY_OBJ(w));
        }
    }

    /* the list may be shorter now                                         */
    SET_LEN_PLIST( list, l );
    SHRINK_PLIST(  list, l );

    /* Set appropriate filters */
    if (!mutable)
      {
	if (!homog)
	  SET_FILT_LIST(list, FN_IS_NHOMOG);
	else
	  SET_FILT_LIST(list, FN_IS_HOMOG);
	SET_FILT_LIST(list, FN_IS_SSORT);
      }

    /* return whether the list contains mutable elements                   */
    if (mutable)
      return 0;
    if (!homog)
      return 1;
    else
      return 2;
}


/****************************************************************************
**
*F * * * * * * * * * * * * * * GAP level functions  * * * * * * * * * * * * *
*/

/****************************************************************************
**
*F  FuncSORT_LIST( <self>, <list> ) . . . . . . . . . . . . . . . sort a list
*/
Obj FuncSORT_LIST (
    Obj                 self,
    Obj                 list )
{
    /* check the first argument                                            */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "SORT_LIST: <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE  <= TNUM_OBJ(list)
      && TNUM_OBJ(list) <= T_PLIST_CYC_SSORT ) {
        SortDensePlist( list );
    }
    else {
        SORT_LIST( list );
    }
    IS_SSORT_LIST(list);

    /* return nothing                                                      */
    return (Obj)0;
}


/****************************************************************************
**


*F  FuncSORT_LIST_COMP( <self>, <list>, <func> )  . . . . . . . . sort a list
*/
Obj FuncSORT_LIST_COMP (
    Obj                 self,
    Obj                 list,
    Obj                 func )
{
    /* check the first argument                                            */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "SORT_LISTComp: <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }

    /* check the third argument                                            */
    while ( TNUM_OBJ( func ) != T_FUNCTION ) {
        func = ErrorReturnObj(
            "SORT_LISTComp: <func> must be a function (not a %s)",
            (Int)TNAM_OBJ(func), 0L,
            "you can replace <func> via 'return <func>;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE  <= TNUM_OBJ(list)
      && TNUM_OBJ(list) <= T_PLIST_CYC_SSORT ) {
        SortDensePlistComp( list, func );
    }
    else {
        SORT_LISTComp( list, func );
    }

    /* return nothing                                                      */
    return (Obj)0;
}


/****************************************************************************
**
*F  FuncSORT_PARA_LIST( <self>, <list> )  . . . . . . sort a list with shadow
*/
Obj FuncSORT_PARA_LIST (
    Obj                 self,
    Obj                 list,
    Obj               shadow )
{
    /* check the first two arguments                                       */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "SORT_PARA_LIST: first <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }
    while ( ! IS_SMALL_LIST(shadow) ) {
        shadow = ErrorReturnObj(
            "SORT_PARA_LIST: second <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(shadow), 0L,
            "you can replace <list> via 'return <list>;'" );
    }
    if( LEN_LIST( list ) != LEN_LIST( shadow ) ) {
        ErrorReturnVoid( 
            "SORT_PARA_LIST: lists must have the same length (not %d and %d)",
            (Int)LEN_LIST( list ),
            (Int)LEN_LIST( shadow ),
            "you can 'return;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE     <= TNUM_OBJ(list)
       && TNUM_OBJ(list)   <= T_PLIST_CYC_SSORT
       && T_PLIST_DENSE    <= TNUM_OBJ(shadow)
       && TNUM_OBJ(shadow) <= T_PLIST_CYC_SSORT ) {
        SortParaDensePlist( list, shadow );
    }
    else {
        SORT_PARA_LIST( list, shadow );
    }
    IS_SSORT_LIST(list);

    /* return nothing                                                      */
    return (Obj)0;
}


/****************************************************************************
**
*F  FuncSORT_LIST_COMP( <self>, <list>, <func> )  . . . . . . . . sort a list
*/
Obj FuncSORT_PARA_LIST_COMP (
    Obj                 self,
    Obj                 list,
    Obj               shadow,
    Obj                 func )
{
    /* check the first two arguments                                       */
    while ( ! IS_SMALL_LIST(list) ) {
        list = ErrorReturnObj(
            "SORT_LISTComp: <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(list), 0L,
            "you can replace <list> via 'return <list>;'" );
    }
    while ( ! IS_SMALL_LIST(shadow) ) {
        shadow = ErrorReturnObj(
            "SORT_PARA_LIST: second <list> must be a small list (not a %s)",
            (Int)TNAM_OBJ(shadow), 0L,
            "you can replace <list> via 'return <list>;'" );
    }
    if( LEN_LIST( list ) != LEN_LIST( shadow ) ) {
        ErrorReturnVoid( 
            "SORT_PARA_LIST: lists must have the same length (not %d and %d)",
            (Int)LEN_LIST( list ),
            (Int)LEN_LIST( shadow ),
            "you can 'return;'" );
    }

    /* check the third argument                                            */
    while ( TNUM_OBJ( func ) != T_FUNCTION ) {
        func = ErrorReturnObj(
            "SORT_LISTComp: <func> must be a function (not a %s)",
            (Int)TNAM_OBJ(func), 0L,
            "you can replace <func> via 'return <func>;'" );
    }

    /* dispatch                                                            */
    if ( T_PLIST_DENSE     <= TNUM_OBJ(list)
       && TNUM_OBJ(list)   <= T_PLIST_CYC_SSORT
       && T_PLIST_DENSE    <= TNUM_OBJ(shadow)
       && TNUM_OBJ(shadow) <= T_PLIST_CYC_SSORT ) {
        SortParaDensePlistComp( list, shadow, func );
    }
    else {
        SORT_PARA_LISTComp( list, shadow, func );
    }

    /* return nothing                                                      */
    return (Obj)0;
}


/****************************************************************************
**
*F  FuncOnPoints( <self>, <point>, <elm> )  . . . . . . . operation on points
**
**  'FuncOnPoints' implements the internal function 'OnPoints'.
**
**  'OnPoints( <point>, <elm> )'
**
**  specifies  the  canonical  default operation.   Passing  this function is
**  equivalent  to  specifying no operation.   This function  exists  because
**  there are places where the operation in not an option.
*/
Obj             FuncOnPoints (
    Obj                 self,
    Obj                 point,
    Obj                 elm )
{
    return POW( point, elm );
}


/****************************************************************************
**
*F  FuncOnPairs( <self>, <pair>, <elm> )  . . .  operation on pairs of points
**
**  'FuncOnPairs' implements the internal function 'OnPairs'.
**
**  'OnPairs( <pair>, <elm> )'
**
**  specifies  the componentwise operation    of group elements on  pairs  of
**  points, which are represented by lists of length 2.
*/
Obj             FuncOnPairs (
    Obj                 self,
    Obj                 pair,
    Obj                 elm )
{
    Obj                 img;            /* image, result                   */
    Obj                 tmp;            /* temporary                       */

    /* check the type of the first argument                                */
    while ( ! IS_SMALL_LIST( pair ) || LEN_LIST( pair ) != 2 ) {
        pair = ErrorReturnObj(
            "OnPairs: <pair> must be a list of length 2 (not a %s)",
            (Int)TNAM_OBJ(pair), 0L,
            "you can replace <pair> via 'return <pair>;'" );
    }

    /* create a new bag for the result                                     */
    img = NEW_PLIST( IS_MUTABLE_OBJ(pair) ? T_PLIST : T_PLIST+IMMUTABLE, 2 );
    SET_LEN_PLIST( img, 2 );

    /* and enter the images of the points into the result bag              */
    tmp = POW( ELMV_LIST( pair, 1 ), elm );
    SET_ELM_PLIST( img, 1, tmp );
    CHANGED_BAG( img );
    tmp = POW( ELMV_LIST( pair, 2 ), elm );
    SET_ELM_PLIST( img, 2, tmp );
    CHANGED_BAG( img );

    /* return the result                                                   */
    return img;
}


/****************************************************************************
**
*F  FuncOnTuples( <self>, <tuple>, <elm> )  . . operation on tuples of points
**
**  'FuncOnTuples' implements the internal function 'OnTuples'.
**
**  'OnTuples( <tuple>, <elm> )'
**
**  specifies the componentwise  operation  of  group elements  on tuples  of
**  points, which are represented by lists.  'OnPairs' is the special case of
**  'OnTuples' for tuples with two elements.
*/
Obj             FuncOnTuples (
    Obj                 self,
    Obj                 tuple,
    Obj                 elm )
{
    Obj                 img;            /* image, result                   */
    Obj                 tmp;            /* temporary                       */
    UInt                i;              /* loop variable                   */

    /* check the type of the first argument                                */
    while ( ! IS_SMALL_LIST( tuple ) ) {
        tuple = ErrorReturnObj(
            "OnTuples: <tuple> must be a small list (not a %s)",
            (Int)TNAM_OBJ(tuple), 0L,
            "you can replace <tuple> via 'return <tuple>;'" );
    }

    /* special case for the empty list */
    if ( HAS_FILT_LIST( tuple, FN_IS_EMPTY )) {
      if (IS_MUTABLE_OBJ(tuple)) {
	img = NEW_PLIST(T_PLIST_EMPTY, 0);
	SET_LEN_PLIST(img,0);
	return img;
      } else {
	return tuple;
      }
    }
    /* special case for permutations                                       */
    if ( TNUM_OBJ(elm) == T_PERM2 || TNUM_OBJ(elm) == T_PERM4 ) {
        PLAIN_LIST( tuple );
        return OnTuplesPerm( tuple, elm );
    }

    /* create a new bag for the result                                     */
    img = NEW_PLIST( IS_MUTABLE_OBJ(tuple) ? T_PLIST : T_PLIST+IMMUTABLE, LEN_LIST(tuple) );
    SET_LEN_PLIST( img, LEN_LIST(tuple) );

    /* and enter the images of the points into the result bag              */
    for ( i = LEN_LIST(tuple); 1 <= i; i-- ) {
        tmp = POW( ELMV_LIST( tuple, i ), elm );
        SET_ELM_PLIST( img, i, tmp );
        CHANGED_BAG( img );
    }

    /* return the result (must be a dense plain list, see 'FuncOnSets')    */
    return img;
}


/****************************************************************************
**
*F  FuncOnSets( <self>, <tuple>, <elm> )  . . . . operation on sets of points
**
**  'FuncOnSets' implements the internal function 'OnSets'.
**
**  'OnSets( <tuple>, <elm> )'
**
**  specifies the operation  of group elements  on  sets of points, which are
**  represented by sorted lists of points without duplicates (see "Sets").
*/

Obj             FuncOnSets (
    Obj                 self,
    Obj                 set,
    Obj                 elm )
{
    Obj                 img;            /* handle of the image, result     */
    UInt                status;        /* the elements are mutable        */

    /* check the type of the first argument                                */
    while ( !HAS_FILT_LIST(set, FN_IS_SSORT) && ! IsSet( set ) ) {
        set = ErrorReturnObj(
            "OnSets: <set> must be a set (not a %s)",
            (Int)TNAM_OBJ(set), 0L,
            "you can replace <set> via 'return <set>;'" );
    }

    /* special case for the empty list */
    if ( HAS_FILT_LIST( set, FN_IS_EMPTY )) {
      if (IS_MUTABLE_OBJ(set)) {
	img = NEW_PLIST(T_PLIST_EMPTY, 0);
	SET_LEN_PLIST(img,0);
	return img;
      } else {
	return set;
      }
    }
	
	 

    /* special case for permutations                                       */
    if ( TNUM_OBJ(elm) == T_PERM2 || TNUM_OBJ(elm) == T_PERM4 ) {
        PLAIN_LIST( set );
        return OnSetsPerm( set, elm );
    }

    /* compute the list of images                                          */
    img = FuncOnTuples( self, set, elm );

    /* sort the images list (which is a dense plain list)                  */
    SortDensePlist( img );

    /* remove duplicates, check for mutable elements                       */
    status = RemoveDupsDensePlist( img );

    /* if possible, turn this into a set                                   */
    switch (status)
      {
      case 0:
	break;
	
      case 1:
	RetypeBag( img, T_PLIST_DENSE_NHOM_SSORT );

      case 2:
	RetypeBag( img, T_PLIST_HOM_SSORT );

      }


    /* return set                                                          */
    return img;
}


/****************************************************************************
**
*F  FuncOnRight( <self>, <point>, <elm> ) . operation by mult. from the right
**
**  'FuncOnRight' implements the internal function 'OnRight'.
**
**  'OnRight( <point>, <elm> )'
**
**  specifies that group elements operate by multiplication from the right.
*/
Obj             FuncOnRight (
    Obj                 self,
    Obj                 point,
    Obj                 elm )
{
    return PROD( point, elm );
}


/****************************************************************************
**
*F  FuncOnLeftAntiOperation( <self>, <point>, <elm> ) op. by mult. from the left
**
**  'FuncOnLeftAntiOperation' implements the internal function
**  'OnLeftAntiOperation'.
**
**  'OnLeftAntiOperation( <point>, <elm> )'
**
**  specifies that group elements operate by multiplication from the left.
*/
Obj             FuncOnLeftAntiOperation (
    Obj                 self,
    Obj                 point,
    Obj                 elm )
{
    return PROD( elm, point );
}


/****************************************************************************
**
*F  FuncOnLeftInverse( <self>, <point>, <elm> )	. . op by mult. from the left
**
**  'FuncOnLeftInverse' implements the internal function 'OnLeftInverse'.
**
**  'OnLeftInverse( <point>, <elm> )'
**
**  specifies that group elements operate by multiplication from the left
**  with the inverse.
*/
Obj             FuncOnLeftInverse (
    Obj                 self,
    Obj                 point,
    Obj                 elm )
{
    elm = INV(elm);
    return PROD( elm, point );
}

/****************************************************************************
**
*F  FuncSTRONGLY_CONNECTED_COMPONENTS_DIGRAPH
**
**  `digraph' should be a list whose entries and the lists of out-neighbours
** of the vertices. So [[2,3],[1],[2]] represents the graph whose edges are
** 1->2, 1->3, 2->1 and 3->2.
**
**  returns a newly constructed list whose elements are lists representing the
** strongly connected components of the directed graph. Neither the components,
** nor their elements are in any particular order.
**
** The algorithm is that of Tarjan, based on the implementation in Sedgwick,
** with a bug fixed, and made non-recursive to avoid problems with stack limits
** under (for instance) Linux. This version is a bit slower than the recursive
** version, but much faster than any of the GAP implementations.
**
** A possible change is to allocate the internal arrays rather smaller, and
** grow them if needed. This might allow some computations to complete that would
** otherwise run out of memory, but would slow things down a bit.
*/


static Obj FuncSTRONGLY_CONNECTED_COMPONENTS_DIGRAPH(Obj self, Obj digraph)
{
  UInt i,level,k,l,x,t,m;
  UInt now = 0,n;
  Obj val, stack, comps,comp;
  Obj frames, adj;
  UInt *fptr;

  n = LEN_LIST(digraph);
  if (n == 0)
    {
      return NEW_PLIST(T_PLIST_EMPTY,0);
    }
  val = NewBag(T_DATOBJ, (n+1)*sizeof(UInt));
  stack = NEW_PLIST(T_PLIST_CYC, n);
  SET_LEN_PLIST(stack, 0);
  comps = NEW_PLIST(T_PLIST_TAB, n);
  SET_LEN_PLIST(comps, 0);
  frames = NewBag(T_DATOBJ, (4*n+1)*sizeof(UInt));  
  for (k = 1; k <= n; k++)
    {
      if (((UInt *)ADDR_OBJ(val))[k] == 0)
	{
	  level = 1;
	  adj = ELM_LIST(digraph, k);
	  PLAIN_LIST(adj);
	  fptr = (UInt *)ADDR_OBJ(frames);
	  fptr[0] = k;
	  now++;
	  ((UInt *)ADDR_OBJ(val))[k] = now;
	  fptr[1] = now;
	  l = LEN_PLIST(stack);
	  SET_ELM_PLIST(stack, l+1, INTOBJ_INT(k));
	  SET_LEN_PLIST(stack, l+1);
	  fptr[2] = 1;
	  fptr[3] = (UInt)adj;
	  while (level > 0 ) {
	    if (fptr[2] > LEN_PLIST(fptr[3]))
	      {
		if (fptr[1] == ((UInt *)ADDR_OBJ(val))[fptr[0]])
		  {
		    l = LEN_PLIST(stack);
		    i = l;
		    do {
		      x = INT_INTOBJ(ELM_PLIST(stack, i));
		      SET_ELM_PLIST(val, x, INTOBJ_INT(n+1));
		      i--;
		    } while (x != fptr[0]);
		    comp = NEW_PLIST(T_PLIST_CYC, l-i);
		    SET_LEN_PLIST(comp, l-i);
		    memcpy( (void *)((char *)(ADDR_OBJ(comp)) + sizeof(Obj)), 
			    (void *)((char *)(ADDR_OBJ(stack)) + (i+1)*sizeof(Obj)), 
			    (size_t)((l - i )*sizeof(Obj)));
		    SET_LEN_PLIST(stack, i);
		    l = LEN_PLIST(comps);
		    SET_ELM_PLIST(comps, l+1, comp);
		    SET_LEN_PLIST(comps, l+1);
		    CHANGED_BAG(comps);
		    fptr = (UInt *)ADDR_OBJ(frames)+(level-1)*4;
		  }
		level--;
		fptr -= 4;
		if (level > 0 && fptr[5]  < fptr[1])
		  fptr[1] = fptr[5];
	      }
	    else
	      {
		adj = (Obj)fptr[3];
		t = INT_INTOBJ(ELM_PLIST(adj, (fptr[2])++));
		if (0 ==(m =  ((UInt *)ADDR_OBJ(val))[t]))
		  {
		    level++;
		    adj = ELM_LIST(digraph, t);
		    PLAIN_LIST(adj);
		    fptr = (UInt *)ADDR_OBJ(frames)+(level-1)*4;
		    fptr[0] = t;
		    now++;
		    ((UInt *)ADDR_OBJ(val))[t] = now;
		    fptr[1] = now;
		    l = LEN_PLIST(stack);
		    SET_ELM_PLIST(stack, l+1, INTOBJ_INT(t));
		    SET_LEN_PLIST(stack, l+1);
		    fptr[2] = 1;
		    fptr[3] = (UInt)adj;
		  }
		else
		  {
		    if (m < fptr[1])
		      fptr[1] = m;
		  }
	      }
	  }
	}
      
    }
  SHRINK_PLIST(comps, LEN_PLIST(comps));
  return comps;
}


/****************************************************************************
**
*F  FuncCOPY_LIST_ENTRIES( <self>, <args> ) . . mass move of list entries
**
*/

static inline Int GetIntObj( Obj list, UInt pos)
{
  Obj entry;
  entry = ELM_PLIST(list, pos);
  if (!entry)
    {
      Pr("panic: internal inconsistency", 0L, 0L);
      SyExit(1);
    }
  while (!IS_INTOBJ(entry))
    {
      entry = ErrorReturnObj("COPY_LIST_ENTRIES: argument %d  must be a small integer, not a %s",
			     (Int)pos, (Int)InfoBags[TNUM_OBJ(entry)].name,
			     "you can return a small integer to continue");
    }
  return INT_INTOBJ(entry);
}

Obj FuncCOPY_LIST_ENTRIES( Obj self, Obj args )
{  
  Obj srclist;
  UInt srcstart;
  Int srcinc;
  Obj dstlist;
  UInt dststart;
  Int dstinc;
  UInt number;
  UInt srcmax;
  UInt dstmax;
  Obj *sptr, *dptr;
  UInt ct;

  if (!IS_PLIST(args))
    {
      Pr("panic: internal inconsistency",0L,0L);
      SyExit(1);
    }
  if (LEN_PLIST(args) != 7)
    {
      ErrorMayQuit("COPY_LIST_ENTRIES: number of arguments must be 7, not %d",
		   (Int)LEN_PLIST(args), 0L);
    }
  srclist = ELM_PLIST(args,1);
  if (!srclist)
    {
      Pr("panic: internal inconsistency", 0L, 0L);
      SyExit(1);
    }
  while (!IS_PLIST(srclist))
    {
      srclist = ErrorReturnObj("COPY_LIST_ENTRIES: source must be a plain list not a %s",
			       (Int)InfoBags[TNUM_OBJ(srclist)].name, 0L,
			       "you can return a plain list to continue");
    }

  srcstart = (UInt)GetIntObj(args,2);
  srcinc = GetIntObj(args,3);
  dstlist = ELM_PLIST(args,4);
  if (!dstlist)
    {
      Pr("panic: internal inconsistency", 0L, 0L);
      SyExit(1);
    }
  while (!IS_PLIST(dstlist) || !IS_MUTABLE_OBJ(dstlist))
    {
      dstlist = ErrorReturnObj("COPY_LIST_ENTRIES: destination must be a mutable plain list not a %s",
			       (Int)InfoBags[TNUM_OBJ(dstlist)].name, 0L,
			       "you can return a plain list to continue");
    }
  dststart = (UInt)GetIntObj(args,5);
  dstinc = GetIntObj(args,6);
  number = GetIntObj(args,7);
  
  if (number == 0)
    return (Obj) 0;
  
  srcmax = (srcinc > 0) ? srcstart + (number-1)*srcinc : srcstart;
  dstmax = (dstinc > 0) ? dststart + (number-1)*dstinc : dststart;
  
  GROW_PLIST(dstlist, dstmax);
  GROW_PLIST(srclist, srcmax);
  if (srcinc == 1 && dstinc == 1)
    {
      memmove((void *) (ADDR_OBJ(dstlist) + dststart),
	      (void *) (ADDR_OBJ(srclist) + srcstart),
	      (size_t) number*sizeof(Obj));
    }
  else if (srclist != dstlist)
    {
      sptr = ADDR_OBJ(srclist) + srcstart;
      dptr = ADDR_OBJ(dstlist) + dststart;
      for (ct = 0; ct < number ; ct++)
	{
	  *dptr = *sptr;
	  sptr += srcinc;
	  dptr += dstinc;
	}
    }
  else if (srcinc == dstinc)
    {
      if (srcstart == dststart)
	return (Obj)0;
      else
	{
	  if ((srcstart > dststart) == (srcinc > 0))
	    {
	      sptr = ADDR_OBJ(srclist) + srcstart;
	      dptr = ADDR_OBJ(srclist) + dststart;
	      for (ct = 0; ct < number ; ct++)
		{
		  *dptr = *sptr;
		  sptr += srcinc;
		  dptr += srcinc;
		}
	    }
	  else
	    {
	      sptr = ADDR_OBJ(srclist) + srcstart + number*srcinc;
	      dptr = ADDR_OBJ(srclist) + dststart + number*srcinc;
	      for (ct = 0; ct < number; ct++)
		{
		  sptr -= srcinc;
		  dptr -= srcinc;
		  *dptr = *sptr;
		}
	      
	    }
	}
	      
    }
  else
    {
      Obj tmplist = NEW_PLIST(T_PLIST,number);
      Obj *tptr = ADDR_OBJ(tmplist)+1;
      sptr = ADDR_OBJ(srclist)+srcstart;
      for (ct = 0; ct < number; ct++)
	{
	  *tptr = *sptr;
	  tptr++;
	  sptr += srcinc;
	}
      tptr = ADDR_OBJ(tmplist)+1;
      dptr = ADDR_OBJ(srclist)+dststart;
      for (ct = 0; ct < number; ct++)
	{
	  *dptr = *tptr;
	  tptr++;
	  dptr += dstinc;
	}
    }

  if (dstmax > LEN_PLIST(dstlist))
    {
      dptr = ADDR_OBJ(dstlist)+dstmax;
      ct = dstmax;
      while (!*dptr)
	{
	  ct--;
	  dptr--;
	}
      SET_LEN_PLIST(dstlist, ct);
    }
  if (LEN_PLIST(dstlist) > 0)
    RetypeBag(dstlist, T_PLIST);
  else
    RetypeBag(dstlist, T_PLIST_EMPTY);
  return (Obj) 0;

}

/****************************************************************************
**
*F  FuncBIMULT_MONOMIALS_ALGEBRA_ELEMENT
**
*/

Obj FuncBIMULT_MONOMIALS_ALGEBRA_ELEMENT(Obj self, 
                                         Obj mona, Obj poly, Obj monb)
{
  UInt len,la,lb,lm,i,j;
  Obj prd;
  Obj mon;
  Obj *po,*pn;

  /* TODO: test arguments */

  /* Make a new polynomial */
  len = LEN_PLIST(poly);
  prd = NEW_PLIST( T_PLIST , len );
  SET_LEN_PLIST( prd, len );

  if (mona == False) {
    la=0;
  }
  else {
    la=LEN_PLIST(mona);
  }

  if (monb == False) {
    lb=0;
  }
  else {
    lb=LEN_PLIST(monb);
  }

  /* fill its entries */
  for (i=1;i<=len;i=i+2) {
    lm = LEN_PLIST(ELM_PLIST(poly,i));
  /*Pr("i= %d, lm= %d \n",i,lm); */
    /* new monomial */
    mon = NEW_PLIST(T_PLIST,lm+la+lb);
    SET_LEN_PLIST(mon,lm+la+lb);
    pn = ADDR_OBJ(mon)+1;
    
    /* put in a */
    j=1;
    po = ADDR_OBJ(mona)+1;
    while (j<=la) {
      *pn++=*po++;
      j++;
    }

    /* append monomial */
    j=1;
    po = ADDR_OBJ(ELM_PLIST(poly,i))+1;
    while (j<=lm) {
      *pn++=*po++;
      j++;
    }

    /* append b */
    j=1;
    po = ADDR_OBJ(monb)+1;
    while (j<=lb) {
      *pn++=*po++;
      j++;
    }

    SET_ELM_PLIST(prd,i,mon);
    /* copy coefficient */
    SET_ELM_PLIST(prd,i+1,ELM_PLIST(poly,i+1));
    CHANGED_BAG(prd);
  }

  return prd;
}



/****************************************************************************
**
*F  FuncHORSPOOL_LISTS
**
*/

Obj FuncHORSPOOL_LISTS(Obj self,Obj wrep, Obj subrep, Obj pre)
{
  UInt i,wsize,subsize,di;
  Int j;
  Obj pos;
  Obj *pw,*ps,*pp;

  wsize = LEN_PLIST(wrep);
  subsize = LEN_PLIST(subrep);
  pw=ADDR_OBJ(wrep);
  ps=ADDR_OBJ(subrep);
  pp=ADDR_OBJ(pre);
 
  pos = Fail;

  if ( subsize <= wsize ) {
    i = 0;
    di = wsize-subsize;
    while (i <= di) {
      j=subsize;
      while (j>0) {
 /* Pr("i= %d j=%d \n",i,j);  */
        if (ps[j] != pw[i+j]) {
	  j=-1;
	}
	else {
	  j--;
	}
      }
      if (j==0) {
        pos=INTOBJ_INT(i+1);
        i=wsize;
      }
      else {
 /* Pr("pw: %d \n",INT_INTOBJ(pw[i+subsize]),0L);  */
	      i = i + INT_INTOBJ(pp[INT_INTOBJ(pw[i+subsize])]);
      }
    }
  }
  return pos;
}

/****************************************************************************
**

*F * * * * * * * * * * * * * initialize package * * * * * * * * * * * * * * *
*/


/****************************************************************************
**

*V  GVarOpers . . . . . . . . . . . . . . . . .  list of operations to export
*/
static StructGVarOper GVarOpers [] = {

    { "ADD_LIST", 2, "list, val", &AddListOper,
      FuncADD_LIST, "src/listfunc.c:ADD_LIST" },

    { "APPEND_LIST", 2, "list, val", &AppendListOper,
      FuncAPPEND_LIST, "src/listfunc.c:APPEND_LIST" },

    { 0 }

};


/****************************************************************************
**
*V  GVarFuncs . . . . . . . . . . . . . . . . . . list of functions to export
*/
static StructGVarFunc GVarFuncs [] = {

    { "APPEND_LIST_INTR", 2, "list1, list2", 
      FuncAPPEND_LIST_INTR, "src/listfunc.c:APPEND_LIST_INTR" },

    { "POSITION_SORTED_LIST", 2, "list, obj", 
      FuncPOSITION_SORTED_LIST, "src/listfunc.c:POSITION_SORTED_LIST" },

    { "POSITION_SORTED_LIST_COMP", 3, "list, obj, func", 
      FuncPOSITION_SORTED_COMP, "src/listfunc.c:POSITION_SORTED_LIST_COMP" },

    { "POSITION_FIRST_COMPONENT_SORTED", 2, "list, obj", 
      FuncPOSITION_FIRST_COMPONENT_SORTED, "src/listfunc.c:POSITION_FIRST_COMPONENT_SORTED" },

    { "SORT_LIST", 1, "list",
      FuncSORT_LIST, "src/listfunc.c:SORT_LIST" },

    { "SORT_LIST_COMP", 2, "list, func",
      FuncSORT_LIST_COMP, "src/listfunc.c:SORT_LIST_COMP" },

    { "SORT_PARA_LIST", 2, "list, list",
      FuncSORT_PARA_LIST, "src/listfunc.c:SORT_PARA_LIST" },

    { "SORT_PARA_LIST_COMP", 3, "list, list, func",
      FuncSORT_PARA_LIST_COMP, "src/listfunc.c:SORT_PARA_LIST_COMP" },

    { "OnPoints", 2, "pnt, elm",
      FuncOnPoints, "src/listfunc.c:OnPoints" },

    { "OnPairs", 2, "pair, elm",
      FuncOnPairs, "src/listfunc.c:OnPairs" },

    { "OnTuples", 2, "tuple, elm",
      FuncOnTuples, "src/listfunc.c:OnTuples" },

    { "OnSets", 2, "set, elm",
      FuncOnSets, "src/listfunc.c:OnSets" },

    { "OnRight", 2, "pnt, elm",
      FuncOnRight, "src/listfunc.c:OnRight" },

    { "OnLeftAntiOperation", 2, "pnt, elm",
      FuncOnLeftAntiOperation, "src/listfunc.c:OnLeftAntiOperation" },

    { "OnLeftInverse", 2, "pnt, elm",
      FuncOnLeftInverse, "src/listfunc.c:OnLeftInverse" },

    { "COPY_LIST_ENTRIES", -1, "srclist,srcstart,srcinc,dstlist,dststart,dstinc,number",
      FuncCOPY_LIST_ENTRIES, "src/listfunc.c:COPY_LIST_ENTRIES" },

    { "STRONGLY_CONNECTED_COMPONENTS_DIGRAPH", 1, "digraph",
      FuncSTRONGLY_CONNECTED_COMPONENTS_DIGRAPH, "src/listfunc.c:STRONGLY_CONNECTED_COMPONENTS_DIGRAPH" },

    { "BIMULT_MONOMIALS_ALGEBRA_ELEMENT",3,"mon, poly, mon",
      FuncBIMULT_MONOMIALS_ALGEBRA_ELEMENT,"src/listfunc.c:BIMULT_MONOMIALS_ALGEBRA_ELEMENT" },

    { "HORSPOOL_LISTS",3,"list, sub, pre",
      FuncHORSPOOL_LISTS,"src/listfunc.c:HORSPOOL_LISTS" },

    { "HEAP_SORT_PLIST",1,"list",
      HEAP_SORT_PLIST,"src/listfunc.c:HEAP_SORT_PLIST" },

    { 0 }

};


/****************************************************************************
**

*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel (
    StructInitInfo *    module )
{
    /* init filters and functions                                          */
    InitHdlrOpersFromTable( GVarOpers );
    InitHdlrFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}


/****************************************************************************
**
*F  InitLibrary( <module> ) . . . . . . .  initialise library data structures
*/
static Int InitLibrary (
    StructInitInfo *    module )
{
    /* init filters and functions                                          */
    InitGVarOpersFromTable( GVarOpers );
    InitGVarFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}


/****************************************************************************
**
*F  InitInfoListFunc()  . . . . . . . . . . . . . . . table of init functions
*/
static StructInitInfo module = {
    MODULE_BUILTIN,                     /* type                           */
    "listfunc",                         /* name                           */
    0,                                  /* revision entry of c file       */
    0,                                  /* revision entry of h file       */
    0,                                  /* version                        */
    0,                                  /* crc                            */
    InitKernel,                         /* initKernel                     */
    InitLibrary,                        /* initLibrary                    */
    0,                                  /* checkInit                      */
    0,                                  /* preSave                        */
    0,                                  /* postSave                       */
    0                                   /* postRestore                    */
};

StructInitInfo * InitInfoListFunc ( void )
{
    module.revision_c = Revision_listfunc_c;
    module.revision_h = Revision_listfunc_h;
    FillInVersion( &module );
    return &module;
}


/****************************************************************************
**

*E  listfunc.c  . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
*/
