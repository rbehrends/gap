/****************************************************************************
**
*W  boehm_gc.c
**
**  This file stores code only required by the boehm garbage collector
**
**  The definitions of methods in this file can be found in gasman.h,
**  where the non-boehm versions of these methods live.
**/

#include <src/system.h>                 /* Ints, UInts */
#include <src/gapstate.h>

#include <src/gasman.h>                 /* garbage collector */

#include <src/objects.h>                /* objects */


#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <src/code.h>                   /* coder */


enum {
    NTYPES = 256
};

TNumInfoBags            InfoBags [ NTYPES ];

UInt            SizeAllBags;

static inline Bag *DATA(BagHeader *bag)
{
    return (Bag *)(((char *)bag) + sizeof(BagHeader));
}


/****************************************************************************
**
*F  InitFreeFuncBag(<type>,<free-func>)
*/

TNumFreeFuncBags TabFreeFuncBags[ NTYPES ];

void InitFreeFuncBag(UInt type, TNumFreeFuncBags finalizer_func)
{
  TabFreeFuncBags[type] = finalizer_func;
}

void StandardFinalizer( void * bagContents, void * data )
{
  Bag bag;
  void *bagContents2;
  bagContents2 = ((char *) bagContents) + sizeof(BagHeader);
  bag = (Bag) &bagContents2;
  TabFreeFuncBags[TNUM_BAG(bag)](bag);
}

#define ALLOCATE_BAGMEM(n) (calloc(1, (n)))
#define ALLOCATE_MPTR() (calloc(1, sizeof(Bag *)))

/****************************************************************************
**
*F  AllocateBagMemory( <type>, <size> )
**
**  Allocate memory for a new bag.
**
**  'AllocateBagMemory' is an auxiliary routine for the Boehm GC that
**  allocates memory from the appropriate pool. 'gc_type' is -1 if all words
**  in the bag can refer to other bags, 0 if the bag will not contain any
**  references to other bags, and > 0 to indicate a specific memory layout
**  descriptor.
**/
void *AllocateBagMemory(int type, UInt size)
{
  // HOOK: return `size` bytes memory of TNUM `type`.
  return ALLOCATE_BAGMEM(size);
}

void InitMarkFuncBags (
    UInt                type,
    TNumMarkFuncBags    mark_func )
{
  // HOOK: set mark function for type `type`.
}

void InitSweepFuncBags (
    UInt                type,
    TNumSweepFuncBags    mark_func )
{
  // HOOK: set sweep function for type `type`.
  // This is intended for weak pointer objects.
}

void            InitBags (
    TNumAllocFuncBags   alloc_func,
    UInt                initial_size,
    TNumStackFuncBags   stack_func,
    Bag *               stack_bottom,
    UInt                stack_align,
    TNumAbortFuncBags   abort_func )
{
    // HOOK: initialization happens here.
}

UInt CollectBags (
    UInt                size,
    UInt                full )
{
    // HOOK: perform a full collection
    return 1;
}

void            RetypeBag (
    Bag                 bag,
    UInt                new_type )
{
    BagHeader * header = BAG_HEADER(bag);

#ifdef COUNT_BAGS
    /* update the statistics      */
    {
          UInt                old_type;       /* old type of the bag */
          UInt                size;

          old_type = header->type;
          size = header->size;
          InfoBags[old_type].nrLive   -= 1;
          InfoBags[new_type].nrLive   += 1;
          InfoBags[old_type].nrAll    -= 1;
          InfoBags[new_type].nrAll    += 1;
          InfoBags[old_type].sizeLive -= size;
          InfoBags[new_type].sizeLive += size;
          InfoBags[old_type].sizeAll  -= size;
          InfoBags[new_type].sizeAll  += size;
    }
#endif

    header->type = new_type;
}

static inline Bag AllocateMasterPointer() {
  // HOOK: Allocate memory for the master pointer.
  // Master pointers require one word of memory.
  return ALLOCATE_MPTR();
}

Bag NewBag (
    UInt                type,
    UInt                size )
{
    Bag                 bag;            /* identifier of the new bag       */
    UInt                alloc_size;

    alloc_size = sizeof(BagHeader) + size;
    bag = AllocateMasterPointer();

    SizeAllBags             += size;

    /* If the size of an object is zero (such as an empty permutation),
     * and the header size is a multiple of twice the word size of the
     * architecture, then the master pointer will actually point past
     * the allocated area. Because this would result in the object
     * being freed prematurely, we will allocate at least one extra
     * byte so that the master pointer actually points to within an
     * allocated memory area.
     */
    if (size == 0)
      alloc_size++;
    /* While we use the Boehm GC without the "all interior pointers"
     * option, stack references to the interior of an object will
     * still be valid from any reference on the stack. This can lead,
     * for example, to a 1GB string never being freed if there's an
     * integer on the stack that happens to also be a reference to
     * any character inside that string. The garbage collector does
     * this because after compiler optimizations (especially reduction
     * in strength) references to the beginning of an object may be
     * lost.
     *
     * However, this is not generally a risk with GAP objects, because
     * master pointers on the heap will always retain a reference to
     * the start of the object (or, more precisely, to the first byte
     * past the header area). Hence, compiler optimizations pose no
     * actual risk unless the master pointer is destroyed also.
     *
     * To avoid the scenario where large objects do not get deallocated,
     * we therefore use the _ignore_off_page() calls. One caveat here
     * is that these calls do not use thread-local allocation, making
     * them somewhat slower. Hence, we only use them for sufficiently
     * large objects.
     */
    BagHeader * header = AllocateBagMemory(type, alloc_size);

    header->type = type;
    header->flags = 0;
    header->size = size;

    /* set the masterpointer                                               */
    SET_PTR_BAG(bag, DATA(header));
    /* return the identifier of the new bag                                */
    return bag;
}

UInt ResizeBag (
    Bag                 bag,
    UInt                new_size )
{
    UInt                type;           /* type of the bag                 */
    UInt                flags;
    UInt                old_size;       /* old size of the bag             */
    Bag *               src;            /* source in copying               */
    UInt                alloc_size;

    /* check the size                                                      */

#ifdef TREMBLE_HEAP
    CollectBags(0,0);
#endif

    BagHeader * header = BAG_HEADER(bag);

    /* get type and old size of the bag                                    */
    type     = header->type;
    flags    = header->flags;
    old_size = header->size;

#ifdef COUNT_BAGS
    /* update the statistics                                               */
    InfoBags[type].sizeLive += new_size - old_size;
    InfoBags[type].sizeAll  += new_size - old_size;
#endif
    SizeAllBags             += new_size - old_size;

    if ( new_size <= old_size ) {
        /* change the size word                                            */
        header->size = new_size;
    }

    /* if the bag is enlarged                                              */
    else {
        alloc_size = sizeof(BagHeader) + new_size;
        if (new_size == 0)
            alloc_size++;
        header = AllocateBagMemory(type, alloc_size);

        header->type = type;
        header->flags = flags;
        header->size = new_size;

        /* set the masterpointer                                           */
        src = PTR_BAG(bag);
        SET_PTR_BAG(bag, DATA(header));

        if (DATA(header) != src) {
            memcpy( DATA(header), src, old_size < new_size ? old_size : new_size );
        } else if (new_size < old_size) {
            memset(DATA(header)+new_size, 0, old_size - new_size);
        }
    }
    /* return success                                                      */
    return 1;
}


/*****************************************************************************
** The following functions are not required respectively supported, so empty
** implementations are provided
**
*/

void InitGlobalBag (
    Bag *               addr,
    const Char *        cookie )
{
  // HOOK: Register global root.
}

void CallbackForAllBags(
     void (*func)(Bag) )
{ }

void            InitCollectFuncBags (
    TNumCollectFuncBags before_func,
    TNumCollectFuncBags after_func )
{ }

void SwapMasterPoint( Bag bag1, Bag bag2 )
{
    Obj *ptr1 = PTR_BAG(bag1);
    Obj *ptr2 = PTR_BAG(bag2);
    SET_PTR_BAG(bag1, ptr2);
    SET_PTR_BAG(bag2, ptr1);
}

// HOOK: mark functions

void MarkNoSubBags( Bag bag )
{
}

void MarkOneSubBags( Bag bag )
{
}

void MarkTwoSubBags( Bag bag )
{
}

void MarkThreeSubBags( Bag bag )
{
}

void MarkFourSubBags( Bag bag )
{
}

void MarkAllSubBags( Bag bag )
{
}

void MarkBagWeakly( Bag bag )
{
}

void MarkArrayOfBags( const Bag array[], UInt count )
{
}
