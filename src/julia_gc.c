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

#include "julia.h"
#include "gcext.h"

extern jl_value_t *(jl_gc_alloc)(jl_ptls_t ptls, size_t sz, void *ty);


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

/****************************************************************************
**
**  Treap functionality
**
**  Treaps are probabilistically balanced binary trees. We use them for
**  range queries on pointers for conservative scans. Unlike red-black
**  trees, they're simple to implement, and unlike AVL trees, insertions
**  take an expected O(1) number of mutations to the tree, making them
**  more cache-friendly for an insertion-heavy workload.
**
**  Their downside is that they are probabilistic and that hypothetically,
**  degenerate cases can occur. However, these are very unlikely, and if
**  that turns out to be a problem, we can replace them with alternate
**  balanced trees (B-trees being a likely suitable candidate).
*/

// Comparing pointers in C without triggering undefined behavior
// can be difficult. As the GC already assumes that the memory
// range goes from 0 to 2^k-1 (region tables), we simply convert
// to uintptr_t and compare those.

static inline int cmp_ptr(void *p, void *q)
{
    uintptr_t paddr = (uintptr_t) p;
    uintptr_t qaddr = (uintptr_t) q;
    if (paddr < qaddr)
        return -1;
    else if (paddr > qaddr)
        return 1;
    else
        return 0;
}

static inline int lt_ptr(void *a, void *b)
{
    return (uintptr_t) a < (uintptr_t) b;
}

static inline int gt_ptr(void *a, void *b)
{
    return (uintptr_t) a > (uintptr_t) b;
}

static inline void *max_ptr(void *a, void *b)
{
    if ((uintptr_t) a > (uintptr_t) b)
        return a;
    else
        return b;
}

static inline void *min_ptr(void *a, void *b)
{
    if ((uintptr_t) a < (uintptr_t) b)
        return a;
    else
        return b;
}

/* align pointer to full word if mis-aligned */
static inline void *align_ptr(void *p)
{
    uintptr_t u = (uintptr_t) p;
    u &= ~(sizeof(p)-1);
    return (void *)u;
}

typedef struct treap_t {
  struct treap_t *left, *right;
  size_t prio;
  void *addr;
  size_t size;
} treap_t;

static treap_t *treap_free_list;

treap_t *alloc_treap(void) {
  treap_t *result;
  if (treap_free_list) {
    result = treap_free_list;
    treap_free_list = treap_free_list->right;
  }
  else
    result = malloc(sizeof(treap_t));
  result->left = NULL;
  result->right = NULL;
  result->addr = NULL;
  result->size = 0;
  return result;
}

void free_treap(treap_t *t) {
  t->right = treap_free_list;
  treap_free_list = t;
}

static inline int test_bigval_range(treap_t *node, void *p)
{
    char *l = node->addr;
    char *r = l + node->size;
    if (lt_ptr(p, l)) return -1;
    if (!lt_ptr(p, r)) return 1;
    return 0;
}


#define L(t) ((t)->left)
#define R(t) ((t)->right)

static inline void treap_rot_right(treap_t **treap)
{
    /*       t                 l       */
    /*     /   \             /   \     */
    /*    l     r    -->    a     t    */
    /*   / \                     / \   */
    /*  a   b                   b   r  */
    treap_t *t = *treap;
    treap_t *l = L(t);
    treap_t *a = L(l);
    treap_t *b = R(l);
    L(l) = a;
    R(l) = t;
    L(t) = b;
    *treap = l;
}

static inline void treap_rot_left(treap_t **treap)
{
    /*     t                   r       */
    /*   /   \               /   \     */
    /*  l     r    -->      t     b    */
    /*       / \           / \         */
    /*      a   b         l   a        */
    treap_t *t = *treap;
    treap_t *r = R(t);
    treap_t *a = L(r);
    treap_t *b = R(r);
    L(r) = t;
    R(r) = b;
    R(t) = a;
    *treap = r;
}

static void *treap_find(treap_t *treap, void *p)
{
    while (treap) {
        int c = test_bigval_range(treap, p);
        if (c == 0)
            return treap->addr;
        else if (c < 0)
            treap = L(treap);
        else
            treap = R(treap);
    }
    return NULL;
}

static void treap_insert(treap_t **treap, treap_t *val)
{
    treap_t *t = *treap;
    if (t == NULL) {
        L(val) = NULL;
        R(val) = NULL;
        *treap = val;
    } else {
        int c = cmp_ptr(val, t);
        if (c < 0) {
            treap_insert(&L(t), val);
            if (L(t)->prio > t->prio) {
                treap_rot_right(treap);
            }
        } else if (c > 0) {
            treap_insert(&R(t), val);
            if (R(t)->prio > t->prio) {
                treap_rot_left(treap);
            }
        }
    }
}

static void treap_delete_node(treap_t **treap)
{
    for (;;) {
        treap_t *t = *treap;
        if (L(t) == NULL) {
            *treap = R(t);
	    free_treap(t);
            break;
        } else if (R(t) == NULL) {
            *treap = L(t);
	    free_treap(t);
            break;
        } else {
            if (L(t)->prio > R(t)->prio) {
                treap_rot_right(treap);
                treap = &R(*treap);
            } else {
                treap_rot_left(treap);
                treap = &L(*treap);
            }
        }
    }
}

static int treap_delete(treap_t **treap, void *addr)
{
    while (*treap != NULL) {
        int c = cmp_ptr(addr, (*treap)->addr);
        if (c == 0) {
          treap_delete_node(treap);
          return 1;
        } else if (c < 0) {
          treap = &L(*treap);
        } else {
          treap = &R(*treap);
        }
    }
    return 0;
}

static uint64_t xorshift_rng_state = 1;

static uint64_t xorshift_rng(void)
{
    uint64_t x = xorshift_rng_state;
    x = x ^ (x >> 12);
    x = x ^ (x << 25);
    x = x ^ (x >> 27);
    xorshift_rng_state = x;
    return x * (uint64_t) 0x2545F4914F6CDD1DUL;
}


static treap_t *bigvals;

void *alloc_bigval(size_t size) {
  void *result = malloc(size);
  memset(result, 0, size);
  treap_t *node = alloc_treap();
  node->addr = result;
  node->prio = xorshift_rng();
  treap_insert(&bigvals, node);
  return result;
}

void free_bigval(void *p) {
  if (p) {
    treap_delete(&bigvals, p);
    free(p);
  }
}

static jl_datatype_t *datatype_mptr;
static jl_datatype_t *datatype_bag;
static void *GapStackBottom = NULL;
static size_t GapStackAlign = sizeof(Int);
static jl_ptls_t JuliaTLS = NULL;

#ifndef NR_GLOBAL_BAGS
#define NR_GLOBAL_BAGS 20000L
#endif

static Bag *GlobalAddr[NR_GLOBAL_BAGS];
static const Char *GlobalCookie[NR_GLOBAL_BAGS];
static Int GlobalCount;



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
  void *result = (void *) jl_gc_alloc(JuliaTLS, size, datatype_bag);
  return result;
}

TNumMarkFuncBags TabMarkFuncBags [ NTYPES ];

void InitMarkFuncBags (
    UInt                type,
    TNumMarkFuncBags    mark_func )
{
  // HOOK: set mark function for type `type`.
  TabMarkFuncBags[type] = mark_func;
}

void InitSweepFuncBags (
    UInt                type,
    TNumSweepFuncBags    mark_func )
{
  // HOOK: set sweep function for type `type`.
  // This is intended for weak pointer objects.
}

static void TryMark(void *p) 
{
  jl_value_t *p2 = jl_pool_base_ptr(p);
  if (!p2)
    p2 = treap_find(bigvals, p);
  if (p2) {
    jl_gc_queue_root(p2);
  }
}

void CHANGED_BAG(Bag bag) {
  // This is the simple Julia write barrier; jl_gc_wb() is more accurate
  // but requires a pointer to the originating back, too, so we go with
  // this one for now.
  jl_gc_wb_back((void *)bag);
}

void GapRootScanner(int global) {
  syJmp_buf registers;
  sySetjmp(registers);
  for (char *p = (char *)registers; p < (char *) GapStackBottom; p += sizeof(Int)) {
    TryMark(*(void **)p);
  }
  for (Int i = 0; i < GlobalCount; i++) {
    Bag p = *GlobalAddr[i];
    if (IS_BAG_REF(p))
      jl_gc_queue_root((jl_value_t *) p);
  }
}

static jl_module_t * Module;

static inline void JMark(void *cache, void *sp, void *obj) {
  jl_gc_mark_queue_obj(cache, sp, obj);
}

void JMarkMPtr(void *cache, void *sp, void *obj) {
  JMark(cache, sp,
    *(char **)obj - sizeof(BagHeader));
}

void JMarkBag(void *cache, void *sp, void *obj);


void            InitBags (
    UInt                initial_size,
    TNumStackFuncBags   stack_func,
    Bag *               stack_bottom,
    UInt                stack_align)
{
    // HOOK: initialization happens here.
    jl_extend_init();
    jl_gc_enable(0); /// DEBUGGING
    Module = jl_new_module(jl_symbol("ForeignGAP"));
    datatype_mptr = jl_new_foreign_type(jl_symbol("Bag"),
      Module, NULL, JMarkMPtr, NULL);
    datatype_bag = jl_new_foreign_type(jl_symbol("BagInner"),
      Module, NULL, JMarkBag, NULL);
    GapStackBottom = stack_bottom;
    GapStackAlign = stack_align;
    JuliaTLS = jl_extend_get_ptls_states();
    jl_root_scanner_hook = GapRootScanner;
    jl_nonpool_alloc_hook = alloc_bigval;
    jl_nonpool_free_hook = free_bigval;
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

static inline Bag AllocateMasterPointer(void) {
  // HOOK: Allocate memory for the master pointer.
  // Master pointers require one word of memory.
  void *result = (void *) jl_gc_alloc(JuliaTLS,
    sizeof(void *), datatype_mptr);
  return result;
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
  GlobalAddr[GlobalCount] = addr;
  GlobalCookie[GlobalCount] = cookie;
  GlobalCount++;
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

static void *JCache;
static void *JSp;

static inline void MarkSlot(Bag bag, int slot)
{
    if (IS_BAG_REF(bag[slot])) JMark(JCache, JSp, bag[slot]);
}


void MarkNoSubBags( Bag bag )
{
}

void MarkOneSubBags( Bag bag )
{
    MarkSlot(bag, 0);
}

void MarkTwoSubBags( Bag bag )
{
    MarkSlot(bag, 0);
    MarkSlot(bag, 1);
}

void MarkThreeSubBags( Bag bag )
{
    MarkSlot(bag, 0);
    MarkSlot(bag, 1);
    MarkSlot(bag, 2);
}

void MarkFourSubBags( Bag bag )
{
    MarkSlot(bag, 0);
    MarkSlot(bag, 1);
    MarkSlot(bag, 2);
    MarkSlot(bag, 3);
}

void MarkAllSubBags( Bag bag )
{
    BagHeader *hdr = (BagHeader *)bag - 1;
    UInt i, size = hdr->size / sizeof(Bag);
    for (i = 0; i < size; i++) {
	MarkSlot(bag, i);
    }
}

void MarkBagWeakly( Bag bag )
{
    MarkAllSubBags(bag);
}

void MarkArrayOfBags( const Bag array[], UInt count )
{
    UInt i;
    for (i = 0; i < count; i++) {
      MarkSlot((Bag) (array[i]), 0);
    }
}

void JMarkBag(void *cache, void *sp, void *obj)
{
  JCache = cache;
  JSp = sp;
  BagHeader *hdr = (BagHeader *)obj;
  Bag contents = (Bag)(hdr + 1);
  UInt tnum = hdr->type;
  TabMarkFuncBags[tnum](contents);
}
