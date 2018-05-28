/****************************************************************************
**
*W  julia_gc.c
**
**  This file stores code only required by the Julia garbage collector
**
**  The definitions of methods in this file can be found in gasman.h,
**  where the non-Julia versions of these methods live. See also boehm_gc.c
**  and gasman.c for two other garbage collector implementations.
**/

#include "code.h"
#include "funcs.h"
#include "gapstate.h"
#include "gasman.h"
#include "objects.h"
#include "plist.h"
#include "sysmem.h"
#include "system.h"
#include "vars.h"
#include "fibhash.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "julia.h"
#include "julia_gcext.h"

#define MARK_CACHE_BITS 16
#define MARK_CACHE_SIZE (1 << MARK_CACHE_BITS)

#define MARK_HASH(x) (FibHash((x), MARK_CACHE_BITS))

// #define STAT_MARK_CACHE

// The MarkCache exists to speed up the conservative tracing of
// objects. While its performance benefit is minimal with the current
// API functionality, it can significantly reduce overhead if a slower
// conservative mechanism is used. It should be disabled for precise
// object tracing, however. The cache does not affect conservative
// *stack* tracing at all, only conservative tracing of objects.

static Bag MarkCache[MARK_CACHE_SIZE];
#ifdef STAT_MARK_CACHE
static UInt MarkCacheHits, MarkCacheAttempts, MarkCacheCollisions;
#endif


enum { NTYPES = 256 };

TNumInfoBags InfoBags[NTYPES];

UInt SizeAllBags;

static inline Bag * DATA(BagHeader * bag)
{
    return (Bag *)(((char *)bag) + sizeof(BagHeader));
}


/****************************************************************************
**
*F  InitFreeFuncBag(<type>,<free-func>)
*/

TNumFreeFuncBags TabFreeFuncBags[NTYPES];

void InitFreeFuncBag(UInt type, TNumFreeFuncBags finalizer_func)
{
    TabFreeFuncBags[type] = finalizer_func;
}

void JFinalizer(void * obj)
{
    BagHeader * hdr = (BagHeader *)obj;
    Bag         contents = (Bag)(hdr + 1);
    UInt        tnum = hdr->type;
    GAP_ASSERT(TabFreeFuncBags[tnum] != 0);
    TabFreeFuncBags[tnum]((Bag)&contents);
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

static inline int cmp_ptr(void * p, void * q)
{
    uintptr_t paddr = (uintptr_t)p;
    uintptr_t qaddr = (uintptr_t)q;
    if (paddr < qaddr)
        return -1;
    else if (paddr > qaddr)
        return 1;
    else
        return 0;
}

static inline int lt_ptr(void * a, void * b)
{
    return (uintptr_t)a < (uintptr_t)b;
}

#if 0
static inline int gt_ptr(void * a, void * b)
{
    return (uintptr_t)a > (uintptr_t)b;
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
#endif

/* align pointer to full word if mis-aligned */
static inline void * align_ptr(void * p)
{
    uintptr_t u = (uintptr_t)p;
    u &= ~(sizeof(p) - 1);
    return (void *)u;
}

typedef struct treap_t {
    struct treap_t *left, *right;
    size_t          prio;
    void *          addr;
    size_t          size;
} treap_t;

static treap_t * treap_free_list;

treap_t * alloc_treap(void)
{
    treap_t * result;
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

void free_treap(treap_t * t)
{
    t->right = treap_free_list;
    treap_free_list = t;
}

static inline int test_bigval_range(treap_t * node, void * p)
{
    char * l = node->addr;
    char * r = l + node->size;
    if (lt_ptr(p, l))
        return -1;
    if (!lt_ptr(p, r))
        return 1;
    return 0;
}


#define L(t) ((t)->left)
#define R(t) ((t)->right)

static inline void treap_rot_right(treap_t ** treap)
{
    /*       t                 l       */
    /*     /   \             /   \     */
    /*    l     r    -->    a     t    */
    /*   / \                     / \   */
    /*  a   b                   b   r  */
    treap_t * t = *treap;
    treap_t * l = L(t);
    treap_t * a = L(l);
    treap_t * b = R(l);
    L(l) = a;
    R(l) = t;
    L(t) = b;
    *treap = l;
}

static inline void treap_rot_left(treap_t ** treap)
{
    /*     t                   r       */
    /*   /   \               /   \     */
    /*  l     r    -->      t     b    */
    /*       / \           / \         */
    /*      a   b         l   a        */
    treap_t * t = *treap;
    treap_t * r = R(t);
    treap_t * a = L(r);
    treap_t * b = R(r);
    L(r) = t;
    R(r) = b;
    R(t) = a;
    *treap = r;
}

static void * treap_find(treap_t * treap, void * p)
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

static void treap_insert(treap_t ** treap, treap_t * val)
{
    treap_t * t = *treap;
    if (t == NULL) {
        L(val) = NULL;
        R(val) = NULL;
        *treap = val;
    }
    else {
        int c = cmp_ptr(val->addr, t->addr);
        if (c < 0) {
            treap_insert(&L(t), val);
            if (L(t)->prio > t->prio) {
                treap_rot_right(treap);
            }
        }
        else if (c > 0) {
            treap_insert(&R(t), val);
            if (R(t)->prio > t->prio) {
                treap_rot_left(treap);
            }
        }
    }
}

static void treap_delete_node(treap_t ** treap)
{
    for (;;) {
        treap_t * t = *treap;
        if (L(t) == NULL) {
            *treap = R(t);
            free_treap(t);
            break;
        }
        else if (R(t) == NULL) {
            *treap = L(t);
            free_treap(t);
            break;
        }
        else {
            if (L(t)->prio > R(t)->prio) {
                treap_rot_right(treap);
                treap = &R(*treap);
            }
            else {
                treap_rot_left(treap);
                treap = &L(*treap);
            }
        }
    }
}

static int treap_delete(treap_t ** treap, void * addr)
{
    while (*treap != NULL) {
        int c = cmp_ptr(addr, (*treap)->addr);
        if (c == 0) {
            treap_delete_node(treap);
            return 1;
        }
        else if (c < 0) {
            treap = &L(*treap);
        }
        else {
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
    return x * (uint64_t)0x2545F4914F6CDD1DUL;
}


static treap_t * bigvals;

void * alloc_bigval(size_t size)
{
    void * result = malloc(size);
    memset(result, 0, size);
    treap_t * node = alloc_treap();
    node->addr = result;
    node->size = size;
    node->prio = xorshift_rng();
    treap_insert(&bigvals, node);
    return result;
}

void free_bigval(void * p)
{
    if (p) {
        treap_delete(&bigvals, p);
        free(p);
    }
}

static jl_module_t *   Module;
static jl_datatype_t * datatype_mptr;
static jl_datatype_t * datatype_bag;
static jl_datatype_t * datatype_largebag;
static void *          GapStackBottom = NULL;
static size_t          GapStackAlign = sizeof(Int);
static void *          JContext[JL_GC_CONTEXT_SIZE];
static size_t          max_pool_obj_size;
static size_t          bigval_startoffset;
static UInt            YoungRef;
static int             OldObj;


#ifndef NR_GLOBAL_BAGS
#define NR_GLOBAL_BAGS 20000L
#endif

static Bag *        GlobalAddr[NR_GLOBAL_BAGS];
static const Char * GlobalCookie[NR_GLOBAL_BAGS];
static Int          GlobalCount;


/****************************************************************************
**
*F  AllocateBagMemory( <type>, <size> )
**
**  Allocate memory for a new bag.
**/
static void * AllocateBagMemory(UInt type, UInt size)
{
    // HOOK: return `size` bytes memory of TNUM `type`.
    void * result;
    if (size <= max_pool_obj_size) {
        result = (void *)jl_gc_alloc_typed(JContext, size, datatype_bag);
    }
    else {
        result =
            (void *)jl_gc_alloc_typed(JContext, size, datatype_largebag);
    }
    memset(result, 0, size);
    if (TabFreeFuncBags[type])
        jl_gc_set_needs_foreign_finalizer((jl_value_t *)result);
    return result;
}

TNumMarkFuncBags TabMarkFuncBags[NTYPES];

void InitMarkFuncBags(UInt type, TNumMarkFuncBags mark_func)
{
    // HOOK: set mark function for type `type`.
    TabMarkFuncBags[type] = mark_func;
}

static inline int JMark(void * obj)
{
    return jl_gc_mark_queue_obj(JContext, obj);
}

static void TryMark(void * p)
{
    jl_value_t * p2 = jl_gc_internal_obj_base_ptr(p);
    if (!p2) {
        // It is possible for p to point past the end of
        // the object, so we subtract one word from the
        // address. This is safe, as the object is preceded
        // by a larger header.
        p2 = treap_find(bigvals, (char *)p - 1);
        if (p2) {
            // It is possible for types to not be valid objects.
            // Objects with such types are not normally made visible
            // to the mark loop, so we need to avoid marking them
            // during conservative stack scanning.
            // While jl_gc_internal_obj_base_ptr(p) already eliminates this
            // case, it can still happen for bigval_t objects, so
            // we run an explicit check that the type is a valid
            // object for these.
            p2 = (jl_value_t *)((char *)p2 + bigval_startoffset);
            jl_taggedvalue_t * hdr = jl_astaggedvalue(p2);
            if (hdr->type != jl_gc_internal_obj_base_ptr(hdr->type))
                return;
        }
    } else {
	if (jl_typeis(p2, datatype_mptr))
	    MarkCache[MARK_HASH((UInt)p2)] = (Bag) p2;
    }
    if (p2) {
        JMark(p2);
    }
}

static void TryMarkRange(void * start, void * end)
{
    if (lt_ptr(end, start)) {
        SWAP(void *, start, end);
    }
    char * p = align_ptr(start);
    char * q = (char *) end - sizeof(void *) + GapStackAlign;
    while (lt_ptr(p, q)) {
        TryMark(*(void **)p);
        p += GapStackAlign;
    }
}

int IsGapObj(void * p)
{
    return jl_typeis(p, datatype_mptr);
}

void CHANGED_BAG(Bag bag)
{
    jl_gc_wb_back(BAG_HEADER(bag));
}

static void MarkStackFrames(Bag frame)
{
    for (; frame; frame = PARENT_LVARS(frame)) {
        JMark(frame);
        JMark(BAG_HEADER(frame));
    }
}

void GapRootScanner(int full)
{
    // mark our Julia module (this contains references to our custom data
    // types, which thus also will not be collected prematurely)
    JMark(Module);

    // scan the stack for further object references, and mark them
    syJmp_buf registers;
    sySetjmp(registers);
    TryMarkRange(registers, (char *)registers + sizeof(syJmp_buf));
    TryMarkRange((char *)registers + sizeof(syJmp_buf), GapStackBottom);

    // mark all global objects
    for (Int i = 0; i < GlobalCount; i++) {
        Bag p = *GlobalAddr[i];
        if (IS_BAG_REF(p)) {
            JMark(p);
        }
    }

    // scan the GAP call stack, too
    // FIXME: is this really necessary? STATE(CurrLVars) is already marked as
    // a global object (via GlobalAddr above), and it is the head of a linked
    // list containing the others, so it should not be necessary (and a quick
    // test confirms this
    MarkStackFrames(STATE(CurrLVars));
}

void GapTaskScanner(jl_task_t *task, int root_task)
{
    if (task->stkbuf) {
       TryMarkRange(task->stkbuf, (char *)task->stkbuf + task->bufsz);
    }
}

static void PreGCHook(int full)
{
    /* information at the beginning of garbage collections                 */
    SyMsgsBags(full, 0, 0);
    memset(MarkCache, 0, sizeof(MarkCache));
#ifdef STAT_MARK_CACHE
    MarkCacheHits = MarkCacheAttempts = MarkCacheCollisions = 0;
#endif
}

static void PostGCHook(int full)
{
    /* information at the end of garbage collections                 */
    UInt totalAlloc = 0;    // FIXME -- is this data even available?
    SyMsgsBags(full, 6, totalAlloc);
#ifdef STAT_MARK_CACHE
    /* printf("\n>>>Attempts: %ld\nHit rate: %lf\nCollision rate: %lf\n",
      (long) MarkCacheAttempts,
      (double) MarkCacheHits/(double)MarkCacheAttempts,
      (double) MarkCacheCollisions/(double)MarkCacheAttempts
      ); */
#endif
}

// helper function to test if Julia considers an object to
// be in the old generation
static inline int GcOld(void * p)
{
    return (jl_astaggedvalue(p)->bits.gc & 2) != 0;
}

// the Julia marking function for master pointer objects (i.e., this function
// is called by the Julia GC whenever it marks a GAP master pointer object)
static void JMarkMPtr(void * obj)
{
    if (!*(void **)obj)
        return;
    if (JMark(BAG_HEADER(obj)) && GcOld(obj))
        jl_gc_mark_push_remset(JContext, obj, 1);
}

// the Julia marking function for bags (i.e., this function is called by the
// Julia GC whenever it marks a GAP bag object)
static void JMarkBag(void * obj)
{
    BagHeader * hdr = (BagHeader *)obj;
    Bag         contents = (Bag)(hdr + 1);
    UInt        tnum = hdr->type;
    YoungRef = 0;
    OldObj = GcOld(obj);
    TabMarkFuncBags[tnum]((Bag)&contents);
    if (OldObj && YoungRef)
        jl_gc_mark_push_remset(JContext, obj, YoungRef);
}

void JMarkFrom(void * parent, void * ref)
{
    if (JMark(ref) && GcOld(parent))
        jl_gc_mark_push_remset(JContext, parent, 1);
}

static void SetJuliaContext(int tid, int index, void *data)
{
    if (tid > 0)
      return;
    JContext[index] = data;
}


void InitBags(UInt initial_size, Bag * stack_bottom, UInt stack_align)
{
    // HOOK: initialization happens here.
    jl_set_gc_root_scanner_hook(GapRootScanner);
    jl_set_gc_task_scanner_hook(GapTaskScanner);
    jl_set_gc_external_obj_alloc_hook(alloc_bigval);
    jl_set_gc_external_obj_free_hook(free_bigval);
    jl_set_pre_gc_hook(PreGCHook);
    jl_set_post_gc_hook(PostGCHook);
    jl_set_gc_context_hook(SetJuliaContext);

    for (UInt i = 0; i < NTYPES; i++)
        TabMarkFuncBags[i] = MarkAllSubBags;
    jl_extend_init();
    // jl_gc_enable(0); /// DEBUGGING
    max_pool_obj_size = jl_gc_max_internal_obj_size();

    Module = jl_new_module(jl_symbol("ForeignGAP"));
    Module->parent = jl_main_module;
    jl_set_const(jl_main_module, jl_symbol("ForeignGAP"),
                 (jl_value_t *)Module);
    datatype_mptr = jl_new_foreign_type(jl_symbol("MPtr"), Module,
                                        jl_any_type, JMarkMPtr, NULL, 1, 0);
    datatype_bag = jl_new_foreign_type(jl_symbol("Bag"), Module, jl_any_type,
                                       JMarkBag, JFinalizer, 1, 0);
    datatype_largebag =
        jl_new_foreign_type(jl_symbol("LargeBag"), Module, jl_any_type,
                            JMarkBag, JFinalizer, 1, 1);

    // export datatypes to Julia level
    jl_set_const(Module, jl_symbol("MPtr"), (jl_value_t *)datatype_mptr);
    jl_set_const(Module, jl_symbol("Bag"), (jl_value_t *)datatype_bag);
    jl_set_const(Module, jl_symbol("LargeBag"), (jl_value_t *)datatype_largebag);

    void * tmp = AllocateBagMemory(T_STRING, max_pool_obj_size + 1);
    void * tmpstart = treap_find(bigvals, tmp);
    bigval_startoffset = (char *)tmp - (char *)tmpstart;
    GAP_ASSERT(jl_is_datatype(datatype_mptr));
    GAP_ASSERT(jl_is_datatype(datatype_bag));
    GAP_ASSERT(jl_is_datatype(datatype_largebag));
    GapStackBottom = stack_bottom;
    GapStackAlign = stack_align;
}

UInt CollectBags(UInt size, UInt full)
{
    // HOOK: perform a garbage collection
    jl_gc_collect(full);
    return 1;
}

void RetypeBag(Bag bag, UInt new_type)
{
    BagHeader * header = BAG_HEADER(bag);

#ifdef COUNT_BAGS
    /* update the statistics      */
    {
        UInt old_type; /* old type of the bag */
        UInt size;

        old_type = header->type;
        size = header->size;
        InfoBags[old_type].nrLive -= 1;
        InfoBags[new_type].nrLive += 1;
        InfoBags[old_type].nrAll -= 1;
        InfoBags[new_type].nrAll += 1;
        InfoBags[old_type].sizeLive -= size;
        InfoBags[new_type].sizeLive += size;
        InfoBags[old_type].sizeAll -= size;
        InfoBags[new_type].sizeAll += size;
    }
#endif

    header->type = new_type;
}

Bag NewBag(UInt type, UInt size)
{
    Bag  bag; /* identifier of the new bag       */
    UInt alloc_size;

    alloc_size = sizeof(BagHeader) + size;

    SizeAllBags += size;

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

    BagHeader * header = AllocateBagMemory(type, alloc_size);

    header->type = type;
    header->flags = 0;
    header->size = size;

    // allocate the new masterpointer
    bag = jl_gc_alloc_typed(JContext, sizeof(void *), datatype_mptr);
    SET_PTR_BAG(bag, DATA(header));

    // return the identifier of the new bag
    return bag;
}

UInt ResizeBag(Bag bag, UInt new_size)
{
    BagHeader * header = BAG_HEADER(bag);
    UInt        old_size = header->size;

#ifdef COUNT_BAGS
    // update the statistics
    InfoBags[header->type].sizeLive += new_size - old_size;
    InfoBags[header->type].sizeAll += new_size - old_size;
#endif

    // if the bag is enlarged
    if (new_size > old_size) {
        SizeAllBags += new_size;
        UInt alloc_size = sizeof(BagHeader) + new_size;
        // if size is zero, increment by 1; see NewBag for an explanation
        if (new_size == 0)
            alloc_size++;

        // allocate new bag
        header = AllocateBagMemory(header->type, alloc_size);

        // copy bag header and data, and update size
        memcpy(header, BAG_HEADER(bag), sizeof(BagHeader) + old_size);

        // update the master pointer
        SET_PTR_BAG(bag, DATA(header));
        jl_gc_wb_back((void *)bag);
    }

    // update the size
    header->size = new_size;

    // return success
    return 1;
}

void InitGlobalBag(Bag * addr, const Char * cookie)
{
    // HOOK: Register global root.
    GAP_ASSERT(GlobalCount < NR_GLOBAL_BAGS);
    GlobalAddr[GlobalCount] = addr;
    GlobalCookie[GlobalCount] = cookie;
    GlobalCount++;
}

void SwapMasterPoint(Bag bag1, Bag bag2)
{
    Obj * ptr1 = PTR_BAG(bag1);
    Obj * ptr2 = PTR_BAG(bag2);
    SET_PTR_BAG(bag1, ptr2);
    SET_PTR_BAG(bag2, ptr1);

    jl_gc_wb((void *)bag1, BAG_HEADER(bag1));
    jl_gc_wb((void *)bag2, BAG_HEADER(bag2));
}

// HOOK: mark functions

inline void MarkBag(Bag bag)
{
    if (IS_BAG_REF(bag)) {
        jl_value_t * p = (jl_value_t *)bag;
#ifdef STAT_MARK_CACHE
	MarkCacheAttempts++;
#endif
        UInt hash = MARK_HASH((UInt) bag);
	if (MarkCache[hash] == bag) {
#ifdef STAT_MARK_CACHE
            MarkCacheHits++;
#endif
	} else
        if (!jl_gc_is_internal_obj_alloc(p) || !jl_typeis(p, datatype_mptr)) {
	    return;
	}
#ifdef STAT_MARK_CACHE
	if (MarkCache[hash])
	    MarkCacheCollisions++;
#endif
	MarkCache[hash] = bag;
	switch (jl_astaggedvalue(p)->bits.gc) {
	case 0:
	    if (JMark(p) && OldObj)
		YoungRef++;
	    break;
	case 1:
	    if (OldObj)
		YoungRef++;
	    break;
	case 2:
	    JMark(p);
	case 3:
	    break;
	}
    }
}

inline void MarkArrayOfBags(const Bag array[], UInt count)
{
    for (UInt i = 0; i < count; i++) {
        MarkBag(array[i]);
    }
}

void MarkNoSubBags(Bag bag)
{
}

void MarkOneSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag), 1);
}

void MarkTwoSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag), 2);
}

void MarkThreeSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag), 3);
}

void MarkFourSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag), 4);
}

void MarkAllSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag), SIZE_BAG(bag) / sizeof(Bag));
}

void MarkAllButFirstSubBags(Bag bag)
{
    MarkArrayOfBags(CONST_PTR_BAG(bag) + 1, SIZE_BAG(bag) / sizeof(Bag) - 1);
}
