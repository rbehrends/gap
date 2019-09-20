/****************************************************************************
**
**  This file is part of GAP, a system for computational discrete algebra.
**
**  Copyright of GAP belongs to its developers, whose names are too numerous
**  to list here. Please refer to the COPYRIGHT file for details.
**
**  SPDX-License-Identifier: GPL-2.0-or-later
*/

#ifndef GAP_TLS_H
#define GAP_TLS_H

#include "system.h"

#if !defined(HPCGAP)
#error This header is only meant to be used with HPC-GAP
#endif

#include "hpc/tlsconfig.h"

typedef struct Region Region;

typedef struct ThreadLocalStorage
{
  int threadID;
  void *threadLock;
  void *threadSignal;
  void *acquiredMonitor;
  unsigned multiplexRandomSeed;
  Region * currentRegion;
  Region * threadRegion;
  Obj threadObject;
  Obj tlRecords;
  Obj lockStack;
  int lockStackPointer;
  Obj copiedObjs;
  Obj interruptHandlers;
  void *CurrentHashLock;
  int DisableGuards;

  /* From intrprtr.c */
  UInt PeriodicCheckCount;

  /* From read.c */
  syJmp_buf threadExit;

  /* From scanner.c */
  Obj DefaultOutput;
  Obj DefaultInput;

  /* Profiling */
  UInt CountActive;
  UInt LocksAcquired;
  UInt LocksContended;
} ThreadLocalStorage;

#ifdef USE_NATIVE_TLS
extern __thread ThreadLocalStorage *TLSInstance;
#endif

#ifdef USE_PTHREAD_TLS

#include <pthread.h>

#ifdef __GNUC__
// pthread_getspecific() is not defined as pure by default; redeclaring
// it as such works for gcc/clang and allows the compiler to hoist calls
// to pthread_getspecific() out of loops and perform constant
// subexpression elimination on expressions containing TLS values.
PURE_FUNC void * pthread_getspecific(pthread_key_t);
#endif

static pthread_key_t TLSKeyCopy;
pthread_key_t GetTLSKey(void);

// This constructor function will initialize the static variable for
// each C module. Making the variable static allows optimizations that
// a global non-static variable would not permit. On some architectures,
// it is also faster to access a static than a global non-static
// variable, avoiding one level of indirection.
//
// Constructor functions are executed upon program start/library load.
CONSTRUCTOR_FUNC static void InitTLSKey()
{
    TLSKeyCopy = GetTLSKey();
}
#endif

#if defined(__APPLE__) && defined(__x86_64__)
#define PTHREAD_TLS_ASM
#endif

#if defined(VERBOSE_GUARDS)
static inline ThreadLocalStorage * GetTLS(void)
#else
static ALWAYS_INLINE ThreadLocalStorage * GetTLS(void)
#endif
{
#if defined(USE_NATIVE_TLS)
    return TLSInstance;
#elif defined(USE_PTHREAD_TLS)
#ifdef USE_MACOS_PTHREAD_TLS_ASM
    long   key;
    void * p;
    key = (long)TLSKeyCopy;
    // The following inline assembly code is the same as that in
    // pthread_getspecific(). That pthread_getspecific() is actually
    // implemented in that way has been verified in the configure
    // script and resulted in defining USE_MACOS_PTHREAD_TLS_ASM.
    // If that test fails, we fall back to the standard implementation
    // of pthread_getspecific().
    asm("movq %%gs:(,%1,8), %0"
        : "=r"(p)  /* output = %0 */
        : "r"(key) /* input = %1 */
        : /* clobber = none */);
    return (ThreadLocalStorage *)p;
#else
#ifdef __GNUC__
    return (ThreadLocalStorage *)pthread_getspecific(TLSKeyCopy);
#else
    return (ThreadLocalStorage *)pthread_getspecific(GetTLSKey());
#endif
#endif /* USE_MACOS_PTHREAD_TLS_ASM */
#else
    // use stack mask approach
    void * stack;
#ifdef __GNUC__
    stack = __builtin_frame_address(0);
#else
    int dummy[1];
    stack = dummy;
#endif
    return (ThreadLocalStorage *)(((uintptr_t)stack) & TLS_MASK);
#endif /* USE_NATIVE_TLS, USE_PTHREAD_TLS */
}

// Convenience helper for accessing TLS members
#define TLS(x) GetTLS()->x

void InitializeTLS(void);

#endif // GAP_TLS_H
