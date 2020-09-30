/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * This is a TEMPLATE. The actual config file is generated by CMake and stored
 * in <BUILD_DIR>/tilck_gen_headers/.
 */


#pragma once

#define KB (1024u)
#define MB (1024u * 1024u)

#define VER_MAJOR              @tilck_VERSION_MAJOR@
#define VER_MINOR              @tilck_VERSION_MINOR@
#define VER_PATCH              @tilck_VERSION_PATCH@

#define VER_MAJOR_STR          "@tilck_VERSION_MAJOR@"
#define VER_MINOR_STR          "@tilck_VERSION_MINOR@"
#define VER_PATCH_STR          "@tilck_VERSION_PATCH@"

#define ARCH_GCC_TC            "@ARCH_GCC_TC@"
#define PROJ_BUILD_DIR         "@CMAKE_BINARY_DIR@"
#define BUILDTYPE_STR          "@CMAKE_BUILD_TYPE@"

#define DEVSHELL_PATH          "@TILCK_DEVSHELL_PATH@"

#define KERNEL_STACK_PAGES     @KERNEL_STACK_PAGES@
#define KERNEL_PADDR           @KERNEL_PADDR@
#define KERNEL_BASE_VA         @KERNEL_BASE_VA@
#define LINEAR_MAPPING_MB      @LINEAR_MAPPING_MB@

/* --------- Boolean config variables --------- */

#cmakedefine01 FAT_TEST_DIR
#cmakedefine01 DEBUG_CHECKS
#cmakedefine01 TINY_KERNEL
#cmakedefine01 KERNEL_GCOV       /* Used for KERNEL_MAX_SIZE */

/* ----------- Convenience defines ------------ */

#if DEBUG_CHECKS
   #ifdef NDEBUG
      #undef NDEBUG
   #endif
#endif

#ifdef KERNEL_TEST
   #define KERNEL_TEST_INT 1
#else
   #define KERNEL_TEST_INT 0
#endif

#ifdef TILCK_RELEASE_BUILD
   #define IS_RELEASE_BUILD 1
#else
   #define IS_RELEASE_BUILD 0
#endif

/* ----------- Derived constants ----------- */

#if defined(TESTING) || defined(KERNEL_TEST)

   extern void *kernel_va;

   /* For the unit tests, we need to override the following defines */
   #undef KERNEL_BASE_VA
   #undef LINEAR_MAPPING_MB

   #define KERNEL_BASE_VA             ((ulong)kernel_va)
   #define LINEAR_MAPPING_MB          (128u)

#endif

#define LINEAR_MAPPING_SIZE        (LINEAR_MAPPING_MB << 20)
#define LINEAR_MAPPING_END         (KERNEL_BASE_VA + LINEAR_MAPPING_SIZE)

/* Constants that have no reason to be changed */
#define FREE_MEM_POISON_VAL    0xFAABCAFE

/*
 * ----------- User tasks constants -----------
 *
 * WARNING: some of them are NOT really "configurable" without having to modify
 * a lot of code. Think about the potential implications changing the following
 * constants or, worse, before promoting them to be configurable as CMake
 * variables.
 */
#define USER_ARGS_PAGE_COUNT                                    1
#define MAX_TTYS                                                9
#define MAX_PATH                                              256
#define MAX_PID                                              8191
