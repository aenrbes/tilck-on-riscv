/* SPDX-License-Identifier: BSD-2-Clause */

#pragma once
#include <tilck/common/basic_defs.h>

void
insertion_sort_ptr(void *arr, u32 elem_count, cmpfun_ptr cmp);

void
insertion_sort_generic(void *a, uptr elem_size, u32 elem_count, cmpfun_ptr cmp);
