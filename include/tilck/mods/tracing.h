/* SPDX-License-Identifier: BSD-2-Clause */

#pragma once
#include <tilck/common/basic_defs.h>

enum trace_event_type {
   te_invalid = 0,
   te_sys_enter = 1,
   te_sys_exit = 2,
};

struct trace_event {

   enum trace_event_type type;
   int tid;

   u64 sys_time;

   u32 sys;
   sptr retval;
   uptr args[6];

   union {

      struct {
         char d0[64];
         char d1[64];
         char d2[32];
         char d3[16];
      } fmt1;

      struct {
         char d0[128];
         char d1[32];
         char d2[16];
      } fmt2;
   };
};

STATIC_ASSERT(sizeof(struct trace_event) <= 256);

enum sys_param_kind {
   sys_param_in,
   sys_param_out,
   sys_param_in_out,
};

struct sys_param_info {

   const char *name;

   /* IN, OUT or IN/OUT */
   enum sys_param_kind kind;

   /* slot in fmt1 or fmt2 where to save its info during tracing */
   u8 slot;

   /* Returns false if buf_size is too small */
   bool (*save)(void *ptr, char *buf, size_t buf_size);

   /* Returns false if dest_buf_size is too small */
   bool (*dump)(char *buf, char *dest, size_t dest_buf_size);
};

enum sys_ret_type {

   sys_ret_type_fd_or_errno,
   sys_ret_type_errno,
   sys_ret_type_ptr,
};

enum sys_saved_param_fmt {
   sys_fmt1,
   sys_fmt2,
};

struct syscall_info {

   /* syscall number */
   u32 sys_n;

   /* number of parameters */
   int n_params;

   /* return type of the syscall */
   enum sys_ret_type ret_type;

   /* format used for saving the paramaters during tracing */
   enum sys_saved_param_fmt pfmt;

   /* info about its parameters */
   struct sys_param_info params[6];
};

void
init_tracing(void);

bool
read_trace_event(struct trace_event *e, u32 timeout_ticks);

void
trace_syscall_enter(u32 sys,
                    uptr a1, uptr a2, uptr a3, uptr a4, uptr a5, uptr a6);
void
trace_syscall_exit(u32 sys, sptr retval,
                   uptr a1, uptr a2, uptr a3, uptr a4, uptr a5, uptr a6);

const char *
tracing_get_syscall_name(u32 n);
