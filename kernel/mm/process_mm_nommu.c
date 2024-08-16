/* SPDX-License-Identifier: BSD-2-Clause */

#include <tilck_gen_headers/config_mm.h>

#include <tilck/common/basic_defs.h>
#include <tilck/common/string_util.h>
#include <tilck/common/utils.h>

#include <tilck/kernel/process.h>
#include <tilck/kernel/process_mm.h>
#include <tilck/kernel/kmalloc.h>
#include <tilck/kernel/errno.h>
#include <tilck/kernel/fs/devfs.h>
#include <tilck/kernel/syscalls.h>

#include <sys/mman.h>      // system header

void *__curr_pdir;
char page_size_buf[PAGE_SIZE] ALIGNED_AT(PAGE_SIZE);

void *sys_brk(void *new_brk)
{
   struct task *ti = get_curr_task();
   struct process *pi = ti->pi;

   if (!new_brk)
      return pi->brk;

   // TODO: check if Linux accepts non-page aligned addresses.
   // If yes, what to do? how to approx? truncation, round-up/round-down?
   if ((ulong)new_brk & OFFSET_IN_PAGE_MASK)
      return pi->brk;

   if (new_brk < pi->initial_brk)
      return pi->brk;

   if ((ulong)new_brk >= (ulong)pi->initial_brk + PAGE_SIZE)
      return pi->brk;

   if (new_brk == pi->brk)
      return pi->brk;

   /*
    * Disable preemption to avoid any threads to mess-up with the address space
    * of the current process (i.e. they might call brk(), mmap() etc.)
    */

   disable_preemption();
   pi->brk = new_brk;
   enable_preemption();
   return pi->brk;
}

static inline void
mmap_err_case_free(struct process *pi, void *ptr, size_t actual_len)
{
   task_temp_kernel_free(ptr);
}

static struct user_mapping *
mmap_on_user_heap(struct process *pi,
                  size_t *actual_len_ref,
                  fs_handle handle,
                  u32 per_heap_kmalloc_flags,
                  size_t off,
                  int prot)
{
   void *res;
   struct user_mapping *um;

   res = task_temp_kernel_alloc(*actual_len_ref);

   if (UNLIKELY(!res))
      return NULL;

   um = process_add_user_mapping(handle, res, *actual_len_ref, off, prot);

   if (UNLIKELY(!um)) {
      task_temp_kernel_free(res);
      return NULL;
   }

   return um;
}

long
sys_mmap_pgoff(void *addr, size_t len, int prot,
               int flags, int fd, size_t pgoffset)
{
   struct task *curr = get_curr_task();
   struct process *pi = curr->pi;
   struct fs_handle_base *handle = NULL;
   struct user_mapping *um = NULL;
   size_t actual_len;
   int rc, fl;

   if ((flags & MAP_PRIVATE) && (flags & MAP_SHARED))
      return -EINVAL; /* non-sense parameters */

   if (!len)
      return -EINVAL;

   if (addr)
      return -EINVAL; /* addr != NULL not supported */

   if (!(prot & PROT_READ))
      return -EINVAL;

   actual_len = pow2_round_up_at(len, PAGE_SIZE);

   if (fd == -1) {

      if (!(flags & MAP_ANONYMOUS))
         return -EINVAL;

      if (flags & MAP_SHARED)
         return -EINVAL; /* MAP_SHARED not supported for anonymous mappings */

      if (!(flags & MAP_PRIVATE))
         return -EINVAL;

      if ((prot & (PROT_READ | PROT_WRITE)) != (PROT_READ | PROT_WRITE))
         return -EINVAL;

      if (pgoffset != 0)
         return -EINVAL; /* pgoffset != 0 does not make sense here */

   } else {

      if (!(flags & MAP_SHARED))
         return -EINVAL;

      handle = get_fs_handle(fd);

      if (!handle)
         return -EBADF;

      fl = handle->fl_flags;

      if ((prot & (PROT_READ | PROT_WRITE)) == 0)
         return -EINVAL; /* nor read nor write prot */

      if ((prot & (PROT_READ | PROT_WRITE)) == PROT_WRITE)
         return -EINVAL; /* disallow write-only mappings */

      if (prot & PROT_WRITE) {
         if (!(fl & O_WRONLY) && (fl & O_RDWR) != O_RDWR)
            return -EACCES;
      }
   }

   if (!pi->mi) {
      ASSERT(!pi->mi);

      if (!(pi->mi = kalloc_obj(struct mappings_info)))
         return -ENOMEM;

      list_init(&pi->mi->mappings);
   }

   disable_preemption();
   {
      um = mmap_on_user_heap(pi,
                             &actual_len,
                             handle,
                             0,
                             pgoffset << PAGE_SHIFT,
                             prot);
   }
   enable_preemption();

   if (!um)
      return -ENOMEM;

   ASSERT(actual_len == pow2_round_up_at(len, PAGE_SIZE));

   if (handle) {

      /* First, try to get the physical address of the file */

      ulong paddr;
      ulong vaddr = um->vaddr;

      rc = vfs_mmap(um, pi->pdir, 0);
      disable_preemption();
      mmap_err_case_free(pi, um->vaddrp, actual_len);
      process_remove_user_mapping(um);

      if (rc) {
         enable_preemption();
         return rc;
      }

      paddr = get_mapping(pi->pdir, (void *)vaddr);
      vfs_munmap(um, (void *)vaddr, actual_len);

      /* Second, establish identity mapping */

      um = process_add_user_mapping(handle,
                                    (void *)paddr,
                                    actual_len,
                                    pgoffset << PAGE_SHIFT,
                                    prot);

      enable_preemption();

      if (!um) {
         return -ENOMEM;
      }

      if ((rc = vfs_mmap(um, pi->pdir, 0))) {

         disable_preemption();
         process_remove_user_mapping(um);
         enable_preemption();
         return rc;
      }

   } else {

      if (MMAP_NO_COW)
         bzero(um->vaddrp, actual_len);
   }

   return (long)um->vaddr;
}

long sys_mmap(void *addr, size_t len, int prot,
              int flags, int fd, size_t offset)
{
   if (UNLIKELY(offset & (~PAGE_MASK)))
      return -EINVAL;

   return sys_mmap_pgoff(addr, len, prot, flags, fd,
                         offset >> PAGE_SHIFT);
}

static int munmap_int(struct process *pi, void *vaddrp, size_t len)
{
   struct user_mapping *um = NULL, *um2 = NULL;
   ulong vaddr = (ulong) vaddrp;
   size_t actual_len;
   int rc;

   ASSERT(!is_preemption_enabled());

   actual_len = pow2_round_up_at(len, PAGE_SIZE);
   um = process_get_user_mapping(vaddrp);

   if (!um) {

      /*
       * We just don't have any user_mappings containing [vaddrp, vaddrp+len).
       * Just ignore that and return 0 [linux behavior].
       */

      printk("[%d] Un-map unknown chunk at [%p, %p)\n",
             pi->pid, TO_PTR(vaddr), TO_PTR(vaddr + actual_len));
      return 0;
   }

   const ulong um_vend = um->vaddr + um->len;

   if (actual_len == um->len) {

      process_remove_user_mapping(um);

   } else {

      /* partial un-map */

      if (vaddr == um->vaddr) {

         /* unmap the beginning of the chunk */
         um->vaddr += actual_len;
         um->off += actual_len;
         um->len -= actual_len;

      } else if (vaddr + actual_len == um_vend) {

         /* unmap the end of the chunk */
         um->len -= actual_len;

      } else {

         /* Unmap something at the middle of the chunk */

         /* Shrink the current struct user_mapping */
         um->len = vaddr - um->vaddr;

         /* Create a new struct user_mapping for its 2nd part */
         um2 = process_add_user_mapping(
            um->h,
            (void *)(vaddr + actual_len),
            (um_vend - (vaddr + actual_len)),
            um->off + um->len + actual_len,
            um->prot
         );

         if (!um2) {

            /*
             * Oops, we're out-of-memory! No problem, revert um->page_count
             * and return -ENOMEM. Linux is allowed to do that.
             */
            um->len = um_vend - um->vaddr;
            return -ENOMEM;
         }
      }
   }

   if (um->h) {
      rc = vfs_munmap(um, vaddrp, actual_len);

      /*
       * If there's an actual user_mapping entry, it means um->h's fops MUST
       * HAVE mmap() implemented. Therefore, we MUST REQUIRE munmap() to be
       * present as well.
       */

      ASSERT(rc != -ENODEV);
      (void) rc; /* prevent the "unused variable" Werror in release */

      if (um2)
         vfs_mmap(um2, pi->pdir, VFS_MM_DONT_MMAP);

      ASSERT(actual_len == pow2_round_up_at(len, PAGE_SIZE));
      return 0;
   }

   task_temp_kernel_free(vaddrp);
   ASSERT(actual_len == pow2_round_up_at(len, PAGE_SIZE));
   return 0;
}

int sys_munmap(void *vaddrp, size_t len)
{
   struct task *curr = get_curr_task();
   struct process *pi = curr->pi;
   int rc;

   if (!len)
      return -EINVAL;

   disable_preemption();
   {
      rc = munmap_int(pi, vaddrp, len);
   }
   enable_preemption();
   return rc;
}

