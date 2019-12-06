/* SPDX-License-Identifier: BSD-2-Clause */

#include <tilck/kernel/signal.h>
#include <tilck/kernel/process.h>

struct tty_and_sig_num {

   int tty_num;
   int sig_num;
};

static void tty_send_signal(int tid, int signum)
{
   send_signal(tid, signum, true);
   ASSERT(is_preemption_enabled());
}

static int per_task_cb(void *obj, void *arg)
{
   struct tty_and_sig_num *ctx = arg;
   struct tty *t = ttys[ctx->tty_num];
   struct task *ti = obj;

   if (!is_kernel_thread(ti) && ti->pi->proc_tty == t) {

      bool ok = enqueue_tasklet2(tty_tasklet_runner,
                                 tty_send_signal,
                                 ti->tid,
                                 ctx->sig_num);

      if (!ok)
         panic("Unable to enqueue tasklet for sending signal");
   }

   return 0;
}

static void tty_async_send_signal_to_fg_group(struct tty *t, int signum)
{
   struct tty_and_sig_num ctx = (struct tty_and_sig_num) {
      .tty_num = t->minor,
      .sig_num = signum,
   };

   disable_preemption();
   {
      iterate_over_tasks(per_task_cb, &ctx);
   }
   enable_preemption();
}

static bool tty_ctrl_stop(struct tty *t)
{
   if (t->c_term.c_iflag & IXON) {
      // TODO: eventually support pause transmission, one day.
      return true;
   }

   return false;
}

static bool tty_ctrl_start(struct tty *t)
{
   if (t->c_term.c_iflag & IXON) {
      // TODO: eventually support pause transmission, one day.
      return true;
   }

   return false;
}

static bool tty_ctrl_intr(struct tty *t)
{
   if (t->c_term.c_lflag & ISIG) {
      tty_keypress_echo(t, (char)t->c_term.c_cc[VINTR]);
      tty_kb_buf_reset(t);
      tty_async_send_signal_to_fg_group(t, SIGINT);
      return true;
   }

   return false;
}

static bool tty_ctrl_susp(struct tty *t)
{
   if (t->c_term.c_lflag & ISIG) {
      tty_keypress_echo(t, (char)t->c_term.c_cc[VSUSP]);
      printk("SUSP not supported yet\n");
      return true;
   }

   return false;
}

static bool tty_ctrl_quit(struct tty *t)
{
   if (t->c_term.c_lflag & ISIG) {
      tty_keypress_echo(t, (char)t->c_term.c_cc[VQUIT]);
      tty_kb_buf_reset(t);
      tty_async_send_signal_to_fg_group(t, SIGQUIT);
      return true;
   }

   return false;
}

static bool tty_ctrl_eof(struct tty *t)
{
   if (t->c_term.c_lflag & ICANON) {
      t->end_line_delim_count++;
      kb_buf_write_elem(t, t->c_term.c_cc[VEOF]);
      kcond_signal_one(&t->input_cond);
      return true;
   }

   return false;
}

static bool tty_ctrl_eol(struct tty *t)
{
   if (t->c_term.c_lflag & ICANON) {
      t->end_line_delim_count++;
      kb_buf_write_elem(t, t->c_term.c_cc[VEOL]);
      kcond_signal_one(&t->input_cond);
      return true;
   }
   return false;
}

static bool tty_ctrl_eol2(struct tty *t)
{
   if (t->c_term.c_lflag & ICANON) {
      t->end_line_delim_count++;
      kb_buf_write_elem(t, t->c_term.c_cc[VEOL2]);
      kcond_signal_one(&t->input_cond);
      return true;
   }
   return false;
}

static bool tty_ctrl_reprint(struct tty *t)
{
   if (t->c_term.c_lflag & (ICANON | IEXTEN)) {
      tty_keypress_echo(t, (char)t->c_term.c_cc[VREPRINT]);
      printk("REPRINT not supported yet\n");
      return true;
   }

   return false;
}

static bool tty_ctrl_discard(struct tty *t)
{
   /*
    * From termios' man page:
    * VDISCARD
    *     (not  in  POSIX;  not supported under Linux; 017, SI, Ctrl-O)
    *     Toggle: start/stop discarding pending output.  Recognized when
    *     IEXTEN is set, and then not passed as input.
    *
    * Since it is not supported under Linux, it won't be supported under
    * Tilck either.
    */

   return false;
}

static bool tty_ctrl_lnext(struct tty *t)
{
   if (t->c_term.c_lflag & IEXTEN) {
      printk("LNEXT not supported yet\n");
      return true;
   }

   return false;
}

static void
tty_set_ctrl_handler(struct tty *t, u8 ctrl_type, tty_ctrl_sig_func h)
{
   u8 c = t->c_term.c_cc[ctrl_type];

   if (!c) {
      /*
       * The character #num associated with the control char 'ctrl_type' is 0:
       * this means that the user doesn't what the terminal to support that
       * specific control character at all. We cannot associate any handler with
       * it.
       */
      return;
   }

   t->special_ctrl_handlers[c] = h;
}

static inline bool tty_handle_special_controls(struct tty *t, u8 c)
{
   tty_ctrl_sig_func handler = t->special_ctrl_handlers[c];

   if (handler)
      return handler(t);

   return false;
}