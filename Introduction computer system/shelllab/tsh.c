/*
 * tsh - A tiny shell program with job control
 * <The line above is not a sufficient documentation.
 *  You will need to write your program documentation.
 *  Follow the 15-213/18-213/15-513 style guide at
 *  http://www.cs.cmu.edu/~213/codeStyle.html.>
 *  Full name: Shu Liu
 *  Andrew ID: shul2
 */

#include "tsh_helper.h"

/*
 * If DEBUG is defined, enable contracts and printing on dbg_printf.
 */
#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Function prototypes */
void eval(const char *cmdline);

void sigchld_handler(int sig);
void sigtstp_handler(int sig);
void sigint_handler(int sig);
void sigquit_handler(int sig);

//volatile sig_atomic_t pid;

/* Job states */
#define OTH 0 /* other */
#define FG  1 /* running in foreground */
#define BG  2 /* running in background */
#define ST  3 /* stopped */

volatile sig_atomic_t waitFlag = 0;  // the flag for foreground is finished
volatile sig_atomic_t waitPid  = -1; // foreground pid

void lock_process(sigset_t *pmask);
int builtin_command(char ** argv);

/*
 * <Write main's function header documentation. What does main do?>
 * "Each function should be prefaced with a comment describing the purpose
 *  of the function (in a sentence or two), the function's arguments and
 *  return value, any error cases that are relevant to the caller,
 *  any pertinent side effects, and any assumptions that the function makes."
 */
int main(int argc, char **argv)
{
    char c;
    char cmdline[MAXLINE_TSH];  // Cmdline for fgets
    bool emit_prompt = true;    // Emit prompt (default)

    // Redirect stderr to stdout (so that driver will get all output
    // on the pipe connected to stdout)
    Dup2(STDOUT_FILENO, STDERR_FILENO);

    // Parse the command line
    while ((c = getopt(argc, argv, "hvp")) != EOF)
    {
        switch (c)
        {
        case 'h':                   // Prints help message
            usage();
            break;
        case 'v':                   // Emits additional diagnostic info
            verbose = true;
            break;
        case 'p':                   // Disables prompt printing
            emit_prompt = false;
            break;
        default:
            usage();
        }
    }

    // Install the signal handlers
    Signal(SIGINT,  sigint_handler);   // Handles ctrl-c
    Signal(SIGTSTP, sigtstp_handler);  // Handles ctrl-z
    Signal(SIGCHLD, sigchld_handler);  // Handles terminated or stopped child

    Signal(SIGTTIN, SIG_IGN);
    Signal(SIGTTOU, SIG_IGN);

    Signal(SIGQUIT, sigquit_handler);

    // Initialize the job list
    initjobs(job_list);

    // Execute the shell's read/eval loop
    while (true)
    {
        if (emit_prompt)
        {
            printf("%s", prompt);
            fflush(stdout);
        }

        if ((fgets(cmdline, MAXLINE_TSH, stdin) == NULL) && ferror(stdin))
        {
            app_error("fgets error");
        }

        if (feof(stdin))
        {
            // End of file (ctrl-d)
            printf ("\n");
            fflush(stdout);
            fflush(stderr);
            return 0;
        }

        // Remove the trailing newline
        cmdline[strlen(cmdline)-1] = '\0';

        // Evaluate the command line
        eval(cmdline);

        fflush(stdout);
    }

    return -1; // control never reaches here
}

// functions begin
/*********************************************/
/*********************************************/
/*
 * process_command is used for the process of non-builtin command
 * include the process for the foreground and background process
 */
void process_command(struct cmdline_tokens token,
                     parseline_return parse_result,
                     const char *cmdline) {
    sigset_t mask_one, prev_one;
    int pid;

    Signal(SIGCHLD, sigchld_handler);
    Signal(SIGINT, sigint_handler);
    Signal(SIGTSTP, sigtstp_handler);

    lock_process(&mask_one);

    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);  // block SIGCHLD
    if ((pid = Fork()) == 0) {
       // child process
      setpgid(pid, 0);
      Sigprocmask(SIG_SETMASK, &prev_one, NULL);  // unblock SIGCHLD
      execve(token.argv[0], token.argv, environ);
    }

    // parent process
    // add job
    if (parse_result == PARSELINE_BG) {
      addjob(job_list, pid, BG, cmdline);
    } else if (parse_result == PARSELINE_FG) {
      addjob(job_list, pid, FG, cmdline);
    }

    // wait process
    if (parse_result == PARSELINE_FG) {
        // set global variale to
        waitFlag = 1;
        waitPid = pid;
        while (waitFlag == 1) {
          Sigsuspend(&prev_one);
        }

    } else if (parse_result == PARSELINE_BG) {
      printf("[%d] (%d) %s\n", pid2jid(job_list, pid), pid, cmdline);
    }

    Sigprocmask(SIG_SETMASK, &prev_one, NULL);

    return;
}


/* Handy guide for eval:
 *
 * If the user has requested a built-in command (quit, jobs, bg or fg),
 * then execute it immediately. Otherwise, fork a child process and
 * run the job in the context of the child. If the job is running in
 * the foreground, wait for it to terminate and then return.
 * Note: each child process must have a unique process group ID so that our
 * background children don't receive SIGINT (SIGTSTP) from the kernel
 * when we type ctrl-c (ctrl-z) at the keyboard.
 */

/*
 * eval is responsible for parsing cmdline as well as
 *   input and output redirection
 *
 */
void eval(const char *cmdline)
{
    parseline_return parse_result;
    struct cmdline_tokens token;
    int fd1, fd2, fdstdin, fdstdout;

    // Parse command line
    parse_result = parseline(cmdline, &token);

    if (parse_result == PARSELINE_ERROR || parse_result == PARSELINE_EMPTY)
    {
        return;
    }

    // redirection input
    if (token.infile != NULL) {
      if ((fd1 = open(token.infile, O_RDONLY, 0)) == -1) {
        perror("open operation error");
      }
      // store the standand input descriptor table temporaly
      fdstdin = dup(STDIN_FILENO);
      // update the newest input standand descriptor table
      dup2(fd1, STDIN_FILENO);
    }

    // redirection output
    if (token.outfile != NULL) {
      if ((fd2 = open(token.outfile, O_WRONLY, 0)) == -1) {
        perror("write operation error");
      }
      // store the standand output descriptor table temporaly
      fdstdout = dup(STDOUT_FILENO);
      // update the newest output standand descriptor table
      dup2(fd2, STDOUT_FILENO);
    }

    if (!builtin_command(token.argv)) {
      process_command(token, parse_result, cmdline);
    }

    if (token.infile != NULL) {
      close(fd1);
      // restore the standard inpout file descriptor table
      dup2(fdstdin, STDIN_FILENO);
    }

    if (token.outfile != NULL) {
      close(fd2);
      // restore the standard output file descriptor table
      dup2(fdstdout, STDOUT_FILENO);
    }

    return;
}


/*****************
 * Signal handlers
 *****************/

/*
 * sigchld_handler used for the handling of "SIGCHLD" signal
 */
void sigchld_handler(int sig)
{
  pid_t cpid;
  int status;
  sigset_t mask_one, prev_one;
  int olderrno = errno;

  lock_process(&mask_one);
  while ((cpid = waitpid(-1, &status, WUNTRACED | WNOHANG)) > 0) {

    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);  // block SIGCHLD

    if (cpid == waitPid) {
      waitFlag = 0;
    }

    if (WIFEXITED(status)) {
      // when the child terminated normally
      deletejob(job_list, cpid);
    } else if (WIFSTOPPED(status)) {
      // when the child that caused the return is currently stopped.
      struct job_t *pjob = getjobpid(job_list, cpid);
      pjob->state = ST;
      int jidnum = pid2jid(job_list, cpid);
      printf("Job [%d] (%d) stopped by signal 20\n", jidnum, cpid);
    } else if (WIFSIGNALED(status)) {
      // when the child process terminated because of
      // a signal that was not caught
      int jidnum = pid2jid(job_list, cpid);
      int signum = WTERMSIG(status);
      printf("Job [%d] (%d) terminated by signal %d\n", jidnum, cpid, signum);
      deletejob(job_list, cpid);
    }

    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
  }

  errno = olderrno;

  return;
}

/*
 * sigint_handler used for the handling of "SIGINT" signal
 */
void sigint_handler(int sig)
{

    sigset_t mask_one, prev_one;
    int olderrno = errno;

    lock_process(&mask_one);
    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
    int pid = fgpid(job_list);
    if (pid != 0) {
      Kill(-pid, SIGINT);
    }
    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
    errno = olderrno;
    return;
}

/*
 * sigtstp_handler used for the handling of "SIGTSTP" signal
 */
void sigtstp_handler(int sig)
{
    sigset_t mask_one, prev_one;
    int olderrno = errno;

    lock_process(&mask_one);
    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
    int pid = fgpid(job_list);
    if (pid != 0) {
      Kill(-pid, SIGTSTP);
    }
    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
    errno = olderrno;
    return;
}


/* helper functions */
/*
 * process_back_fore is used for processing builtin bg and fg command.
 *
 */
void process_back_fore(char ** argv) {
  int backgroundFlag = 0;
  int foregroundFlag = 0;
  int jobFlag, id;
  struct job_t *pjob;
  sigset_t mask_one, prev_one;

  if (argv == NULL) {
    return;
  }
  if (argv[1] == NULL) {
    printf("command require PID or JID argument\n");
    return;
  }

  if (!strcmp(argv[0], "bg")) {
    backgroundFlag = 1;
  } else if (!strcmp(argv[0], "fg")) {
    foregroundFlag = 1;
  }

  // parse the builtin_command
  if (!strncmp(argv[1], "%%", 1)) {
    jobFlag = 1;
  }

  lock_process(&mask_one);
  Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
  if (jobFlag) {
    id = atoi(argv[1]+1);
    pjob = getjobjid(job_list, id);
  } else {
    id = atoi(argv[1]);
    pjob = getjobpid(job_list, id);
  }
  Sigprocmask(SIG_SETMASK, &prev_one, NULL);

  // background or foreground
  if (backgroundFlag) {

    // when it is background process
    pjob->state = BG;
    Kill(-pjob->pid, SIGCONT);
    printf("[%d] (%d) %s", pjob->jid, pjob->pid, pjob->cmdline);

  } else if (foregroundFlag) {

    // when it is foreground process
    pjob->state = FG;
    lock_process(&mask_one);
    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
    // update the global variable
    waitFlag = 1;
    waitPid = pjob->pid;
    Kill(-pjob->pid, SIGCONT);
    // wait for the foreground to terminate
    while (waitFlag == 1) {
      Sigsuspend(&prev_one);
    }
    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
  }
  return;
}

/*
 * builtin_command is used for the determing whether it is
 *  the builtin_command.
 *
 */
int builtin_command(char ** argv) {
  sigset_t mask_one, prev_one;

  if (!strcmp(argv[0], "quit")) {
    exit(0);
  }
  if (!strcmp(argv[0], "jobs")) {
    lock_process(&mask_one);
    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
    listjobs(job_list, STDOUT_FILENO);
    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
    return 1;
  }
  if (!strncmp(argv[0], "bg", 2) || !strncmp(argv[0], "fg", 2)) {
    process_back_fore(argv);
    return 1;
  }
  return 0;
}

/*
 * lock_process is used for lock SIGCHLD, SIGINT, SIGTSTP
 */
void lock_process(sigset_t *pmask) {
  Sigemptyset(pmask);
  Sigaddset(pmask, SIGCHLD);
  Sigaddset(pmask, SIGINT);
  Sigaddset(pmask, SIGTSTP);
}
