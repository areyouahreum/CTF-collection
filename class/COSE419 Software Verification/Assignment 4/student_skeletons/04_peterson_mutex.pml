/*
 * 04_peterson_mutex.pml
 *
 * Two processes use Peterson's algorithm to protect the critical section.
 *
 * Peterson's algorithm uses:
 *
 *   1. wantP and wantQ:
 *        These variables indicate whether each process wants to enter
 *        the critical section.
 *
 *   2. turn:
 *        This variable breaks ties when both processes want to enter.
 *        If both want to enter, the process whose turn it is not must wait.
 *
 *
 * This model has:
 *
 *   1. Mutual exclusion:
 *        P and Q must never be in their critical sections at the same time.
 *
 *   2. Liveness / progress:
 *        If a process wants to enter its critical section,
 *        then it should eventually enter it.
 *
 *
 * Expected verification results:
 *
 *   - The mutex property should PASS.
 *     Peterson's algorithm prevents the two processes from entering
 *     the critical section simultaneously.
 *
 *   - The liveness property may FAIL without fairness.
 *     Without any fairness assumption, SPIN can construct unfair executions
 *     where one enabled process is ignored forever by the scheduler.
 *
 *   - The liveness property should PASS with SPIN weak fairness.
 *     Peterson's algorithm is starvation-free under weak process fairness.
 *
 *
 * Verification commands
 * ---------------------
 *
 * Step 1: Generate the verifier.
 *
 *     spin -a 04_peterson_mutex.pml
 *
 * Step 2: Compile the verifier.
 *
 *     gcc -O2 -o pan pan.c
 *
 * Important:
 *
 *     Do NOT compile with -DSAFETY when checking liveness.
 *     The -DSAFETY option disables cycle detection, including the
 *     acceptance-cycle search needed for LTL liveness checking.
 *
 *
 * Check mutex
 * -----------
 *
 *     ./pan -a -N mutex
 *
 * Expected result:
 *
 *     errors: 0
 *
 * Meaning:
 *
 *     There is no execution where both P@critP and Q@critQ hold
 *     at the same time.
 *
 *
 * Check liveness
 * --------------
 *
 * Fill in the liveness property in the model, replacing the "FIXME" placeholders.
 *
 * Without weak fairness:
 *
 *     ./pan -a -N liveness
 *
 * Expected result:
 *
 *     errors: 1
 *
 * Meaning:
 *
 *     SPIN may find an unfair execution where an enabled process is never
 *     scheduled.  This is a scheduler-fairness issue, not a Peterson
 *     mutual-exclusion error.
 *
 *
 * With SPIN weak fairness:
 *
 *     ./pan -a -f -N liveness
 *
 * Expected result:
 *
 *     errors: 0
 *
 * Meaning:
 *
 *     Under weak fairness, an enabled process cannot be ignored forever.
 *     Peterson's algorithm then guarantees that a process that wants to
 *     enter the critical section will eventually enter it.
 *
 *
 * Why weak fairness is enough here
 * --------------------------------
 *
 *     In Peterson's algorithm, if both processes want to enter, the turn
 *     variable gives priority to one process.
 *
 *     The process with priority becomes continuously enabled to enter
 *     the critical section.  Therefore, SPIN weak fairness is sufficient:
 *     a continuously enabled process must eventually execute.
 *
 *     Unlike the simple binary semaphore model, Peterson's algorithm does
 *     not need an explicit strong fairness assumption for starvation freedom.
 *
 *
 * Replay the counterexample trail
 * -------------------------------
 *
 * Run this after a failing verification run:
 *
 *     spin -t -p -g 04_peterson_mutex.pml
 *
 * Notes:
 *
 *     - If you run another verification after the failing one,
 *       the .trail file may be overwritten.
 *
 *     - A liveness failure without -f usually represents an unfair
 *       scheduling execution.
 */

bool wantP = false;
bool wantQ = false;

/*
 * turn == 0 means it is P's turn.
 * turn == 1 means it is Q's turn.
 */
byte turn = 0;

#define P_TURN 0
#define Q_TURN 1

active proctype P() {
    do
    :: wantP = true;

       /*
        * Peterson entry protocol for P:
        *
        * P announces that it wants to enter, then gives priority to Q.
        * If Q also wants to enter and it is Q's turn, P waits.
        */
       turn = Q_TURN;

waitP:
       (!wantQ || turn == P_TURN); /* can enter if Q doesn't want to enter, or if it's P's turn */

critP: skip;        /* P's critical section */

       /*
        * Peterson exit protocol for P:
        *
        * P announces that it no longer wants to enter.
        */
       wantP = false
    od
}

active proctype Q() {
    do
    :: wantQ = true;

       /*
        * Peterson entry protocol for Q:
        *
        * Q announces that it wants to enter, then gives priority to P.
        * If P also wants to enter and it is P's turn, Q waits.
        */
       turn = P_TURN;

waitQ:
       (!wantP || turn == Q_TURN); /* can enter if P doesn't want to enter, or if it's Q's turn */

critQ: skip;        /* Q's critical section */

       /*
        * Peterson exit protocol for Q:
        *
        * Q announces that it no longer wants to enter.
        */
       wantQ = false
    od
}

/*
 * Mutex property:
 *
 * It is always false that both processes are at their critical-section
 * labels at the same time.
 *
 * This is a safety property.
 */
ltl mutex {
    [] !(P@critP && Q@critQ)
}

/*
 * Liveness property:
 *
 * If P wants to enter, then P must eventually reach critP.
 * If Q wants to enter, then Q must eventually reach critQ.
 *
 * For Peterson's algorithm, this property should hold under SPIN weak
 * fairness, checked with:
 *
 *     ./pan -a -f -N liveness
 */
ltl liveness {
    ( [] (wantP -> <> P@critP) )
    &&
    ( [] (wantQ -> <> Q@critQ) )
}

