/*
 * 02_too_polite_mutex_deadlock.pml
 *
 * Two processes are too polite:
 * each process first announces that it wants to enter the critical section,
 * and then waits while the other process also wants to enter.
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
 * Expected verification results:
 *
 *   - The mutex property should PASS.
 *     The two processes never enter the critical section simultaneously.
 *
 *   - The liveness property should FAIL.
 *     SPIN can find an execution where:
 *
 *         wantP == true
 *         wantQ == true
 *
 *     After that, P waits for !wantQ and Q waits for !wantP. (DEADLOCK)
 *     Therefore neither process can reach its critical-section label.
 *
 *
 * Verification commands
 * ---------------------
 *
 * Step 1: Generate the verifier.
 *
 *     spin -a 02_too_polite_mutex_deadlock.pml
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
 *     Fill in the missing part of the liveness property in the code below,
 *     and then run:
 *
 *     ./pan -a -N liveness
 *
 * Expected result:
 *
 *     errors: 1
 *
 * Meaning:
 *
 *     There is an execution where at least one process wants to enter
 *     the critical section but never reaches its critical-section label.
 *
 *
 * Replay the counterexample trail
 * -------------------------------
 *
 * Run this after a failing verification run:
 *
 *     spin -t -p -g 02_too_polite_mutex_deadlock.pml
 *
 * Notes:
 *
 *     - If you run another verification after the failing one,
 *       the .trail file may be overwritten.
 *
 *     - The liveness failure corresponds to the too-polite deadlock:
 *       P is blocked at !wantQ, and Q is blocked at !wantP.
 */

bool wantP = false;
bool wantQ = false;

active proctype P() {
    do
    :: wantP = true;
       !wantQ;

critP: skip;        /* P's critical section */

       wantP = false
    od
}

active proctype Q() {
    do
    :: wantQ = true;
       !wantP;

critQ: skip;        /* Q's critical section */

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
 * This is intentionally violated by the too-polite algorithm.
 */
ltl liveness {
    ([] (wantP -> <> P@critP ))
    && 
    ([] (wantQ -> <> Q@critQ ))
}