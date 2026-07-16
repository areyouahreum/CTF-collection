/*
 * 03_semaphore_mutex.pml
 *
 * Two processes use a binary semaphore to protect the critical section.
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
 *   3. Liveness under strong fairness:
 *        The same liveness property is also checked under an explicit
 *        strong fairness assumption written in LTL.
 *
 * Expected verification results:
 *
 *   - The mutex property should PASS.
 *     The binary semaphore prevents the two processes from entering
 *     the critical section simultaneously.
 *
 *   - The plain liveness property should FAIL.
 *     Without a strong fairness assumption, SPIN can construct executions
 *     where one process repeatedly reacquires the semaphore and the other
 *     process starves forever.
 *
 *   - The strong-fair liveness property should PASS.
 *     Under the explicit strong fairness assumption, a process that gets
 *     infinitely many chances to acquire the semaphore must eventually
 *     enter its critical section.
 *
 *
 * Verification commands
 * ---------------------
 *
 * Step 1: Generate the verifier.
 *
 *     spin -a 03_semaphore_mutex.pml
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
 *
 * Check plain liveness
 * --------------------
 * 
 * First, fill in the liveness property in the model, replacing the "FIXME" placeholder.
 *
 * Without weak fairness:
 *
 *     ./pan -a -N liveness
 *
 * Expected result:
 *
 *     errors: 1
 *
 * With SPIN weak fairness:
 *
 *     ./pan -a -f -N liveness
 *
 * Expected result:
 *
 *     errors: 1
 *
 * Meaning:
 *
 *     Weak fairness is not strong enough to guarantee starvation freedom
 *     for this simple binary semaphore model.
 *
 *     A waiting process may become enabled infinitely often, whenever
 *     sem == true, but it is not continuously enabled because the other
 *     process may immediately acquire the semaphore again.
 *
 *     To prove starvation freedom, the model needs either a stronger
 *     fairness assumption or a fair semaphore implementation, such as
 *     a turn-based or queue-based semaphore.
 *
 *
 * Check liveness under strong fairness assumption
 * -----------------------------------------------
 *
 *     Fill in the strong_fair_liveness property in the model, replacing the "fairness assumption" and "liveness property" placeholders.
 *
 *     Check the strong_fair_liveness property:
 *
 *     ./pan -a -f -N strong_fair_liveness
 *
 *     Weak process fairness -f prevents SPIN from not scheduling one of the processes at all.
 *
 * Expected result:
 *
 *     errors: 0
 *
 * Meaning:
 *
 *     The property strong_fair_liveness checks liveness under an explicit
 *     strong fairness assumption written in LTL.
 *
 *     SPIN does not provide a separate built-in command-line option for
 *     strong fairness. The -f option only enables SPIN's built-in weak
 *     fairness. Therefore, strong fairness is modeled here as part of
 *     the LTL formula itself.
 *
 *     The strong fairness assumption says:
 *
 *         If P's acquire action is enabled infinitely often,
 *         then P must enter its critical section infinitely often.
 *
 *         If Q's acquire action is enabled infinitely often,
 *         then Q must enter its critical section infinitely often.
 *
 *     In this model, P's acquire action is considered enabled when:
 *
 *         P@waitP && sem
 *
 *     and Q's acquire action is considered enabled when:
 *
 *         Q@waitQ && sem
 *
 *     This removes unfair starvation executions where a process is given
 *     infinitely many chances to acquire the semaphore but is never chosen.
 *
 *     This does not prove that the binary semaphore implementation is
 *     fair by itself. It proves that the liveness property holds assuming
 *     strong fairness of semaphore acquisition.
 */

bool wantP = false;
bool wantQ = false;

/*
 * Binary semaphore:
 *
 *   sem == true   means the semaphore is available.
 *   sem == false  means the semaphore is held by some process.
 */
bool sem = true;

active proctype P() {
    do
    :: wantP = true;

       /*
        * Acquire the binary semaphore.
        * This must be atomic so that testing and setting sem
        * happen as one indivisible action.
        */
waitP: atomic {
           sem == true ->
           sem = false
       }

critP: skip;        /* P's critical section */

       wantP = false;

       /*
        * Release the binary semaphore.
        */
       sem = true
    od
}

active proctype Q() {
    do
    :: wantQ = true;

       /*
        * Acquire the binary semaphore.
        * This must be atomic so that testing and setting sem
        * happen as one indivisible action.
        */
waitQ: atomic {
           sem == true ->
           sem = false
       }

critQ: skip;        /* Q's critical section */

       wantQ = false;

       /*
        * Release the binary semaphore.
        */
       sem = true
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
 * For semaphore-based mutual exclusion, this property depends on
 * scheduling fairness.
 */
ltl liveness {
    ([] (wantP -> <> P@critP))
    &&
    ([] (wantQ -> <> Q@critQ))
}

/*
 * Liveness under strong fairness assumption:
 *
 * Strong fairness assumption:
 *
 *   If P's acquire is enabled infinitely often,
 *   then P must enter its critical section infinitely often.
 *
 *   If Q's acquire is enabled infinitely often,
 *   then Q must enter its critical section infinitely often.
 *
 * Here, "P's acquire is enabled" means:
 *
 *   P is waiting at waitP, and sem == true.
 *
 * The same idea applies to Q.
 */
ltl strong_fair_liveness {
    (( [] <>(P@waitP && sem) -> [] <> P@critP) && ([] <> (Q@waitQ && sem) -> [] <> Q@critQ))
    ->
    ( [] (P@waitP -> <> P@critP) && [](Q@waitQ -> <> Q@critQ))
}