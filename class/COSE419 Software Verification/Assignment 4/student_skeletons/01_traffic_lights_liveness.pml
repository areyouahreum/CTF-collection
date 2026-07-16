/*
 * 01_traffic_lights_liveness.pml
 *
 * Independent red/green traffic lights and weak process fairness.
 *
 * This example is intentionally simple.
 * Each traffic light is modeled as an independent process that toggles
 * forever between RED and GREEN.
 *
 * There is no shared resource and no mutual exclusion yet.
 *
 *
 * Goal of this example:
 *
 *   - Introduce simulation in SPIN.
 *   - Introduce liveness properties.
 *   - Show why liveness verification searches infinite executions.
 *   - Show how unfair scheduling can violate a liveness property.
 *   - Show how SPIN weak fairness changes the verification result.
 *
 *
 * Traffic-light behavior:
 *
 *   Light1 repeatedly toggles:
 *
 *       RED -> GREEN -> RED -> GREEN -> ...
 *
 *   Light2 repeatedly toggles:
 *
 *       RED -> GREEN -> RED -> GREEN -> ...
 *
 *
 * LTL properties:
 *
 *   live1: light 1 is green infinitely often.
 *
 *       []<> (light1 == GREEN)
 *
 *   live2: light 2 is green infinitely often.
 *
 *       []<> (light2 == GREEN)
 *
 *
 * Simulation commands
 * -------------------
 *
 * Random simulation:
 *
 *     spin 01_traffic_lights_liveness.pml
 *
 * More detailed simulation:
 *
 *     spin -p -g -l 01_traffic_lights_liveness.pml
 *
 * Meaning:
 *
 *     -p  shows process execution steps
 *     -g  shows global variable changes
 *     -l  shows local variable changes
 *
 * In simulation mode, SPIN executes one possible behavior of the model.
 * It does not prove or disprove the LTL properties.
 *
 *
 * Verification commands
 * ---------------------
 *
 * Step 1: Generate the verifier.
 *
 *     spin -a 01_traffic_lights_liveness.pml
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
 * Check live2 without fairness
 * ----------------------------
 *
 *     ./pan -a -N live2
 *
 * Expected result:
 *
 *     errors: 1
 *
 * Meaning:
 *
 *     SPIN may find an infinite execution where Light1 is scheduled forever
 *     and Light2 is never scheduled. In that execution, light2 never becomes
 *     GREEN infinitely often.
 *
 *
 * Replay the counterexample trail
 * -------------------------------
 *
 *     spin -t -p -g -l 01_traffic_lights_liveness.pml
 *
 *
 * Check live2 with weak process fairness
 * --------------------------------------
 *
 *     ./pan -a -f -N live2
 *
 * Expected result:
 *
 *     errors: 0
 *
 * Meaning:
 *
 *     Light2's toggle action is continuously enabled. With SPIN weak
 *     fairness, a continuously enabled process cannot be ignored forever.
 */

mtype = { RED, GREEN };

mtype light1 = RED;
mtype light2 = RED;

active proctype Light1() {
    do
    :: if
       :: light1 == RED ->
            light1 = GREEN;
            printf("Light1: RED -> GREEN\n")
       :: light1 == GREEN ->
            light1 = RED;
            printf("Light1: GREEN -> RED\n")
       fi
    od
}

active proctype Light2() {
    do
    :: if
       :: light2 == RED ->
            light2 = GREEN;
            printf("Light2: RED -> GREEN\n")
       :: light2 == GREEN ->
            light2 = RED;
            printf("Light2: GREEN -> RED\n")
       fi
    od
}

/*
 * Liveness properties:
 *
 * Each light should be GREEN infinitely often.
 */
ltl live1 {
    []<> (light1 == GREEN)
}

ltl live2 {
    []<> (light2 == GREEN)
}