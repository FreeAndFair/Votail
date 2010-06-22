package ie.votail.tally;

/**  
 * Abstract State Machine for Election Algorithm.
 * <p>
 * The election count algorithm is modeled as a two tier state machine with 
 * state values and transitions between those states. The normal path for the 
 * outer tier of the state machine is: 
 * <p>
 * EMPTY --> SETTING_UP --> PRELOAD --> LOADING --> PRECOUNT --> 
 * COUNTING --> FINISHED
 * <p>
 * The inner state machine models the status of the count.
 */

public class ElectionStatus extends CountConfiguration {

  /*@ public model byte state;
    @ public initially state == EMPTY;
    @ public constraint \old (state) <= state;
    @ public invariant (state >= EMPTY) ||  (state <= FINISHED);
    @*/

  protected transient /*@ spec_public @*/ byte status; //@ in state;
  //@ public represents state <- status;

  /*@ public invariant EMPTY < SETTING_UP;
    @ public invariant SETTING_UP < PRELOAD;
    @ public invariant PRELOAD < LOADING;
    @ public invariant LOADING < PRECOUNT;
    @ public invariant PRECOUNT < COUNTING;
    @ public invariant COUNTING < FINISHED;
    @*/

  /* Start */
  public static final byte EMPTY = 0;

  /* Setting up candidate list and number of seats to fill*/
  public static final byte SETTING_UP = EMPTY + 1;

  /* Ready to load ballots */
  public static final byte PRELOAD = SETTING_UP + 1;

  /* Load all valid ballots */
  public static final byte LOADING = PRELOAD + 1;

  /* Ready to count votes */
  public static final byte PRECOUNT = LOADING + 1;

  /* Count the votes */
  public static final byte COUNTING = PRECOUNT + 1;

  /* Finished counting */
  public static final byte FINISHED = COUNTING + 1;
}