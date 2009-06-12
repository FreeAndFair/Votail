package election.tally;

public interface BallotCountingModel {

	// States within the ballot counting machine
	public static final int READY_TO_COUNT = 1;
	public static final int NO_SEATS_FILLED_YET = 2;
	public static final int CANDIDATES_HAVE_QUOTA = 3;
	public static final int CANDIDATE_ELECTED = 4;
	public static final int NO_SURPLUS_AVAILABLE = 5;
	public static final int SURPLUS_AVAILABLE = 6;
	public static final int READY_TO_CALCULATE_ROUNDING_TRANSFERS = 7;
	public static final int READY_TO_ALLOCATE_SURPLUS = 8;
	public static final int READY_TO_ADJUST_NUMBER_OF_TRANSFERS = 9;
	public static final int READY_TO_MOVE_BALLOTS = 10;
	public static final int CANDIDATE_EXCLUDED = 11;
	public static final int READY_FOR_NEXT_ROUND_OF_COUNTING = 12;
	public static final int LAST_SEAT_BEING_FILLED = 13;
	public static final int MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS = 14;
	public static final int ONE_OR_MORE_SEATS_REMAINING = 15;
	public static final int ALL_SEATS_FILLED = 16;
	public static final int END_OF_COUNT = 17;
	public static final int ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT = 18;
	public static final int READY_TO_REWEIGHT_BALLOTS = 19;

	/*@ public constraint \old(getState()) == READY_TO_COUNT ==> 
	  @                   getState() == NO_SEATS_FILLED_YET;
	  @
	  @ public constraint \old(getState()) == NO_SEATS_FILLED_YET ==> 
	  @                   getState() == CANDIDATE_ELECTED || 
	  @                   getState() == NO_SURPLUS_AVAILABLE;
	  @
	  @ public constraint \old(getState()) == CANDIDATE_ELECTED ==> 
	  @                   getState() == SURPLUS_AVAILABLE ||
	  @                   getState() == NO_SURPLUS_AVAILABLE ||
	  @                   getState() == CANDIDATES_HAVE_QUOTA;
	  @
	  @ public constraint \old(getState()) == SURPLUS_AVAILABLE ==> 
	  @                   getState() == READY_TO_ALLOCATE_SURPLUS ||
	  @                   getState() == READY_TO_REWEIGHT_BALLOTS;
	  @
	  @ public constraint \old(getState()) == READY_TO_ALLOCATE_SURPLUS ==> 
	  @                   getState() == READY_TO_CALCULATE_ROUNDING_TRANSFERS;
	  @
	  @ public constraint \old(getState()) == READY_TO_CALCULATE_ROUNDING_TRANSFERS ==> 
	  @                   getState() == READY_TO_ADJUST_NUMBER_OF_TRANSFERS;
	  @
	  @ public constraint \old(getState()) == READY_TO_ADJUST_NUMBER_OF_TRANSFERS ==> 
	  @                   getState() == READY_TO_MOVE_BALLOTS;
	  @
	  @ public constraint \old(getState()) == READY_TO_MOVE_BALLOTS ==> 
	  @                   getState() == READY_FOR_NEXT_ROUND_OF_COUNTING;
	  @
	  @ public constraint \old(getState()) == CANDIDATE_EXCLUDED ==> 
	  @                   getState() == READY_TO_MOVE_BALLOTS;
	  @
	  @ public constraint \old(getState()) == NO_SURPLUS_AVAILABLE ==> 
	  @                   getState() == CANDIDATE_EXCLUDED;
	  @
	  @ public constraint \old(getState()) == READY_FOR_NEXT_ROUND_OF_COUNTING ==> 
	  @                   getState() == ALL_SEATS_FILLED ||
	  @                   getState() == ONE_OR_MORE_SEATS_REMAINING;
	  @
	  @ public constraint \old(getState()) == ALL_SEATS_FILLED ==> 
	  @                   getState() == END_OF_COUNT;
	  @
	  @ public constraint \old(getState()) == ONE_OR_MORE_SEATS_REMAINING ==> 
	  @                   getState() == MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS ||
	  @                   getState() == ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT ||
	  @                   getState() == LAST_SEAT_BEING_FILLED ||
	  @                   getState() == ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT;
	  @
	  @ public constraint \old(getState()) == MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS ==>
	  @                   getState() == CANDIDATE_ELECTED ||
	  @                   getState() == NO_SURPLUS_AVAILABLE;
	  @
	  @ public constraint \old(getState()) == LAST_SEAT_BEING_FILLED ==>
	  @                   getState() == CANDIDATE_EXCLUDED;
	  @
	  @ public constraint \old(getState()) == READY_TO_REWEIGHT_BALLOTS ==>
	  @                   getState() == READY_FOR_NEXT_ROUND_OF_COUNTING;
	  @
	  @ public constraint \old(getState()) == ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT ==>
	  @                   getState() == ALL_SEATS_FILLED;
	  @
	  @ public constraint (* No other state transitions are possible *);
	  @*/
	  
	/**
	 * Get the current stage of counting.
	 */
	 //@ ensures isPossibleState(\result);
	public abstract /*@ pure @*/ int getState();

	/**
	 * Move to the next stage of counting.
	 * 
	 * @param newState The next stage of counting.
	 */
	//@ requires isPossibleState (newState);
	//@ requires isTransition (getState(), newState);
	//@ ensures getState() == newState;
	public abstract void changeState(int newState);

	/**
	 * Confirm that this value is a valid stage of counting.
	 * 
	 * @param value The stage in the counting process.
	 */
	//@ ensures \result <==> (READY_TO_COUNT <= value && value <= READY_TO_REWEIGHT_BALLOTS);
	public abstract /*@ pure @*/ boolean isPossibleState(int value);

	/**
	 * Confirm that this is a valid transition from one stage of counting to another.
	 * 
	 * @param fromState The current stage of counting.
	 * @param toState The next stage if counting.
	 */
	//@ requires isPossibleState(fromState);
	//@ requires isPossibleState(toState);
	public abstract /*@ pure @*/ boolean isTransition(int fromState, int toState);

}