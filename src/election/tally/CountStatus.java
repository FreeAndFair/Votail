package election.tally;

public interface CountStatus {

	// States within the ballot counting machine
	public static final int READY_TO_COUNT = 1;
	public static final int NO_SEATS_FILLED_YET = 2;
	public static final int CANDIDATES_HAVE_QUOTA = 3;
	public static final int CANDIDATE_ELECTED = 4;
	public static final int NO_SURPLUS_AVAILABLE = 5;
	public static final int SURPLUS_AVAILABLE = 6;
	public static final int READY_TO_ALLOCATE_SURPLUS = 8;
	public static final int READY_TO_MOVE_BALLOTS = 10;
	public static final int CANDIDATE_EXCLUDED = 11;
	public static final int READY_FOR_NEXT_ROUND_OF_COUNTING = 12;
	public static final int LAST_SEAT_BEING_FILLED = 13;
	public static final int MORE_CONTINUING_CANDIDATES_THAN_REMAINING_SEATS = 14;
	public static final int ONE_OR_MORE_SEATS_REMAINING = 15;
	public static final int ALL_SEATS_FILLED = 16;
	public static final int END_OF_COUNT = 17;
	public static final int ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT = 18;
	/**
	 * Get the current stage of counting.
	 */
	 //@ ensures isPossibleState(\result);
	public /*@ pure @*/ int getState();

	/**
	 * Move to the next stage of counting.
	 * 
	 * @param newState The next stage of counting.
	 */
	//@ requires isPossibleState (newState);
	//@ requires isTransition (getState(), newState);
	//@ ensures getState() == newState;
	public void changeState(int newState);

	/**
	 * Confirm that this value is a valid stage of counting.
	 * 
	 * @param value The stage in the counting process.
	 */
	/*@ ensures \result <==> (READY_TO_COUNT <= value && 
	  @         value <= CountStatus.ONE_CONTINUING_CANDIDATE_PER_REMAINING_SEAT);
	  @*/
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