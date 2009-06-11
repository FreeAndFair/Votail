package election.tally;

public interface BallotCountingModel extends election.util.Workflow {

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

	public abstract /*@ pure @*/ int getState();

	public abstract void changeState(int newState);

	/**
	 * Set of possible states
	 */
	public abstract /*@ pure @*/ boolean isPossibleState(int value);

	/**
	 * Set of valid transitions from state machine diagram
	 */
	public abstract /*@ pure @*/ boolean isTransition(int fromState, int toState);

}