package election.tally;

public class DecisionStatus {

	/**
	 * State value of decision to declare this candidate elected by
	 * reaching the quota
	 */
	public static final byte ELECT_BY_QUOTA = 0;
	/**
	 * State value for decision to eliminate this candidate as the lowest
	 * continuing candidate
	 */
	public static final byte EXCLUDE = 1;
	/**
	 * Default state value to indicate that no decision has been taken
	 */
	public static final byte NO_DECISION = 2;
	/**
	 * State value for decision to round up a fractional transfer of votes
	 * to this candidate
	 */
	public static final byte ROUND_UP_FRACTION = 3;
	/**
	 * State value for decision to distribute the surplus of this candidate
	 */
	public static final byte DISTRIBUTE_SURPLUS = 4;
	/**
	 * State value for the decision to deem this candidate elected as one
	 * of the highest continuing candidates for the last remaining seats 
	 */
	public static final byte DEEM_ELECTED = 5;

	public DecisionStatus() {
		super();
	}

}