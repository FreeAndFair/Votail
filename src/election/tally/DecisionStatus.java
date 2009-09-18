package election.tally;

public class DecisionStatus {

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
	 * State value for the decision to deem this candidate elected as one
	 * of the highest continuing candidates for the last remaining seats 
	 */
	public static final byte DEEM_ELECTED = 5;
}