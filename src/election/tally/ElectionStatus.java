package election.tally;

public class ElectionStatus {

	/** Start state */
	public static final byte EMPTY = 0;
	/** Setting up candidate list and number of seats to fill*/
	public static final byte SETTING_UP = 1;
	/** Ready to load ballots */
	public static final byte PRELOAD = 2;
	/** Load all valid ballots */
	public static final byte LOADING = 3;
	/** Ready to count votes */
	public static final byte PRECOUNT = 4;
	/** Count the votes */
	public static final byte COUNTING = 5;
	/** Finished counting */
	public static final byte FINISHED = 6;

}