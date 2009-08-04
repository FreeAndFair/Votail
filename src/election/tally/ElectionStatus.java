package election.tally;

public class ElectionStatus {

	/** Start */
	public static final byte EMPTY = 0;
	/** Setting up candidate list and number of seats to fill*/
	public static final byte SETTING_UP = EMPTY + 1;
	/** Ready to load ballots */
	public static final byte PRELOAD = SETTING_UP + 1;
	/** Load all valid ballots */
	public static final byte LOADING = PRELOAD + 1;
	/** Ready to count votes */
	public static final byte PRECOUNT = LOADING + 1;
	/** Count the votes */
	public static final byte COUNTING = PRECOUNT + 1;
	/** Finished counting */
	public static final byte FINISHED = COUNTING + 1;

}