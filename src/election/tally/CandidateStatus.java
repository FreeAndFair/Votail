package election.tally;

public class CandidateStatus {

	/** State value for a candidate neither elected nor eliminated yet */
	public static final byte CONTINUING = 0;
	/**
	 * State value for a candidate deemed to have been elected either by
	 * having a quota or being the highest continuing candidate for the
	 * last remaining seat.  
	 */
	public static final byte ELECTED = 1;
	/**
	 * State value for a candidate excluded from election as being one
	 * of the lowest continuing candidates at the end of a round of counting.  
	 */
	public static final byte ELIMINATED = 2;
	/**
	 * State value for a candidate defeated at the last round of the election
	 * e.g. the second highest remaining candidate when the last seat is 
	 * being filled  
	 */
	public static final byte DEFEATED = 4;

}