package ie.lero.evoting.tally.test.util;

import election.tally.Ballot;

/**
 * @author Dermot Cochran
 *
 */
public class TestBallot extends Ballot {
	private long timestamp;

	/**
	 * @return the timestamp
	 */
	public long getTimestamp() {
		return timestamp;
	}

	/**
	  * Generate a single-preference ballot for test purposes
	  * 
	  * @param firstPreferenceID The candidateID for the first preference on the ballot
	  */
	public TestBallot(final int firstPreferenceID) {
		numberOfPreferences = 1;
		this.candidateID = firstPreferenceID;
		timestamp = System.currentTimeMillis();
		// TODO log this event and raise a security alert
	}
}
