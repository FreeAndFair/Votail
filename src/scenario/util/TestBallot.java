package scenario.util;

import election.tally.Ballot;

/**
 * Sample ballot paper for mock elections.
 * 
 * @author <http://kind.ucd.ie/documents/research/lgsse/evoting">Dermot Cochran</a>
 */
public class TestBallot extends Ballot {
	private long timestamp;

	/**
	 * Get the time and date of the most recent modification  to this ballot paper.
	 * 
	 * @return The timestamp
	 */
	public /*@ pure @*/ long getTimestamp() {
		return timestamp;
	}

	/**
	  * Generate a single-preference ballot
	  * 
	  * @param firstPreferenceID The candidateID for the first preference on the ballot
	  */
	public TestBallot(final int firstPreferenceID) {
		numberOfPreferences = 1;
		this.candidateID = firstPreferenceID;
		preferenceList[0] = firstPreferenceID;
		updateTimeStamp();
	}

	private void updateTimeStamp() {
		timestamp = System.currentTimeMillis();
	}

	/**
	 * Generate a multi-preference ballot
	 * 
	 * @param candidateIDList An ordered list of candidate ID numbers
	 * @param howManyPreferences The number of preferences to use
	 */
	public TestBallot(int[] candidateIDList, final int howManyPreferences) {
		this.numberOfPreferences = howManyPreferences;
		this.candidateID = candidateIDList[0];
		for (int c = 0; c < howManyPreferences; c++) {
			preferenceList[c] = candidateIDList[c];
		}
		updateTimeStamp();
		
	}
}
