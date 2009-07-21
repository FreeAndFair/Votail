package election.tally.mock;

public class MockBallot extends election.tally.Ballot {

    //@ requires firstPreferenceID != NONTRANSFERABLE;
	//@ requires 0 < firstPreferenceID;
	public void setFirstPreference(final int firstPreferenceID) {
		numberOfPreferences = 1;
		preferenceList[0] = firstPreferenceID;
		ballotID = nextBallotID++; // new ballot paper
	} //@ nowarn;

	public void setMultiplePreferences(final /*@ non_null @*/ int[] candidateIDList) {
		load(candidateIDList);
		ballotID = nextBallotID++; // new ballot paper
	}

}
