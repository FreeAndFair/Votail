package election.tally.mock;

public class MockBallot extends election.tally.Ballot {

  //@ requires firstPreferenceID != NONTRANSFERABLE;
	//@ requires 0 < firstPreferenceID;
	public void setFirstPreference(final int firstPreferenceID) {
		numberOfPreferences = 1;
		preferenceList[0] = firstPreferenceID;
		ballotID = nextBallotID++; // new ballot paper
	} //@ nowarn;

	/*@ requires 1 < howManyPreferences;
	  @ requires howManyPreferences <= candidateIDList.length;
	  @ requires howManyPreferences <= preferenceList.length;
	  @ requires candidateIDList != null;
	  @ requires (\forall int c; 0 <= c && c < howManyPreferences;
	  @          candidateIDList[c] != NONTRANSFERABLE);
	  @*/
	public void setMultiplePreferences(final int[] candidateIDList, final int howManyPreferences) {
		this.numberOfPreferences = howManyPreferences;
		for (int c = 0; c < howManyPreferences; c++) {
			preferenceList[c] = candidateIDList[c];
		}
    ballotID = nextBallotID++; // new ballot paper
	}

}
