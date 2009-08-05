package election.tally.mock;

public class MockBallot extends election.tally.Ballot {

    //@ requires firstPreferenceID != NONTRANSFERABLE;
	//@ requires 0 < firstPreferenceID;
	public void setFirstPreference(final int firstPreferenceID) {
		numberOfPreferences = 1;
		preferenceList[0] = firstPreferenceID;
		ballotID = nextBallotID++; // new ballot paper
	} //@ nowarn;

	/*@ requires (\forall int i; 0 <= i && i < list.length;
      @   list[i] != NONTRANSFERABLE);
      @ requires (\forall int i; 0 <= i && i < list.length; 0 < list[i]);
      @ requires positionInList == 0;
      @*/
	public void setMultiplePreferences(final /*@ non_null @*/ int[] list) {
		load (list);
		ballotID = nextBallotID++; // new ballot paper
	}

}
