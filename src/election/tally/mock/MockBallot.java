package election.tally.mock;

public class MockBallot extends election.tally.Ballot {

	public void setFirstPreference(final int firstPreferenceID) {
		numberOfPreferences = 1;
		this.candidateID = firstPreferenceID;
		preferenceList[0] = firstPreferenceID;
	}

	public void setMultiplePreferences(int[] candidateIDList, final int howManyPreferences) {
		this.numberOfPreferences = howManyPreferences;
		this.candidateID = candidateIDList[0];
		for (int c = 0; c < howManyPreferences; c++) {
			preferenceList[c] = candidateIDList[c];
		}
	}

}
