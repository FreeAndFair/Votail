package scenario.util;

import election.tally.BallotBox;

final class TestBallotBox extends BallotBox {

	/**
	 * Add single preference ballot for testing.
	 * 
	 * @param candidateID The first preference candidateID for the test ballot
	 */
	public void addBallot(int candidateID) {
		ballots[numberOfBallots++] = new TestBallot(candidateID);
	}
	

}
