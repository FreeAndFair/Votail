package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;

public class CheckRemainingSeatsEventM extends TestCase {

	public void testEvent() {
		BallotCounting ballotCounting = new BallotCounting();
		Election election = new Election();
		election.numberOfSeatsInThisElection = 3;
		election.totalNumberOfSeats = 3;
		election.setNumberOfCandidates(4);
		ballotCounting.setup(election);
		assertTrue (election.numberOfSeatsInThisElection 
            == ballotCounting.getRemainingSeats());
		BallotBox ballotBox = new BallotBox();
		MockBallot ballot = new MockBallot();
		ballot.setFirstPreference(election.getCandidate(0).getCandidateID());
		ballotBox.accept(ballot);
		ballotCounting.load(ballotBox);
        assertTrue (election.numberOfSeatsInThisElection 
            == ballotCounting.getRemainingSeats());
        ballotCounting.count();
        assertTrue (0 == ballotCounting.getRemainingSeats());
	}
}
