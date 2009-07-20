package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotCounting;
import election.tally.Election;

public class CheckRemainingSeatsEventM extends TestCase {

	public void testEvent() {
		BallotCounting ballotCounting = new BallotCounting();
		Election election = new Election();
		election.numberOfCandidates = 4;
		election.numberOfSeatsInThisElection = 3;
		election.totalNumberOfSeats = 3;
		ballotCounting.setup(election);
		assertTrue (3 == ballotCounting.getRemainingSeats());
	}

}
