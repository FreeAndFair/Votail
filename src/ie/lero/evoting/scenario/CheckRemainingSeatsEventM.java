package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockCandidate;

public class CheckRemainingSeatsEventM extends TestCase {

	public void testEvent() {
		BallotCounting ballotCounting = new BallotCounting();
		Election election = new Election();
		election.numberOfCandidates = 4;
		election.numberOfSeatsInThisElection = 3;
		election.totalNumberOfSeats = 3;
		Candidate[] candidates = MockCandidate.generateCandidates(4);
    election.setCandidateList(candidates);
		ballotCounting.setup(election);
		assertTrue (3 == ballotCounting.getRemainingSeats());
	}

  

}
