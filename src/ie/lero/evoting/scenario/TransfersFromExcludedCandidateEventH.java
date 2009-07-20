package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;
import election.tally.mock.MockCandidate;
import junit.framework.TestCase;

public class TransfersFromExcludedCandidateEventH extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfCandidates = 3;
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   Candidate[] candidates = MockCandidate.generateCandidates(3);
	   election.setCandidateList(candidates);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {candidates[0].getCandidateID(),
	                        candidates[1].getCandidateID()};
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(candidates[i].getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.setMultiplePreferences(preferences, 2);
	     ballotBox.accept(ballot);
	   }
	   ballotCounting.load(ballotBox);
		 int loser = ballotCounting.findLowestCandidate();
		 ballotCounting.eliminateCandidate(loser);
	}

}
