package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.CountStatus;
import election.tally.Election;
import election.tally.mock.MockBallot;
import junit.framework.TestCase;

public class TransfersFromExcludedCandidateEventH extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfCandidates = 4;
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   Candidate[] candidates = Election.generateCandidates(election.numberOfCandidates);
	   election.setCandidateList(candidates);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {candidates[0].getCandidateID(),
	                        candidates[1].getCandidateID()};
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(candidates[i].getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.setMultiplePreferences(preferences);
	     ballotBox.accept(ballot);
	   }
	   ballotCounting.load(ballotBox);
	   ballotCounting.calculateSurpluses();
		 int loser = ballotCounting.findLowestCandidate();
		 ballotCounting.eliminateCandidate(loser);
		 ballotCounting.incrementCountNumber();
		 ballotCounting.updateCountStatus(CountStatus.CANDIDATE_EXCLUDED);
		 assertTrue(ballotCounting.getContinuingCandidates() == 3);
		 int countState = ballotCounting.countStatus.getState();
		 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	}

}