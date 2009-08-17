package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;

public class TransfersFromExcludedCandidateEventH extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   election.generateCandidates(4);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {election.getCandidate(0).getCandidateID(),
			   election.getCandidate(1).getCandidateID()};
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(election.getCandidate(i).getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.setMultiplePreferences(preferences);
	     ballotBox.accept(ballot);
	   }
	   
	   ballotCounting.load(ballotBox);
	   ballotCounting.startCounting();
	   ballotCounting.calculateSurpluses();
	   int loser = ballotCounting.findLowestCandidate();
	   ballotCounting.eliminateCandidate(loser);
	   ballotCounting.incrementCountNumber();
	   ballotCounting.updateCountStatus(AbstractCountStatus.CANDIDATE_EXCLUDED);
	   assertTrue(ballotCounting.getContinuingCandidates() == 3);
	   int countState = ballotCounting.countStatus.getState();
	   assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	}

}
