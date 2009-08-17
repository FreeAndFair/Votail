package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;

public class MoveBallotsEventL extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   election.generateCandidates(3);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(election.getCandidate(0).getCandidateID());
	     ballotBox.accept(ballot);
	   }
	   
	   ballotCounting.load(ballotBox);
	   assertTrue (3 == ballotBox.size());
	   int firstElected = ballotCounting.findHighestCandidate();
	   assertTrue (0 == firstElected);
	   final int surplus = ballotCounting.getSurplus(election.getCandidate(firstElected));
       assertTrue (surplus > 0);
       ballotCounting.startCounting();
	   ballotCounting.distributeSurplus(firstElected);
	}

}
