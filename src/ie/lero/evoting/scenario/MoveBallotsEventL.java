package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;
import junit.framework.TestCase;

public class MoveBallotsEventL extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfCandidates = 3;
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   Candidate[] candidates = new Candidate[3];
	   candidates[0] = new Candidate();
	   candidates[1] = new Candidate();
	   candidates[2] = new Candidate();
	   election.setCandidateList(candidates);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(candidates[i].getCandidateID());
	     ballotBox.accept(ballot);
	   }
	   
	   ballotCounting.load(ballotBox);
	   int firstElected = ballotCounting.findHighestCandidate();
	   ballotCounting.distributeSurplus(firstElected);
	}

}
