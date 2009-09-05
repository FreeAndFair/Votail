package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;

public class MoveBallotsEventL extends TestCase {

	private static final int NUM_CANDIDATES = 5;
  private static final int NUM_BALLOTS = 10;
  private static final int NUM_SEATS = 3;

  public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfSeatsInThisElection = NUM_SEATS;
	   election.totalNumberOfSeats = NUM_SEATS;
	   election.generateCandidates(NUM_CANDIDATES);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {election.getCandidate(0).getCandidateID(),
	                        election.getCandidate(1).getCandidateID()};
	   for (int i=0; i<NUM_BALLOTS; i++) {
	     ballot.setMultiplePreferences(preferences);
	     ballotBox.accept(ballot);
	   }
	   
	   ballotCounting.load(ballotBox);
     ballotCounting.startCounting();
	   assertTrue (NUM_BALLOTS == ballotBox.size());
	   int firstElected = ballotCounting.findHighestCandidate();
	   ballotCounting.electCandidate(firstElected);
	   assertTrue (0 == firstElected);
	   final int surplus = ballotCounting.getSurplus(
	     election.getCandidate(firstElected));
     assertTrue (surplus > 0);
     ballotCounting.countStatus.changeState(
       AbstractCountStatus.SURPLUS_AVAILABLE);
	   ballotCounting.distributeSurplus(firstElected);
	}

}
