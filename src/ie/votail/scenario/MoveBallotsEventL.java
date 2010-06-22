package ie.votail.scenario;

import ie.votail.tally.AbstractCountStatus;
import ie.votail.tally.Ballot;
import ie.votail.tally.BallotBox;
import ie.votail.tally.BallotCounting;
import ie.votail.tally.Constituency;
import junit.framework.TestCase;

public class MoveBallotsEventL extends TestCase {

	private static final int NUM_CANDIDATES = 5;
  private static final int NUM_BALLOTS = 10;
  private static final int NUM_SEATS = 3;

  public void testEvent() {
	   final BallotCounting ballotCounting = new BallotCounting();
	   final Constituency election = new Constituency();
	   election.setNumberOfSeats (NUM_SEATS, NUM_SEATS);
	   election.setNumberOfCandidates(NUM_CANDIDATES);
	   ballotCounting.setup(election);    
	   final BallotBox ballotBox = new BallotBox();
	    
	   final int[] preferences = {election.getCandidate(0).getCandidateID(),
	                        election.getCandidate(1).getCandidateID()};
 	   for (int i=0; i<NUM_BALLOTS; i++) {
	     ballotBox.accept(preferences);
	   }
	   
	   ballotCounting.load(ballotBox);
     ballotCounting.startCounting();
	   assertTrue (NUM_BALLOTS == ballotBox.size());
	   final int firstElected = ballotCounting.findHighestCandidate();
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
