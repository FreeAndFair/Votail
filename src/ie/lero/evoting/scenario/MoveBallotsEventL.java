package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

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
