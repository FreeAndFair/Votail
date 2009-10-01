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
	   BallotCounting ballotCounting = new BallotCounting();
	   Constituency constituency = new Constituency();
	   constituency.setNumberOfSeats (NUM_SEATS, NUM_SEATS);
	   constituency.setNumberOfCandidates(NUM_CANDIDATES);
	   ballotCounting.setup(constituency);    
	   BallotBox ballotBox = new BallotBox();
	   Ballot ballot = new Ballot();
	   int[] preferences = {constituency.getCandidate(0).getCandidateID(),
	                        constituency.getCandidate(1).getCandidateID()};
	   for (int i=0; i<NUM_BALLOTS; i++) {
	     ballot.load(preferences);
	     ballotBox.accept(ballot);
	   }
	   
	   ballotCounting.load(ballotBox);
     ballotCounting.startCounting();
	   assertTrue (NUM_BALLOTS == ballotBox.size());
	   int firstElected = ballotCounting.findHighestCandidate();
	   ballotCounting.electCandidate(firstElected);
	   assertTrue (0 == firstElected);
	   final int surplus = ballotCounting.getSurplus(
	     constituency.getCandidate(firstElected));
     assertTrue (surplus > 0);
     ballotCounting.countStatus.changeState(
       AbstractCountStatus.SURPLUS_AVAILABLE);
	   ballotCounting.distributeSurplus(firstElected);
	}

}
