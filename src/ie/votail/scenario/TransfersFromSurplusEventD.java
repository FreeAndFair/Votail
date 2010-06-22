/**
 * 
 */
package ie.votail.scenario;

import ie.votail.tally.AbstractCountStatus;
import ie.votail.tally.Ballot;
import ie.votail.tally.BallotBox;
import ie.votail.tally.BallotCounting;
import ie.votail.tally.Constituency;
import junit.framework.TestCase;

/**
 * @author Dermot Cochran
 *
 */
public class TransfersFromSurplusEventD extends TestCase {

	private static final int NUM_CANDIDATES = 10;

  public void testEvent() {
	   final BallotCounting ballotCounting = new BallotCounting();
	   final Constituency election = new Constituency();
	   election.setNumberOfSeats(3,3);
	   election.setNumberOfCandidates(NUM_CANDIDATES);
	   
	   ballotCounting.setup(election);    
	   final BallotBox ballotBox = new BallotBox();
	   final int[] preferences = {election.getCandidate(0).getCandidateID(), 
	                        election.getCandidate(1).getCandidateID(),
	                        election.getCandidate(2).getCandidateID()};
	   int[] preferenceA = new int[1];
	   int[] preferenceB = new int[1];
	   
	   for (int i=0; i<NUM_CANDIDATES; i++) {
	     assertTrue (election.getCandidate(i).sameAs(election.getCandidate(i)));
	     preferenceA[0] = (election.getCandidate(0).getCandidateID());
       ballotBox.accept(preferenceA);
	     preferenceB[0] = (election.getCandidate(i).getCandidateID());
	     ballotBox.accept(preferenceB);
	     ballotBox.accept(preferences);
	   }
	  
	   ballotCounting.load(ballotBox);
	   ballotCounting.startCounting();
	   assertTrue (ballotBox.size() == 3 * NUM_CANDIDATES);
	   assertTrue (NUM_CANDIDATES == ballotCounting.getContinuingCandidates()); 
	   final int winner = ballotCounting.findHighestCandidate();
	   assertTrue (21 == ballotCounting.countBallotsFor(election.getCandidate(0).getCandidateID()));
	   assertTrue (0 == winner);
	   assertTrue (21 == ballotCounting.countBallotsFor(election.getCandidate(winner).getCandidateID()));
	   ballotCounting.electCandidate(winner);
	   assertTrue (ballotCounting.isElected(election.getCandidate(winner)));
	   assertTrue (election.getCandidate(winner).isElected());
	   ballotCounting.countStatus.changeState(AbstractCountStatus.SURPLUS_AVAILABLE);
	   ballotCounting.distributeSurplus(winner);
	   ballotCounting.incrementCountNumber();
	   final int numberContinuing = ballotCounting.getContinuingCandidates();
	   assertTrue (NUM_CANDIDATES - 1 == numberContinuing);
     final int secondPlace = ballotCounting.findHighestCandidate();
     assertTrue (0 <= secondPlace);
     assertTrue (ballotCounting.randomSelection(election.getCandidate(0), election.getCandidate(1)) ==
     ballotCounting.randomSelection(election.getCandidate(1), election.getCandidate(0)));

	   assertTrue (0 == winner);
	   assertTrue (NUM_CANDIDATES - 1 == ballotCounting.getContinuingCandidates());
	   assertTrue (2 == ballotCounting.getRemainingSeats());
	   assertTrue (3 * NUM_CANDIDATES == ballotBox.size());
	   assertTrue (1 == secondPlace);
	   final int countState = ballotCounting.countStatus.getState();
	   assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	   
	   // Test that the count completes normally
	   ballotCounting.count();
	   assertTrue (election.getCandidate(2).isElected());
	}
}
