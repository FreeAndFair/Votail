/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;

/**
 * @author Dermot Cochran
 *
 */
public class TransfersFromSurplusEventD extends TestCase {

	private static final int NUM_CANDIDATES = 10;

  public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   election.setNumberOfCandidates(NUM_CANDIDATES);
	   
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   Ballot ballot = new Ballot();
	   int[] preferences = {election.getCandidate(0).getCandidateID(), election.getCandidate(1).getCandidateID(),
	                        election.getCandidate(2).getCandidateID()};
	   
	   for (int i=0; i<NUM_CANDIDATES; i++) {
	     assertTrue (election.getCandidate(i).sameAs((election.getCandidate(i))));
	     ballot.setFirstPreference(election.getCandidate(0).getCandidateID());
       ballotBox.accept(ballot);
	     ballot.setFirstPreference(election.getCandidate(i).getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.load(preferences);
	     ballotBox.accept(ballot);
	   }
	  
	   ballotCounting.load(ballotBox);
	   ballotCounting.startCounting();
	   assertTrue (ballotBox.size() == 3 * NUM_CANDIDATES);
	   ballotCounting.calculateSurpluses();
	   assertTrue (NUM_CANDIDATES == ballotCounting.getContinuingCandidates()); 
	   int winner = ballotCounting.findHighestCandidate();
	   assertTrue (21 == ballotCounting.countBallotsFor(election.getCandidate(0).getCandidateID()));
	   assertTrue (0 == winner);
	   assertTrue (21 == ballotCounting.countBallotsFor(election.getCandidate(winner).getCandidateID()));
	   ballotCounting.electCandidate(winner);
	   assertTrue (ballotCounting.isElected(election.getCandidate(winner)));
	   assertTrue (election.getCandidate(winner).isElected());
	   ballotCounting.countStatus.changeState(AbstractCountStatus.SURPLUS_AVAILABLE);
	   ballotCounting.distributeSurplus(winner);
	   ballotCounting.incrementCountNumber();
	   int numberContinuing = ballotCounting.getContinuingCandidates();
	   assertTrue (NUM_CANDIDATES - 1 == numberContinuing);
     int secondPlace = ballotCounting.findHighestCandidate();
     assertTrue (0 <= secondPlace);
     assertTrue (ballotCounting.randomSelection(election.getCandidate(0), election.getCandidate(1)) ==
     ballotCounting.randomSelection(election.getCandidate(1), election.getCandidate(0)));

	   assertTrue (0 == winner);
	   assertTrue (NUM_CANDIDATES - 1 == ballotCounting.getContinuingCandidates());
	   assertTrue (2 == ballotCounting.getRemainingSeats());
	   assertTrue (3 * NUM_CANDIDATES == ballotBox.size());
	   assertTrue (1 == secondPlace);
	   int countState = ballotCounting.countStatus.getState();
	   assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	   
	   // Test that the count completes normally
	   ballotCounting.count();
	   assertTrue (election.getCandidate(2).isElected());
	}
}
