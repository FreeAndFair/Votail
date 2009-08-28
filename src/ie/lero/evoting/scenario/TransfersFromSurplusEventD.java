/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;

/**
 * @author Dermot Cochran
 *
 */
public class TransfersFromSurplusEventD extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   election.generateCandidates(20);
	   
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {election.getCandidate(0).getCandidateID(), election.getCandidate(1).getCandidateID(),
	                        election.getCandidate(2).getCandidateID()};
	   
	   // Candidate 0 has 41 first preferences of which 20 are second preferences for candidate 1
	   // Candidate 0 has a surplus of 25 of which 20 should transfer to candidate 1
	   // Candidate 1 will then have a surplus of 5 votes which will go to candidate 2
	   for (int i=0; i<20; i++) {
	     assertTrue (election.getCandidate(i).sameAs((election.getCandidate(i))));
	     ballot.setFirstPreference(election.getCandidate(0).getCandidateID());
       ballotBox.accept(ballot);
	     ballot.setFirstPreference(election.getCandidate(i).getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.setMultiplePreferences(preferences);
	     ballotBox.accept(ballot);
	   }
	  
	   ballotCounting.load(ballotBox);
	   ballotCounting.startCounting();
	   assertTrue (ballotBox.size() == 60);
	   ballotCounting.calculateFirstPreferences();
	   ballotCounting.calculateSurpluses();
	   assertTrue (20 == ballotCounting.getContinuingCandidates()); 
	   int winner = ballotCounting.findHighestCandidate();
	   assertTrue (41 == ballotCounting.countBallotsFor(election.getCandidate(0).getCandidateID()));
	   assertTrue (0 == winner);
	   assertTrue (41 == ballotCounting.countBallotsFor(election.getCandidate(winner).getCandidateID()));
	   ballotCounting.electCandidate(winner);
	   assertTrue (ballotCounting.isElected(election.getCandidate(winner)));
	   assertTrue (election.getCandidate(winner).isElected());
	   assertTrue (1 == ballotCounting.countBallotsFor(election.getCandidate(1).getCandidateID()));
	   ballotCounting.countStatus.changeState(AbstractCountStatus.SURPLUS_AVAILABLE);
	   ballotCounting.distributeSurplus(winner);
	   ballotCounting.incrementCountNumber();
	   int numberContinuing = ballotCounting.getContinuingCandidates();
	   assertTrue (19 == numberContinuing);
	   assertTrue (21 == ballotCounting.countBallotsFor(election.getCandidate(1).getCandidateID()));
       int secondPlace = ballotCounting.findHighestCandidate();
       assertTrue (0 <= secondPlace);
       int votesForSecondPlace = 
         ballotCounting.countBallotsFor(election.getCandidate(secondPlace).getCandidateID());
       assertTrue (ballotCounting.randomSelection(election.getCandidate(0), election.getCandidate(1)) ==
         ballotCounting.randomSelection(election.getCandidate(1), election.getCandidate(0)));

       assertTrue (votesForSecondPlace == 21);
       assertTrue (16 == ballotCounting.getQuota());
	   assertTrue (0 == winner);
	   assertTrue (19 == ballotCounting.getContinuingCandidates());
	   assertTrue (2 == ballotCounting.getRemainingSeats());
	   assertTrue (60 == ballotBox.size());
	   assertTrue (1 == secondPlace);
	   int countState = ballotCounting.countStatus.getState();
	   assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	   
	   // Test that the count completes normally
	   ballotCounting.count();
	   assertTrue (election.getCandidate(2).isElected());
	}
}
