/**
 * 
 */
package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;
import election.tally.mock.MockCandidate;
import junit.framework.TestCase;

/**
 * @author Dermot Cochran
 *
 */
public class TransfersFromSurplusEventD extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfCandidates = 20;
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   Candidate[] candidates = MockCandidate.generateCandidates(
			   election.numberOfCandidates);
	   election.setCandidateList(candidates);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   int[] preferences = {candidates[0].getCandidateID(), candidates[1].getCandidateID(),
	                        candidates[2].getCandidateID()};
	   
	   // Candidate 0 has 41 first preferences of which 20 are second preferences for candidate 1
	   // Candidate 0 has a surplus of 25 of which 20 should transfer to candidate 1
	   // Candidate 1 will then have a surplus of 5 votes which will go to candidate 2
	   for (int i=0; i<election.numberOfCandidates; i++) {
	     ballot.setFirstPreference(candidates[0].getCandidateID());
       ballotBox.accept(ballot);
	     ballot.setFirstPreference(candidates[i].getCandidateID());
	     ballotBox.accept(ballot);
	     ballot.setMultiplePreferences(preferences);
	     ballotBox.accept(ballot);
	   }
	  
	   ballotCounting.load(ballotBox);
	   assertTrue (ballotBox.size() == 60);
	   ballotCounting.calculateFirstPreferences();
	   ballotCounting.calculateSurpluses();
	   assertTrue (20 == ballotCounting.getContinuingCandidates()); 
	   int winner = ballotCounting.findHighestCandidate();
	   assertTrue (41 == ballotCounting.countBallotsFor(candidates[0].getCandidateID()));
	   assertTrue (0 == winner);
	   int votesForWinner =
	     ballotCounting.countBallotsFor(candidates[winner].getCandidateID());
	   assertTrue (41 == votesForWinner);
	   ballotCounting.electCandidate(winner);
	   assertTrue (ballotCounting.isElected(candidates[winner]));
	   assertTrue (1 == ballotCounting.countBallotsFor(candidates[1].getCandidateID()));
	   ballotCounting.distributeSurplus(winner);
	   ballotCounting.incrementCountNumber();
	   int numberContinuing = ballotCounting.getContinuingCandidates();
	   assertTrue (19 == numberContinuing);
	   assertTrue (21 == ballotCounting.countBallotsFor(candidates[1].getCandidateID()));
     int secondPlace = ballotCounting.findHighestCandidate();
     assertTrue (0 <= secondPlace);
     int votesForSecondPlace = 
       ballotCounting.countBallotsFor(candidates[secondPlace].getCandidateID());

     assertTrue (votesForWinner == 41);
     assertTrue (votesForSecondPlace == 21);
     assertTrue (16 == ballotCounting.getQuota());
	   assertTrue (0 == winner);
	   assertTrue (19 == ballotCounting.getContinuingCandidates());
	   assertTrue (2 == ballotCounting.getRemainingSeats());
	   assertTrue (60 == ballotBox.size());
	   assertTrue (1 == secondPlace);
	}
}
