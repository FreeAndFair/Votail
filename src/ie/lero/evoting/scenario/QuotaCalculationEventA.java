/**
 * Event A: Calculate Quota
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.ElectionStatus;
import election.tally.mock.MockBallot;

/**
 * @author Dermot Cochran
 */
public class QuotaCalculationEventA extends TestCase {
  
	/**
	 * Test the calculation of quota and deposit saving threshold.
	 */
	public void testCalculateQuota () {
	  BallotCounting ballotCounting = new BallotCounting();
	  Election parameters = new Election();
	  parameters.numberOfCandidates = 3;
	  parameters.numberOfSeatsInThisElection = 1;
	  parameters.totalNumberOfSeats = 1;
	  Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
	  candidates[0] = new Candidate();
	  candidates[1] = new Candidate();
	  candidates[2] = new Candidate();
	  parameters.setCandidateList(candidates);
	  ballotCounting.setup(parameters);
	  
 		assertTrue(ballotCounting.getStatus() == ElectionStatus.PRELOAD);
		BallotBox ballotBox = new BallotBox();
		MockBallot ballot = new MockBallot();
		for (int i = 0; i < 50001; i++) {
		  ballot.setFirstPreference(candidates[0].getCandidateID());
		  ballotBox.accept(ballot);
		}
		for (int i = 0; i < 49999; i++) {
		  ballot.setFirstPreference(candidates[1].getCandidateID());
		  ballotBox.accept(ballot);
		}
		
		ballotCounting.load(ballotBox);
		
		ballotCounting.calculateFirstPreferences();
		ballotCounting.calculateSurpluses();
		int countState = ballotCounting.countStatus.getState();
	 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	 	
		assertTrue (ballotCounting.getRemainingSeats() == 1);
		
		assertTrue (ballotBox.size() == 100000);
		
		int quota = ballotCounting.getQuota();
		assertTrue (50001 == quota);
		
		// Candidate 0 has the full quota but no surplus
		assertTrue (quota == 
			ballotCounting.countBallotsFor(candidates[0].getCandidateID()));
		assertTrue (ballotCounting.getTotalNumberOfSurpluses() == 0);
		assertTrue (ballotCounting.getTotalSumOfSurpluses() == 0);
		
		ballotCounting.count();
		assertTrue (quota == ballotCounting.getQuota());
		countState = ballotCounting.countStatus.getState();
	 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	 	assertTrue (candidates[0].isElected());
	}

}
