/**
 * Event A: Calculate Quota
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
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
	  parameters.numberOfSeatsInThisElection = 1;
	  parameters.totalNumberOfSeats = 1;
	  parameters.generateCandidates(3);
	  ballotCounting.setup(parameters);
	  
 		assertTrue(ballotCounting.getStatus() == ElectionStatus.PRELOAD);
		BallotBox ballotBox = new BallotBox();
		MockBallot ballot = new MockBallot();
		for (int i = 0; i < 51; i++) {
		  ballot.setFirstPreference(parameters.getCandidate(0).getCandidateID());
		  ballotBox.accept(ballot);
		}
		for (int i = 0; i < 49; i++) {
		  ballot.setFirstPreference(parameters.getCandidate(1).getCandidateID());
		  ballotBox.accept(ballot);
		}
		
		ballotCounting.startCounting();
		ballotCounting.load(ballotBox);
		
		ballotCounting.calculateFirstPreferences();
		ballotCounting.calculateSurpluses();
		int countState = ballotCounting.countStatus.getState();
	 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	 	
		assertTrue (ballotCounting.getRemainingSeats() == 1);
		
		assertTrue (ballotBox.size() == 100);
		
		int quota = ballotCounting.getQuota();
		assertTrue (51 == quota);
		
		// Candidate 0 has the full quota but no surplus
		assertTrue (quota == 
			ballotCounting.countBallotsFor(
			parameters.getCandidate(0).getCandidateID()));
		assertTrue (ballotCounting.getTotalNumberOfSurpluses() == 0);
		assertTrue (ballotCounting.getTotalSumOfSurpluses() == 0);
		
		ballotCounting.count();
		assertTrue (quota == ballotCounting.getQuota());
		countState = ballotCounting.countStatus.getState();
	 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	 	assertTrue (parameters.getCandidate(0).isElected());
	}

}
