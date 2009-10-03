/**
 * Event A: Calculate Quota
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;
import election.tally.ElectionStatus;

/**
 * @author Dermot Cochran
 */
public class QuotaCalculationEventA extends TestCase {
  
	/**
	 * Test the calculation of quota and deposit saving threshold.
	 */
	public void testCalculateQuota () {
	  final BallotCounting ballotCounting = new BallotCounting();
	  final Constituency parameters = new Constituency();
	  parameters.setNumberOfSeats (1,1);
	  parameters.setNumberOfCandidates(3);
	  ballotCounting.setup(parameters);
	  
 		assertTrue(ballotCounting.getStatus() == ElectionStatus.PRELOAD);
		final BallotBox ballotBox = new BallotBox();
		final Ballot ballot = new Ballot();
		for (int i = 0; i < 51; i++) {
		  ballot.setFirstPreference(parameters.getCandidate(0).getCandidateID());
		  ballotBox.accept(ballot);
		}
		for (int i = 0; i < 49; i++) {
		  ballot.setFirstPreference(parameters.getCandidate(1).getCandidateID());
		  ballotBox.accept(ballot);
		}
		
		ballotCounting.load(ballotBox);
		ballotCounting.startCounting();
		
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
		assertTrue (ballotCounting.getTotalSumOfSurpluses() == 0);
		
		ballotCounting.count();
		assertTrue (quota == ballotCounting.getQuota());
		countState = ballotCounting.countStatus.getState();
	 	assertTrue (ballotCounting.countStatus.isPossibleState(countState));
	 	assertTrue (parameters.getCandidate(0).isElected());
	}

}
