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
	  parameters.numberOfCandidates = 2;
	  parameters.numberOfSeatsInThisElection = 1;
	  parameters.totalNumberOfSeats = 1;
	  Candidate[] candidates = new Candidate[parameters.numberOfCandidates];
	  candidates[0] = new Candidate();
	  candidates[1] = new Candidate();
	  parameters.setCandidateList(candidates);
	  ballotCounting.setup(parameters);
	  
 		assertTrue(ballotCounting.getStatus() == ElectionStatus.PRELOAD);
		BallotBox ballotBox = new BallotBox();
		MockBallot ballot = new MockBallot();
		for (int i = 0; i < 60000; i++) {
		  ballot.setFirstPreference(candidates[0].getCandidateID());
		  ballotBox.accept(ballot);
		}
		for (int i = 0; i < 40000; i++) {
		  ballot.setFirstPreference(candidates[1].getCandidateID());
		  ballotBox.accept(ballot);
		}
		
		ballotCounting.load(ballotBox);
		
		ballotCounting.calculateFirstPreferences();
		ballotCounting.calculateSurpluses();
		assertTrue (ballotCounting.getRemainingSeats() == 1);
		
		assertTrue (ballotBox.size() == 100000);
		
		int quota = ballotCounting.getQuota();
		assertTrue (50001 == quota);
		
		ballotCounting.count();
	}

}
