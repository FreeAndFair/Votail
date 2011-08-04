/**
 * Event A: Calculate Quota
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

/**
 * @author Dermot Cochran
 */
public class QuotaCalculationEventA extends TestCase {
  
  /**
   * Test the calculation of quota and deposit saving threshold.
   */
  public void testCalculateQuota() {
    final BallotCounting ballotCounting = new BallotCounting();
    final Constituency parameters = new Constituency();
    parameters.setNumberOfSeats(1, 1);
    parameters.setNumberOfCandidates(3);
    ballotCounting.setup(parameters);
    
    final BallotBox ballotBox = new BallotBox();
    int[] preferences = new int[1];
    for (int i = 0; i < 51; i++) {
      preferences[0] = parameters.getCandidate(0).getCandidateID();
      ballotBox.accept(preferences);
    }
    for (int i = 0; i < 49; i++) {
      preferences[0] = parameters.getCandidate(1).getCandidateID();
      ballotBox.accept(preferences);
    }
    
    ballotCounting.load(ballotBox);
    ballotCounting.startCounting();
    
    //@ assert (ballotCounting.getRemainingSeats() == 1);
    
    assertTrue(ballotBox.size() == 100);
    
    final int quota = ballotCounting.getQuota();
    assertTrue(51 == quota);
    
    // Candidate 0 has the full quota but no surplus
    assertTrue(quota == ballotCounting.countBallotsFor(parameters.getCandidate(
        0).getCandidateID()));
    
    ballotCounting.count();
    assertTrue(quota == ballotCounting.getQuota());
    assertTrue(parameters.getCandidate(0).isElected());
  }
  
}
