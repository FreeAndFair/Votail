/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.mock.MockBallot;


/**
 * @author Dermot Cochran
 *
 */
public class SelectHighestContinuingCandidateEventB extends TestCase {
  
    private static final int candidateToWin = 0;
    private BallotCounting ballotCounting;

    protected void setUp() throws Exception {
    super.setUp();
    BallotBox ballotBox = new BallotBox();
    ballotCounting = new BallotCounting();
    Election parameters = new Election();
    parameters.numberOfSeatsInThisElection = 1;
    parameters.totalNumberOfSeats = 3;
    parameters.generateCandidates(2);
    ballotCounting.setup(parameters);
    MockBallot mockBallot = new MockBallot();
    mockBallot.setFirstPreference(
    parameters.getCandidate(candidateToWin).getCandidateID());
    ballotBox.accept(mockBallot);
    ballotCounting.load(ballotBox);
  }

  /**
	 * Test selection of highest continuing candidate
	 */
	public void testEvent() {
    ballotCounting.startCounting();
    int winner = ballotCounting.findHighestCandidate();
    assertTrue(winner == candidateToWin);
    int countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));
    // Test election without surplus
    ballotCounting.calculateSurpluses();
    assertTrue(ballotCounting.getTotalSumOfSurpluses() == 0);
  }

 	

 	

}
