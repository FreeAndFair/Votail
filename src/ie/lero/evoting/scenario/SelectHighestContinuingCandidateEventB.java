/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;


/**
 * @author Dermot Cochran
 *
 */
public class SelectHighestContinuingCandidateEventB extends TestCase {
  
    private static final int candidateToWin = 0;
    private BallotCounting ballotCounting;
    private static final int NUM_CANDIDATES = 2;

    protected void setUp() throws Exception {
    super.setUp();
    BallotBox ballotBox = new BallotBox();
    ballotCounting = new BallotCounting();
    Election parameters = new Election();
    parameters.numberOfSeatsInThisElection = 1;
    parameters.totalNumberOfSeats = 3;
    parameters.setNumberOfCandidates(NUM_CANDIDATES);
    ballotCounting.setup(parameters);
    // All candidates get one vote; draw lots to resolve ties
    Ballot mockBallot = new Ballot();
    for (int i=0; i < NUM_CANDIDATES; i++) {
      mockBallot.setFirstPreference(
        parameters.getCandidate(i).getCandidateID());
      ballotBox.accept(mockBallot);
    }
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
