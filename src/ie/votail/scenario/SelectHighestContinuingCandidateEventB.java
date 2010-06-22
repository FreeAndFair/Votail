/**
 * 
 */
package ie.votail.scenario;

import ie.votail.tally.BallotBox;
import ie.votail.tally.BallotCounting;
import ie.votail.tally.Constituency;
import junit.framework.TestCase;


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
    final BallotBox ballotBox = new BallotBox();
    ballotCounting = new BallotCounting();
    final Constituency parameters = new Constituency();
    parameters.setNumberOfSeats(1,3);
    parameters.setNumberOfCandidates(NUM_CANDIDATES);
    // TODO precondition not established
    ballotCounting.setup(parameters); //@ nowarn;
    // All candidates get one vote; draw lots to resolve ties
    for (int i=0; i < NUM_CANDIDATES; i++) {
      int[] preferences =
        {parameters.getCandidate(i).getCandidateID()};
      ballotBox.accept(preferences);
    }
    ballotCounting.load(ballotBox);
  }

  /**
	 * Test selection of highest continuing candidate
	 */
	public void testEvent() {
	  assertTrue (ballotCounting != null);
    ballotCounting.startCounting();
    final int winner = ballotCounting.findHighestCandidate();
    assertTrue(winner == candidateToWin);
    final int countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));
    // Test election without surplus
    assertTrue(ballotCounting.getTotalSumOfSurpluses() == 0);
  }

 	

 	

}
