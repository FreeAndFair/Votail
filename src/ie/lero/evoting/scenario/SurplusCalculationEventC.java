package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.AbstractCountStatus;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.CandidateStatus;
import election.tally.Constituency;

/**
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 *         Dermot Cochran</a>
 */
public class SurplusCalculationEventC extends TestCase {

  private static final int QUOTA = 26;
  private static final int NUM_BALLOTS = 100;
  private static final int NUM_SEATS = 3;
  private static final int NUM_CANDIDATES = 7;
  protected BallotCounting ballotCounting;
  protected Constituency parameters;
  protected BallotBox ballotBox;

  /**
   * Create the scenario data needed
   */
  protected void setUp() {
    ballotCounting = new BallotCounting();
    ballotBox = new BallotBox();
    parameters = new Constituency();
    parameters.setNumberOfSeats (NUM_SEATS, NUM_SEATS);
    parameters.setNumberOfCandidates(NUM_CANDIDATES);

    int[] preferences = new int[NUM_CANDIDATES];

    for (int i = 0; i < NUM_CANDIDATES; i++) {
      preferences[i] = parameters.getCandidate(i).getCandidateID();
      assertTrue(parameters.getCandidate(i).getStatus() == CandidateStatus.CONTINUING);
      assertTrue(parameters.getCandidate(i).getTotalAtCount(0) == 0);
    }

    final int numberOfVotes = NUM_BALLOTS;

    assertTrue(numberOfVotes <= Ballot.MAX_BALLOTS);
    assertTrue(ballotBox.size() == 0);
    final Ballot testBallot = new Ballot();
    testBallot.load(preferences);
    for (int b = 0; b < numberOfVotes; b++) {
      ballotBox.accept(testBallot);
    }
  }

  /**
   * Test the distribution of surplus ballots.
   */
  public void testDistributionOfSurplus() {

    ballotCounting.setup(parameters);
    ballotCounting.load(ballotBox);
    assertTrue(QUOTA == ballotCounting.getQuota());

    // Find and distribute the first surplus
    ballotCounting.startCounting();
    final int indexOfHighestCandidate = ballotCounting.findHighestCandidate();
    assertTrue(0 <= indexOfHighestCandidate);

    int countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));

    ballotCounting.electCandidate(indexOfHighestCandidate);

    countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));

    ballotCounting.countStatus.changeState(
      AbstractCountStatus.READY_TO_ALLOCATE_SURPLUS);
    ballotCounting.distributeSurplus(indexOfHighestCandidate);
    countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));

    ballotCounting.count();
    countState = ballotCounting.countStatus.getState();
    assertTrue(ballotCounting.countStatus.isPossibleState(countState));
  }
}
