package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;

/**
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */
public class BallotCountingStartsEventR extends TestCase {

  private Election parameters;
  private BallotBox ballotBox;
  private BallotCounting ballotCounting;

  protected void setUp() throws Exception {
    super.setUp();
    setUpParameters();
    setUpBallotBox();
    ballotCounting = new BallotCounting();
    ballotCounting.setup(parameters);
    ballotCounting.load(ballotBox);
 }

  protected void setUpBallotBox() {
		ballotBox = new BallotBox();
		MockBallot ballot1, ballot2;
		MockBallot ballot = new MockBallot(); //@ nowarn;
 		ballot.setFirstPreference(candidate2.getCandidateID());
 		ballotBox.accept(ballot);
		
 		for (int i = 0; i < 50; i++) {
 			  ballot1 = new MockBallot();
  			  ballot1.setFirstPreference(candidate1.getCandidateID());
 			  ballotBox.accept(ballot1);
 			  ballot2 = new MockBallot();
 			  ballot2.setFirstPreference(candidate2.getCandidateID());
 			  ballotBox.accept(ballot2);
 			}
	}

 	/*@ assignable parameters, candidate1, candidate2;
 	  @*/
	protected void setUpParameters() {
	  parameters = new Election();
		parameters.totalNumberOfSeats = 1;
		parameters.numberOfSeatsInThisElection = 1;
		parameters.numberOfCandidates = 2;
		candidate1 = new Candidate();
		candidate2 = new Candidate();
 		
 		Candidate[] list = {candidate1,candidate2};
		parameters.setCandidateList(list);
		
	}

	protected Candidate candidate1, candidate2;
	 

	/**
	 * Test start-of-count event.
	 */
	public void testEvent() {
		 
		assertTrue(ballotCounting.getStatus() == election.tally.ElectionStatus.PRECOUNT);
		ballotCounting.calculateFirstPreferences();
	}
}
