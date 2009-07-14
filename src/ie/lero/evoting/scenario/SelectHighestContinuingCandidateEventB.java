/**
 * 
 */
package ie.lero.evoting.scenario;

import election.tally.BallotCounting;
import election.tally.State;

/**
 * @author Dermot
 *
 */
public class SelectHighestContinuingCandidateEventB extends VotailEventTestCase {

	/**
	 * @param name Name of test
	 */
	public SelectHighestContinuingCandidateEventB(String name) {
		super(name);
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		ballotCounting = new BallotCounting();
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	protected void tearDown() throws Exception {
		super.tearDown();
	}

	/**
		 * Test a tie between two equal candidates.
		 */
		public void testTie () {
			assertTrue(ballotCounting.getStatus() == State.EMPTY);
 			ballotCounting.load(ballotBox);
			
 			assertTrue(ballotCounting.getStatus() == State.PRECOUNT);
			//@ assert ballotCounting.getStatus() == BallotCounting.PRECOUNT;
			ballotCounting.count();
			
			assertTrue((ballotCounting.getStatus() == State.FINISHED)
			    && (1 == ballotCounting.report().getNumberElected())
			   && (1 == ballotCounting.report().getTotalNumberOfCounts()));
			//@ assert ballotCounting.getStatus() == BallotCounting.FINISHED;
			//@ assert 1 == ballotCounting.report().getNumberElected();
			//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
		}

}
