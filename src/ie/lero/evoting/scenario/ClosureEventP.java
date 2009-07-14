/**
 * 
 */
package ie.lero.evoting.scenario;

import election.tally.State;


/**
 * @author Dermot Cochran
 *
 */
public class ClosureEventP extends VotailEventTestCase {

	/**
	 * @param name Name of test
	 */
	public ClosureEventP(String name) {
		super(name);
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	protected void tearDown() throws Exception {
		super.tearDown();
	}

	public void testClosureEvent() {
		assertTrue(ballotCounting.getStatus() == State.FINISHED);
		//@ assert ballotCounting.getStatus() == election.tally.AbstractBallotCounting.FINISHED;
	}
}
