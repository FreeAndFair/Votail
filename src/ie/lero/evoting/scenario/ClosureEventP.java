/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.ElectionStatus;


/**
 * @author Dermot Cochran
 *
 */
public class ClosureEventP extends TestCase {

 	private BallotCounting ballotCounting;

   

	protected void setUp() throws Exception {
		super.setUp();
		ballotCounting = new BallotCounting();
		Election parameters = new Election();
		BallotBox ballotBox = new BallotBox();
		ballotCounting.setup(parameters);
		ballotCounting.load(ballotBox);
		ballotCounting.count();
	}

	public void testClosureEvent() {
		assertTrue(ballotCounting.getStatus() == ElectionStatus.FINISHED);
		//@ assert ballotCounting.getStatus() == election.tally.AbstractBallotCounting.FINISHED;
	}
}
