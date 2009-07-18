/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotCounting;
import election.tally.ElectionStatus;


/**
 * @author Dermot Cochran
 *
 */
public class ClosureEventP extends TestCase {

 	private BallotCounting ballotCounting;

  protected void setEventCode() {
		// TODO Auto-generated method stub
		
	}

 	protected void setUpBallotBox() {
		// TODO Auto-generated method stub
		
	}

 	protected void setUpParameters() {
		// TODO Auto-generated method stub
		
	}

 	public void testEvent() {
		// TODO Auto-generated method stub
		
	}

	protected void setUp() throws Exception {
		super.setUp();
	}

	protected void tearDown() throws Exception {
		super.tearDown();
	}

	public void testClosureEvent() {
		assertTrue(ballotCounting.getStatus() == ElectionStatus.FINISHED);
		//@ assert ballotCounting.getStatus() == election.tally.AbstractBallotCounting.FINISHED;
	}
}
