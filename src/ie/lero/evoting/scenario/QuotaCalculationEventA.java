/**
 * 
 */
package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotCounting;
import election.tally.Election;
import election.tally.ElectionStatus;


/**
 * @author Dermot Cochran
 *
 */
public class QuotaCalculationEventA extends TestCase {
  
  BallotCounting ballotCounting;
  Election parameters;

	protected void setUp() throws Exception {
		super.setUp();
	}

	protected void tearDown() throws Exception {
		super.tearDown();
	}
	
	/**
	 * Test the calculation of quota and deposit saving threshold.
	 */
	public void testCalculateQuota () {
		assertTrue(ballotCounting != null);
		assertTrue(ballotCounting.getStatus() == ElectionStatus.EMPTY);
		//@ assert ballotCounting.getStatus() == election.tally.AbstractBallotCounting.EMPTY;
		ballotCounting.setup(parameters);
		
		assertTrue(1 == ballotCounting.report().getTotalNumberOfCounts());
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
	}

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

}
