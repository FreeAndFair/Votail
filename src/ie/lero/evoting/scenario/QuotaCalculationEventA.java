/**
 * 
 */
package ie.lero.evoting.scenario;

import election.tally.ElectionStatus;


/**
 * @author Dermot Cochran
 *
 */
public class QuotaCalculationEventA extends AbstractEvent {

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

}
