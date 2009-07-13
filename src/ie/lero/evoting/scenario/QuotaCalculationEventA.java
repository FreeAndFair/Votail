/**
 * 
 */
package ie.lero.evoting.scenario;


/**
 * @author Dermot Cochran
 *
 */
public class QuotaCalculationEventA extends VotailEventTestCase {

	/**
	 * @param name Name of test
	 */
	public QuotaCalculationEventA(String name) {
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
	
	/**
	 * Test the calculation of quota and deposit saving threshold.
	 */
	public void testCalculateQuota () {
		assertTrue(ballotCounting != null);
		assertTrue(ballotCounting.getStatus() == election.tally.AbstractBallotCounting.EMPTY);
		//@ assert ballotCounting.getStatus() == election.tally.AbstractBallotCounting.EMPTY;
		ballotCounting.setup(parameters);
		
		assertTrue(1 == ballotCounting.report().getTotalNumberOfCounts());
		//@ assert 1 == ballotCounting.report().getTotalNumberOfCounts();
	}

}
