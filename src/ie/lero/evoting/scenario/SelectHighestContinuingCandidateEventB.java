/**
 * 
 */
package ie.lero.evoting.scenario;


/**
 * @author Dermot Cochran
 *
 */
public class SelectHighestContinuingCandidateEventB extends AbstractEvent {

	/**
	 * Test selection of highest continuing candidate
	 */
	public void testEvent () {
		int winner = ballotCounting.findHighestCandidate();
		
	}

}
