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

 	protected void setEventCode() {
      eventCode = 'B';		
	}

 	protected void setUpBallotBox() {
		// TODO Auto-generated method stub
		
	}

 	protected void setUpParameters() {
		// TODO Auto-generated method stub
		
	}

}
