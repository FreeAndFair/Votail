package ie.votail.scenario;

import ie.votail.tally.BallotCounting;
import ie.votail.tally.Constituency;
import junit.framework.TestCase;

public class CountContinuingCandidatesEventK extends TestCase {

 	public void testEvent() {
 	 final BallotCounting ballotCounting = new BallotCounting();
   final Constituency constituency = new Constituency();
   constituency.setNumberOfSeats(3,3);
   constituency.setNumberOfCandidates(4);
   // TODO precondition not established
   ballotCounting.setup(constituency); //@ nowarn;
	 assertTrue (4 == ballotCounting.getContinuingCandidates());
	}
}
