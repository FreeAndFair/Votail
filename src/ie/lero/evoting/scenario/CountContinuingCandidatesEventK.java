package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class CountContinuingCandidatesEventK extends TestCase {

 	public void testEvent() {
 	 BallotCounting ballotCounting = new BallotCounting();
   Constituency constituency = new Constituency();
   constituency.setNumberOfSeatsInThisElection(3);
   constituency.setTotalNumberOfSeats(3);
   constituency.setNumberOfCandidates(4);
   ballotCounting.setup(constituency);
	 assertTrue (4 == ballotCounting.getContinuingCandidates());
	}
}
