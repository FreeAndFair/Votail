package ie.lero.evoting.scenario;

import election.tally.BallotCounting;
import election.tally.Election;
import junit.framework.TestCase;

public class CountContinuingCandidatesEventK extends TestCase {

 	 

 	public void testEvent() {
 	 BallotCounting ballotCounting = new BallotCounting();
   Election election = new Election();
   election.numberOfCandidates = 4;
   election.numberOfSeatsInThisElection = 3;
   election.totalNumberOfSeats = 3;
   ballotCounting.setup(election);
	 assertTrue (4 == ballotCounting.getContinuingCandidates());
	}

	 

}
