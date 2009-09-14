package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Election;

public class ElectRemainingCandidatesEventN extends TestCase {

 	public void testEvent() {
 	 BallotCounting ballotCounting = new BallotCounting();
   Election election = new Election();
   election.numberOfSeatsInThisElection = 3;
   election.totalNumberOfSeats = 3;
   election.setNumberOfCandidates(4);
   ballotCounting.setup(election);		
   BallotBox ballotBox = new BallotBox();
   Ballot ballot = new Ballot();
   for (int i=0; i<3; i++) {
     ballot.setFirstPreference(election.getCandidate(i).getCandidateID());
     ballotBox.accept(ballot);
   }
   ballotCounting.load(ballotBox);
   ballotCounting.count();
   for (int i=0; i<3; i++) {
     assertTrue (ballotCounting.isElected(election.getCandidate(i)));
   }
	}

}
