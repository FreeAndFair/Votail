/**
 * 
 */
package ie.lero.evoting.scenario;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.Election;
import election.tally.mock.MockBallot;
import election.tally.mock.MockCandidate;
import junit.framework.TestCase;

/**
 * @author Dermot Cochran
 *
 */
public class TransfersFromSurplusEventD extends TestCase {

	public void testEvent() {
	   BallotCounting ballotCounting = new BallotCounting();
	   Election election = new Election();
	   election.numberOfCandidates = 20;
	   election.numberOfSeatsInThisElection = 3;
	   election.totalNumberOfSeats = 3;
	   Candidate[] candidates = MockCandidate.generateCandidates(
			   election.numberOfCandidates);
	   election.setCandidateList(candidates);
	   ballotCounting.setup(election);    
	   BallotBox ballotBox = new BallotBox();
	   MockBallot ballot = new MockBallot();
	   for (int i=0; i<3; i++) {
	     ballot.setFirstPreference(candidates[0].getCandidateID());
	     ballotBox.accept(ballot);
	   }
	   ballotCounting.load(ballotBox);
	   int winner = ballotCounting.findHighestCandidate();
	   ballotCounting.electCandidate(winner);
	   assertTrue (19 == ballotCounting.getContinuingCandidates());
	   assertTrue (2 == ballotCounting.getRemainingSeats());
	   assertTrue (3 == ballotBox.size());
	   ballotCounting.count();
	}
}
