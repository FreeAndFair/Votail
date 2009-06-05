package ie.lero.evoting.scenario;

import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.ElectionParameters;
import election.tally.dail.DailBallotCounting;

/**
 * @author Dermot
 *
 */
public class ElectionOfHighestCandidate {

	protected DailBallotCounting ballotCounting;
	protected ElectionParameters parameters;
	protected Candidate candidate;
	protected BallotBox ballotBox;

	/**
	 * 
	 */
	public void testElectionOfCandidate() {
 		//@ assert candidate.getStatus() == Candidate.CONTINUING;
		candidate.declareElected();
 		//@ assert candidate.getStatus() == Candidate.ELECTED;
	}

	protected void setUp() {
		ballotCounting = new DailBallotCounting();
		parameters = new ElectionParameters();
		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;
 		parameters.numberOfCandidates = 3;
		candidate = new Candidate();
		ballotBox = new BallotBox();
		ballotBox.numberOfBallots = 2;
		Ballot ballot1 = new Ballot();
		int[] list1 = {candidate.getCandidateID()};
		ballot1.load(list1);
		Ballot ballot2 = new Ballot();
		int[] list2 = {candidate.getCandidateID()};
		ballot2.load(list2);
	}
	
	
	/**
	 * 
	 * 
	 * 
	 */
	public void main () {
		setUp();
		testElectionOfCandidate();
	}

}
