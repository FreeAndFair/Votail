package ie.lero.evoting.scenario;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Candidate;
import election.tally.CandidateStatus;
import election.tally.Election;
import election.tally.ElectionStatus;
import election.tally.mock.MockBallot;

/**
 * This is a test for the correctness of the ballot counting process in the 
 * event that the lowest continuing candidate is excluded from election.
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 * 
 * @see election.tally.Candidate
 */
public class ExclusionEventJ extends TestCase {

  private int numberOfCandidates;
  private Election parameters;
  private BallotCounting ballotCounting;
  private BallotBox ballotBox;

	/**
	 * Execute this scenario.
	 */
	public final void testExclusion() {
	 	
	  assertTrue (ballotCounting.getStatus() == ElectionStatus.PRECOUNT);
	  ballotCounting.startCounting();
	 	final int lowestCandidate = ballotCounting.findLowestCandidate();
		ballotCounting.eliminateCandidate(lowestCandidate);
		assertTrue (ballotCounting.isDepositSaved(lowestCandidate) == false);
		assertTrue (5 == ballotCounting.getContinuingCandidates());
		final int secondLowest = ballotCounting.findLowestCandidate();
		assertTrue (secondLowest != lowestCandidate);
		ballotCounting.eliminateCandidate(secondLowest);
		ballotCounting.count();
		assertTrue (parameters.getCandidate(secondLowest).getStatus() 
		            == CandidateStatus.ELIMINATED);
		assertTrue (parameters.getCandidate(lowestCandidate).getStatus() 
		            == CandidateStatus.ELIMINATED);
 	}

 	protected void setUpBallotBox() {
 	  int numberOfVotes;
 	  MockBallot ballot = new MockBallot();
 		for (int i = 0; i < numberOfCandidates; i++) {
			 numberOfVotes = i*10;
			 
			// Generate first preference ballots
			for (int b = 0; b < numberOfVotes; b++) {
 			  ballot.setFirstPreference(parameters.getCandidate(i).getCandidateID());
				ballotBox.accept(ballot);
			}
		}
	}

  protected void setUpParameters() {
 		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;		
		numberOfCandidates = 2 + parameters.numberOfSeatsInThisElection;
		parameters.setNumberOfCandidates(numberOfCandidates);
	}
 	
 	protected void setUp() throws Exception {
    super.setUp();
    ballotBox = new BallotBox();
    ballotCounting = new BallotCounting();
    parameters = new Election();
    setUpParameters();
    setUpBallotBox();
    ballotCounting.setup(parameters);
    ballotCounting.load(ballotBox);
	}
}
