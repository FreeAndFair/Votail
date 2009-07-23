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

  private /*@ spec_public @*/ int numberOfCandidates;
  private /*@ spec_public @*/ Candidate[] candidates;
  private /*@ spec_public @*/ Election parameters;
  private /*@ spec_public @*/ BallotCounting ballotCounting;
  private /*@ spec_public @*/ BallotBox ballotBox;

	/**
	 * Execute this scenario.
	 */
	//@ requires ballotCounting != null;
	public final void testExclusion() {
	 	
	  assertTrue (ballotCounting.getStatus() == ElectionStatus.PRECOUNT);
	 	final int lowestCandidate = ballotCounting.findLowestCandidate();
		ballotCounting.eliminateCandidate(lowestCandidate);
		assertTrue (ballotCounting.isDepositSaved(lowestCandidate));
		assertTrue (5 == ballotCounting.getContinuingCandidates());
		final int secondLowest = ballotCounting.findLowestCandidate();
		assertTrue (secondLowest != lowestCandidate);
		ballotCounting.eliminateCandidate(secondLowest);
		ballotCounting.count();
		assertTrue (candidates[secondLowest].getStatus() == CandidateStatus.ELIMINATED);
    assertTrue (candidates[lowestCandidate].getStatus() == CandidateStatus.ELIMINATED);

 	}

  //@ requires candidates != null;
	//@ requires numberOfCandidates < candidates.length;
 	protected void setUpBallotBox() {
 	  int numberOfVotes;
 	  MockBallot ballot = new MockBallot();
 		for (int i = 0; i < numberOfCandidates; i++) {
			 
			assertTrue (candidates[i].getStatus() == CandidateStatus.CONTINUING);
			numberOfVotes = i*1000;
			 
			// Generate first preference ballots
			for (int b = 0; b < numberOfVotes; b++) {
				
 			    ballot.setFirstPreference(candidates[i].getCandidateID());
				  ballotBox.accept(ballot);
			}
		}
	}

    //@ requires parameters != null;
 	//@ assignable candidates, numberOfCandidates;
 	protected void setUpParameters() {
 		parameters.totalNumberOfSeats = 4;
		parameters.numberOfSeatsInThisElection = 4;		
		

		// Generate candidates
		numberOfCandidates = 2 + parameters.numberOfSeatsInThisElection;
		candidates = new Candidate[numberOfCandidates];
		for (int i = 0; i < numberOfCandidates; i++) {
			candidates[i] = new Candidate();
			assertTrue (candidates[i].getStatus() == CandidateStatus.CONTINUING);
			int numberOfVotes = i*1000;
			candidates[i].addVote(numberOfVotes, 1);
			assertTrue (candidates[i].getTotalAtCount(1) == numberOfVotes);
		}
		
		parameters.setCandidateList(candidates);
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
