package ie.votail.model;

import ie.votail.model.factory.BallotBoxFactory;

import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.Candidate;
import election.tally.Constituency;

/**
 * Election Configuration, including generated Ballot Box and related 
 * information derived from an Alloy model solution for an Electoral Scenario.
 * 
 * @author Dermot Cochran
 */
public class ElectionConfiguration extends BallotBox {
  
  /** The null value for a candidate ID */
  public static final int NO_CANDIDATE_ID = 0;
  
  public static final int MAX_VOTES = Ballot.MAX_BALLOTS;
  
  protected int numberOfWinners;

  protected int numberOfSeats;

  protected int numberOfCandidates;

  private Logger logger;

  //@ invariant numberOfCandidateIDs <= numberOfCandidates;
  private int numberOfCandidateIDs;

  //@ invariant numberOfCandidateIDs <= candidateIDs.length;
  private int[] candidateIDs;

  private int currentBallotID;

  public ElectionConfiguration() {
    logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    candidateIDs = new int [Candidate.MAX_CANDIDATES];
    for (int i=0; i < candidateIDs.length; i++) {
      candidateIDs[i] = Candidate.NO_CANDIDATE;
    }
    currentBallotID = 0;
  }

  /**
   * Extract the list of ballot identifiers from an Alloy tuple set
   * 
   * @param tupleSet The Alloy tuple set
   */
  public void extractPreferences(/*@ non_null*/ A4TupleSet tupleSet) {
    int[] preferences = new int[numberOfCandidates];
    int lengthOfBallot = 0;
    
    for (A4Tuple tuple: tupleSet) {  
      if (tuple.arity() == 3) {
        String ballot = tuple.atom(0).substring(7); // prefix = "Ballot$"
        int ballotID = 1 + Integer.parseInt(ballot);
        int preference = Integer.parseInt(tuple.atom(1));
        //@ assert 0 <= preference
        String candidate = tuple.atom(2).substring(10); // prefix = "Candidate$"
        int candidateID = 1 + Integer.parseInt(candidate); 
        logger.info("ballot = " + ballotID + ", preference = " + (preference+1) +
                    ", candidate = " + candidateID);
        updateCandidateIDs(candidateID);
        
        if (ballotID != currentBallotID && 0 < lengthOfBallot) {
          currentBallotID = ballotID;
          lengthOfBallot = 0;
          this.accept (preferences); // add these preferences to the ballot box
          preferences = new int[Candidate.MAX_CANDIDATES]; // reset values
        }
        preferences[preference] = candidateID;
        lengthOfBallot++;
      }
      else {
        logger.warning("Unexpected arity for this tuple: " + tuple.toString());
      }
    }
    this.accept (preferences); // add these preferences to the ballot box
  }

  
//@ ensures numberOfCandidateIDs <= numberOfCandidates;
  protected void updateCandidateIDs(int candidateID) {
    for (int i=0; i < numberOfCandidateIDs; i++) {
      if (candidateID == candidateIDs[i]) {
        return;
      }
    }
    candidateIDs[numberOfCandidateIDs] = candidateID;
    numberOfCandidateIDs++;
  }
  
  
  /**
   * Generate a constituency list of Candidates to match the Ballot Box for this scenario
   * 
   * @return The constituency with matching candidate ID numbers
   */
  public Constituency getConstituency() {
    Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(this.numberOfWinners, this.numberOfSeats);
    constituency.load(this.candidateIDs, this.numberOfCandidates);
    return constituency;
  }

  //@ requires 0 < theNumberOfWinners
  //@ ensures this.numberOfWinners == theNumberOfWinners
  public void setNumberOfWinners(int theNumberOfWinners) {
    this.numberOfWinners = theNumberOfWinners;
  }

  //@ requires this.numberOfWinners <= theNumberOfSeats
  //@ ensures this.numberOfSeats == theNumberOfSeats
  public void setNumberOfSeats(int theNumberOfSeats) {
    this.numberOfSeats = theNumberOfSeats;
  }

  public void setNumberOfCandidates(int theNumberOfCandidates) {
    this.numberOfCandidates = theNumberOfCandidates;
  }
}