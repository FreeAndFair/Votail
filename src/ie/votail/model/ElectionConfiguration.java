package ie.votail.model;

import ie.votail.model.factory.BallotBoxFactory;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInput;
import java.io.ObjectInputStream;
import java.io.Serializable;
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
public class ElectionConfiguration extends BallotBox implements Serializable {
  
  /**
   * 
   */
  private static final long serialVersionUID = 2644255293869580385L;

  protected ElectoralScenario scenario;

  /* The null value for a candidate ID */
  public static final int NO_CANDIDATE_ID = 0;
  
  public static final int MAX_VOTES = Ballot.MAX_BALLOTS;
  
  protected int numberOfWinners;

  protected int numberOfSeats;

  protected int numberOfCandidates;

  protected transient Logger logger;

  //@ invariant numberOfCandidateIDs <= numberOfCandidates;
  protected int numberOfCandidateIDs;

  //@ invariant numberOfCandidateIDs <= candidateIDs.length;
  protected int[] candidateIDs;

  protected int currentBallotID;

  /**
   * Create an empty election configuration, with no data yet.
   * 
   */
  public ElectionConfiguration() {
    setup();
  }

  /**
   * Create an empty Election configuration for a given Scenario
   * 
   * @param canonical
   */
  public ElectionConfiguration(ElectoralScenario canonical) {
    setup();
    this.scenario = canonical;
   }

  /**
   * 
   */
  protected void setup() {
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
   * Generate a constituency list of Candidates to match the Ballot Box for 
   * this scenario
   * 
   * @return The constituency with matching candidate ID numbers
   */
  public Constituency getConstituency() {
    Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(this.numberOfWinners, this.numberOfSeats);
    constituency.load(this.candidateIDs);
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

  /**
   * Create a new election configuration with the same ballot box and
   * constituency data.
   * 
   * @return
   */
  //@ ensures this.equals(\result);
  public ElectionConfiguration copy() {
    ElectionConfiguration copy = new ElectionConfiguration();
    
    copy.ballots = this.ballots;
    copy.candidateIDs = this.candidateIDs;
    copy.numberOfSeats = this.numberOfSeats;
    copy.numberOfCandidates = this.numberOfCandidates;
    copy.numberOfWinners = this.numberOfWinners;
    
    return copy;
  }

  //@ ensures \result == this.scenario;
  public /*@ pure @*/ ElectoralScenario getScenario() {
    return this.scenario;
  }

  /**
   * @return the numberOfWinners
   */
  public int getNumberOfWinners() {
    return numberOfWinners;
  }

  /**
   * @return the numberOfSeats
   */
  public int getNumberOfSeats() {
    return numberOfSeats;
  }

  /**
   * @return the numberOfCandidates
   */
  public int getNumberOfCandidates() {
    return numberOfCandidates;
  }

  /**
   * @return the numberOfCandidateIDs
   */
  public int getNumberOfCandidateIDs() {
    return numberOfCandidateIDs;
  }

  /**
   * @return the candidateIDs
   */
  public int[] getCandidateIDs() {
    return candidateIDs;
  }

  /**
   * @return the currentBallotID
   */
  public int getCurrentBallotID() {
    return currentBallotID;
  }

  /**
   * @param scenario the scenario to set
   */
  public void setScenario(ElectoralScenario scenario) {
    this.scenario = scenario;
  }

  /**
   * @param numberOfCandidateIDs the numberOfCandidateIDs to set
   */
  public void setNumberOfCandidateIDs(int numberOfCandidateIDs) {
    this.numberOfCandidateIDs = numberOfCandidateIDs;
  }

  /**
   * @param candidateIDs the candidateIDs to set
   */
  public void setCandidateIDs(int[] candidateIDs) {
    this.candidateIDs = candidateIDs;
  }

  /**
   * @param currentBallotID the currentBallotID to set
   */
  public void setCurrentBallotID(int currentBallotID) {
    this.currentBallotID = currentBallotID;
  }
  
  /**
   * Get the contents of the ballot box
   * 
   * @return The ballots
   */
  public Ballot[] getBallots() {
    return ballots;
  }
}