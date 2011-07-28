package ie.votail.model;

import ie.votail.model.data.ElectionData;

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
  
  protected static final transient Logger logger = Logger.getAnonymousLogger();
  
  //@ invariant numberOfCandidateIDs <= numberOfCandidates;
  protected int numberOfCandidateIDs;
  
  //@ invariant numberOfCandidateIDs <= candidateIDs.length;
  protected int[] candidateIDs;
  
  protected transient int currentBallotID = 0;
  
  /**
   * Create an Election Configuration by deserialisation
   * 
   */
  protected ElectionConfiguration() {
    super();
  }
  
  /**
   * Create an empty Election configuration for a given scenario
   * 
   * @param theScenario The electoral scenario 
   */
  public ElectionConfiguration(final ElectoralScenario theScenario) {
    super();
    this.scenario = theScenario;
    candidateIDs = new int[Candidate.MAX_CANDIDATES];
    for (int i = 0; i < candidateIDs.length; i++) {
      candidateIDs[i] = Candidate.NO_CANDIDATE;
    }
  }
  
  /**
   * Extract the list of ballot identifiers from an Alloy tuple set
   * 
   * @param tupleSet
   *          The Alloy tuple set
   */
  public void extractPreferences(final /*@ non_null*/A4TupleSet tupleSet) {
    int[] preferences = new int[numberOfCandidates];
    int lengthOfBallot = 0;
    
    for (A4Tuple tuple : tupleSet) {
      if (tuple.arity() == 3) {
        final String ballot = tuple.atom(0).substring(7); // prefix = "Ballot$"
        final int ballotID = 1 + Integer.parseInt(ballot);
        final int preference = Integer.parseInt(tuple.atom(1));
        //@ assert 0 <= preference
        final String candidate = tuple.atom(2).substring(10); // prefix = "Candidate$"
        final int candidateID = 1 + Integer.parseInt(candidate);
        logger.info("ballot = " + ballotID + ", preference = "
            + (preference + 1) + ", candidate = " + candidateID);
        updateCandidateIDs(candidateID);
        
        if (ballotID != currentBallotID) { // Start of new ballot paper
          currentBallotID = ballotID;
          if (0 < lengthOfBallot) {
            this.accept(preferences); // Add to the ballot box
            lengthOfBallot = 0;
          }
          preferences = new int[Candidate.MAX_CANDIDATES]; // reset values
        }
        preferences[preference] = candidateID;
        lengthOfBallot++;
      }
      else {
        logger.warning("Unexpected arity for this tuple: " + tuple.toString());
      }
    }
    this.accept(preferences); // add these preferences to the ballot box
  }
  
  //@ ensures numberOfCandidateIDs <= numberOfCandidates;
  protected final void updateCandidateIDs(final int candidateID) {
    for (int i = 0; i < numberOfCandidateIDs; i++) {
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
    final Constituency constituency = new Constituency();
    constituency.setNumberOfSeats(this.numberOfWinners, this.numberOfSeats);
    constituency.load(this.candidateIDs);
    return constituency;
  }
  
  //@ requires 0 < theNumberOfWinners
  //@ ensures this.numberOfWinners == theNumberOfWinners
  public void setNumberOfWinners(final int theNumberOfWinners) {
    this.numberOfWinners = theNumberOfWinners;
  }
  
  //@ requires this.numberOfWinners <= theNumberOfSeats
  //@ ensures this.numberOfSeats == theNumberOfSeats
  public void setNumberOfSeats(final int theNumberOfSeats) {
    this.numberOfSeats = theNumberOfSeats;
  }
  
  //@ requires 0 < theNumberOfCandidates;
  //@ ensures this.numberOfCandidates == theNumberOfCandidates;
  public void setNumberOfCandidates(final int theNumberOfCandidates) {
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
    return new ElectionConfiguration(this.export());
  }
  
  //@ ensures \result == this.scenario;
  public/*@ pure @*/ElectoralScenario getScenario() {
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
  /*@ ensures (\forall int i; 0 <= i && i < this.candidateIDs.length;
    @   \result[i] == this.candidatesIDs[i]);
    @*/
  public int[] getCandidateIDs() {
    int [] theCandidateIDs = new int[this.candidateIDs.length];
    for (int index = 0; index < this.candidateIDs.length; index++) {
      theCandidateIDs[index] = this.candidateIDs[index];
    }
    return theCandidateIDs;
  }
  
  /**
   * @return the currentBallotID
   */
  public int getCurrentBallotID() {
    return currentBallotID;
  }
  
  /**
   * @param theScenario
   *          the scenario to set
   */
  /*@ assignable this.scenario;
    @ ensures this.scenario == theScenario;
   */
  public void setScenario(final /*@ non_null @*/ ElectoralScenario theScenario) {
    this.scenario = theScenario;
  }
  
  /**
   * @param numberOfCandidateIDs
   *          the numberOfCandidateIDs to set
   */
  public void setNumberOfCandidateIDs(int numberOfCandidateIDs) {
    this.numberOfCandidateIDs = numberOfCandidateIDs;
  }
  
  /**
   * @param theCandidateIDs
   *          the candidateIDs to set
   */
  /*@ ensures (\forall int i; 0 <= i && i < theCandidateIDs.length;
   *   this.candidateIDs[i] == theCandidateIDs[i]);
   */
  public void setCandidateIDs(final int[] theCandidateIDs) {
    this.candidateIDs = new int[theCandidateIDs.length];
    for (int index = 0; index < theCandidateIDs.length; index++) {
      this.candidateIDs[index] = theCandidateIDs[index];
    }
  }
  
  /**
   * @param currentBallotID
   *          the currentBallotID to set
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
  
  /**
   * Prune empty ballots and candidate IDs from data
   * 
   * @return The minimal ballot configuration
   */
  public ElectionConfiguration trim() {
    ElectionConfiguration copy = new ElectionConfiguration();
    
    copy.ballots = new Ballot[this.numberOfBallots];
    for (int i = 0; i < this.numberOfBallots; i++) {
      copy.ballots[i] = this.ballots[i];
    }
    copy.candidateIDs = new int[this.numberOfCandidates];
    for (int j = 0; j < this.numberOfCandidates; j++) {
      copy.candidateIDs[j] = this.candidateIDs[j];
    }
    
    copy.numberOfCandidates = this.numberOfCandidates;
    copy.numberOfWinners = this.getNumberOfWinners();
    copy.scenario = this.getScenario();
    copy.currentBallotID = this.currentBallotID;
    copy.index = this.index;
    copy.numberOfBallots = this.numberOfBallots;
    copy.numberOfSeats = this.numberOfSeats;
    return copy;
  }

  /**
   * Export the test data
   * 
   * @return The data needed for export
   */
  public /*@ pure @*/ ElectionData export() {
    ElectionData electionData = new ElectionData();
    electionData.setScenario(scenario);
    electionData.setBallots(ballots);
    
    return electionData;
  }
  
  /**
   * Load election data
   * 
   * @param electionData Electoral Scenario and Ballot Data
   */
  public ElectionConfiguration (ElectionData electionData) {
    super();
    final ElectoralScenario theScenario = electionData.getScenario();
    this.scenario = theScenario.canonical();
    candidateIDs = new int[Candidate.MAX_CANDIDATES];
    for (int i = 0; i < candidateIDs.length; i++) {
      candidateIDs[i] = Candidate.NO_CANDIDATE;
    }
    
    final Ballot[] theBallots = electionData.getBallots();
    if (theBallots != null) {
    for (int b = 0; b < theBallots.length; b++) {
      Ballot ballot = theBallots[b];
      if (ballot == null) {
        logger.warning("Unexpected empty ballot");
      }
      else {
        final int numberOfPreferences = ballot.getNumberOfPreferences();
        final int[] preferenceList = new int[numberOfPreferences];
        for (int p = 0; p < numberOfPreferences; p++) {
          preferenceList[p] = ballot.getNextPreference(p);
        }
          
        this.accept(preferenceList);
        // Recreate the anonymous list of candidates
        for (int preference = 0; preference < preferenceList.length; 
          preference++) {
          updateCandidateIDs(preferenceList[preference]);
        }
      }
    }
    }
  }
}