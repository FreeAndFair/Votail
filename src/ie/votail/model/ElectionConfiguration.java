package ie.votail.model;

import ie.votail.model.factory.BallotBoxFactory;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInput;
import java.io.ObjectInputStream;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
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
  private static final long serialVersionUID = 1L;

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

  /**
   * Load election configuration from a file.
   * 
   * @param filename
   */
  public ElectionConfiguration(String filename) {
    setup();
    
    InputStream file;
    InputStream buffer;
    ObjectInput input;
    
    try {
    file = new FileInputStream(filename);
    buffer = new BufferedInputStream(file);
    input = new ObjectInputStream(buffer);
    
      try {
        this.ballots = (Ballot[]) input.readObject();
        this.candidateIDs = (int[]) input.readObject();
      }
      catch (Exception e) {
        logger.severe(e.getLocalizedMessage());
      }
      finally {
        input.close();
        buffer.close();
        file.close();
      }
    }
    catch (FileNotFoundException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IOException e) {
      logger.severe(e.getLocalizedMessage());
    }
    
  }

  /**
   * Create an empty election configuration, with no data yet.
   * 
   */
  public ElectionConfiguration() {
    setup();
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
   * Save the Election Configuration data
   * 
   * @param ballotboxFilename
   */
  public void writeToFile(String ballotboxFilename) {
    try {
      OutputStream file = new FileOutputStream(ballotboxFilename);
      OutputStream buffer = new BufferedOutputStream(file);
      ObjectOutput output = new ObjectOutputStream(buffer);
      try {
        output.writeObject(this.ballots);
        output.writeObject(this.candidateIDs);
      }
      finally {
        output.close();
        buffer.close();
        file.close();
      }
    }
    catch (FileNotFoundException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IOException e) {
      logger.severe(e.getLocalizedMessage());
    }
    
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
}