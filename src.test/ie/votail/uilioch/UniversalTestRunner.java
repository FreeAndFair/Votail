package ie.votail.uilioch;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectionResult;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;

import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.FileHandler;

import com.hexmedia.prstv.Candidate;
import com.hexmedia.prstv.Display;
import com.hexmedia.prstv.Election;
import com.hexmedia.prstv.Surplus;

import coyle_doyle.election.BallotPaper;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class UniversalTestRunner extends Uilioch {
  
  /**
   * @author dero
   *
   */
  protected class VotailElectionResult extends ElectionResult {
    
    /**
     * @param candidates
     * @param theQuota
     * @param theThreshold
     */
    public VotailElectionResult(election.tally.Candidate[] candidates,
        int theQuota, int theThreshold) {
      super(candidates, theQuota, theThreshold);
    }
    
  }

  public static final String RUNNER_LOGFILENAME = "logs/uilioch/runner.log";
  public static final int INITIAL_SCOPE = 6;
  public static final String LOG_NAME = "Cross Testing and Validation";
  public static final String SUFFIX = ".txt";
  public static final String TESTDATA_PREFIX = "/var/tmp/uilioch";
  public static final int GENERAL_ELECTION = 0;
  
  protected class VotailRunner extends BallotCounting {
    /**
     * Run the whole election count.
     * 
     * @param ballotBox
     *          Ballot box and election configuration
     * @return The election results
     */
    //@ requires state == EMPTY;
    //@ ensures state == FINISHED;
    public final /*@ non_null @*/ElectionResult run(
      final Constituency constituency,
      final BallotBox ballotBox) {
      this.setup(constituency);
      this.load(ballotBox);
      if (0 < this.totalNumberOfVotes) {
        this.count();
      }
      
      logger.info(this.getResults());
      logger.info(ballotBox.size() + " ballots");
      logger.info(this.getTotalNumberOfCandidates() + " candidates");
      
      return new VotailElectionResult(this.candidates, this.getQuota(), 
          this.getSavingThreshold());
    }
  }
  
  /**
   * Test all scenarios for all known implementations
   * 
   * @param capacity
   */
  public void testScenarios(final int capacity, final int width) {
    
    try {
      final FileHandler handler =
          new FileHandler(UniversalTestRunner.RUNNER_LOGFILENAME);
      logger.addHandler(handler);
    }
    catch (SecurityException e1) {
      logger.info("not allowed to attach logfile" + e1.toString());
    }
    catch (IOException e1) {
      logger.info("not able to find logfile" + e1.toString());
    }
    
    final String dataFilename = getFilename();
    
    try {
      
      final FileInputStream fis = new FileInputStream(dataFilename);
      final ObjectInputStream objectInputStream = new ObjectInputStream(fis);
      
      while (true) {
        
        // Deserialize and load the next Ballot Box
        final ElectionData testData = getTestData(objectInputStream);
        
        if (testData == null || testData.getScenario() == null
            || testData.getBallots().length == 0) {
          logger.warning("Test data is either missing or not readable");
          break;
        }
        
        final ElectionResult votailResult =
            runVotail(new ElectionConfiguration(testData));
        logger.info(votailResult.toString());
//        final ElectionResult coyleDoyleResult =
//            runCoyleDoyle(new ElectionConfiguration(testData));
//        logger.info(coyleDoyleResult.toString());
        //          ElectionResult hexMediaResult =
        //              runHexMedia(new ElectionConfiguration(testData));
        
        //          assert hexMediaResult.equals(coyleDoyleResult);
//        if (coyleDoyleResult.equals(votailResult)) {
//          logger.info("We get the same results for this scenario:" +
//          		" " +
//              testData.getScenario().toString());
//        }
        //          assert votailResult.equals(hexMediaResult);
        
      }
      objectInputStream.close();
      
    }
    catch (IOException e) {
      logger.info("Finished reading test data because " + e.getMessage());
    }
    finally {
      logger.info("Finished!");
    }
    
  }
  
  /**
   * Run Votail with test data and match results with expected scenario
   * 
   * @param ballotBox
   *          The test data
   * @return The actual result
   */
  protected ElectionResult runVotail(final ElectionConfiguration ballotBox) {
    final VotailRunner votail = new VotailRunner();
    final Constituency constituency = ballotBox.getConstituency();
    final ElectoralScenario scenario = ballotBox.getScenario();

    int seatsInElection;
    final int seatsInConstituency = scenario.numberOfWinners();
    logger.info(seatsInConstituency + " seats in constituency");
    if (scenario.isByeElection()) {
      seatsInElection = 1;
      logger.info("bye-election for 1 seat");
    }
    else {
      seatsInElection = seatsInConstituency;
      logger.info(seatsInElection + " seats for election");
    }
    
    constituency.setNumberOfSeats(seatsInElection, seatsInConstituency);
    final int numberOfCandidates = scenario.getNumberOfCandidates();
    constituency.setNumberOfCandidates(numberOfCandidates);
    logger.info(numberOfCandidates + " candidates");
    
    final ElectionResult result = votail.run(constituency, ballotBox);
    
    if (!scenario.check(votail)) {
      logger.warning("Unexpected results for scenario " + scenario);
    }
    
    
    return result;
  }
  
  /**
   * @param scenario
   * @param result
   */
  protected void checkResult(final ElectoralScenario scenario, final ElectionResult result) {
    if (!scenario.matchesResult(result)) {
      logger.severe("Expected result: " + scenario.toString()
          + " but actual result " + result.toString());
    }
  }
  
  protected String getRank(Ballot ballot, int candidateID) {
    for (int index = 0; index < ballot.remainingPreferences(); index++) {
      if (ballot.getNextPreference(index) == candidateID) {
        return Integer.toString(index);
      }
    }
    
    return " "; // White space if no preference for this candidate
  }

  public static void main(final String[] args) {
    final UniversalTestRunner uilioch = new UniversalTestRunner();
    uilioch.testScenarios(10, 10);
  }
}
