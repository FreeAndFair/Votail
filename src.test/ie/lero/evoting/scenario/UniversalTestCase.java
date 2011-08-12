package ie.lero.evoting.scenario;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectionResult;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;
import ie.votail.uilioch.Uilioch;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.logging.FileHandler;
import java.util.logging.Logger;

import junit.framework.TestCase;
import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class UniversalTestCase extends TestCase {
  
  protected static final String FILENAME_PREFIX = "testdata/";
  protected static final String DATA_FILENAME_SUFFIX = "_election.data";
  protected static final Logger logger = Logger.getAnonymousLogger();
  
  /**
   * @author Dermot Cochran
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

  public static final String LOGFILENAME = "logs/uilioch/votail.log";
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
   * Test all known scenarios for Votail
   * 
   */
  public void testScenarios() {
    
    Uilioch uilioch = new Uilioch();
    
    try {
      final FileHandler handler =
          new FileHandler(LOGFILENAME);
      logger.addHandler(handler);
    }
    catch (SecurityException e1) {
      logger.info("not allowed to attach logfile" + e1.toString());
    }
    catch (IOException e1) {
      logger.info("not able to find logfile" + e1.toString());
    }
    
    final String dataFilename = uilioch.getFilename();
    
    try {
      
      final FileInputStream fis = new FileInputStream(dataFilename);
      final ObjectInputStream objectInputStream = new ObjectInputStream(fis);
      
      while (true) {
        
        // Deserialize and load the next Ballot Box
        final ElectionData testData = uilioch.getTestData(objectInputStream);
        
        if (testData == null || testData.getScenario() == null
            || testData.getBallots().length == 0) {
          logger.warning("Test data is either missing or not readable");
          break;
        }
        
        final ElectionResult votailResult =
            runVotail(new ElectionConfiguration(testData));
        logger.info(votailResult.toString());
        
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

  
}
