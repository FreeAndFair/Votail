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
import java.util.logging.Logger;

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
  
  public static final String LOGFILENAME = "logs/uilioch/runner.log";
  public static final int INITIAL_SCOPE = 6;
  public static final String LOG_NAME = "Cross Testing and Validation";
  public static final String SUFFIX = ".txt";
  public static final String TESTDATA_PREFIX = "/var/tmp/uilioch";
  public static final int GENERAL_ELECTION = 0;
  protected Logger logger;
  
  public class VotailRunner extends BallotCounting {
    /**
     * Run the whole election count
     * 
     * @param ballotBox
     *          Ballot box and election configuration
     * @return The election results
     */
    //@ requires state == EMPTY;
    //@ ensures state == FINISHED;
    public/*@ non_null @*/ElectionResult run(Constituency constituency,
        BallotBox ballotBox) {
      this.setup(constituency);
      this.load(ballotBox);
      if (0 < this.totalNumberOfVotes) {
      this.count();
      }
      else {
        logger.warning("Unexpected empty ballot box");
      }
      ElectionResult electionResult = new ElectionResult(this.candidates);
      return electionResult;
    }
  }
  
  /**
   * Test all scenarios for all known implementations
   * 
   * @param capacity
   */
  public void testScenarios(int capacity, int width) {
    logger = Logger.getLogger(this.getClass().getName());
    try {
      FileHandler handler = new FileHandler(UniversalTestRunner.LOGFILENAME);
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
      
      FileInputStream fis = new FileInputStream(dataFilename);
      ObjectInputStream in = new ObjectInputStream(fis);
      
      while (true) {
        
        // Derserialize and load the next Ballot Box
        final ElectionData testData = getTestData(in);
        
        if (testData == null || testData.getScenario() == null ||
            testData.getBallots().length == 0) {
          logger.warning("Test data is either missing or not readable");
          break;
        }

        
        ElectionConfiguration electionConfiguration =
            new ElectionConfiguration(testData);
                
        if (0 < electionConfiguration.getBallots().length) {
          
          // Test different implementations
          ElectionResult votailResult = runVotail(electionConfiguration);
//          ElectionResult coyleDoyleResult =
//              runCoyleDoyle(electionConfiguration.copy());
//          ElectionResult hexMediaResult =
//              runHexMedia(electionConfiguration.copy());
          
//          assert hexMediaResult.equals(coyleDoyleResult);
//          assert coyleDoyleResult.equals(votailResult);
//          assert votailResult.equals(hexMediaResult);
        }
        else {
          logger.warning("Empty ballot box data");
        }
      }
      in.close();
      
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
  protected ElectionResult runVotail(ElectionConfiguration ballotBox) {
    VotailRunner votail = new VotailRunner();
    ElectionResult result = votail.run(ballotBox.getConstituency(), ballotBox);
    
    ElectoralScenario scenario = ballotBox.getScenario();
    
    if (scenario == null) {
      logger.warning("Unexpected null scenario");
    }
    
    else if (!scenario.check(votail)) {
      logger.warning("Unexpected results for scenario " + scenario);
    }
    
    return result;
  }
  
  /**
   * Run the Coyle-Doyle election algorithm.
   * 
   * @param ballotBox
   *          The set of test data
   * @return The actual result
   */
  public ElectionResult runCoyleDoyle(ElectionConfiguration ballotBox) {
    
    ElectionResult result = null;
    Constituency constituency = ballotBox.getConstituency();
    ElectoralScenario scenario = ballotBox.getScenario();
    
    int numberOfCandidates = scenario.getNumberOfCandidates();
    String[] candidates = new String[numberOfCandidates];
    
    for (int i = 0; i < numberOfCandidates; i++) {
      candidates[i] = "" + constituency.getCandidate(i).getCandidateID();
    }
    
    int numberOfSeats = scenario.numberOfWinners();
    int electionType = GENERAL_ELECTION;
    
    int[] outcome;
    coyle_doyle.election.Election election =
        new coyle_doyle.election.Election(candidates, numberOfSeats,
            electionType);
    
    List<BallotPaper> ballotPapers =
        convertBallotsIntoCoyleDoyleFormat(ballotBox);
    logger.info("CoyleDoyle ballot papers: " + ballotPapers.toString());
    
    if (!ballotPapers.isEmpty()) {
    
      outcome = election.election(ballotPapers); 
      result = new ElectionResult(outcome, numberOfSeats);
      checkResult(scenario, result);
    }
    else {
      logger.severe("Failed to extract ballot data from " + ballotBox.toString()
          + " to " + ballotPapers.toString());
    }
    
    return result;
  }
  
  /**
   * @param scenario
   * @param result
   */
  protected void checkResult(ElectoralScenario scenario, ElectionResult result) {
    if (!scenario.matchesResult(result)) {
      logger.severe("Expected result: " + scenario.toString()
          + " but actual result " + result.toString());
    }
  }
  
  /**
   * Convert ballot box test data into a format readable by the
   * Coyle-Doyle election algorithm.
   * 
   * @param ballotBox
   *          The test data in Votail format.
   * @return The test data in Coyle-Doyle format.
   */
  protected List<BallotPaper> convertBallotsIntoCoyleDoyleFormat(
      ElectionConfiguration ballotBox) {
    
    List<BallotPaper> votes = new ArrayList<BallotPaper>();
    
    int voteNumber = 0;
    while (ballotBox.isNextBallot()) {
      Ballot ballot = ballotBox.getNextBallot();
      int numberOfPreferences = ballot.remainingPreferences();
      int[] preferences = new int[numberOfPreferences];
      for (int i = 0; i < numberOfPreferences; i++) {
        preferences[i] = ballot.getNextPreference(i);
      }
      BallotPaper bp = new BallotPaper(voteNumber, preferences);
      votes.add(bp);
      voteNumber++;
      logger.info(bp.toString());
    }
    
    return votes;
  }
  
  /**
   * Test the HexMedia algorithm for PR-STV
   * 
   * @param ballotBox
   *          Test data in Votail format
   * @return Actual results
   */
  public ElectionResult runHexMedia(ElectionConfiguration ballotBox) {
    
    String ballotBox_filename = convertBallotsToHexMediaFormat(ballotBox);
    
    int numberOfSeats =
        ballotBox.getConstituency().getNumberOfSeatsInThisElection();
    
    String[] args = new String[3];
    args[0] = "true"; // Droop Quota
    args[1] = ballotBox_filename;
    args[2] = Integer.toString(numberOfSeats);
    
    try {
      // TODO run headless or set virtual display
      com.hexmedia.prstv.Election.main(args);
      // TODO Initialise event
      // TODO Run All Counts event
      // TODO Quit event
    }
    catch (Exception e) {
      logger.severe(e.getMessage());
    }
    
    ElectionResult electionResult = getResult();
    
    ElectoralScenario scenario = ballotBox.getScenario();
    checkResult(scenario, electionResult);
    
    return electionResult;
    
  }
  
  /**
   * Use reflection to get HexMedia election result.
   * 
   * @param election
   *          The HexMedia API
   * @return The election result
   */
  @SuppressWarnings("unchecked")
  protected ElectionResult getResult() {
    
    ElectionResult result = new ElectionResult();
    
    try {
      Field displayField =
          com.hexmedia.prstv.Display.class.getDeclaredField("display");
      displayField.setAccessible(true);
      
      com.hexmedia.prstv.Display display = (Display) displayField.get(null);
      
      Field electionField =
          com.hexmedia.prstv.Display.class.getDeclaredField("election");
      electionField.setAccessible(true);
      
      com.hexmedia.prstv.Election election =
          (Election) electionField.get(display);
      
      Field elected = election.getClass().getDeclaredField("elected");
      elected.setAccessible(true);
      List<Candidate> electedCandidates =
          (List<Candidate>) elected.get(election);
      
      Field eliminated = election.getClass().getDeclaredField("eliminated");
      eliminated.setAccessible(true);
      List<Candidate> eliminatedCandidates =
          (List<Candidate>) eliminated.get(election);
      
      final int numberOfWinners = electedCandidates.size();
      int numberOfCandidates = numberOfWinners + eliminatedCandidates.size();
      
      int[] outcomes = new int[numberOfCandidates];
      int index = 0;
      for (Candidate candidate : electedCandidates) {
        outcomes[index] = Integer.valueOf(candidate.name());
        index++;
      }
      for (Candidate candidate : eliminatedCandidates) {
        outcomes[index] = Integer.valueOf(candidate.name());
        index++;
      }
      
      result.load(outcomes, numberOfWinners);
      
    }
    catch (SecurityException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (NoSuchFieldException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalArgumentException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalAccessException e) {
      logger.severe(e.getLocalizedMessage());
    }
    
    return result;
  }
  
  /**
   * Initialise a HexMedia election object
   * 
   * @param election
   */
  protected void initialise(com.hexmedia.prstv.Election election) {
    try {
      
      Class<?> parameters[] = {};
      Method initialiseElection =
          com.hexmedia.prstv.Election.class.getDeclaredMethod("initialise",
              parameters);
      logger.info("Method found " + initialiseElection.getName());
      initialiseElection.setAccessible(true);
      initialiseElection.invoke(election);
    }
    catch (SecurityException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalArgumentException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (NoSuchMethodException e) {
      logger.severe("no such method " + e.getLocalizedMessage());
    }
    catch (IllegalAccessException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (InvocationTargetException e) {
      logger.severe(e.getLocalizedMessage());
    }
  }
  
  /**
   * Construct the Hexmedia Election object through reflection
   * 
   * @param numberOfSeats
   *          The number of seats
   * @param election
   *          The election object to be constructed
   */
  protected void setNumberOfSeats(int numberOfSeats,
      com.hexmedia.prstv.Election election) {
    final Class<? extends Election> electionClass = election.getClass();
    
    try {
      Field nseats = electionClass.getDeclaredField("nseats");
      Field elected = electionClass.getDeclaredField("elected");
      Field eliminated = electionClass.getDeclaredField("eliminated");
      Field surpluses = electionClass.getDeclaredField("surpluses");
      
      nseats.setAccessible(true);
      nseats.setInt(election, numberOfSeats);
      
      elected.setAccessible(true);
      eliminated.setAccessible(true);
      surpluses.setAccessible(true);
      
      elected.set(election, new LinkedList<Candidate>());
      eliminated.set(election, new LinkedList<Candidate>());
      surpluses.set(election, new LinkedList<Surplus>());
    }
    catch (IllegalArgumentException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalAccessException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (SecurityException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (NoSuchFieldException e) {
      logger.severe(e.getLocalizedMessage());
    }
  }
  
  /**
   * @param ballotBox_filename
   * @param election
   */
  protected void setFilename(String ballotBox_filename,
      com.hexmedia.prstv.Election election) {
    try {
      Field filename;
      filename = election.getClass().getDeclaredField("file");
      filename.setAccessible(true);
      filename.set(election, ballotBox_filename);
    }
    catch (SecurityException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (NoSuchFieldException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalArgumentException e) {
      logger.severe(e.getLocalizedMessage());
    }
    catch (IllegalAccessException e) {
      logger.severe(e.getLocalizedMessage());
    }
  }
  
  /**
   * Convert test ballot box into hexmedia format.
   * 
   * @param ballotBox
   *          The test data representing a ballot box
   * @return The name of the file into which testdata was written
   */
  protected String convertBallotsToHexMediaFormat(
      ElectionConfiguration ballotBox) {
    
    String filename =
        TESTDATA_PREFIX + ballotBox.hashCode() + System.currentTimeMillis()
            + SUFFIX;
    
    FileWriter fileWriter;
    BufferedWriter writer;
    try {
      fileWriter = new FileWriter(filename);
      writer = new BufferedWriter(fileWriter);
      
      Constituency candidateList = ballotBox.getConstituency();
      int numberOfCandidates = candidateList.getNumberOfCandidates();
      
      writer.append("\"Mixed Vote No.\"");
      for (int c = 0; c < numberOfCandidates; c++) {
        election.tally.Candidate candidate = candidateList.getCandidate(c);
        writer.append(";\"" + candidate.getCandidateID() + "\"");
        
      }
      
      int index = 1;
      while (ballotBox.isNextBallot()) {
        Ballot ballot = ballotBox.getNextBallot();
        writer.append("\"" + index + "\"");
        
        for (int i = 0; i < numberOfCandidates; i++) {
          election.tally.Candidate candidate = candidateList.getCandidate(i);
          int candidateID = candidate.getCandidateID();
          
          if (!ballot.isApproved(candidateID)) {
            writer.append(";\"" + " " + "\"");
          }
          else {
            writer.append(";\"" + Integer.toString(ballot.getRank(candidateID))
                + "\"");
          }
        }
        index++;
      }
      writer.flush();
      writer.close();
    }
    catch (IOException e) {
      logger.severe("Unable to create CSV file because "
          + e.getLocalizedMessage());
      
    }
    
    return filename;
  }
  
  public static void main(String[] args) {
    UniversalTestRunner uilioch = new UniversalTestRunner();
    uilioch.testScenarios(10, 10);
  }
}
