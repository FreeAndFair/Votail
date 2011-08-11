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
   * @author Dermot Cochran
   *
   */
  protected class HexMediaElectionResult extends ElectionResult {
    
    /**
     * Use reflection to get HexMedia election result.
     * 
     * @param election
     *          The HexMedia API
     * @return The election result
     */
    @SuppressWarnings("unchecked")
    public HexMediaElectionResult() {
            
      try {
        final Field displayField =
            com.hexmedia.prstv.Display.class.getDeclaredField("display");
        displayField.setAccessible(true);
        
        final com.hexmedia.prstv.Display display = 
          (Display) displayField.get(null);
        
        final Field electionField =
            com.hexmedia.prstv.Display.class.getDeclaredField("election");
        electionField.setAccessible(true);
        
        final com.hexmedia.prstv.Election election =
            (Election) electionField.get(display);
        
        final Field elected = election.getClass().getDeclaredField("elected");
        elected.setAccessible(true);
        final List<Candidate> electedCandidates =
            (List<Candidate>) elected.get(election);
        
        final Field eliminated = election.getClass().getDeclaredField("eliminated");
        eliminated.setAccessible(true);
        final List<Candidate> eliminatedCandidates =
            (List<Candidate>) eliminated.get(election);
        
        final int numberOfWinners = electedCandidates.size();
        final int numberOfCandidates = numberOfWinners + eliminatedCandidates.size();
        
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
        
        load(outcomes, numberOfWinners);
        
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
    
  }

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

  /**
   * @author dero
   *
   */
  protected class CoyleDoyleElectionResult extends ElectionResult {
    
    /**
     * @param outcome
     * @param numberOfWinners
     */
    public CoyleDoyleElectionResult(int[] outcome, int numberOfWinners) {
      load(outcome, numberOfWinners);
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
   * Run the Coyle-Doyle election algorithm.
   * 
   * @param ballotBox
   *          The set of test data
   * @return The actual result
   */
  public ElectionResult runCoyleDoyle(final ElectionConfiguration ballotBox) {
    
    CoyleDoyleElectionResult result = null;
    final Constituency constituency = ballotBox.getConstituency();
    final ElectoralScenario scenario = ballotBox.getScenario();
    
    final int numberOfCandidates = scenario.getNumberOfCandidates();
    String[] candidates = new String[numberOfCandidates];
    
    for (int i = 0; i < numberOfCandidates; i++) {
      candidates[i] = Integer.toString(
          constituency.getCandidate(i).getCandidateID());
    }
    
    final int numberOfSeats = scenario.numberOfWinners();
    final int electionType = GENERAL_ELECTION;
    
    int[] outcome;
    final coyle_doyle.election.Election election =
        new coyle_doyle.election.Election(candidates, numberOfSeats,
            electionType);
    
    final List<BallotPaper> ballotPapers =
        convertBallotsIntoCoyleDoyleFormat(ballotBox);
    logger.info("CoyleDoyle ballot papers: " + ballotPapers.toString());
    
    if (!ballotPapers.isEmpty()) {
      outcome = election.election(ballotPapers); 
      if (outcome != null) {
        result = new CoyleDoyleElectionResult(outcome, numberOfSeats);
      }
    }
    
    checkResult(scenario, result);
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
  
  /**
   * Convert ballot box test data into a format readable by the
   * Coyle-Doyle election algorithm.
   * 
   * @param ballotBox
   *          The test data in Votail format.
   * @return The test data in Coyle-Doyle format.
   */
  protected List<BallotPaper> convertBallotsIntoCoyleDoyleFormat(
      final ElectionConfiguration ballotBox) {
    
    final List<BallotPaper> votes = new ArrayList<BallotPaper>();
    
    int voteNumber = 0;
    while (ballotBox.isNextBallot()) {
      final Ballot ballot = ballotBox.getNextBallot();
      final int numberOfPreferences = ballot.remainingPreferences();
      int[] preferences = new int[numberOfPreferences];
      for (int i = 0; i < numberOfPreferences; i++) {
        preferences[i] = ballot.getNextPreference(i);
      }
      final BallotPaper ballotPaper = new BallotPaper(voteNumber, preferences);
      votes.add(ballotPaper);
      voteNumber++;
      logger.info(ballotPaper.toString());
    }
    logger.info("Number of ballots: " + voteNumber);
    logger.info(votes.toString());
    
    return votes;
  }
  
  /**
   * Test the HexMedia algorithm for PR-STV
   * 
   * @param ballotBox
   *          Test data in Votail format
   * @return Actual results
   */
  public ElectionResult runHexMedia(final ElectionConfiguration ballotBox) {
    
    final String ballotBox_filename = convertBallotsToHexMediaFormat(ballotBox);
    
    final int numberOfSeats =
        ballotBox.getConstituency().getNumberOfSeatsInThisElection();
    
    String[] args = new String[3];
    args[0] = "true"; // Droop Quota
    args[1] = ballotBox_filename;
    args[2] = Integer.toString(numberOfSeats);
    
    try {
      com.hexmedia.prstv.Election.main(args);
    }
    catch (Exception e) {
      logger.severe(e.getMessage());
    }
    
    final ElectionResult electionResult = new HexMediaElectionResult();
    
    final ElectoralScenario scenario = ballotBox.getScenario();
    checkResult(scenario, electionResult);
    
    return electionResult;
    
  }
  
  /**
   * Initialise a HexMedia election object
   * 
   * @param election
   */
  protected void initialise(final com.hexmedia.prstv.Election election) {
    try {
      
      final Class<?> parameters[] = {};
      final Method initialiseElection =
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
  protected void setNumberOfSeats(final int numberOfSeats,
      final com.hexmedia.prstv.Election election) {
    final Class<? extends Election> electionClass = election.getClass();
    
    try {
      final Field nseats = electionClass.getDeclaredField("nseats");
      final Field elected = electionClass.getDeclaredField("elected");
      final Field eliminated = electionClass.getDeclaredField("eliminated");
      final Field surpluses = electionClass.getDeclaredField("surpluses");
      
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
  protected void setFilename(final String ballotBox_filename,
      final com.hexmedia.prstv.Election election) {
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
      final ElectionConfiguration ballotBox) {
    
    final String filename =
        TESTDATA_PREFIX + ballotBox.hashCode() + System.currentTimeMillis()
            + SUFFIX;
    
    FileWriter fileWriter;
    BufferedWriter writer;
    try {
      fileWriter = new FileWriter(filename);
      writer = new BufferedWriter(fileWriter);
      
      final Constituency candidateList = ballotBox.getConstituency();
      final int numberOfCandidates = candidateList.getNumberOfCandidates();
      
      writer.append("\"Mixed Vote No.\"");
      for (int c = 0; c < numberOfCandidates; c++) {
        final election.tally.Candidate candidate = candidateList.getCandidate(c);
        writer.append(";\"" + candidate.getCandidateID() + "\"");
        
      }
      
      int index = 1;
      while (ballotBox.isNextBallot()) {
        final Ballot ballot = ballotBox.getNextBallot();
        writer.append("\"" + index + "\"");
        
        for (int i = 0; i < numberOfCandidates; i++) {
          final election.tally.Candidate candidate = candidateList.getCandidate(i);
          final int candidateID = candidate.getCandidateID();
         
            writer.append(";\"" + getRank(ballot,candidateID) + "\"");
          
         
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
