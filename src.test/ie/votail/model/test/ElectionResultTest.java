package ie.votail.model.test;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectionResult;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioList;
import ie.votail.model.factory.test.UniversalTest;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

import junit.framework.TestCase;
import coyle_doyle.election.BallotPaper;
import election.tally.Ballot;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class ElectionResultTest extends TestCase {
  
  public static final int INITIAL_SCOPE = 6;
  public static final String LOG_NAME = "Cross Testing and Validation";
  public static final String SUFFIX = ".txt";
  public static final String TESTDATA_PREFIX = "testdata/BallotBox";
  public static final int GENERAL_ELECTION = 0;
  private Logger logger;
  
  public void testScenarios() {
    logger = Logger.getLogger(LOG_NAME);
    
    // replay PR-STV scenario list from stored file
    ScenarioList scenarioList;
    final String filename = UniversalTest.PRSTV_SCENARIO_LIST_FILENAME;
    try {
      
      scenarioList = new ScenarioList(filename);
      
      for (ElectoralScenario scenario : scenarioList) {
        // TODO read Ballot Box test data from pre-generated file of Ballot Boxes
        ElectionConfiguration ballotBox = extractBallotBox(scenario);
        
        ElectionResult votailResult = runVotail(ballotBox, scenario);
        ElectionResult hexMediaResult = runHexMedia(ballotBox, scenario);
        ElectionResult coyleDoyleResult = runCoyleDoyle(ballotBox, scenario);
        
        assert hexMediaResult.equals(coyleDoyleResult);
        assert coyleDoyleResult.equals(votailResult);
        assert votailResult.equals(hexMediaResult);
      }
      
    }
    catch (IOException e) {
      logger.severe("Failed to read scenarios from file " + filename
          + " because " + e.getMessage());
    }
    catch (ClassNotFoundException e) {
      logger.severe("Failed to load scenarios from file " + filename
          + " because " + e.getMessage());
    }
  }
  
  /**
   * Run Votail with test data and match results with expected scenario
   * 
   * @param ballotBox
   *          The test data
   * @param scenario
   *          The expected result
   * @return The actual result
   */
  protected ElectionResult runVotail(ElectionConfiguration ballotBox,
      ElectoralScenario scenario) {
    BallotCounting votail = new BallotCounting();
    ElectionResult result = votail.run(ballotBox);
    
    if (!scenario.check(votail)) {
      logger.severe("Unexpected results for scenario " + scenario
          + " using predicate " + scenario.toPredicate() + " and ballot box "
          + ballotBox);
    }
    
    return result;
  }
  
  public ElectionConfiguration extractBallotBox(ElectoralScenario scenario) {
    BallotBoxFactory factory = new BallotBoxFactory();
    return factory.extractBallots(scenario, INITIAL_SCOPE);
  }
  
  /**
   * Run the Coyle-Doyle election algorithm.
   * 
   * @param ballotBox The set of test data
   * @param scenario The expected result
   * @return The actual result
   */
  public ElectionResult runCoyleDoyle(ElectionConfiguration ballotBox,
      ElectoralScenario scenario) {
    
    ElectionResult result;
    Constituency constituency = ballotBox.getConstituency();
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
      logger.info(ballotPapers.toString());
      
      outcome = election.election(ballotPapers);
      
      result = new ElectionResult(outcome, numberOfSeats);
    
    // TODO check actual results against expected scenario
    
    return result;
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
   * @param scenario
   *          Expected results
   * @return Actual results
   */
  public ElectionResult runHexMedia(ElectionConfiguration ballotBox,
      ElectoralScenario scenario) {
    
    String ballotBox_filename = convertBallotsToHexMediaFormat(ballotBox);
    
    int numberOfSeats =
        ballotBox.getConstituency().getNumberOfSeatsInThisElection();
    com.hexmedia.prstv.Election election =
        new com.hexmedia.prstv.Election(numberOfSeats, ballotBox_filename);
    
    com.hexmedia.prstv.Display.create();
    com.hexmedia.prstv.Display.setElection(election);
    election.initialize();
    election.runCount();
    
    String results_filename = "results.html";
    ElectionResult electionResult = new ElectionResult(results_filename);
    
    return electionResult;
  }
  
  /**
   * Convert test ballot box into hexmedia format.
   * 
   * @param ballotBox
   * @return
   */
  protected String convertBallotsToHexMediaFormat(
      ElectionConfiguration ballotBox) {
    
    String filename = TESTDATA_PREFIX + ballotBox.hashCode() + SUFFIX;
    
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
}
