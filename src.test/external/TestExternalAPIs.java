package external;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

import com.hexmedia.prstv.BallotList;
import com.hexmedia.prstv.Candidate;
import com.hexmedia.prstv.CandidatePreference;

import junit.framework.TestCase;

import coyle_doyle.election.BallotPaper;
import election.tally.Ballot;
import election.tally.BallotBox;
import election.tally.BallotCounting;

public class TestExternalAPIs extends TestCase {
  
  public static final int INITIAL_SCOPE = 6;
  public static final String LOG_NAME = "Cross Testing and Validation";
  
  public void testScenarios() {
    Logger logger = Logger.getLogger(LOG_NAME);
    
    // replay PR-STV scenario list from stored file
    ScenarioList scenarioList;
    try {
      scenarioList =
          new ScenarioList(
              ie.votail.model.factory.test.VotailSystemTest.SCENARIO_LIST_FILENAME
                  + ie.votail.model.factory.test.VotailSystemTest.PR_STV);
      
      for (ElectoralScenario scenario : scenarioList) {
        ElectionConfiguration ballotBox = extractBallotBox(scenario);
        
        ElectionResult result1 = testHexMedia(ballotBox, scenario);
        ElectionResult result2 = testCoyleDoyle(ballotBox, scenario);
        ElectionResult result4 = testVotail(ballotBox, scenario);
        
        TestReport report4_1 = result4.compare(result1, scenario);
        TestReport report4_2 = result4.compare(result2, scenario);
        TestReport report1_2 = result1.compare(result2, scenario);
        
        logger.info(scenario + ":" + report4_1 + report4_2 + report1_2);
      }
      
    }
    catch (IOException e) {
      logger.severe("Failed to read scenarios from file because "
          + e.getMessage());
    }
    catch (ClassNotFoundException e) {
      logger.severe("Failed to load scenarios from file because"
          + e.getMessage());
    }
  }
  
  protected ElectionResult testVotail(ElectionConfiguration ballotBox,
      ElectoralScenario scenario) {
    BallotCounting bc = new BallotCounting();
    bc.setup(ballotBox.getConstituency());
    bc.load(ballotBox);
    bc.count();
    
    ElectionResult result = new ElectionResult();
    result.setTitle("Votail");
    result.setQuota(bc.getQuota());
    return result;
  }
  
  public ElectionConfiguration extractBallotBox(ElectoralScenario scenario) {
    BallotBoxFactory factory = new BallotBoxFactory();
    return factory.extractBallots(scenario, INITIAL_SCOPE);
  }
  
  public ElectionResult testCoyleDoyle(ElectionConfiguration ballotBox,
      ElectoralScenario scenario) {
    
    ElectionResult result = new ElectionResult();
    String[] candidates = null;
    int numberOfSeats = scenario.numberOfWinners();
    int electionType = 0; // General election
    coyle_doyle.election.Election election =
        new coyle_doyle.election.Election(candidates, numberOfSeats,
            electionType);
    
    List<BallotPaper> ballotPapers =
        convertBallotsIntoCoyleDoyleFormat(ballotBox);
    int[] outcome = election.election(ballotPapers);
    result.addOutcome(outcome);
    
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
  public List<BallotPaper> convertBallotsIntoCoyleDoyleFormat(
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
  public ElectionResult testHexMedia(BallotBox ballotBox,
      ElectoralScenario scenario) {
    ElectionResult electionResult = new ElectionResult();
    
    // TODO convert ballot data and run election
    com.hexmedia.prstv.BallotList ballotList =
        convertBallotsToHexMediaFormat(ballotBox);
    
    // TODO count ballots
    
    // TODO store results
    
    return electionResult;
  }
  
  /**
   * Convert Votail ballot box into hexmedia format.
   * 
   * @param ballotBox
   * @return
   */
  public BallotList convertBallotsToHexMediaFormat(BallotBox ballotBox) {
    BallotList ballotList = new BallotList();
    
    int voteNumber = 0;
    while (ballotBox.isNextBallot()) {
      Ballot ballot = ballotBox.getNextBallot();
      int numberOfPreferences = ballot.remainingPreferences();
      List<CandidatePreference> candidateList = new ArrayList<CandidatePreference>();
      for (int i = 0; i < numberOfPreferences; i++) {
        Candidate candidate = null; // TODO
        CandidatePreference preference = new CandidatePreference(candidate, i);
        candidateList.add(preference);
      }
      com.hexmedia.prstv.Ballot hexMediaBallot =
          new com.hexmedia.prstv.Ballot(voteNumber, candidateList, false,
              numberOfPreferences, false);
      ballotList.add(hexMediaBallot);
      voteNumber++;
    }
    return ballotList;
  }
}
