package external;

import java.util.List;
import java.util.logging.Logger;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioList;
import election.tally.BallotBox;
import election.tally.BallotCounting;

public class TestExternalAPIs {
  
  public static final int INITIAL_SCOPE = 6;
  public static final String LOG_NAME = "Cross Testing and Validation";
  
  void testScenarios() {
    Logger logger = Logger.getLogger(LOG_NAME);
    
    // replay PR-STV scenario list from stored file
    ScenarioList scenarioList =
        new ScenarioList(
            ie.votail.model.factory.test.VotailSystemTest.SCENARIO_LIST_FILENAME);
    
    for (ElectoralScenario scenario : scenarioList) {
      ElectionConfiguration ballotBox = extractBallotBox(scenario);
      
      ElectionResult result1 = testHexMedia(ballotBox, scenario);
      ElectionResult result2 = testCoyleDoyle(ballotBox, scenario);
      ElectionResult result3 = testMacCarthyBallotBox(ballotBox, scenario);
      ElectionResult result4 = testVotail(ballotBox, scenario);
      
      TestReport report41 = result4.compare(result1, scenario);
      TestReport report42 = result4.compare(result2, scenario);
      TestReport report43 = result4.compare(result3, scenario);
      
      logger.info(scenario + ":" + report41 + report42 + report43);
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
  
  private ElectionResult testMacCarthyBallotBox(BallotBox ballotBox,
      ElectoralScenario scenario) {
    return null;
    // TODO Auto-generated method stub
    
  }
  
  private ElectionResult testCoyleDoyle(BallotBox ballotBox,
      ElectoralScenario scenario) {
    
    ElectionResult result = new ElectionResult(); 
    String[] candidates = null;
    int numberOfSeats= scenario.numberOfWinners();
    int electionType = 0; // General election
    election.Election election = new election.Election(candidates, 
        numberOfSeats, electionType);
    
    List ballotPapers = convertBallotsIntoCoyleDoyleFormat(ballotBox);
    election.election(ballotPapers);
    
    
    return result;
  }
  
  private List convertBallotsIntoCoyleDoyleFormat(BallotBox ballotBox) {
    // TODO Auto-generated method stub
    return null;
  }

  private ElectionResult testHexMedia(BallotBox ballotBox,
      ElectoralScenario scenario) {
    return null;
    // TODO Auto-generated method stub
    
  }
  
}
