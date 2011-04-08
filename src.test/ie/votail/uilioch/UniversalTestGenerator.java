// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.IOException;
import java.util.logging.Logger;

import junit.framework.TestCase;

import org.testng.annotations.Test;

public class UniversalTestGenerator extends TestCase {
    
  public static final String PSRTV_BALLOTBOX_FILENAME = 
    "testdata/ballotboxes.prstv";
  public static final String PRSTV_SCENARIO_LIST_FILENAME = 
    "testdata/scenarios.prstv";
  public static final String PLURALITY_SCENARIO_LIST_FILENAME = 
    "testdata/scenarios.plurality";
  public static final String PLURALITY_BALLOTBOX_FILENAME = 
    "testdata/ballotboxes.plurality";

  @Test
  public void makeDataForPRSTV(int numberOfSeats, int numberOfCandidates) {
    
    final int scope = numberOfCandidates;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    logger.info("Using scope = " + scope);

    for (int seats = 1; seats <= numberOfSeats; seats++) {
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
        
        ScenarioList scenarioList =
            scenarioFactory.find(candidates, seats, Method.STV);
        
        // Save and replay the scenario list for use in other tests
        try {
          scenarioList.writeToFile (PRSTV_SCENARIO_LIST_FILENAME);
        }
        catch (IOException e) {
          logger.severe("Unable to store scenario list, because " + e.getMessage());
        }
        
        for (ElectoralScenario scenario : scenarioList) {
          logger.info(scenario.toString());
          ElectionConfiguration electionConfiguration =
              createElection(scenario);
          
          electionConfiguration.writeToFile(PSRTV_BALLOTBOX_FILENAME);
          
        }
      }
    }
  }
  
  /**
   * Create an election configuration, including constituency and ballot box.
   * 
   * @param scenario
   *          The scenario for which to create this configuration
   * 
   * @return The election configuration
   */
  protected/*@ non_null @*/ElectionConfiguration createElection(
      ElectoralScenario scenario) {
    BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
    ElectionConfiguration electionConfiguration =
        ballotBoxFactory.extractBallots(scenario, scenario
            .getNumberOfCandidates());
    return electionConfiguration;
  }
  
  public static void main(String[] args) {
    UniversalTestGenerator universalTest = new UniversalTestGenerator();
    universalTest.makeDataForPRSTV(5, 11);
    universalTest.makeDataForPlurality(1, 7);
  }
  
  @Test
  //@ requires 0 < numberOfSeats && numberOfSeats < numberOfCandidates;
  public void makeDataForPlurality(int numberOfSeats, int numberOfCandidates) {
    
    final int seats = numberOfSeats;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    
    for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
      
      final int scope = candidates;
      logger.info("Using scope = " + scope);
      
      ScenarioList scenarioList =
          scenarioFactory.find(candidates, seats, Method.Plurality);
      
      // Save and replay the scenario list for use in other tests
      try {
        scenarioList.writeToFile (PLURALITY_SCENARIO_LIST_FILENAME);
      }
      catch (IOException e) {
        logger.severe("Unable to store scenario list, because " + e.getMessage());
      }
      
      for (ElectoralScenario scenario : scenarioList) {
        logger.info(scenario.toString());
        ElectionConfiguration electionConfiguration = createElection(scenario);
        
        electionConfiguration.writeToFile(PLURALITY_BALLOTBOX_FILENAME);

      }
    }
  }
}
