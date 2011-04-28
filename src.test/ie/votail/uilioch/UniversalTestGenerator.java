// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import flexjson.JSONSerializer;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.logging.Logger;

public class UniversalTestGenerator {
  
  protected static final String FILENAME_PREFIX = "testdata/";
  protected static final String FILENAME_SUFFIX = "_election.data";
  
  protected BallotBoxFactory ballotBoxFactory;
  protected ScenarioFactory scenarioFactory;
  protected Logger logger;
  protected JSONSerializer serializer;
  
  public UniversalTestGenerator() {
    ballotBoxFactory = new BallotBoxFactory();
    scenarioFactory = new ScenarioFactory();
    logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    serializer = new JSONSerializer();
  }
  
  /**
   * @param numberOfSeats
   * @param numberOfCandidates
   * @param method
   */
  public void generateTests(final int numberOfSeats,
      final int numberOfCandidates, final Method method) {
    
    try {
      FileWriter writer = new FileWriter(getFilename(method));
      
      for (int seats = 1; seats <= numberOfSeats; seats++) {
        for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
          
          createBallotBoxes(seats, candidates, method, writer);
        }
      }
      
      writer.close();
    }
    catch (FileNotFoundException e) {
      logger.severe("Generation failed because " + e.getMessage());
    }
    catch (IOException e) {
      logger.severe("Generation failed because " + e.getMessage());
    }
    finally {
      logger.info("Finished!");
    }
  }
  
  /**
   * @param seats
   * @param candidates
   * @param method
   * @param writer
   */
  protected void createBallotBoxes(int seats, int candidates,
      final Method method, FileWriter writer) {
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      ElectionConfiguration electionData =
          ballotBoxFactory.extractBallots(scenario, candidates);
      
      try {
        serializer.include("ballots.preferences","candidateIDs").serialize(electionData, writer);
      }
      catch (Exception e) {
        logger.severe("Failed to save generated test data because "
            + e.getCause());
      }
      count++;
    }
    
    logger.info("Generated " + count + " scenarios for " + method.toString()
        + " with " + candidates + " for " + seats + "seats.");
  }
  
  /**
   * @param method
   * @return
   */
  protected static String getFilename(final Method method) {
    return FILENAME_PREFIX + method.toString() + FILENAME_SUFFIX;
  }
  
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator();
    uilioch.generateTests(5, 11, Method.STV);
    uilioch.generateTests(1, 7, Method.Plurality);
  }
}
