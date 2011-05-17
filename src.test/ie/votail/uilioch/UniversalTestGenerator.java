// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import flexjson.JSONDeserializer;
import flexjson.JSONSerializer;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.logging.Logger;

public class UniversalTestGenerator {
  
  protected static final String FILENAME_PREFIX = "testdata/";
  protected static final String FILENAME_SUFFIX = "_election.json";
  
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
      final int numberOfCandidates, final Method method,
      final boolean appendToFile) {
    
    for (int seats = 1; seats <= numberOfSeats; seats++) {
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
        
        createBallotBoxes(seats, candidates, method);
      }
    }
    logger.info("Finished.");
  }
  
  /**
   * @param seats
   * @param candidates
   * @param method
   * @param writer
   */
  protected void createBallotBoxes(int seats, int candidates,
      final Method method) {
    
    final String filename = getFilename(method);
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      if (notAlreadyGenerated(scenario, filename)) {
        
        ElectionConfiguration electionData =
            ballotBoxFactory.extractBallots(scenario, candidates);
        
        logger.info(electionData.getScenario().toPredicate());
        
        try {
          
          FileWriter writer = new FileWriter(filename, true);
          
          serializer.include("ballots.preferenceList", "candidateIDs")
              .serialize(electionData, writer);
          
          writer.close();
        }
        catch (Exception e) {
          logger.severe("Failed to save generated test data because "
              + e.getCause());
        }
        count++;
      }
    }
    
    logger.info("Generated " + count + " scenarios for " + method.toString()
        + " with " + candidates + " candidates for " + seats + " seats.");
  }
  
  /**
   * Ensure that a ballot box has not already been generated for this scenario
   * 
   * @param scenario
   * @return
   */
  protected boolean notAlreadyGenerated(ElectoralScenario scenario,
      String filename) {
    
    try {
      FileReader reader = new FileReader(filename);
      
      while (reader.ready()) {
        
        ElectionConfiguration electionConfiguration =
            new JSONDeserializer<ElectionConfiguration>().deserialize(reader);
        
        if (scenario.equivalentTo(electionConfiguration.getScenario())) {
          reader.close();
          return false;
        }
      }
      reader.close();
    }
    catch (IOException e) {
      logger.severe("Failed to read scenarios from file " + filename
          + " because " + e.getMessage());
    }
    
    return true;
  }
  
  /**
   * Get name of the file which contains testdata for this method.
   * 
   * @param method
   *          The type of voting scheme
   * @return The filename
   */
  protected/*@ pure @*/static String getFilename(final Method method) {
    return FILENAME_PREFIX + method.toString() + FILENAME_SUFFIX;
  }
  
  /**
   * Generate enough test data for 100% coverage
   * 
   * @param args
   *          Command line arguments (not used)
   */
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator();
    // TODO Command Line Interface
    
    uilioch.generateTests(5, 11, Method.STV, true);
    uilioch.generateTests(1, 7, Method.Plurality, true);
  }
}
