// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import flexjson.JSONDeserializer;
import flexjson.JSONSerializer;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.OutcomeList;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.File;
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
  protected final JSONDeserializer<ElectionData> jsonDeserializer;
  
  public UniversalTestGenerator() {
    ballotBoxFactory = new BallotBoxFactory();
    scenarioFactory = new ScenarioFactory();
    logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    serializer = new JSONSerializer();
    jsonDeserializer = new JSONDeserializer<ElectionData>();
  }
  
  /**
   * Generate ballot box data for an election for the required number of seats,
   * candidates and voting scheme.
   * 
   * @param numberOfSeats The number of seats to be filled
   * @param numberOfCandidates The number of candidates for election
   * @param method The voting scheme
   */
  public void generateTests(final int numberOfSeats,
      final int numberOfCandidates, final Method method) {
    
    for (int seats = 1; seats <= numberOfSeats; seats++) {
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; 
        candidates++) {
        
        createBallotBoxes(seats, candidates, method);
      }
    }
    logger.info("Finished.");
  }
  
  /**
   * @param seats
   *          The number of seats to be filled
   * @param candidates
   *          The number of candidates
   * @param method
   *          The voting scheme and method of election
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
        
        ElectionData electionData =
            ballotBoxFactory.extractBallots(scenario, candidates).export();
        
        logger.info(electionData.getScenario().toPredicate());
        
        try {
          
          FileWriter writer = new FileWriter(filename, true);
          
          serializer.include("ballotBox.ballots.preferenceList", 
            "scenario.listOfOutcomes.outcomes").
            exclude("byeElection","constituency").
            serialize(electionData, writer);
          
          writer.flush();
          writer.close();
        }
        catch (Exception e) {
          logger.severe("Failed to save generated test data because "
            + e.getCause());
          break;
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
   * @param scenario The scenario that we are looking for
   * 
   * @return <code>True></code> if a ballot box exists for this scenario
   */
  protected boolean notAlreadyGenerated(ElectoralScenario scenario,
      String filename) {
    
    try {
      File file = new File(filename);
      if (file.exists()) {
        
        FileReader reader = new FileReader(filename);
        
        while (reader.ready()) {
          
          ElectionData electionData = getTestData(reader);
          
          if (scenario.equivalentTo(electionData.getScenario())) {
            reader.close();
            return false;
          }
          
        }
        reader.close();
      }
      else {
        logger.fine("No pre-existing data found.");
        return true;
      }
      
    }
    catch (IOException e) {
      logger.info("Failed to reopen existing test data from " + filename
          + " : " + e.getMessage());
    }
    
    return true;
  }

  /**
   * Deserialization of Test Data
   * 
   * @param reader The File Reader which contains the test data
   * @return The Test Data
   */
  public ElectionData getTestData(FileReader reader) {
    
    /* Note that generics need explicit type information, which otherwise is
     * lost during serialization and deserialization by FlexJSON, due to the
     * way that generic information is handled by Java compilers.
     */
    
    ElectionData electionData =
        jsonDeserializer.use(null, ElectionData.class).
        use("scenario", ElectoralScenario.class).
        use("outcomes",Outcome.class).
        use("method", Method.class).
        use("STV", Method.class).
        use("OutcomeList", OutcomeList.class).
        use("outcome", Outcome.class).
        use("ElectoralScenario", ElectoralScenario.class).
        deserialize(reader);
    return electionData;
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
   */
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator();
    
    uilioch.generateTests(5, 11, Method.STV);
    uilioch.generateTests(1, 7, Method.Plurality);
  }
}
