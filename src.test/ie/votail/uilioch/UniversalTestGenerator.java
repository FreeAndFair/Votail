// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.logging.FileHandler;
import java.util.logging.Logger;

public class UniversalTestGenerator {
  
  protected static final String FILENAME_PREFIX = "testdata/";
  protected static final String DATA_FILENAME_SUFFIX = "_election.data";
  protected static final String LOGFILENAME = "logs/uilioch/generator.log";
  
  protected BallotBoxFactory ballotBoxFactory;
  protected ScenarioFactory scenarioFactory;
  protected Logger logger;
  
  public UniversalTestGenerator() {
    ballotBoxFactory = new BallotBoxFactory();
    scenarioFactory = new ScenarioFactory();
    logger = Logger.getLogger(this.getClass().getName());
    try {
      FileHandler handler = new FileHandler(UniversalTestGenerator.LOGFILENAME);
      logger.addHandler(handler);
    }
    catch (SecurityException e1) {
      logger.info("not allowed to attach logfile" + e1.getMessage());
    }
    catch (IOException e1) {
      logger.info("not able to find logfile" + e1.getMessage());
    }
  }
  
  /**
   * Generate ballot box data for an election for the required number of seats,
   * candidates and voting scheme.
   * 
   * @param numberOfSeats
   *          The number of seats to be filled
   * @param numberOfCandidates
   *          The number of candidates for election
   * @param method
   *          The voting scheme
   */
  public void generateTests(final int numberOfSeats,
      final int numberOfCandidates, final Method method) {
    
    for (int seats = 1; seats <= numberOfSeats; seats++) {
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
        
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
    
    final String dataFilename = getFilename(method, DATA_FILENAME_SUFFIX);
    
    FileInputStream fis = null;
    ObjectInputStream in = null;
    try {
      fis = new FileInputStream(dataFilename);
      in = new ObjectInputStream(fis);
    }
    catch (FileNotFoundException e) {
      logger.info("No existing data because " + e.getMessage());
    }
    catch (IOException e) {
      logger.severe("Cannot read existing data because " + e.getMessage());
    }
    finally {
    }
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      if (in == null || notAlreadyGenerated(scenario, in)) {
        
        ElectionData electionData =
            ballotBoxFactory.extractBallots(scenario, candidates).export();
        
        logger.info(electionData.getScenario().toPredicate());
        
        try {
          FileOutputStream fos = new FileOutputStream(dataFilename, true);
          ObjectOutputStream out = new ObjectOutputStream(fos);
          out.writeObject(electionData);
          out.close();
          fos.close();
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
   * @param scenario
   *          The scenario that we are looking for
   * 
   * @return <code>True></code> if a ballot box exists for this scenario
   */
  protected boolean notAlreadyGenerated(ElectoralScenario scenario,
      ObjectInputStream in) {
    
    try {
      while (0 < in.available()) {
        
        ElectionData electionData = getTestData(in);
        
        if (electionData == null
            || scenario.equivalentTo(electionData.getScenario())) {
          in.close();
          return false;
        }
      }
      in.close();
    }
    catch (IOException e) {
      logger.severe(e.getMessage());
    }
    
    return true;
  }
  
  /**
   * Deserialization of Test Data
   * 
   * @param in
   *          The Object Input Stream which contains the test data
   * @return The Test Data (or null)
   */
  public ElectionData getTestData(ObjectInputStream in) {
    
    ElectionData electionData = null;
    
    try {
      electionData = (ElectionData) in.readObject();
    }
    catch (IOException e1) {
      logger.severe("Cannot read data because " + e1.getMessage());
    }
    catch (ClassNotFoundException e1) {
      logger.severe("Cannot load data because " + e1.getMessage());
    }
    return electionData;
  }
  
  /**
   * Get name of the file which contains testdata for this method.
   * 
   * @param method
   *          The type of voting scheme
   * @return The filename
   */
  public/*@ pure @*/String getFilename(final Method method, final String suffix) {
    return FILENAME_PREFIX + method.toString() + suffix;
  }
  
  /**
   * Generate enough test data for 100% path coverage 
   */
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator();
    
    uilioch.generateTests(1, 5, Method.STV);        // IRV 1-seat
    uilioch.generateTests(3, 7, Method.STV);        // PR-STV 3-seat
    uilioch.generateTests(4, 9, Method.STV);        // PR-STV 4-seat
    uilioch.generateTests(5, 11, Method.STV);       // PR-STV 5-seat
    uilioch.generateTests(1, 5, Method.Plurality);  // First-past-the-post
  }
}
