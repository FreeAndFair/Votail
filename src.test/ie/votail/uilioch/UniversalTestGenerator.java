// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.logging.FileHandler;
import java.util.logging.Logger;

public class UniversalTestGenerator extends Uilioch {
  
  protected BallotBoxFactory ballotBoxFactory;
  protected ScenarioFactory scenarioFactory;
  protected AlloyPool taskPool;
  protected String dataFilename;
  protected String existingDataFilename;
  protected boolean existingDataFlag;
  
  /**
   * Prepare for test generation
   * 
   * @param workers
   *          The number of tasks than run in parallel
   * @param width
   *          The expected maximum queue length per task
   */
  /*@ requires 0 < workers;
    @ requires 0 < width; */
  public UniversalTestGenerator(int workers, int capacity) {
    ballotBoxFactory = new BallotBoxFactory();
    scenarioFactory = new ScenarioFactory();
    logger = Logger.getLogger(this.getClass().getName());
    
    try {
      final String logFilename =
          UniversalTestGenerator.LOGFILENAME + "." + System.currentTimeMillis();
      FileHandler handler = new FileHandler(logFilename);
      logger.addHandler(handler);
    }
    catch (SecurityException e1) {
      logger.info("not allowed to attach logfile " + e1.getMessage());
    }
    catch (IOException e1) {
      logger.info("not able to find logfile " + e1.getMessage());
    }
    
    taskPool = new AlloyPool(workers, capacity);
    
    dataFilename = getFilename();
    existingDataFilename = dataFilename + System.currentTimeMillis();
    existingDataFlag = checkAndRename(dataFilename, existingDataFilename);
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
   * @param scope
   *          Maximum scope for Alloy solution
   */
  public void generateTests(final int numberOfSeats,
      final int numberOfCandidates, final Method method) {
    
    
    try {
      FileOutputStream fos = new FileOutputStream(dataFilename, true);
      ObjectOutputStream out = new ObjectOutputStream(fos);
      
      for (int seats = 1; seats <= numberOfSeats; seats++) {
        for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
          
          createBallotBoxes(seats, candidates, method, out);
        }
      }
      out.close();
      fos.close();
    }
    catch (FileNotFoundException e) {
      logger.severe(e.toString());
    }
    catch (IOException e) {
      logger.severe(e.toString());
    }
    finally {
    }
    logger.info("Finished.");
  }
  
  /**
   * Check if file already exists and rename it if it does.
   * 
   * @param oldName
   *          The filename to check
   * @param newName
   *          The new filename
   */
  protected boolean checkAndRename(/*@ non_null*/String oldName,
  /*@ non_null*/String newName) {
    
    File file = new File(oldName);
    if (file.exists()) {
      File newFile = new File(newName);
      file.renameTo(newFile);
      newFile.setReadOnly();
      return true;
    }
    return false;
  }
  
  /**
   * Simulate test data or universal testing of an election
   * 
   * @param seats
   *          The number of seats to be filled
   * @param candidates
   *          The number of candidates
   * @param method
   *          The voting scheme and method of election
   * @param in
   * @param out
   *          Output file stream for generated data
   * @param scope
   *          Maximum scope for Alloy solution
   */
  protected void createBallotBoxes(final int seats, final int candidates,
      final Method method, ObjectOutputStream out) {
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      // Check if this scenario already generated
      if (!alreadyExists(scenario, out)) {
          taskPool.execute(new AlloyTask(out, scenario));
          count++;
      }
    }
    
    logger.info("Generated " + count + " scenarios for " + method.toString()
        + " with " + candidates + " candidates for " + seats + " seats.");
  }
  
  /**
   * Check if data for this scenario already exists
   * 
   * @param scenario
   *          The scenario to check
   * @param out
   * @param in
   *          The file input stream containing existing test data
   * @return <code>false></code> if scenario is found in the data
   */
  protected boolean alreadyExists(ElectoralScenario scenario,
      ObjectOutputStream out) {
    
    if (!existingDataFlag) {
      return false;
    }
    
    // Open a new reader
    try {
      FileInputStream fis = new FileInputStream(existingDataFilename);
      ObjectInputStream in = new ObjectInputStream(fis);
      
      ElectionData testData = getTestData(in);
      try {
        while (testData != null) {
          if (testData.getScenario().equivalentTo(scenario)) {
            logger.info("Found an existing ballot box for this scenario");
            writeBallots(out, testData, scenario);
            return true;
            
          }
          testData = getTestData(in);
        }
      }
      catch (EOFException eofe) {
        
        logger.info("No existing ballot box for this scenario");
      }
      in.close();
      fis.close();
    }
    
    catch (IOException ioe) {
      logger.severe(ioe.getMessage());
    }
    
    logger.info("Generating new ballot box for this scenario");
    return false;
  }
  
  /**
   * Rewrite existing test data to the new data file
   * 
   * @param out The new output stream
   * @param testData The existing test data
   * @param scenario  The expected results from this test data
   * @throws IOException
   */
  protected synchronized void writeBallots(ObjectOutputStream out,
      ElectionData testData, ElectoralScenario scenario) throws IOException {
    AlloyTask alloyTask = new AlloyTask(out,scenario);
    alloyTask.writeBallots(testData);
  }
  
  /**
   * Generate enough test data for 100% path coverage
   */
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator(80,100);
    
    uilioch.generateTests(1, 5, Method.STV); // IRV 1-seat
    uilioch.generateTests(3, 7, Method.STV); // PR-STV 3-seat
    uilioch.generateTests(4, 9, Method.STV); // PR-STV 4-seat
    uilioch.generateTests(5, 11, Method.STV); // PR-STV 5-seat
    uilioch.generateTests(1, 11, Method.Plurality); // First-past-the-post
  }
}
