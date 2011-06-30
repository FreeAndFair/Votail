// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.io.File;
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
  private AlloyPool alloyPool;
  private Channel taskQueue;
  
  public UniversalTestGenerator(int capacity) {
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
    taskQueue = new TaskQueue(capacity);
    alloyPool = new AlloyPool(taskQueue, capacity);
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
      final int numberOfCandidates, final Method method, int scope) {
    
    final String dataFilename = getFilename(method, DATA_FILENAME_SUFFIX);
    final String existingDataFilename =
        dataFilename + System.currentTimeMillis();
    
    // If file already exists then rename it to old file
    checkAndRename(dataFilename, existingDataFilename);
    
    try {
      FileOutputStream fos = new FileOutputStream(dataFilename, true);
      ObjectOutputStream out = new ObjectOutputStream(fos);
      FileInputStream fis = new FileInputStream(existingDataFilename);
      ObjectInputStream in = new ObjectInputStream(fis);
      
      for (int seats = 1; seats <= numberOfSeats; seats++) {
        for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
          
          createBallotBoxes(seats, candidates, method, in, out, scope);
        }
      }
      out.close();
      fos.close();
    }
    catch (FileNotFoundException e) {
      logger.severe(e.getMessage());
    }
    catch (IOException e) {
      logger.severe(e.getMessage());
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
  protected void checkAndRename(/*@ non_null*/String oldName,
  /*@ non_null*/String newName) {
    
    File file = new File(oldName);
    if (file.exists()) {
      File newFile = new File(newName);
      file.renameTo(newFile);
    }
    
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
      final Method method, ObjectInputStream in, ObjectOutputStream out,
      final int scope) {
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      // Check if this scenario already generated
      if (notAlreadyExists(scenario, in)) {
        
        alloyTask(candidates, out, scope, scenario);
        count++;
      }
    }
    
    logger.info("Generated " + count + " scenarios for " + method.toString()
        + " with " + candidates + " candidates for " + seats + " seats.");
  }
  
  /**
   * Create a work package and add to the queue of tasks
   * 
   * @param candidates The number of candidates to consider
   * @param out The output stream for test data
   * @param scope The maximum scope for bounded model finding
   * @param scenario The scenario for which we require test data
   */
  protected void alloyTask(final int candidates, ObjectOutputStream out,
      final int scope, final ElectoralScenario scenario) {
    
    // Add scenario to the list of tasks
    AlloyTask task = new AlloyTask(out);
    WorkQueue wq = task.getWorkQueue();
    WorkPackage wp = new WorkPackage (scenario, candidates, scope);
    try {
      wq.put(wp);
      taskQueue.put(task);
    }
    catch (InterruptedException e1) {
      logger.severe(e1.getMessage());
    }
  }
  
  /**
   * Check if data for this scenario already exists
   * 
   * @param scenario
   *          The scenario to check
   * @param in
   *          The file input stream containg existing test data
   * @return <code>false></code> if scenario is found in the data
   */
  protected boolean notAlreadyExists(ElectoralScenario scenario,
      ObjectInputStream in) {
    
    try {
      in.reset();
    }
    catch (IOException e) {
      logger.severe("Unable to reset input stream: " + e.getMessage());
    }
    ElectionData testData = getTestData(in);
    while (testData != null) {
      if (testData.getScenario().equivalentTo(scenario)) {
        return false;
      }
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
    UniversalTestGenerator uilioch = new UniversalTestGenerator(10);
    
    uilioch.generateTests(1, 5, Method.STV, 15); // IRV 1-seat
    uilioch.generateTests(3, 7, Method.STV, 20); // PR-STV 3-seat
    uilioch.generateTests(4, 9, Method.STV, 20); // PR-STV 4-seat
    uilioch.generateTests(5, 11, Method.STV, 20); // PR-STV 5-seat
    uilioch.generateTests(1, 5, Method.Plurality, 15); // First-past-the-post
  }
}
