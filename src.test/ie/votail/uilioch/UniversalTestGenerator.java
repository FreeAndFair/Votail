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
  protected Channel<AlloyTask> taskQueue;
  protected AlloyPool taskPool;
  protected String dataFilename;
  protected String existingDataFilename;
  
  /**
   * Prepare for test generation
   * 
   * @param workers The number of tasks than run in parallel
   * @param width The expected maximum queue length per task
   */
  /*@ requires 0 < workers;
    @ requires 0 < width; */
  public UniversalTestGenerator(int workers, int width) {
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
    taskQueue = new ChannelQueue<AlloyTask>(workers*width);
    taskPool = new AlloyPool(taskQueue, workers);
    
    dataFilename = getFilename();
    existingDataFilename = dataFilename + System.currentTimeMillis();
  }

  /**
   * @return
   */
  public String getFilename() {
    return getFilename(Method.STV, DATA_FILENAME_SUFFIX);
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
    
    
    
    // If file already exists then rename it
    final boolean existingData = checkAndRename(dataFilename, existingDataFilename);
    
    try {
      FileOutputStream fos = new FileOutputStream(dataFilename, true);
      ObjectOutputStream out = new ObjectOutputStream(fos);
      
      for (int seats = 1; seats <= numberOfSeats; seats++) {
        for (int candidates = 1 + seats; candidates <= numberOfCandidates; 
          candidates++) {
          
          createBallotBoxes(seats, candidates, method, out, 
            existingDataFilename, existingData);
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
      final Method method, ObjectOutputStream out, 
      final String filename, final boolean existingData) {
    
    ScenarioList scenarioList = scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      // Check if this scenario already generated
      if (!existingData || !alreadyExists(scenario, filename, out)) {
        
        try {
        taskQueue.put(new AlloyTask(out,scenario));
        count++;
        }
        catch (InterruptedException ioe) {
          logger.severe(ioe.toString());
        }
        
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
      String filename, ObjectOutputStream out) {
    
    // Open a new reader
    try {
      FileInputStream fis = new FileInputStream(filename);
      ObjectInputStream in = new ObjectInputStream(fis);
      
      ElectionData testData = getTestData(in);
      while (testData != null) {
        if (testData.getScenario().equivalentTo(scenario)) {
          
          // Copy existing data into new data file
          logger.info("Copying existing data: " + testData);
          out.writeObject(testData);
          
          return true;
        }
      }
      in.close();
      fis.close();
    }
    catch (IOException e) {
      logger.severe(e.getMessage());
    }
    
    return false;
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
    catch (IOException ioe) {
      logger.severe(ioe.toString());
    }
    catch (ClassNotFoundException cnfe) {
      logger.severe(cnfe.toString());
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
  protected /*@ pure @*/String getFilename(final Method method, final String suffix) {
    return FILENAME_PREFIX + method.toString() + suffix;
  }
  
  /**
   * Generate enough test data for 100% path coverage
   */
  public static void main(String[] args) {
    UniversalTestGenerator uilioch = new UniversalTestGenerator(15, 10);
    
    uilioch.generateTests(1, 5, Method.STV); // IRV 1-seat
    uilioch.generateTests(3, 7, Method.STV); // PR-STV 3-seat
    uilioch.generateTests(4, 9, Method.STV); // PR-STV 4-seat
    uilioch.generateTests(5, 11, Method.STV); // PR-STV 5-seat
    uilioch.generateTests(1, 11, Method.Plurality); // First-past-the-post
  }
}
