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

public class UniversalTestGenerator extends Uilioch {
  
  protected BallotBoxFactory ballotBoxFactory;
  protected ScenarioFactory scenarioFactory;
  protected AlloyPool taskPool;
  protected String dataFilename;
  protected String existingDataFilename;
  protected boolean existingDataFlag;
  protected int maxScope;
  
  /**
   * Prepare for test generation
   * 
   * @param workers
   *          The number of tasks than run in parallel
   * @param scopeLimit TODO
   * @param width
   *          The expected maximum queue length per task
   */
  /*@ requires 0 < workers;
    @ requires 0 < width; */
  public UniversalTestGenerator(final int workers, final int capacity, int scopeLimit) {
    super();
    
    ballotBoxFactory = new BallotBoxFactory();
    scenarioFactory = new ScenarioFactory();
    
    try {
      final String logFilename =
          UniversalTestGenerator.LOGFILENAME + "." + System.currentTimeMillis();
      final FileHandler handler = new FileHandler(logFilename);
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
      final FileOutputStream fos = new FileOutputStream(dataFilename);
      final ObjectOutputStream out = new ObjectOutputStream(fos);
      
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
  protected final boolean checkAndRename(final /*@ non_null*/String oldName,
    final /*@ non_null*/String newName) {
    
    final File file = new File(oldName);
    if (file.exists()) {
      final File newFile = new File(newName);
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
      final Method method, final ObjectOutputStream out) {
    
    final ScenarioList scenarioList = 
      scenarioFactory.find(candidates, seats, method);
    logger.fine("Scenarios: " + scenarioList.toString());
    
    int count = 0;
    
    for (ElectoralScenario scenario : scenarioList) {
      logger.info(scenario.toString());
      
      // Check if this scenario already generated
      if (!alreadyExists(scenario, out)) {
          taskPool.execute(new AlloyTask(out, scenario, maxScope));
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
  protected boolean alreadyExists(final ElectoralScenario scenario,
      final ObjectOutputStream out) {
    
    if (!existingDataFlag) {
      return false;
    }
    
    // Open a new reader
    try {
      final FileInputStream fis = new FileInputStream(existingDataFilename);
      final ObjectInputStream objectInputStream = new ObjectInputStream(fis);
      
      ElectionData testData = getTestData(objectInputStream);
      try {
        while (testData != null) {
          if (testData.getScenario().equivalentTo(scenario)) {
            logger.info("Found an existing ballot box for this scenario");
            writeBallots(out, testData, scenario);
            return true;
            
          }
          testData = getTestData(objectInputStream);
        }
      }
      catch (EOFException eofe) {
        
        logger.info("No existing ballot box for this scenario");
      }
      objectInputStream.close();
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
  protected void writeBallots(final ObjectOutputStream out,
    final ElectionData testData, final ElectoralScenario scenario) 
    throws IOException {
    final AlloyTask alloyTask = new AlloyTask(out,scenario);
    alloyTask.writeBallots(testData);
  }
  
  /**
   * Generate enough test data for 100% path coverage
   */
  public static void main(final String[] args) {
    final UniversalTestGenerator uilioch = 
      new UniversalTestGenerator(17, 17, 17); // 17 tasks with max scope of 17
    
    uilioch.generateTests(1, 5, Method.STV); // IRV 1-seat
    uilioch.generateTests(3, 7, Method.STV); // PR-STV 3-seat
    uilioch.generateTests(4, 9, Method.STV); // PR-STV 4-seat
    uilioch.generateTests(5, 11, Method.STV); // PR-STV 5-seat
    uilioch.generateTests(1, 11, Method.Plurality); // First-past-the-post
  }
}
