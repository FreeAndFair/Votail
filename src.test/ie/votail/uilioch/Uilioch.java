package ie.votail.uilioch;

import ie.votail.model.Method;
import ie.votail.model.data.ElectionData;

import java.io.EOFException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.logging.Logger;

public class Uilioch {
  
  protected static final String FILENAME_PREFIX = "testdata/";
  protected static final String DATA_FILENAME_SUFFIX = "_election.data";
  protected static final String LOGFILENAME = "logs/uilioch/generator.log";
  protected Logger logger;

  public Uilioch() {
    super();
  }

  /**
   * @return
   */
  public String getFilename() {
    return getFilename(Method.STV, DATA_FILENAME_SUFFIX);
  }

  /**
   * Deserialization of Test Data
   * 
   * @param in
   *          The Object Input Stream which contains the test data
   * @return The Test Data (or null)
   */
  public synchronized ElectionData getTestData(ObjectInputStream in) {
    
    ElectionData electionData = null;
    
    try {
      electionData = (ElectionData) in.readObject();
    }
    catch (EOFException eofe) {
      
      logger.info("No more ballot boxes to read");
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
   * Get name of the file in which to store generated test data and from which
   * the test data will be read when running the tests.
   * 
   * @param method
   *          The type of voting scheme
   * @return The filename
   */
  protected String getFilename(final Method method, final String suffix) {
    return FILENAME_PREFIX + method.toString() + suffix;
  }
  
}