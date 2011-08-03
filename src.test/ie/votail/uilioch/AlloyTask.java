package ie.votail.uilioch;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.logging.Logger;

public class AlloyTask implements Runnable {
  
  protected ObjectOutputStream out;
  protected int initialScope = 7;
  protected ElectoralScenario scenario;
  protected static final Logger logger = Logger.getAnonymousLogger();
  protected BallotBoxFactory ballotBoxFactory;
  protected Analysis analysis;
  protected int limit; //@ protected invariant initialScope <= limit;
  
  public AlloyTask(final ObjectOutputStream out, 
      final ElectoralScenario scenario, final int maximumScope) {
    this.scenario = scenario;
    this.out = out;
    this.ballotBoxFactory = new BallotBoxFactory();
    this.analysis = new Analysis();
    this.limit = maximumScope;
  }
  
  @Override
  public void run() {
    
    try {
      // Find solution
      final ElectionConfiguration ballots =
          ballotBoxFactory.extractBallots(scenario, initialScope, limit);
      
      if (ballots == null) {
        logger.info("Failed to find a solution for scenario " + scenario);
      }
      else {
        logger.info("Writing newly generated ballot box for scenario " +
          scenario);
        writeBallots(ballots.export());
        logger.info("Finished writing ballot box for scenario " + scenario);
        
      }
      
    }
    catch (IOException e) {
      logger.severe(e.toString());
    }
  }
  
  /**
   * @param ballotBox
   * @throws IOException
   */
  protected void writeBallots(final ElectionData ballotBox)
      throws IOException {
    synchronized(out) {
      out.writeObject(ballotBox);
      out.flush();
    }
    analysis.add(scenario,ballotBox);
  }
  
}
