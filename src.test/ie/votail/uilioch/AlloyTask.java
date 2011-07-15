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
  protected int scope = 7;
  protected ElectoralScenario scenario;
  protected Logger logger;
  protected BallotBoxFactory ballotBoxFactory;
  protected Analysis analysis;
  
  public AlloyTask(ObjectOutputStream out, ElectoralScenario scenario) {
    this.scenario = scenario;
    this.out = out;
    this.logger = Logger.getAnonymousLogger();
    this.ballotBoxFactory = new BallotBoxFactory();
    this.analysis = new Analysis();
  }
  
  @Override
  public void run() {
    
    try {
      // Find solution
      final ElectionConfiguration ballots =
          ballotBoxFactory.extractBallots(scenario, scope);
      
      if (ballots == null) {
        logger.severe("Failed to find a solution for scenario " + scenario);
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
  protected synchronized void writeBallots(final ElectionData ballotBox)
      throws IOException {
    out.writeObject(ballotBox);
    out.flush();
    analysis.add(scenario,ballotBox);
  }
  
}
