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
  
  public AlloyTask(ObjectOutputStream out, ElectoralScenario scenario) {
    this.scenario = scenario;
    this.out = out;
  }
  
  @Override
  public void run() {
    
    Logger logger = Logger.getAnonymousLogger();    
    BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
    try { 
      
      // Write solution to the output file
      final ElectionConfiguration ballots = 
        ballotBoxFactory.extractBallots(scenario,scope);
      final ElectionData electionData = ballots.export();
      
      if (electionData == null) {
        logger.severe("Failed to find a solution for scenario " +
            scenario);
      }
      else {
        logger.info("Writing: " + electionData);
        out.writeObject(electionData);
      }
      
    }
    catch (IOException e) {
      logger.warning(e.toString());
    }
  }
  
}
