package ie.votail.uilioch;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.logging.Logger;

public class AlloyTask implements Runnable {
  
  protected static ChannelQueue<ElectoralScenario> dataQueue;
  protected ObjectOutputStream out;
  protected int scope = 7;
  
  public AlloyTask(ObjectOutputStream out) {
    if (dataQueue == null) {
      dataQueue = new ChannelQueue<ElectoralScenario>(scope);
    }
    this.out = out;
  }
  
  @Override
  public void run() {
    
    Logger logger = Logger.getAnonymousLogger();    
    BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
    ElectoralScenario scenario;
    try { 
      // Get next scenario from queue
      scenario = (ElectoralScenario) dataQueue.take();
      
      if (scenario == null) {
        logger.severe ("Failed to read scenario from data queue");
      }
      else {
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
    }
    catch (InterruptedException e1) {
      logger.severe(e1.getMessage());
    }
    catch (IOException e) {
      logger.severe(e.getMessage());
    }
  }
  
  public ChannelQueue<ElectoralScenario> getWorkQueue() {
    return dataQueue;
  }
  
}
