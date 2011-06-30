package ie.votail.uilioch;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.logging.Logger;

import ie.votail.model.data.ElectionData;
import ie.votail.model.factory.BallotBoxFactory;

public class AlloyTask implements Runnable {

  protected static WorkQueue wq;
  protected ObjectOutputStream out;
  
  
  public AlloyTask(ObjectOutputStream out) {
    if (wq == null) {
      wq = new WorkQueue();
    }
    this.out = out;
  }

  @Override
  public void run() {
    
    Logger logger = Logger.getAnonymousLogger();
    
    // Get next scenario from queue
    
    BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
    WorkPackage wp;
    try {
      wp = (WorkPackage) wq.take();
      
   // Write solution to the output file
      ElectionData electionData =
        ballotBoxFactory .extractBallots(wp).export();
      
      logger.info("Writing: " + electionData);
      out.writeObject(electionData);
    }
    catch (InterruptedException e1) {
      logger.severe(e1.getMessage());
    }
    
    catch (IOException e) {
    logger.severe("Failed to save generated test data because "
        + e.getCause());
  }
  }

  public WorkQueue getWorkQueue() {
    return wq;
  }
  
}
