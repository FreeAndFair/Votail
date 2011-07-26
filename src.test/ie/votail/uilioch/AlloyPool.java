package ie.votail.uilioch;

import java.util.concurrent.Executor;
import java.util.logging.Logger;

public class AlloyPool implements Executor {
  protected final Channel<AlloyTask> workQueue;
  
  @Override
  public void execute(final Runnable task) {
    try {
      workQueue.put((AlloyTask) task);
    }
    catch (InterruptedException ie) {
      Thread.currentThread().interrupt();
    }
  }
  
  /**
   * 
   * @param nworkers
   * @param capacity
   */
  
  //@ requires 0 <= nworkers;
  //@ requires 0 <= capacity;
  public AlloyPool(final int nworkers, final int capacity) {
    workQueue = new ChannelQueue<AlloyTask>(capacity);
    for (int i = 0; i < nworkers; ++i) {
      activate();
    }
  }
  
  protected final void activate() {
    final Runnable runLoop = new Runnable() {
      public void run() {
        try {
          for (;;) {
            Runnable runner = (Runnable) (workQueue.take());
            runner.run();
          }
        }
        catch (InterruptedException ie) {
          Logger log = Logger.getAnonymousLogger();
          log.severe(ie.toString());
        }
      }
    };
    new Thread(runLoop).start();
  }
}
