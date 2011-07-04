package ie.votail.uilioch;

import java.util.concurrent.Executor;



public class AlloyPool implements Executor {
  protected final Channel<AlloyTask> workQueue;
  
  @Override
  public void execute(Runnable r) {
    try {
      workQueue.put((AlloyTask)r);
    }
    catch (InterruptedException ie) { // postpone response
      Thread.currentThread().interrupt();
    }
    
  }
  
  public AlloyPool (Channel<AlloyTask> ch, int nworkers) {
    workQueue = ch;
    for (int i = 0; i < nworkers; ++i) activate();
  }
  
  protected void activate() {
    Runnable runLoop = new Runnable() {
      public void run() {
        try {
          for (;;) {
            Runnable r = (Runnable)(workQueue.take());
            r.run();
          }
        }
        catch (InterruptedException ie) {} // stop
      }
    };
    new Thread(runLoop).start();
    }
  }
