package ie.votail.uilioch;

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.logging.Logger;

public class ChannelQueue<T> implements Channel<T> {
  
  BlockingQueue<T> queue;
  protected Logger logger;
  
  
  public ChannelQueue (int capacity) {
    queue = new ArrayBlockingQueue<T> (capacity);
    logger = Logger.getAnonymousLogger();
  }
  
  @Override
  public void put(T x) throws InterruptedException {
   
    queue.put(x); 
  }
  
  @Override
  public T take() throws InterruptedException {
    return queue.take();
  }
  
}
