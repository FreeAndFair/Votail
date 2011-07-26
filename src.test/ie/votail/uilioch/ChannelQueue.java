package ie.votail.uilioch;

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

public class ChannelQueue<T> implements Channel<T> {
  
  protected BlockingQueue<T> queue;  
  
  public ChannelQueue (final int capacity) {
    queue = new ArrayBlockingQueue<T> (capacity);
  }
  
  public void put(final T task) throws InterruptedException {
   
    queue.put(task); 
  }
  
  public T take() throws InterruptedException {
    return queue.take();
  }
  
}
