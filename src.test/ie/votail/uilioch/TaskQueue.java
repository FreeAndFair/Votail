package ie.votail.uilioch;

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

public class TaskQueue implements Channel {
  
  BlockingQueue<AlloyTask> queue;
  
  public TaskQueue (int capacity) {
    queue = new ArrayBlockingQueue<AlloyTask> (capacity);
  }
  
  @Override
  public void put(Object x) throws InterruptedException {
    queue.add((AlloyTask) x);    
  }
  
  @Override
  public Object take() throws InterruptedException {
    return queue.take();
  }
  
}
