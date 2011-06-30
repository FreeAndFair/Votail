/**
 * 
 */
package ie.votail.uilioch;

import java.util.concurrent.Executor;

/**
 * @author dero
 *
 */
public class AlloyExecutor implements Executor {
  
  /* (non-Javadoc)
   * @see java.util.concurrent.Executor#execute(java.lang.Runnable)
   */
  @Override
  public void execute(Runnable r) {
    new Thread(r).start();
    
  }
  
}
