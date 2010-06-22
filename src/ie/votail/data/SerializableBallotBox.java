/**
 * 
 */
package ie.votail.data;

import ie.votail.tally.BallotBox;

import java.io.IOException;
import java.io.Serializable;


/**
 * @author dero
 * @version 0.0.2
 */
public class SerializableBallotBox extends BallotBox implements Serializable {

  /**
   * 
   */
  public SerializableBallotBox() {
    // TODO Auto-generated constructor stub
  }

  private void writeObject(java.io.ObjectOutputStream out) throws IOException {
  }

  private void readObject(java.io.ObjectInputStream in) throws IOException,
      ClassNotFoundException {
  }

}
