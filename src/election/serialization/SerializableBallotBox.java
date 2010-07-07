/**
 * 
 */
package election.serialization;

import java.io.IOException;
import java.io.Serializable;

import election.tally.BallotBox;

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
