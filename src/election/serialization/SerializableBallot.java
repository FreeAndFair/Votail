package election.serialization;

import java.io.IOException;
import java.io.Serializable;

import election.tally.Ballot;

public class SerializableBallot extends Ballot implements Serializable {

  public SerializableBallot(int[] preferences) {
    super(preferences);
    // TODO Auto-generated constructor stub
  }

  private void writeObject(java.io.ObjectOutputStream out) throws IOException {
  }

  private void readObject(java.io.ObjectInputStream in) throws IOException,
      ClassNotFoundException {
  }

}
