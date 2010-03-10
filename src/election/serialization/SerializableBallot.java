package election.serialization;

import java.io.Serializable;

import election.tally.Ballot;

public class SerializableBallot extends Ballot implements Serializable {

  public SerializableBallot(int[] preferences) {
    super(preferences);
    // TODO Auto-generated constructor stub
  }

}
