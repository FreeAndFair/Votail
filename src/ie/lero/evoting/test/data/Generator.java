package ie.lero.evoting.test.data;

import election.tally.Ballot;
import election.tally.Candidate;

public class Generator {
  
  Ballot generateBallot(int number) {
    int [] preferences = new int [number];
    return new Ballot(preferences);
  }
  
  Candidate generateCandidate(int number) {
    return new Candidate();
  }

}
