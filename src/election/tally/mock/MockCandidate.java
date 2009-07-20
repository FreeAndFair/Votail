package election.tally.mock;

import election.tally.Candidate;

public class MockCandidate extends Candidate {
  
  //@ requires 1 <= n;
  public static Candidate[] generateCandidates(int n) {
    Candidate[] candidates = new Candidate[n];
    for (int i=0; i<n; i++) {
        candidates[i] = new Candidate();
    }
    return candidates;
  }

}
