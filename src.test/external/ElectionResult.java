package external;

import election.tally.Candidate;

/**
 * Generic record of PR-STV election results
 * 
 * @author Dermot Cochran
 * 
 */
public class ElectionResult {
  
  public static class CandidateResults {
    private byte[] status;
    private int[][] votes;
    private int[] finalVotes;
    private int[] identifiers;
    
    public CandidateResults() {
    }
    
    public byte[] getStatus() {
      return status;
    }
    
    public void setStatus(byte[] status) {
      this.status = status;
    }
    
    public int[][] getVotes() {
      return votes;
    }
    
    public void setVotes(int[][] votes) {
      this.votes = votes;
    }
    
    public int[] getFinalVotes() {
      return finalVotes;
    }
    
    public void setFinalVotes(int[] finalVotes) {
      this.finalVotes = finalVotes;
    }
    
    public int[] getIdentifiers() {
      return identifiers;
    }
    
    public void setIdentifiers(int[] identifiers) {
      this.identifiers = identifiers;
    }
    
    /**
     * The candidate results, ordered by candidate identifier
     * 
     * @return
     */
    public CandidateResults canonical() {
      CandidateResults result = new CandidateResults ();
      
      // TODO
      
      return result;
      
    }
    
    public boolean equals (CandidateResults other) {
      // TODO
      
      return false;
    }
  }

  protected int quota;
  protected int threshold;
  protected CandidateResults candidateResults = new CandidateResults();

  public ElectionResult(int quota, int threshold) {
    
    this.quota = quota;
    this.threshold = threshold;
  }
  
  public ElectionResult(int quota, int threshold, int rounds,
      Candidate[] candidates) {
    
    this.quota = quota;
    this.threshold = threshold;
    
    extractCandidateResults(rounds, candidates);
  }

  /**
   * @param rounds
   * @param candidates
   */
  protected void extractCandidateResults(int rounds, Candidate[] candidates) {
    int numberOfCandidates = candidates.length;
    candidateResults.setStatus(new byte [numberOfCandidates]);
    candidateResults.setVotes(new int[numberOfCandidates][rounds]);
    candidateResults.setFinalVotes(new int[numberOfCandidates]);
    candidateResults.setIdentifiers(new int[numberOfCandidates]);
    
    for (int i = 0; i < numberOfCandidates; i++) {
      for (int r = 0; r < rounds; r++) {
        candidateResults.getVotes()[i][r] = candidates[i].getTotalAtCount(r);
      }
     candidateResults.getStatus()[i] = candidates[i].getStatus();
     candidateResults.getFinalVotes()[i] = candidates[i].getFinalVote();
     candidateResults.getIdentifiers()[i] = candidates[i].getCandidateID();
    }
  }
  
  /**
   * @return the quota
   */
  public int getQuota() {
    return quota;
  }
  
  /**
   * @return the threshold
   */
  public int getThreshold() {
    return threshold;
  }
  
  /**
   * Compare with another election result
   * 
   * @param other The other sets of results
   * 
   * @return True if all values agree, when sorted by identifier
   */
  public boolean equals (ElectionResult other) {
    
    if (this.quota != other.quota) {
      return false;
    }
    
    if (this.threshold != other.threshold) {
      return false;
    }
    
    return this.candidateResults.equals(
      other.candidateResults);
  }
  
  
}
