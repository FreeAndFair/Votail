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
    protected int roundsOfCounting;
    protected int numberOfCandidates;
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
    
    public boolean equals (CandidateResults other) {
      if (this.numberOfCandidates != other.numberOfCandidates) {
        return false;
      }
      
      if (this.roundsOfCounting != other.roundsOfCounting) {
        return false;
      }
      
      for (int i=0; i<numberOfCandidates;i++) {
        
        // Find matching candidate ID
        boolean matchedID = false;
        for (int j=0; j<numberOfCandidates; j++) {
          if (this.identifiers[i] == other.identifiers[j]) {
            matchedID = true;
            if (this.status[i] != other.status[j]) {
              return false;
            }
            
            // TODO
            // TODO
            // TODO
            
            for (int round=0; round<this.roundsOfCounting; rounds++) {
              
            }
          }
          if (!matchedID) {
            return false;
          }
        }
      }
      
      return true;
    }

    /**
     * @return the roundsOfCounting
     */
    public int getRoundsOfCounting() {
      return roundsOfCounting;
    }

    /**
     * @return the numberOfCandidates
     */
    public int getNumberOfCandidates() {
      return numberOfCandidates;
    }

    /**
     * @param roundsOfCounting the roundsOfCounting to set
     */
    public void setRoundsOfCounting(int roundsOfCounting) {
      this.roundsOfCounting = roundsOfCounting;
    }

    /**
     * @param numberOfCandidates the numberOfCandidates to set
     */
    public void setNumberOfCandidates(int numberOfCandidates) {
      this.numberOfCandidates = numberOfCandidates;
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
