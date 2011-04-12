package ie.votail.model;

import election.tally.Candidate;
import election.tally.CandidateStatus;

/**
 * Generic record of PR-STV election results
 * 
 * @author Dermot Cochran
 * 
 */
public class ElectionResult {
  
  /**
   * Results for each candidate.
   * 
   * @author Dermot Cochran
   */
  
  public static class CandidateResults {
    protected int numberOfCandidates;
    private byte[] status;
    private int[] identifiers;
    
    public CandidateResults() {
    }
    
    public byte[] getStatus() {
      return status;
    }
    
    public void setStatus(byte[] status) {
      this.status = status;
    }
    
    public int[] getIdentifiers() {
      return identifiers;
    }
    
    public void setIdentifiers(int[] identifiers) {
      this.identifiers = identifiers;
    }
    
    /**
     * Do these candidate results match each other?
     * 
     * @param other
     *          The other set of results
     * @return <code>True</code> if the election results agree, when sorted in
     *         a canonical order
     */
    public boolean equals(CandidateResults other) {
      if (this.numberOfCandidates != other.numberOfCandidates) {
        return false;
      }
      
      for (int i = 0; i < numberOfCandidates; i++) {
        
        // Find matching candidate ID
        boolean matchedID = false;
        for (int j = 0; j < numberOfCandidates; j++) {
          if (this.identifiers[i] == other.identifiers[j]) {
            matchedID = true;
            if (this.status[i] != other.status[j]) {
              return false;
            }
          }
        }
        if (!matchedID) {
          return false;
        }
      }
      
      return true;
    }
    
    /**
     * @return the numberOfCandidates
     */
    public int getNumberOfCandidates() {
      return numberOfCandidates;
    }
    
    /**
     * @param numberOfCandidates
     *          the numberOfCandidates to set
     */
    public void setNumberOfCandidates(int numberOfCandidates) {
      this.numberOfCandidates = numberOfCandidates;
    }
  }
  
  protected CandidateResults candidateResults = new CandidateResults();
  
  /**
   * Extract election results from Votail format
   * 
   * @param quota
   * @param threshold
   * @param rounds
   * @param candidates
   */
  public ElectionResult(Candidate[] candidates) {
    
    extractCandidateResults(candidates);
  }
  
  /**
   * @deprecated
   */
  public ElectionResult(int[] outcome, int numberOfWinners) {
    load(outcome, numberOfWinners);
  }
  
  /**
   * Extract election results from Coyle Doyle format
   * 
   * @param outcome The ordered list of winners and losers
   * @param numberOfWinners The number of winners
   */
  public void load(int[] outcome, int numberOfWinners) {
    candidateResults.numberOfCandidates = outcome.length;
    
    candidateResults.setIdentifiers(outcome);
    for (int i = 0; i < candidateResults.numberOfCandidates; i++) {
      if (i < numberOfWinners) {
        candidateResults.status[i] = CandidateStatus.ELECTED;
      }
      else {
        candidateResults.status[i] = CandidateStatus.ELIMINATED;
      }
    }
  }
  
  /**
   * Create an empty Election Result.
   */
  public ElectionResult() {
  }
  
  /**
   * Extract candidate results from Votail format
   * 
   * @param candidates
   */
  protected void extractCandidateResults(Candidate[] candidates) {
    candidateResults.numberOfCandidates = candidates.length;
    candidateResults.setStatus(new byte[candidateResults.numberOfCandidates]);
    candidateResults
        .setIdentifiers(new int[candidateResults.numberOfCandidates]);
  }
  
  /**
   * Compare with another election result
   * 
   * @param other
   *          The other sets of results
   * 
   * @return True if all values agree, when sorted by identifier
   */
  public boolean equals(ElectionResult other) {
    
    return this.candidateResults.equals(other.candidateResults);
  }
  
}
