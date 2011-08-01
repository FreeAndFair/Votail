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
    protected byte[] status;
    protected int[] identifiers;
    
    //@ requires this.status == null;
    //@ requires \nonnullelements (listOfStates);
    //@ ensures \nonnullelements (this.status);
    public void setStatus(final byte[] listOfStates) {
      this.status = new byte[listOfStates.length];
      for (int i = 0; i < listOfStates.length; i++) {
        this.status[i] = listOfStates[i];
      }
    }
    
    //@ requires thus.identifiers == null;
    //@ requires \nonnullelements (listOfIDs);
    //@ ensures \nonnullelements (this.identifiers);
    public void setIdentifiers(final int[] listOfIDs) {
      this.identifiers = new int[listOfIDs.length];
      for (int i = 0; i < listOfIDs.length; i++) {
        this.identifiers[i] = listOfIDs[i];
      }
    }
    
    /**
     * Do these candidate results match each other?
     * 
     * @param other
     *          The other set of results
     * @return <code>True</code> if the election results agree, when sorted in
     *         a canonical order
     */
    public boolean matches(final CandidateResults other) {
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
     * @param number
     *          the numberOfCandidates to set
     */
    /*@ requires 1 < number;
      @ assignable this.numberOfCandidates;
      @ ensures this.numberOfCandidates == number;
      @*/
    public void setNumberOfCandidates(final int number) {
      this.numberOfCandidates = number;
    }
  }
  
  protected CandidateResults candidateResults = new CandidateResults();
  private int threshold;
  private int quota;
  
  /**
   * Extract election results from Votail format
   * 
   * @param candidates
   * @param theThreshold 
   * @param theQuota 
   */
  public ElectionResult(final Candidate[] candidates, final int theQuota, 
      final int theThreshold) {
    
    extractCandidateResults(candidates);
    this.setQuota(theQuota);
    this.setThreshold(theThreshold);
  }
  
  public ElectionResult(final int[] outcome, final int numberOfWinners) {
    load(outcome, numberOfWinners);
  }
  
  /**
   * Extract election results from Coyle Doyle format
   * 
   * @param outcome The ordered list of winners and losers
   * @param numberOfWinners The number of winners
   */
  public final void load(int[] outcome, final int numberOfWinners) {
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
    // Create an empty result, to be filled later
  }
  
  /**
   * Extract candidate results from Votail format
   * 
   * @param candidates
   */
  protected final void extractCandidateResults(Candidate[] candidates) {
    candidateResults.numberOfCandidates = candidates.length;
    byte[] status = new byte[candidateResults.numberOfCandidates];
    int[] identifiers = new int[candidateResults.numberOfCandidates];
    for (int index=0; index < candidates.length; index++) {
      status[index] = candidates[index].getStatus();
      identifiers[index] = candidates[index].getCandidateID();
    }
    candidateResults.setIdentifiers(identifiers);
    candidateResults.setStatus(status);    
  }
  
  /**
   * Compare with another election result
   * 
   * @param other
   *          The other sets of results
   * 
   * @return True if all values agree, when sorted by identifier
   */
  public boolean matches(ElectionResult other) {
    
    return this.candidateResults.matches(other.candidateResults);
  }
 
  public /*@ pure */ byte getStatus (int index) {
    return this.candidateResults.status[index];   
  }
  
  public int getThreshold() {
    return threshold;
  }
  
  public int getQuota() {
    return quota;
  }

  /**
   * @param threshold the threshold to set
   */
  public void setThreshold(int threshold) {
    this.threshold = threshold;
  }

  /**
   * @param quota the quota to set
   */
  public void setQuota(int quota) {
    this.quota = quota;
  }
}
