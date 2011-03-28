package external;

import ie.votail.model.ElectoralScenario;

public class ElectionResult {
  
  protected String title;
  private int quota;
  private int[] orderOfCandidates;

  public TestReport compare(ElectionResult other, ElectoralScenario scenario) {
    
    TestReport report = new TestReport();
    
    report.setTitle (this.title + " compared with " + other.title);
    
    // Check quota
    if (this.getQuota() != other.getQuota()) {
      report.add ("Quota calculations are not in agreement");
    }
    
    
    // Check number of rounds of counting
    
    // Check Winners
    
    
    // Check Losers
    
    return report;
  }

  private Object getQuota() {
    return this.quota;
  }

  public void setQuota(int quota) {
    this.quota = quota;
  }

  public void setTitle(String string) {
    this.title = string;
  }

  /**
   * Record election results
   * 
   * @param outcome Ordering of candidates
   */
  public void addOutcome(int[] outcome) {
    this.orderOfCandidates = outcome;
  }
  
}
