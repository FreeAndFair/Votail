/**
 * Double list of Scenarios, containing partitions based on the numbers of
 * winners in each scenario, as well as the full list of all scenarios, for
 * a given number of outcomes.
 * 
 * @author Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model.factory;

import ie.votail.model.Scenario;

import java.util.ArrayList;

public class ScenarioList extends ArrayList<Scenario> {
  
  // Maximum number of winners to keep track of
  public static int MAX_PARTITIONS = 6;
  
  // Sublists of scenarios for each fixed number of winners
  protected ArrayList<Scenario>[] partitions;
  
  // Scenarios with a larger number of winners, not held in any partition
  protected ArrayList<Scenario> bucket;

  /**
   * Creates a new empty list of scenarios, with an empty bucket and 
   * empty partitions.
   */
  /*@
   * ensures this.partitions.length == MAX_PARTITIONS;
   * ensures this.bucket.size() == 0;
   * ensures this.size() == 0;
   */
  @SuppressWarnings("unchecked")
  
  public ScenarioList() {
    this.partitions = new ArrayList[MAX_PARTITIONS];
    for (int i=0; i<MAX_PARTITIONS; i++) {
      partitions[i] = new ArrayList<Scenario>();
    }
    bucket = new ArrayList<Scenario>();
  }

  /**
   * Add scenario to one of the partitions or to the bucket as well as adding
   * to the master list
   * 
   * @param scenario The scenario to be added
   * @return <code>true</code> if this scenario is not already in list
   */
  @Override
  public boolean add(/*@ non_null*/ Scenario scenario) {
    // Sort the scenario into canonical order before adding it
    Scenario canonical = scenario.canonical();
    
    // Also, add to sublist according to number of winners
    int partitionNumber = scenario.numberOfWinners()-1;
    if (partitionNumber < MAX_PARTITIONS) {
      if (!partitions[partitionNumber].contains(canonical)) {
        partitions[partitionNumber].add(canonical);
      }
    }
    else if (!bucket.contains(canonical)){
      bucket.add(canonical);
    }
    if (!super.contains(canonical)) {
      return super.add(canonical);
    }
    return false;
  }
  
  /**
   * Get the number of scenarios with this exact number of winners, or the 
   * number of scenarios in the bucket if there are more winners than
   * partitions
   * 
   * @param numberOfWinners The number of winners in each scenario
   * @return Either the number of scenarios in this partition or the bucket
   */
  /*@
   * requires 0 < numberOfWinners;
   * ensures 0 <= \result;
   */
  public /*@ pure*/ int getNumberOfScenarios (int numberOfWinners) {
    if (numberOfWinners <= MAX_PARTITIONS) {
      return partitions[numberOfWinners-1].size();
    }
    return bucket.size();
  }
}
