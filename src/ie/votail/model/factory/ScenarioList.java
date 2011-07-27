/**
 * List of Electoral Scenarios.
 * 
 * @author Dermot Cochran, 2010-2011, IT University of Copenhagen, Denmark.
 */

package ie.votail.model.factory;

import ie.votail.model.ElectoralScenario;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ScenarioList extends ArrayList<ElectoralScenario> implements Serializable {
  
  /**
   * 
   */
  private static final long serialVersionUID = 7207848959544184536L;

  // Maximum number of partitions within the list
  public static final int MAX_PARTITIONS = 11; // Ten possible outcomes, plus one
  
  // Sublists of scenarios for each fixed number of winners
  protected List<ElectoralScenario>[] partitions;
  
  // Scenarios with a larger number of winners, not held in any partition
  protected List<ElectoralScenario> bucket;
  
  /**
   * Creates a new empty list of scenarios, with an empty bucket and
   * empty partitions.
   */
  /*@ ensures this.partitions.length == MAX_PARTITIONS;
    @ ensures this.bucket.size() == 0;
    @ ensures this.size() == 0;
    @*/
  @SuppressWarnings("unchecked")
  public ScenarioList() {
    super();
    this.partitions = new ArrayList[MAX_PARTITIONS];
    for (int i = 0; i < MAX_PARTITIONS; i++) {
      partitions[i] = new ArrayList<ElectoralScenario>();
    }
    bucket = new ArrayList<ElectoralScenario>();
  }
  
  /**
   * Discover whether a scenario is in the <code>ScenarioList</code>.
   * 
   * @param scenario
   *          The scenario to look for
   * @return <code>true</code> if the scenario is in the list
   */
  public boolean hasScenario(final /*@ non_null @*/ ElectoralScenario scenario) {
    final Iterator<ElectoralScenario> scenarioIterator = this.iterator();
    while (scenarioIterator.hasNext()) {
      if (scenarioIterator.next().equivalentTo(scenario)) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Add scenario to one of the partitions or to the bucket as well as adding
   * to the master list.
   * 
   * @param scenario
   *          The scenario to be added
   * @return <code>true</code> if this scenario is not already in list
   */
  //@ ensures this.hasScenario(scenario);
  @Override
  public boolean add(final /*@ non_null*/ElectoralScenario scenario) {
    if (this.hasScenario(scenario)) {
      return false;
    }
    
    // Sort the scenario into canonical order before adding it
    final ElectoralScenario canonical = scenario.canonical();
    
    // Also, add to sublist according to number of winners
    final int partitionNumber = scenario.numberOfWinners();
    if (partitionNumber < MAX_PARTITIONS) {
      partitions[partitionNumber].add(canonical);
    }
    else {
      bucket.add(canonical);
    }
    return super.add(canonical);
  }
  
  /**
   * Get the number of scenarios with this exact number of winners, or the
   * number of scenarios in the bucket if there are more winners than
   * partitions
   * 
   * @param numberOfWinners
   *          The number of winners in each scenario
   * @return Either the number of scenarios in this partition or the bucket
   */
  /*@ requires 0 < numberOfWinners;
    @ ensures 0 <= \result;
   */
  public/*@ pure*/int getNumberOfScenarios(final int numberOfWinners) {
    if (numberOfWinners <= MAX_PARTITIONS) {
      return partitions[numberOfWinners].size();
    }
    return bucket.size();
  }
}
