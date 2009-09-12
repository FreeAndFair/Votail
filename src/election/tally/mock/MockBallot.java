package election.tally.mock;

/**
 * Mock ballot object for testing only.
 * 
 * @author Dermot Cochran, University College Dublin, Ireland.
 */
public class MockBallot extends election.tally.Ballot {

  /**
   * Set the first preference candidate ID on the ballot paper.
   * 
   * @param firstPreferenceID The first preference candidate ID
   */
  public final void setFirstPreference(final int firstPreferenceID) {
    int[] list = { firstPreferenceID };
    setMultiplePreferences(list);
  }

  /**
   * Set the preferences on a ballot paper.
   * 
   * @param list The list of preferences on a ballot paper.
   */
  public final void setMultiplePreferences(final int[] list) {
    load(list);
  }

}
