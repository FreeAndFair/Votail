package election.tally;

/**
 * Inner state machine
 */
public class CountStatus extends AbstractCountStatus {
  
  // Initial state
  /**
   * Inner state machine for counting of Dail election ballots.
   */
  //@ assignable substate;
  //@ ensures READY_TO_COUNT == getState();
  public CountStatus() {
    super();
    this.substate = READY_TO_COUNT;
  }
  
  
  
  /**
   * Move along the next valid transition in state.
   * 
   * @param newState
   *          The next stage of counting.
   */
  //@ also assignable substate;
  public void changeState(final int newState) {
    substate = newState;
  }
}
