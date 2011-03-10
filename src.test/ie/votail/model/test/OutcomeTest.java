package ie.votail.model.test;

import ie.votail.model.Outcome;
import junit.framework.TestCase;

import org.junit.Test;

public class OutcomeTest extends TestCase {

  @Test
  public void testIsTied() {
    
    assertTrue (Outcome.TiedSoreLoser.isTied());
    assertTrue (Outcome.TiedLoser.isTied());
    assertTrue (Outcome.TiedWinner.isTied());
    
    assertFalse (Outcome.CompromiseWinner.isTied());
    assertFalse (Outcome.Winner.isTied());
    assertFalse (Outcome.QuotaWinner.isTied());
    assertFalse (Outcome.CompromiseWinner.isTied());
    assertFalse (Outcome.SoreLoser.isTied());
    assertFalse (Outcome.EarlyLoser.isTied());
  }

}
