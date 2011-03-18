package external;

import ie.votail.model.factory.ScenarioList;
import com.hexmedia.prstv.Election;
import com.hexmedia.prstv.Main;
import com.hexmedia.prstv.InitParams;

public class TestExternalAPIs {
  
  // TODO replay PR-STV scenario list from stored file
  ScenarioList scenarioList 
    = new ScenarioList (ie.votail.model.factory.test.VotailSystemTest.SCENARIO_LIST_FILENAME);
;  

  Election election;
}

// TODO HexMedia - Michael McMahon

// TODO CoyleDoyle

// TODO BallotBox.ie - Joe McCarthey et al
