package ie.lero.evoting.scenario;

import junit.framework.Test;
import junit.framework.TestSuite;

public class AllTests {

	public static Test suite() {
		TestSuite suite = new TestSuite("Test for ie.lero.evoting.scenario");
		//$JUnit-BEGIN$
		suite.addTestSuite(SurplusScenario.class);
		suite.addTestSuite(ExclusionScenario.class);
		suite.addTestSuite(StartOfCount.class);
		//$JUnit-END$
		return suite;
	}

}
