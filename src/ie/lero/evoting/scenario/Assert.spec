package org.junit.framework;

public class Assert {

	/*@ public normal_behaviour
	  @   requires flag == true;
	  @*/
	public /*@ pure @*/ void assertTrue (boolean flag);	
}