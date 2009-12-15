public class Example {

    /** The referenced object is owned
     * by the current object.
     */
    /*@ \rep */ Example owned;


    /** The referenced object could be owned
     * by any other object.
     * Only pure methods can be called and
     * fields can only be read.
     */
    /*@ \readonly */ Example someone;


    /** This method is pure and does not 
     * modify the object state.
     * Only pure methods can be called on
     * readonly references.
     */
    public /*@ pure */ String toString() {
	return "My example program.";
    }


    /** This method returns a rep reference
     * and can therefore only be called through
     * "this".
     */
    public /*@ \rep */ Example getRep() {
	return owned;
    }


    public void doSomething() {
	/* when you create a new object you can either
	 * create it with the same owner as 
	 * the current object ("new peer ...")
	 * or let it be owned by the current object ("new rep ...").
	 * It is not possible to create a readonly object.
	 */
	owned = new /*@ \rep */ Example();

	/**
	 * readonly can be used to store references to objects that
	 * are owned by any other object.
	 */
	someone = owned;

	/**
	 * This method call is forbidden, because it would expose the
	 * internal representation of an other object.
	 */
	// /*@ \rep */ Example target = owned.getRep(); // forbidden

	/**
	 * Arrays take two annotations, one for the array as a whole,
	 * the other one for the array elements.
	 * The array xe is owned by the current object and the
	 * contained objects can be in any context (readonly)
	 * The array is initialised with an array that is owned by the
	 * current object, but all its elements are in the same
	 * context (peer).
	 * "rep peer" arrays are subtypes of "rep readonly" arrays.
	 */
	/*@ \rep \readonly */ Example[] xe = new /*@ \rep \peer */ Example[10];

	/**
	 * This assignment is valid and does not create a runtime
	 * problem.
	 */
	xe[0] = owned;

	/**
	 * This could write an element that belongs to any context
	 * into the "rep peer" array that assumes that its elements
	 * all belong to the same context.
	 * A runtime check/verification is needed to ensure that the
	 * reference is valid.
	 * It has to be allowed at compile time, because the context
	 * is not known statically.
	 */
	xe[1] = someone;

	/**
	 * This array is owned by the same object as the current
	 * object (peer). The referenced objects are readonly and
	 * could belong to any context.
	 */
	/*@ \peer \readonly */ Example[] xb = new /*@ \peer \readonly */ Example[20];

	/**
	 * The array can be in any context and also the array elements
	 * are in any context.
	 */
	/*@ \readonly */ /*@ \readonly */ Example[] xf;

	/**
	 * We can assign any kind of array to xf.
	 */
	xf = xe;
	xf = xb;
	xf = new /*@ \peer \peer */ Example[1];
    }

}
