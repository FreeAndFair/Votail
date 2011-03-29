/**
 *  Copyright 2005 Michael McMahon
 *
 *  This file is part of STVCounter
 *
 *  STVCounter is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  STVCounter is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.hexmedia.prstv;

import java.awt.*;
import java.awt.event.*;

public class Main implements ActionListener {
    public static void main (String[] args) throws Exception {
    	Main app = new Main();
	try {
	    String s = System.getProperty ("java.specification.version");
	    System.out.println ("version: "+ s);
	    String s1[] = s.split("\\.");
	    int version = Integer.parseInt (s1[0]) * 10 +
				Integer.parseInt (s1[1]);
	
	    if (version < 15) {
		app.error ("Wrong version of Java on this system. This "+
			"application "+
			"requires version 1.5 or higher. Get the latest "+
			"version of the Java runtime (JRE) "+
			"from http://java.sun.com/ ");
	    } else {
	    	Election.main (args);
	    }
	} catch (Throwable t) {
	    app.error (t.toString());
	}
    }

    public void actionPerformed (ActionEvent e) {
	System.exit (1);
    }

    Dialog d;

    public void error (String s) {
	d = new Dialog (new Frame(), true);
	d.setLayout (new BorderLayout());
	Button button = new Button ("Quit");
	button.addActionListener (this);
	d.add (new Label (s), BorderLayout.NORTH);
	Container c = new Container();
	c.setLayout (new FlowLayout());
	d.add (c, BorderLayout.SOUTH);
	c.add (button);
	d.setSize (new Dimension (900, 100));
	d.show();
    }
}
