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

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.text.html.*;
import java.beans.*;

public class InitParams extends JDialog implements ActionListener {

    Box vbox, hbox;
    JButton choose, okB, cancelB;
    JTextField name, nseats;
    JPanel panel;
    JFileChooser chooser;

    static final String chooseS = "Choose file ...";
    static final String okS = "Ok";

    JButton createButton (String label) {
	JButton b = new JButton (label);
	b.addActionListener (this);
	b.setActionCommand (label);
	b.setAlignmentY (0.5f);
	b.setAlignmentX (0.0f);
	b.setEnabled (true);
	return b;
    }

    InitParams (Frame parent) {
	super (parent, "Initialize parameters", true);
    	chooser = new JFileChooser ();
	chooser.setFileFilter (new javax.swing.filechooser.FileFilter() {
	    public boolean accept (File f) {
		if (f.isDirectory()) {
		    return true;
		}
		String name = f.getName();
		int index = name.lastIndexOf ('.');
		if (index == -1) {
		    return false;
		}
		String sub= name.substring (index);
		return sub.equalsIgnoreCase(".txt") ||
			sub.equalsIgnoreCase(".csv");
	    }
	    public String getDescription () {
		return ".CSV and .TXT files";
	    }
	});
	JLabel l1, l2;
	setSize (400, 275);
	vbox = Box.createVerticalBox();
	vbox.setBorder (new EmptyBorder (10,10,10,10));
	hbox = Box.createHorizontalBox();
	getContentPane().add (vbox);
	String msg = 
	    "<html>Please enter the input file containing the comma separated (csv) vote "+
	    "data, and also the number of seats in the race.<p>Note, you can also enter the "+
	    "filename and number of seats on the command line.</html>";
	l1 = new JLabel (msg);
	l1.setAlignmentX(0.0f);
	hbox.setAlignmentX(0.0f);
	vbox.add (l1);
	vbox.add (Box.createVerticalGlue());
	Box p = Box.createHorizontalBox ();
	p.setAlignmentX(0.0f);
	l2 = new JLabel ("Input file name:     ");
	l2.setAlignmentX(0.0f);
	p.add (l2);
	p.add (Box.createHorizontalStrut (20));
	name = new JTextField (10);
	name.setMaximumSize (new Dimension (100, 30));
	name.setAlignmentX(0.0f);
	name.setEditable (true);
	name.setEnabled (true);
	p.add (name);
	p.add (Box.createHorizontalStrut (20));
	choose = createButton (chooseS);
	choose.setAlignmentX(0.0f);
	p.add (choose);
	vbox.add (p);
	vbox.add (Box.createVerticalGlue());
	p = Box.createHorizontalBox ();
	p.setAlignmentX(0.0f);
	l2 = new JLabel ("Number of seats: ");
	l2.setAlignmentX(0.0f);
	p.add (l2);
	p.add (Box.createHorizontalStrut (20));
	nseats = new JTextField (10);
	nseats.setMaximumSize (new Dimension (100, 30));
	nseats.setAlignmentX(0.0f);
	nseats.setEditable (true);
	nseats.setEnabled (true);
	p.add (nseats);
	vbox.add (p);
	vbox.add (Box.createVerticalGlue());
	vbox.add (new JSeparator());
	vbox.add (hbox);
	okB = createButton (okS);
	hbox.add (okB);
	setVisible(true);
    }

    public static void main (String[] a ) throws Exception {
	InitParams ip = new InitParams (null);
    }

    public String filename() {
	String s = name.getText();
	if (s == null) {
	    return null;
	}
	return s;
    }

    public String chooserfilename() {
	File f = chooser.getSelectedFile();
	if (f == null) {
	    return "";
	}
	String s = chooser.getSelectedFile().getAbsolutePath();
	if (s == null) {
	    return "";
	}
	return s;
    }

    public String seats () {
	String s = nseats.getText();
	if (s == null) {
	    return "";
	}
	return s;
    }

    public void actionPerformed (ActionEvent e) {
	String cmd = e.getActionCommand();
	if (cmd.equals (okS)) {
	    dispose();
	} else if (cmd.equals (chooseS)) {
	    chooser.showOpenDialog (this);
	    name.setText (chooserfilename());
	}
    }
}
