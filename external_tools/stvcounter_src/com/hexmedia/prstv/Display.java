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
import java.io.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.filechooser.*;
import javax.swing.text.html.*;
import java.beans.*;

public class Display implements ActionListener {
    static JFrame frame;
    Box buttonPanel;

    static JEditorPane edPane;
    JScrollPane scrollPane;
    static Container cp;

    static JButton initB, quitB, nextB, prevB, runAllB;

    public static final String RANDOM = "Random";
    public static final String FRACTIONAL_LAST = "Fractional (last set only)";
    public static final String FRACTIONAL_ALL = "Fractional (all votes)";
    static JLabel rulesLabel;
    static JComboBox rulesBox;

    public static String getRules () {
	rulesBox.setEnabled (false);
	rulesLabel.setEnabled (false);
	return (String) rulesBox.getSelectedItem();
    }

    FileOutputStream fout;
    public static boolean stillCounting = true;

    static Display display;

    String[] buffers;
    static int current_buffer = 0;
    static int last_buffer = -1;

    Election election;

    void nextBuffer () {
	if (current_buffer == last_buffer) {
	    return;
	}
	current_buffer ++;
	String buf = buffers[current_buffer];
	if (buf != null) {
	    display();
	}
    }

    void prevBuffer () {
	current_buffer --;
	if (current_buffer <0) {
	    current_buffer = 0;
	}
	String buf = buffers[current_buffer];
	if (buf != null) {
	    display();
	}
    }


    static Cursor oldCursor;

    public static void waitCursor () {
	oldCursor = frame.getCursor ();
	assert !oldCursor.equals(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
	frame.setCursor (Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
	cp.setCursor (Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
	edPane.setCursor (Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
    }

    public static void restoreCursor () {
	frame.setCursor (oldCursor);
	cp.setCursor (oldCursor);
	edPane.setCursor (oldCursor);
    }

    JButton createButton (String label) {
	JButton b = new JButton (label);
	b.addActionListener (this);
	b.setActionCommand (label);
	b.setAlignmentY (0.5f);
	b.setAlignmentX (0.0f);
	b.setEnabled (false);
	return b;
    }

    volatile static boolean completed = false;

    static class Worker extends SwingWorker {
        enum Task { ONE_COUNT, ALL_COUNTS};

	private Election election;
	private Task task;

	public Worker (Election e, Task t ) {
	    election = e;
	    task = t;
	}

	public Object construct () {
	    if (task == Task.ONE_COUNT) {
		completed = election.runCount();
		Display.head2 ("End of count " + election.count());
		Display.hr ();
		if (completed) {	
		    Display.head2 ("End of all counts: results follow ");
		    election.printResults();
		    last_buffer = current_buffer;
		    prevB.setEnabled (true);
		}
	    } else {
		while (!completed) {
		    completed = election.runCount();
		    Display.head2 ("End of count " + election.count());
		    Display.hr ();
		}
	    	Display.head2 ("End of all counts: results follow ");
	    	election.printResults();
	    }
	    return null;
	}

	public void finished () {
	    Display.display();
	    Display.restoreCursor();
	}
    }
	    
	    
    public void actionPerformed (ActionEvent e) {
	String cmd = e.getActionCommand();
	if (cmd.equals ("Quit")) {
	    System.exit (1);
	} else if (cmd.equals ("Initialize")) {
	    election.initialize();
	    initB.setEnabled (false);
	} else if (cmd.equals ("Run all counts")) {
	    nextBuffer();
	    if (!completed) {
	    	Display.waitCursor();
	    	new Worker (election, Worker.Task.ALL_COUNTS).start();
	    }
	} else if (cmd.equals ("Next count")) {
	    nextBuffer();
	    if (!completed) {
	    	Display.waitCursor();
	    	new Worker (election, Worker.Task.ONE_COUNT).start();
	    }
	} else if (cmd.equals ("Previous count")) {
	    Display.stillCounting = false;
	    try {
		fout.close();
	    } catch (IOException e1) {}
	    prevBuffer();
	}
    }

    Component getStrut (int size) {
	Component c = Box.createHorizontalStrut (size);
	return c;
    }

    static final String initString = "PR-STV counter V0.3";

    public static void create () {
	display = new Display ();
	head1 (initString);
	log ("(c) Michael McMahon 2005");
	log ("");
	display();
    }

    public Display () {
	buffers = new String [50];
	initB = createButton ("Initialize");
	initB.setEnabled (true);
	quitB = createButton ("Quit");
	quitB.setEnabled (true);
	nextB = createButton ("Next count");
	prevB = createButton ("Previous count");
	runAllB = createButton ("Run all counts");
	rulesLabel = new JLabel ("Surplus distribution:  ");
	rulesLabel.setAlignmentY (0.5f);
	rulesLabel.setAlignmentX (0.0f);
	rulesLabel.setVerticalTextPosition (JLabel.CENTER);
	rulesBox = new JComboBox (new Object[] {RANDOM, FRACTIONAL_LAST, FRACTIONAL_ALL});
	rulesBox.setAlignmentY (0.5f);
	rulesBox.setAlignmentX (0.0f);
	buttonPanel = Box.createHorizontalBox();
	buttonPanel.setBorder (new EmptyBorder (5,5,5,5));
	buttonPanel.add (quitB);
	buttonPanel.add (getStrut(5));
	buttonPanel.add (initB);
	buttonPanel.add (getStrut(5));
	buttonPanel.add (nextB);
	buttonPanel.add (getStrut(5));
	buttonPanel.add (prevB);
	buttonPanel.add (getStrut(5));
	buttonPanel.add (runAllB);
	buttonPanel.add (getStrut (5));
	buttonPanel.add (rulesLabel);
	buttonPanel.add (rulesBox);
	buttonPanel.setMaximumSize (new Dimension (800, 30));

	JEditorPane.registerEditorKitForContentType (
		"text/html", "com.hexmedia.prstv.EditorKit"
	);
	edPane = new JEditorPane ("text/html","");
	edPane.setBorder (new EmptyBorder (5,5,5,5));
	edPane.setEditable (false);
	
	scrollPane = new JScrollPane (
		edPane,
		ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
		ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER
	);
	scrollPane.setBorder (new CompoundBorder (new EmptyBorder(5,5,5,5), new LineBorder (Color.BLACK)));
	frame = new JFrame ("Elections");
	cp = frame.getContentPane();
	frame.setLayout (new BoxLayout(cp, BoxLayout.Y_AXIS));
	cp.add (scrollPane);
	cp.add (buttonPanel);
	frame.setSize (new Dimension (800, 600));
	frame.setVisible(true);
	try {
	    fout = new FileOutputStream ("results.html");
	} catch (Exception e) {
	    error ("could not open results.html for writing", e);
	}
    }

    public static void enableNextButton () {
	display.nextB.setEnabled (true);
	display.runAllB.setEnabled (true);
    }

    public static void setElection (Election e) {
	display.election = e;
    }

    public static void logRed (String text) {
	display.head2 ("<font color=\"red\">"+text+"</font><br>");
    }

    public static void logGreen (String text) {
	display.head2 ("<font color=\"green\">"+text+"</font><br>");
    }

    public static void log (String text) {
	display.log0 (text+"<br>");
    }

    public static void startBulletList() {
	logx ("<ul>");
    }

    public static void endBulletList() {
	logx ("</ul>");
    }

    public static void listItem (String text) {
	logx("<li>"+text+"<p></li>");
    }

    public static void logx (String text) {
	display.log0 (text);
    }

    public static void nextPage () {
	display.nextBuffer ();
    }

    /* display the current buffer */

    public static void display () {
	display.display0();
    }

    static int fg = 0;

    public synchronized void display0 () {
	if (stillCounting) {
	    try {
	    	fout.write (buffers[current_buffer].getBytes());
	    } catch (IOException e) {
		error (e.toString(), e);
	    }
	}
	edPane.setText (buffers[current_buffer]);
	final JEditorPane p = edPane;
	SwingUtilities.invokeLater ( new Runnable () {
	    public void run () {
		p.scrollRectToVisible (new Rectangle (0,0, 90, 90));
	    }
	});
    }

    synchronized void log0 (String t) {
	if (buffers[current_buffer] == null) {
	    buffers[current_buffer] = "";
	}
	buffers[current_buffer] = buffers[current_buffer] + t;
    }

    public static void head2 (String s) {
	logx ("<h2>"+s+"</h2>");
    }

    public static void hr() {
	logx ("<hr>");
    }

    public static void tableStart (boolean border) {
	String s = border? "border" :"";
	logx ("<table "+s+" caption=\""+s+"\">");
    }

    public static void tableRow (Object[] row) {
	tableRow (row, null);
    }

    public static void tableRow (Object[] row, String align) {
	for (int i=0; i<row.length; i++) {
	    String s=null;
	    String alstr="";
	    if (i!=0 && align!= null) {
		alstr = "align=\""+align+"\"";
	    }
	    if (row[i] instanceof String) {
		s = (String) row[i];
	    } else {
		s = row[i].toString();
	    }
	    logx ("<td " + alstr + ">"+s+"</td>");
	}
	logx ("</tr>");
    }
	
    public static void tableHead (Object[] row) {
	logx ("<tr>");
	for (int i=0; i<row.length; i++) {
	    String s=null;
	    if (row[i] instanceof String) {
		s = (String) row[i];
	    } else {
		s = row[i].toString();
	    }
	    logx ("<td><i>"+s+"</i></td>");
	}
	logx ("</tr>");
    }
	
    public static void tableEnd () {
	logx ("</table>");
    }

    public static void head1 (String s) {
	logx ("<h1>"+s+"</h1>");
    }

    public static void error (String text, Throwable t) {
	display.error0 (text);
	if (t != null) {
	    try {
	        FileOutputStream ferr = new FileOutputStream ("exception.txt");
	        PrintStream ps = new PrintStream (ferr);
		ps.println (t.getMessage());
	        t.printStackTrace (ps);
		ps.close();
	    } catch (Exception e) {
		System.out.println (e);
	    }
	}
	System.exit (0);
    }

    void error0 (String text) {
	JOptionPane.showMessageDialog (frame, text, "Error", 
	    JOptionPane.ERROR_MESSAGE
	);
    }
	
    public static void warn (String[] text) {
	display.warn0 (text);
    }

    public static void warn (String text) {
	display.warn0 (text);
    }

    void warn0 (String text) {
	JOptionPane.showMessageDialog (frame, text, "Warning", 
	    JOptionPane.WARNING_MESSAGE
	);
    }

    void warn0 (String[] text) {
	JOptionPane.showMessageDialog (frame, text, "Warning", 
	    JOptionPane.WARNING_MESSAGE
	);
    }
}
