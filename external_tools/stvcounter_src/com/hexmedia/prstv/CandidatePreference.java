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

/* Ballots originally just stored the preferences
 * as a List<Ballot> assuming that the first element
 * of the list was #1, the 2nd #2 etc.
 * 
 * Now that preferences can be hidden we have to associate
 * the actual preference number with the candidate. This is
 * so we can detect hidden preferences, which should not
 * be hidden. eg. a ballot with some hidden prefs, but no 
 * #1 preference. This cannot happen in practice and would
 * be a sign of incorrect hiding
 *
 * Preferences are now stored as List<CandidatePreference>
 * and they must be sorted in order of highest pref (lowest number)
 * to lowest pref.
 */

package com.hexmedia.prstv;

public class CandidatePreference {

    public CandidatePreference (Candidate c, int pref) {
	this.c = c;
	this.n = pref;
    }

    public Candidate c;
    public int	     n;
}

