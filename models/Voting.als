-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Voting

open util/integer

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API, but not by the analyser

/* 
	 There are 8 winning-outcomes and 8 losing-outcomes, 
  of which 2 winning-outcomes and 4 losing-outcomes are for Plurality

  WinnerNonTransferable: 
                    elected on first round with at least one non-transferable surplus vote (STV),
	 SurplusWinner:		  elected on first round with at least one surplus vote (STV),
	 Winner: 				      elected in the first round of counting either by quota or plurality,

  AboveQuotaWinner: elected with surplus votes after receipt of transfers (STV),
  QuotaWinnerNonTransferable:
				                elected with at least one non-transferable surplus vote (STV),
  QuotaWinner: 		   elected with quota after transfers from another candidate (STV),

	 CompromiseWinner: elected on the last round of counting without quota (STV),
	 TiedWinner:			    elected by tie breaker,

	 TiedLoser:			     defeated only by tie breaker but reaches the threshold,
  TiedSoreLoser:		  defeated only by tie breaker but does not reach threshold,
	 Loser:			 		      defeated on last round but reaches the minimum threshold of votes,
  SoreLoser: 			    defeated, but does not even reach the mimimum threshold of votes

  EarlyLoserNonTransferable:
                    reaches threshold bit is eliminated with some non-transferable votes (STV),
	 EarlyLoser:		     reaches threshold but is eliminated before last round (STV),
  EarlySoreLoser:   eliminated before last round, and below threshold (STV),
  EarlySoreLoserNonTransferable:
																				below threshold and eliminated with some non-transferable votes (STV)

*/
enum Event {SurplusWinner, 
            WinnerNonTransferable, 
            Winner, 
            AboveQuotaWinner, 
            QuotaWinnerNonTransferable, 
            QuotaWinner, 
            CompromiseWinner, 
	           TiedWinner, 
            TiedLoser, 
            Loser, 
            EarlyLoser, 
            EarlyLoserNonTransferable,
            TiedSoreLoser, 
            SoreLoser,
            EarlySoreLoser,
            EarlySoreLoserNonTransferable}

/* 
	Two existing real-world voting methods,
	and one experimental method chosen for being hard to
	manipulate and for other ideal properties.
*/
enum Method {Plurality, STV, Ideal}

/*
	Ideal method does not rely on randomisation either for tie breakers, or
 for redistribution of transfers. So the ordering of ballots does not matter.

	Joint preferences and fractional transfers are allowed.
	Ties are resolved with a mini-election as if all other candidates were excluded.

	No wasted votes; a non-preference for a candidate indicates non-approval, 
 used when mini-elections are tied. An unresolvable tie leads to a fresh 
 bye-election for the remaining seats.
	
 None of these steps are possible with paper-based counting; since there is only
	one copy of the paper ballot, so fractional transfers and pairwise comparisons
	are impossible unless digital counting of ballots is allowed.

	Approvals are used to determine thresholds for funding and deposits, so that each
	candidate needs a full quota of approvals. 

 Optionaly, pre-elimination could be used for candidates without a half-quota of
 approvals since by definition, those candidates would never reach a full
	quota of ballots under any combination of transfers, although such a candidate 
 might still be elected without quota in the last round.

 Pre-elimination of too many candidates would also lead to a bye-election. A blank
	spoilt vote would count as disapproval of all candidates.
*/

-- An individual person standing for election
sig Candidate {
  votes: 			  set Ballot, 	-- First preference ballots assigned to this candidate
	 transfers: 	set Ballot,  -- Second and subsequent preferences received
	 surplus: 		 set Ballot, 	-- Ballots tranferred to another candidate election
  wasted:		 	 set Ballot,	 -- Ballots non-transferable due to exhaustion of preferences
	 outcome: 		 Event		      -- Path to election result for each candidate
} {
     // Ballots available for transfers but without further preferences
     0 < #wasted iff (outcome = WinnerNonTransferable or 
                      outcome = QuotaWinnerNonTransferable or
                      outcome = EarlyLoserNonTransferable or
	                     outcome = EarlySoreLoserNonTransferable)

     // Ballots are only counted as wasted in they belong to the surplus, or
     (outcome = WinnerNonTransferable or outcome = QuotaWinnerNonTransferable)
       implies wasted in surplus

     // ... if the ballots are from an excluded candidate
     (outcome = EarlyLoserNonTransferable or outcome = EarlySoreLoserNonTransferable)
       implies wasted in votes + transfers

     // Division of ballots into first preferences and transfers
	    no b: Ballot | b in votes & transfers

     // Division of ballots into piles for each candidate
	    all b: Ballot | b in votes + transfers implies this in b.assignees

     // Selection of surplus ballots for re-distribution
	    surplus in votes + transfers
	    Election.method = Plurality implies #surplus = 0 and #transfers = 0
    	0 < #transfers implies Election.method = STV

     // Losers excluded but above threshold
    	(outcome = EarlyLoser or  
      outcome = EarlyLoserNonTransferable) iff 
		     (this in Scenario.eliminated and 
       not (#votes + #transfers < Scenario.threshold))

    	// All non-sore losers are at or above the threshold
     outcome = TiedLoser implies Scenario.threshold <= #votes + #transfers
     outcome = Loser implies Scenario.threshold <= #votes + #transfers
     outcome = EarlyLoser implies Scenario.threshold <= #votes + #transfers
     outcome = EarlyLoserNonTransferable implies 
       Scenario.threshold <= #votes + #transfers
     
    	// Plurality outcomes; 2 winning-outcomes and 4 losing-outcomes
    	Election.method = Plurality implies
		   (outcome = Loser or outcome = SoreLoser or outcome = Winner or 
		    outcome = TiedWinner or outcome = TiedLoser or outcome = TiedSoreLoser)

    	// PR-STV Winner has at least a quota of first preference votes
    	(Election.method = STV and outcome = Winner) implies 
       Scenario.quota = #votes
     (outcome = SurplusWinner or outcome = WinnerNonTransferable) implies 
       Scenario.quota < #votes

     // Quota Winner has a least a quota of votes after transfers
	    outcome = QuotaWinner implies
	      Scenario.quota = #votes + #transfers
     (outcome = AboveQuotaWinner or outcome = QuotaWinnerNonTransferable) 
       implies
	      Scenario.quota < #votes + #transfers

     // Quota Winner does not have a quota of first preference votes
	    (outcome = QuotaWinner or outcome = AboveQuotaWinner or 
       outcome = QuotaWinnerNonTransferable) implies
		     not Scenario.quota <= #votes

     // Compromise winners do not have a quota of votes
	    outcome = CompromiseWinner  implies
		     not (Scenario.quota <= #votes + #transfers)

    // STV Tied Winners have less than a quota of votes
	   (Election.method = STV and outcome = TiedWinner) implies
		     not (Scenario.quota <= #votes + #transfers)

    // Sore Losers have less votes than the threshold
	   (outcome = SoreLoser or outcome = EarlySoreLoserNonTransferable or
     outcome = EarlySoreLoser or outcome = EarlySoreLoserNonTransferable) implies 
		    #votes + #transfers < Scenario.threshold

    // Tied Sore Losers have less votes than the threshold
	   outcome = TiedSoreLoser implies 
		    #votes + #transfers < Scenario.threshold

    // Size of surplus for each STV Winner and Quota Winner
	   (outcome = SurplusWinner or outcome = WinnerNonTransferable) 
      implies ((#surplus = #votes - Scenario.quota) and #transfers = 0)
    (outcome = AboveQuotaWinner or outcome = QuotaWinnerNonTransferable) 
      implies (#surplus = #votes + #transfers - Scenario.quota)
    (outcome = Winner and Election.method = STV) implies
       (Scenario.quota + #surplus = #votes) and #transfers = 0
    	(outcome = QuotaWinner or outcome = AboveQuotaWinner or
      outcome = QuotaWinnerNonTransferable) implies surplus in transfers 
    	(outcome = QuotaWinner or outcome = AboveQuotaWinner or
      outcome = QuotaWinnerNonTransferable) implies 
		    Scenario.quota + #surplus = #votes + #transfers

     // Existance of surplus ballots
    	0 < #surplus implies (outcome = SurplusWinner or outcome = AboveQuotaWinner or
						outcome = WinnerNonTransferable or outcome = QuotaWinnerNonTransferable)
}

-- A digital or paper artifact which accurately records the intentions of the voter
sig Ballot {
  assignees: 		set Candidate,  -- Candidates to which this ballot has been assigned
  preferences: 	seq Candidate  -- Ranking of candidates
} {
	 assignees in preferences.elems
  not preferences.hasDups
	 preferences.first in assignees
	 Election.method = Plurality implies #preferences <= 1
  0 <= #preferences
  // First preference
  all c: Candidate | preferences.first = c iff this in c.votes
  // Second and subsequent preferences
  all disj donor,receiver: Candidate |
		  (donor + receiver in assignees and
		  this in receiver.transfers and this in donor.surplus) implies 
		  (preferences.idxOf[donor] < preferences.idxOf[receiver] and
		  receiver in preferences.rest.elems)
  // All ballot transfers are associated with the last candidate to receive the transfer
	 all disj c,d: Candidate | this in c.transfers implies c in assignees and 
		  (d not in assignees or preferences.idxOf[d] < preferences.idxOf[c])
  // Transfers to next continuing candidate
	 all disj skipped, receiving: Candidate | 
		  preferences.idxOf[skipped] < preferences.idxOf[receiving] and
		  receiving in assignees and (not skipped in assignees) implies
		  (skipped in Scenario.eliminated or skipped.outcome = SurplusWinner or 
		  skipped.outcome = AboveQuotaWinner or skipped.outcome = WinnerNonTransferable or
    skipped.outcome = QuotaWinnerNonTransferable or skipped.outcome = Winner or
    skipped.outcome = QuotaWinner)
}

-- An election result
one sig Scenario {
  losers: 				set Candidate,
  winners: 			set Candidate,
	 eliminated: set Candidate, -- Early and Sore Losers under STV rules
	 threshold: 	Int, 					     -- Minimum number of votes for a Loser or Early Loser
	 quota: 				 Int,					      -- Minimum number of votes for a STV Winner or Quota Winner
  fullQuota:		Int					       -- Quota if all constituency seats were vacant
} {
 	all c: Candidate | c in winners + losers
 	#winners = Election.seats
 	no c: Candidate | c in losers & winners
 	0 < #losers
 	all w: Candidate | all l: Candidate | l in losers and w in winners implies 
		  (#l.votes + #l.transfers <= #w.votes + #w.transfers)
  Election.method = STV implies threshold = 1 + fullQuota.div[4]
	 eliminated in losers
  // All PR-STV losers have less votes than the quota
	 all c: Candidate | (c in losers and Election.method = STV) implies 
       #c.votes + #c.transfers < quota
    // Winners have more votes than all non-tied losers
    all disj c,d: Candidate | c in winners and 
       (d.outcome = SoreLoser or d.outcome = EarlyLoser or d.outcome = Loser or 
        d.outcome = EarlySoreLoser) implies
	   (#d.votes + #d.transfers) < (#c.votes + #c.transfers)

   // Losers have less votes than all non-tied winners
   all disj c,d: Candidate | 
	  (c.outcome = CompromiseWinner or c.outcome = QuotaWinner or c.outcome = Winner
		or c.outcome = SurplusWinner or c.outcome = AboveQuotaWinner or 
     c.outcome = WinnerNonTransferable or c.outcome = QuotaWinnerNonTransferable) and 
	  d in losers implies
	  #d.votes + #d.transfers < #c.votes + #c.transfers

   // Lowest candidate is eliminated first
	all disj c,d: Candidate | c in eliminated and d not in eliminated implies
		#c.votes + #c.transfers <= #d.votes + #d.transfers

    // A non-sore plurality loser must have received at least five percent of the total vote
	Election.method = Plurality implies threshold = 1 + BallotBox.size.div[20]

   // Winning outcomes
	  all c: Candidate | c in winners iff 
		   (c.outcome = Winner or c.outcome = QuotaWinner or 
		   c.outcome = CompromiseWinner or 
		   c.outcome = TiedWinner or c.outcome = SurplusWinner or 
		   c.outcome = AboveQuotaWinner or
     c.outcome = WinnerNonTransferable or
     c.outcome = QuotaWinnerNonTransferable)

  // Losing outcomes
	 all c: Candidate | c in losers iff
		  (c.outcome = Loser or c.outcome = EarlyLoser or c.outcome = SoreLoser or 
		  c.outcome = TiedLoser or c.outcome = EarlySoreLoser or 
    c.outcome = TiedSoreLoser or
    c.outcome = EarlySoreLoserNonTransferable or 
    c.outcome = EarlyLoserNonTransferable)

    // STV election quotas
    Election.method = STV implies quota = 1 + BallotBox.size.div[Election.seats+1] and
    	fullQuota = 1 + BallotBox.size.div[Election.constituencySeats + 1]
    Election.method = Plurality implies quota = 1 and fullQuota = 1

   // All ties involve equality between at least one winner and at least one loser
    all w: Candidate | some l: Candidate | w.outcome = TiedWinner and 
	 	 (l.outcome = TiedLoser or l.outcome = TiedSoreLoser) implies
		  (#l.votes + #l.transfers = #w.votes + #w.transfers)
    all s: Candidate | some w: Candidate | w.outcome = TiedWinner and 
       (s.outcome = SoreLoser or s.outcome = TiedLoser) implies
       (#s.votes = #w.votes) or (#s.votes + #s.transfers = #w.votes + #w.transfers)

   // When there is a tied sore loser then there are no non-sore losers
   no disj a,b: Candidate | a.outcome = TiedSoreLoser and 
        (b.outcome = TiedLoser or 
         b.outcome=Loser or b.outcome=EarlyLoser or b.outcome = EarlyLoserNonTransferable)
    // For each Tied Winner there is a Tied Loser
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser)
    // Tied Winners and Tied Losers have an equal number of votes
	all disj l,w: Candidate | 
    ((l.outcome = TiedLoser or l.outcome = TiedSoreLoser) and
    w.outcome = TiedWinner) implies 
    #w.votes + #w.transfers = #l.votes + #l.transfers
    // Compromise winner must have more votes than any tied winners
	all disj c,t: Candidate | (c.outcome = CompromiseWinner and 
  t.outcome = TiedWinner) 
		implies
		#t.votes + #t.transfers < #c.votes + #c.transfers
    // Winners have more votes than non-tied losers
	all w,l: Candidate | w.outcome = Winner and 
      (l.outcome = Loser or l.outcome = EarlyLoser or l.outcome = SoreLoser or
       l.outcome = EarlyLoserNonTransferable or l.outcome = EarlySoreLoser or
       l.outcome = EarlySoreLoserNonTransferable) 
       implies 
     ((#l.votes < #w.votes) or (#l.votes + #l.transfers < #w.votes + #w.transfers))
    // For each Tied Loser there is at least one Tied Winner
   all c: Candidate | some w: Candidate |
   (c.outcome = TiedLoser or c.outcome = TiedSoreLoser) 
		implies w.outcome = TiedWinner
}

-- The Ballot Box
one sig BallotBox {
  spoiltBallots:		  set Ballot,		-- empty ballots excluded from count
  nonTransferables: set Ballot,		-- ballots for which preferences are exhausted
  size:					        Int 			      -- number of unspolit ballots
}
{
  no b: Ballot | b in spoiltBallots and b in nonTransferables
  size = #Ballot - #spoiltBallots
	 all b: Ballot | b in spoiltBallots iff #b.preferences = 0
  // All non-transferable ballots belong to an non-transferable surplus
  all b: Ballot | some c: Candidate | b in nonTransferables implies 
    b in c.wasted
}

-- An Electoral Constituency
one sig Election {
  seats: 				        Int,		 -- number of seats to be filled in this election
  constituencySeats:	Int,		 -- full number of seats in this constituency
  method: 				       Method	-- type of election; PR-STV or plurality
}
{
 	0 < seats and seats <= constituencySeats
 	seats < #Candidate
  method = Plurality or method = STV
}
   
-- Version Control for changes to model 
one sig Version {
   year, month, day: Int
} {
  year = 11
  month = 03
  day = 14
}
