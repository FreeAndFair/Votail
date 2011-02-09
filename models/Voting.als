-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Voting

open util/integer

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API, but not by the analyser

/* 
	There are four winner-outcomes and six loser-outcomes:

	Winner: 						(W1) elected in the first round of counting either by quota or plurality,
	QuotaWinner: 				(W2) elected with transfers from another candidate (STV only),
	CompromiseWinner: 	(W3) elected on the last round of counting without quota (STV only),
	TiedWinner:					(W4) elected by tie breaker,
	TiedLoser:					(L1) loses only by tie breaker but reaches the threshold,
	Loser:			 				(L2) defeated on last round but reaches the minimum threshold of votes,
    TiedEarlyLoser:			(L3) reaches threshold but eliminated by tie breaker (STV only),
	EarlyLoser:					(L4) reaches threshold but is eliminated before last round (STV only),
	TiedSoreLoser:				(L5) loses only by tie breaker but does not reach threshold,
	SoreLoser: 					(L6) does not even reach the mimimum threshold of votes.
*/
enum Event {Winner, QuotaWinner, CompromiseWinner, TiedWinner, 
	TiedLoser, Loser, TiedEarlyLoser, EarlyLoser, TiedSoreLoser, SoreLoser}

enum Method {Plurality, STV}

-- An individual person standing for election
sig Candidate {
    votes: 			  set Ballot, 	-- First preference ballots assigned to this candidate
	transfers: 	      set Ballot,   -- Ballots received by transfer from another candidate
	surplus: 		  set Ballot, 	-- Ballots given to another candidate (on election or elimination)
	outcome: 		  Event	
} {
	no b: Ballot | b in votes & transfers
	all b: Ballot | b in votes + transfers implies this in b.assignees
	surplus in votes + transfers
	Election.method = Plurality implies #surplus = 0 and #transfers = 0
    0 < #transfers implies Election.method = STV
    outcome = Winner and Election.method = STV implies
       Scenario.quota + #surplus = #votes
    outcome = Winner implies #transfers = 0
    outcome = QuotaWinner implies surplus in transfers 
    outcome = QuotaWinner implies Scenario.quota + #surplus = #votes + #transfers
     all b: Ballot | b in votes implies this in b.assignees
    0 < #surplus implies (outcome = Winner or outcome = QuotaWinner)
    (outcome = EarlyLoser or outcome = TiedEarlyLoser) iff 
		(this in Scenario.eliminated and not (#votes + #transfers < Scenario.threshold))
    // All non-sore losers are above the threshold
    outcome = TiedLoser implies Scenario.threshold < #votes + #transfers
    outcome = Loser implies Scenario.threshold < #votes + #transfers
    outcome = EarlyLoser implies Scenario.threshold < #votes + #transfers
    outcome = TiedEarlyLoser implies Scenario.threshold < #votes + #transfers
    // Plurality outcomes
    Election.method = Plurality implies
		(outcome = Loser or outcome = SoreLoser or outcome = Winner or 
		outcome = TiedWinner or outcome = TiedLoser or outcome = TiedSoreLoser)
    // PR-STV Winner has at least a quota of first preference votes
    (Election.method = STV and outcome = Winner) implies 
       Scenario.quota <= #votes
    // Quota Winner has a least a quota of votes after transfers
	outcome = QuotaWinner implies
	   Scenario.quota <= #votes + #transfers
    // Quota Winner does not have a quota of first preference votes
	outcome = QuotaWinner implies
		not Scenario.quota <= #votes
    // Compromise winners do not have a quota of votes
	outcome = CompromiseWinner  implies
		not (Scenario.quota <= #votes + #transfers)
    // STV Tied Winners have less than a quota of votes
	(Election.method = STV and outcome = TiedWinner) implies
		not (Scenario.quota <= #votes + #transfers)
    // Sore Losers have less votes than the threshold
	outcome = SoreLoser implies 
		#votes + #transfers < Scenario.threshold
    // Tied Sore Losers have less votes than the threshold
	outcome = TiedSoreLoser implies 
		#votes + #transfers < Scenario.threshold
    // Size of surplus for each STV Winner and Quota Winner
	(outcome = QuotaWinner or (outcome = Winner and Election.method = STV)) implies 
		(#surplus = #votes + #transfers - Scenario.quota)
}

-- A digital or paper artifact which accurately records the intentions of the voter
sig Ballot {
  assignees: 		set Candidate,  -- Candidates to which this ballot has been assigned
  preferences: 	seq Candidate  -- Ranking of candidates
} {
	assignees in preferences.elems
    not preferences.hasDups
	preferences.elems in Election.candidates
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
		(skipped in Scenario.eliminated or skipped.outcome = Winner or 
		skipped.outcome = QuotaWinner)
}

-- An election result
one sig Scenario {
   	losers: 				set Candidate,
   	winners: 			set Candidate,
	eliminated: 		set Candidate, 	-- Early and Sore Losers under STV rules
	threshold: 		Int, 					-- Minimum number of votes for a Loser or Early Loser
	quota: 				Int,					-- Minimum number of votes for a STV Winner or Quota Winner
    fullQuota:			Int					-- Quota if all constituency seats were vacant
} {
 	winners + losers = Election.candidates
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
       (d.outcome = SoreLoser or d.outcome = EarlyLoser or d.outcome = Loser) implies
	   (#d.votes + #d.transfers) < (#c.votes + #c.transfers)
   // Losers have less votes than all non-tied winners
   all disj c,d: Candidate | 
	  (c.outcome = CompromiseWinner or c.outcome = QuotaWinner or c.outcome = Winner) and 
	  d in losers implies
	  #d.votes + #d.transfers < #c.votes + #c.transfers
   // Lowest candidate is eliminated first
	all disj c,d: Candidate | c in eliminated and d not in eliminated implies
		#c.votes + #c.transfers <= #d.votes + #d.transfers
    // A non-sore plurality loser must have received at least five percent of the total vote
	Election.method = Plurality implies threshold = 1 + Election.ballots.div[20]
    // Winning outcomes
	all c: Candidate | c in winners iff 
		(c.outcome = Winner or c.outcome = QuotaWinner or c.outcome = CompromiseWinner or 
		c.outcome = TiedWinner)
    // Losing outcomes
	all c: Candidate | c in losers iff
		(c.outcome = Loser or c.outcome = EarlyLoser or c.outcome = SoreLoser or 
		c.outcome = TiedLoser or c.outcome = TiedEarlyLoser or c.outcome = TiedSoreLoser)
}

-- An Election Constituency
one sig Election {
  candidates: 			set Candidate,
  seats: 					Int,				-- number of seats vacant in this election
  constituencySeats:	Int,				-- full number of seats in this constituency
  method: 				Method,
  spoiltBallots:			set Ballot,		-- empty ballots excluded from count
  ballots:					Int 				-- number of ballots counted
}
{
 	0 < seats and seats <= constituencySeats
 	seats < #candidates
 	all c: Candidate | c in candidates
    ballots = #Ballot - #spoiltBallots
	all b: Ballot | b in spoiltBallots iff #b.preferences = 0
    method = STV implies Scenario.quota = 1 + ballots.div[seats+1] and
    	Scenario.fullQuota = 1 + ballots.div[constituencySeats + 1]
    method = Plurality implies Scenario.quota = 1 and Scenario.fullQuota = 1
    // All ties involve equality between at least one winner and at least one loser
    all w: Candidate | some l: Candidate | w.outcome = TiedWinner and 
	 	(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies
		(#l.votes + #l.transfers = #w.votes + #w.transfers)
  all s: Candidate | some w: Candidate | w.outcome = TiedWinner and 
       (s.outcome = SoreLoser or s.outcome = TiedLoser or s.outcome = TiedEarlyLoser) implies
       (#s.votes = #w.votes) or (#s.votes + #s.transfers = #w.votes + #w.transfers)
   // When there is a tied sore loser then there are no non-sore losers
   no disj a,b: Candidate | a.outcome = TiedSoreLoser and 
        (b.outcome = TiedLoser or b.outcome = TiedEarlyLoser or 
         b.outcome=Loser or b.outcome=EarlyLoser)
    // For each Tied Winner there is a Tied Loser
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser)
    // Tied Winners and Tied Losers have an equal number of votes
	all disj l,w: Candidate | 
    ((l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) and
    w.outcome = TiedWinner) implies #w.votes + #w.transfers = #l.votes + #l.transfers
    // Compromise winner must have more votes than any tied winners
	all disj c,t: Candidate | (c.outcome = CompromiseWinner and t.outcome = TiedWinner) 
		implies
		#t.votes + #t.transfers < #c.votes + #c.transfers
    // Winners have more votes than non-tied losers
	all w,l: Candidate | w.outcome = Winner and 
      (l.outcome = Loser or l.outcome = EarlyLoser or l.outcome = SoreLoser) implies 
     ((#l.votes < #w.votes) or (#l.votes + #l.transfers < #w.votes + #w.transfers))
    // For each Tied Loser there is at least one Tied Winner
   all c: Candidate | some w: Candidate |
   (c.outcome = TiedLoser or c.outcome = TiedSoreLoser or c.outcome = TiedEarlyLoser) 
		implies 
        w.outcome = TiedWinner
}

-- Version Control for changes to model 
one sig Version {
   year, month, day: Int
} {
  year = 11
  month = 02
  day = 09
  -- Dermot Cochran 2011-02-09
}
