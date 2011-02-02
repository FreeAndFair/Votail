-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Voting

open util/integer

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API

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
	Election.method = Plurality implies #preferences = 1
    0 < #preferences
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
	eliminated: 		set Candidate, 		-- Early and Sore Losers under STV rules
	threshold: 		Int, 						-- Minimum number of votes for a Loser or Early Loser
	quota: 				Int						-- Minimum number of votes for a STV Winner or Quota Winner
}
{
 	winners + losers = Election.candidates
 	#winners = Election.seats
 	no c: Candidate | c in losers & winners
 	0 < #losers
 	all w: Candidate | all l: Candidate | l in losers and w in winners implies 
		(#l.votes + #l.transfers <= #w.votes + #w.transfers)
    Election.method = STV implies threshold = 1 + quota.div[4]
	eliminated in losers
    // All PR-STV losers have less votes than the quota
	all c: Candidate | c in losers implies Election.method = Plurality 
       or #c.votes + #c.transfers < quota
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
}

-- An Election Constituency
one sig Election {
  candidates: 		set Candidate,
  seats: 				Int,
  method: 			Method,
  ballots:				Int -- number of ballots counted
}
{
 	0 < seats
 	seats < #candidates
 	all c: Candidate | c in candidates
    ballots = #Ballot
    method = STV implies Scenario.quota = 1 + ballots.div[seats+1]
    method = Plurality implies Scenario.quota = 1
  all c: Candidate | method = Plurality implies
		(c.outcome = Loser or c.outcome = SoreLoser or c.outcome = Winner or 
		c.outcome = TiedWinner or c.outcome = TiedLoser or c.outcome = TiedSoreLoser)
  --winnerSTV {
	all c: Candidate | (method = STV and c.outcome = Winner) implies 
       Scenario.quota <= #c.votes
  --transferWinnerWithQuota {
	all c: Candidate | c.outcome = QuotaWinner implies
	   Scenario.quota <= #c.votes + #c.transfers
  --transferWinnerNotFirst {
	all c: Candidate |  c.outcome = QuotaWinner implies
		not Scenario.quota <= #c.votes
  --closeWinner {
	all c: Candidate | c.outcome = CompromiseWinner  implies
		not (Scenario.quota <= #c.votes + #c.transfers)
  --tiedWinner {
	all c: Candidate | c.outcome = TiedWinner implies
		not (Scenario.quota <= #c.votes + #c.transfers) or method = Plurality
  --soreLoser {
	all c: Candidate | c.outcome = SoreLoser implies 
		#c.votes + #c.transfers < Scenario.threshold
  --tiedSoreLoser {
	all c: Candidate | c.outcome = TiedSoreLoser implies 
		#c.votes + #c.transfers < Scenario.threshold
  --winners {
	all c: Candidate | c in Scenario.winners iff 
		(c.outcome = Winner or c.outcome = QuotaWinner or c.outcome = CompromiseWinner or 
		c.outcome = TiedWinner)
  --losers {
	all c: Candidate | c in Scenario.losers iff
		(c.outcome = Loser or c.outcome = EarlyLoser or c.outcome = SoreLoser or 
		c.outcome = TiedLoser or c.outcome = TiedEarlyLoser or c.outcome = TiedSoreLoser)
-- sizeOfSurplus {
	all c: Candidate | (c in Scenario.winners and method = STV and 0 < #c.surplus) implies 
		(#c.surplus = #c.votes + #c.transfers - Scenario.quota)
-- pluralityWinner {
	all disj a, b: Candidate | (method = Plurality and seats = 1 and
		a.outcome = Winner) implies #b.votes <= #a.votes
// All ties involve equality between at least one winner and at least one loser on either original votes or
// on transfers plus original votes
   all w: Candidate | some l: Candidate | w.outcome = TiedWinner and 
	 	(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies
		(#l.votes = #w.votes) or (#l.votes + #l.transfers = #w.votes + #w.transfers)
  all s: Candidate | some w: Candidate | w.outcome = TiedWinner and 
       (s.outcome = SoreLoser or s.outcome = TiedLoser or s.outcome = TiedEarlyLoser) implies
       (#s.votes = #w.votes) or (#s.votes + #s.transfers = #w.votes + #w.transfers)
// When there is a tied sore loser then there are no non-sore losers
   no disj a,b: Candidate | a.outcome = TiedSoreLoser and 
        (b.outcome = TiedLoser or b.outcome = TiedEarlyLoser or 
         b.outcome=Loser or b.outcome=EarlyLoser)
-- tieBreaker {
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser)
-- validTieBreaker {
	all l: Candidate |
      (l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies 
      some w: Candidate |  w.outcome = TiedWinner
-- equalTieBreaker {
	all disj l,w: Candidate | 
    ((l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) and
    w.outcome = TiedWinner) implies #w.votes + #w.transfers = #l.votes + #l.transfers
// Compromise winner must have more votes than any tied winners
	all disj c,t: Candidate | (c.outcome = CompromiseWinner and t.outcome = TiedWinner) implies
		#t.votes + #t.transfers < #c.votes + #c.transfers
// Tied Winners and Tied Losers have an equal number of votes
	all disj a,b: Candidate | a.outcome = TiedWinner and 
        (b.outcome = TiedLoser or b.outcome = TiedEarlyLoser or b.outcome = TiedSoreLoser) implies
		#a.votes + #a.transfers = #b.votes + #b.transfers
// Winners have more votes than non-tied losers
	all w,l: Candidate | w.outcome = Winner and 
      (l.outcome = Loser or l.outcome = EarlyLoser or l.outcome = SoreLoser) implies 
     ((#l.votes < #w.votes) or (#l.votes + #l.transfers < #w.votes + #w.transfers))
}

-- Version Control for changes to model
one sig Version {
   year, month, day: Int
} {
  year = 11
  month = 02
  day = 02
  -- Dermot Cochran 2011-02-02
}
