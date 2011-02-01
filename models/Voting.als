-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Voting

open util/integer

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
	all c: Candidate | c in losers implies Election.method = Plurality 
       or #c.votes + #c.transfers < quota
}

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

-- An Election Constituency
one sig Election {
  candidates: 	set Candidate,
  seats: 				Int,
  method: 			Method,
  ballots:			Int -- number of unspoilt ballots cast
}
{
 	0 < seats
 	seats < #candidates
 	all c: Candidate | c in candidates
    ballots = #Ballot
    method = STV implies Scenario.quota = 1 + ballots.div[seats+1]
}

-- Independent (or Fundamental) Axioms
fact surplus {
  all c: Candidate | (c.outcome = Winner and Election.method = STV) implies
     Scenario.quota + #c.surplus = #c.votes 
}

fact winnersWithoutTransfers {
  all c: Candidate | (c.outcome = Winner and Election.method = STV) implies #c.transfers = 0 
}

fact surplusFromTransfers {
  all c: Candidate | c.outcome = QuotaWinner implies ((surplus in transfers) and 
     ((Scenario.quota + #c.surplus) = (#c.votes + #c.transfers)))
}

fact integrity {
  all c: Candidate | all b: Ballot | b in c.votes implies c in b.assignees
}

fact pluralityEvents {
	all c: Candidate | Election.method = Plurality implies
		(c.outcome = Loser or c.outcome = SoreLoser or c.outcome = Winner or 
		c.outcome = TiedWinner or c.outcome = TiedLoser)
}

fact winnerSTV {
	all c: Candidate | (Election.method = STV and c.outcome = Winner) implies 
       Scenario.quota <= #c.votes
}

fact transferWinnerWithQuota {
	all c: Candidate | c.outcome = QuotaWinner implies
	   Scenario.quota <= #c.votes + #c.transfers
}

fact transferWinnerNotFirst {
	all c: Candidate |  c.outcome = QuotaWinner implies
		not Scenario.quota <= #c.votes
}

fact closeWinner {
	all c: Candidate | c.outcome = CompromiseWinner  implies
		not (Scenario.quota <= #c.votes + #c.transfers)
}

fact tiedWinner {
	all c: Candidate | c.outcome = TiedWinner implies
		not (Scenario.quota <= #c.votes + #c.transfers) or Election.method = Plurality
}

fact soreLoser {
	all c: Candidate | c.outcome = SoreLoser implies 
		#c.votes + #c.transfers < Scenario.threshold
}

fact tiedSoreLoser {
	all c: Candidate | c.outcome = TiedSoreLoser implies 
		#c.votes + #c.transfers < Scenario.threshold
}

fact loser {
	all c: Candidate | (c.outcome = Loser or c.outcome = TiedLoser) 
        implies (c in Scenario.losers and c not in Scenario.eliminated)
}

fact earlyLoser {
	all c: Candidate | (c.outcome = EarlyLoser or c.outcome = TiedEarlyLoser) iff 
		(c in Scenario.eliminated and not (#c.votes + #c.transfers < Scenario.threshold))
}

fact winners {
	all c: Candidate | c in Scenario.winners iff 
		(c.outcome = Winner or c.outcome = QuotaWinner or c.outcome = CompromiseWinner or 
		c.outcome = TiedWinner)
}

fact losers {
	all c: Candidate | c in Scenario.losers iff
		(c.outcome = Loser or c.outcome = EarlyLoser or c.outcome = SoreLoser or 
		c.outcome = TiedLoser or c.outcome = TiedEarlyLoser or c.outcome = TiedSoreLoser)
}

-- Non-Independent Axioms for Ballot Integrity
fact transfers {
	all c: Candidate | 0 < #c.transfers implies Election.method = STV
}

fact onlyWinnersAndQuotaWinnersHaveSurplus {
	all c: Candidate | 0 < #c.surplus implies 
		(c.outcome = Winner or c.outcome = QuotaWinner)
}

fact winnersNeedNoTransfers {
		all c: Candidate | c.outcome = Winner implies 0 = #c.transfers
}

fact firstPreference {
	all b: Ballot | all c: Candidate | b.preferences.first = c iff b in c.votes
}

fact sizeOfSurplus {
	all c: Candidate | (c in Scenario.winners and Election.method = STV and 0 < #c.surplus) implies 
		(#c.surplus = #c.votes + #c.transfers - Scenario.quota)
}

fact transferToNextPreference {
	all b: Ballot | all disj donor,receiver: Candidate |
		(donor + receiver in b.assignees and
		b in receiver.transfers and b in donor.surplus) implies 
		(b.preferences.idxOf[donor] < b.preferences.idxOf[receiver] and
		receiver in b.preferences.rest.elems)
}

fact pluralityWinner {
	all disj a, b: Candidate | (Election.method = Plurality and Election.seats = 1 and
		a.outcome = Winner) implies #b.votes <= #a.votes
}

fact transferToNextContinuingCandidate {
	all disj skipped, receiving: Candidate | all b: Ballot |
		b.preferences.idxOf[skipped] < b.preferences.idxOf[receiving] and
		receiving in b.assignees and (not skipped in b.assignees) implies
		(skipped in Scenario.eliminated or skipped.outcome = Winner or 
		skipped.outcome = QuotaWinner)
}

// All ballot transfers are associated with the last candidate to receive the transfer
fact ownership {
	all disj c,d: Candidate | all b: Ballot | b in c.transfers implies c in b.assignees and 
		(d not in b.assignees or b.preferences.idxOf[d] < b.preferences.idxOf[c])
}

// Lowest candidate is eliminated first
fact lowestElimination {
	all disj c,d: Candidate | c in Scenario.eliminated and d not in Scenario.eliminated implies
		#c.votes + #c.transfers <= #d.votes + #d.transfers
}

// All ties involve equality between at least one winner and at least one loser on either original votes or
// on transfers plus original votes
fact equalityOfTiedWinner {
   all w: Candidate | some l: Candidate | w.outcome = TiedWinner and 
	 	(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies
		(#l.votes = #w.votes) or (#l.votes + #l.transfers = #w.votes + #w.transfers)
}

fact equalityOfTiedLosers {
  all s: Candidate | some w: Candidate | w.outcome = TiedWinner and 
       (s.outcome = SoreLoser or s.outcome = TiedLoser or s.outcome = TiedEarlyLoser) implies
       (#s.votes = #w.votes) or (#s.votes + #s.transfers = #w.votes + #w.transfers)
}

// An ordinary plurality loser must have received at least five percent of the total vote
fact minimumThreshold {
	Election.method = Plurality implies 1 + Election.ballots.div[20] = Scenario.threshold
}

-- Scenario Validity Axioms
// When there is a tied sore loser then there are no non-sore losers
fact typeOfTiedLoser {
   no disj a,b: Candidate | a.outcome = TiedSoreLoser and 
        (b.outcome = TiedLoser or b.outcome = TiedEarlyLoser or 
         b.outcome=Loser or b.outcome=EarlyLoser)
}

fact tieBreaker {
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser)
}

fact validTieBreaker {
	all l: Candidate |
      (l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies 
      some w: Candidate |  w.outcome = TiedWinner
}

fact equalTieBreaker {
	all disj l,w: Candidate | 
    ((l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) and
    w.outcome = TiedWinner) implies #w.votes + #w.transfers = #l.votes + #l.transfers
}

// Compromise winner must have more votes than any tied winners
fact compromiseNotTied {
	all disj c,t: Candidate | (c.outcome = CompromiseWinner and t.outcome = TiedWinner) implies
		#t.votes + #t.transfers < #c.votes + #c.transfers
}



// Highest winner has a quota
fact highestWinners {
   all c: Candidate | Election.method = STV and c.outcome = Winner implies 
		Scenario.quota <= #c.votes + #c.transfers
}

// Tied Winners and Tied Losers have an equal number of votes
fact equalTies {
	all disj a,b: Candidate | a.outcome = TiedWinner and 
        (b.outcome = TiedLoser or b.outcome = TiedEarlyLoser or b.outcome = TiedSoreLoser) implies
		#a.votes + #a.transfers = #b.votes + #b.transfers
}

// Winners have more votes than non-tied losers
fact winnersHaveVotes {
	all w,l: Candidate | w.outcome = Winner and 
      (l.outcome = Loser or l.outcome = EarlyLoser or l.outcome = SoreLoser) implies 
     ((#l.votes < #w.votes) or (#l.votes + #l.transfers < #w.votes + #w.transfers))
}

// All non-sore losers are above the threshold
fact losersAboveThreshold {
  all c: Candidate | c.outcome = Loser implies Scenario.threshold < #c.votes + #c.transfers
}

fact earlyLosersAboveThreshold {
  all c: Candidate | c.outcome = EarlyLoser implies Scenario.threshold < #c.votes + #c.transfers
}

fact tiedLosersAboveThreshold {
  all c: Candidate | c.outcome = TiedLoser implies Scenario.threshold < #c.votes + #c.transfers
}

fact tiedEarlyLosersAboveThreshold {
  all c: Candidate | c.outcome = TiedEarlyLoser implies Scenario.threshold < #c.votes + #c.transfers
}

fact nonTiedWinnerHigherThanAllLosers {
  all disj c,d: Candidate | 
	(c.outcome = CompromiseWinner or c.outcome = QuotaWinner or c.outcome = Winner) and 
	d in Scenario.losers implies
	 #d.votes + #d.transfers < #c.votes + #c.transfers
}

fact winnerHigherThanAllNonTiedLosers {
  all disj c,d: Candidate | c in Scenario.winners and 
     (d.outcome = SoreLoser or d.outcome = EarlyLoser or d.outcome = Loser) implies
	 (#d.votes + #d.transfers) < (#c.votes + #c.transfers)
}

fact nonNegativeQuota {
  0 <= Scenario.quota
}

-- Version Control for changes to model
one sig Version {
   year, month, day: Int
} {
  year = 11
  month = 01
  day = 26
  -- Dermot Cochran 2011-01-26
}
