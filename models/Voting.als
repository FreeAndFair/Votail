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
		((#l.votes + #l.transfers <= #w.votes + #w.transfers) and (#l.votes <= #w.votes))
    threshold = 1 + quota.div[4]
	Election.method = Plurality implies #eliminated = 0
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
  ballots:			Int -- number of ballots cast
}
{
 	0 < seats
 	seats < #candidates
 	all c: Candidate | c in candidates
    ballots = #Ballot
    Scenario.quota = 1 + ballots.div[seats+1]
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
	all c: Candidate | (Election.method = STV and c.outcome = QuotaWinner) implies
	   Scenario.quota <= #c.votes + #c.transfers
}

fact transferWinnerNotFirst {
	all c: Candidate |  (Election.method = STV and c.outcome = QuotaWinner) implies
		not Scenario.quota <= #c.votes
}

fact closeWinner {
	all c: Candidate | (c.outcome = CompromiseWinner or c.outcome = TiedWinner) implies
		not (Scenario.quota <= #c.votes + #c.transfers) or Election.method = Plurality
}

fact soreLoser {
	all c: Candidate | (c.outcome = SoreLoser or c.outcome = TiedSoreLoser) implies 
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
	all l: Candidate | some w: Candidate | 
    (l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser) implies 
    w.outcome = TiedWinner and #w.votes + #w.transfers = #l.votes + #l.transfers
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
	 #d.votes + #d.transfers < #c.votes + #c.transfers
}

-- Basic Lemmas
assert honestCount {
	  all c: Candidate | all b: Ballot | b in c.votes + c.transfers implies c in b.assignees
}
check honestCount for 15 but 6 int

assert atLeastOneLoser {
	0 < #Scenario.losers
}
check atLeastOneLoser for 15 but 6 int

assert atLeastOneWinner {
	0 < #Scenario.winners
}
check atLeastOneWinner for 14 but 6 int

assert plurality {
	all c: Candidate | all b: Ballot | b in c.votes and 
		Election.method = Plurality implies c in b.preferences.first
}
check plurality for 18 but 6 int

assert pluralityNoTransfers {
  all c: Candidate | Election.method = Plurality implies 0 = #c.transfers
}
check pluralityNoTransfers for 13 but 7 int

assert wellFormedTieBreaker {
	some w,l : Candidate | (w in Scenario.winners and l in Scenario.losers and 
		#w.votes = #l.votes and #w.transfers = #l.transfers) implies 
		w.outcome = TiedWinner and 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome=TiedEarlyLoser)
}
check wellFormedTieBreaker for 18 but 6 int

assert validSurplus {
	all c: Candidate | 0 < #c.surplus implies (c.outcome = Winner or c.outcome = QuotaWinner or 
		c in Scenario.eliminated)
}
check validSurplus for 16 but 6 int

-- Advanced Lemmas
// Equal losers are tied
assert equalityofTiedWinnersAndLosers {
	all disj w,l: Candidate | w in Scenario.winners and l in Scenario.losers and 
		#w.votes + #w.transfers = #l.votes + #l.transfers implies
			w.outcome = TiedWinner and 
			(l.outcome = TiedLoser or l.outcome = TiedEarlyLoser or l.outcome = TiedSoreLoser)
}
check equalityofTiedWinnersAndLosers for 13 but 7 int

// No lost votes during counting
assert accounting {
	all b: Ballot | some c: Candidate | b in c.votes and c in b.assignees
}
check accounting for 16 but 6 int

// Cannot have tie breaker with both tied sore loser and non-sore loser
assert tiedWinnerLoserTiedSoreLoser {
	no disj c,w,l: Candidate | c.outcome = TiedSoreLoser and
	   w.outcome = TiedWinner and (l.outcome = Loser or l.outcome = TiedLoser)
}
check tiedWinnerLoserTiedSoreLoser for 6 int

// Compromise winner must have at least one vote
assert validCompromise {
	all c: Candidate | c.outcome = CompromiseWinner implies 0 < #c.votes + #c.transfers
}
check validCompromise for 6 int

// Quota winner needs transfers
assert quotaWinnerNeedsTransfers {
  all c: Candidate | c.outcome = QuotaWinner implies 0 < #c.transfers
}
check quotaWinnerNeedsTransfers for 7 int

// Sore losers below threshold
assert soreLoserBelowThreshold {
  all c: Candidate | c.outcome = SoreLoser implies not (Scenario.threshold <= #c.votes + #c.transfers)
}
check soreLoserBelowThreshold for 10 but 6 int

// Possible outcomes when under the threshold
assert underThresholdOutcomes {
  all c: Candidate | (#c.votes + #c.transfers < Scenario.threshold) implies
     (c.outcome = SoreLoser or c.outcome = TiedSoreLoser or c.outcome = TiedWinner or
     c.outcome = CompromiseWinner or (Election.method = Plurality and c.outcome = Winner))
}
check underThresholdOutcomes for 10 but 6 int

// Tied Winners have equality of votes and transfers
assert tiedWinnerEquality {
  all a,b: Candidate | (a.outcome = TiedWinner and b.outcome = TiedWinner) implies
	#a.votes + #a.transfers = #b.votes + #b.transfers
}
check tiedWinnerEquality for 10 but 6 int

// Non-negative threshold and quota
assert nonNegativeThresholdAndQuota {
	0 <= Scenario.threshold and Scenario.threshold <= Scenario.quota
}
check nonNegativeThresholdAndQuota for 6 but 6 int

-- Sample scenarios
pred TwoCandidatePlurality { 
	Election.method = Plurality
	Election.seats = 1
	#Election.candidates = 2
}
run TwoCandidatePlurality for 10 but 2 Ballot, 6 int

pred PluralityTiedWinner {
	Election.method = Plurality
	Election.seats = 1
	some disj a,b: Candidate | a.outcome = TiedWinner and b.outcome = TiedLoser
}
run PluralityTiedWinner for 10 but 6 int

pred ThreeCandidatePlurality {
	Election.method = Plurality
	Election.seats = 1
	#Election.candidates = 3
}
run ThreeCandidatePlurality for 6 int

pred Plurality {
	Election.method = Plurality
	Election.seats = 1
	3 < #Election.candidates
}
run Plurality for 5 but 6 int

pred TenCandidatePluralityWithTwoSeats {
	Election.method = Plurality
	Election.seats = 2
	#Election.candidates = 10
}
run TenCandidatePluralityWithTwoSeats for 10 but 6 int

pred InstantRunoffVoting {
	Election.method = STV
	Election.seats = 1
	3 < #Election.candidates
}
run InstantRunoffVoting for 10 but 6 int

pred STV3 {
	Election.method = STV
	Election.seats = 3
}
run STV3 for 5 but 6 int

pred ThreeWinnersOneLoser {
    Election.method = STV
	some disj a,b,d: Candidate | a.outcome = Winner
   	  and b.outcome = QuotaWinner or b.outcome = CompromiseWinner
	  and d in Scenario.losers
}
run ThreeWinnersOneLoser for 6 but 6 int

pred LoserAndEarlyLoser {
	one d: Candidate | d.outcome = Loser
	one e: Candidate | e.outcome = EarlyLoser
}
run LoserAndEarlyLoser for 5 but 6 int

pred OneWinnerNineLosers {
	#Scenario.winners = 1
	#Scenario.losers = 9
}
run OneWinnerNineLosers for 16 but 6 int

pred ThreeWayTie {
	#Election.candidates = 3
    Election.method = Plurality
	some disj a,b,c: Candidate | a.outcome = TiedWinner and 
		b.outcome = TiedLoser and
		c.outcome = TiedLoser
}
run ThreeWayTie for 10 but 6 int

pred FiveWayTie {
	some disj a,b,c,d,e: Candidate | a.outcome = TiedWinner and
	    b.outcome = TiedLoser and
		c.outcome = TiedLoser and d.outcome = TiedLoser and e.outcome = TiedWinner
}
run FiveWayTie for 7 but 6 int

pred ScenarioLWW {
	some disj a,b,c: Candidate | a.outcome = Loser and b.outcome = Winner and 
		c.outcome = Winner
    #Election.candidates = 3
	Election.method = STV
    0 < #Ballot
}
run ScenarioLWW for 7 but 7 int

pred LongBallot {
	some b: Ballot | #b.preferences = 7
}
run LongBallot for 7 but 6 int

pred MultipleBallotsUnderSTV {
	Election.method = STV
	some disj a,b,c,d: Ballot | 1 < #a.preferences and 1 < #b.preferences 
	and 0 < #c.preferences and 0 < #d.preferences and 
        a.preferences.first = b.preferences.last
}
run MultipleBallotsUnderSTV for 10 but 6 int

pred WinnerLoserEarlyLoser {
	some a,b,c,d : Candidate | a.outcome = Winner and b.outcome = Loser and 
		c.outcome = EarlyLoser and d.outcome = SoreLoser
	Election.method = STV
}
run WinnerLoserEarlyLoser for 7 but 6 int

pred TiedScenario { 
  some disj a,b: Candidate | a.outcome = TiedLoser and b.outcome = TiedWinner
     Election.method = STV
     #Election.candidates = 2
     #Election.seats = 1
}
run TiedScenario for 7 but 6 int

pred NoTiesAndNoSoresScenarios {
  Election.method = STV
  #Election.candidates > 3
  #Ballot > 6
  no c: Candidate | c.outcome = TiedLoser or c.outcome = TiedWinner or
    c.outcome = TiedEarlyLoser or c.outcome = TiedSoreLoser or c.outcome = SoreLoser
}
run NoTiesAndNoSoresScenarios for 10 but 6 int

-- Scenario tests
pred SLW {
  some disj c0,c1,d: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  Election.method = Plurality and #Election.candidates = 3
  Scenario.threshold = 1
}
run SLW for 6 but 6 int

pred SSSLW {
  some disj c0,c1,d,e,f: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  e.outcome = SoreLoser and
  f.outcome = SoreLoser and
  Election.method = Plurality and #Election.candidates = 5
}
run SSSLW for 6 but 6 int

pred SSSSLW {
  some disj c0,c1,d,e,f,g: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  e.outcome = SoreLoser and
  f.outcome = SoreLoser and
  g.outcome = SoreLoser and
  Election.method = Plurality and #Election.candidates = 6
}
run SSSSLW for 6 but 6 int

pred LW {
  some disj c0,c1: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  Election.method = Plurality and 0 < #Ballot and #Election.candidates = 2
}
run LW for 5 but 6 int

pred LQ {
	some disj a,b: Candidate | a.outcome = Loser and b.outcome = QuotaWinner
    #Election.candidates = 2
    0 < #Ballot
}
run LQ for 10 but 6 int

pred LQQ {
	some disj a,b,c: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and
       c.outcome = QuotaWinner
    #Election.candidates = 3
    0 < #Ballot
}
run LQQ for 10 but 6 int

pred LQW {
	some disj a,b,c: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and 
		c.outcome = Winner
    #Election.candidates = 3
    0 < #Ballot
}
run LQW for 10 but 6 int

pred LQQW {
	some disj a,b,c,d: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and 
		c.outcome = Winner and d.outcome = QuotaWinner
    #Election.candidates = 4
    0 < #Ballot
}
run LQQW for 10 but 6 int

pred SLQQW {
	some disj a,b,c,d,e: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and 
		c.outcome = Winner and d.outcome = QuotaWinner and e.outcome = SoreLoser
    #Election.candidates = 5
    0 < #Ballot
}

pred SLTT {
  some disj c1,c3,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c3.outcome = Loser and 
    c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Election.candidates = 4
}
run SLTT for 13 but 7 int

pred SLLTT {
  some disj c2,c3,c4,c8,c9: Candidate | 
    c2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Election.candidates = 5
}
run SLLTT for 13 but 7 int

pred SSLTT {
  some disj c1,c2,c4,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c2.outcome = SoreLoser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Election.candidates = 5
}
run SSLTT for 13 but 7 int

pred SSLLTT {
  some disj c1,c2,c3,c4,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Election.candidates = 6
}
run SSLLTT for 13 but 7 int

pred SSLLLTT {
  some disj c0,c1,c3,c4,c5,c7,c8: Candidate | c0.outcome = SoreLoser and 
    c1.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c5.outcome = Loser and 
    c7.outcome = TiedLoser and c8.outcome = TiedLoser and 
    Election.method = Plurality and #Election.candidates = 7
}
run SSLLLTT for 20 but 7 int

pred SSSLLLLTTT {
  some disj c0,c1,c2,c3,c4,c5,c6,c7,c8,c9: Candidate | c0.outcome = SoreLoser and 
    c1.outcome = SoreLoser and c2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c5.outcome = Loser and c6.outcome = Loser and 
    c7.outcome = TiedLoser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Election.candidates = 10
}
run SSSLLLLTTT for 13 but 7 int

-- Version Control for changes to model
one sig Version {
   year, month, day: Int
} {
  year = 11
  month = 01
  day = 26
  -- Dermot Cochran 2011-01-26
}
