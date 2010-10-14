-- Dermot Cochran, 2010, IT University of Copenhagen
-- http://www.kindsoftware.com
-- See ICSE 2011 paper 'Exploring the Universe of Ballot Boxes'

module Scenario

open util/integer
open voting

-- An election result
sig Scenario {
   	losers: 					set Outcome,
   	winners: 				set Outcome
}
{
 	winners + losers = Election.candidates
 	#winners = Election.seats
 	no c: Candidate | c in losers & winners
 	0 < #losers
 	all w: Candidate | all l: Candidate | l in losers and w in winners implies 
		#l.votes + #l.transfers <= #w.votes + #w.transfers
	0 <= threshold
	threshold < quota
	Election.method = Plurality implies #eliminated = 0
	eliminated in losers
	all c: Candidate | c in losers implies Election.method = Plurality or #c.votes + #c.transfers < quota
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
	SoreLoser: 					(L6) does not even reach the mimimum threshold of votes
*/
enum Event {Winner, QuotaWinner, CompromiseWinner, TiedWinner, 
	TiedLoser, Loser, TiedEarlyLoser, EarlyLoser, TiedSoreLoser, SoreLoser}

enum Method {Plurality, STV}

-- A collection of ballots cast in an election
one sig BallotBox {
	ballots: set Ballot
} {
    0 < #ballots
	all b: Ballot | b in ballots
}

-- An Election Constituency
one sig Election {
  candidates: 	set Candidate,
  seats: 				Int,
  method: 			Method
}
{
 	0 < seats
 	seats < #candidates
 	all c: Candidate | c in candidates
}

-- Independent Axioms
fact integrity {
  all c: Candidate | all b: Ballot | b in c.votes implies c in b.assignees
}

fact pluralityEvents {
	all c: Candidate | Election.method = Plurality implies
		(c.outcome = Loser or c.outcome = SoreLoser or c.outcome = Winner or 
		c.outcome = TiedWinner or c.outcome = TiedLoser)
}

fact wellFormedQuota {
	Election.method = STV implies 
		#BallotBox.ballots < Scenario.quota.mul[Election.seats+1] and
		Scenario.quota.mul[Election.seats] <= #BallotBox.ballots 
}

fact wellFormedThreshold {
	#BallotBox.ballots <= Scenario.threshold.mul[20] or 
	Election.method = STV implies Scenario.quota <= Scenario.threshold.mul[4]
}

fact noStrayBallots {
	all b: Ballot | b in BallotBox.ballots
}

fact winnerSTV {
	all c: Candidate | Election.method = STV implies (
		c.outcome = Winner iff Scenario.quota <= #c.votes)
}

fact transferWinner {
	all c: Candidate | c.outcome = QuotaWinner iff 
		#c.votes < Scenario.quota and Scenario.quota <= #c.votes + #c.transfers 
}

fact closeWinner {
	all c: Candidate | c.outcome = CompromiseWinner or c.outcome = TiedWinner iff 
		c in Scenario.winners and #c.votes + #c.transfers < Scenario.quota
}

fact soreLoser {
	all c: Candidate | (c.outcome = SoreLoser or c.outcome = TiedSoreLoser) iff 
		#c.votes + #c.transfers < Scenario.threshold
}

fact loser {
	all c: Candidate | (c.outcome = Loser or c.outcome = TiedLoser or c.outcome = TiedSoreLoser) iff 
		c in Scenario.losers - Scenario.eliminated
}

fact earlyLoser {
	all c: Candidate | c.outcome = EarlyLoser or c.outcome = TiedEarlyLoser iff 
		(c in Scenario.losers & Scenario.eliminated and Scenario.threshold <= #c.votes + #c.transfers)
}

fact winners {
	all c: Candidate | c in Scenario.winners iff 
		c.outcome = Winner or c.outcome = QuotaWinner or c.outcome = CompromiseWinner or 
		c.outcome = TiedWinner
}

fact losers {
	all c: Candidate | c in Scenario.losers iff
		(c.outcome = Loser or c.outcome = EarlyLoser or c.outcome = SoreLoser or 
		c.outcome = TiedLoser or c.outcome = TiedEarlyLoser or c.outcome = TiedSoreLoser)
}

-- Non-Independent Axioms
fact transfers {
	all c: Candidate | 0 < #c.transfers implies Election.method = STV
}

fact onlyWinnersAndQuotaWinnersHaveSurplus {
	all c: Candidate | 0 < #c.surplus implies 
		c.outcome = Winner or c.outcome = QuotaWinner
}

fact winnersNeedNoTransfers {
		all c: Candidate | c.outcome = Winner implies 0 = #c.transfers
}

fact firstPreference {
	all b: Ballot | all c: Candidate | b.preferences.first = c iff b in c.votes
}

fact sizeOfSurplus {
	all c: Candidate | (c in Scenario.winners and Election.method = STV and 0 < #c.surplus) implies 
		#c.surplus = #c.votes + #c.transfers - Scenario.quota
}

fact tieBreaker {
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser)
}

fact transferToNextPreference {
	all b: Ballot | all disj donor,receiver: Candidate |
		(donor + receiver in b.assignees and
		b in receiver.transfers and b in donor.surplus implies 
		b.preferences.idxOf[donor] < b.preferences.idxOf[receiver] and
		receiver in b.preferences.rest.elems)
}

fact pluralityWinner {
	all disj a, b: Candidate | (Election.method = Plurality and Election.seats = 1) and
		a.outcome = Winner implies #b.votes <= #a.votes
}

fact validTieBreaker {
	all l: Candidate | some w: Candidate | l.outcome = TiedLoser implies w.outcome = TiedWinner
}

fact transferToNextContinuingCandidate {
	all disj skipped, receiving: Candidate | all b: Ballot |
		b.preferences.idxOf[skipped] < b.preferences.idxOf[receiving] and
		receiving in b.assignees and (not skipped in b.assignees) implies
		(skipped in Scenario.eliminated or skipped.outcome = Winner or 
		skipped.outcome = QuotaWinner)
}

// All ballots transfers are associated with the last candidate to receive the transfer
fact ownership {
	all disj c,d: Candidate | all b: Ballot | b in c.transfers implies c in b.assignees and 
		(d not in b.assignees or b.preferences.idxOf[d] < b.preferences.idxOf[c])
}

// Lowest candidate is eliminated first
fact lowestElimination {
	all disj c,d: Candidate | c in Scenario.eliminated and d not in Scenario.eliminated implies
		#c.votes + #c.transfers <= #d.votes + #d.transfers
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

assert wellFormednessOfBallots {
	all b: Ballot | b.assignees in Election.candidates
}
check wellFormednessOfBallots for 18 but 6 int

assert wellFormedBallotBox {
		#BallotBox.ballots = sum (#Election.candidates.votes) 
}
check wellFormedBallotBox for 14 but 6 int

assert plurality {
	all c: Candidate | all b: Ballot | b in c.votes and 
		Election.method = Plurality implies c in b.preferences.first
}
check plurality for 18 but 6 int

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
// No lost votes during counting
assert accounting {
	all b: Ballot | one c: Candidate | b in c.votes and c in b.assignees
}
check accounting for 16 but 6 int

// No ballots created or destroyed during counting
assert immutability {
	all c: Candidate | c.votes + c.transfers in BallotBox.ballots and c.surplus in BallotBox.ballots
}
check immutability for 16 but 6 int

-- 18 Different Scenarios
pred TwoCandidatePlurality { 
	Election.method = Plurality
	Election.seats = 1
	#Election.candidates = 2
}
run TwoCandidatePlurality for 10 but 1 Ballot, 6 int

pred PluralityTiedWinner {
	Election.method = Plurality
	Election.seats = 1
	some disj a,b: Candidate | a.outcome = TiedWinner and b.outcome = TiedLoser
}
run PluralityTiedWinner for 10 but 2 Ballot, 6 int

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
	some a: Candidate | a.outcome = Winner
   	some b: Candidate | b.outcome = QuotaWinner
	some c: Candidate | c.outcome = CompromiseWinner
	some d: Candidate | d in Scenario.losers
}
run ThreeWinnersOneLoser for 8 but 6 int

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

pred TwentyFiveBallots {
	#BallotBox.ballots = 25
}
run TwentyFiveBallots for 25 but 6 int

pred ThreeWayTie {
	some disj a,b,c: Candidate | a.outcome = TiedWinner and b.outcome = TiedLoser and
		c.outcome = TiedLoser
}
run ThreeWayTie for 5 but 6 int

pred FiveWayTie {
	some disj a,b,c,d,e: Candidate | a.outcome = TiedWinner and b.outcome = TiedLoser and
		c.outcome = TiedLoser and d.outcome = TiedLoser and e.outcome = TiedWinner
}
run FiveWayTie for 7 but 6 int

pred TwentyCandidates {
	#Election.candidates = 20
	some c: Candidate | 0 < #c.votes and c in Scenario.losers
}
run TwentyCandidates for 20 but 6 int

pred Outcomes {
 	some disj a,b,c0,d,e,f,g,h,i: Candidate | 
		(a.outcome = Winner and b.outcome = QuotaWinner and 
		c0.outcome = CompromiseWinner and d.outcome = Loser and
		e.outcome = EarlyLoser and f.outcome = SoreLoser and
		g.outcome = TiedWinner and h.outcome = TiedLoser and i.outcome = TiedEarlyLoser)
}
run Outcomes for 10 but 6 int

pred FifteenDifferentBallots {
	#BallotBox.ballots = 15
	no disj a,b: Ballot | a.preferences.first = b.preferences.first and #a.preferences = #b.preferences and
		a.preferences.last = b.preferences.last and #a.assignees = #b.assignees
}
run FifteenDifferentBallots for 15 but 6 int

pred ScenarioLWW {
	some a: Candidate | a.outcome = Loser
	some disj b,c: Candidate | b.outcome = Winner and c.outcome = Winner
}
run ScenarioLWW for 6 int

pred AnyScenarioWithTiedSoreLoser {
	some c: Candidate | c.outcome = TiedSoreLoser
}
run AnyScenarioWithTiedSoreLoser for 6 int
