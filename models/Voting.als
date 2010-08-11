-- Dermot Cochran, 2010, IT University of Copenhagen
-- http://www.kindsoftware.com
-- See ICSE 2011 paper 'Exploring the Universe of Ballot Boxes'

module Voting

open util/integer

-- A person standing for election
sig Candidate {
  	votes: 		set Ballot, 	-- First preference ballots assigned to this candidate
	transfers: set Ballot, 	-- Ballots received by transfer from another candidate
	surplus: 	set Ballot, 	-- Ballots given to another candidate (on election or elimination)
	outcome: 	Event	
} {
	no b: Ballot | b in votes & transfers
	all b: Ballot | b in votes + transfers => this in b.assignees
	surplus in votes + transfers
	Election.method = Plurality implies #surplus = 0 and #transfers = 0
}

-- A digital or paper artifact which accurately records the intentions of the voter
sig Ballot {
  assignees: 		set Candidate, -- Candidates to which this ballot has been assigned
  preferences: 	seq Candidate
} {
	assignees in preferences.elems
    0 < #assignees
    not preferences.hasDups
	preferences.elems in Election.candidates
	preferences.first in assignees
	Election.method = Plurality implies #preferences = 1
}

-- An election result
one sig Scenario {
   	losers: 					set Candidate,
   	winners: 				set Candidate,
	eliminated: 			set Candidate, 		-- Candidates excluded under STV rules
	threshold: 			Int, 						-- Minimum number of votes for a Loser or EarlyLoser
	quota: 					Int,						-- Minimum number of votes for a Winner or QuotaWinner
	transfers:				set Transfer			-- Ballot transfers between candidates under STV rules
}
{
 	winners + losers = Election.candidates
 	#winners = Election.seats
 	no c: Candidate | c in losers & winners
 	0 < #losers
 	all w: Candidate | all l: Candidate | l in losers and w in winners implies #l.votes <= #w.votes
	0 <= threshold
	threshold < quota
	Election.method = Plurality implies #eliminated = 0
	eliminated in losers
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

-- A movement of a ballot from one candidate's surplus to another candidate
sig Transfer {
	donor:		Candidate,	-- Candidate with surplus or excluded candidate
	receiver:	Candidate,	--	 Candidate next in preference
	ballot:		Ballot			-- The Ballot which was transfered
} {
	donor in Scenario.winners + Scenario.eliminated
	donor in ballot.assignees
	receiver in ballot.assignees & ballot.preferences.rest.elems
	ballot in receiver.transfers & donor.surplus
	ballot in donor.votes + donor.transfers
	ballot.preferences.idxOf[donor] < ballot.preferences.idxOf[receiver]
	-- all candidates inbetween are either elected or eliminated (Lemma)
}

-- Axioms
fact wellFormedQuota {
	Election.method = STV implies 
		#BallotBox.ballots < Scenario.quota.mul[Election.seats+1] and
		Scenario.quota.mul[Election.seats] <= #BallotBox.ballots 
}

fact wellFormedThreshold {
	#BallotBox.ballots <= Scenario.threshold.mul[20] or 
	Election.method = STV implies Scenario.quota <= Scenario.threshold.mul[4]
}

fact transfers {
	some c: Candidate | 0 < #c.transfers implies Election.method = STV
}

fact integrity {
  all c: Candidate | all b: Ballot | b in c.votes implies c in b.assignees
}

fact pluralityEvents {
	all c: Candidate | Election.method = Plurality implies
		(c.outcome = Loser or c.outcome = SoreLoser or c.outcome = Winner or 
		c.outcome = TiedWinner or c.outcome = TiedLoser)
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

fact sizeOfSurplus {
	all c: Candidate | (c in Scenario.winners and Election.method = STV and 0 < #c.surplus) implies 
		#c.surplus = #c.votes + #c.transfers - Scenario.quota
}

fact tieBreaker {
	all w: Candidate | some l: Candidate | w.outcome = TiedWinner implies 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome = TiedEarlyLoser)
}

fact pluralityWinner {
	all disj a, b: Candidate | (Election.method = Plurality and Election.seats = 1) and
		a.outcome = Winner implies #b.votes < #a.votes
}

fact transferToNextPreference {
	all b: Ballot | all c,d: Candidate | c in b.assignees and d in b.assignees and
		b in c.votes and b in d.transfers implies 
		(c in b.preferences.first and d in b.preferences.rest.elems and b in c.surplus)
}

fact wellFormedTieBreaker {
	all disj a,b : Candidate | (a.outcome = TiedWinner or b.outcome = TiedLoser) and 
		#a.votes = #b.votes and #a.transfers = #b.transfers iff 
		(b.outcome = TiedWinner or b.outcome = TiedLoser)
}

fact validTieBreaker {
	all l: Candidate | some w: Candidate | l.outcome = TiedLoser implies w.outcome = TiedWinner
}

fact transferRecord {
	all c: Candidate | all b: Ballot | some t: Transfer | b in c.transfers implies
		b in t.ballot and c in t.receiver and t in Scenario.transfers
}

fact noDuplicateTransferForSameBallot {
	no disj a,b: Transfer | a.ballot = b.ballot and (a.donor = b.donor or a.receiver = b.receiver)
}

-- Lemmas
assert atLeastTwoCandidates {
	1 < #Election.candidates
}
check atLeastTwoCandidates for 6 int

assert transfersOnlyInSTV {
	Election.method = Plurality implies #Scenario.transfers = 0
}
check transfersOnlyInSTV for 5 but 6 int

assert eliminatedCandidates {
		Scenario.eliminated in Election.candidates
}
check eliminatedCandidates for 5 but 6 int

assert pluralityBallot {
	all b: Ballot | Election.method = Plurality implies #b.assignees = 1
}
check pluralityBallot for 5 but 6 int

assert atLeastOnePreference {
	all b: Ballot | 0 < #b.preferences
}
check atLeastOnePreference for 5 but 6 int

assert honestCount {
	  all c: Candidate | all b: Ballot | b in c.votes or b in c.transfers implies c in b.preferences.elems
}
check honestCount for 5 but 6 int

assert atLeastOneLoser {
	0 < #Scenario.losers
}
check atLeastOneLoser for 5 but 6 int

assert atLeastOneWinner {
	0 < #Scenario.winners
}
check atLeastOneWinner for 4 but 6 int

assert moreCandidatesThanSeats {
	Election.seats < #Election.candidates
}
check moreCandidatesThanSeats for 4 but 6 int

assert assignedCandidates {
	all b: Ballot | b.assignees in Election.candidates 
}
check assignedCandidates for 10 but 6 int

assert assignedBallots {
		all b: Ballot | #b.assignees <= #b.preferences
}
check assignedBallots for 8 but 6 int

assert nonZeroQuota {
	0 < Scenario.quota or Election.method = Plurality
}
check nonZeroQuota for 4 but 6 int

assert wellFormednessOfBallots {
	all b: Ballot | b.preferences.first in Election.candidates
}
check wellFormednessOfBallots for 8 but 6 int

assert wellFormedBallotBox {
		#BallotBox.ballots = sum (#Election.candidates.votes) 
}
check wellFormedBallotBox for 4 but 6 int

assert plurality {
	all c: Candidate | all b: Ballot | b in c.votes and 
		Election.method = Plurality implies c in b.preferences.first
}
check plurality for 8 but 6 int

assert wellFormedTieBreaker {
	some w,l : Candidate | w in Scenario.winners and l in Scenario.losers and 
		#w.votes = #l.votes and #w.transfers = #l.transfers implies 
		w.outcome = TiedWinner and 
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser or l.outcome=TiedEarlyLoser)
}
check wellFormedTieBreaker for 8 but 6 int

assert numberOfWinners {
	#Scenario.winners = Election.seats
}
check numberOfWinners for 16 but 6 int

assert onlyWinnersHaveSurplus {
	all c: Candidate | 0 < #c.surplus implies c in Scenario.winners 
}
check onlyWinnersHaveSurplus for 5 but 6 int

assert exclusiveLosers {
	Scenario.losers = Election.candidates - Scenario.winners
}
check exclusiveLosers for 5 but 6 int

assert transfersReceived {
	all b: Ballot | all c: Candidate | some d: Candidate | 
		b in c.transfers implies b in d.votes & d.surplus
}
check transfersReceived for 5 but 6 int

assert validSurplus {
	all c: Candidate | 0 < #c.surplus implies c.outcome = Winner or c.outcome = QuotaWinner or 
		c in Scenario.eliminated
}
check validSurplus for 6 but 6 int

assert validElimination {
	all c: Candidate | c in Scenario.eliminated iff c.outcome = TiedEarlyLoser or c.outcome = EarlyLoser or
		c.outcome = SoreLoser
}
check validElimination for 8 but 6 int

-- Generation of Ballot Boxes for Different Scenarios
pred TwoCandidatePlurality { 
	Election.method = Plurality
	Election.seats = 1
	#Election.candidates = 2
}
run TwoCandidatePlurality for 10 but 1 Ballot, 6 int

assert oneBallot {
	not (TwoCandidatePlurality implies #BallotBox.ballots = 1) and
	(TwoCandidatePlurality implies #BallotBox.ballots = 1)
}
check oneBallot for 10 but 1 Ballot, 6 int

pred PluralityTiedWinner {
	Election.method = Plurality
	Election.seats = 1
	some disj a,b: Candidate | a.outcome = TiedWinner and b.outcome = TiedLoser
}
run PluralityTiedWinner for 32 but 6 int

pred ThreeCandidatePlurality {
	Election.method = Plurality
	Election.seats = 1
	#Election.candidates = 3
}
run ThreeCandidatePlurality for 8 int

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
 	some disj a,b,c,d,e,f,g,h,i: Candidate | 
		(a.outcome = Winner and b.outcome = QuotaWinner and 
		c.outcome = CompromiseWinner and d.outcome = Loser and
		e.outcome = EarlyLoser and f.outcome = SoreLoser and
		g.outcome = TiedWinner and h.outcome = TiedLoser and i.outcome = TiedEarlyLoser)
}
run Outcomes for 6 int

pred FifteenDifferentBallots {
	#BallotBox.ballots = 15
	no disj a,b: Ballot | a.preferences.first = b.preferences.first and #a.preferences = #b.preferences and
		a.preferences.last = b.preferences.last and #a.assignees = #b.assignees
}
run FifteenDifferentBallots for 6 int

pred ScenarioLWW {
	some a: Candidate | a.outcome = Loser
	some disj b,c: Candidate | b.outcome = Winner and c.outcome = Winner
}
run ScenarioLWW for 6 int

pred AnyScenarioWithTiedSoreLoser {
	some c: Candidate | c.outcome = TiedSoreLoser
}
run AnyScenarioWithTiedSoreLoser for 6 int

assert consistentTheory {
	all c: Candidate | c not in Election.candidates
}
check consistentTheory for 6 int
