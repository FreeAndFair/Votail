-- (c) 2010, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Voting

open util/integer

-- A individual person standing for election
sig Candidate {
    identifier:       Int,             -- Unique identifier for this candidate
    votes: 			  set Ballot, 	-- First preference ballots assigned to this candidate
	transfers: 	      set Ballot,   -- Ballots received by transfer from another candidate
	surplus: 		  set Ballot, 	-- Ballots given to another candidate (on election or elimination)
	outcome: 		  Event	
} {
	no b: Ballot | b in votes & transfers
	all b: Ballot | b in votes + transfers => this in b.assignees
	surplus in votes + transfers
	Election.method = Plurality implies #surplus = 0 and #transfers = 0
    0 < identifier
}

-- A digital or paper artifact which accurately records the intentions of the voter
sig Ballot {
  identifier:		Int,				    -- Unique identifier for this ballot
  assignees: 		set Candidate,  -- Candidates to which this ballot has been assigned
  preferences: 	seq Candidate
} {
	assignees in preferences.elems
    not preferences.hasDups
	preferences.elems in Election.candidates
	preferences.first in assignees
	Election.method = Plurality implies #preferences = 1
    0 < #preferences
    0 < identifier
    some v: Vote | v.ballot = identifier and v.candidate = preferences.first.identifier and v.ranking = 1
    some v: Vote | v.ballot = identifier and 
		v.candidate = preferences.last.identifier and v.ranking = #preferences
    all v: Vote | v.ballot = identifier implies 
		v.candidate = preferences.subseq[v.ranking-1,v.ranking].first.identifier
}

-- Table of fragments of Votes used for encoding of results
sig Vote {
	ballot:			Int,		-- Ballot identifier
    candidate: 	Int,		-- Candidate identifier
    ranking: 		Int		-- Ranking of candidate on ballot paper (e.g. 1,2,3,...)
} {
	0 < ranking and ranking <= #Election.candidates
    some b: Ballot | b.identifier = ballot and ranking <= #b.preferences
    some c: Candidate | c.identifier = candidate
}

-- An election result
one sig Scenario {
   	losers: 				set Candidate,
   	winners: 			set Candidate,
	eliminated: 		set Candidate, 		-- Candidates excluded under STV rules
	threshold: 		Int, 						-- Minimum number of votes for a Loser or EarlyLoser
	quota: 				Int						-- Minimum number of votes for a STV Winner or QuotaWinner
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

-- An Election Constituency
one sig Election {
  candidates: 	set Candidate,
  seats: 				Int,
  method: 	Method
}
{
 	0 < seats
 	seats < #candidates
 	all c: Candidate | c in candidates
}

-- Independent (or Fundamental) Axioms
fact uniqueCandidateID {
  no disj a,b: Candidate | a.identifier = b.identifier
}

fact uniqueBallotID {
  no disj a,b: Ballot | a.identifier = b.identifier
}

fact nonDuplicationOfVotes {
  no disj a,b: Vote | a.ballot = b.ballot and a.candidate = b.candidate
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

-- Non-Independent Axioms for Ballot Integrity
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

// Ranking of votes on ballots
fact firstPreference {
	all v: Vote | some b: Ballot | v.ballot = b.identifier and
		v.ranking = 1 implies b.preferences.first.identifier = v.candidate
}

fact rankingOfVotes {
   	all v: Vote | some b: Ballot | some c: Candidate | Election.method = STV and
		v.ballot = b.identifier and v.candidate = c.identifier implies
	    c in b.preferences.elems and v.ranking = b.preferences.idxOf[c] + 1
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
    w.outcome = TiedWinner
}

-- Axioms for the recording of vote fragments
fact allVotesRecorded {
   all b: Ballot | some v: Vote | v.ballot = b.identifier and v.ranking = #b.preferences
}

// All vote fragments are recorded for each ballot
fact lowerRankings {
   all v: Vote | some w: Vote | 1 < v.ranking implies w.ranking + 1 = v.ranking and
	v.ballot = w.ballot and not v.candidate = w.candidate
}

// No duplicate ranking of candidates in same ballot
fact wellFormedRanking {
	no disj v,w: Vote | v.ballot = w.ballot and
		(v.candidate = w.candidate or v.ranking = w.ranking)
}

// Compromise winner must have more votes than any tied winners
fact compromiseNotTied {
	all disj c,t: Candidate | (c.outcome = CompromiseWinner and t.outcome = TiedWinner) implies
		#t.votes + #t.transfers < #c.votes + #t.transfers
}

// Equal losers are tied
fact equalityofTiedWinnersAndLosers {
	all disj w,l: Candidate | w in Scenario.winners and l in Scenario.losers and 
		#w.votes = #l.votes and #w.transfers = #l.transfers implies
			w.outcome = TiedWinner and 
			(l.outcome = TiedLoser or l.outcome = TiedEarlyLoser or l.outcome = TiedSoreLoser)
}

// Highest winner has a quota
fact highestWinner {
   some c: Candidate | Election.method = STV implies 
		Scenario.quota <= #c.votes + #c.transfers
}

// At least one long ballot for STV
fact atLeastOne {
  some b: Ballot | Election.method = STV implies 1 < #b.preferences
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

assert wellFormedVote {
	all v: Vote | 0 < v.ballot and 0 < v.candidate
}
check wellFormedVote for 4 but 6 int

-- Advanced Lemmas
// No lost votes during counting
assert accounting {
	all b: Ballot | one c: Candidate | b in c.votes and c in b.assignees
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

-- Sample scenarios
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
run ThreeWayTie for 5 but 6 int

pred FiveWayTie {
	some disj a,b,c,d,e: Candidate | a.outcome = TiedWinner and
	    b.outcome = TiedLoser and
		c.outcome = TiedLoser and d.outcome = TiedLoser and e.outcome = TiedWinner
}
run FiveWayTie for 7 but 6 int

pred ScenarioLWW {
	some disj a,b,c: Candidate | a in Scenario.losers and b.outcome = Winner and 
		c in Scenario.winners
    #Election.candidates = 3
}
run ScenarioLWW for 6

pred LongBallot {
	some b: Ballot | #b.preferences = 7
}
run LongBallot for 7 but 6 int

pred MultipleBallotsUnderSTV {
	Election.method = STV
	some disj a,b,c,d: Ballot | 1 < #a.preferences and 1 < #b.preferences 
	and 0 < #c.preferences and 0 < #d.preferences and a.preferences.first = b.preferences.last
}
run MultipleBallotsUnderSTV for 10
