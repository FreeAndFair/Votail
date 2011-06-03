-- Copyright (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Lemmas

open Voting

-- Basic Lemmas
assert honestCount {
	  all c: Candidate | all b: Ballot | b in c.votes + c.transfers implies 
     c in b.assignees
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
		(l.outcome = TiedLoser or l.outcome = TiedSoreLoser)
}
check wellFormedTieBreaker for 18 but 6 int

assert validSurplus {
	all c: Candidate | 0 < #c.surplus implies (c.outcome = WinnerNonTransferable or 
		c.outcome = QuotaWinnerNonTransferable or c.outcome = SurplusWinner or
		c.outcome = AboveQuotaWinner or
		c in Scenario.eliminated)
}
check validSurplus for 16 but 6 int

-- Advanced Lemmas
// Equal losers are tied or excluded early before last round
assert equalityofTiedWinnersAndLosers {
	all disj w,l: Candidate | w in Scenario.winners and l in Scenario.losers and 
		#w.votes + #w.transfers = #l.votes + #l.transfers implies
			w.outcome = TiedWinner and 
			(l.outcome = TiedLoser or 
    l.outcome = TiedSoreLoser or
    l.outcome = EarlyLoserNonTransferable or
    l.outcome = EarlySoreLoserNonTransferable or
    l.outcome = EarlyLoser)
}
check equalityofTiedWinnersAndLosers for 16 but 7 int

// No lost votes during counting
assert accounting {
	all b: Ballot | some c: Candidate | 0 < #b.preferences implies 
      b in c.votes and c in b.assignees
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
     c.outcome = EarlySoreLoserNonTransferable or c.outcome = EarlySoreLoser or
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
	0 <= Scenario.threshold and 0 <= Scenario.quota
}
check nonNegativeThresholdAndQuota for 6 but 6 int

// STV threshold below quota
assert thresholdBelowQuota {
   Election.method = STV and 0 < #Ballot implies Scenario.threshold <= Scenario.quota
}
check thresholdBelowQuota for 13 but 7 int

// Plurality sore loser
assert pluralitySoreLoser {
	all c: Candidate | (c.outcome = SoreLoser and Election.method = Plurality) implies
       #c.votes < Scenario.threshold
}
check pluralitySoreLoser for 13 but 7 int

// Plurality winner for a single seat constituency
assert pluralityWinner {
all disj a, b: Candidate | (Election.method = Plurality and Election.seats = 1 and
		a.outcome = Winner) implies #b.votes <= #a.votes
}
check pluralityWinner for 2 but 7 int

// Length of PR-STV ballot does not exceed number of candidates
assert lengthOfBallot {
  all b: Ballot | Election.method = STV implies
    #b.preferences <= #Candidate
}
check lengthOfBallot for 7 int

// Quota for a full election is less than for a by-election
assert  fullQuota {
	Scenario.fullQuota <= Scenario.quota
}
check fullQuota for 7 int

// All transfers have a source either from a winner with surplus or by early elimination
// of a loser
assert transfersHaveSource {
  all b: Ballot | some disj donor, receiver : Candidate | b in receiver.transfers 
   		implies b in donor.votes and 
   		(donor in Scenario.winners or donor in Scenario.eliminated)
}
check transfersHaveSource for 7 int 

// No missing candidates
assert noMissingCandidates {
  #Candidate = #Scenario.winners + #Scenario.losers
  }
check noMissingCandidates for 7 int

// Spoilt votes are not allocated to any candidate
assert handleSpoiltBallots {
    no c : Candidate | some b : Ballot | b in c.votes and b in BallotBox.spoiltBallots
}
check handleSpoiltBallots for 7 int

-- Sample scenarios
pred TwoCandidatePlurality { 
	Election.method = Plurality
	Election.seats = 1
	#Candidate = 2
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
	#Candidate = 3
}
run ThreeCandidatePlurality for 6 int

pred Plurality {
	Election.method = Plurality
	Election.seats = 1
	3 < #Candidate
}
run Plurality for 5 but 6 int

pred TenCandidatePluralityWithTwoSeats {
	Election.method = Plurality
	Election.seats = 2
	#Candidate = 10
}
run TenCandidatePluralityWithTwoSeats for 10 but 6 int

pred InstantRunoffVoting {
	Election.method = STV
	Election.seats = 1
	3 < #Candidate
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
	#Candidate = 3
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
    #Candidate = 3
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
     #Candidate = 2
     #Election.seats = 1
}
run TiedScenario for 7 but 6 int

pred NoTiesAndNoSoresScenarios {
  Election.method = STV
  #Candidate > 3
  #Ballot > 6
  no c: Candidate | c.outcome = TiedLoser or c.outcome = TiedWinner or
    c.outcome = TiedSoreLoser or c.outcome = SoreLoser
}
run NoTiesAndNoSoresScenarios for 10 but 6 int

-- Scenario tests
pred SLW {
  some disj c0,c1,d: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  Election.method = Plurality and #Candidate = 3
  Scenario.threshold = 1
}
run SLW for 6 but 6 int

pred SSSLW {
  some disj c0,c1,d,e,f: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  e.outcome = SoreLoser and
  f.outcome = SoreLoser and
  Election.method = Plurality and #Candidate = 5
}
run SSSLW for 6 but 6 int

pred SSSSLW {
  some disj c0,c1,d,e,f,g: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  d.outcome = SoreLoser and
  e.outcome = SoreLoser and
  f.outcome = SoreLoser and
  g.outcome = SoreLoser and
  Election.method = Plurality and #Candidate = 6
}
run SSSSLW for 6 but 6 int

pred LW {
  some disj c0,c1: Candidate | c0.outcome = Loser and c1.outcome = Winner and 
  Election.method = Plurality and 0 < #Ballot and #Candidate = 2
}
run LW for 5 but 6 int

pred LLWstv {
  some disj c0,c1,c2: Candidate | c0.outcome = Loser and c1.outcome = Winner and
  c2.outcome = Loser and 
  Election.method = STV and #Candidate = 3
}
run LLWstv for 6 but 6 int

pred SW {
  some disj c0,c1: Candidate | c0.outcome = SoreLoser and c1.outcome = Winner and 
  Election.method = Plurality and 1 < #Ballot and #Candidate = 2
}
run SW for 2 but 7 int

pred StWt {
  some disj c0,c1: Candidate | c0.outcome = TiedSoreLoser and 
  c1.outcome = TiedWinner and 
  Election.method = Plurality
}
run StWt for 2 but 7 int

pred LQ {
	some disj a,b: Candidate | a.outcome = Loser and b.outcome = QuotaWinner
    #Candidate = 2
    0 < #Ballot
}
run LQ for 10 but 6 int

pred LQQ {
	some disj a,b,c: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and
       c.outcome = QuotaWinner
    #Candidate = 3
    0 < #Ballot
}
run LQQ for 10 but 6 int

pred LQW {
	some disj a,b,c: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and 
		c.outcome = Winner
    #Candidate = 3
    0 < #Ballot
}
run LQW for 10 but 6 int

pred LQQW {
	some disj a,b,c,d: Candidate | a.outcome = Loser and b.outcome = QuotaWinner and 
		c.outcome = Winner and d.outcome = QuotaWinner
    #Candidate = 4
    0 < #Ballot
}
run LQQW for 10 but 6 int

pred SLAQW {
	some disj a,b,c,d,e: Candidate | a.outcome = Loser and 
  b.outcome = AboveQuotaWinner and 
		c.outcome = SurplusWinner and d.outcome = Winner and e.outcome = SoreLoser
    #Candidate = 5
}
run SLAQW for 16 but 7 int

pred SurplusWinner {
 some c: Candidate | c.outcome = SurplusWinner
}
run SurplusWinner for 10 but 7 int

pred AboveQuotaWinner {
 some c: Candidate | c.outcome = AboveQuotaWinner
}
run AboveQuotaWinner for 10 but 7 int

pred WinnerNonTransferable {
	some c: Candidate | c.outcome = WinnerNonTransferable
}
run WinnerNonTransferable for 16 but 7 int

pred QuotaWinnerNonTransferable {
 some c: Candidate | c.outcome = QuotaWinnerNonTransferable
}
run QuotaWinnerNonTransferable for 16 but 7 int

pred SoreLoserNonTransferable {
	some c: Candidate | c.outcome = EarlySoreLoserNonTransferable
}
run SoreLoserNonTransferable for 16 but 7 int

pred EarlyLoserNonTransferable {
 some c: Candidate | c.outcome = EarlyLoserNonTransferable
}
run EarlyLoserNonTransferable for 16 but 7 int

pred SLTT {
  some disj c1,c3,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c3.outcome = Loser and 
    c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 4
}
run SLTT for 13 but 7 int

pred SLLTT {
  some disj c2,c3,c4,c8,c9: Candidate | 
    c2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 5
}
run SLLTT for 13 but 7 int

pred SSLTT {
  some disj c1,c2,c4,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c2.outcome = SoreLoser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 5
}
run SSLTT for 13 but 7 int

pred SSLLTT {
  some disj c1,c2,c3,c4,c8,c9: Candidate | 
    c1.outcome = SoreLoser and c2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c8.outcome = TiedLoser and c9.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 6
}
run SSLLTT for 13 but 7 int

pred SSLLLTTw {
  some disj c0,c1,c3,c4,c5,c7,c8: Candidate | c0.outcome = SoreLoser and 
    c1.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c5.outcome = Loser and 
    c7.outcome = TiedLoser and c8.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 7
}
run SSLLLTTw for 13 but 7 int

pred SSSLLLTTw {
  some disj c0,s2,c1,c3,c4,c5,c7,c8: Candidate | c0.outcome = SoreLoser and 
    c1.outcome = SoreLoser and s2.outcome = SoreLoser and c3.outcome = Loser and 
    c4.outcome = Loser and c5.outcome = Loser and 
    c7.outcome = TiedLoser and c8.outcome = TiedWinner and 
    Election.method = Plurality and #Candidate = 8
}
run SSSLLLTTw for 13 but 7 int

pred LLLLTTw {
  some disj c3,c4,c5,c6,c7,c9: Candidate | 
    c3.outcome = Loser and 
    c4.outcome = Loser and 
    c5.outcome = Loser and 
    c6.outcome = Loser and 
    c7.outcome = TiedLoser and 
    c9.outcome = TiedWinner and 
    Election.method = Plurality and 
    #Candidate = 6
}
run LLLLTTw for 16 but 7 int

pred LLLLLLW {
  some disj c3,c4,c5,c6,c7,c8,c9: Candidate | 
    c3.outcome = Loser and 
    c4.outcome = Loser and 
    c5.outcome = Loser and 
    c6.outcome = Loser and 
    c7.outcome = Loser and 
    c8.outcome = Loser and 
    c9.outcome = Winner and 
    Election.method = Plurality and 
    #Candidate = 7
}
run LLLLLLW for 16 but 7 int

pred largeSurplus {
  some c: Candidate | 0 < #c.surplus
}
run largeSurplus for 10 but 7 int

pred LWW6 {
some disj c0,c1,c2: Candidate | c0.outcome = Loser and c1.outcome = Winner 
    and c2.outcome = Winner and Election.method = STV and #Candidate = 3
}
run LWW6 for 16 but 7 int

pred LLLtLtWt {
  some disj c5,c6,c7,c8,c9: Candidate | 
    c5.outcome = TiedLoser and 
    c6.outcome = TiedLoser and 
    c7.outcome = Loser and 
    c8.outcome = Loser and 
    c9.outcome = TiedWinner and 
    Election.method = Plurality and 
    #Candidate = 5
}
run LLLtLtWt for 10 but 7 int

pred LLLLWstv {
  some disj a,b,c,d,e: Candidate | 
    e.outcome = Loser and 
    d.outcome = Loser and 
    c.outcome = Loser and 
    b.outcome = Loser and 
    a.outcome = Winner and 
    Election.method = STV and 
    #Candidate = 5
}
run LLLLWstv for 16 but 7 int


