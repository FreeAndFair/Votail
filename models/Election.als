-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Election

open Voting
open Trust
open Ethics

one sig Constituency {
	population: set Voter -- those eligible to vote
}

sig Registrar {
  registry: set Voter, -- those registered to vote
  candidates: set Candidate
} {
}

sig Voter {
	ballotCast: Ballot,
 eligible: boolean,
 registered: boolean
}

sig ElectoralBoard {
	registrars: set Registar
}

-- Requirements as Lemmas for Election Integrity



-- Security Features as Solutions for Predicates

sig EventLog {
	events: set SignificantEvent}
{}

sig SignificantEvent{
		anonymized: boolean}
{}


