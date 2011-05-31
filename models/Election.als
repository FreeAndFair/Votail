-- (c) 2010-2011, Dermot Cochran, IT University of Copenhagen
-- http://www.kindsoftware.com/about/people/dc
-- http://www.itu.dk/people/dero

module Election

open Voting, Risk, Ethics, Trust, Privacy, Secrecy

abstract sig Agent {} extends Actor

sig Process {
}

sig Registrar extends Agent {
  registry: set Voter,
  candidates: set Candidate
}

sig Voter extends Agent {
	ballotCast: Ballot
}

sig ElectoralBoard {
	registrars: set Registar
}

-- Requirements as Lemmas for Election Integrity



-- Security Features as Solutions for Predicates
