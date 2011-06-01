-- Copyright, Dermot Cochran, 2010-2011, IT University of Copenhagen

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API

module Trust

open Risk, Voting

/* A Trusted System contains solutions for all known threats */
sig TrustedSystem {
	 solves: set Solution,
		avoids: set Threats
} {
	all t: Thread | some s: Solution | t in avoids implies 
   s in solves & t.antidotes
 no f.feature | some a,b: Solution | (a in solves and b in solves) implies 
		 f in a.requires and f in b.conflicts
}

/* A Verified Trusted System contains Verifiable Solutions */
sig VerifiedElection extends Trusted System {
  election: Election
}
{
	all f feature | all s: Solution | (s in solves and f in s.requires) implies
			f.verifiable and f.feasible
}

sig Solution {
 	requires: set Feature,
		conflicts:	set Feature 
}
{
		no f: Feature | f in requires & conflicts
}

abstract sig Feature {
  verifiable: boolean,
  feasible: boolean
}
{
}

one sig BallotTraceability extends Feature {
}
{} 

one sig IndependantAudit extends Feature {
}

abstract sig Threat {
  liklihood: Natural,
  severity: Natural,
	 detectable: boolean,
  antidote: Solution
}

-- Different Kinds of Threats: Defects, Falsification, Coercion and Failure

sig Failure extends Threat {}
sig SystemFailure extends Failure {}
sig UsabilityFailure extends Failure {}


sig Defect extends Threat {
	preventable: boolean,
	testable: boolean,
 provable: boolean
}{
	provable and testable implies detectable
}
sig MisCount extends Defect{} {
	-- To Do: independant auditabity (software independence)

}

sig DenialOfService extends Defect{}
sig LostBallot extends Defect{}{
  BallotTraceability in this.antodotes
}

sig Attack extends Threat {
		cost: Natural,
	 attacker: Actor,
		feasability: Natural
}

-- Falsification Threats
sig Falsification extends Attack {}
sig VoteTampering extends Falsification{}
sig DisenfrancismentOfVoters extends Falsification{}
sig AlterationOfResults extends Falsification{}
sig Impersonation extends Falsification{}

-- Coercion Threats
sig Coercion extends Attack {
 // TODO axiom: feasibility of Coercion requires lack of privacy
}
sig Bribery extends Coercion {}
sig Intimidation extends Coercion {}

abstract sig Auditee {}
abstract sig Supplier extends Auditee {
  customer: lone Distributor,
  approval: Boolean,
  trusted: Risk,
  ethics: Risk
  }
sig Inspector extends Auditee{}
sig Farmer, Distributor extends Supplier {}
sig Auditor{}

-- Foreman/boss is a potential coercer/abuser
sig Foreman{
  employer: one Farmer,
  ethical: Boolean}
sig Worker{
  employer: one Farmer
  supervisor: lone Foreman
  exploited: boolean
  }
one sig Committee {
  members: set Auditor
  }


-- Number of inspections or audits per time unit (year)
one sig Periodicity {
      number: Natural
      -- time-unit day/week/month/year
}

-- Maximum expected level of bad product


-- Theorems

-- All bad suppliers are eventually detected
-- All bad distributors are detected
-- Volume of undetected bad product is less than threshold

pred detect-bad-supplier{}

pred detect-bad-distributor{}

pred threshold-of-bad-product{}

/*
TODO

Axioms
Proper Approval : Supplier is not approved until ethical behavior is proven
Regular Inspection: An approved supplier is subject is regular inspections
Any discovery of unethical behavior changes supplier status to unapproved
Provenance
A product must be from an approved supplier through an approved supply chain
A product is not approved unless from an approved supplier and its provenance is verified
A product with unknown provenance or from an unapproved supplier is tainted
Tainted Product
  One tainted product leads to removal of a supplier, and the backwards supply chain, until next audit
Actors
Farmer
Primary source of each product
Does not subcontract
Responsible for own finances
Inspector
Responsible for quality control
Potential for collusion or corruption
Accountable to the Auditors
Responsible for ensuring protection of workers rights
Distributor
Manages supply chain
Suppliers may be farmers or subordinate distributors
Responsible for monitoring of suppliers
Workers
Potential victims that need to be protected
Accountable to local farmer
Committee of Auditors
Jointly responsible for compliance
Jointly appoint and dismiss Inspectors
Jointly appoint and dismiss Suppliers
Auditors act by a majority of the committee
Auditors give first priory to auditing of Inspectors, then Suppliers from top-level down to Farmers
Products
Foreman
Properties
Perceived Trustworthiness of Inspectors and Suppliers
Initially zero, but increases  by one for each failed inspection or audit, and halves with each passed inspection, but not less than zero, with rounding down to nearest natural number
Ethical Risk
Non deterministic number from zero for no risk, 1=very low, 2=low, 3=medium, 4=high, 5=very high, 6=extreme, using a seven point scale
Risk Tolerance in Inspector
Non deterministic less than actual risk
Will detect all agents with risk greater than tolerance
Relationships between agents
Farmers employ Workers
Farmers supply Distributors
Distributors supply other Distributors
Inspectors inspect Suppliers
Auditors audit Agents
Inheritance Relations
Agents can be Inspectors or Suppliers
Suppliers can be Distributors or Farmers
Approval
  A supplier is initially unapproved and must pass a regular audit to become and remain approved
Unfairness
One of more workers can have status of unfair treatment, a status of ‘unfair employment’
Initially, all workers are treated as being fairly employed
Definitions
Provence
The chain of custody of  a product
The integrity of the supply chain
  Each distributor is verified only if they can prove their chain of distribution, suppliers and products
Ethical Production Process
An ethical production process does not use child labour
An ethical production process pays fair wages
An ethical production process is environmentally friendly
 An ethical production process uses organic materials
Theorems
Purity
No tainted product ever receives the Ethical Trade brand label.
An approved supplier will never release a tainted product
Process
Approved Supplier have a verifiable process to detect and prevent unethical practices
Distributors have a verifiable process for monitoring their suppliers
Non Corruption
At least one of the committee of auditors is competent, unbiased, honest and trustworthy at all times
It is impossible to deceive all of the auditors
Lemmas
Recursive Goodness
A product is assumed good if supplied by an ethical farmer, who is assumed honest if he supplies good products, until or unless he fails an inspection
Independent Inspection
One inspector is not enough
One auditor is never enough
All Farmers will be inspected
Long supply chain
Not all farmers are required to be audited
*/
