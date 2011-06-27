-- Copyright, Dermot Cochran, 2010-2011, IT University of Copenhagen

module Risk

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API

abstract sig Risk {
  level: Level
  }

one sig Threshold {
  precent: Natural
}

enum Level {High, Medium, Low}

/* Issues: (Lemmas and Predicates)

			(1) pre-arranged ballot signatures in anonymised votes
			(2) Duplicate registration of voters
			(3) Unfair disqualification of eligible voters
*/

/* Assumptions: (Axioms)

1) Voters are invited for election, and must show identification at the (virtual) polling 
place.

2) Voters arrive at the (virtual) polling place, so that the voting 
environment is controlled.

3) Instead of a physical ballot you will be provided, for example, a piece of 
paper with a barcode . Leaflet can authenticate against voting machine that is a 
valid ballot, without revealing identity. This could also be a USB key that 
contains a cryptographic token. (DemTech)

4) Then you go into the voting booth and vote through a voting machine. 

5) Once you have voted, is printed a physical proof out with a barcode on. Via a 
handheld scanner in the box, you can scan its barcode on the physical form and 
voting machine once again shows who you voted for.

6) Subsequent counting of electronic ballots up and if there is cheating, the 
physical banknotes still be scanned and counted. If there is fraud involved, you 
can detect it because the physical currency must match the computer generated 
'image', which formed when the electronic ballot counting. (DemTech)

7) When voting from home, a secondary password can be used to record a fake vote,
   to avoid vote selling and coercion, same as duress code on burgular alarms

8) When ballots are published, only the effective preferences should be shown;
			unused preferences should never be published (McMahon)

*/

/* Unsolved Issues:

	(1) How to prevent coercion when voting from home (fake votes etc.)
 (2) Mobile Smart Phones are not secure enough; passwords etc. can be stolen
 (3) How to detect vulnerabilities



*/
