-- Copyright, Dermot Cochran, 2010-2011, IT University of Copenhagen

module Risk

-- Note that all axioms should be expressed as facts appended to signatures
-- Standalone facts will be ignored by the API

abstract sig Risk {
  level: Natural
  }

one sig Threshold {
  precent: Natural
}
