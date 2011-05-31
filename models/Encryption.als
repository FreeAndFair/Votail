-- Copyright (c) 2011, Dermot Cochran, IT Univeristy of Copenhagen

module Encryption

-- Axioms for Digital Signatures
abstract sig DigitalSignature {}

-- Axioms for Encyption

abstract sig Encryption {}

-- Axioms for Double Blind Signatures

sig DoubleBlind extends DigitalSignature {
}

-- Axioms for Homomorphic Encryption

sig Homomorphic extends Encryption {
}
