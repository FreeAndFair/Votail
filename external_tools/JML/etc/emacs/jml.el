;; @(#)$Id: jml.el,v 1.2 2003/09/24 18:21:04 leavens Exp $

;; Copyright (C) 2003 Iowa State University

;; This file is part of JML

;; JML is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; JML is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with JML; see the file COPYING.  If not, write to
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

;; Initial support for performing JDEE-based inline completion of JML
;; constructs.

;; Joe Kiniry <kiniry@acm.org>

;; JML Ref Manual errors?
;; o constraint keywords missing: "for", "constraint", "constraint_redundantly"
;; o semantics of @code{==>} @code{<==} @code{<==>} @code{<=!=>} not covered yet



(setq jde-complete-function 'jde-complete-in-line)

(setq jde-enable-abbrev-mode nil)

;; Build new abbreviation table.
;(setq jde-mode-abbreviations nil)
;(if (< (length jde-mode-abbreviations) 50)
(custom-set-variables
 '(jde-mode-abbreviations
      (append
       '(

	 ;; General Java abbreviations that are not part of the default JDE abbreviation set.
	 ("as" . "assert")
	 ("nen" . "!= null;")
              
	 ;; JML-specific abbreviations.

	 ;; JML Predicate Keywords
	 ("et" . "\\elemtype")
	 ("ev" . "\\everything") ;; 6.2 Constraints and 6.5 Store Refs
	 ("exi" . "\\exists")
	 ("fo" . "\\fields_of")	;; 6.5 Store Refs
	 ("fa" . "\\forall") 
	 ("fr" . "\\fresh")
	 ("invf" . "\\invariant_for")
	 ("ii" . "\\is_initialized") 
	 ("lbln" . "\\lblneg")
	 ("lblp" . "\\lblpos")
	 ("ls" . "\\lockset") 
	 ("max" . "\\max")
	 ("min" . "\\min")
	 ("nne" . "\\nonnullelements") 
	 ("no" . "\\nothing") ;; 6.5 Store Refs
	 ("nm" . "\\not_modified")
	 ("ns" . "\\not_specified") ;; 6.5 Store Refs
	 ("numo" . "\\num_of")
	 ("old" . "\\old")
	 ("oth" . "\\other") ;; 6.2 Constraints
	 ("prod" . "\\product")
	 ("rea" . "\\reach")
	 ("res" . "\\result") 
	 ("sut" . "\\such_that")
	 ("sum" . "\\sum")
	 ("ty" . "\\type") 
	 ("to" . "\\typeof")
	 ("TY" . "\\TYPE")

	 ;; JML Keywords
	 ("abb" . "abrupt_behavior")
	 ("accr" . "accessible_redundantly")
	 ("acc" . "accessible")
	 ("al" . "also")
	 ("ar" . "assert_redundantly")
	 ("assir" . "assignable_redundantly")
	 ("assi" . "assignable") 
	 ("assr" . "assume_redundantly")
	 ("ass" . "assume")
	 ("ax" . "axiom")
	 ("be" . "behavior")
	 ("brr" . "breaks_redundantly")
	 ("brks" . "breaks")
	 ("cr" . "callable_redundantly")
	 ("cal" . "callable")
	 ("ci" . "choose_if")
	 ("dr" . "decreases_redundantly")
	 ("dcs" . "decreases")
	 ("dcr" . "decreasing_redundantly")
	 ("dc" . "decreasing")
	 ("depr" . "depends_redundantly") ;; 6.4 Depends Clauses
	 ("dep" . "depends") ;; 6.4 Depends Clauses
	 ("divr" . "diverges_redundantly")
	 ("div" . "diverges")
	 ("durr" . "duration_redundantly")
	 ("dur" . "duration")
	 ("enr" . "ensures_redundantly") 
	 ("en" . "ensures") 
	 ("exam" . "example")
	 ("eb" . "exceptional_behavior")
	 ("ee" . "exceptional_example")
	 ("exsr" . "exsures_redundantly")
	 ("exs" . "exsures")
	 ("forall" . "forall")
	 ("fe" . "for_example")
	 ("gh" . "ghost")
	 ("implt" . "implies_that")
	 ("help" . "helper")
	 ("hbr" . "hence_by_redundantly")
	 ("hb" . "hence_by")
	 ("init" . "initializer")
	 ("ini" . "initially") ;; 6.6 Variable Declaration Assertions
	 ("ins" . "instance")
	 ("invr" . "invariant_redundantly") 
	 ("inv" . "invariant") 
	 ("lir" . "loop_invariant_redundantly")
	 ("li" . "loop_invariant")
	 ("mair" . "maintaining_redundantly")
	 ("mai" . "maintaining")
	 ("mbr" . "measured_by_redundantly")
	 ("mb" . "measured_by")
	 ("mp" . "model_program")
	 ("model" . "model")
	 ("modir" . "modifiable_redundantly")
	 ("modi" . "modifiable")
	 ("modr" . "modifies_redundantly")
	 ("mod" . "modifies")
	 ("mb" . "monitored_by") ;; 6.6 Variable Declaration Assertions
	 ("mo" . "monitored") ;; 6.6 Variable Declaration Assertions
	 ("nn" . "non_null")
	 ("nb" . "normal_behavior")
	 ("ne" . "normal_example")
	 ("nw" . "nowarn")
	 ("old" . "old")
	 ("or" . "or")
	 ("post" . "post")
	 ("pre" . "pre")
	 ("pure" . "pure")
	 ("ri" . "readable_if")	;; 6.6 Variable Declaration Assertions
	 ("ref" . "refine")
	 ("repr" . "represents_redundantly") ;; 6.3 Represents Clauses
	 ("rep" . "represents")	;; 6.3 Represents Clauses
	 ("reqr" . "requires_redundantly")
	 ("req" . "requires")
	 ("rr" . "returns_redundantly")
	 ("rets" . "returns")
	 ("set" . "set")
	 ("sigr" . "signals_redundantly")
	 ("sig" . "signals")
	 ("spr" . "spec_protected")
	 ("spu" . "spec_public")
	 ("stati" . "static_initializer")
	 ("subc" . "subclassing_contract")
	 ("uninit" . "uninitialized")
	 ("unr" . "unreachable")
	 ("weak" . "weakly")
	 ("whr" . "when_redundantly")
	 ("wh" . "when")
	 ("wsr" . "working_space_redundantly")
	 ("ws" . "working_space")

	 ;; JML Special Symbols.

	 ("==>" . "==>")
	 ("<==" . "<==")
	 ("<==>" . "<==>")
	 ("<!>" . "<=!=>")
	 ("->" . "->")
	 ("->" . "<-")
	 (".." . "..")
	 ("{|" . "{|")
	 ("|}" . "|{")

	 ;; JML Informal Descriptions.

	 ("infdesc" . "(* informal description *)")

	 ;; JML Type Definitions (JMLRef 5.1)

	 ;; Keywords taken care of above:
	 ;; \TYPE spec_public spec_protected model ghost pure instance helper monitored
	 ;; uninitialized non_null weakly

	 ;; Keywords that are part of JDE core:
	 ;; public private protected abstract static final synchronized transient volatile
	 ;; native strictfp const

	 ;; JML Fields (JMLRef 5.2)

	 ;; Keywords taken care of above:
	 ;; static_initializer initializer axiom non_null

	 ;; Keywords that are part of JDE core:
	 ;; static final

	 ;; JML Constraints (JMLRef 6.2)

	 ;; Keywords taken care of above:
	 ;; constraint constraint_redundantly \everything \other

	 ;; JML Convenience Expressions.

	 ("depe" . "depends store-ref-expression <- store-ref-list ;")
	 ("ense" . "ensures Q;")
	 ("exe" . "(\\exists Type t; G(t); P(t));") 
	 ("fae" . "(\\forall Type t; G(t); P(t));")
	 ("mode" . "modifies \\everything;")
	 ("modn" . "modifies \\nothing;")
	 ("repe" . "represents store-ref-expression <- spec-expression ;") 
	 ("repst" . "represents store-ref-expression \\such_that spec-expression ;")
	 ("reqe" . "requires P;")
	 ("sige" . "signals (Expression e) R;")
	 ("exse" . "exsures (Expression e) R;")
	 ("oe" . "\\old()")
	 ("sume" . "(\\sum Type t, G(t); P(t));")
	 ("prode" . "(\\product Type t, G(t); P(t));")
	 ("maxe" . "(\\max Type t, G(t); P(t));")
	 ("minee" . "(\\min Type t, G(t); P(t));")
	 ("numoe" . "(\\num_of Type t, G(t); P(t));")

	 ;; JML Full spec outlines.  Note my default indent is four spaces.

	 ("hspec" . "    //@ behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   ensures Q;
    //@   signals (Exception) R;")

	 ;; Lightweight specifications do not use any behavior
	 ;; keyword or visibilty modifiers at all.  This tells
	 ;; JML that the specification is incomplete in the
	 ;; sense of the only contains what the specifier
	 ;; wanted to write down, and not everything possible

	 ("lspec" . "    //@ requires P;
    //@ assignable X;
    //@ ensures Q;
    //@ signals (Exception) R;")

	 ;; For each standard visibility modifier, a normal and
	 ;; an exception behavioral specification.

	 ;; Note that normal_behaviors do not have signals clauses.
	 ;; It is equivalent to a standard behavior spec with a
	 ;; signals clause of "signals (java.lang.Exception) false".

	 ("pubnhspec" . "    //@ public normal_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   ensures Q;")
	 ("pronhspec" . "    //@ protected normal_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   ensures Q;")
	 ("prinhspec" . "    //@ private normal_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   ensures Q;")
	 ("nhspec" . "    //@ normal_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   ensures Q;")

	 ;; Note that exceptional_behaviors do not have ensures
	 ;; clauses because they do not specify a method's
	 ;; semantics when it terminates normally.  It is
	 ;; equivalent to a standard behavior spec with an
	 ;; ensures clause of "ensures false".

	 ("pubehspec" . "    //@ public exceptional_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   signals (Exception) R;")
	 ("proehspec" . "    //@ protected exceptional_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   signals (Exception) R;")
	 ("priehspec" . "    //@ private exceptional_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   signals (Exception) R;")
	 ("ehspec" . "    //@ exceptional_behavior
    //@   requires P;
    //@   diverges \\not_specified;
    //@   assignable X;
    //@   when \\not_specified;
    //@   signals (Exception) R;")

	 )
       jde-mode-abbreviations)))
