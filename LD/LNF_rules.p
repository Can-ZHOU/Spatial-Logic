/* --- Copyright University of Nottingham 2011. All rights reserved. ------
 > File:            ontology_rules.p
 > Purpose:	    Rules for a simple LNF reasoner.
 > Author:          Hai Nguyen & Brian Logan, January 14 2012
 > Documentation:   
 > Related Files:   LNF_rules.p
 */


vars lnf_ruleset;

;;; The following is fairly ugly, as the key of a database item
;;; essentially can't be a list (comparison is done with ==). We
;;; therefore have to lift complex terms that are arguments to logical
;;; connectives up one level when they appear on the left of a
;;; connective, to allow indexing of database entries.
define :ruleset lnf_ruleset;
;;;    [DLOCAL [prb_show_conditions = true]];
    [VARS prb_allrules trigger_db];

    ;;; An inconsistency results when we have both [not c] and [c] where c
    ;;; is a (simple or complex) concept instance.
/*    RULE inconsistent1
	[INDATA ?trigger_db [not ?c]] [->> negated_instance]
	[??c] [->> concept_instance]
    ==>
	[SAYIF lnf 'Inconsistent data' ?concept_instance ?negated_instance]
	[ATMS_INCONSISTENT ?concept_instance ?negated_instance]

    ;;; Not clear if ontologies are in negation normal form, so the
    ;;; following may not be safe.
    RULE inconsistent2
	[INDATA ?trigger_db [??c]] [->> concept_instance]
	[not ?c] [->> negated_instance]
    ==>
	[SAYIF lnf 'Inconsistent data' ?concept_instance ?negated_instance]
	[ATMS_INCONSISTENT ?concept_instance ?negated_instance]
*/

    ;;; DECOMPOSITION RULES
/*
    RULE conjunction
    	[INDATA ?trigger_db [and ??c]] [->> conjunction]
    ==> 
    	[LVARS [conjuncts = add_new_formulas(c)]]
	[SAYIF lnf 'Conjunction elimination:' ??c]
    	[ATMS_AND_JUSTIFY ?conjuncts ?conjunction]

    ;;; Instances of disjunctive concepts are of the form [or c1 ... cn]
    ;;; where c1, ..., cn are (simple or complex) concepts
    RULE disjunction
    	[INDATA ?trigger_db [or ??d]] [->> disjunction]
    ==> 
    	[LVARS [disjuncts = add_new_formulas(d)]]
	[SAYIF lnf 'Disjunction elimination:' ??d]
    	[ATMS_OR_JUSTIFY ?disjuncts ?disjunction]
*/

    ;;; INFERENCE RULES
    
    
    
     RULE inference_2
	[INDATA ?trigger_db [?X BEQ ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [^Y BEQ ^X ])]
		[r= lnf_axiom()]]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a ?r]
	[ATMS_JUSTIFY ?consequent [?a ?r]]
	
     RULE inference_3
	[INDATA ?trigger_db [?X NEAR ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [^Y NEAR ^X ])]
		[r= lnf_axiom()]]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a ?r]
	[ATMS_JUSTIFY ?consequent [?a ?r]]
	
     RULE inference_4
	[INDATA ?trigger_db [ ?X FAR ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [ ^Y FAR ^X ])]
		[r= lnf_axiom()]]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a ?r]
	[ATMS_JUSTIFY ?consequent [?a ?r]]
    
     RULE inference_5
	[ ?A BEQ ?B] [->>a1]
	[ ?B BEQ ?C] [->>a2]
	[not [ ?A NEAR ?C]] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
	
    RULE inference_6
	[ ?A BEQ ?B] [->>a1]
	[ ?B NEAR ?C] [->>a2]
	[ ?C BEQ ?D] [->>a3]
	[ ?D FAR ?A] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4 ?r]
;;;;	[POP11 atms_lazy_node_label([ ])]
	
    RULE inference_7
	[ ?A NEAR ?B] [->>a1]
	[ ?B NEAR ?C] [->>a2]
	[ ?A FAR ?C] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]

    RULE inference_8
    	[?A BEQ  ?B] [->>a1]
	[?B BEQ ?C] [->>a2] 
	[?C NEAR ?D] [->>a3]
	[?D FAR ?A] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_9
	[?A BEQ ?B] [->>a1]
	[not [?A NEAR ?B]] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_10
	[?A NEAR ?B] [->>a1]
	[?A FAR  ?B] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]

    RULE inference_11
	[?A BEQ  ?B] [->>a1]
	[?B FAR  ?C] [->>a2]
	[?A NEAR  ?C] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
   
    RULE inference_12
	[?A BEQ ?B] [->>a1]
	[?A FAR ?B] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]

    RULE inference_13
	[?A BEQ ?B] [->>a1]
	[?B BEQ  ?C] [->>a2]
	[?A FAR ?C] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]	
	
     RULE inference_14
    	[?A BEQ ?B] [->>a1]
	[?B BEQ ?C] [->>a2]
	[?C BEQ ?D] [->>a3]
	[?D FAR ?A] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_15
    	[?A BEQ ?B] [->>a1]
	[?B BEQ ?C] [->>a2]
	[?C BEQ ?D] [->>a3]
	[?D BEQ ?E] [->>a4]
	[?E FAR ?A] [->>a5]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4 ^a5],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4 ?a5 ?r]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4 ?a5 ?r]
;;;	[POP11 atms_lazy_node_label([ ])]
;;;*/
/*
   RULE inference_2
	[INDATA ?trigger_db [?X BEQ ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [^Y BEQ ^X ])]
	]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a]
	[ATMS_JUSTIFY ?consequent [?a]]
	
     RULE inference_3
	[INDATA ?trigger_db [?X NEAR ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [^Y NEAR ^X ])]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a]
	[ATMS_JUSTIFY ?consequent [?a]]
	
     RULE inference_4
	[INDATA ?trigger_db [ ?X FAR ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [ ^Y FAR ^X ])]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a]
	[ATMS_JUSTIFY ?consequent [?a]]

     RULE inference_5
	[ ?A BEQ ?B] [->>a1]
	[ ?B BEQ ?C] [->>a2]
	[not [ ?A NEAR ?C]] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
;;;	[POP11 atms_lazy_node_label([ ])]
	
    RULE inference_6
	[OR [ ?A BEQ ?B] [?B BEQ ?A]] [->>a1]
	[OR [ ?B NEAR ?C] [?C NEAR ?B]] [->>a2]
	[OR [ ?D BEQ ?C] [?C BEQ ?D]] [->>a3]
	[OR [ ?A FAR ?B] [?B FAR ?A]] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;;;	[POP11 atms_lazy_node_label([ ])]
	
;;;    RULE inference_7
;;;	[ ?A NEAR ?B] [->>a1]
;;;	[ ?B NEAR ?C] [->>a2]
;;;	[ ?A FAR ?C] [->>a3]
;;;	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
;;;	==>
;;;	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3]
;;;	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
;;;	[POP11 atms_lazy_node_label([ ])]
/*
    RULE inference_8
    	[?A BEQ  ?B] [->>a1]
	[?B BEQ ?C] [->>a2] 
	[?C NEAR ?D] [->>a3]
	[?A FAR ?D] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_9
	[?A BEQ ?B] [->>a1]
	[not [?A NEAR ?B]] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_10
	[?A NEAR ?B] [->>a1]
	[?A FAR  ?B] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
;;;	[POP11 atms_lazy_node_label([ ])]

    RULE inference_11
	[?A BEQ  ?B] [->>a1]
	[?B FAR  ?C] [->>a2]
	[?A NEAR  ?C] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
;;;	[POP11 atms_lazy_node_label([ ])]
   
    RULE inference_12
	[?A BEQ ?B] [->>a1]
	[?A FAR ?B] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
;;;	[POP11 atms_lazy_node_label([ ])]

    RULE inference_13
	[?A BEQ ?B] [->>a1]
	[?B BEQ ?C] [->>a2]
	[?A FAR ?C] [->>a3]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
;;;	[POP11 atms_lazy_node_label([ ])]	
	
     RULE inference_14
    	[?A BEQ ?B] [->>a1]
	[?B BEQ ?C] [->>a2]
	[?C BEQ ?D] [->>a3]
	[?A FAR ?D] [->>a4]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;;	[POP11 atms_lazy_node_label([ ])]
	
     RULE inference_15
    	[?A BEQ ?B] [->>a1]
	[?B BEQ ?C] [->>a2]
	[?C BEQ ?D] [->>a3]
	[?D BEQ ?E] [->>a4]
	[?A FAR ?E] [->>a5]
	[WHERE some_in_db_p([ ^a1 ^a2 ^a3 ^a4 ^a5],trigger_db)]
;;;	[LVARS	[r =lnf_axiom()]]
	==>
	[SAYIF lnf 'Inconsistent data' ?a1 ?a2 ?a3 ?a4 ?a5]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4 ?a5]
;;;	[POP11 atms_lazy_node_label([ ])]

*/
/* 
;;;
;;; SAMEAS axioms: sameas(a,b) => sameas (b,a)
;;; sameas(a,b) & P(a,x) => P (b,x) where P={BEQ, NEAR, FAR}
;;;
*/
/*
    RULE inference_16
	[INDATA ?trigger_db [?X SAMEAS ?Y ]] [->> a]
	[LVARS
		[consequent=add_new_formula( [ ^Y  SAMESAS ^X ])]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a]
	[ATMS_JUSTIFY ?consequent [?a ]]
*/	
    RULE inference_17
        [?A SAMEAS ?B]  [->>a1]
	[?A BEQ ?X] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	
		[consequent=add_new_formula( [^B BEQ ^X ])]
		[r =lnf_axiom()]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ]]
  
   RULE inference_18
        [?A SAMEAS ?B]  [->>a1]
	[?A FAR ?X] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	
		[consequent=add_new_formula( [^B FAR ^X ])]
		[r =lnf_axiom()]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a1 ?a2 ]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ]]
	
   RULE inference_19
        [?A SAMEAS ?B]  [->>a1]
	[?A NEAR ?X] [->>a2]
	[WHERE some_in_db_p([ ^a1 ^a2 ],trigger_db)]
	[LVARS	
		[consequent=add_new_formula( [ ^B NEAR ^X ])]
		[r =lnf_axiom()]
		]
	==>
	[SAYIF lnf 'Justifying datum' ?consequent ?a1 ?a2 ]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ]]
    
;;;*/	

enddefine;

;;; LNF_rules ends here
vars LNF_rules = true;
