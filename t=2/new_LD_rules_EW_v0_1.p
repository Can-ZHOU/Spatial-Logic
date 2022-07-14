/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	    Rules for LD.
 > Author:          Can ZHOU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=2
vars ew_ld_ruleset;

;;; LD rules
;;; W and E rules

define :ruleset ew_ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;; Deﬁnition 2.
	;;; deﬁnitely north dE (a, b) = def E(a, b) ∧ ¬Iew(a, b)
    ;;; somewhat north sE (a, b) = def E (a, b) ∧ Iew(a, b)
    ;;; neither north nor south nEW(a, b) =def ¬E (a, b) ∧ ¬W(a, b) == nEW(a, b) ∧ (E (a, b) or W(a,b)) = bot
    ;;; somewhat south sW(a, b) =def W(a, b) ∧ Iew(a, b)
    ;;; deﬁnitely south dW(a,b)=def W(a,b)∧¬Iew(a,b)

;;; basic_rules_added_01
;;; two basic rules been added 
;;; AS 1 dE(a, b) → dW(b, a)
;;; AS 2 dW(a, b) → W(a, b)
    RULE EW_axiom_01_0
	[dE ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_01_0 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

;;; basic_rules_added_02
	RULE EW_axiom_01_1
	[dW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([W ^A ^B])]]
    ==>
	[SAYIF ld 'EW_axiom_01_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


	RULE EW_def2_dE1
	[dE ?A ?B] [->> a1]
    [Iew ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([E ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_dE1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


	RULE EW_def2_nEW1
	[nEW ?A ?B] [->> a1]
    [E ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    ==>
    [SAYIF ld 'EW_def2_nEW1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


	RULE EW_def2_nEW2
	[nEW ?A ?B] [->> a1]
    [W ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    ==>
    [SAYIF ld 'EW_def2_nEW2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


	RULE EW_def2_dW1
	[dW ?A ?B] [->> a1]
    [Iew ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_dW1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


	RULE EW_definition01
	[nEW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([nEW ^B ^A])]]
    ==>
	[SAYIF ld 'EW_definition01 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE EW_definition02
	[dE ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^B ^A])]]
    ==>
	[SAYIF ld 'EW_definition02 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;;; new axioms
    ;;; AS 1 ¬W (a, a);
    ;;; AS 2 E(a, b) ↔ W (b, a);
    ;;; AS 3 Iew (a, b) → Iew (b, a);
    ;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b))
    ;;; This axiom has been deleted /*AS 5 extra: dE(a, b) ↔ dW(b, a)*/
    ;;; AS 6 W (a, b) ∧ ¬dE(b, c) ∧ W (c, a) → ⊥;
    ;;; AS 7 ¬E(a, b) ∧ dW (b, c) ∧ ¬E(c, a) → ⊥;
    ;;; AS 8 W (a, b) ∧ ¬E(b, c) ∧ W(c, d) ∧ ¬E(d, a) → ⊥;
    ;;; AS 9 W (a, b) ∧ ¬E(b, c) ∧ ¬dE(c, d) ∧ dW (d, a) → ⊥;
    ;;; AS 10 ¬E(a, b) ∧ W (b, c) ∧ dW (c, d) ∧ ¬dE(d, a) → ⊥;
    ;;; AS 11 dW (a, b) ∧ ¬dE(b, c) ∧ dW (c, d) ∧ ¬dE(d, a) → ⊥;
    ;;; AS 12 dW (a, b) ∧ ¬dE(b, c) ∧ ¬dE(c, d) ∧ dW (d, a) → ⊥;

    ;;; or: ¬E(a,b) == nEW(a,b) ∨ W(a,b)
    ;;;     ¬dE(a,b) == Iew(a,b) ∨ dW(a,b)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_b1
	[sW ?A ?B] [->> a1]
	[nEW ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_b1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_b2
	[dW ?A ?B] [->> a1]
	[sE ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_b2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_b3
	[sW ?A ?B] [->> a1]
	[dE ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_b3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    RULE EW_axiom_b4
	[dW ?A ?B] [->> a1]
	[nEW ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_b4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_7_1
	[sW ?A ?B] [->> a1]
	[sW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_7_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

    RULE EW_axiom_7_2
	[sW ?A ?B] [->> a1]
	[sE ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([nEW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_7_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_7_3
	[sE ?A ?B] [->> a1]
	[sW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([nEW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_7_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_8_1
	[nEW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

    RULE EW_axiom_8_2
	[nEW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sE ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_8_3
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_8_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE EW_axiom_9_1
	[sW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[sW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_9_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_9_2
	[nEW ?A ?B] [->> a1]
	[sW ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([nEW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_9_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE EW_axiom_10_1
	[sW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[sE ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sE ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_2
	[sE ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[sW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE EW_axiom_11_1
	[dW ?A ?B] [->> a1]
	[sE ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([nEW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_11_2
	[nEW ?A ?B] [->> a1]
	[sW ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE EW_axiom_12_1
	[dW ?A ?B] [->> a1]
	[sE ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_12_2
	[sE ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[sE ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sE ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE EW_axiom_13_1
	[dW ?A ?B] [->> a1]
	[sE ?B ?C] [->> a2]
	[sE ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sE ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_13_2
	[sE ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ?A ?D])]]
	==>
	[SAYIF ld 'EW_axiom_9_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


enddefine;

;;; LD_rules ends here
vars LD_rules = true;
