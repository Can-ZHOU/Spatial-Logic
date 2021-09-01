/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
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

/*
	RULE EW_def2_dE2
	[E ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([dE ^A ^B])]
	       [consequent2 = add_new_formula([Iew ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_dE2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE EW_def2_sE1
	[sE ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([E ^A ^B])]
	       [consequent2 = add_new_formula([Iew ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_sE Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE EW_def2_sE2
	[E ?A ?B] [->> a1]
    [Iew ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sE ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_sE2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
*/

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

/*
	RULE EW_def2_sW1
	[sW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([W ^A ^B])]
	       [consequent2 = add_new_formula([Iew ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_sW1 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE EW_def2_sW2
	[W ?A ?B] [->> a1]
    [Iew ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sW ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_sW2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
*/

	RULE EW_def2_dW1
	[dW ?A ?B] [->> a1]
    [Iew ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_dW1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
/*
	RULE EW_def2_dW2
	[W ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([dW ^A ^B])]
	       [consequent2 = add_new_formula([Iew ^A ^B])]]
    ==>
	[SAYIF ld 'EW_def2_dW2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]
*/
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
	RULE EW_axiom_1
	[W ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'EW_axiom_1 Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_2_1
	[E ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([W ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_2_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE EW_axiom_2_2
	[W ?B ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([E ^a ^b])]]
    ==>
	[SAYIF ld 'EW_axiom_2_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_3
	[Iew ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([Iew ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    RULE EW_axiom_4_1
	[Iew ?A ?B] [->> a1]
	[dE ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_4_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE EW_axiom_4_2
	[Iew ?A ?B] [->> a1]
	[dW ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_4_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	;;; For Rule 4.3: already satisified


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_5_1
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ?A ?C])]]
	==>
	[SAYIF ld 'EW_axiom_5_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_5_2_1
	[dW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dE ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_5_2_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE EW_axiom_5_2_2
	[dE ?B ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^a ^b])]]
    ==>
	[SAYIF ld 'EW_axiom_5_2_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE EW_axiom_5_3
	[dW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([W ^A ^B])]]
    ==>
	[SAYIF ld 'EW_axiom_5_3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    RULE EW_axiom_6_1
	[W ?A ?B] [->> a1]
	[nEW ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_6_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE EW_axiom_6_2
	[nEW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[nEW ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	RULE EW_axiom_6_3
	[nEW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([nEW ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_6_3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_7
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
    [nEW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_8
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[Iew ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_9
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_10
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_11
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[Iew ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


enddefine;

;;; LD_rules ends here
vars LD_rules = true;
