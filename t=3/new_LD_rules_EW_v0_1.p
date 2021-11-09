/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=3
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
    [LVARS [consequent = add_new_formula([E ^A ^B])]]
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
	[dE ?A ?B] [->> a2]
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
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^A ^D])]]
    ==>
	[SAYIF ld 'EW_axiom_5_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_5_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    [LVARS [consequent = add_new_formula([W ^A ^C])]]
    ==>
	[SAYIF ld 'EW_axiom_5_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_5_3
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^A ^C])]]
    ==>
	[SAYIF ld 'EW_axiom_5_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_5_4
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    [LVARS [consequent = add_new_formula([dW ^A ^C])]]
    ==>
	[SAYIF ld 'EW_axiom_5_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_5_5
	[dW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([W ^A ^B])]]
    ==>
	[SAYIF ld 'EW_axiom_5_5 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_6_1
	[nEW ?A ?B] [->> a1]
	[W ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_6_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE EW_axiom_6_2
	[nEW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [nEW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_8
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_9
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [W ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_10
	[Iew ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_11
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_12
	[Iew ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_13
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[Iew ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_13 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_14
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[Iew ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_14 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_15
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [Iew ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_15 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	RULE EW_axiom_16_1
	[W ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[nEW ?C ?D] [->> a3]
    [dW ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_16_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


enddefine;

;;; LD_rules ends here
vars LD_rules = true;