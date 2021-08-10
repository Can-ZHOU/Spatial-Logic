/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=2
vars ns_ld_ruleset;

;;; LD rules
;;; S and N rules

define :ruleset ns_ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;; Deﬁnition 2.
	;;; deﬁnitely north dN (a, b) = def N(a, b) ∧ ¬Ins(a, b)
    ;;; somewhat north sN (a, b) = def N (a, b) ∧ Ins(a, b)
    ;;; neither north nor south nNS(a, b) =def ¬N (a, b) ∧ ¬S(a, b) == nNS(a, b) ∧ (N (a, b) or S(a,b)) = bot
    ;;; somewhat south sS(a, b) =def S(a, b) ∧ Ins(a, b)
    ;;; deﬁnitely south dS(a,b)=def S(a,b)∧¬Ins(a,b)

;;; basic_rules_added_01
;;; two basic rules been added 
;;; AS 1 dN(a, b) → dS(b, a)
;;; AS 2 dS(a, b) → S(a, b)
	RULE NS_axiom_01_0
	[dN ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dS ^B ^A])]]
    ==>
	[SAYIF ld 'EW_axiom_01_0 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

;;; basic_rules_added_02
	RULE EW_axiom_01_1
	[dS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([S ^A ^B])]]
    ==>
	[SAYIF ld 'EW_axiom_01_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE NS_def2_dN1
	[dN ?A ?B] [->> a1]
    [Ins ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([N ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_dN1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

/*
	RULE NS_def2_dN2
	[N ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([dN ^A ^B])]
	       [consequent2 = add_new_formula([Ins ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_dN2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE NS_def2_sN1
	[sN ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([N ^A ^B])]
	       [consequent2 = add_new_formula([Ins ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_sN Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE NS_def2_sN2
	[N ?A ?B] [->> a1]
    [Ins ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_sN2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
*/

	RULE NS_def2_nNS1
	[nNS ?A ?B] [->> a1]
    [N ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    ==>
    [SAYIF ld 'NS_def2_nNS1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


	RULE NS_def2_nNS2
	[nNS ?A ?B] [->> a1]
    [S ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
    ==>
    [SAYIF ld 'NS_def2_nNS2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

/*
	RULE NS_def2_sS1
	[sS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([S ^A ^B])]
	       [consequent2 = add_new_formula([Ins ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_sS1 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]

	RULE NS_def2_sS2
	[S ?A ?B] [->> a1]
    [Ins ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_sS2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
*/

	RULE NS_def2_dS1
	[dS ?A ?B] [->> a1]
    [Ins ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_dS1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
/*
	RULE NS_def2_dS2
	[S ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1 = add_new_formula([dS ^A ^B])]
	       [consequent2 = add_new_formula([Ins ^A ^B])]]
    ==>
	[SAYIF ld 'NS_def2_dS2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]
*/
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;;; new axioms
    ;;; AS 1 ¬S (a, a);
    ;;; AS 2 N(a, b) ↔ S (b, a);
    ;;; AS 3 Ins (a, b) → Ins (b, a);
    ;;; AS 4 Ins(a, b) ↔ (¬dN(a, b) ∧ ¬dS (a, b))
    ;;; AS 5 extra: dN(a, b) ↔ dS(b, a)
    ;;; AS 6 S (a, b) ∧ ¬dN(b, c) ∧ S (c, a) → ⊥;
    ;;; AS 7 ¬N(a, b) ∧ dS (b, c) ∧ ¬N(c, a) → ⊥;
    ;;; AS 8 S (a, b) ∧ ¬N(b, c) ∧ S(c, d) ∧ ¬N(d, a) → ⊥;
    ;;; AS 9 S (a, b) ∧ ¬N(b, c) ∧ ¬dN(c, d) ∧ dS (d, a) → ⊥;
    ;;; AS 10 ¬N(a, b) ∧ S (b, c) ∧ dS (c, d) ∧ ¬dN(d, a) → ⊥;
    ;;; AS 11 dS (a, b) ∧ ¬dN(b, c) ∧ dS (c, d) ∧ ¬dN(d, a) → ⊥;
    ;;; AS 12 dS (a, b) ∧ ¬dN(b, c) ∧ ¬dN(c, d) ∧ dS (d, a) → ⊥;

    ;;; or: ¬N(a,b) == nNS(a,b) ∨ S(a,b)
    ;;;     ¬dN(a,b) == Ins(a,b) ∨ dS(a,b)

;;; AS 1 ¬S (a, a);
	RULE NS_axiom_1
	[S ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'NS_axiom_1 Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]

	;;; AS 2 N(a, b) ↔ S (b, a);
	RULE NS_axiom_2_1
	[N ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([S ^B ^A])]]
    ==>
	[SAYIF ld 'NS_axiom_2_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

/*
	RULE NS_axiom_2_2
	[S ?B ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([N ^A ^B])]]
    ==>
	[SAYIF ld 'NS_axiom_2_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
*/

    ;;; AS 3 Ins (a, b) → Ins (b, a);
	RULE NS_axiom_3
	[Ins ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([Ins ^B ^A])]]
    ==>
	[SAYIF ld 'NS_axiom_3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	
    ;;; AS 4 Ins(a, b) ↔ (¬dN(a, b) ∧ ¬dS (a, b)) == ¬(dN(a, b) ∨ dS(a, b))
	;;; AS 4a Ins(a, b) ^ (dN(a, b) ∨ dS(a, b)) → bot
    RULE NS_axiom_4_1
	[Ins ?A ?B] [->> a1]
	[dN ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_4_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE NS_axiom_4_2
	[Ins ?A ?B] [->> a1]
	[dS ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_4_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

    ;;; AS 5 dN(a, b) ↔ dS(b,a)
	RULE NS_axiom_5_1
	[dN ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dS ^B ^A])]]
    ==>
	[SAYIF ld 'NS_axiom_5_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

/*	
	RULE NS_axiom_5_2
	[dS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    [LVARS [consequent = add_new_formula([dN ^B ^A])]]
    ==>
	[SAYIF ld 'NS_axiom_5_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
*/

    ;;; AS 6 S (a, b) ∧ ¬dN(b, c) ∧ S (c, a) → ⊥;
    ;;; AS 6 S (a, b) ∧ (Ins(b,c) ∨ dS(b,c)) ∧ S (c, a) → ⊥; 
	RULE NS_axiom_6_1
	[S ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_6_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE NS_axiom_6_2
	[S ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[S ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

    ;;; AS 7 ¬N(a, b) ∧ dS (b, c) ∧ ¬N(c, a) → ⊥;
    ;;; (nNS(a,b) ∨ S(a,b)) ∧ dS (b,c) ∧ (nNS(c,a) ∨ S(c,a)) → ⊥;
	RULE NS_axiom_7_1
	[nNS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[nNS ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_7_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	RULE NS_axiom_7_2
	[nNS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[S ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_7_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	RULE NS_axiom_7_3
	[S ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[nNS ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_7_3 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

/*
	RULE NS_axiom_7_4
	[S ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[S ?C ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_7_4 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
*/

    ;;; AS 8 S (a, b) ∧ ¬N(b, c) ∧ S(c, d) ∧ ¬N(d, a) → ⊥;
    ;;; S (a, b) ∧ (nNS(b, c) ∨ S(b, c)) ∧ S(c, d) ∧ (nNS(d, a) ∨ S(d, a)) → ⊥;
	RULE NS_axiom_8_1
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
    [nNS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_8_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_8_2
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
    [S ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_8_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_8_3
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
    [nNS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_8_3 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;; new_deleted_rule_01
/*
	RULE NS_axiom_8_4
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
    [S ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_8_4 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
/*
    ;;; AS 9 S (a, b) ∧ ¬N(b, c) ∧ ¬dN(c, d) ∧ dS (d, a) → ⊥;
    ;;; S (a, b) ∧ (nNS(b, c) ∨ S(b, c)) ∧  (Ins(c, d) ∨ dS(c, d)) ∧ dS (d, a) → ⊥;
	RULE NS_axiom_9_1
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[Ins ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_9_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_9_2
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_9_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;; new_deleted_rule_02 new_deleted_rule_03
/*
	RULE NS_axiom_9_3
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[Ins ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_9_3 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_9_4
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_9_4 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/
    ;;; AS 10 ¬N(a, b) ∧ S (b, c) ∧ dS (c, d) ∧ ¬dN(d, a) → ⊥;
    ;;; (nNS(a, b) ∨ S(a, b)) ∧ S (b, c) ∧ dS (c, d) ∧(Ins(d, a) ∨ dS(d, a)) → ⊥;
	RULE NS_axiom_10_1
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [Ins ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_10_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_10_2
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_10_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
;;; new_deleted_rule_04
/*
	RULE NS_axiom_10_3
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [Ins ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_10_3 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/
/*
	RULE NS_axiom_10_4
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_10_4 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/

    ;;; AS 11 dS (a, b) ∧ ¬dN(b, c) ∧ dS (c, d) ∧ ¬dN(d, a) → ⊥;
    ;;; dS (a, b) ∧ (Ins(b, c) ∨ dS(b, c)) ∧ dS (c, d) ∧ (Ins(d, a) ∨ dS(d, a)) → ⊥;
	RULE NS_axiom_11_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [Ins ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_11_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_11_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_11_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE NS_axiom_11_3
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [Ins ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_11_3 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/
	RULE NS_axiom_11_4
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_11_4 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/
    ;;; AS 12 dS (a, b) ∧ ¬dN(b, c) ∧ ¬dN(c, d) ∧ dS (d, a) → ⊥;
    ;;; dS (a, b) ∧ (Ins(b, c) ∨ dS(b, c)) ∧ (Ins(c, d) ∨ dS(c, d)) ∧ dS (d, a) → ⊥;
	RULE NS_axiom_12_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[Ins ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_12_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

/*
	RULE NS_axiom_12_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_12_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
*/

	RULE NS_axiom_12_3
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[Ins ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_12_3 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


	RULE NS_axiom_12_4
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
    [dS ?D ?A] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_12_4 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]


enddefine;

;;; LD_rules ends here
vars LD_rules = true;
