/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;记得改这个vars
vars ns_ld_ruleset;

;;; LD rules
;;; S and N rules

;;; AS 1 ¬S (a, a);
;;; AS 2 N(a, b) ↔ S (b, a);
;;; AS 3 Ins (a, b) → Ins (b, a);
;;; AS 4 Ins(a, b) ↔ (¬dN(a, b) ∧ ¬dS (a, b)) == ¬(dN(a, b) ∨ dS(a, b))
;;; AS 5 S(a,b) ∧ S(b,c) → S(a,c)
;;; AS 6 ¬dN(a,b) ∧ S(b,c) → ¬N(a,c)
;;; AS 7 S(a,b) ∧ ¬dN(b,c) → ¬N(a,c)
;;; AS 8 dS(a,b) ∧ ¬N(b,c) → S(a,c)
;;; AS 9 ¬N(a,b) ∧ dS(b,c) → S(a,c)

define :ruleset ns_ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;; N/S/dN/dS/nNS/Ins needs converse
;;; E变W，W变E，dE变dW，dW变dE，同时字母位置互换，nEW和Iew只需字母位置互换
 
	RULE NS_axiom_1a
	[S ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'NS_1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE NS_axiom_1b
	[N ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'NS_1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]

;;; 11 12 21 22; 111 112 121 122 211 212 221 222
;;; a表示是第几个变体公式，a前面的数字是第几个axioms，a后面的数字是此变体公式的第几次转换order
    RULE NS_axiom_4a_1
	[Ins ?A ?B] [->> a1]
	[dN ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4a_2
	[Ins ?A ?B] [->> a1]
	[dS ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4a_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4a_3
	[Ins ?B ?A] [->> a1]
	[dN ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4a_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4a_4
	[Ins ?B ?A] [->> a1]
	[dS ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4a_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE NS_axiom_4b_1
	[Ins ?A ?B] [->> a1]
	[dS ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4b_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4b_2
	[Ins ?A ?B] [->> a1]
	[dN ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4b_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4b_3
	[Ins ?B ?A] [->> a1]
	[dS ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4b_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE NS_axiom_4b_4
	[Ins ?B ?A] [->> a1]
	[dN ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_4b_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
	
	;;; AS 5 S(a,b) ∧ S(b,c) → S(a,c)
	RULE NS_axiom_5a_1
	[S ?A ?B] [->> a1]
    [S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_5a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_2
	[S ?A ?B] [->> a1]
    [S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_5a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_3
	[S ?A ?B] [->> a1]
    [N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_5a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_4
	[S ?A ?B] [->> a1]
    [N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_5a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_5
	[N ?B ?A] [->> a1]
    [S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_5a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_6
	[N ?B ?A] [->> a1]
    [S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_5a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_7
	[N ?B ?A] [->> a1]
    [N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_5a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_5a_8
	[N ?B ?A] [->> a1]
    [N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_5a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 6 ¬dN(a,b) ∧ S(b,c) → ¬N(a,c)
	;;; AS 6 S(b,c) ∧ N(a,c) → dN(a,b)
	RULE NS_axiom_6a_1
	[S ?B ?C] [->> a1]
    [N ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dN ^A ^B])]]
	==>
	[SAYIF ld 'NS_6a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_2
	[S ?B ?C] [->> a1]
    [N ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dS ^B ^A])]]
	==>
	[SAYIF ld 'NS_6a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_3
	[S ?B ?C] [->> a1]
    [S ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dN ^A ^B])]]
	==>
	[SAYIF ld 'NS_6a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_4
	[S ?B ?C] [->> a1]
    [S ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dS ^B ^A])]]
	==>
	[SAYIF ld 'NS_6a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_5
	[N ?C ?B] [->> a1]
    [N ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dN ^A ^B])]]
	==>
	[SAYIF ld 'NS_6a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_6
	[N ?C ?B] [->> a1]
    [N ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dS ^B ^A])]]
	==>
	[SAYIF ld 'NS_6a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_7
	[N ?C ?B] [->> a1]
    [S ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dN ^A ^B])]]
	==>
	[SAYIF ld 'NS_6a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_6a_8
	[N ?C ?B] [->> a1]
    [S ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dS ^B ^A])]]
	==>
	[SAYIF ld 'NS_6a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 8 dS(a,b) ∧ ¬N(b,c) → S(a,c)
	;;; dS(a,b) ∧ nNS(b,c) → S(a,c) or dS(a,b) ∧ S(b,c) → S(a,c)
	RULE NS_axiom_8a_1
	[dS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_2
	[dS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_3
	[dS ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_4
	[dS ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_5
	[dN ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_6
	[dN ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_7
	[dN ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8a_8
	[dN ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	;;; dS(a,b) ∧ S(b,c) → S(a,c)
	RULE NS_axiom_8b_1
	[dS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_2
	[dS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_3
	[dS ?A ?B] [->> a1]
	[N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_4
	[dS ?A ?B] [->> a1]
	[N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_5
	[dN ?B ?A] [->> a1]
	[S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_6
	[dN ?B ?A] [->> a1]
	[S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_7
	[dN ?B ?A] [->> a1]
	[N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld 'NS_8b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_8b_8
	[dN ?B ?A] [->> a1]
	[N ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([N ^C ^A])]]
	==>
	[SAYIF ld 'NS_8b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬N(a,b) ∧ dS(b,c) → S(a,c)
	;;; nNS(a,b) ∧ dS(b,c) → S(a,c) or S(a,b) ∧ dS(b,c) → S(a,c)
	
	;;; AS 10 S(a,b) ∧ ¬N(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; AS 10_1a:  S(a,b) ∧ nNS(b,c) ∧ S(c,d) -> S(a,d) (16)
	;;; AS 10_1b:  S(a,b) ∧ S(b,c) ∧ S(c,d) -> S(a,d) *删掉
	RULE NS_axiom_10_1a_1
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_2
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_3
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_4
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([S ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_5
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_6
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_7
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_8
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([S ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_9
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_10
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_11
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_12
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([S ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_13
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_14
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_15
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_10_1a_16
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([S ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; 10_2a: S(a,b) ∧ nNS(b,c) ∧ dS(c,d) → dS(a,d),delete
	;;; 10_2b: S(a,c) ∧ dS(c,d) → dS(a,d)
	RULE NS_axiom_10_2b_1
	[S ?A ?C] [->> a1]
	[dS ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_2b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_2
	[S ?A ?C] [->> a1]
	[dS ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_2b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_3
	[S ?A ?C] [->> a1]
	[dN ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_2b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_4
	[S ?A ?C] [->> a1]
	[dN ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_2b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_5
	[N ?C ?A] [->> a1]
	[dS ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_2b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_6
	[N ?C ?A] [->> a1]
	[dS ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_2b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_7
	[N ?C ?A] [->> a1]
	[dN ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_10_2b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_2b_8
	[N ?C ?A] [->> a1]
	[dN ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_10_2b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 10.3a: dS(d,b) ∧ nNS(b,c) -> N(c,d) delete
	;;; AS 10.3b: S(d,a) ∧ S(a,c)  ->  S(d,c) delete
	
	;;; As 10.4a: S(a,b) ∧ nNS(b,c) ∧ dN(a,d) -> dN(c,d)
	RULE NS_axiom_10_4a_1
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_2
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_3
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_4
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_5
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_6
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_7
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_8
	[S ?A ?B] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_9
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_10
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_11
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_12
	[N ?B ?A] [->> a1]
	[nNS ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_13
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_14
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_15
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_4a_16
	[N ?B ?A] [->> a1]
	[nNS ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; As 10.4b: S(a,c) ∧ dN(a,d) -> dN(c,d)
	RULE NS_axiom_10_4b_1
	[S ?A ?C] [->> a1]
	[dN ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_4b_2
	[S ?A ?C] [->> a1]
	[dN ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE NS_axiom_10_4b_3
	[S ?A ?C] [->> a1]
	[dS ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_4b_4
	[S ?A ?C] [->> a1]
	[dS ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_4b_5
	[N ?C ?A] [->> a1]
	[dN ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_4b_6
	[N ?C ?A] [->> a1]
	[dN ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE NS_axiom_10_4b_7
	[N ?C ?A] [->> a1]
	[dS ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_10_4b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_10_4b_8
	[N ?C ?A] [->> a1]
	[dS ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_10_4b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	

	;;; As 11.1a: dS(b,d) ∧ nNS(a,b) -> S(a,d) delete
	;;; AS 11.1b: repeat

	;;; AS 11.2a: nNS(a,b) ∧ dS(b,d) -> S(a,d) delete
	;;; AS 11.2b: repeat

	;;; AS 11.3a: S(b,c) ∧ nNS(a,b) ∧ N(a,d) -> N(c,d)
	RULE NS_axiom_11_3a_1
	[S ?B ?C] [->> a1]
	[nNS ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_2
	[S ?B ?C] [->> a1]
	[nNS ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_11_3a_3
	[S ?B ?C] [->> a1]
	[nNS ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_4
	[S ?B ?C] [->> a1]
	[nNS ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_11_3a_5
	[S ?B ?C] [->> a1]
	[nNS ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_6
	[S ?B ?C] [->> a1]
	[nNS ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_11_3a_7
	[S ?B ?C] [->> a1]
	[nNS ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_8
	[S ?B ?C] [->> a1]
	[nNS ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_11_3a_9
	[N ?C ?B] [->> a1]
	[nNS ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_10
	[N ?C ?B] [->> a1]
	[nNS ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_11_3a_11
	[N ?C ?B] [->> a1]
	[nNS ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_12
	[N ?C ?B] [->> a1]
	[nNS ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_11_3a_13
	[N ?C ?B] [->> a1]
	[nNS ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_14
	[N ?C ?B] [->> a1]
	[nNS ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_11_3a_15
	[N ?C ?B] [->> a1]
	[nNS ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_11_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_11_3a_16
	[N ?C ?B] [->> a1]
	[nNS ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_11_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	;;; AS 11.3b: repeat
	
	;;; AS 11.4a: S(d,b) ∧ S(b,c) -> dN(c,d)，和AS6一样, delete
    ;;; AS 11.4b: 一样
	
	
	;;; AS 12.1a: dS(a,b) ∧ Ins(b,c) ∧ S(c,d) -> S(a,d)
	RULE NS_axiom_12_1a_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_3
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_4
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_5
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_6
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_7
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_8
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_1a_9
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_10
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_11
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_12
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_13
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_14
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_15
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_1a_16
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
    ;;; AS 12.1b: dS(a,b) ∧ S(b,d) -> S(a,d) = AS8 delete
	
	;;; AS 12.2a: dS(a,b) ∧ Ins(b,c) ∧ dS(c,d) -> dS(a,d)
	RULE NS_axiom_12_2a_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_3
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_4
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_5
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_6
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_7
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_8
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_2a_9
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_10
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_11
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_12
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_13
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_14
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_15
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_12_2a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_12_2a_16
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_12_2a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.2b: dS(a,b) ∧ dS(b,c) -> dS(a,c)
	RULE NS_axiom_12_2b_1
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dS ^A ^C])]]
	==>
	[SAYIF ld 'NS_12_2b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_2
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dN ^C ^A])]]
	==>
	[SAYIF ld 'NS_12_2b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_3
	[dS ?A ?B] [->> a1]
	[dN ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dS ^A ^C])]]
	==>
	[SAYIF ld 'NS_12_2b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_4
	[dS ?A ?B] [->> a1]
	[dN ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dN ^C ^A])]]
	==>
	[SAYIF ld 'NS_12_2b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE NS_axiom_12_2b_5
	[dN ?B ?A] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dS ^A ^C])]]
	==>
	[SAYIF ld 'NS_12_2b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_6
	[dN ?B ?A] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dN ^C ^A])]]
	==>
	[SAYIF ld 'NS_12_2b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_7
	[dN ?B ?A] [->> a1]
	[dN ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dS ^A ^C])]]
	==>
	[SAYIF ld 'NS_12_2b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE NS_axiom_12_2b_8
	[dN ?B ?A] [->> a1]
	[dN ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dN ^C ^A])]]
	==>
	[SAYIF ld 'NS_12_2b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 12.3a: dS(a,b) ∧ Ins(b,c) ∧ N(a,d) -> N(c,d)
	RULE NS_axiom_12_3a_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_3
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_4
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_5
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_6
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_7
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_8
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_9
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_10
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_11
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_12
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_13
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_14
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_15
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_16
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.3b: S(d,a) ∧ dS(a,c) -> S(d,c) = AS9，delete
	
	;;; AS 12.4a: dS(a,b) ∧ Ins(b,c) ∧ dN(a,d) -> dN(c,d)
	RULE NS_axiom_12_3a_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_2
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_3
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_4
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_5
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_6
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_7
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_8
	[dS ?A ?B] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_9
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_10
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_11
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_12
	[dN ?B ?A] [->> a1]
	[Ins ?B ?C] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_13
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_14
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_15
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_12_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_12_3a_16
	[dN ?B ?A] [->> a1]
	[Ins ?C ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_12_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.4b: 和AS12.2b一样,delete
	
	;;; for AS 13, a式都没办法改动，b式和12都一样
	;;; AS 13.1a: dS(b,c) ∧ Ins(a,b) ∧ S(c,d) -> S(a,d)
	RULE NS_axiom_13_1a_1
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_2
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_3
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_4
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_5
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_6
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_7
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_8
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_9
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_10
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_11
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_12
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_13
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_14
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_15
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_1a_16
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([N ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13.2a: dS(b,c) ∧ Ins(a,b) ∧ dS(c,d) -> dS(a,d)
	RULE NS_axiom_13_2a_1
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_2
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_3
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_4
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_5
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_6
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_7
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_8
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_9
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_10
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_11
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_12
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_13
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_14
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_15
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld 'NS_13_2a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE NS_axiom_13_2a_16
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dN ^D ^A])]]
	==>
	[SAYIF ld 'NS_13_2a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	;;; AS 13.3a: dS(b,c) ∧ Ins(a,b) ∧ N(a,d) -> N(c,d)
	RULE NS_axiom_13_3a_1
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_2
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_3a_3
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_4
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_5
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_6
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_3a_7
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_8
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_13_3a_9
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_10
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_3a_11
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_12
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_13
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_14
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[N ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_3a_15
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([N ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_3a_16
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[S ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([S ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13.4a: dS(b,c) ∧ Ins(a,b) ∧ dN(a,d) -> dN(c,d)
	RULE NS_axiom_13_4a_1
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_2
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_4a_3
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_4
	[dS ?B ?C] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_5
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_6
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_4a_7
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_8
	[dS ?B ?C] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_13_4a_9
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_10
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_4a_11
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_12
	[dN ?C ?B] [->> a1]
	[Ins ?A ?B] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_13
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_14
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dN ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE NS_axiom_13_4a_15
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dN ^C ^D])]]
	==>
	[SAYIF ld 'NS_13_4a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE NS_axiom_13_4a_16
	[dN ?C ?B] [->> a1]
	[Ins ?B ?A] [->> a2]
	[dS ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dS ^D ^C])]]
	==>
	[SAYIF ld 'NS_13_4a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

/*
	RULE NS_axiom_S_1
    [S ?A ?B] [->> a1]
	[S ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_S_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_S_2
    [S ?A ?B] [->> a1]
	[N ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_S_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_S_3
    [N ?B ?A] [->> a1]
	[S ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_S_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_S_4
    [N ?B ?A] [->> a1]
	[N ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_N_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_dS_1
    [dS ?A ?B] [->> a1]
	[dS ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_dS_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_dS_2
    [dS ?A ?B] [->> a1]
	[dN ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_dS_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_dS_3
    [dN ?B ?A] [->> a1]
	[dS ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_dS_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE NS_axiom_dS_4
    [dN ?B ?A] [->> a1]
	[dN ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_dN_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
*/

enddefine;

;;; LD_rules ends here
vars LD_rules = true;

