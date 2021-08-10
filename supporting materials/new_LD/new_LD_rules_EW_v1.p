/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;记得改这个vars
vars ew_ld_ruleset;

;;; LD rules
;;; W and E rules

;;; AS 1 ¬W (a, a);
;;; AS 2 E(a, b) ↔ W (b, a);
;;; AS 3 Iew (a, b) → Iew (b, a);
;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b)) == ¬(dE(a, b) ∨ dW(a, b))
;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
;;; AS 7 W(a,b) ∧ ¬dE(b,c) → ¬E(a,c)
;;; AS 8 dW(a,b) ∧ ¬E(b,c) → W(a,c)
;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)

define :ruleset ew_ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;; E/W/dE/dW/nEW/Iew needs converse
;;; E变W，W变E，dE变dW，dW变dE，同时字母位置互换，nEW和Iew只需字母位置互换
 
	RULE EW_axiom_1a
	[W ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'EW_1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE EW_axiom_1b
	[E ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'EW_1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]

;;; 11 12 21 22; 111 112 121 122 211 212 221 222
;;; a表示是第几个变体公式，a前面的数字是第几个axioms，a后面的数字是此变体公式的第几次转换order
    RULE EW_axiom_4a_1
	[Iew ?A ?B] [->> a1]
	[dE ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4a_2
	[Iew ?A ?B] [->> a1]
	[dW ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4a_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4a_3
	[Iew ?B ?A] [->> a1]
	[dE ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4a_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4a_4
	[Iew ?B ?A] [->> a1]
	[dW ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4a_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE EW_axiom_4b_1
	[Iew ?A ?B] [->> a1]
	[dW ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4b_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4b_2
	[Iew ?A ?B] [->> a1]
	[dE ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4b_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4b_3
	[Iew ?B ?A] [->> a1]
	[dW ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4b_3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
    RULE EW_axiom_4b_4
	[Iew ?B ?A] [->> a1]
	[dE ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_4b_4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
	
	;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
	RULE EW_axiom_5a_1
	[W ?A ?B] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_5a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_2
	[W ?A ?B] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_5a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_3
	[W ?A ?B] [->> a1]
    [E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_5a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_4
	[W ?A ?B] [->> a1]
    [E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_5a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_5
	[E ?B ?A] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_5a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_6
	[E ?B ?A] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_5a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_7
	[E ?B ?A] [->> a1]
    [E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_5a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_5a_8
	[E ?B ?A] [->> a1]
    [E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_5a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
	;;; AS 6 W(b,c) ∧ E(a,c) → dE(a,b)
	RULE EW_axiom_6a_1
	[W ?B ?C] [->> a1]
    [E ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dE ^A ^B])]]
	==>
	[SAYIF ld 'EW_6a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_2
	[W ?B ?C] [->> a1]
    [E ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dW ^B ^A])]]
	==>
	[SAYIF ld 'EW_6a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_3
	[W ?B ?C] [->> a1]
    [W ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dE ^A ^B])]]
	==>
	[SAYIF ld 'EW_6a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_4
	[W ?B ?C] [->> a1]
    [W ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dW ^B ^A])]]
	==>
	[SAYIF ld 'EW_6a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_5
	[E ?C ?B] [->> a1]
    [E ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dE ^A ^B])]]
	==>
	[SAYIF ld 'EW_6a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_6
	[E ?C ?B] [->> a1]
    [E ?A ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dW ^B ^A])]]
	==>
	[SAYIF ld 'EW_6a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_7
	[E ?C ?B] [->> a1]
    [W ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, B)]
	[LVARS [consequent = add_new_formula([dE ^A ^B])]]
	==>
	[SAYIF ld 'EW_6a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_6a_8
	[E ?C ?B] [->> a1]
    [W ?C ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(B, A)]
	[LVARS [consequent = add_new_formula([dW ^B ^A])]]
	==>
	[SAYIF ld 'EW_6a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 8 dW(a,b) ∧ ¬E(b,c) → W(a,c)
	;;; dW(a,b) ∧ nEW(b,c) → W(a,c) or dW(a,b) ∧ W(b,c) → W(a,c)
	RULE EW_axiom_8a_1
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8a_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_2
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8a_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_3
	[dW ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8a_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_4
	[dW ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8a_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_5
	[dE ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8a_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_6
	[dE ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8a_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_7
	[dE ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8a_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8a_8
	[dE ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8a_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	;;; dW(a,b) ∧ W(b,c) → W(a,c)
	RULE EW_axiom_8b_1
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_3
	[dW ?A ?B] [->> a1]
	[E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_4
	[dW ?A ?B] [->> a1]
	[E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_5
	[dE ?B ?A] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_6
	[dE ?B ?A] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_7
	[dE ?B ?A] [->> a1]
	[E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld 'EW_8b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8b_8
	[dE ?B ?A] [->> a1]
	[E ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([E ^C ^A])]]
	==>
	[SAYIF ld 'EW_8b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)
	;;; nEW(a,b) ∧ dW(b,c) → W(a,c) or W(a,b) ∧ dW(b,c) → W(a,c)
	
	;;; AS 10 W(a,b) ∧ ¬E(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; AS 10_1a:  W(a,b) ∧ nEW(b,c) ∧ W(c,d) -> W(a,d) (16)
	;;; AS 10_1b:  W(a,b) ∧ W(b,c) ∧ W(c,d) -> W(a,d) *删掉
	RULE EW_axiom_10_1a_1
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_2
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_3
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_4
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([W ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_5
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_6
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_7
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_8
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([W ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_9
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_10
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_11
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_12
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([W ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_13
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_14
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_15
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_1a_16
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([W ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; 10_2a: W(a,b) ∧ nEW(b,c) ∧ dW(c,d) → dW(a,d),delete
	;;; 10_2b: W(a,c) ∧ dW(c,d) → dW(a,d)
	RULE EW_axiom_10_2b_1
	[W ?A ?C] [->> a1]
	[dW ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_2b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_2
	[W ?A ?C] [->> a1]
	[dW ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_2b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_3
	[W ?A ?C] [->> a1]
	[dE ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_2b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_4
	[W ?A ?C] [->> a1]
	[dE ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_2b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_5
	[E ?C ?A] [->> a1]
	[dW ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_2b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_6
	[E ?C ?A] [->> a1]
	[dW ?C ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_2b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_7
	[E ?C ?A] [->> a1]
	[dE ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_10_2b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_2b_8
	[E ?C ?A] [->> a1]
	[dE ?D ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_10_2b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 10.3a: dW(d,b) ∧ nEW(b,c) -> E(c,d) delete
	;;; AS 10.3b: W(d,a) ∧ W(a,c)  ->  W(d,c) delete
	
	;;; As 10.4a: W(a,b) ∧ nEW(b,c) ∧ dE(a,d) -> dE(c,d)
	RULE EW_axiom_10_4a_1
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_2
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_3
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_4
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_5
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_6
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_7
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_8
	[W ?A ?B] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_9
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_10
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_11
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_12
	[E ?B ?A] [->> a1]
	[nEW ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_13
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_14
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_15
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_10_4a_16
	[E ?B ?A] [->> a1]
	[nEW ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; As 10.4b: W(a,c) ∧ dE(a,d) -> dE(c,d)
	RULE EW_axiom_10_4b_1
	[W ?A ?C] [->> a1]
	[dE ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_4b_2
	[W ?A ?C] [->> a1]
	[dE ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_10_4b_3
	[W ?A ?C] [->> a1]
	[dW ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_4b_4
	[W ?A ?C] [->> a1]
	[dW ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_4b_5
	[E ?C ?A] [->> a1]
	[dE ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_4b_6
	[E ?C ?A] [->> a1]
	[dE ?A ?D] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_10_4b_7
	[E ?C ?A] [->> a1]
	[dW ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_10_4b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_10_4b_8
	[E ?C ?A] [->> a1]
	[dW ?D ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_10_4b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	

	;;; As 11.1a: dW(b,d) ∧ nEW(a,b) -> W(a,d) delete
	;;; AS 11.1b: repeat

	;;; AS 11.2a: nEW(a,b) ∧ dW(b,d) -> W(a,d) delete
	;;; AS 11.2b: repeat

	;;; AS 11.3a: W(b,c) ∧ nEW(a,b) ∧ E(a,d) -> E(c,d)
	RULE EW_axiom_11_3a_1
	[W ?B ?C] [->> a1]
	[nEW ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_2
	[W ?B ?C] [->> a1]
	[nEW ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_11_3a_3
	[W ?B ?C] [->> a1]
	[nEW ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_4
	[W ?B ?C] [->> a1]
	[nEW ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_11_3a_5
	[W ?B ?C] [->> a1]
	[nEW ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_6
	[W ?B ?C] [->> a1]
	[nEW ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_11_3a_7
	[W ?B ?C] [->> a1]
	[nEW ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_8
	[W ?B ?C] [->> a1]
	[nEW ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_11_3a_9
	[E ?C ?B] [->> a1]
	[nEW ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_10
	[E ?C ?B] [->> a1]
	[nEW ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_11_3a_11
	[E ?C ?B] [->> a1]
	[nEW ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_12
	[E ?C ?B] [->> a1]
	[nEW ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_11_3a_13
	[E ?C ?B] [->> a1]
	[nEW ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_14
	[E ?C ?B] [->> a1]
	[nEW ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_11_3a_15
	[E ?C ?B] [->> a1]
	[nEW ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_11_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3a_16
	[E ?C ?B] [->> a1]
	[nEW ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_11_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	;;; AS 11.3b: repeat
	
	;;; AS 11.4a: W(d,b) ∧ W(b,c) -> dE(c,d)，和AS6一样, delete
    ;;; AS 11.4b: 一样
	
	
	;;; AS 12.1a: dW(a,b) ∧ Iew(b,c) ∧ W(c,d) -> W(a,d)
	RULE EW_axiom_12_1a_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_2
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_4
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_5
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_6
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_7
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_8
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_1a_9
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_10
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_11
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_12
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_13
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_14
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_15
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_1a_16
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
    ;;; AS 12.1b: dW(a,b) ∧ W(b,d) -> W(a,d) = AS8 delete
	
	;;; AS 12.2a: dW(a,b) ∧ Iew(b,c) ∧ dW(c,d) -> dW(a,d)
	RULE EW_axiom_12_2a_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_2
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_4
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_5
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_6
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_7
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_8
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_2a_9
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_10
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_11
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_12
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_13
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_14
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_15
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_12_2a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_12_2a_16
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_12_2a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.2b: dW(a,b) ∧ dW(b,c) -> dW(a,c)
	RULE EW_axiom_12_2b_1
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dW ^A ^C])]]
	==>
	[SAYIF ld 'EW_12_2b_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dE ^C ^A])]]
	==>
	[SAYIF ld 'EW_12_2b_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_3
	[dW ?A ?B] [->> a1]
	[dE ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dW ^A ^C])]]
	==>
	[SAYIF ld 'EW_12_2b_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_4
	[dW ?A ?B] [->> a1]
	[dE ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dE ^C ^A])]]
	==>
	[SAYIF ld 'EW_12_2b_4 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_12_2b_5
	[dE ?B ?A] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dW ^A ^C])]]
	==>
	[SAYIF ld 'EW_12_2b_5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_6
	[dE ?B ?A] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dE ^C ^A])]]
	==>
	[SAYIF ld 'EW_12_2b_6 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_7
	[dE ?B ?A] [->> a1]
	[dE ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(A, C)]
	[LVARS [consequent = add_new_formula([dW ^A ^C])]]
	==>
	[SAYIF ld 'EW_12_2b_7 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]	
	
	RULE EW_axiom_12_2b_8
	[dE ?B ?A] [->> a1]
	[dE ?C ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db) and alphabefore(C, A)]
	[LVARS [consequent = add_new_formula([dE ^C ^A])]]
	==>
	[SAYIF ld 'EW_12_2b_8 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 12.3a: dW(a,b) ∧ Iew(b,c) ∧ E(a,d) -> E(c,d)
	RULE EW_axiom_12_3a_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_2
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_4
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_5
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_6
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_7
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_8
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_9
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_10
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_11
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_12
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_13
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_14
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_15
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_16
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.3b: W(d,a) ∧ dW(a,c) -> W(d,c) = AS9，delete
	
	;;; AS 12.4a: dW(a,b) ∧ Iew(b,c) ∧ dE(a,d) -> dE(c,d)
	RULE EW_axiom_12_3a_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_2
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_4
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_5
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_6
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_7
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_8
	[dW ?A ?B] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_9
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_10
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_11
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_12
	[dE ?B ?A] [->> a1]
	[Iew ?B ?C] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_13
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_14
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_15
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_12_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3a_16
	[dE ?B ?A] [->> a1]
	[Iew ?C ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_12_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12.4b: 和AS12.2b一样,delete
	
	;;; for AS 13, a式都没办法改动，b式和12都一样
	;;; AS 13.1a: dW(b,c) ∧ Iew(a,b) ∧ W(c,d) -> W(a,d)
	RULE EW_axiom_13_1a_1
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_2
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_3
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_4
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_5
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_6
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_7
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_8
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_9
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_10
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_11
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_12
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_13
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_14
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_15
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_1a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_1a_16
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([E ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_1a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13.2a: dW(b,c) ∧ Iew(a,b) ∧ dW(c,d) -> dW(a,d)
	RULE EW_axiom_13_2a_1
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_2
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_3
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_4
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_5
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_6
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_7
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_8
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_9
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_10
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_11
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_12
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_13
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_14
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_15
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(A, D)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld 'EW_13_2a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2a_16
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?D ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, A)]
	[LVARS [consequent = add_new_formula([dE ^D ^A])]]
	==>
	[SAYIF ld 'EW_13_2a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	;;; AS 13.3a: dW(b,c) ∧ Iew(a,b) ∧ E(a,d) -> E(c,d)
	RULE EW_axiom_13_3a_1
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_2
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_3a_3
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_4
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_5
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_6
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_3a_7
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_8
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_13_3a_9
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_10
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_3a_11
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_12
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_13
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_14
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[E ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_3a_15
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([E ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_3a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_3a_16
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[W ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([W ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_3a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13.4a: dW(b,c) ∧ Iew(a,b) ∧ dE(a,d) -> dE(c,d)
	RULE EW_axiom_13_4a_1
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_2
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_4a_3
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_4
	[dW ?B ?C] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_5
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_5 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_6
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_6 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_4a_7
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_7 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_8
	[dW ?B ?C] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_8 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE EW_axiom_13_4a_9
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_9 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_10
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_10 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_4a_11
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_11 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_12
	[dE ?C ?B] [->> a1]
	[Iew ?A ?B] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_12 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_13
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_13 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_14
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dE ?A ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_14 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_13_4a_15
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(C, D)]
	[LVARS [consequent = add_new_formula([dE ^C ^D])]]
	==>
	[SAYIF ld 'EW_13_4a_15 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	
	
	RULE EW_axiom_13_4a_16
	[dE ?C ?B] [->> a1]
	[Iew ?B ?A] [->> a2]
	[dW ?D ?A] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db) and alphabefore(D, C)]
	[LVARS [consequent = add_new_formula([dW ^D ^C])]]
	==>
	[SAYIF ld 'EW_13_4a_16 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]	

	RULE EW_axiom_W_Inconsistent
    [W ?A ?B] [->> a1]
	[W ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_W_Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE EW_axiom_E_Inconsistent
    [E ?A ?B] [->> a1]
	[E ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_E_Inconsistent Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE EW_axiom_dW_Inconsistent
    [dW ?A ?B] [->> a1]
	[dW ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_dW_Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

	RULE EW_axiom_dE_Inconsistent
    [dE ?A ?B] [->> a1]
	[dE ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'EW_axiom_dE_Inconsistent Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]

enddefine;

;;; LD_rules ends here
vars LD_rules = true;
