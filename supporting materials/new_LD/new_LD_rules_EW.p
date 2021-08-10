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

/*
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; particle converse 
	RULE nEW
	[nEW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([nEW ^B ^A])]]
    ==>
	[SAYIF ld 'nEW Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]
	
	RULE EW_axiom_2_a
	[E ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^B ^A])]]
	==>
	[SAYIF ld '2_a Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
    	RULE EW_axiom_2_b
	[W ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([E ^B ^A])]]
	==>
	[SAYIF ld '2_b Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE EW_axiom_2_c
	[dE ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^B ^A])]]
	==>
	[SAYIF ld '2_c Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
    	RULE EW_axiom_2_d
	[dW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([dE ^B ^A])]]
	==>
	[SAYIF ld '2_d Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
	;;; 会不会把同一个formula加两次？ 用这个还是用alphabefore？ （用重复的formula似乎也没关系）
    ;;; AS 3 Iew (a, b) → Iew (b, a);	
    	RULE EW_axiom_3
	[Iew ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([Iew ^B ^A])]]
	==>
	[SAYIF ld '3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
*/

	RULE EW_axiom_1a
	[W ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE EW_axiom_1b
	[E ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
    ;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b)) == ¬(dE(a, b) ∨ dW(a, b))
	;;; AS 4a Iew(a, b) ^ (dE(a, b) ∨ dW(a, b)) → bot
	;;; 不知道or+[->> a1]能不能运行：不能！解决方法：把OR拆成两个rules
    RULE EW_axiom_4a_1
	[IEW ?A ?B] [->> a1]
	[dE ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld '4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE EW_axiom_4a_2
	[IEW ?A ?B] [->> a1]
	[dW ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld '4a_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
	
	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	;;; 逆否命题等价，否命题不等价： A -> B 是否等价于 ¬A -> ¬B？
    ;;; (¬dE(a, b) ∧ ¬dW (a, b)) → Iew(a, b)
	;;; 这里用的NOT！加不了->>a
    ;;;RULE EW_axiom_4b
	;;;[NOT dE ?A ?B]
	;;;[NOT dW ?A ?B]
	;;;[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	;;;[LVARS [consequent = add_new_formula([Iew ^A ^B])]]
	;;;==>
	;;;[SAYIF ld '4b Justifying datum' ?consequent]
	;;;[ATMS_JUSTIFY ?consequent]
    
    ;;;alphabefore 根据add new formula来决定
    ;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
	RULE EW_axiom_5
	[W ?A ?B] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
	;;; AS 6 (Iew(a,b) ∨ dW(a,b)) ∧ W(b,c) ∧ E(a,c) → bot
	RULE EW_axiom_6_1
	[Iew ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE EW_axiom_6_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	;;; AS 7 W(a,b) ∧ ¬dE(b,c) → ¬E(a,c)
	;;; AS 7 W(a,b) ∧ (Iew(b,c) ∨ dW(b,c)) ∧ E(a,c) → bot
	RULE EW_axiom_7_1
	[W ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '7_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE EW_axiom_7_2
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '7_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	;;; 怎么处理¬E：用nEW ∨ W ？
	;;; AS 8 dW(a,b) ∧ ¬E(b,c) → W(a,c)
	;;; dW(a,b) ∧ nEW(b,c) or dW(a,b) ∧ W(b,c)
	RULE EW_axiom_8_1
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE EW_axiom_8_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)
	;;; nEW(a,b) ∧ dW(b,c) or W(a,b) ∧ dW(b,c)
	RULE EW_axiom_9_1
	[nEW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '9_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE EW_axiom_9_2
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '9_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 10 W(a,b) ∧ ¬E(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	RULE EW_axiom_10_1
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_3
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '10_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_10_4
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '10_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 10 W(a,b) ∧ ¬E(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; W(a,b) ∧ (nEW(b,c) ∨ W(b,c)) ∧ (nEW(c,d) ∨ W(c,d)) ∧ E(a,d) -> bot
	RULE EW_axiom_10_5
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_10_6
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE EW_axiom_10_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_10_8
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 10 W(a,b) ∧ ¬E(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝R = ¬dE
	;;; W(a,b) ∧ (nEW(b,c) ∨ W(b,c)) ∧ (Iew(c,d) ∨ dW(c,d)) ∧ dE(a,d) -> bot
	RULE EW_axiom_10_9
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; Iew(c,d) ∧ dE(a,d) or dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_10_10
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_10_11
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_10_12
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 11 ¬E(a,b) ∧ W(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	RULE EW_axiom_11_1
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_3
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '11_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_11_4
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '11_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 11 ¬E(a,b) ∧ W(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; (nEW(a,b) ∨ W(a,b)) ∧ W(b,c) ∧ (nEW(c,d) ∨ W(c,d)) ∧ E(a,d) -> bot
	RULE EW_axiom_11_5
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_11_6
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE EW_axiom_11_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_11_8
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 11 ¬E(a,b) ∧ W(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝R = ¬dE
	;;; (nEW(b,c) ∨ W(b,c)) ∧ W(a,b) ∧ (Iew(c,d) ∨ dW(c,d)) ∧ dE(a,d) -> bot
	RULE EW_axiom_11_9
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; Iew(c,d) ∧ dE(a,d) or dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_11_10
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_11_11
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_11_12
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 12 dW(a,b) ∧ ¬dE(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; ¬dE = Iew ∨ dW
	RULE EW_axiom_12_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '12_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_12_4
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '12_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12 dW(a,b) ∧ ¬dE(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; dW(a,b) ∧ (Iew(b,c) ∨ dW(b,c)) ∧ (nEW(c,d) ∨ W(c,d)) ∧ E(a,d) -> bot
	RULE EW_axiom_12_5
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_12_6
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE EW_axiom_12_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_12_8
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 12 dW(a,b) ∧ ¬dE(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝R = ¬dE
	;;; dW(a,b) ∧ (Iew(b,c) ∨ dW(b,c)) ∧ (Iew(c,d) ∨ dW(c,d)) ∧ dE(a,d) -> bot
	RULE EW_axiom_12_9
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; Iew(c,d) ∧ dE(a,d) or dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_12_10
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_12_11
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_12_12
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 13 ¬dE(a,b) ∧ dW(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; ¬dE = Iew ∨ dW
	RULE EW_axiom_13_1
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '13_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_3
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '13_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE EW_axiom_13_4
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '13_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13 ¬dE(a,b) ∧ dW(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	;;; (Iew(a,b) ∨ dW(a,b)) ∧ dW(b,c) ∧ (nEW(c,d) ∨ W(c,d)) ∧ E(a,d) -> bot
	RULE EW_axiom_13_5
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_13_6
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE EW_axiom_13_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_13_8
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 13 ¬dE(a,b) ∧ dW(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝R = ¬dE
	;;; (Iew(b,c) ∨ dW(b,c)) ∧ dW(a,b) ∧ (Iew(c,d) ∨ dW(c,d)) ∧ dE(a,d) -> bot
	RULE EW_axiom_13_9
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; Iew(c,d) ∧ dE(a,d) or dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_13_10
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_13_11
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[Iew ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE EW_axiom_13_12
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬dE(c,d) ∧ dE(a,d)  -> bot
	;;; a = Iew(c,d) ∧ dE(a,d) or b = dW(c,d) ∧ dE(a,d) -> bot
	[dW ?C ?D] [->> a3]
	[dE ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
enddefine;

;;; LD_rules ends here
vars LD_rules = true;
