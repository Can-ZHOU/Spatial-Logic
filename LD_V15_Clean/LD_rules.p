/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   new_LD_reasoner.p
 */

;;; τ=2
vars ld_ruleset;

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

define :ruleset ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
    ;;;particle???
    ;;; original is BPT(A,B) ==> BPT(B,A)
	RULE BPT
	[BPT ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([BEQ ^A ^B])]]
    ==>
	[SAYIF ld 'BPT Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]
	
	;;;RULE BEQ
	;;;[BEQ ?A ?B] [->> a1]
	;;;[WHERE some_in_db_p([^a1], trigger_db)]
	;;;[LVARS [consequent=add_new_formula([BEQ ^B ^A])]]
    ;;;==>
	;;;[SAYIF ld 'BEQ Justifying datum' ?consequent ?a1]
	;;;[ATMS_JUSTIFY ?consequent ?a1]
	
	RULE nEW
	[nEW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([nEW ^B ^A])]]
    ==>
	[SAYIF ld 'nEW Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]

	RULE nNS
	[nNS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([nNS ^B ^A])]]
    ==>
	[SAYIF ld 'nNS Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	;;;RULE BEQ1
	;;;[BPT ?A ?B] [->> a1]
	;;;[BPT ?B ?A] [->> a2]
	;;;[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	;;;[LVARS [consequent=add_new_formula([BEQ ^A ^B])]]
   ;;; ==>
	;;;[SAYIF ld 'BEQ1 Justifying datum' ?consequent ?a1 ?a2]
	;;;[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE BEQ2
	[BEQ ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1=add_new_formula([nEW ^A ^B])]]
	[LVARS [consequent2=add_new_formula([nNS ^A ^B])]]
	==>
	[SAYIF ld 'BEQ2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1]
	
	RULE axiom_1a
	[W ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_1b
	[E ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_2_a
	[E ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^B ^A])]]
	==>
	[SAYIF ld '2_a Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
    RULE axiom_2_b
	[W ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([E ^B ^A])]]
	==>
	[SAYIF ld '2_b Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
	;;; 会不会把同一个formula加两次？ 用这个还是用alphabefore？ （用重复的formula似乎也没关系）
    ;;; AS 3 Iew (a, b) → Iew (b, a);	
    RULE axiom_3
	[Iew ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([Iew ^B ^A])]]
	==>
	[SAYIF ld '3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	
    ;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b)) == ¬(dE(a, b) ∨ dW(a, b))
	;;; AS 4a Iew(a, b) ^ (dE(a, b) ∨ dW(a, b)) → bot
	;;; 不知道or+[->> a1]能不能运行：不能！解决方法：把OR拆成两个rules
    RULE axiom_4a_1
	[IEW ?A ?B] [->> a1]
	[dE ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld '4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE axiom_4a_2
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
    ;;;RULE axiom_4b
	;;;[NOT dE ?A ?B]
	;;;[NOT dW ?A ?B]
	;;;[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	;;;[LVARS [consequent = add_new_formula([Iew ^A ^B])]]
	;;;==>
	;;;[SAYIF ld '4b Justifying datum' ?consequent]
	;;;[ATMS_JUSTIFY ?consequent]
    
    ;;;alphabefore 根据add new formula来决定
    ;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
	RULE axiom_5
	[W ?A ?B] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
	;;; AS 6 (Iew(a,b) ∨ dW(a,b)) ∧ W(b,c) ∧ E(a,c) → bot
	RULE axiom_6_1
	[Iew ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_6_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	;;; AS 7 W(a,b) ∧ ¬dE(b,c) → ¬E(a,c)
	;;; AS 7 W(a,b) ∧ (Iew(b,c) ∨ dW(b,c)) ∧ E(a,c) → bot
	RULE axiom_7_1
	[W ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '7_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_7_2
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
	RULE axiom_8_1
	[dW ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE axiom_8_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)
	;;; nEW(a,b) ∧ dW(b,c) or W(a,b) ∧ dW(b,c)
	RULE axiom_9_1
	[nEW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '9_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE axiom_9_2
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF ld '9_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 10 W(a,b) ∧ ¬E(b,c) ∧ R(c,d) -> R(a,d), where R∈｛W,dW,¬E,¬dE｝
	RULE axiom_10_1
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_3
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '10_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_4
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
	RULE axiom_10_5
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_6
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_10_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_8
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
	RULE axiom_10_9
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
	
	RULE axiom_10_10
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
	
	RULE axiom_10_11
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
	
	RULE axiom_10_12
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
	RULE axiom_11_1
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_3
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '11_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_4
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
	RULE axiom_11_5
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_6
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_11_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_8
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
	RULE axiom_11_9
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
	
	RULE axiom_11_10
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
	
	RULE axiom_11_11
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
	
	RULE axiom_11_12
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
	RULE axiom_12_1
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '12_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_4
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
	RULE axiom_12_5
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_6
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_12_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_8
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
	RULE axiom_12_9
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
	
	RULE axiom_12_10
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
	
	RULE axiom_12_11
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
	
	RULE axiom_12_12
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
	RULE axiom_13_1
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF ld '13_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_3
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF ld '13_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_4
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
	RULE axiom_13_5
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_6
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_13_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_8
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
	RULE axiom_13_9
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
	
	RULE axiom_13_10
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
	
	RULE axiom_13_11
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
	
	RULE axiom_13_12
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


;;; S and N rules
;;; LD rules
;;; AS 1 ¬S (a, a);
;;; AS 2 N(a, b) ↔ S (b, a);
;;; AS 3 Ins (a, b) → Ins (b, a);
;;; AS 4 Ins(a, b) ↔ (¬dN(a, b) ∧ ¬dS (a, b)) == ¬(dN(a, b) ∨ dS(a, b))
;;; AS 5 S(a,b) ∧ S(b,c) → S(a,c)
;;; AS 6 ¬dN(a,b) ∧ S(b,c) → ¬N(a,c)
;;; AS 7 S(a,b) ∧ ¬dN(b,c) → ¬N(a,c)
;;; AS 8 dS(a,b) ∧ ¬N(b,c) → S(a,c)
;;; AS 9 ¬N(a,b) ∧ dS(b,c) → S(a,c)

	;;; 用不用把其他三个方向也写上
	RULE axiom_1a
	[S ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_1b
	[N ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld '1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_2_a
	[N ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^B ^A])]]
	==>
	[SAYIF ld '2_a Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
    RULE axiom_2_b
	[S ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([N ^B ^A])]]
	==>
	[SAYIF ld '2_b Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
	;;; 会不会把同一个formula加两次？ 用这个还是用alphabefore？ （用重复的formula似乎也没关系）
    ;;; AS 3 Ins (a, b) → Ins (b, a);	
    RULE axiom_3
	[Ins ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([Ins ^B ^A])]]
	==>
	[SAYIF ld '3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	
    ;;; AS 4 Ins(a, b) ↔ (¬dN(a, b) ∧ ¬dS (a, b)) == ¬(dN(a, b) ∨ dS(a, b))
	;;; AS 4a Ins(a, b) ^ (dN(a, b) ∨ dS(a, b)) → bot
	;;; 不知道or+[->> a1]能不能运行：不能！解决方法：把OR拆成两个rules
    RULE axiom_4a_1
	[IEW ?A ?B] [->> a1]
	[dN ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld '4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE axiom_4a_2
	[IEW ?A ?B] [->> a1]
	[dS ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld '4a_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
	
	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	;;; 逆否命题等价，否命题不等价： A -> B 是否等价于 ¬A -> ¬B？
    ;;; (¬dN(a, b) ∧ ¬dS (a, b)) → Ins(a, b)
	;;; 这里用的NOT！加不了->>a
    ;;;RULE axiom_4b
	;;;[NOT dN ?A ?B]
	;;;[NOT dS ?A ?B]
	;;;[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	;;;[LVARS [consequent = add_new_formula([Ins ^A ^B])]]
	;;;==>
	;;;[SAYIF ld '4b Justifying datum' ?consequent]
	;;;[ATMS_JUSTIFY ?consequent]
    
    ;;;alphabefore 根据add new formula来决定
    ;;; AS 5 S(a,b) ∧ S(b,c) → S(a,c)
	RULE axiom_5
	[S ?A ?B] [->> a1]
    [S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld '5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 6 ¬dN(a,b) ∧ S(b,c) → ¬N(a,c)
	;;; AS 6 (Ins(a,b) ∨ dS(a,b)) ∧ S(b,c) ∧ N(a,c) → bot
	RULE axiom_6_1
	[Ins ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[N ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_6_2
	[dS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[N ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	;;; AS 7 S(a,b) ∧ ¬dN(b,c) → ¬N(a,c)
	;;; AS 7 S(a,b) ∧ (Ins(b,c) ∨ dS(b,c)) ∧ N(a,c) → bot
	RULE axiom_7_1
	[S ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	[N ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '7_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_7_2
	[S ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[N ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF ld '7_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	;;; 怎么处理¬N：用nEW ∨ S ？
	;;; AS 8 dS(a,b) ∧ ¬N(b,c) → S(a,c)
	;;; dS(a,b) ∧ nNS(b,c) or dS(a,b) ∧ S(b,c)
	RULE axiom_8_1
	[dS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld '8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE axiom_8_2
	[dS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld '8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬N(a,b) ∧ dS(b,c) → S(a,c)
	;;; nNS(a,b) ∧ dS(b,c) or S(a,b) ∧ dS(b,c)
	RULE axiom_9_1
	[nNS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld '9_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE axiom_9_2
	[S ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^C])]]
	==>
	[SAYIF ld '9_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 10 S(a,b) ∧ ¬N(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	RULE axiom_10_1
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_2
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_3
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '10_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_4
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '10_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 10 S(a,b) ∧ ¬N(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; S(a,b) ∧ (nNS(b,c) ∨ S(b,c)) ∧ (nNS(c,d) ∨ S(c,d)) ∧ N(a,d) -> bot
	RULE axiom_10_5
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_6
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_10_7
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_8
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 10 S(a,b) ∧ ¬N(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝R = ¬dN
	;;; S(a,b) ∧ (nNS(b,c) ∨ S(b,c)) ∧ (Ins(c,d) ∨ dS(c,d)) ∧ dN(a,d) -> bot
	RULE axiom_10_9
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; Ins(c,d) ∧ dN(a,d) or dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_10
	[S ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_11
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_12
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '10_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 11 ¬N(a,b) ∧ S(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	RULE axiom_11_1
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_2
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_3
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '11_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_4
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '11_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 11 ¬N(a,b) ∧ S(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; (nNS(a,b) ∨ S(a,b)) ∧ S(b,c) ∧ (nNS(c,d) ∨ S(c,d)) ∧ N(a,d) -> bot
	RULE axiom_11_5
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_6
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_11_7
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_8
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 11 ¬N(a,b) ∧ S(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝R = ¬dN
	;;; (nNS(b,c) ∨ S(b,c)) ∧ S(a,b) ∧ (Ins(c,d) ∨ dS(c,d)) ∧ dN(a,d) -> bot
	RULE axiom_11_9
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; Ins(c,d) ∧ dN(a,d) or dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_10
	[nNS ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_11
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_12
	[S ?A ?B] [->> a1]
	[S ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '11_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 12 dS(a,b) ∧ ¬dN(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; ¬dN = Ins ∨ dS
	RULE axiom_12_1
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_2
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_3
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '12_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_4
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '12_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 12 dS(a,b) ∧ ¬dN(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; dS(a,b) ∧ (Ins(b,c) ∨ dS(b,c)) ∧ (nNS(c,d) ∨ S(c,d)) ∧ N(a,d) -> bot
	RULE axiom_12_5
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_6
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_12_7
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_8
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 12 dS(a,b) ∧ ¬dN(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝R = ¬dN
	;;; dS(a,b) ∧ (Ins(b,c) ∨ dS(b,c)) ∧ (Ins(c,d) ∨ dS(c,d)) ∧ dN(a,d) -> bot
	RULE axiom_12_9
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; Ins(c,d) ∧ dN(a,d) or dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_10
	[dS ?A ?B] [->> a1]
	[Ins ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_11
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_12
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '12_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	;;; AS 13 ¬dN(a,b) ∧ dS(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; ¬dN = Ins ∨ dS
	RULE axiom_13_1
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_2
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=S
	[S ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([S ^A ^D])]]
	==>
	[SAYIF ld '13_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_3
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '13_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_4
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R=dS
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ^A ^D])]]
	==>
	[SAYIF ld '13_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	;;; AS 13 ¬dN(a,b) ∧ dS(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝
	;;; (Ins(a,b) ∨ dS(a,b)) ∧ dS(b,c) ∧ (nNS(c,d) ∨ S(c,d)) ∧ N(a,d) -> bot
	RULE axiom_13_5
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_6
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_13_7
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[nNS ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_8
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬N(c,d) ∧ ¬N(a,d)  -> bot
	[S ?C ?D] [->> a3]
	[N ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	;;; AS 13 ¬dN(a,b) ∧ dS(b,c) ∧ R(c,d) -> R(a,d), where R∈｛S,dS,¬N,¬dN｝R = ¬dN
	;;; (Ins(b,c) ∨ dS(b,c)) ∧ dS(a,b) ∧ (Ins(c,d) ∨ dS(c,d)) ∧ dN(a,d) -> bot
	RULE axiom_13_9
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; Ins(c,d) ∧ dN(a,d) or dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_10
	[Ins ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_11
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[Ins ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_12
	[dS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	;;; R= ¬dN(c,d) ∧ dN(a,d)  -> bot
	;;; a = Ins(c,d) ∧ dN(a,d) or b = dS(c,d) ∧ dN(a,d) -> bot
	[dS ?C ?D] [->> a3]
	[dN ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF ld '13_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
enddefine;

;;; LD_rules ends here
vars LD_rules = true;
