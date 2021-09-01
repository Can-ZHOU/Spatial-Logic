/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules_EW.p
 > Purpose:	        Rules for LD.
 > Author:          Mingda LIU, 2021
 > Documentation:   
 > Related Files:   LD_reasoner.p
 */

;;; τ=2
vars ld_ruleset;

;;; LBPT rules
;;; A0 All tautologies of classical propositional logic
;;; A1 BPT (a, a);
;;; A2 NEAR(a, b) → NEAR(b, a);
;;; A3 FAR(a, b) → FAR(b, a);
;;; A4 BPT (a, b) ∧ BPT (b, c) → NEAR(c, a);
;;; A5 BPT (b, a) ∧ BPT (b, c) → NEAR(c, a);
;;; A6 BPT (b, a) ∧ NEAR(b, c) ∧ BPT (c, d) → ¬FAR(d, a);
;;; A7 NEAR(a, b) ∧ BPT (b, c) ∧ BPT (c, d) → ¬FAR(d, a);
;;; MP Modus ponens: φ, φ → ψ ⊢ ψ.

;;; W and E rules
;;; LD rules
;;; AS 1 ¬W (a, a);
;;; AS 2 E(a, b) ↔ W (b, a);
;;; AS 3 Iew (a, b) → Iew (b, a);
;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b)) == ¬(dE(a, b) ∨ dW(a, b))
;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
;;; AS 7 W(a,b) ∧ ¬dE(b,c) → ¬E(a,c)
;;; AS 8 dW(a,b) ∧ ¬E(b,c) → W(a,c)
;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)

;;; alphabefore()没有必要用在方向上，但是要用在BEQ上
;;; 加上(near far) BPT BEQ的逆。用不用加dE等的逆？

define :ruleset ld_ruleset;
	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	;;;已经加了
	;;;要不要BPT的定义，还要不要加BPT->BEQ的rule
	
	;;;先不加
	;;;LBPT_rule有一个near_far的axiom，这里用不用额外加bot的axiom
	
	;;;alphabefore可以减小数据库，但不elegant
	;;;alphabefore()在new里面用，不在LBPT里面用。但在new里面删掉了前两个rules。用alphabefore()的可能优劣
	
	;;;查一下BPT(A,B)能不能匹配 (A,A)
	;;;先不写额外的axioms
	;;;new里面额外加了许多paper里面没有，但是成立的axioms，例如axiom_4b，axiom_6a，那用不用加
	
	;;;查一下mapping_relation
	;;;new里面多了两个Additional rules for BPT，用不用加
	
	;;;处理or和not的方式
	;;;有一个axiom用了not
	
	;;; LNF
	;;; LNF中运用了把complex argument提升一级的办法来应对not，or，and
	;;; LNF中有许多成立但是没有写在paper中的axioms，用的data format也不一样
	;;; LNF中有一些输出文档，他们也都没有nogood，只有部分有。
	;;; LNF可以run，但是估计LNF的reasoner不能用到LBPT中，格式不同（可以run，但没有reason time）
	
	RULE_BPT
	[BPT ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([BPT ^B ^A])]]
    ==>
	[SAYIF lbpt 'BPT Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]
	
	;;;实际上应该是不用加
	RULE_BEQ
	[BEQ ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([BEQ ^B ^A])]]
    ==>
	[SAYIF lbpt 'BEQ Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]
	
	RULE_nEW
	[nEW ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([nEW ^B ^A])]]
    ==>
	[SAYIF lbpt 'nEW Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]

	RULE_nNS
	[nNS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent=add_new_formula([nNS ^B ^A])]]
    ==>
	[SAYIF lbpt 'nNS Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent ?a1]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE_BEQ1
	[BPT ?A ?B] [->> a1]
	[BPT ?B ?A] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent=add_new_formula([BEQ ^A ^B])]]
    ==>
	[SAYIF lbpt 'BEQ1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE_BEQ2
	[BEQ ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent1=add_new_formula([nEW ^A ^B])]]
	[LVARS [consequent2=add_new_formula([nNS ^A ^B])]]
	==>
	[SAYIF lbpt 'BEQ2 Justifying datum' ?consequent1 ?consequent2 ?a1]
	[ATMS_JUSTIFY [?consequent1 ?consequent2] a1]
	
	;;; 用不用把其他三个方向也写上
	RULE axiom_1a
	[W ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF lbpt '1a Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_1b
	[E ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF lbpt '1b Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]
	
	RULE axiom_2_a
	[E ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^B ^A])]]
	==>
	[SAYIF lbpt '2_a Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
    RULE axiom_2_b
	[W ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([E ^B ^A])]]
	==>
	[SAYIF lbpt '2_b Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
    
	;;; 会不会把同一个formula加两次？ 用这个还是用alphabefore？ （用重复的formula似乎也没关系）
    ;;; AS 3 Iew (a, b) → Iew (b, a);	
    RULE axiom_3
	[Iew ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([Iew ^B ^A])]]
	==>
	[SAYIF lbpt '3 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	
    ;;; AS 4 Iew(a, b) ↔ (¬dE(a, b) ∧ ¬dW (a, b)) == ¬(dE(a, b) ∨ dW(a, b))
	;;; AS 4a Iew(a, b) ^ (dE(a, b) ∨ dW(a, b)) → bot
	;;; 不知道or+[->> a1]能不能运行：不能！解决方法：把OR拆成两个rules
    RULE axiom_4a_1
	[IEW ?A ?B] [->> a1]
	[dE ?A ?B][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF lbpt '4a_1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
    
	RULE axiom_4a_2
	[IEW ?A ?B] [->> a1]
	[dW ?A ?B] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF lbpt '4a_2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]
	
	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	;;; 逆否命题等价，否命题不等价： A -> B 是否等价于 ¬A -> ¬B？
    ;;; (¬dE(a, b) ∧ ¬dW (a, b)) → Iew(a, b)
	;;; 这里用的NOT！加不了->>a
    RULE axiom_4b
	[NOT dE ?A ?B]
	[NOT dW ?A ?B]
	;;;[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([Iew ^A ^B])]]
	==>
	[SAYIF lbpt '4b Justifying datum' ?consequent]
	[ATMS_JUSTIFY ?consequent]
    
    ;;;alphabefore 根据add new formula来决定
    ;;; AS 5 W(a,b) ∧ W(b,c) → W(a,c)
	RULE axiom_5
	[W ?A ?B] [->> a1]
    [W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF lbpt '5 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	;;; AS 6 ¬dE(a,b) ∧ W(b,c) → ¬E(a,c)
	;;; AS 6 (Iew(a,b) ∨ dW(a,b)) ∧ W(b,c) ∧ E(a,c) → bot
	RULE axiom_6_1
	[Iew ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF lbpt '6_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_6_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF lbpt '6_2 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]

	;;; AS 7 W(a,b) ∧ ¬dE(b,c) → ¬E(a,c)
	;;; AS 7 W(a,b) ∧ (Iew(b,c) ∨ dW(b,c)) ∧ E(a,c) → bot
	RULE axiom_7_1
	[W ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF lbpt '7_1 Inconsistent data' ?a1 ?a2 ?a3]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3]
	
	RULE axiom_7_2
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[E ?A ?C] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	==>
    [SAYIF lbpt '7_2 Inconsistent data' ?a1 ?a2 ?a3]
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
	[SAYIF lbpt '8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	RULE axiom_8_2
	[dW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF lbpt '8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]
	
	;;; AS 9 ¬E(a,b) ∧ dW(b,c) → W(a,c)
	;;; nEW(a,b) ∧ dW(b,c) or W(a,b) ∧ dW(b,c)
	RULE axiom_9_1
	[nEW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF lbpt '9_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE axiom_9_2
	[W ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^C])]]
	==>
	[SAYIF lbpt '9_2 Justifying datum' ?consequent ?a1 ?a2]
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
	[SAYIF lbpt '10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF lbpt '10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_3
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '10_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_10_4
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '10_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
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
    [SAYIF lbpt '10_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_6
	[W ?A ?B] [->> a1]
	[nEW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '10_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_10_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '10_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_10_8
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '10_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '10_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '10_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '10_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '10_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
	[SAYIF lbpt '11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_2
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF lbpt '11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_3
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '11_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_11_4
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '11_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
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
    [SAYIF lbpt '11_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_6
	[nEW ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '11_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_11_7
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '11_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_11_8
	[W ?A ?B] [->> a1]
	[W ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '11_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '11_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '11_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '11_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '11_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
	[SAYIF lbpt '12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF lbpt '12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_3
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '12_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_12_4
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '12_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
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
    [SAYIF lbpt '12_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_6
	[dW ?A ?B] [->> a1]
	[Iew ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '12_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_12_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '12_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_12_8
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '12_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '12_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '12_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '12_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '12_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
	[SAYIF lbpt '13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_2
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=W
	[W ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([W ^A ^D])]]
	==>
	[SAYIF lbpt '13_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_3
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '13_3 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]
	
	RULE axiom_13_4
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R=dW
	[dW ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dW ^A ^D])]]
	==>
	[SAYIF lbpt '13_4 Justifying datum' ?consequent ?a1 ?a2 ?a3]
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
    [SAYIF lbpt '13_5 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_6
	[Iew ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '13_6 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]

	RULE axiom_13_7
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[nEW ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '13_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	RULE axiom_13_8
	[dW ?A ?B] [->> a1]
	[dW ?B ?C] [->> a2]
	;;; R= ¬E(c,d) ∧ ¬E(a,d)  -> bot
	[W ?C ?D] [->> a3]
	[E ?A ?D] [->> a4]
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)]
	==>
    [SAYIF lbpt '13_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '13_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '13_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '13_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
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
    [SAYIF lbpt '13_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4]
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4]
	
	
enddefine;

;;; LD_rules ends here
vars LD_rules = true;
