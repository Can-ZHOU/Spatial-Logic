/* --- Copyright University of Nottingham 2021. All rights reserved. ------
 > File:            LD_rules.p
 > Purpose:	    Rules for LD.
 > Author:          Can ZHOU, 2021
 > Documentation:   t=2/new_LD_rules_NS_v0_1.p
 > Related Files:   nns_LD_reasoner.p
 */

;;; τ=2
vars ns_ld_ruleset;

;;; LD rules
;;; N and S rules

define :ruleset ns_ld_ruleset;
;;;	[DLOCAL [prb_show_conditions = true]];
	[VARS prb_allrules trigger_db];


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_2
	[dS ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'NS_axiom_2 Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_3
	[sS ?A ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
    ==>
	[SAYIF ld 'NS_axiom_3 Inconsistent data' ?a1]
	[ATMS_INCONSISTENT ?a1]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_4_1
	[dN ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ?B ?A])]]
	==>
	[SAYIF ld 'NS_axiom_4_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE NS_axiom_4_2
	[dS ?B ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([dN ?A ?B])]]
	==>
	[SAYIF ld 'NS_axiom_4_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_5_1
	[sN ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ?B ?A])]]
	==>
	[SAYIF ld 'NS_axiom_5_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]

	RULE NS_axiom_5_2
	[sS ?B ?A] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ?A ?B])]]
	==>
	[SAYIF ld 'NS_axiom_5_2 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_6_1
	[nNS ?A ?B] [->> a1]
	[WHERE some_in_db_p([^a1], trigger_db)]
	[LVARS [consequent = add_new_formula([nNS ?B ?A])]]
	==>
	[SAYIF ld 'NS_axiom_6_1 Justifying datum' ?consequent ?a1]
	[ATMS_JUSTIFY ?consequent [?a1]]
	

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_b1
	[sS ?A ?B] [->> a1]
	[nNS ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_b1 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_b2
	[dS ?A ?B] [->> a1]
	[sN ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_b2 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_b3
	[sS ?A ?B] [->> a1]
	[dS ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_b3 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    RULE NS_axiom_b4
	[dS ?A ?B] [->> a1]
	[nNS ?B ?A][->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	==>
    [SAYIF ld 'NS_axiom_b4 Inconsistent data' ?a1 ?a2]
	[ATMS_INCONSISTENT ?a1 ?a2]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_7_1
	[sS ?A ?B] [->> a1]
	[sS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_7_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

    RULE NS_axiom_7_2
	[sS ?A ?B] [->> a1]
	[sN ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([nNS ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_7_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE NS_axiom_7_3
	[sN ?A ?B] [->> a1]
	[sS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([nNS ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_7_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_8_1
	[nNS ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_8_1 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

    RULE NS_axiom_8_2
	[nNS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_8_2 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]

	RULE NS_axiom_8_3
	[dS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ?A ?C])]]
	==>
	[SAYIF ld 'NS_axiom_8_3 Justifying datum' ?consequent ?a1 ?a2]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

	RULE NS_axiom_9_1
	[sS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[sS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_9_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_9_2
	[nNS ?A ?B] [->> a1]
	[sS ?B ?C] [->> a2]
	[nNS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([nNS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_9_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE NS_axiom_10_1
	[sS ?A ?B] [->> a1]
	[nNS ?B ?C] [->> a2]
	[sN ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_10_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_10_2
	[sN ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[sS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_10_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE NS_axiom_11_1
	[dS ?A ?B] [->> a1]
	[sN ?B ?C] [->> a2]
	[nNS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([nNS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_11_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_11_2
	[nNS ?A ?B] [->> a1]
	[sS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_11_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE NS_axiom_12_1
	[dS ?A ?B] [->> a1]
	[sN ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_12_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_12_2
	[sN ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[sN ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_12_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
	RULE NS_axiom_13_1
	[dS ?A ?B] [->> a1]
	[sN ?B ?C] [->> a2]
	[sN ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([sN ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_13_1 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]

	RULE NS_axiom_13_2
	[sN ?A ?B] [->> a1]
	[dS ?B ?C] [->> a2]
	[dS ?C ?D] [->> a3]
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)]
	[LVARS [consequent = add_new_formula([dS ?A ?D])]]
	==>
	[SAYIF ld 'NS_axiom_9_2 Justifying datum' ?consequent ?a1 ?a2 ?a3]
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]]


enddefine;

;;; LD_rules ends here
vars LD_rules = true;
