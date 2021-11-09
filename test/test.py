import itertools
import time
import os

EW_rules_pre = "" \
+ ";;; τ=3 \n" \
+ "vars ew_ld_ruleset; \n" \
+ " \n" \
+ ";;; LD rules \n" \
+ ";;; W and E rules \n" \
+ " \n" \
+ "define :ruleset ew_ld_ruleset; \n" \
+ ";;;	[DLOCAL [prb_show_conditions = true]]; \n" \
+ "	[VARS prb_allrules trigger_db]; \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "    ;;; Deﬁnition 2. \n" \
+ "	;;; deﬁnitely north dE (a, b) = def E(a, b) ∧ ¬Iew(a, b) \n" \
+ "    ;;; somewhat north sE (a, b) = def E (a, b) ∧ Iew(a, b) \n" \
+ "    ;;; neither north nor south nEW(a, b) =def ¬E (a, b) ∧ ¬W(a, b) == nEW(a, b) ∧ (E (a, b) or W(a,b)) = bot \n" \
+ "    ;;; somewhat south sW(a, b) =def W(a, b) ∧ Iew(a, b) \n" \
+ "    ;;; deﬁnitely south dW(a,b)=def W(a,b)∧¬Iew(a,b) \n" \
+ " \n" \
+ "	RULE EW_def2_dE1 \n" \
+ "	[dE ?A ?B] [->> a1] \n" \
+ "    [Iew ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([E ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_dE1 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" \
+ "/* \n" \
+ "	RULE EW_def2_dE2 \n" \
+ "	[E ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([dE ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Iew ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_dE2 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE EW_def2_sE1 \n" \
+ "	[sE ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([E ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Iew ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_sE Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE EW_def2_sE2 \n" \
+ "	[E ?A ?B] [->> a1] \n" \
+ "    [Iew ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([sE ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_sE2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "*/ \n" \
+ " \n" \
+ "	RULE EW_def2_nEW1 \n" \
+ "	[nEW ?A ?B] [->> a1] \n" \
+ "    [E ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    ==> \n" \
+ "    [SAYIF ld 'EW_def2_nEW1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ " \n" \
+ "	RULE EW_def2_nEW2 \n" \
+ "	[nEW ?A ?B] [->> a1] \n" \
+ "    [W ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    ==> \n" \
+ "    [SAYIF ld 'EW_def2_nEW2 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "/* \n" \
+ "	RULE EW_def2_sW1 \n" \
+ "	[sW ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([W ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Iew ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_sW1 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE EW_def2_sW2 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "    [Iew ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([sW ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_sW2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "*/ \n" \
+ " \n" \
+ "	RULE EW_def2_dW1 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "    [Iew ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([W ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_dW1 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "/* \n" \
+ "	RULE EW_def2_dW2 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([dW ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Iew ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_def2_dW2 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ "*/ \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_1 \n" \
+ "	[W ?A ?A] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_1 Inconsistent data' ?a1] \n" \
+ "	[ATMS_INCONSISTENT ?a1] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_2_1 \n" \
+ "	[E ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([W ^B ^A])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_2_1 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ "	RULE EW_axiom_2_2 \n" \
+ "	[W ?B ?A] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([E ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_2_2 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_3 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([Iew ^B ^A])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_3 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "    RULE EW_axiom_4_1 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[dE ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_4_1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ "     \n" \
+ "	RULE EW_axiom_4_2 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[dW ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_4_2 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "	;;; For Rule 4.3: already satisified \n" \
+ " \n" \
+ " \n" \



EW_rules_501 = "" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_5_1 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[W ?C ?D] [->> a3] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dW ^A ^D])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_5_1 Justifying datum' ?consequent ?a1 ?a2 ?a3] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]] \n" \
+ " \n" 

EW_rules_502 = "" \
+ "	RULE EW_axiom_5_2 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([W ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_5_2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

EW_rules_503 = "" \
+ "	RULE EW_axiom_5_3 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dW ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_5_3 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

EW_rules_504 = "" \
+ "	RULE EW_axiom_5_4 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[dW ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dW ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_5_4 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

EW_rules_505 = "" \
+ "	RULE EW_axiom_5_5 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([W ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'EW_axiom_5_5 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ " \n" 





EW_rules_post = "" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_6_1 \n" \
+ "	[nEW ?A ?B] [->> a1] \n" \
+ "	[W ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_6_1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "	RULE EW_axiom_6_2 \n" \
+ "	[nEW ?A ?B] [->> a1] \n" \
+ "	[nEW ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [dW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_7 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [nEW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_8 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [Iew ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_9 \n" \
+ "	[nEW ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [W ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_10 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[W ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [dW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_11 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "	[nEW ?B ?C] [->> a2] \n" \
+ "	[W ?C ?D] [->> a3] \n" \
+ "    [Iew ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_12 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[nEW ?B ?C] [->> a2] \n" \
+ "	[W ?C ?D] [->> a3] \n" \
+ "    [dW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_13 \n" \
+ "	[dW ?A ?B] [->> a1] \n" \
+ "	[dW ?B ?C] [->> a2] \n" \
+ "	[Iew ?C ?D] [->> a3] \n" \
+ "    [Iew ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_13 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_14 \n" \
+ "	[Iew ?A ?B] [->> a1] \n" \
+ "	[dW ?B ?C] [->> a2] \n" \
+ "	[Iew ?C ?D] [->> a3] \n" \
+ "    [dW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_14 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_15 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[dW ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [Iew ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_15 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE EW_axiom_16_1 \n" \
+ "	[W ?A ?B] [->> a1] \n" \
+ "	[Iew ?B ?C] [->> a2] \n" \
+ "	[nEW ?C ?D] [->> a3] \n" \
+ "    [dW ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'EW_axiom_16_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ "enddefine; \n" \
+ " \n" \
+ ";;; LD_rules ends here \n" \
+ "vars LD_rules = true;"


NS_rules_pre =  "" \
+ ";;; τ=3 \n" \
+ "vars ns_ld_ruleset; \n" \
+ " \n" \
+ ";;; LD rules \n" \
+ ";;; S and N rules \n" \
+ " \n" \
+ "define :ruleset ns_ld_ruleset; \n" \
+ ";;;	[DLOCAL [prb_show_conditions = true]]; \n" \
+ "	[VARS prb_allrules trigger_db]; \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "    ;;; Deﬁnition 2. \n" \
+ "	;;; deﬁnitely north dN (a, b) = def N(a, b) ∧ ¬Ins(a, b) \n" \
+ "    ;;; somewhat north sN (a, b) = def N (a, b) ∧ Ins(a, b) \n" \
+ "    ;;; neither north nor south nNS(a, b) =def ¬N (a, b) ∧ ¬S(a, b) == nNS(a, b) ∧ (N (a, b) or S(a,b)) = bot \n" \
+ "    ;;; somewhat south sS(a, b) =def S(a, b) ∧ Ins(a, b) \n" \
+ "    ;;; deﬁnitely south dS(a,b)=def S(a,b)∧¬Ins(a,b) \n" \
+ " \n" \
+ "	RULE NS_def2_dN1 \n" \
+ "	[dN ?A ?B] [->> a1] \n" \
+ "    [Ins ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([N ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_dN1 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" \
+ "/* \n" \
+ "	RULE NS_def2_dN2 \n" \
+ "	[N ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([dN ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Ins ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_dN2 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE NS_def2_sN1 \n" \
+ "	[sN ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([N ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Ins ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_sN Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE NS_def2_sN2 \n" \
+ "	[N ?A ?B] [->> a1] \n" \
+ "    [Ins ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([sN ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_sN2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "*/ \n" \
+ " \n" \
+ "	RULE NS_def2_nNS1 \n" \
+ "	[nNS ?A ?B] [->> a1] \n" \
+ "    [N ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    ==> \n" \
+ "    [SAYIF ld 'NS_def2_nNS1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ " \n" \
+ "	RULE NS_def2_nNS2 \n" \
+ "	[nNS ?A ?B] [->> a1] \n" \
+ "    [S ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    ==> \n" \
+ "    [SAYIF ld 'NS_def2_nNS2 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "/* \n" \
+ "	RULE NS_def2_sS1 \n" \
+ "	[sS ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([S ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Ins ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_sS1 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ " \n" \
+ "	RULE NS_def2_sS2 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "    [Ins ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([sS ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_sS2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "*/ \n" \
+ " \n" \
+ "	RULE NS_def2_dS1 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "    [Ins ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	[LVARS [consequent = add_new_formula([S ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_dS1 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ "/* \n" \
+ "	RULE NS_def2_dS2 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "	[LVARS [consequent1 = add_new_formula([dS ^A ^B])] \n" \
+ "	       [consequent2 = add_new_formula([Ins ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_def2_dS2 Justifying datum' ?consequent1 ?consequent2 ?a1] \n" \
+ "	[ATMS_JUSTIFY [?consequent1 ?consequent2] ?a1] \n" \
+ "*/ \n" \
+ " \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_1 \n" \
+ "	[S ?A ?A] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_1 Inconsistent data' ?a1] \n" \
+ "	[ATMS_INCONSISTENT ?a1] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_2_1 \n" \
+ "	[N ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([S ^B ^A])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_2_1 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ "	RULE NS_axiom_2_2 \n" \
+ "	[S ?B ?A] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([N ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_2_2 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_3 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([Ins ^B ^A])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_3 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "    RULE NS_axiom_4_1 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[dN ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_4_1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ "     \n" \
+ "	RULE NS_axiom_4_2 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[dS ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_4_2 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "	;;; For Rule 4.3: already satisified \n" \
+ " \n" \
+ " \n" \

NS_rules_501 = "" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_5_1 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[S ?C ?D] [->> a3] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dS ^A ^D])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_5_1 Justifying datum' ?consequent ?a1 ?a2 ?a3] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]] \n" \
+ " \n" 

NS_rules_502 = "" \
+ "	RULE NS_axiom_5_2 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([S ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_5_2 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

NS_rules_503 = "" \
+ "	RULE NS_axiom_5_3 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dS ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_5_3 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

NS_rules_504 = "" \
+ "	RULE NS_axiom_5_4 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[dS ?B ?C] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([dS ^A ^C])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_5_4 Justifying datum' ?consequent ?a1 ?a2] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] \n" \
+ " \n" 

NS_rules_505 = "" \
+ "	RULE NS_axiom_5_5 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "	[WHERE some_in_db_p([^a1], trigger_db)] \n" \
+ "    [LVARS [consequent = add_new_formula([S ^A ^B])]] \n" \
+ "    ==> \n" \
+ "	[SAYIF ld 'NS_axiom_5_5 Justifying datum' ?consequent ?a1] \n" \
+ "	[ATMS_JUSTIFY ?consequent [?a1]] \n" \
+ " \n" \


NS_rules_post = "" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_6_1 \n" \
+ "	[nNS ?A ?B] [->> a1] \n" \
+ "	[S ?A ?B] [->> a2] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_6_1 Inconsistent data' ?a1 ?a2] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2] \n" \
+ " \n" \
+ "	RULE NS_axiom_6_2 \n" \
+ "	[nNS ?A ?B] [->> a1] \n" \
+ "	[nNS ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [dS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_7 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [nNS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_8 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [Ins ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_9 \n" \
+ "	[nNS ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [S ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_10 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[S ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [dS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_11 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "	[nNS ?B ?C] [->> a2] \n" \
+ "	[S ?C ?D] [->> a3] \n" \
+ "    [Ins ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_12 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[nNS ?B ?C] [->> a2] \n" \
+ "	[S ?C ?D] [->> a3] \n" \
+ "    [dS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_13 \n" \
+ "	[dS ?A ?B] [->> a1] \n" \
+ "	[dS ?B ?C] [->> a2] \n" \
+ "	[Ins ?C ?D] [->> a3] \n" \
+ "    [Ins ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_13 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_14 \n" \
+ "	[Ins ?A ?B] [->> a1] \n" \
+ "	[dS ?B ?C] [->> a2] \n" \
+ "	[Ins ?C ?D] [->> a3] \n" \
+ "    [dS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_14 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_15 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[dS ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [Ins ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_15 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; \n" \
+ "	RULE NS_axiom_16_1 \n" \
+ "	[S ?A ?B] [->> a1] \n" \
+ "	[Ins ?B ?C] [->> a2] \n" \
+ "	[nNS ?C ?D] [->> a3] \n" \
+ "    [dS ?D ?A] [->> a4] \n" \
+ "	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] \n" \
+ "	==> \n" \
+ "    [SAYIF ld 'NS_axiom_16_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4] \n" \
+ "	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] \n" \
+ " \n" \
+ " \n" \
+ "enddefine; \n" \
+ " \n" \
+ ";;; LD_rules ends here \n" \
+ "vars LD_rules = true;"


text = EW_rules_pre + EW_rules_501 + EW_rules_502 + EW_rules_503 + EW_rules_504 + EW_rules_505 + EW_rules_post
fo = open("new_LD_rules_EW_v0_1.p", "w")
fo.write(text)
fo.close()

NS_rule5_list = [NS_rules_501, NS_rules_502, NS_rules_503, NS_rules_504, NS_rules_505]

combinations = list(itertools.permutations(NS_rule5_list))

record = ""
record_times = []
min_time = 1000
for item in combinations:
    tmp = ""
    for i in item:
        tmp += i
    text = NS_rules_pre + tmp + NS_rules_post
    fo = open("new_LD_rules_NS_v0_1.p", "w")
    fo.write(text)
    fo.close()

    start = time.clock()
    for _ in range(10):
        cmd = "pop11 new_LD_reasoner_v0_1.p"
        os.system(cmd)
    end = time.clock()
    
    tmp = end - start
    record_times.append(tmp)
    if tmp < min_time:
        fo = open("bestRule.txt", "w")
        fo.write(text)
        fo.close()
        min_time = tmp

    record += "time is " + str(tmp) + "\n"

print(record)