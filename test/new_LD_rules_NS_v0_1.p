;;; τ=3 
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
 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_1 
	[S ?A ?A] [->> a1] 
	[WHERE some_in_db_p([^a1], trigger_db)] 
    ==> 
	[SAYIF ld 'NS_axiom_1 Inconsistent data' ?a1] 
	[ATMS_INCONSISTENT ?a1] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_2_1 
	[N ?A ?B] [->> a1] 
	[WHERE some_in_db_p([^a1], trigger_db)] 
    [LVARS [consequent = add_new_formula([S ^B ^A])]] 
    ==> 
	[SAYIF ld 'NS_axiom_2_1 Justifying datum' ?consequent ?a1] 
	[ATMS_JUSTIFY ?consequent [?a1]] 
 
	RULE NS_axiom_2_2 
	[S ?B ?A] [->> a1] 
	[WHERE some_in_db_p([^a1], trigger_db)] 
    [LVARS [consequent = add_new_formula([N ^A ^B])]] 
    ==> 
	[SAYIF ld 'NS_axiom_2_2 Justifying datum' ?consequent ?a1] 
	[ATMS_JUSTIFY ?consequent [?a1]] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_3 
	[Ins ?A ?B] [->> a1] 
	[WHERE some_in_db_p([^a1], trigger_db)] 
    [LVARS [consequent = add_new_formula([Ins ^B ^A])]] 
    ==> 
	[SAYIF ld 'NS_axiom_3 Justifying datum' ?consequent ?a1] 
	[ATMS_JUSTIFY ?consequent [?a1]] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
    RULE NS_axiom_4_1 
	[Ins ?A ?B] [->> a1] 
	[dN ?A ?B] [->> a2] 
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
 
	;;; For Rule 4.3: already satisified 
 
 
	RULE NS_axiom_5_5 
	[dS ?A ?B] [->> a1] 
	[WHERE some_in_db_p([^a1], trigger_db)] 
    [LVARS [consequent = add_new_formula([S ^A ^B])]] 
    ==> 
	[SAYIF ld 'NS_axiom_5_5 Justifying datum' ?consequent ?a1] 
	[ATMS_JUSTIFY ?consequent [?a1]] 
 
	RULE NS_axiom_5_4 
	[S ?A ?B] [->> a1] 
	[dS ?B ?C] [->> a2] 
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] 
    [LVARS [consequent = add_new_formula([dS ^A ^C])]] 
    ==> 
	[SAYIF ld 'NS_axiom_5_4 Justifying datum' ?consequent ?a1 ?a2] 
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] 
 
	RULE NS_axiom_5_3 
	[dS ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] 
    [LVARS [consequent = add_new_formula([dS ^A ^C])]] 
    ==> 
	[SAYIF ld 'NS_axiom_5_3 Justifying datum' ?consequent ?a1 ?a2] 
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] 
 
	RULE NS_axiom_5_2 
	[S ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] 
    [LVARS [consequent = add_new_formula([S ^A ^C])]] 
    ==> 
	[SAYIF ld 'NS_axiom_5_2 Justifying datum' ?consequent ?a1 ?a2] 
	[ATMS_JUSTIFY ?consequent [?a1 ?a2]] 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_5_1 
	[S ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[S ?C ?D] [->> a3] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3], trigger_db)] 
    [LVARS [consequent = add_new_formula([dS ^A ^D])]] 
    ==> 
	[SAYIF ld 'NS_axiom_5_1 Justifying datum' ?consequent ?a1 ?a2 ?a3] 
	[ATMS_JUSTIFY ?consequent [?a1 ?a2 ?a3]] 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_6_1 
	[nNS ?A ?B] [->> a1] 
	[S ?A ?B] [->> a2] 
	[WHERE some_in_db_p([^a1 ^a2], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_6_1 Inconsistent data' ?a1 ?a2] 
	[ATMS_INCONSISTENT ?a1 ?a2] 
 
	RULE NS_axiom_6_2 
	[nNS ?A ?B] [->> a1] 
	[nNS ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [dS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_6_2 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_7 
	[S ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [nNS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_7 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_8 
	[dS ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [Ins ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_8 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_9 
	[nNS ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [S ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_9 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_10 
	[Ins ?A ?B] [->> a1] 
	[S ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [dS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_10 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_11 
	[dS ?A ?B] [->> a1] 
	[nNS ?B ?C] [->> a2] 
	[S ?C ?D] [->> a3] 
    [Ins ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_11 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_12 
	[Ins ?A ?B] [->> a1] 
	[nNS ?B ?C] [->> a2] 
	[S ?C ?D] [->> a3] 
    [dS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_12 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_13 
	[dS ?A ?B] [->> a1] 
	[dS ?B ?C] [->> a2] 
	[Ins ?C ?D] [->> a3] 
    [Ins ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_13 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_14 
	[Ins ?A ?B] [->> a1] 
	[dS ?B ?C] [->> a2] 
	[Ins ?C ?D] [->> a3] 
    [dS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_14 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_15 
	[S ?A ?B] [->> a1] 
	[dS ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [Ins ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_15 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
	RULE NS_axiom_16_1 
	[S ?A ?B] [->> a1] 
	[Ins ?B ?C] [->> a2] 
	[nNS ?C ?D] [->> a3] 
    [dS ?D ?A] [->> a4] 
	[WHERE some_in_db_p([^a1 ^a2 ^a3 ^a4], trigger_db)] 
	==> 
    [SAYIF ld 'NS_axiom_16_1 Inconsistent data' ?a1 ?a2 ?a3 ?a4] 
	[ATMS_INCONSISTENT ?a1 ?a2 ?a3 ?a4] 
 
 
enddefine; 
 
;;; LD_rules ends here 
vars LD_rules = true;