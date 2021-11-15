/* --- Copyright University of Nottingham 2011. All rights reserved. ------
 > File:            ontology_rules.p
 > Purpose:	    A simple reasoner in Poprulebase for SUMO ontologies.
 > Author:          Hai Nguyen & Brian Logan, January 14 2012
 > Documentation:   Reasoner code and utilties
 > Related Files:   SUMO_rules.p
 */


;;; Simple ontology reasoner for the SUMO upper level ontology.

;;; This file contains the definitions of the following procedures:

vars ;;; PRB interface procedures 
     procedure reasoner_init,
     procedure print_reasoner_stats,
     procedure datum_p,
     procedure add_new_formula,
     procedure add_new_formulas,
     procedure print_new_formulas,

     ;;; Procedures used in poprulebase rules
     procedure lnf_axiom,    
     procedure relation_p,
     procedure mark_nonloop_formula_new,
     procedure justification_loop_p,
     procedure some_in_db_p,
     ;;; Reasoner procedures and utilities
     procedure print_db,
     procedure printable_atms_assumptions,
     procedure atms_environment_datum_list,
     procedure printable_atms_nogoods,
     procedure lnf_run;
     
false -> poplinewidth;


;;; pop11 memory limit: default 300000 words is 1.2 million bytes
;;; False is the same as pop_max_int
false -> popmemlim;

uses prblib
uses poprulebase


;;; Profiling

false -> popgctrace;
uses profile;
true -> profile_count_all;
1 -> profile_interval;
20 -> profile_show_max;


;;; Tracing and profiling prb

;;; [ lnf ] -> prb_sayif_trace;
;;; uses prb_profile
;;;uses prb_trace_procs


;;; POPRULEBASE control variables

;;; Force the use of [ADD datum] in actions.
false -> prb_auto_add;

;;; This must be true for the changes to prb_sortrules to have an effect.
true -> prb_allrules;

;;; We ensure that no rule may be fired more than once on the same
;;; antecedents (and hence that there are no copies of
;;; justifications). Each rule tests that one of its antecedents (the
;;; trigger condition) is new, i.e., has not previously been derived. We
;;; use two additional prb databases to record new formulas derived at
;;; the previous and current cycles, and match trigger conditions
;;; against formulas derived at the previous cycle. At each cycle, the
;;; reasoner effectively derives the consequences of new formulas from
;;; the last cycle until no new formulas can be derived or until
;;; lnf_cycle_limit is reached. Since we fire all matching rule
;;; instances at each cycle, it suffices to hold only those formulas
;;; derived at the last cycle. We can therefore set prb_repeating to
;;; true (as the membership test on prb_remember would be guaranteed to
;;; fail).
true -> prb_repeating;


;;; Reasoner/D-ATMS code starts here

;;; Extend popuseslist
[ '.' ^^popuseslist] -> popuseslist;
uses prb_atms

uses LNF_axiom_assoc
uses LNF_base_abox
uses LNF_rules


;;; The reasoner should not claim the same justification twice, but this
;;; needs to be true to check for repeated assumptions.

;;;false -> atms_check_dups;

;;; Defer label computation until the reasoner terminates
true -> atms_lazy_labels;


;;; new_db and trigger_db are subsets of db. new_db marks datums derived
;;; at the current prb cycle and trigger_db marks datums derived at the
;;; previous prb cycle.
vars procedure db, 
     procedure trigger_db, 
     procedure new_db;


vars file, randomised_tbox, unsat_concept, tbox, 
     reasoner_cycle = 0, filter_time = 0, cpu_time = 0;

;;; Hash table mapping from poprulebase rules to SUMO axioms.
vars lnf_axiom_map = newanyproperty(lnf_axiom_assoc, 250, 1, false, 
				     syshash, nonop ==, "perm", false, false);

;;; The maximum number of reasoner cycles: false means run until STOP
;;;vars lnf_cycle_limit = false;
vars lnf_cycle_limit = false;

;;; Number of reasoner cycles after which we should start checking for
;;; possible loops. False means don't check for loops.
;;;vars lnf_loop_check_limit = false;
vars lnf_loop_check_limit = false;

;;; Formulas whose derivations may contain loops. Note that the
;;; existence of a possible loop does not meant a loop formula could not
;;; be used to derive a larger label if reasoning were to continue --
;;; however any inconsistencies not found within lnf_loop_check_limit
;;; must involve axioms in the labels of one or more loop formulas.
vars lnf_loop_formulas = [];


;;; (Re)initialise the reasoner global variables.
define reasoner_init();
    ;;; Reinitialse the hash tables.
    newanyproperty(lnf_axiom_assoc, 250, 1, false, 
		   syshash, nonop ==, "perm", false, false) -> lnf_axiom_map;

    [] -> lnf_loop_formulas;

    0 -> reasoner_cycle;
    1 -> gensym("i");
    0 -> filter_time;
    0 -> cpu_time;
    enddefine;


;;; Print reasoner and ATMS statistics since the last initialisation
define print_reasoner_stats();
    printf('\Reasoner statistics\n');
    printf('%p reasoner cycles\n', [ ^reasoner_cycle ]);

    print_atms_stats();
    enddefine;


;;; If <f> is = to a datum in <db>, return a reference to that
;;; datum. Otherwise return false.
define datum_p(f, db) -> datum;
    lvars datum = false, s;
    if (lmember_=(f, db(fast_front(f))) ->> s) then
	fast_front(s) -> datum; 
	return;
	endif;
/*	
   if ((hd(f)) = "not") then return; endif;	
    lvars f_rev = rev(f);
    if (lmember_=(f_rev, db(fast_front(f_rev))) ->> s) then
       fast_front(s) -> datum;
    endif;
  */
    enddefine;


;;; Add formula <f> to the appropriate database if it isn't already
;;; present. If <f> isn't present, returns <f>. Otherwise returns the
;;; existing (previously derived) datum = to <f>.
define add_new_formula(f) -> datum;
lvars f_rev = [];


    unless datum_p(f, db) ->> datum then
    lvars a,b;
    if (f fmatches [?a BEQ ?b]) and (alphabefore(a,b)==false) then
	    [?b BEQ ?a]->f_rev;    
	 elseif f fmatches [?a NEAR ?b] and alphabefore(a,b)==false then
	    [?b NEAR ?a]->f_rev;
	  elseif f fmatches [?a FAR ?b] and alphabefore(a,b)==false then
	    [?b FAR ?a]->f_rev;   
	endif;
     unless datum_p(f_rev, db) ->> datum then
	prb_add_to_db(f, new_db);
	prb_add_to_db(f, db);
	f -> datum;
   	endunless;
 	endunless; 
    enddefine;


;;; For each item in <formula_list>, add it to the appropriate database if
;;; it isn't already present.
define add_new_formulas(formula_list) -> data;
    maplist(formula_list, add_new_formula) -> data;
    enddefine;


define print_new_formulas(prop);
    appproperty(prop, procedure(item, val); printf('%p ', [^val]); endprocedure);
    printf('\n', []);
    enddefine;


;;; Note the use of #_IF to allow recompiliation of the rest of this file.
#_IF not(DEF cycle_new_formulas)

define cycle_new_formulas();
   ;;; print_reasoner_stats();
    ;;; Copy items added at the previous cycle to the trigger database.
    clearproperty(trigger_db);
    prb_add_db_to_db(new_db, trigger_db, false);
    clearproperty(new_db);
    reasoner_cycle + 1 -> reasoner_cycle;
    enddefine;

;;; prb_applicable is called by prb_do_rules at each cycle to
;;; find a list of applicable rule instances. 
cycle_new_formulas <> prb_applicable -> prb_applicable;

#_ENDIF


;;; Procedures for use in WHERE conditions in reasoner rules

;;; Return the SUMO axiom corresponding to the currently executing
;;; poprulebase rule.
define lnf_axiom() -> axiom;
    lnf_axiom_map(this_rule_name) -> axiom;
    enddefine;

;;; True if <item> is not a logical connective.
define relation_p(item) -> bool;
    not((item = "and") or 
	(item = "or") or 
	(item = "not") or 
	(item = "exists") or 
	(item = "forall") or 
	(item = "implies") or 
	(item = "equiv")) -> bool;
    enddefine;

;;; Return true if some fact is in database db and false otherwise
define some_in_db_p(datums,db)->bool;
lvars datum, bool=false;
	fast_for datum in datums do
		unless (not(datum_p(datum,db))) then
			true->bool;
			return;
		endunless;
	endfor;
enddefine;

;;; Blocking loops (currently not used)

/*

;;; Mark <formula> as new if (a) it has not been derived before, and (b)
;;; its label is not the same as that of one of the antecedents used to
;;; derive it.
define mark_nonloop_formula_new(formula);
[checking ^formula] =>
    if lnf_loop_check_limit and reasoner_number > lnf_loop_check_limit then

	lvars node = hd(atms_node_list([ ^formula ], false));
	
	;;; Hack for now
	if hd(formula) = "or" then
            formula :: lnf_loop_formulas -> lnf_loop_formulas;
	else
	    if atms_lazy_labels then
	    	;;; Compute the label of <formula>
	    	atms_lazy_node_label([ ^node ]);
	    	endif;
[^formula label ^(atms_node_label(node))] =>
	    
	    if some(atms_node_antecedents(node), justification_loop_p) then
                formula :: lnf_loop_formulas -> lnf_loop_formulas;
	    else
	    	;;; Mark <formula> as new
[nonlooping formula ^formula at cycle ^cycle_number] =>
    	    	true -> new_new_formulas(formula);
	    	endif;
	    endif;

    ;;; prb_present should be safe so long as formula doesn't contain
    ;;; any prb variables
    elseif not(prb_present(formula)) then 
	;;; Mark <formula> as new
    	true -> new_new_formulas(formula);
	endif;
    enddefine;


;;; Return true if the label of the consequent of <justif> is the same
;;; as the label of the one the antecedents. Note that this does not
;;; mean that consequent can never be used to derive a larger label --
;;; however any inconsistencies not found within lnf_loop_check_limit
;;; must involve axioms in the label of the consequent.
define justification_loop_p(justif) -> bool;
    lvars consequent = atms_justification_consequent(justif),
	  clabel = atms_sort_environment_list(atms_node_label(consequent)),
	  antecedents = atms_justification_antecedents(justif),
	  antecedent, bool = false;
    
    for antecedent in antecedents do
[loop_p ^clabel ^(atms_sort_environment_list(atms_node_label(antecedent)))] =>
	if atms_sort_environment_list(atms_node_label(antecedent)) = clabel then
	    true -> bool;
	    return;
	    endif;
	endfor;
    enddefine;

*/

;;; Generating output

define print_db(rules, data);
    '==== PRB DATABASE ====' =>;
    prb_print_table(data);
    enddefine;
;;;print_db -> prb_finish;
     
define printable_atms_assumptions() -> printable_assumptions;
    lvars i;
    [% for i from 1 to extensible_vector_length(atms_assumptions) - 1 do
	   atms_node_datum(atms_assumptions(i)); 
	   endfor; %] -> printable_assumptions;
    enddefine;


;;; Return a list of the assumption datums in an atms_environment
define atms_environment_datum_list(environment) -> datum_list;
    maplist(printable_atms_aset(atms_aset(environment)),
            procedure(i) -> datum;
                atms_node_datum(atms_assumptions(i)) -> datum;
                endprocedure) -> datum_list;
    enddefine;


;;; Print the assumption datums in each nogood
define printable_atms_nogoods() -> printable_nogoods;
    lvars size, nogood, printable_nogoods = [];
    for size from 0 to extensible_vector_length(atms_nogoods) - 1 do 
    	for nogood in atms_nogoods(size) do
	    ;;; Only print global nogoods
   	    if (atms_cseq_disjunctions_length(nogood) == 0) then
		;;; We assume that the Abox concept instance is the
		;;; first element of the list returned by
		;;; print_atms_environment_datums, and so only print the
		;;; concept names in the tail of the list
		lvars datum_list = atms_environment_datum_list(nogood);
	       	cons(datum_list, printable_nogoods) -> printable_nogoods;
   	   	endif;
    	    endfor;
    	endfor;
    enddefine;
   


;;; Run the SUMO reasoner
define lnf_run(abox, tbox);
    sys_unlock_heap();
    popatms_init();
    timediff() ->;
    reasoner_init();

    ;;; Assume abox and tbox
    atms_assume_all(abox,true);
    atms_assume_all(tbox,false);
    

    ;;; Initialise the prb databases with the abox and the tbox
    prb_newdatabase(64, abox <> tbox) -> db;
    prb_newdatabase(64,  tbox) -> new_db;
    prb_newdatabase(64, []) -> trigger_db;

    sysgarbage();
    sys_lock_heap();
    timediff() ->;
    prb_run(lnf_ruleset, db, lnf_cycle_limit);
    'time reasoning:'><(timediff()*1000) =>

    '==== FINISH reasoner ====' =>;
    ;;; Build the labels
    atms_lazy_node_label([ ^atms_falsity ]);
    timediff() * 1000 -> cpu_time;
  ;;;  printf('%p;\n',
  ;;;	   	   [  ^(printable_atms_nogoods()) ]);
  	printable_atms_nogoods()==>

	   	'time computing label '>< cpu_time=>
;;;    prb_print_table(db);
    print_atms_stats();
    enddefine;

vars tbox = maplist(lnf_axiom_assoc, back <> hd);
 	     

lnf_run( base_abox, tbox<>LNF_mappings); 
;;;lnf_run( base_abox, tbox<>wrong_mappings);
