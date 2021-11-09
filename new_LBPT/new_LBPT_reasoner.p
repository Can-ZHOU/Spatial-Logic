/* --- Copyright University of Nottingham 2011. All rights reserved. ------
 > File:            LBPT_reasoner.p
 > Purpose:	    A simple reasoner in Poprulebase for LBPT matchings.
 > Author:          Hai Nguyen & Brian Logan, January 14 2012
 > Documentation:   Reasoner code and utilties
 > Related Files:   LBPT_rules.p
 */


;;; This file contains the definitions of the following procedures:

vars ;;; PRB interface procedures 
     procedure reasoner_init,
     procedure print_reasoner_stats,
     procedure datum_p,
     procedure add_new_formula,
     procedure add_new_formulas,
     procedure print_new_formulas,

     ;;; Procedures used in poprulebase rules
     procedure some_in_db_p,
     procedure cannonicalise_datum,

     ;;; Reasoner procedures and utilities
     procedure print_db,
     procedure printable_atms_assumptions,
     procedure atms_environment_datum_list,
     procedure printable_atms_nogoods,
     procedure lbpt_run,
     procedure prb_name,
     procedure read_relations,
     procedure mapping_relation,
     procedure lbpt_axiom1,
     procedure beq_expand,
     procedure check_premises,
     procedure lbpt_read;
     
false -> poplinewidth;


;;; pop11 memory limit: default 300000 words is 1.2 million bytes
;;; False is the same as pop_max_int
false -> popmemlim;

uses prblib
uses poprulebase

;;; debugging
uses debugger;
true -> debugger_debugging ;

;;; Profiling

false -> popgctrace;
uses profile;
true -> profile_count_all;
1 -> profile_interval;
20 -> profile_show_max;


;;; Tracing and profiling prb

;;;[ lbpt ] -> prb_sayif_trace;
;;;uses prb_profile
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
;;; lbpt_cycle_limit is reached. Since we fire all matching rule
;;; instances at each cycle, it suffices to hold only those formulas
;;; derived at the last cycle. We can therefore set prb_repeating to
;;; true (as the membership test on prb_remember would be guaranteed to
;;; fail).
true -> prb_repeating;


;;; Reasoner/D-ATMS code starts here

;;; Extend popuseslist
[ '.' ^^popuseslist] -> popuseslist;
uses prb_atms
uses new_LBPT_rules


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


vars reasoner_cycle = 0, filter_time = 0, cpu_time = 0;

;;; Remember input for debugging
vars lbpt_relations = [], lbpt_assumptions = [], lbpt_premises = [];

;;; The maximum number of reasoner cycles: false means run until STOP
;;;vars lbpt_cycle_limit = false;
vars lbpt_cycle_limit = false;


;;; (Re)initialise the reasoner global variables.
define reasoner_init();
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
    ;;;'=====================================================' ==>
    ;;;printf('condition is %p\n', [^(lmember_=(f, db(fast_front(f))) ->> s)]);
    ;;;printf('fast_front(f)_ = %p\n', [^(fast_front(f))]);
    ;;;printf('db(fast_front(f))_ = %p\n', [^(db(fast_front(f)))]);
    
    ;;;printf('(f, db(fast_front(f)))', [^(f, db(fast_front(f)))]);
    ;;;printf('lmember_ should be: %p\n', [^(f, db(fast_front(f)))]);
	;;;printf('f = %p\n', [^f]);
	;;;printf('lmember_ = %p\n', [^(datalist(lmember_))]);
	;;;printf('db = %p\n', [^(datalist(db))]);
	fast_front(s) -> datum; 
	;;;printf('s = %p\n',[^s]);
	;;;printf('datum = %p\n',[^datum]);
	endif;
    enddefine;


;;; Add formula <f> to the appropriate database if it isn't already
;;; present. If <f> isn't present, returns <f>. Otherwise returns the
;;; existing (previously derived) datum = to <f>.
define add_new_formula(f) -> datum;

    unless datum_p(f, db) ->> datum then
	prb_add_to_db(f, new_db);
	prb_add_to_db(f, db);
	f -> datum;
 	endunless; 
    enddefine;


;;; For each item in <formula_list>, add it to the appropriate database if
;;; it isn't already present.
define add_new_formulas(formula_list) -> data;
    maplist(formula_list, add_new_formula) -> data;
    ;;; Don't do this with the current ruleset
;;;    maplist(maplist(formula_list, 
;;;		    cannonicalise_datum),
;;;	    add_new_formula) -> data;
    enddefine;


define print_new_formulas(prop);
    appproperty(prop, procedure(item, val); printf('%p ', [^val]); endprocedure);
    printf('\n', []);
    enddefine;


;;; Note the use of #_IF to allow recompiliation of the rest of this file.
#_IF not(DEF cycle_new_formulas)

define cycle_new_formulas();
    print_reasoner_stats();
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

define cannonicalise_datum(datum) -> cannonical_datum;
    lvars p, a, b;

    if datum fmatches [?p ?a ?b] and 
       alphabefore(b, a) and 
       (p = "NEAR" or p = "FAR" or p = "BEQ") then
        [^p ^b ^a]-> cannonical_datum;
    else
	datum -> cannonical_datum
        endif;
    enddefine;

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
    for size from 1 to extensible_vector_length(atms_nogoods) - 1 do 
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

;;; Print the assumption datums in each nogood, omitting premises and duplicates
define printable_lbpt_nogoods() -> printable_nogoods;
    lvars size, nogood, printable_nogoods = [];
    for size from 1 to extensible_vector_length(atms_nogoods) - 1 do 
    	for nogood in atms_nogoods(size) do
	    ;;; Only print global nogoods
   	    if (atms_cseq_disjunctions_length(nogood) == 0) then
		;;; We assume that the Abox concept instance is the
		;;; first element of the list returned by
		;;; print_atms_environment_datums, and so only print the
		;;; concept names in the tail of the list
		lvars datum_list = atms_environment_datum_list(nogood);
		remove_if(member(% lbpt_premises %), datum_list) -> datum_list;
		unless member(datum_list, printable_nogoods) then
	       	    cons(datum_list, printable_nogoods) -> printable_nogoods;
		    endunless;
   	   	endif;
    	    endfor;
    	endfor;
    enddefine;


;;; Run the LBPT reasoner
define lbpt_run(assumptions, premises);
    lvars no_goods_length = 0;
    sys_unlock_heap();
    popatms_init();
    timediff() ->;
    reasoner_init();

    ;;; Add asssumptions and premises. We add assumptions first to keep the
    ;;; environments small, since assumption ids determine bit position.
    atms_assume_all(assumptions);
;;;    atms_assume_all(premises);
    atms_premise_all(premises);
    
    ;;; Initialise the prb databases with the assumptions and premises.
    ;;; Note that premises need to be new to derive symmetric NEAR and FAR
    ;;; relations.
    prb_newdatabase(64, assumptions <> premises) -> db;
    prb_newdatabase(64, assumptions <> premises) -> new_db;
    prb_newdatabase(64, []) -> trigger_db;

    sysgarbage();
    sys_lock_heap();
    timediff() ->;
    prb_run(lbpt_ruleset, db, lbpt_cycle_limit);
    'Reasoner time:'><(timediff()) =>

    ;;; Build the labels
    ;;;atms_falsity==>
    atms_lazy_node_label([ ^atms_falsity ]);
    timediff() -> cpu_time;
    'Label computation time '>< cpu_time =>
    printable_lbpt_nogoods() -> no_goods_length;
    no_goods_length ==> 
    printf('nogoods length = %p\n', [^(length(no_goods_length))]);  	
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;;print_atms_stats();
datalist(atms_assumptions) ==>
    enddefine;

;;; Property containing all the spatial objects in both data sets
vars objects = newassoc([]); 

vars os_url = consword('http://www.ordnancesurvey.co.uk/ontology/BuildingsAndPlaces/v1.1/BuildingsAndPlaces.owl'),
     sm_url = consword('http://www.semanticweb.org/ontologies/2012/2/OpenStreetMapFeatures.owl');

vars prb_name_prefix = newassoc([[^os_url 'os'] [^sm_url 'sm']]);

;;; Convert an owl url/id to a word for prb, and remember it.
define prb_name(url, id) -> name;
    consword(prb_name_prefix(url) >< id) -> name;
    true -> objects(name);
    enddefine;

define read_relations(filename) -> relations;
    lvars item, items;

    lvars itemrep = incharitem(discin(filename));
    1 -> item_chartype(`/`, itemrep);
    1 -> item_chartype(`:`, itemrep);
    1 -> item_chartype(`.`, itemrep);

    ;;; Forget objects in any previous data set.
    clearproperty(objects);

    ;;; Each relation in the input is split into 9 items. We assume that the
    ;;; data files are well formed, i.e., don't contain partial relations.
    [% until itemrep() == termin do
	[% until (itemrep() ->> item) = "]" do
	       item;
	       enduntil %] -> items;
	[% items(1), 
	   prb_name(items(2), items(4)),
	   prb_name(items(5), items(7)) %];
	enduntil %] -> relations;
    enddefine;

;;; Returns true if <relation> is a mapping relation, i.e., relates spatial
;;; objects in different data sets. This should only be BPT relations, but
;;; the data also contains BEQ mapping relations. Only mapping relations can
;;; be assumptions -- other relations are premises.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
define mapping_relation(relation) -> bool;
    (subword(1, 2, relation(2)) /= subword(1, 2, relation(3))) -> bool;
    enddefine;

;;; Create reflexive BPT relations for each object.
define lbpt_axiom1() -> reflexive_relations;
    [% appproperty(objects, 
		   procedure(o, v) -> reflexive_relation;
		       [BPT ^o ^o] -> reflexive_relation;
		       endprocedure) %] -> reflexive_relations;
    enddefine;

;;; Expand BEQ relations into two BPT relations
define beq_expand(relation);
    lvars a, b;

    if relation fmatches [BEQ ?a ?b] then 
    	[BPT ^a ^b], [BPT ^b ^a];
    else
	relation;
	endif;
    enddefine;

;;; Check for inconsistent premises: a BPT relation between objects
;;; in the same data set derives false.
define check_premises(premises);
    lvars premise;

    for premise in premises do
	if premise fmatches [BPT = =] and not(mapping_relation(premise)) then 
	    'WARNING: inconsistent premise(s): ' >< premise =>
	    return;
	    endif;
	endfor;
    enddefine;


;;; Read the relations and run the reasoner.
define lbpt_read(filename);
    read_relations(filename) -> lbpt_relations;

    ;;; Expand the BEQ relations
    lbpt_relations ==>
    maplist(lbpt_relations, beq_expand) -> lbpt_relations;
    ;;;lbpt_relations ==>

    
    ;;; Canonicalise the relations
    maplist(lbpt_relations, cannonicalise_datum) -> lbpt_relations;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;;; lbpt_relations ==>

    ;;; Remove any duplicate relations
    lvars relation_set = [], relation;
    for relation in lbpt_relations do
	adjoin(relation, relation_set) -> relation_set;
	endfor;

    ;;; Split into assumptions and premises
    remove_if_not(mapping_relation, relation_set) -> lbpt_assumptions;
    remove_if(mapping_relation, relation_set) -> lbpt_premises;

    'Processing ' >< filename >< ' assumptions ' >< (length(lbpt_assumptions)) >< ' premises ' >< (length(lbpt_premises)) =>

    ;;; Check for inconsistent premises
    check_premises(lbpt_premises);
    lbpt_run(lbpt_assumptions, lbpt_premises);
    enddefine;


false -> prb_show_conditions;
false -> prb_pausing;
false -> prb_chatty;
false -> prb_walk;

;;; Process any command line arguments. We assume the first argument is the
;;; name of a file containing the within dataset relations and the mapping
;;; relations.
;;; if listlength(poparglist) >= 1 then
;;; lbpt_read(hd(poparglist));
;;; endif;

define run_reasoner(poparglist);
    lvars file;
    if listlength(poparglist) >= 1 then
        for file in poparglist do
            printf('===================== processing the file %S =======================\n', [^file]);
            lbpt_read(file);
        endfor;
    endif;
enddefine;

;;; vars poparglist = ['nott_0.txt' 'nott_1.txt' 'nott_2.txt' 'nott_3.txt' 'nott_4.txt' 'nott_5.txt' 'nott_6.txt' 'nott_7.txt' 'nott_8.txt' 'nott_9.txt' 'nott_10.txt' 'nott_11.txt' 'nott_12.txt' 'nott_13.txt' 'nott_14.txt' 'nott_15.txt'];

vars poparglist = ['south_0.txt' 'south_1.txt' 'south_2.txt' 'south_3.txt' 'south_4.txt' 'south_5.txt' 'south_6.txt' 'south_7.txt' 'south_8.txt' 'south_9.txt' 'south_10.txt' 'south_12.txt' 'south_13.txt' 'south_14.txt' 'south_16.txt' 'south_17.txt' 'south_18.txt' 'south_19.txt' 'south_20.txt' 'south_21.txt' 'south_22.txt' 'south_23.txt' 'south_24.txt' 'south_25.txt' 'south_26.txt'];

;;; vars poparglist = ['nott_0.txt'];

run_reasoner(poparglist);

;;; load new_LBPT_reasoner.p;

