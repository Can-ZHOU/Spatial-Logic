### Code & Data for Paper: (Submitted to Journal of Artificial Intelligence Research) 
## A Logic of Directions and its Finite Axiomatisability over 2D Euclidean Space

### Set Up && Environment
- Running environment: Ubuntu 20.04
- Programming environment: Poplog (can be downloaded via [this link](https://www.cs.bham.ac.uk/research/projects/poplog/freepoplog.html))

### Run Code
- For getting results' details:
  - When tau == 2, run:
    - `` pop11 t=2/new_LD_reasoner_v0_1.p``
  - when tau == 3, rum:
     - `` pop11 t=3/new_LD_reasoner_v0_1.p``
- For comparing nogoods between tau=2 and tau=3, run:
  - ``python3 compare/compare.py

### Code Structure
```
Spatial Logic  
|  
|--- compare  
|    |--- compare.py  
|    |--- compare_nott.txt  
|    |--- compare_south.txt  
|    |--- nott_LD_t2.txt  
|    |--- nott_LD_t3.txt  
|    |--- south_LD_t2.txt  
|    |--- south_LD_t3.txt  
|  
|--- data  
|  
|--- difference  
|    |--- diff.py  
|    |--- diff_nott_t2.txt
|    |--- diff_nott_t3.txt
|    |--- diff_south_t2.txt
|    |--- diff_south_t3.txt
|    |--- nott_LD_t2.txt
|    |--- nott_LD_t2_old.txt
|    |--- nott_LD_t3.txt
|    |--- nott_LD_t3_old.txt
|    |--- south_LD_t2.txt
|    |--- south_LD_t2_old.txt
|    |--- south_LD_t3.txt
|    |--- south_LD_t3_old.txt
|
|--- t=2
|    |--- results
|    |    |--- SpatialLogic.py
|    |    |--- analysis_report_nott_t2.txt
|    |    |--- analysis_report_south_t2.txt
|    |    |--- justification_results_nott_ew.txt
|    |    |--- justification_results_nott_ns.txt
|    |    |--- justification_results_south_ew.txt
|    |    |--- justification_results_south_ns.txt
|    |    |--- nott_LD.txt
|    |    |--- results_nott_ew.txt
|    |    |--- results_nott_ns.txt
|    |    |--- results_south_ew.txt
|    |    |--- results_south_ns.txt
|    |    |--- south_LD.txt
|    |    |--- t2_justification.zip
|    |
|    |--- LD_rules.p
|    |--- LD_rules_EW.p
|    |--- LNF_reasoner.p
|    |--- LNF_rules.p
|    |--- atms_nodes.p
|    |--- atms_types.p
|    |--- lisp_utils.p
|    |--- new_LBPT_reasoner.p
|    |--- new_LD_reasoner_v0_1.p
|    |--- new_LD_rules_EW_v0_1.p
|    |--- new_LD_rules_NS_v0_1.p
|    |--- rest is dataset.
|
|--- t=3
|    |--- results
|    |    |--- SpatialLogic.py
|    |    |--- analysis_report_nott_t3.txt
|    |    |--- analysis_report_south_t3.txt
|    |    |--- justification_results_nott_ew.txt
|    |    |--- justification_results_nott_ns.txt
|    |    |--- justification_results_south_ew.txt
|    |    |--- justification_results_south_ns.txt
|    |    |--- nott_LD.txt
|    |    |--- results_nott_ew.txt
|    |    |--- results_nott_ns.txt
|    |    |--- results_south_ew.txt
|    |    |--- results_south_ns.txt
|    |    |--- south_LD.txt
|    |    |--- t3_justification.zip
|    |    |--- test_nott_ew.txt
|    |    |--- test_nott_ns.txt
|    |    |--- test_south_ew.txt
|    |    |--- test_south_ns.txt
|    |
|    |--- atms_nodes.p
|    |--- atms_types.p
|    |--- lisp_utils.p
|    |--- new_LD_reasoner_v0_1.p
|    |--- new_LD_rules_EW_v0_1.p
|    |--- new_LD_rules_NS_v0_1.p
|    |--- rest is dataset.
|
|--- LICENSE
|
|--- README.md
```
### Contact
- For any issue/question about this paper and project, please contact [Dr. Heshan Du](<Heshan.Du@nottingham.edu.cn>)
- For any issue/question about codes, please contact [Can Zhou](<Can.Zhou@nottingham.edu.cn>)
