# Group Identification

 - Tomás Oliveira, 90781, tomas.de.oliveira@tecnico.ulisboa.pt 
 - Guilherme Garrilha, 110827, guilhermegarrilha@tecnico.ulisboa.pt
 - André Alves, 110857, andre.f.alves@tecnico.ulisboa.pt 

# Implemented Features

- Extended *Imp.v* in order to implement a **non-deterministic choice** and a **conditional guard** with the respective notations `c1 !! c2` and `b -> c`
- Implemented **ceval_step** in *Interpreter.v* that evaluates a program and returns either `Success`, `Fail` or `OutOfGas`
- Proved the two properties **p1_equals_p2** and **ceval_step_more**
- Implemented the **ceval** relation with the notation `st1 / q1 =[ c ]=> st2 / q2 / r`
- Proved the examples **ceval_example_if**, **ceval_example_guard1**, **ceval_example_guard2**, **ceval_example_guard3** and **ceval_example_guard4**
- Implemented the **behavioral equivalence** (**cequiv**) in order to define some equivalence properties of our program. The *lemmas* defined are: **cequiv_ex1**, **cequiv_ex2**, **choice_idempotent**, **choice_comm**, **choice_seq_distr_l** and **choice_congruence**
- Updated the parser *ImpParser.v* in order for the interpreter to recognize and parse our implemented constructs (**non-deterministic choice** and a **conditional guard**)
  

# Extras
No extra functionalities have yet been implemented.
