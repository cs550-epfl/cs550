# Lab 4: First Order Logic proofs in LISA

### Prelude: Proof Assistants
Proof assistants, also called interactive theorem provers (ITP) are tools allowing to write fully formal mathematical proofs. Typically, the system is built on a small, fixed syntax for mathematical statement and set of inference rule, for example first order logic. Everything else is then built on those small foundations. The main role of the proof assistant is then to provide tools and assistance to the user to help produce such low level proofs. The assistant typically builds level of abstraction that hide the low level formalism and expose higher level concepts. It also provides tactics, algorithms that will partially or fully solve mathematical statements of some kind while producing a low level proof.

This approach is quite different from what you've seen in Stainless. While it is possible to state some mathematical statements and properties in Stainless, it is aimed at formalizing programs rather than maths. But mostly, Stainless doesn't produce explicit proofs: Programs and correctness conditions are transformed into SMT formulas (Satisfiability Modulo Theories, i.e. propositional statements over theories such as linear arithmetic, arrays, strings and more). Then the formula is given to a specialized decision procedure, a solver, who will answer if the formula is true or not. However, neither the transformation of the program into SMT formulas nor the decision procedure are witnessed by formal proofs. Note that a minority of proof assistants designed for mathematics adopt a similar procedure: Their set of deduction rules is then an algorithm that decide if a set of formulas entails another formula.

Producing proofs is generaly a burden to very advanced decision procedure, as it slows down the search. But said procedure are also very complicated tools, prone to bugs and errors. Producing proofs is a great way to ensure you will never accept a statement that is in fact not correct.


### The Lab
In this Lab, you will use LISA, a proof assistant developed in the LARA.
The first step for you is to read [the first chapter of the user manual](https://github.com/epfl-lara/lisa/blob/main/refman/lisa.pdf). You do not need to insally Lisa manually. To check the theorems in the file [Lab04.scala], run 
```
scala-cli run .\Lab04.scala --dependency "ch.epfl.lara::lisa::0.7,url=https://github.com/epfl-lara/lisa/releases/download/0.7/lisa_3-0.7.jar"
```

You will see 3 theorems printed in green and 6 in yellow. Those correspond to the 9 theorems you can find in the file 


Your goal for this Lab is to is to complete the proofs of the last 6 theorems so that they are all accepted.
Read carefuly the first chapter of LISA's user manual, and the 3 proofs given as example: They contain all the tools needed to complete the proofs. Keep the last two theorems, `richGrandfather` and `greenDragonsAreHappy`, for last: they are more challenging.

You may use any tactic described in the user manual except for the `Tableau` and `Goeland` tactics, but the tactics shown in the comment at the begining of the Lab04.scala file are all you need. Make sure to read the examples attentively to understand the syntax.

When you've finished, upload your file Lab04.scala on [moodle](https://moodle.epfl.ch/mod/assign/view.php?id=1100580) (one submission per group).
