# EPFL CS550 - Formal Verification

[Moodle](https://moodle.epfl.ch/course/view.php?id=13051), [Coursebook](https://edu.epfl.ch/coursebook/en/formal-verification-CS-550?cb_cycle=bama_cyclemaster&cb_section=in)

This  repository is the homepage of the course Formal Verification (autumn 2022) and hosts the material necesary for the labs.

### Staff:

- Professor: [Viktor Kunčak](https://people.epfl.ch/viktor.kuncak)
- Teaching Assistant: [Simon Guilloud](https://people.epfl.ch/simon.guilloud)
- Student Assistants: [Noé De Santo](https://people.epfl.ch/noe.desanto), [Andrea Gilot](https://people.epfl.ch/andrea.gilot)

### Grading

The grade is based on the written mid-term, as well as code, documentation, and explanation of projects during the semester. Specific percentages will be communicated in the first class and posted here.

The types of graded materials will include:

- 40% Mid-term: 27 October 15:15-18:00 (see [this folder with past exams](past-exams/))
- 20% total: four labs, to be done in groups, each group working independently on same projects
- 40% final project to be done in groups, you will choose a topic with our agreement
    - 10% Written presentation of a background paper 
    - 10% Results accomplished (how hard it was, how far you got)
    - 10% Presentation of results
    - 10% Final report

# Content

In this course we introduce formal verification as a principled approach for developing systems that do what they should do.

The course has two aspects:
- learning the practice of formal verification - how to use tools to construct verified software
- understanding the principles behind formal verification and the ways in which verification tools work

The course will follow a similar structure to the [2020 edition](https://lara.epfl.ch/w/fv20/top). Project can be a case study in developing a verified piece of software, an implementation of verification tool functionality, or a theoretical result about verification, constraint solving or theorem proving. Students present their projects with a written report as well as by a live presentation of the background material and project results, answering our questions.

Note that slides can be found **underneath each lecture video** on switch tube linkes below. 

## Books

* [HandMC] **Handbook of Model Checking**, 2018, from [from Springer](https://link.springer.com/book/10.1007/978-3-319-10575-8), [from EPFL Library](https://library.epfl.ch/en/beast?isbn=9783319105758), edited by Edmund M. Clarke, Thomas A. Henzinger, Helmut Veith, Roderick Bloem.
* [HandAR] **Handbook of Practical Logic and Automated Reasoning**, 2009, [from Cambridge University Press](https://doi.org/10.1017/CBO9780511576430) and [from EPFL Library](https://library.epfl.ch/en/beast?isbn=9786612058776), by John Harrison
* [CalComp] **The Calculus of Computation - Decision Procedures with Applications to Verification**, 2007, [from Springer](https://doi.org/10.1007/978-3-540-74113-8), [from EPFL library](https://www.epfl.ch/campus/library/beast/?isbn=9783540741138), by Aaron Bradley and Zohar Manna.

In the reading list below, HandAR-Ch.2 means Chapter 2 in the Handbook of Practical Logic and Automated Reasoning Above, whereas HandMC-Ch.9 means Chapter 9 of the Handbook of Model Checking, etc.

## COURSE OUTLINE 


| Week | Day | Date       | Time  | Room   | Topic                           | Videos & Slides              |
| :--  | :-- | :--        | :--   | :--    | :--                             | :--                          |
| 1    | Thu | 22.09.2022 | 15:15 | [GRA330](https://plan.epfl.ch/?room==GR%20A3%2030) | Lecture 1                       | [Intro to FV](https://tube.switch.ch/videos/56b40f7e), [Intro to Stainless](https://tube.switch.ch/videos/c7d203e8), [Auxiliary Assertions](https://tube.switch.ch/videos/44e8a0dc), [Unfolding](https://tube.switch.ch/videos/ada8a42c), [Disasters, Successes, and Inductive Invariants](https://tube.switch.ch/videos/cca7c3f8) |
|      |     |           |   |   | Follow:                       | [Stainless ASPLOS'22 Tutorial](https://epfl-lara.github.io/asplos2022tutorial/)  |
|      |     |           | 17:15 | GRA330 | Lecture 2                       | [Dispenser Example](https://tube.switch.ch/videos/ded227dd), [Finite Systems Expressed with Formulas](https://tube.switch.ch/videos/088d2823) |
|      |     |            |   |   | Reading:                       | HandMC-Ch.10  |
|      | Fri | 23.09.2022 | 13:15 | [INR219](https://plan.epfl.ch/?room==INR%20219) | Lecture 3                       | [What is a Formal Proof?](https://tube.switch.ch/videos/4a211e7a) and [Propositional Resolution](https://tube.switch.ch/videos/280bbc4c) |
|      |     |            |   |   | Reading:                       | CalComp-Ch.1 ∨ HandAR-Ch.2 |
| 2    | Thu | 29.09.2022 | 15:15 | GRA330 | Exercises 1 | [Part 1](exercises/ex1/exercise1-part1.pdf) ([solution](exercises/ex1/solutions1.pdf)), [Part 2](exercises/ex1/exercise1-part2.pdf) ([solution](exercises/ex1/solutions2.pdf)) | 
|      |     |            | 17:15 | GRA330 | Labs 1  | [Using Stainless](labs/lab1/) | 
|      | Fri | 30.09.2022 | 13:15 | INR219 | Lecture 4 | Finish  [Propositional Resolution](https://tube.switch.ch/videos/280bbc4c) and do [Automating First-Order Logic Proofs Using Resolution](https://tube.switch.ch/videos/60fb9217) until normal forms | 
|      |     |            |   |   | Reading:                       | (CalComp-1.6,1.7 ∨ HandAR-Ch.2) ∧ HandMC-Ch.9 ∧ CalComp-2.{1,2,3} |
| 3    | Thu | 06.10.2022 | 15:15 | GRA330 | Exercises 2 | [Sheet](exercises/ex2/Exercise2.pdf) ([solution](exercises/ex2/solutions2.pdf)) | 
|      |     |            | 17:15 | GRA330 | Labs 1 | Continue [Using Stainless](labs/lab1/)  | 
|      | Fri | 07.10.2022 | 13:15 | INR219 | Lecture 5  | Formal Hardware Verification in Industry (Barbara Jobstmann) and [Symbolic Exploration](https://tube.switch.ch/videos/DuvmOssLQG) (Viktor) |
| 4    | Thu | 13.10.2022 | 15:15 | GRA330 | Lecture 6 | [Automating First-Order Logic Proofs Using Resolution](https://tube.switch.ch/videos/60fb9217), from normal forms onwards. [Term Models for FOL](slides/term-models.pdf) | 
|      |     |            | 17:15 | GRA330 | Labs 2 | [Resolution for FOL](labs/lab2/) | 
|      | Fri | 14.10.2022 | 13:15 | INR219 | Lecture 7 | [Converting Imperative Programs to Formulas](https://tube.switch.ch/videos/79219264), [Hoare Logic, Strongest Postcondition, Weakest Precondition](https://tube.switch.ch/videos/3fc107a7) |   |
| 5    | Thu | 20.10.2022 | 15:15 | GRA330 | Exercises 3 | [Sheet 2: FOL models. Weakest Preconditions. Programs to Formulas](exercises/ex3/Exercise3.pdf) ([solution](exercises/ex3/solutions3.pdf)) | 
|      |     |            | 17:15 | GRA330 | Labs 2 | Continue [Resolution for FOL](labs/lab2/) | 
|      | Fri | 21.10.2022 | 13:15 | INR219 | Lecture 8 | [Monotonicity and Semantics of Local Variables](https://tube.switch.ch/videos/pJFK2gi0YM), [Relational Semantics of Loops](https://tube.switch.ch/videos/jAePaQR8jc), [Loop Semantics Example](https://tube.switch.ch/videos/M2YCTkGZ4F) |  
| 6    | Thu | 27.10.2022 | 15:15 | [GRA330](https://plan.epfl.ch/?room==GR%20A3%2030) and  [MEB331](https://plan.epfl.ch/?room=%253DME%20B3%2031) | **MID-TERM**: [INSTRUCTIONS](exam/) |      | 
|      |     |            | 18:00 |        | End of mid-term |  | 
|      | Fri | 28.10.2022 | 13:15 | INR219 | Lab 3 Background | [Sequent Calculus Presentation](https://tube.switch.ch/videos/bF3Jixi666) and [Lisa](https://github.com/epfl-lara/lisa) Demo |
<<<<<<< HEAD
| 7    | Thu | 03.11.2022 | 15:15 | GRA330 | Lecture |  |      
| 7    | Thu | 03.11.2022 | 15:15 | GRA330 | Lecture 9 | [Presburger Arithmetic 1](https://tube.switch.ch/videos/535e9dea), [Presburger Airhtmetic 2](https://tube.switch.ch/videos/ceecf2f6) |
|      |     |            | 17:15 | GRA330 | Labs 3 | Proofs in Lisa (due 13.11.2022) | 
|      | Fri | 28.10.2022 | 13:15 | INR219 | Lecture 10 | [Discussion of Projects](https://gitlab.epfl.ch/kuncak/student-projects/) and of [Isabelle Proof Assistant](https://isabelle.in.tum.de/) including [Concrete Semantics](http://concrete-semantics.org/), [Selected Slides](lectures/lec10-isabelle/lecture10-isabelle.pdf), [Demos](lectures/lec10-isabelle/Demos/) |
| 8    | Thu | 10.11.2022 | 15:15 | GRA330 | Exam Solution Presentation |  |
| 8    |     |            | 16:15 | BC 420 | Suggestion: attend talk of Avi Wigderson (see email from Tania) |  |
|      |     |            | 17:15 | GRA330 | Labs 4 | Isabelle Lab (1 week) | 
|      | Fri | 11.11.2022 | 13:15 | INR219 | Lecture |  |
| 09   |     | 16.11.2022 | 23:59 |        | Abstracts Due | project abstract + background paper title |
|      | Thu | 17.11.2022 | 15:15 | GRA330 |  |  |
|      |     |            | 17:15 | GRA330 |  |  | 
|      | Fri | 18.11.2022 | 13:15 | INR219 |  |  |
|      | Thu | 24.11.2022 | 15:15 | GRA330 |  |  |
|      |     |            | 17:15 | GRA330 |  |  | 
|      | Fri | 25.11.2022 | 13:15 | INR219 |  |  |
| 11   |     | 30.11.2022 | 23:59 |        | Reports Due | for Background Paper |
|      | Thu | 01.12.2022 | 15:15 | GRA330 |  |  |
|      |     |            | 17:15 | GRA330 |  |  | 
|      | Fri | 02.12.2022 | 13:15 | INR219 |  |  |
| 12   | Thu | 08.12.2022 | 15:15 | GRA330 |  |  |
|      |     |            | 17:15 | GRA330 |  |  | 
|      | Fri | 09.12.2022 | 13:15 | INR219 |  |  |
| 13   | Thu | 15.12.2022 | 15:15 | GRA330 |  |  |
|      |     |            | 17:15 | GRA330 |  |  | 
|      | Fri | 16.12.2022 | 13:15 | INR219 | Presentations | Project Presentations |
| 14   | Thu | 22.12.2022 | 15:15 | GRA330 | Presentations | Project Presentations |
|      |     |            | 17:15 | GRA330 | Presentations | Project Presentations |
|      | Fri | 23.12.2022 | 13:15 | INR219 | Presentations | Project Presentations |

You are welcome to submit your final project (report and code) by the end of the semester. We will start grading on 9 January 2023.
