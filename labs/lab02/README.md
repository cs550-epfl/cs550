# Week 2: More Stainless

## Part 1: Dichotomic Search

This search function operates on a sorted array, and is supposed to return true when there exists an index **i** between **lo** and **hi** such that **arr(i) = x**. The function is left a bit unspecified, as we don't specify that arr should be sorted, and we could return as an option the index i instead of a boolean, but we will not worry about these aspects in this exercise.

Run Stainless on the example (with the options "**--functions=search --strict-arithmetic=false**"), and observe how it complains about the array index **i** in **arr(i)** being out of bounds, and see that it isn't able to prove that the function is terminating.
1. First, the line starting with **val i** is incorrect. Fix it to have a correct implementation of dichotomic search. 
1. Second, write the most general **require(...)** preconditions that are necessary for the algorithm to be correct and bug-free. 
1. Third, prove that the function terminates. To do so you can give a mesure using **decreases(...)** right after the require line. The argument of the decreases function should be a positive numerical expression that is guarantee to decreases at every recursive call. Find the correct mesure. If you found the correct mesure but stainless complains that he is not able to show that it is positive or decreasing, you may need to adequatly adapt your preconditions.
1. Finaly, run stainless with option "**--strict-arithmetic=true**". You will see that stainless finds some possibility of overflow. Minimaly correct your precondition to avoid those case of overflow. Be careful, the order in which you write your preconditions may matter.


## Part 2: Ordered  Trees

In the second part of the file, we define the basic structure of a binary tree. The function **forall** returns true if and only iff all elements stored in the tree satisfy the given predicate. The function **isOrdered** verify if a tree of integers is correctly sorted.

In **forallAfterInsert**, we already proved (by induction on the tree) that if a function **p** returns true on all elements of a tree **t**, and it returns true on an element **x**, then **p** returns true on all elements of the tree **insert(t, x)**.

In **orderedAfterInsert**, our goal is to prove that if we insert an element in an ordered tree, the resulting tree is still ordered. Run Stainless (with a timeout of 10 seconds) on this code and observe that it times out on the two assertions **assert(isOrdered(insert(t, x)))**.

For the first assertion, if we unroll the definition of insert once, we get that **insert(t , x)** equals N**ode(root, insert(left, x), right)**. Then, observe that four conditions need to be verified so that isOrdered returns true on that tree. For each condition, write an assertion (above the **assert(isOrdered(insert(t, x)))** of the first branch) stating that the condition is true.

Run Stainless (again with a timeout of 10 seconds) and by reading the line numbers in the report, see for which of the four conditions (which of the four new assertions) Stainless times out. In order to have Stainless verify this code, you need to use recursve calls to **orderedAfterInsert** and the previous lemma **forallAfterInsert** by calling them with the right arguments.

Do the same thing for the second branch. 


## Submission
Once you've completed all proofs, you can submite your Lab02.scala file [on Moodle](https://moodle.epfl.ch/mod/assign/view.php?id=1169500) by Saturday, 9 October 2021, 23:59. For this assignment, we'll take into account the validity of your proofs as well as the minimality of the preconditions you wrote for the first part.

## Project Session
Project session can be followed in classroom or in [zoom](https://epfl.zoom.us/j/69030789600).
