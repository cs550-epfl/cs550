//> using scala "3.5.1"
//> using dep "ch.epfl.lara::lisa::0.7,url=https://github.com/epfl-lara/lisa/releases/download/0.7/lisa_3-0.7.jar"

object Lab04 extends lisa.Main {

    /*
    You may use the following tactics: 
        - Restate              | "Trivially" true Sequent. Deals with alpha equivalence and most propositional rules but not distributivity
        - Weakening            | "Trivially" weaker sequent (than the previous one).
        - Tautology.from       | Anything that can be solved by propositional reasoning alone

        - LeftForall           | To introduce a ∀ quantifier in an assumption
        - LeftExists           | To introduce a ∃ quantifier in an assumption (the variable must not be free somewhere else)
        - RightForall          | To introduce a ∀ quantifier in the conclusion (the variable must not be free somewhere else)
        - RightExists          | To introduce a ∃ quantifier in the conclusion
        - InstantiateForall    | To obtain a formula of the form P(t) from a quantified assumption ∀(x, P(x))



        thm1 and thm2 illustrate how those tactics can be used, as well as the usage of "assume", "have", "thenHave", "by", "thesis", "of" and "subproof".
    */

    val x = variable
    val y = variable
    val z = variable
    val f = function[1]
    val P = formulaVariable
    val Q = predicate[1]
    val R = predicate[1]
    val S = predicate[2]





    //A standard theorem about reordering quantifiers. Does the converse hold?
    val thm1 = Theorem( ∃(x, ∀(y, S(x, y))) |-  ∀(y, ∃(x, S(x, y))) ) {
        have(S(x, y) |- S(x, y)) by Restate
        thenHave(∀(y, S(x, y)) |-  S(x, y)) by LeftForall
        thenHave(∀(y, S(x, y)) |-  ∃(x, S(x, y))) by RightExists
        thenHave(∃(x, ∀(y, S(x, y))) |-  ∃(x, S(x, y))) by LeftExists
        thenHave(∃(x, ∀(y, S(x, y))) |-  ∀(y, ∃(x, S(x, y)))) by RightForall
    }

    //A standard and important property of ∀: It distributes over conjunction. This is useful to justify prenex normal form.
    val thm2 = Theorem ( (∀(x,  Q(x)) /\ ∀ (x, R(x))) <=> ∀(x, Q(x) /\ R(x)) ) {

        //Here we prove the two directions of <=> separately and then combine them.
        val forward = have((∀(x,  Q(x)), ∀(x, R(x))) |- ∀(x, Q(x) /\ R(x))) subproof {
            have((Q(x), R(x)) |- Q(x) /\ R(x)) by Restate
            thenHave((∀(x, Q(x)), R(x)) |- Q(x) /\ R(x)) by LeftForall
            thenHave((∀(x, Q(x)), ∀(x, R(x))) |- Q(x) /\ R(x)) by LeftForall
            thenHave(thesis) by RightForall
        }

        //The second direction
        val backward = have( ∀(x, Q(x) /\ R(x)) |- ∀(x,  Q(x)) /\ ∀(x, R(x)) ) subproof {
            assume(∀(x, Q(x) /\ R(x)))
            val assump = have(Q(x) /\ R(x)) by InstantiateForall
            have(Q(x)) by Weakening(assump)
            val conj1 = thenHave(∀(x, Q(x))) by RightForall
            have(R(x)) by Weakening(assump)
            val conj2 = thenHave(∀(x, R(x))) by RightForall
            have(thesis) by Tautology.from(conj1, conj2)
        }

        have(thesis) by Tautology.from(forward, backward)
    }

    // This theorem requires instantiating the assumption twice, once with x and once with f(x), and then combine the two. 
    // Since x is free is the sequent step1, then step 1 is true with anything substituted for x.
    // We can do such substitution with the "of" keyword.
    // Specifically, `step1 of (x := f(x))` proves the formula P(f(x)) ==> P(f(f(x)))
    val thm3 = Theorem(∀(x, Q(x) ==> Q(f(x))) |- Q(x) ==> Q(f(f(x)))) {
      assume(∀(x, Q(x) ==> Q(f(x))))
      val step1 = have(Q(x) ==> Q(f(x))) by InstantiateForall
      have(thesis) by Tautology.from(step1, step1 of (x := f(x)))
    } 


    //////////////////////////////////
    // Prove the following theorems //
    //////////////////////////////////


    // This Theorem should be straightforward: You simply need to apply the ∀ and the ∃ quantifiers in the good order.
    val thm4 = Theorem( (∀(x, Q(x) ==> P), ∃(x, Q(x))) |- P ) {
        assume(∀(x, Q(x) ==> P))
        val instance = have(Q(x) ==> P) by InstantiateForall
        //val same = have(∃(x, Q(x))) by ???
        have(thesis) by Tautology.from(instance)
    }

    // This theorem is also short. 
    val thm5 = Theorem( ! ∀(x, Q(x)) |- ∃(x, !Q(x)) ) {
        assume(! ∀(x, Q(x)))
        have(∃(x, !Q(x))) by Restate // What is alpha equivalence?
        thenHave(thesis)
    }

    // Quantifiers are not very nice to use.
    // The following theorem, called Russel's Paradox in Set theory, is equivalent to |- !∃(x, ∀(y, (y ∈ x) <=> !(y ∈ y)))
    // If we can, we prefer to avoid using the top level quantifier! Here x is a free parameter: The sequent is true for any term substituted for x.
    val thm6 = Theorem( ∀(y, (y ∈ x) <=> !(y ∈ y)) |- () ) {
        assume(∀(y, (y ∈ x) <=> !(y ∈ y)))
        val paradox = have((y ∈ x) <=> !(y ∈ y)) by InstantiateForall
        have(thesis) by Tautology.from(paradox of (y := x)) // Why can I not rename `x`?
    }

    //Again, free variables in a sequent are implicitly universaly quantified: The statement hold with any term substituted for x.
    val thm7 = Theorem( (Q(x), R(x)) |- (∃(y, Q(y)) /\ ∃(y, R(y))) )  {
        val distribute = have(∃(x, Q(x) /\ R(x))  |- (∃(y, Q(y)) /\ ∃(y, R(y)))) subproof {
            assume(∃(x, Q(x) /\ R(x)))
            val assump = have(∃(x, Q(x) /\ R(x))) by Restate
            val q = have( ∃(y, Q(y)) ) by Weakening(assump) of (x:=y)
            val r = have( ∃(y, R(y)) ) by Weakening(assump) of (x:=y)
            have(thesis ) by Tautology.from(q, r)
        }
        have((Q(x), R(x)) |- Q(x) /\ R(x)) by Restate
        val e = thenHave((Q(x), R(x)) |- ∃(x, Q(x) /\ R(x))) by RightExists
        have(thesis) by Tautology.from(e, distribute)
    }

    // This theorem is a bit more involved
    val thm8 = Theorem( ∃(y, ∀(x, Q(y) ==> Q(x) )) ) {
        val qInvalid = have(∃(y, !Q(y)) |- ∃(y, ∀(x, Q(y) ==> Q(x)))) subproof {
            /*
            assume(!Q(y))
            have(Q(y) ==> Q(x)) by Restate
            thenHave(∀(x, Q(y) ==> Q(x))) by RightForall
            thenHave(∃(y, ∀(x, Q(y) ==> Q(x)))) by RightExists
            thenHave(thesis) by LeftExists
            */
            have(!Q(y) |- !Q(y)) by Restate
            thenHave(!Q(y) |- (Q(y) ==> Q(x))) by Restate
            thenHave(!Q(y) |- ∀(x, Q(y) ==> Q(x))) by RightForall
            thenHave(!Q(y) |- ∃(y, ∀(x, Q(y) ==> Q(x)))) by RightExists
            thenHave(thesis) by LeftExists
        }
        
        val qValid = have( ∀(y, Q(y)) |- ∃(y, ∀(x, Q(y) ==> Q(x)))) subproof {
            assume(∀(y, Q(y)))
            have(∀(x, Q(x))) by Restate of (y := x)
            thenHave(∀(x, Q(y) ==> Q(x))) by Weakening
            thenHave(thesis) by RightExists
        }
        
        have(thesis) by Tautology.from(qInvalid, qValid)
    }




    // This theorem is more complex. it says that "If all poor person have a rich father, then there is a rich person with a rich grandfather".
    // If you're stuck, make sure to first prove the statement with pen and paper.
    val father = function[1]
    val rich = predicate[1]

    /* 
     * 0) either a person or their father is rich
     * 1) pick arbitrary x0 who's rich
     * 2) x0 must have poor grandfather (negation of conclusion)
     *
     * case 1) if x0 has poor father, violate premise
     *
     * case 2) if x0 has rich father (RFx0), then x0's greatgrandpa is poor (FFFx0) (negation of conclusion)
     *          x0's poor grandfather has a poor father (FFFx0), violate premise !RFFx0 ===> RFFFx0
     */
    val richGrandfather = Theorem(∀(x, !rich(x) ==> rich(father(x))) |- ∃(x, rich(x) /\ rich(father(father(x)))) ) {
        assume(∀(x, !rich(x) ==> rich(father(x))))

        val contradiction = have(∀(x, !rich(x) ==> rich(father(x))) /\ !(∃(x, rich(x) /\ rich(father(father(x))))) |- ()) subproof {
            assume(∀(x, !rich(x) ==> rich(father(x))))
            assume(!(∃(x, rich(x) /\ rich(father(father(x))))))
            
            have(!rich(x) ==> rich(father(x))) by InstantiateForall
            val premise = thenHave(rich(x) \/ rich(father(x))) by Restate
            have(∀(x, !rich(x) \/ !rich(father(father(x))))) by Restate
            val negConclusion = thenHave(!rich(x) \/ !rich(father(father(x)))) by InstantiateForall(x)

            val contr = have ( rich(x) |- ()) subproof {
                assume(rich(x))
                val poorGrandpa = have( !rich(father(father(x)))) by Tautology.from(negConclusion)

                val poorFather = have( !rich(father(x)) |- ()) subproof {
                    assume(!rich(father(x)))
                    val c = have(rich(father(x)) \/ rich(father(father(x)))) by Tautology.from(premise of (x := father(x)))

                    have(thesis) by Tautology.from(c, poorGrandpa)
                }
                
                val richFather = have( rich(father(x)) |- ()) subproof{
                    assume(rich(father(x)))
                    have(!rich(father(x)) \/ !rich(father(father(father(x))))) by Tautology.from(negConclusion of (x := father(x)))
                    val poorGrGrandpa = thenHave(!rich(father(father(father(x))))) by Restate // tautalogy?? 
                    
                    val substitutedPremise = have(rich(father(father(x)))  \/  rich(father(father(father(x))))) by Tautology.from(premise of (x:= father(father(x))))
                    have(thesis) by Tautology.from(poorGrGrandpa, poorGrandpa, substitutedPremise)
                }

                have(thesis) by Tautology.from(poorFather, richFather)
            }
            
            have(thesis) by Tautology.from(contr, contr of (x:= father(x)), premise) 
        }

        have(thesis) by Tautology.from(contradiction)
    }


    val canFly = predicate[1]
    val happy = predicate[1]
    val green = predicate[1]
    val child = predicate[2]


    val greenDragonsAreHappy = Theorem((
        ∀(x, ( ∀(y, child(x, y) ==> canFly(y)) ==> happy(x) ) ), // A dragon is happy if all its children can fly
        ∀(x, canFly(x)),                                         // Dragons can fly
        ∀(x, ( ∃(y, green(y) /\ child(y, x)) ==> green(x) ) )    // A dragon is green if it is a child of at least one green dragon
    ) |- ∀(x, green(x) ==> happy(x))                             // All green dragons are happy
    ) {
        assume(∀(x, ( ∀(y, child(x, y) ==> canFly(y)) ==> happy(x) ) ))
        assume(∀(x, canFly(x)))
        assume(∀(x, ( ∃(y, green(y) /\ child(y, x)) ==> green(x) )))
        
        have(canFly(y)) by InstantiateForall of (x := y)
        thenHave(child(x, y) ==> canFly(y)) by Weakening // Why not `Restate`?
        val p = thenHave(∀(y, child(x, y) ==> canFly(y))) by RightForall

        val q = have(∀(y, child(x, y) ==> canFly(y)) ==> happy(x)) by InstantiateForall
        have(happy(x)) by Tautology.from(p, q) // or `Restate`?
        thenHave(green(x) ==> happy(x)) by Weakening // Why not `Restate`?
        
        thenHave(thesis) by RightForall
    }
}
