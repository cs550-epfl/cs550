//> using scala "3.5.1"
//> using dep "ch.epfl.lara::lisa::0.7,url=https://github.com/epfl-lara/lisa/releases/download/0.7/lisa_3-0.7.jar"

import lisa.automation.Substitution.ApplyRules as Substitution
import lisa.automation.Tableau
import scala.util.Try

object Lab05 extends lisa.Main {

    val x = variable
    val y = variable
    val z = variable

    // We introduce the signature of lattices
    val <= = ConstantPredicateLabel.infix("<=", 2)
    addSymbol(<=)
    val u = ConstantFunctionLabel.infix("u", 2) //join (union for sets, disjunction in boolean algebras)
    addSymbol(u)
    val n = ConstantFunctionLabel.infix("n", 2) //meet (interestion for sets, conjunction in boolean algebras)
    addSymbol(n)

    //Enables infix notation
    extension (left: Term) {
        def <=(right : Term):Formula = (Lab05.<= : ConstantPredicateLabel[2])(left, right)
        infix def u(right : Term):Term = (Lab05.u : ConstantFunctionLabel[2])(left, right)
        infix def n(right : Term):Term = (Lab05.n : ConstantFunctionLabel[2])(left, right)
    }

    // We will now prove some statement about partial orders, which we axiomatize

    val reflexivity  = Axiom(x <= x)
    val antisymmetry = Axiom(((x <= y) /\ (y <= x)) ==> (x === y))
    val transitivity = Axiom(((x <= y) /\ (y <= z)) ==> (x <= z))
    val lub = Axiom(((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
    val glb = Axiom(((z <= x) /\ (z <= y)) <=> (z <= (x n y)))

    //Now we'll need to reason with equality. We can do so with the Substitution tactic, which substitutes equals for equals.
    //The argument of Substitutions can be either an equality (s===t). In this case, the result should contain (s===t) in assumptions.
    //Or it can be a previously proven step showing a formula of the form (s===t). 
    //In this case, assumptions of this precedently proven fact need to be in the assumptions of the conclusion.

    //Note however that Restate and Tautology now by themselves that t === t, for any t.


    val joinLowerBound = Theorem((x <= (x u y)) /\ (y <= (x u y))) {
        have (thesis) by Tautology.from(lub of (z:= (x u y)), reflexivity of (x := (x u y)))
    }


    val joinCommutative = Theorem((x u y) === (y u x)) {
        val s1 = have ((x u y) <= (y u x)) by Tautology.from(lub of (z := (y u x)), joinLowerBound of (x := y, y := x))
        have (thesis) by Tautology.from(s1, s1 of (x:=y, y:=x), antisymmetry of (x := x u y, y := y u x))
    }

    val joinAbsorption = Theorem((x <= y) |- (x u y) === y) {
        sorry //TODO
    }

    val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
        sorry //TODO
    }

    val meetCommutative = Theorem((x n y) === (y n x)) {
        sorry //TODO
    }

    val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
        sorry //TODO
    }


    val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
        sorry //TODO
    }

    //Tedious, isn't it
    //Can we automate this?
    //Yes, we can!


    import lisa.prooflib.ProofTacticLib.ProofTactic
    import lisa.prooflib.Library

    object Whitman extends ProofTactic {
        def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
            if goal.left.nonEmpty || goal.right.size!=1 then
                proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
            else TacticSubproof {  //Starting the proof of `goal`

                goal.right.head match {
                    case <=(left: Term, right: Term) => {
                        //We have different cases to consider
                        (left, right) match {
                            //1. left is a join. In that case, lub gives us the decomposition
                            case (u(a: Term, b: Term), _) => 
                                //solve recursively a <= right and b <= right
                                val s1 = solve(a <= right)
                                val s2 = solve(b <= right)
                                //check if the recursive calls succedded
                                if s1.isValid & s2.isValid then
                                    have (left <= right) by Tautology.from(lub of (x := a, y := b, z:= right), have(s1), have(s2))
                                else return proof.InvalidProofTactic("The inequality is not true in general")

                            //2. right is a meet. In that case, glb gives us the decomposition
                            case (_, n(a: Term, b: Term)) => 
                              ??? //TODO

                            //3. left is a meet, right is a join. In that case, we try all pairs.
                            case (n(a: Term, b: Term), u(c: Term, d: Term)) => 
                              ??? //TODO

                            //4. left is a meet, right is a variable or unknown term.
                            case (n(a: Term, b: Term), _) =>
                              ??? //TODO


                            //5. left is a variable or unknown term, right is a join.
                            case (_, u(c: Term, d: Term)) =>
                              ??? //TODO


                            //6. left and right are variables or unknown terms.
                            case _ =>
                              ??? //TODO
                        }
                    }

                    case ===(left: Term, right: Term) => 
                      ??? //TODO
                    case _ => return proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t or () |- s === t")
                }
            }

        }

    }


    //uncomment when the tactic is implemented

    val test1 = Theorem(x <= x) {
        sorry // have(thesis) by Whitman.solve
    }
    val test2 = Theorem(x <= (x u y)) {
        sorry // have(thesis) by Whitman.solve
    }
    val test3 = Theorem((y n x) <= x) {
        sorry // have(thesis) by Whitman.solve
    }
    val test4 = Theorem((x n y) <= (y u z)) {
        sorry // have(thesis) by Whitman.solve
    }
    val idempotence = Theorem((x u x) === x) {
        sorry // have(thesis) by Whitman.solve
    }
    val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
        sorry // have(thesis) by Whitman.solve
    }
    val semiDistributivITY = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
        sorry // have(thesis) by Whitman.solve
    }

   

}