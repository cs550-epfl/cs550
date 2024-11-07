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
        assume(x <= y)

        // ((x u y) <= y) /\ (y <= (x u y)))  
        val s1 = have((x u y) <= y) by Tautology.from(lub of (z := y), reflexivity of (x := y))
        val s2 = have(y <= (x u y)) by Tautology.from(joinLowerBound)

        have(thesis) by Tautology.from(s1, s2, antisymmetry of (x := y, y := (x u y)))
    }

    val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
        have (thesis) by Tautology.from(glb of (z:= (x n y)), reflexivity of (x := (x n y)))
    }

    val meetCommutative = Theorem((x n y) === (y n x)) {
        val s1 = have ((y n x) <= (x n y)) by Tautology.from(glb of (z := (y n x)), meetUpperBound of (x := y, y := x))
        have (thesis) by Tautology.from(s1, s1 of (x:=y, y:=x), antisymmetry of (x := x n y, y := y n x))
    }

    val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
        assume(x <= y)

        // ((x n y) <= x) /\ (x <= (x n y)))  
        val s1 = have(x <= (x n y)) by Tautology.from(glb of (z := x), reflexivity)
        val s2 = have((x n y) <= x) by Tautology.from(meetUpperBound)
        have (thesis) by Tautology.from(s1, s2, antisymmetry of (x := x, y := (x n y)))
    }


    val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
        // Prove (x u (y u z)) <= ((x u y) u z) 
        val s1 = have((x u (y u z)) <= ((x u y) u z)) subproof {
            // lub (z := (x u y) u z), y := (y u z)) gives ((x <= (x u y) u z)) /\ ((y u z) <= (x u y) u z))) <=> ((x u (y u z)) <= (x u y) u z))

            // Show (x <= (x u y) u z))
            val _x = have(x <= ((x u y) u z)) by Tautology.from(
                joinLowerBound, 
                joinLowerBound of (x := (x u y), y := z), 
                transitivity of (y := (x u y), z := ((x u y) u z))
            )
            // Show (y u z) <= ((x u y) u z))
            // - show y <= (x u y) u z
            val _y = have (y <= ((x u y) u z)) by Tautology.from(
                joinLowerBound,
                joinLowerBound of (x := (x u y), y := z),
                transitivity of (x := y, y := (x u y), z := ((x u y) u z))
            )
            // - show z <= (x u y) u z
            //val _z = have(z <= ((x u y) u z)) by Tautology.from(joinLowerBound of (x := (x u y)))
            
            val yuz = have((y u z) <= ((x u y) u z)) by Tautology.from(
                _y, 
                joinLowerBound of (x := (x u y), y := z), 
                lub of (x := y, y := z, z := (x u y) u z)
            )
            // Show ((x u (y u z)) <= (x u y) u z))
            have(thesis) by Tautology.from(_x, yuz, lub of (y := (y u z), z := (x u y) u z))
        }

        // Prove ((x u y) u z) <= x u (y u z)
        val s2 = have(((x u y) u z) <= (x u (y u z))) subproof {
            // Show (z <= (x u (y u z)))
            val _z = have(z <= (x u (y u z))) by Tautology.from(
                joinLowerBound of (x := y, y := z), 
                joinLowerBound of (y := (y u z)), 
                transitivity of (x := z, y := (y u z), z := (x u (y u z)))
            )
            // Show ((x u y) <= (x u (y u z)))
            // - show (x <= (x u (y u z)))
            //val _x = have(x <= (x u (y u z))) by Tautology.from(joinLowerBound of (y := (y u z)))

            // - show (y <= (x u (y u z)))
            val _y = have(y <= (x u (y u z))) by Tautology.from(
                joinLowerBound of (x := y, y := z),
                joinLowerBound of (y := (y u z)),
                transitivity of (x := y, y := (y u z), z := (x u (y u z)))
            )

            val xuy = have((x u y) <= (x u (y u z))) by Tautology.from(
                joinLowerBound of (y := (y u z)),
                _y,
                lub of (z := (x u (y u z)))
            )
            // Show ((x u y) u z) <= (x u (y u z))
            have(thesis) by Tautology.from(xuy, _z, lub of (x:= (x u y), y:= z, z := (x u (y u z))))
        }

        have(thesis) by Tautology.from(s1, s2, antisymmetry of (x := x u (y u z), y := ((x u y) u z)))
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
                                if s1.isValid && s2.isValid then
                                    have (left <= right) by Tautology.from(lub of (x := a, y := b, z:= right), have(s1), have(s2))
                                else
                                    return proof.InvalidProofTactic("The inequality is not true in general")

                            //2. right is a meet. In that case, glb gives us the decomposition
                            case (_, n(a: Term, b: Term)) => 
                                //solve recursively left <= a and left <= b
                                val s1 = solve(left <= a)
                                val s2 = solve(left <= b)
                                if s1.isValid && s2.isValid then
                                    have (left <= right) by Tautology.from(glb of (x := a, y:= b, z:= left), have(s1), have(s2))
                                else
                                    return proof.InvalidProofTactic("The inequality is not true in general")

                            //3. left is a meet, right is a join. In that case, we try all pairs.
                            case (n(a: Term, b: Term), u(c: Term, d: Term)) =>
                                val ac = Try(solve(a <= c)).toOption
                                val ad = Try(solve(a <= d)).toOption
                                val bc = Try(solve(b <= c)).toOption
                                val bd = Try(solve(b <= d)).toOption

                                if ac.isDefined then
                                    have(left <= right) by Tautology.from(
                                        meetUpperBound of (x:=a, y:=b), // (a n b) <= a
                                        have(ac.get), // a <= c
                                        transitivity of (x := (a n b), y := a, z := c), //  if ... then (a n b) <= c
                                        joinLowerBound of (x:=c, y:=d), // c <= (c u d)
                                        transitivity of (x := (a n b), y := c, z := (c u d)) // if ... then (a n b) <= (c u d)
                                    )
                                else if ad.isDefined then
                                    have(left <= right) by Tautology.from(
                                        meetUpperBound of (x := a, y := b), // (a n b) <= a
                                        have(ad.get), // a <= d
                                        transitivity of (x := (a n b), y := a, z := d), //  if ... then (a n b) <= d
                                        joinLowerBound of (x := c, y := d), // d <= (c u d)
                                        transitivity of (x := (a n b), y := d, z := (c u d)) // if ... then (a n b) <= (c u d)
                                    )
                                else if bc.isDefined then
                                    have(left <= right) by Tautology.from(
                                        meetUpperBound of (x := a, y := b), // (a n b) <= b
                                        have(bc.get), // b <= c
                                        transitivity of (x := (a n b), y := b, z := c), //  if ... then (a n b) <= c
                                        joinLowerBound of (x := c, y := d), // c <= (c u d)
                                        transitivity of (x := (a n b), y := c, z := (c u d)) // if ... then (a n b) <= (c u d)
                                    )
                                else if bd.isDefined then
                                    have(left <= right) by Tautology.from(
                                        meetUpperBound of (x := a, y := b), // (a n b) <= b
                                        have(bd.get), // b <= d
                                        transitivity of (x := (a n b), y := b, z := d), //  if ... then (a n b) <= d
                                        joinLowerBound of (x := c, y := d), // d <= (c u d)
                                        transitivity of (x := (a n b), y := d, z := (c u d)) // if ... then (a n b)
                                    )
                                else 
                                    proof.InvalidProofTactic("The inequality is not true in general")
                            //4. left is a meet, right is a variable or unknown term.
                            case (n(a: Term, b: Term), _) =>
                                val s1 = Try(solve(a <= right)).toOption
                                val s2 = Try(solve(b <= right)).toOption

                                if s1.isDefined then
                                    have (left <= right) by Tautology.from(
                                        have(s1.get), // a < right
                                        meetUpperBound of (x := a, y:= b), // (a n b) <= a
                                        transitivity of (x := (a n b), y := a, z := right)
                                    )
                                else if s2.isDefined then
                                    have (left <= right) by Tautology.from(
                                        have(s2.get), // b < right
                                        meetUpperBound of (x:= a, y:= b), // (a n b) <= b
                                        transitivity of (x := (a n b), y := b, z := right)
                                    )
                                else
                                    proof.InvalidProofTactic("The inequality is not true in general")
                            //5. left is a variable or unknown term, right is a join.
                            case (_, u(c: Term, d: Term)) =>
                                val s1 = Try(solve(left <= c)).toOption
                                val s2 = Try(solve(left <= d)).toOption
                           
                                    
                                if s1.isDefined then
                                    have (left <= right) by Tautology.from(
                                        have(s1.get), // left <= c
                                        joinLowerBound of (x := c, y := d), // c <= (c u d)
                                        transitivity of (x := left, y := c, z := right) // if ... then left <= right
                                    )
                                else if s2.isDefined then
                                    have (left <= right) by Tautology.from(
                                        have(s2.get), // left <= d
                                        joinLowerBound of (x := c, y := d), // d <= (c u d)
                                        transitivity of (x := left, y := d, z := right) // if ... then left <= right
                                    )
                                else 
                                    proof.InvalidProofTactic("The inequality is not true in general")
                            //6. left and right are variables or unknown terms.
                            case _ =>
                                if left == right then
                                    have(left <= right) by Tautology.from(
                                        reflexivity of (x := left)
                                    )
                                else 
                                    proof.InvalidProofTactic("The inequality is not true in general")
                        }
                    }

                    case ===(left: Term, right: Term) => 
                        val s1 = solve(left  <= right)
                        val s2 = solve(right <= left)
                        if s1.isValid && s2.isValid then
                            have(left === right) by Tautology.from(have(s1), have(s2), antisymmetry of (x := left, y := right))
                        else
                            proof.InvalidProofTactic("The equality is not true in general")

                    case _ => return proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t or () |- s === t")
                }
            }
        }
    }


    //uncomment when the tactic is implemented

    val test1 = Theorem(x <= x) {
        have(thesis) by Whitman.solve
    }
    val test2 = Theorem(x <= (x u y)) {
        have(thesis) by Whitman.solve
    }
    val test3 = Theorem((y n x) <= x) {
        have(thesis) by Whitman.solve
    }
    val test4 = Theorem((x n y) <= (y u z)) {
        have(thesis) by Whitman.solve
    }
    val idempotence = Theorem((x u x) === x) {
        have(thesis) by Whitman.solve
    }
    val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
        have(thesis) by Whitman.solve
    }
    val semiDistributivITY = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
        have(thesis) by Whitman.solve
    }

   

}
