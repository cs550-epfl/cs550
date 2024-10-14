import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
import stainless.lang.Map.ToMapOps

import Utils.*
import Formulas.*
import Resolution.MansionFragments.charlesInnocent
import Formulas.Literal

object Resolution {
  /**
   * Make sure that all bound variables are uniquely named, and with names different from free variables.
   * This will simplify a lot future transformations. The specific renaming can be arbitrary.
   */
  def makeVariableNamesUnique(f: Formula): Formula = {
    /*
     * A generator of fresh names
     * Any call to `get` should be followed by a call to `next`
     */
    case class FreshNames(i: BigInt) {
      require(i >= 0)

      // Return a fresh identifier
      def get: Identifier = Synthetic(i)
      // Update (functionally) this generator
      def next = FreshNames(i + 1)
    }

    def mVNUForm(subst: Map[Identifier, Term])(f: Formula, freshId0: FreshNames): (Formula, FreshNames) = {
      decreases(f)
      f match {
        case Predicate(name, children) => (Predicate(name, children.map(t => t.substitute(subst))), freshId0)
        case And(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (And(nLeft, nRight), freshId2)
        case Or(left, right)  =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Or(nLeft, nRight), freshId2)
        case Implies(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Implies(nLeft, nRight), freshId2)
        case Neg(inner) =>
          val (nInner, freshId1) = mVNUForm(subst)(inner, freshId0)
          (Neg(nInner), freshId1)
        case Forall(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Forall(x, p._1), p._2)
        case Exists(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Exists(x, p._1), p._2)
      }
    }

    // Generate fresh names for free variables
    val (alreadyTaken, freshId) = statefulLeftMap(
      f.freeVariables,
      FreshNames(0),
      (v: Identifier, id: FreshNames) => ((v, Var(id.get): Term), id.next)
    )
    mVNUForm(alreadyTaken.toMap)(f, freshId)._1
  }

  /* Part one: transforming formulas */

  /*
   * Put the formula in Negation Normal Form.
   */
  def negationNormalForm(f: Formula): Formula = {
    /* TODO: Implement me */
    decreases(f)
    f match {
      case And(left, right) => 
        And(negationNormalForm(left), negationNormalForm(right))
      case Neg(And(left, right)) =>
        Or(negationNormalForm(Neg(left)), negationNormalForm(Neg(right)))
      
      case Or(left, right) =>
        Or(negationNormalForm(left), negationNormalForm(right))
      case Neg(Or(left, right)) =>
        And(negationNormalForm(Neg(left)), negationNormalForm(Neg(right)))
          
      case Implies(left, right) => 
        Or(negationNormalForm(Neg(left)), negationNormalForm(right))
      case Neg(Implies(left, right)) =>
        And(negationNormalForm(left), negationNormalForm(Neg(right)))

      case Forall(Var(id), inner) => 
        Forall(Var(id), negationNormalForm(inner))
      case Neg(Forall(Var(id), inner)) => 
        Exists(Var(id), negationNormalForm(Neg(inner)))

      case Exists(Var(id), inner) =>
        Exists(Var(id), negationNormalForm(inner))
      case Neg(Exists(Var(id), inner)) =>
        Forall(Var(id), negationNormalForm(Neg(inner)))

      case Neg(Neg(inner)) => negationNormalForm(inner)

      case _ => f
    }
  }.ensuring(res =>
    res.isNNF
  )

  /**
   * Backtracking to transform existential quantifiers into Skolem functions
   */
  def skolemization(f: Formula)(using subst: Map[Identifier, Term],
                                      quantified: List[Identifier]): Formula = {
    require(f.isNNF)
    decreases(f)
    f match {
      case Exists(Var(id), inner) => {
        // Replace all occurances of id in inner with skolem fn
        val skolemFn = Function(Named("skolem_" + id.toString()), quantified.map(Var(_)) )
        skolemization(inner)(using subst + (id -> skolemFn), quantified)
      }
      case Forall(Var(id), inner) =>
        Forall(Var(id), skolemization(inner)(using subst, quantified :+ id))
      
      case Predicate(name, children) =>
        Predicate(name, children.map(_.substitute(subst)))
      case And(left, right) =>
        And(skolemization(left), skolemization(right))
      case Or(left, right) =>
        Or(skolemization(left), skolemization(right))
      case Implies(left, right) =>
        Implies(skolemization(left), skolemization(right)) // TODO: convert to NNF
      case Neg(inner) =>
        Neg(skolemization(inner))
    }
  }.ensuring(res => 
    res.isNNF && res.containsNoExistential  
  )

  /**
   * Perform the following steps:
   * - Make variable names unique (using [[makeVariableNamesUnique]]);
   * - Put the formula in negation normal form (using [[negationNormalForm]]);
   * - Eliminate existential quantifiers using Skolemization.
   */
  def skolemizationNegation(f0: Formula): Formula = {
    /* TODO: Implement me */
    val f1 = negationNormalForm(makeVariableNamesUnique(f0))
    //assert(f1.freeVariables.isEmpty)
    skolemization(f1)(using Map.empty, List.empty)
    //negationNormalForm(f2)
  }.ensuring(res =>
    res.isNNF && res.containsNoExistential
  )

  /**
   * 
   */
  def prenex(f: Formula): Formula = {
    require(f.containsNoExistential && f.isNNF)
    decreases(f)
    f match {
      case Predicate(name, children) => f
      case And(left, right) => And(prenex(left), prenex(right))
      case Or(left, right) => Or(prenex(left), prenex(right))
      case Implies(left, right) => Implies(prenex(left), prenex(right)) // TODO: convert to NNF
      case Neg(inner) => Neg(prenex(inner))
      case Forall(Var(id), inner) => prenex(inner)
      // This case does not exist.
      case Exists(Var(id), inner) =>
        Exists(Var(id), prenex(inner))
    }
  }.ensuring(res =>
    res.isNNF && res.containsNoUniversal && res.containsNoExistential
  )

  /**
   * Perform the following steps:
   * - Put the formula in negation normal, skolemized form (using [[skolemizationNegation]]);
   * - Return the matrix? of the formula.
   */
  def prenexSkolemizationNegation(f: Formula): Formula = {
    /* TODO: Implement me */
    val _f = skolemizationNegation(f)
    prenex(_f)
  }.ensuring(res =>
    res.isNNF && res.containsNoUniversal && res.containsNoExistential
  )

  /** 
   *
   */
  def conjunction(f: Formula): List[Clause] = {
    f match {
      case p@Predicate(name, children) =>
        List(List(Literal(p)))
      case Or(left, right) => {
        val _left:  List[Clause] = conjunction(left)
        val _right: List[Clause] = conjunction(right)
        _left.foldLeft(List.empty[Clause])((wip: List[Clause], cl: Clause) => 
          wip ++ _right.map((cr: Clause) => cr ++ cl)
        )
        // `stainless` `List` does not support `foreach` method, thus no
        // support for `<-` syntactic sugar.
        /*
        var res = List.empty[Clause]
        for (l <- _left) {
          for (r <- _right) {
            res = res :+ (l ++ r)
          }
        }
        res
        */
      }
      case And(left, right) =>
        conjunction(left) ++ conjunction(right)
      case _ => List.empty[Clause]
    }
  }

  /**
   * Perform the following steps:
   * - Put the formula in prenex, negation normal, skolemized form (using [[prenexSkolemizationNegation]]);
   * - Put the formula in conjunctive normal form (CNF).
   *
   * Note that the formula might grow exponentially in size.
   * If we only want to preserve satisfiability, we could avoid it by introducing fresh variables.
   * This function should NOT do that.
   */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
    /* TODO: Implement me */
    val _f = prenexSkolemizationNegation(f)
    conjunction(_f)
  }

  /* Part two: proof checking */

  /**
   * A clause in a proof is either assumed, i.e. it is an hypothesis, or it is deduced from previous clauses.
   * A proof is written in a specific order, and a justification should not refer to a subsequent step.
   */
  sealed abstract class Justification
  case object Assumed extends Justification
  case class Deduced(premises: (BigInt, BigInt), subst: Map[Identifier, Term]) extends Justification

  type ResolutionProof = List[(Clause, Justification)]

  sealed trait ProofCheckResult {
    def valid = this match {
      case Valid => true
      case Invalid(_) => false
    }
  }
  case object Valid extends ProofCheckResult
  case class Invalid(reason: String = "Unspecified") extends ProofCheckResult {
    @extern
    override def toString(): String = {
      reason
    }
  }

  /**
   * Verify that [[proof]] is a valid proof, i.e. that every clause is correctly justified (unless assumed).
   * It is quite easy to miss some corner cases. We thus recommend that you:
   * - Have a look at the provided methods on Literal, as you will most likely need them;
   * - "Keep It Simple, Stupid!": efficiency is not taken into account, so no need for fancy efficient checks;
   * - On the other hand, checking that the conclusion of a resolution step is valid might be a bit more involved
   *   than it seems;
   * - As a consequence of the previous point: add more tests;
   * - You should return [[Valid]] when the proof is valid, and [[Invalid]] otherwise.
   *   In the latter case, you are free to set any string as the reason. Having precise failure reasons will help
   *   you a lot in the third part of this lab.
   *
   * Note: in order to use string interpolation in stainless, you need to wrap it in an extern function, e.g.
   * @extern def mkErrorMessage = s"This is an error at step ${k}"
   * Invalid(mkErrorMessage)
   */
  def checkResolutionProof(proof: ResolutionProof): ProofCheckResult = {
    /* TODO: Implement me */
    val assumptions = this.assumptions(proof)
    val conclusion = this.conclusion(proof)

    def verifyProofStep(index: BigInt, step: (Clause, Justification)): ProofCheckResult = {
      val clause = step._1
      val justification = step._2

      justification match {
        case Assumed => Valid
        case Deduced((i, j), subst) => {
          if (i >= index || j >= index) {
            Invalid("Deduced step refers to a future step")
          }

          // Do work here.

          Valid
        }
        case _ => Invalid()
      }
    }

    // Go through each step of the resolution proof and verify each clause is valid or not. If any step is invalid, return invalid.
    proof.foldLeft[ProofCheckResult](Valid)((res, step) =>
      res match {
        case Valid => verifyProofStep(proof.indexOf(step), step)
        case _ => res // Invalid Case
      }
    )
  }

  def assumptions(proof: ResolutionProof): List[Clause] = {
    proof
      .filter(_._2 match {
        case Assumed        => true
        case Deduced(_, _)  => false
      })
      .map(_._1)
  }

  def conclusion(proof: ResolutionProof): Clause = {
    require(!proof.isEmpty)
    proof(proof.length-1)._1
  }

  /* Part three: The Dreadsbury Mansion Mystery */
  object MansionFragments {
    import Mansion.*
    /** 
     * You can use the (scala) variable killer to refer to the killer
     * E.g. of a proof step using it: The killer is one of the characters
     * ( List(eqv(killer, a), eqv(killer, b), eqv(killer, c)), Deduced((0, 5), Map(id(1) -> killer)) )
     */

    def charlesInnocent: ResolutionProof = {
      List(
        /* TODO: Complete me */
      )
    }

    /*
     * k is the index your first step will have in the final proof.
     * You can use it to refer to previous steps relatively to this index,
     * so that your proof won't break if you go back and change your previous one.
     *
     * Mansion.buildFullProof contains all of the steps we implemented in your stead
     * and indexed them relatively to k.
     */
    def agathaKilledAgatha(k: BigInt): ResolutionProof = {List(
        /* TODO: Complete me */
      )
    }
  }

  /*
   * To show that a formula phi is valid, we show that it's negation is unsatisfiable, i.e. !phi -> false.
   * Hence if a Proof contains an empty clause, then the negation of the conjunction of all assumed clauses has to be valid
   */
  def extractTheorem(proof: ResolutionProof): Formula = {
    require(!assumptions(proof).isEmpty && assumptions(proof).forall(!_.isEmpty))  // Has "reasonable" assumptions
    require(proof.last._1 == Nil()) // Concludes unsat

    def toFormulas(clauses: List[Clause]): List[Formula] = {
      require(clauses.forall(!_.isEmpty))

      clauses match {
        case Nil() => Nil()
        case Cons(c, cs) => Cons(or(c.map(_.get)), toFormulas(cs))
      }
    }

    val assumpts = toFormulas(assumptions(proof))
    assert(!assumpts.isEmpty)

    Neg(and(assumpts))
  }

}
