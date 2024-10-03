
object BooleanAlgebra {


  // AST for boolean formulas

  sealed trait Formula {
    infix def &&(rhs: Formula): Formula = And(this, rhs)
    infix def ||(rhs: Formula): Formula = Or(this, rhs)
    infix def ==>(rhs: Formula): Formula = Implies(this, rhs)
    def unary_! : Formula = Not(this)

    override def toString(): String = this match {
      case Var(id) => s"x($id)"
      case And(lhs, rhs) => s"($lhs && $rhs)"
      case Or(lhs, rhs) => s"($lhs || $rhs)"
      case Implies(lhs, rhs) => s"($lhs ==> $rhs)"
      case Not(f) => s"!$f"
      case True => "True"
      case False => "False"
    }
  }
  def x(id: Int): Formula = Var(id)

  case class Var(id: Int) extends Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case object True extends Formula
  case object False extends Formula



  /**
    * Evaluates a formula under a given environment.
    * An environment is an assignement of boolean values to variables.
    */
  def eval(f: Formula, env: Int => Boolean): Boolean =
    f match {
      case True => true
      case False => false
      case Var(id) => env(id)
      case And(lhs, rhs) => eval(lhs, env) && eval(rhs, env)
      case Or(lhs, rhs) => eval(lhs, env) || eval(rhs, env)
      case Implies(lhs, rhs) => !eval(lhs, env) || eval(rhs, env)
      case Not(f) => !eval(f, env)
    }

  /**
    * Substitutes the variables in a formula with other formulas.
    */
  def substitute(f: Formula, env: Int => Formula): Formula =
    f match {
      case Var(id) => env(id)
      case And(lhs, rhs) => And(substitute(lhs, env), substitute(rhs, env))
      case Or(lhs, rhs) => Or(substitute(lhs, env), substitute(rhs, env))
      case Implies(lhs, rhs) => Implies(substitute(lhs, env), substitute(rhs, env))
      case Not(f) => Not(substitute(f, env))
      case _ => f
    }

  /**
    * Returns the negation normal form of a formula.
    */
  def nnf(f: Formula): Formula =
    f match {
      case True => True
      case Not(True) => False

      case False => False
      case Not(False) => True
      
      case Var(id) => Var(id)
      case Not(Var(id)) => Not(Var(id))

      case Not(Not(_f)) => nnf(_f)

      case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
      case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))

      case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
      case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
      
      case Implies(lhs, rhs) => Or(nnf(Not(lhs)), nnf(rhs))
      case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))

    }

  /**
    * Returns the set of variables in a formula.
    */
  def variables(f: Formula): Set[Int] = {
    f match {
      case Var(id) => Set(id)
      case And(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Or(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Implies(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Not(f) => variables(f)
      case _ => Set()
    }
  }

  /**
    * A formula is valid if it evaluates to true under any environment.
    */
  def validity(f: Formula): Boolean = {  
      val vars: Set[Int] = variables(f)
      lazy val envs: Set[Int => Boolean] = vars.subsets().map { s =>
        val env: Int => Boolean = (id: Int) => s.contains(id)
        env
      }.toSet
  
      envs.forall { env =>
        eval( f, env)
      }
  }

  // And-Inverter Graphs representation
  // (https://en.wikipedia.org/wiki/And-inverter_graph)

  sealed trait AIG_Formula{
    infix def &&(rhs: AIG_Formula): AIG_Formula = AIG_Node(this, rhs, true)
    infix def ↑(rhs: AIG_Formula): AIG_Formula = AIG_Node(this, rhs, false)

    override def toString(): String = this match {
      case AIG_Var(id, true) => s"y($id)"
      case AIG_Var(id, false) => s"!y($id)"
      case AIG_Node(lhs, rhs, true) => s"($lhs && $rhs)"
      case AIG_Node(lhs, rhs, false) => s"($lhs ↑ $rhs)"
    }
  }

  case class AIG_Var(id: Int, polarity: Boolean) extends AIG_Formula {
    infix def unary_! = AIG_Var(id, !polarity)
  }
  case class AIG_Node(lhs: AIG_Formula, rhs: AIG_Formula, polarity: Boolean ) extends AIG_Formula

  def y(id: Int) = AIG_Var(id, true)
  /**
    * Evaluates an AIG formula under a given environment.
    */
  def AIG_eval(f: AIG_Formula, env: Int => Boolean): Boolean = {
    f match {
      case AIG_Var(id, true) => env(id)
      case AIG_Var(id, false) => !env(id)
      case AIG_Node(lhs, rhs, true) => AIG_eval(lhs, env) && AIG_eval(rhs, env)
      case AIG_Node(lhs, rhs, false) => !(AIG_eval(lhs, env) && AIG_eval(rhs, env))
    } 
  }

  /**
    * Returns the set of variables in an AIG_Formula
    */
  def AIG_variables(f: AIG_Formula): Set[Int] = {
    f match {
      case AIG_Var(id, _) => Set(id)
      case AIG_Node(lhs, rhs, _) => AIG_variables(lhs) ++ AIG_variables(rhs)
    }
  }

  /**
    * A formula is valid if it evaluates to true under any environment.
    */
  def AIG_validity(f: AIG_Formula): Boolean = {
    val vars: Set[Int] = AIG_variables(f)
      lazy val envs: Set[Int => Boolean] = vars.subsets().map { s =>
        val env: Int => Boolean = (id: Int) => s.contains(id)
        env
      }.toSet
  
      envs.forall { env =>
        AIG_eval(f, env)
      }
  }

  /**
    * Converts a boolean formula to an AIG formula.
    * The resulting formula should evaluates to the same truth value as the original formula, under every assignment.
    */
  def formulaToAIG(f: Formula): AIG_Formula = {
    f match {

      case True => formulaToAIG(Or(Var(0), Not(Var(0))))  // A || !A ==> !(!A && A) = True
      case False => formulaToAIG(And(Var(0), Not(Var(0)))) // A && !A = False

      case Var(id) => AIG_Var(id, true)
      case Not(Var(id)) => AIG_Var(id, false)

      case Not(Not(f)) => formulaToAIG(f)

      case And(lhs, rhs) => AIG_Node(formulaToAIG(lhs), formulaToAIG(rhs), true)
      case Not(And(lhs, rhs)) => AIG_Node(formulaToAIG(lhs), formulaToAIG(rhs), false)

      case Or(lhs, rhs) => AIG_Node(formulaToAIG(Not(lhs)), formulaToAIG(Not(rhs)), false) // a || b = !(!a && !b)
      case Not(Or(lhs, rhs)) => AIG_Node(formulaToAIG(Not(lhs)), formulaToAIG(Not(rhs)), true) // !(a || b) = !a && !b

      case Implies(lhs, rhs) => AIG_Node(formulaToAIG(lhs), formulaToAIG(Not(rhs)), false) // a ==> b = !a || b = 
      case Not(Implies(lhs, rhs)) => AIG_Node(formulaToAIG(lhs), formulaToAIG(Not(rhs)), true)
    }    
  }
}
