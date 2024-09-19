
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
  def x(i: Int): Formula = Var(i)

  case class Var(id: Int) extends Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case object True extends Formula
  case object False extends Formula



  // Evaluation of boolean formulas

  def eval(f: Formula, env: Int => Boolean): Boolean = f match {
    case Var(id) => env(id)
    case And(lhs, rhs) => eval(lhs, env) && eval(rhs, env)
    case Or(lhs, rhs) => eval(lhs, env) || eval(rhs, env)
    case Implies(lhs, rhs) => !eval(lhs, env) || eval(rhs, env)
    case Not(f) => !eval(f, env)
    case True => true
    case False => false
  }

  // Substitution of boolean formulas
  def substitute(f: Formula, env: Int => Formula): Formula = f match {
    case Var(id) => env(id)
    case And(lhs, rhs) => And(substitute(lhs, env), substitute(rhs, env))
    case Or(lhs, rhs) => Or(substitute(lhs, env), substitute(rhs, env))
    case Implies(lhs, rhs) => Implies(substitute(lhs, env), substitute(rhs, env))
    case Not(f) => Not(substitute(f, env))
    case True => True
    case False => False
  }

  // Negation normal form

  def nnf(f: Formula): Formula = f match {
    case Var(_) => f
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Implies(lhs, rhs) => Or(nnf(Not(lhs)), nnf(rhs))
    case Not(Var(_)) => f
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(True) => False
    case Not(False) => True
  }

  def variables(f: Formula): Set[Int] = f match {
    case Var(id) => Set(id)
    case And(lhs, rhs) => variables(lhs) ++ variables(rhs)
    case Or(lhs, rhs) => variables(lhs) ++ variables(rhs)
    case Implies(lhs, rhs) => variables(lhs) ++ variables(rhs)
    case Not(f) => variables(f)
    case True => Set()
    case False => Set()
  } 

  def validity(f: Formula): Boolean = {
    def variables(f: Formula): Set[Int] = f match {
      case Var(id) => Set(id)
      case And(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Or(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Implies(lhs, rhs) => variables(lhs) ++ variables(rhs)
      case Not(f) => variables(f)
      case True => Set()
      case False => Set()
    }
    variables(f).subsets.forall(subset => eval(f, id => subset.contains(id)))
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
  def y(id: Int) = AIG_Var(id, true)

  case class AIG_Var(id: Int, polarity: Boolean) extends AIG_Formula {
    infix def unary_! = AIG_Var(id, !polarity)
  }
  case class AIG_Node(lhs: AIG_Formula, rhs: AIG_Formula, polarity: Boolean ) extends AIG_Formula

  def AIG_eval(f: AIG_Formula, env: Int => Boolean): Boolean = f match {
    case AIG_Var(id, polarity) => polarity == env(id)
    case AIG_Node(lhs, rhs, polarity) => polarity == (AIG_eval(lhs, env) && AIG_eval(rhs, env))
  }

  def AIG_variables(f: AIG_Formula): Set[Int] = f match {
    case AIG_Var(id, _) => Set(id)
    case AIG_Node(lhs, rhs, _) => AIG_variables(lhs) ++ AIG_variables(rhs)
  }

  def AIG_validity(f: AIG_Formula): Boolean = {
    AIG_variables(f).subsets.forall(subset => AIG_eval(f, id => subset.contains(id)))
  }

  def formulaToAIG(f: Formula): AIG_Formula = {
    def notaig(f:AIG_Formula) = AIG_Node(f, f, false)
    f match {
      case Var(id) => AIG_Var(id, true)
      case Not(Var(id)) => AIG_Var(id, false)
      case And(lhs, rhs) => AIG_Node(formulaToAIG(lhs), formulaToAIG(rhs), true)
      case Or(lhs, rhs) => AIG_Node(formulaToAIG(!lhs), formulaToAIG(!rhs), false)
      case Implies(lhs, rhs) => AIG_Node(formulaToAIG(lhs), formulaToAIG(!rhs), false)
      case Not(And(lhs, rhs)) => AIG_Node(formulaToAIG(lhs), formulaToAIG(rhs), false)
      case Not(Or(lhs, rhs)) => AIG_Node(formulaToAIG(!lhs), formulaToAIG(!rhs), true)
      case Not(Implies(lhs, rhs)) => AIG_Node(formulaToAIG(lhs), formulaToAIG(!rhs), true)
      case Not(Not(f)) => formulaToAIG(f)
      case True => AIG_Node(y(0), !y(0), false)
      case False => AIG_Node(y(0), !y(0), true)
    }
  }







}