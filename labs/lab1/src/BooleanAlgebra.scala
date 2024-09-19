
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

  def eval(f: Formula, env: Int => Boolean): Boolean = ??? // TODO

  // Substitution of boolean formulas
  def substitute(f: Formula, env: Int => Formula): Formula = ??? // TODO

  // Negation normal form

  def nnf(f: Formula): Formula = ??? // TODO

  def variables(f: Formula): Set[Int] = ??? // TODO

  def validity(f: Formula): Boolean = ??? // TODO

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

  def AIG_eval(f: AIG_Formula, env: Int => Boolean): Boolean = ??? // TODO

  def AIG_variables(f: AIG_Formula): Set[Int] = ??? // TODO

  def AIG_validity(f: AIG_Formula): Boolean = ??? // TODO

  def formulaToAIG(f: Formula): AIG_Formula = ??? // TODO


}