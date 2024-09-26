
import stainless.lang._
import stainless.collection._
import stainless.annotation._
 
/* 
 * The definition of List and its operations can be found here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala
 * You should not need them, but you can find some lemmas on List here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/ListSpecs.scala
 */

def sublist[T](l1: List[T], l2: List[T]): Boolean = {
  (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && sublist(xs, ys)) || sublist(l1, ys)
  }
}

@extern
@main
def main(): Unit = {
  def example(lhs: List[Int], rhs: List[Int]): Unit = {
    println(s"${lhs.toScala.mkString("<", ",", ">")} ⊑ ${rhs.toScala.mkString("<", ",", ">")} = ${sublist(lhs, rhs)}")
  }

  example(List(0, 2), List(0, 1, 2))
  example(List(0, 0, 2), List(0, 2))
  example(List(1, 0), List(0, 0, 1))
  example(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))
  example(List(25, 11, 53, 38), List(15, 25, 11, 8, 53, 22, 38))
}

object SublistSpecs {
 
  /* forall l, sublist(l, l) */
  def reflexivity[T](l: List[T]): Unit = {
    /* TODO: Prove me */
    /*
    // Recursively prove that the list is a sublist of itself
    decreases(l)
    // base case: the empty list is a sublist of itself
    if !l.isEmpty then {
      // recursive case: check with subset(l.tail) of the list
      reflexivity(l.tail)
    }
    */
    l match {
      case Nil() => ()
      case Cons(_, xs) => reflexivity(xs)
    }
  }.ensuring(_ =>
    sublist(l, l)
  )

  def leftTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && sublist(l1, l2))

    /* TODO: Prove me */
    if (sublist(l1, l2.tail))
      leftTail(l1, l2.tail)
    else
      ()
  }.ensuring(_ =>
    sublist(l1.tail, l2)
  )

  def tails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && sublist(l1, l2))
 
    /* TODO: Prove me */
    /*
    // base case
    if (l1.size == 1 || l2.size == 1) {
      return ()
    }

    // recursive case
    (l1.tail, l2.tail) match {
      case (Nil(), _)                 => ()
      case (_, Nil())                 => ()
      case (Cons(x1, x1s), Cons(y1, y1s)) => {
        leftTail(l1, l2) // Prove that l1.tail <= l2
        if (x1 != y1 && !y1s.isEmpty) {
          leftTail(l1.tail, l2.tail.tail)
        } 
      }
    }
    */
    if (sublist(l1, l2.tail))
      leftTail(l1, l2.tail)
    else 
      ()
  }.ensuring(_ =>
    sublist(l1.tail, l2.tail)
  )


  
  def transitivity[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l3))
 
    /* TODO: Prove me */
    /*
    l1 match
      case Nil() => ()
      case Cons(x, xs) =>
        val (Cons(y, ys), Cons(z, zs)) = (l2, l3)··
        if x == y && y == z then
          tails(l1, l2)
          tails(l2, l3)
          transitivity(l1.tail, l2.tail, l3.tail)
        else if x != y && sublist(l1, l2.tail) then
          leftTail(l2, l3)
          transitivity(l1, l2.tail, l3)
        else if y != z && sublist(l2, l3.tail) then
          transitivity(l1, l2, l3.tail)
    */
    if (l1.size == 0) {
      return ()
    }
    if (sublist(l1, l2.tail) &&  sublist(l2, l3.tail)) {
      leftTail(l2, l3.tail)
      transitivity(l1, l2.tail, l3.tail)
    } else if (sublist(l2, l3.tail)) {
      transitivity(l1,l2,l3.tail)
      //assert()
    }
    else if (sublist(l1, l2.tail)) {
      transitivity(l1, l2.tail, l3.tail)
    }
    else{
      transitivity(l1.tail, l2.tail, l3.tail)
      assert(l1.head == l2.head && l2.head == l3.head)
      assert(sublist(l1.head :: l1.tail, l3.head :: l3.tail))
    }
  }.ensuring(_ =>
    sublist(l1, l3)
  )  
 
  // def lengthHomomorphism[T](l1: List[T], l2: List[T]): Unit = {
  //   require(sublist(l1, l2))
 
  //   /* TODO: Prove me */
  // }.ensuring(_ =>
  //   l1.length <= l2.length
  // )
 
  // def biggerSublist[T](l1: List[T], l2: List[T]): Unit = {
  //   require(sublist(l1, l2) && l1.length >= l2.length)
 
  //   /* TODO: Prove me */
  // }.ensuring(_ =>
  //   l1 == l2
  // )
 
  // def antisymmetry[T](l1: List[T], l2: List[T]): Unit = {
  //   require(sublist(l1, l2) && sublist(l2, l1))
 
  //   /* TODO: Prove me */
  // }.ensuring(_ =>
  //   l1 == l2
  // )

  // /* 
  // * ++ is the list concatenation operator.
  // * It is defined here: 
  // * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala#L46
  // */
  // def extendRight[T](l1: List[T], l2: List[T]): Unit = {
  //   /* TODO: Prove me */
  // }.ensuring(_ => 
  //   sublist(l1, l1 ++ l2)  
  // )

  // def extendLeft[T](l1: List[T], l2: List[T]): Unit = {
  //   /* TODO: Prove me */
  // }.ensuring(_ => 
  //   sublist(l2, l1 ++ l2)  
  // )

  // def prepend[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
  //   require(sublist(l1, l2))

  //   /* TODO: Prove me */
  // }.ensuring(_ =>
  //   sublist(l ++ l1, l ++ l2)  
  // )

  // def append[T](l1: List[T], l2: List[T], l: List[T]): Unit = {
  //   require(sublist(l1, l2))

  //   /* TODO: Prove me */
  // }.ensuring(_ =>
  //   sublist(l1 ++ l, l2 ++ l)  
  // )
}
