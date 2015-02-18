/*
 * Implementation of a dependently typed lambda calculus based on the paper
 * 
 *     An Implementation of a dependently typed lambda calculus
 *     Andres Loh, Conor McBride, and Wouter Swierstra
 *     Fundamenta Informaticae, 2008
 * 
 *  The orginal paper describes a Haskell implementaiton and at the
 *  time of writing I was learning the basics of implementing
 *  dependetly type languages and at the same time introducing myself
 *  to Scala it seemed interesing to reimplement their work in Scala.
 * 
 */
package org
package object lambdapi {

  import scala.util.parsing.combinator._
  import org.kiama.output.PrettyPrinter
  import scala.util.{Try,Success,Failure}

  case class ErrorException(msg: String) extends RuntimeException(msg)
  object ErrorException {
    def create(msg: String) : ErrorException  = ErrorException(msg)
    def create(msg: String, cause: Throwable) = ErrorException(msg).initCause(cause)
  }

  // Terms
  sealed abstract class Name
  case class Global( g : String ) extends Name
  case class Local ( l : Int )    extends Name
  case class Quote ( i : Int )    extends Name

  sealed abstract class TermInfer
  case class Ann(e : TermCheck, t : Type)                extends TermInfer
  case class Bound( i : Int)                             extends TermInfer
  case class Free( n : Name)                             extends TermInfer
  case class App( lhs : TermInfer, rhs : TermCheck)      extends TermInfer

  sealed abstract class TermCheck
  case class Inf ( t : TermInfer ) extends TermCheck
  case class Lam ( l : TermCheck ) extends TermCheck 

  // Types
  sealed abstract class Type
  case class TFree ( n : Name )         extends Type
  case class Fun ( a : Type, r : Type ) extends Type

  // Values
  sealed abstract class Value
  case class VLam ( f : (Value => Value) ) extends Value
  case class VNeutral ( n : Neutral ) extends Value

  sealed abstract class Neutral
  case class NFree ( n : Name ) extends Neutral
  case class NApp ( a : Neutral, v : Value ) extends Neutral

  // create a value from a free variable
  def vfree ( n : Name ) : Value =
    VNeutral (NFree (n))

  type Env = Vector[Value]

  object Eval {
    def eval ( t : TermInfer, env : Env ) : Value =
      t match  {
        case Ann(e, t) => eval(e, env)
        case Free(x)   => vfree(x)
        case Bound(i)  => env(i)
        case App(f,e)  => vapp( eval(f, env), eval(e, env) )
      }

    def vapp ( v1 : Value, v2 : Value ) : Value =
      v1 match {
        case VLam(f)     => f(v2)
        case VNeutral(n) => VNeutral( NApp(n,v2) )
      }

  def eval ( t : TermCheck, env : Env ) : Value =
    t match {
      case Inf(i) => eval(i, env)
      case Lam(e) => VLam ((x) => eval( e, x +: env ))
    }
  }

  sealed abstract class Kind
  case class Star() extends Kind

  sealed abstract class Info
  case class HasKind( k : Kind ) extends Info
  case class HasType( t : Type ) extends Info

  type Result[A] = Try[A]

  object Typing {

    type Context = Vector[(Name,Info)]
    def lookup ( k : Name, c : Context) : Result[Info] =
      c match {
        case IndexedSeq() => throw ErrorException.create("undefined identifier")
        case a +: cs      => if (a._1 == k) Success(a._2) else lookup(k,cs)
      }

    def kind ( c : Context, t : Type, k : Kind) : Result[Unit] =
      (t,k) match {
        case (TFree(x), Star()) =>
          Try(lookup(x,c)).map( (x) => Success() )
        case (Fun(k1,k2), Star()) => for {
          _ <- kind(c, k1, Star())
          _ <- kind(c, k2, Star())
        } yield (Success())
      }

    def typeTerm ( c : Context, t : TermInfer ) : Result[Type] =
      typeTerm(0, c, t)

    def typeTerm ( i : Int, c : Context, t : TermInfer ) : Result[Type] =
      t match {
        case Ann(e, t)     => for {
          k  <- kind(c, t, Star())
          tt <- typeTerm(i, c, e, t)
        } yield(t)

        case Bound(i)     =>
          throw ErrorException.create("typeTerm should received bound")

        case Free(n)      =>
          lookup(n,c) match {
            case Success(HasType(ty)) => Success(ty)
            case _          => throw ErrorException.create("undefined identifier")
          }

        case App(lhs,rhs) => for {
          s <- typeTerm(i, c, lhs)
          r <- s match {
            case Fun(t1, t2) => for {
              tt <- typeTerm(i, c, rhs, t1)
            } yield(t2)
            case _ =>
              throw ErrorException.create("illegal application")
          }
        } yield(r)

      }

    def typeTerm( i : Int, c : Context, e : TermCheck, t : Type) : Result[Unit] =
      (e, t) match {
        case (Inf(ee), tt) =>
          for {
            ty  <- typeTerm(i, c, ee)
            r <- if (ty == tt) Success()
                 else throw ErrorException.create("type mismatch")
          } yield(r)
        case (Lam(e),Fun(a,r)) =>
          typeTerm(i+1, ((Local(i),HasType(a)) +: c), subst(0, Free(Local(i)), e), r)
        case (_,_) =>
          throw ErrorException.create("type mismatch")
      }

    def subst( i : Int, r : TermInfer, t : TermInfer ) : TermInfer =
      t match {
        case Ann(e,t) => Ann(subst(i, r, e), t)
        case Bound(j) => if (i == j) r else Bound(j)
        case Free(y)  => Free(y)
        case App(f,e) => App( subst(i,r,f), subst(i,r,e) )
      }

    def subst( i : Int, r : TermInfer, t : TermCheck ) : TermCheck =
      t match {
        case Inf(e) => Inf (subst(i,r,e))
        case Lam(e) => Lam (subst(i+1, r, e))
      }
  }


  object Parser extends JavaTokenParsers {
  }

  object Printer extends org.kiama.output.PrettyPrinter {
  }

  val id = Lam ( Inf (Bound(0)))
  val const = Lam (Lam (Inf (Bound (1))))
  val tfree = (a : String)  => TFree (Global(a))
  val free  = (x : String ) => Inf (Free (Global(x)))
  val term1 = App( Ann(id, Fun( tfree("a"), tfree("a"))), free("y"))

  val env1 = Vector(
    (Global("y"), HasType(tfree("a"))),
    (Global("a"),HasKind(Star())) )
} // package object minicl

object Main {
  def main ( args : Array[String] ) = {
    if (args.length > 0 ) {
    }
  }
}
