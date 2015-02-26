/*
 * Implementation of a dependently typed lambda calculus based on the paper
 * 
 *     An Implementation of a dependently typed lambda calculus
 *     Andres Loh, Conor McBride, and Wouter Swierstra
 *     Fundamenta Informaticae, 2008
 * 
 *  The orginal paper describes a Haskell implementaiton and at the
 *  time of writing I was learning the basics of implementing
 *  dependetly type languages and also introducing myself to Scala,
 *  hence it seemed interesing to reimplement their work in Scala.
 * 
 */
package org

package object utils {
  object Printer extends org.kiama.output.PrettyPrinter {
    def parensIf( b : Boolean , d : Doc ) : Doc = if (b) parens(d) else d
  }
}

package object lambdapi {

  import org.kiama.output.PrettyPrinter
  import org.kiama.attribution.Attributable
  import org.kiama.util.ParserUtilities
  import org.kiama.util.PositionedParserUtilities
  import scala.util.{Try,Success,Failure}

  case class ErrorException(msg: String) extends RuntimeException(msg)
  object ErrorException {
    def create(msg: String) : ErrorException  = ErrorException(msg)
    def create(msg: String, cause: Throwable) =
      ErrorException(msg).initCause(cause)
  }

  /*
   *  First we define the AST representation for LambdaPI, whose
   *  grammar is defined by the following BNF
   *  
   *  The term language:
   * 
   *     e ::= e : p                  annotated term
   *         | *                      type of types (i.e. kind)
   *         | Nat                    type of natural numbers
   *         | Zero                   base case, i.e. 0, for natural numbers
   *         | [0-9]+                 alternative numeric representation for natural numbers
   *         | Succ (e)               the inductive case, i.e. successor of a natural number
   *         | natElim e e e e        Eliminator for natural numbers (see McBride's paper on elimination with motive)
   *         | forall (a : e)+ . e    dependent function space (PI)
   *         | e -> e                 non-dependent function space
   *         | x                      variable
   *         | $$                     shorthand to refer to last expression evaluated in command processor
   *         | e e                    application
   *         | \x+ . e                lambda abstraction
   * 
   *  The language of values:
   * 
   *     v ::= n                      netural term
   *         | *                      type of types
   *         | Nat                    type of natural numbers
   *         | Zero                   base case for natural numbers
   *         | Succ (n)               inductive case for natural numbers
   *         | forall (a : v)+ . e    dependent function space
   *         | \x+ . v                lambda abstraction
   * 
   *  Note non-dependent function space is provided only as a syntatic
   *  convience and not represented in the AST itself as it is just a
   *  degenerate form of dependent function space
   */

  // Terms
  sealed abstract class Name
  case class Global( g : String ) extends Name
  case class Local ( l : Int )    extends Name
  case class Quote ( i : Int )    extends Name

  sealed abstract class TermInfer
  case class Ann(e : TermCheck, t : TermCheck)           extends TermInfer
  case class Star()                                      extends TermInfer
  case class Pi( d : TermCheck, t : TermCheck)           extends TermInfer
  case class Bound( i : Int)                             extends TermInfer
  case class Free( n : Name)                             extends TermInfer
  case class App( lhs : TermInfer, rhs : TermCheck)      extends TermInfer

  // Natural numbers
  case class Nat() extends TermInfer
  case class Zero() extends TermInfer
  case class Succ( n : TermCheck ) extends TermInfer
  case class NatElim( t1 : TermCheck, t2 : TermCheck, t3 : TermCheck, t4 : TermCheck ) extends TermInfer

  implicit class IApp(val i: TermInfer) extends AnyVal {
    def $$(that: TermCheck) = new App(this.i, that)
  }

  sealed abstract class TermCheck
  case class Inf ( t : TermInfer ) extends TermCheck
  case class Lam ( l : TermCheck ) extends TermCheck 

  // Values
  sealed abstract class Value
  case class VLam ( f : (Value => Value) )          extends Value
  case class VStar()                                extends Value
  case class VPi( v : Value, f : (Value => Value) ) extends Value
  case class VNeutral ( n : Neutral )               extends Value

  // Natural numbers
  case class VNat()                                 extends Value
  case class VZero()                                extends Value
  case class VSucc( n : Value )                     extends Value

  sealed abstract class Neutral
  case class NFree ( n : Name ) extends Neutral
  case class NApp ( a : Neutral, v : Value ) extends Neutral
  case class NNatElim ( v1: Value, v2 : Value, v3: Value, n : Neutral ) extends Neutral

  // create a value from a free variable
  def vfree ( n : Name ) : Value =
    VNeutral (NFree (n))

  // some natural number helper functions
  def toInt( n : Value ) : Int = n match {
    case VZero()  => 0
    case VSucc(n) => 1 + toInt(n)
    case _        => throw ErrorException.create("not a number")
  }

  def canConvertToInt ( n : Value ) : Boolean = n match {
    case VZero()  => true
    case VSucc(n) => canConvertToInt(n)
    case _        => false
  }

  def canConvertToInt ( n : TermInfer ) : Boolean = n match {
    case Zero()  => true
    case Succ(n) => canConvertToInt(n)
    case _        => false
  }

  def canConvertToInt ( n : TermCheck ) : Boolean = n match {
    case Inf(n)  => canConvertToInt(n)
    case _        => false
  }

  def toNat( i : Int ) : TermInfer = if (i <= 0 ) Zero() else Succ ( Inf (toNat(i - 1)) )

  def lookup[A] ( k : Name, c : Vector[(Name,A)]) : A =
    c match {
      case IndexedSeq() => throw ErrorException.create("undefined identifier")
      case a +: cs      => if (a._1 == k) a._2 else lookup(k,cs)
    }

  // now we define the evaluator
  type Env = (Vector[(Name,Value)], Vector[Value])

  object Eval {
    def eval ( t : TermInfer, env : Env ) : Value =
      t match  {
        case Ann(e, t)  => eval(e, env)
        case Star()     => VStar()
        case Zero()     => VZero()
        case Nat()      => VNat()          
        case Succ(n)    => VSucc( eval(n, env) )

        case NatElim(m, mz, ms, k) => {
          val mzVal  = eval(mz, env)
          val msVal = eval(ms, env)

          def rec ( kVal : Value ) : Value = kVal match {
            case VZero()     => mzVal
            case VSucc(l)    => vapp( vapp(msVal, l), rec(l) )
            case VNeutral(k) => VNeutral(NNatElim(eval(m,env), mzVal, msVal, k))
            case _           => throw ErrorException.create("should not get here")
          }

          rec (eval(k, env))
        }

        case Pi(t1, t2) => VPi(eval(t1, env), (x) => eval(t2, (env._1, x +: env._2)))
        case Free(x)    => (Try(lookup(x,env._1)) recover { case _ => vfree(x) }) get
        case Bound(i)   => env._2(i)
        case App(f,e)   => vapp( eval(f, env), eval(e, env) )
      }

    def vapp ( v1 : Value, v2 : Value ) : Value =
      v1 match {
        case VLam(f)     => f(v2)
        case VNeutral(n) => VNeutral( NApp(n,v2) )
        case _ => throw new RuntimeException // Should not happen
      }

    def eval ( t : TermCheck, env : Env ) : Value =
    t match {
      case Inf(i) => eval(i, env)
      case Lam(e) => VLam ((x) => eval( e, (env._1, x +: env._2 )))
    }

    def quote( v : Value ) : TermCheck = quote(0, v)

    def quote( i : Int, v : Value ) : TermCheck =
      v match {
        case VLam(f)     => Lam( quote(i+1, f(vfree(Quote(i))) ) )
        case VStar()     => Inf( Star() )
        case VPi(v,f)  => Inf( Pi(quote(i, v), quote(i+1, f(vfree(Quote(i))) ) ))
        case VNeutral(n) => Inf( neutralQuote(i,n) )

        case VNat()   => Inf( Nat() )
        case VZero()  => Inf( Zero() )
        case VSucc(n) => Inf( Succ( quote(i, n) ) )
      }

    def neutralQuote( i : Int, n : Neutral ) : TermInfer =
      n match {
        case NFree(x)  => boundfree(i, x)
        case NApp(n,v) => App( neutralQuote(i, n), quote(i,v) )
        case NNatElim(m,mz,ms,k) =>
          NatElim(quote(i,m), quote(i,mz), quote(i,ms), Inf(neutralQuote(i,k)))
      }


    def boundfree (i : Int, n : Name) : TermInfer =
      n match {
        case Quote(k) => Bound(i - k - 1)
        case x        => Free(x)
      }
  }

  // now define the typechecker

  type Result[A] = Try[A]
  type Type = Value
  type Context = Vector[(Name,Type)]

  def dummy( s : String ) : Result[Type] = {
    println(s)
    Success(VZero())
  }

  object Typing {

    def typeTerm ( c : Context, t : TermInfer ) : Result[Type] =
      typeTerm(0, c, t)

    def typeTerm ( i : Int, c : Context, t : TermInfer ) : Result[Type] =
      t match {
        case Ann(e, p)     => for {
          _ <- typeTerm(i, c, p, VStar())
          val t = Eval.eval(p, (Vector(), Vector()))  
          tt <- typeTerm(i, c, e, t)
        } yield(t)

        case Star()        => Success(VStar())
        case Nat()         => Success(VStar())
        case Zero()        => Success(VNat())
        case Succ(n)       => for {
          _ <- typeTerm(i, c, n, VNat())
        } yield(VNat())

        case NatElim(m,mz,ms,k) => for {
          _ <- typeTerm(i, c, m, VPi(VNat(), (_) => VStar()) )
          val mVal = Eval.eval(m, (Vector(), Vector()))
          _ <- typeTerm(i, c, mz, Eval.vapp(mVal, VZero()))
          _ <- typeTerm(i, c, ms, VPi(VNat(), (l) => VPi(Eval.vapp(mVal,l), (_) => Eval.vapp(mVal,VSucc(l)))))
          _ <- typeTerm(i, c, k, VNat())
          val kVal = Eval.eval(k, (Vector(), Vector()))
        } yield(Eval.vapp(mVal, kVal))

        case Pi(p1, p2)    => for {
          _ <- typeTerm(i, c, p1, VStar())
          val t = Eval.eval(p1, (Vector(), Vector()))
          _ <- typeTerm(i+1, (Local(i),t) +: c, subst(0,Free(Local(i)), p2), VStar())
        } yield(VStar())

        case Bound(i)     =>
          throw ErrorException.create("typeTerm should not have received bound")

        case Free(n)      => Try( lookup(n,c) )

        case App(e1,e2) => for {
          s <- typeTerm(i, c, e1)
          r <- s match {
            case VPi(t1, t2) => for {
              tt <- typeTerm(i, c, e2, t1)
            } yield( t2( Eval.eval(e2,(Vector(), Vector())) ) )
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
            r <- if (Eval.quote(ty) == Eval.quote(tt)) Success()
                 else throw ErrorException.create("type mismatch " + ty.toString + " " + tt.toString)
          } yield(r)
        case (Lam(e),VPi(t1,t2)) =>
          typeTerm(
            i+1,
            (Local(i),t1) +: c,
            subst(0, Free(Local(i)), e),
            t2(vfree(Local(i))) )
        case (_,_) =>
          throw ErrorException.create("type mismatch " + e + " " + t)
      }

    def subst( i : Int, r : TermInfer, t : TermInfer ) : TermInfer =
      t match {
        case Ann(e,t)   => Ann(subst(i, r, e), subst(i, r, t))
        case Star()     => Star()
        case Nat()      => Nat()
        case Zero()     => Zero()
        case Succ(n)    => Succ( subst(i,r,n) )
        case NatElim(t1,t2,t3,t4) =>
          NatElim( subst(i, r, t1),  subst(i, r, t2), subst(i, r, t3), subst(i, r, t4))
        case Pi(t1, t2) => Pi(subst(i, r, t1), subst(i+1, r, t2))
        case Bound(j)   => if (i == j) r else Bound(j)
        case Free(y)    => Free(y)
        case App(f,e)   => App( subst(i,r,f), subst(i,r,e) )
      }

    def subst( i : Int, r : TermInfer, t : TermCheck ) : TermCheck =
      t match {
        case Inf(e) => Inf (subst(i,r,e))
        case Lam(e) => Lam (subst(i+1, r, e))
      }
  }

  // parser for LambdaPi

  trait Parser extends PositionedParserUtilities {
    import scala.collection.immutable.Seq
    import scala.language.postfixOps

    class Bindings( b : Boolean, e: List[String] )
        extends PackratParser[(List[String], List[TermCheck])] {

      // parse one or more parens bindings
      class BindingsRec( b : Boolean, e: List[String], ts: List[TermCheck] )
        extends PackratParser[(List[String], List[TermCheck])] {

        lazy val pp : PackratParser[(String,TermCheck)] = parens (
          variable ~ (":" : Parser[String]) ~ pTermCheck(e) ^^
            { case v ~ ":" ~ e => (v,e) })

        def apply(s: org.lambdapi.Parser.Input) = pp(s) match {
          case Success(a, rem) => {
            val bi = if (b) new BindingsRec(b, a._1 :: e, a._2 :: ts)
                     else   new BindingsRec(b, e, ts)

              bi(rem) match {
                case Success(aa, remm) =>
                  if (b) Success(aa,remm)
                  else Success((a._1 :: (aa._1 ++ e), a._2 :: (aa._2 ++ ts)), remm)
                case _                 => Success((a._1 :: e, a._2 :: ts), rem)
              }
          }
          case f: Failure => f
          case _ => throw new RuntimeException // remove warnings
        }
      }

      // parse only a single binding with no parens
      lazy val alt : PackratParser[(List[String],List[TermCheck])] =
        variable ~ (":" : Parser[String]) ~ pTermCheck(e) ^^
      { case v ~ ":" ~ t => (v :: e, List(t)) }

      def apply(s: org.lambdapi.Parser.Input) =
        new BindingsRec(b, e, List())(s) match {
          case Success(a, rem) => Success(a,rem)
          case f: Failure => {
            alt(s)
          }
          case _ => throw new RuntimeException // remove warnings
      }
    }

    def bindings(b : Boolean, e : List[String]) :
        Parser[(List[String], List[TermCheck])] = new Bindings(b, e)

    val lastStr : String = "_last"

    def pTermInfer ( e : List[String] ) : Parser[TermInfer] = 
     presZero(e)

    def presZero ( e : List[String] ) : Parser[TermInfer] =
      forall(e) | funarrow(e) | presOne(e)

    def forall ( e : List[String] ) : Parser[TermInfer] =
      Parser[TermInfer] { in =>
        ("forall" ~  new Bindings(true, e))(in) match {
          case Success("forall" ~ bs, rem) => ("." ~ pTermCheck(bs._1) ^^
              { case "." ~ t =>
                bs._2.tail.foldLeft(Pi(bs._2 head,t)) ((a,b) => Pi(bs._2 head, Inf(a)))
              } )(rem)
          case f : Failure => f
          case _ => throw new RuntimeException // remove warnings
        }
      }

    def funarrow ( e : List[String] ) : Parser[TermInfer] = {
      presOne(e) ~ "->" ~ pTermCheck("" :: e) ^^ {
        case ti ~ "->" ~ tc => Pi(Inf(ti), tc) }
    }

    def presOne ( e : List[String] ) : Parser[TermInfer] =
      annLambda(e) | presTwo(e)

    def annLambda ( e : List[String] ) : Parser[TermInfer] =
      (presTwo(e) ~ ":" ~ pTermCheck(e) ^^ {
        case ti ~ ":" ~ tc => Ann(Inf(ti), tc)
      }) | (parens(pLambda(e)) ~ ":" ~ pTermCheck(e) ^^ {
        case tc1 ~ ":" ~ tc2 => Ann(tc1,tc2)
      })

    def presTwo ( e : List[String] ) : Parser[TermInfer] =
      presThree(e) ~ rep(pTermCheckPresThree(e)) ^^ {
        // note that we don't allow partial application of natElim, just lambdas...
        case (Free(Global("natElim"))) ~ (t1 :: t2 :: t3 :: t4 :: ts) =>
          ts.foldLeft(NatElim(t1,t2,t3,t4) : TermInfer) ((a,b) => a $$ b)
        case t ~ ts => ts.foldLeft(t) ((a,b) => a $$ b) } | presThree(e)

    def presThree ( e : List[String] ) : Parser[TermInfer] =
       star | nat(e) | "$$" ^^ { _ => Free(Global(lastStr)) } | identifier(e) |  parens( pTermInfer(e) )

    def identifier ( e : List[String] ) : Parser[TermInfer] =
      variable ^^ { v => e.indexOf(v) match {
        case -1 => Free(Global (v))
        case n  => Bound(n)
      } }

    def  pTermCheck ( e : List[String] ) : Parser[TermCheck] =
      pLambda(e) | pTermInfer(e) ^^ { t => Inf(t) } | parens( pLambda(e) )

    def  pTermCheckPresThree ( e : List[String] ) : Parser[TermCheck] =
      pLambda(e) | presThree(e) ^^ { t => Inf(t) } | parens( pLambda(e) )

    // maybe I'm being dumb but it would be nice if Monad syntax worked here!!
    def pLambda(e : List[String] ) : Parser[TermCheck] =
      Parser[TermCheck] { in =>
        ("\\" ~ rep1(variable))(in) match {
          case Success("\\" ~ xs, rem) => ("." ~ pTermCheck(xs.reverse ++ e) ^^
            { case "." ~ t => xs.foldRight(t)((a,b) => Lam(b)) } )(rem)
          case f : Failure => f
          case _ => throw new RuntimeException // remove warnings
        }
      }

    def nat( e : List[String] ) : Parser[TermInfer] =
      "Nat" ^^ { _ => Nat() } |
      "[0-9]+".r ^^ { n => toNat(n.toInt) } |
      "Zero" ^^ { _ => Zero() } |
      "Succ" ~> parens(pTermCheck(e)) ^^ { Succ }

    lazy val star = "*" ^^ { _ => Star() }

    lazy val variable : Parser[String] =
      idn

    lazy val idn : Parser[String] =
      not (keyword) ~> "[a-zA-Z][a-zA-Z0-9]*".r

    lazy val keyword : Parser[String] =
      "let" | "assume" | "forall" | "$$"

    def parens[A]( p : Parser[A] ) : Parser[A] =
      "(" ~> p <~ ")"

  }

  // We need this as Parser is only a trait and we want to be able to
  // direclty reference members (i still find the Scala parser
  // combinators somewhat odd for this reason)
  object Parser extends Parser

  // Pretty printer for LambdaPi

  object Printer extends org.kiama.output.PrettyPrinter {

    def pretty (s : Name) : String =
      super.pretty (show (s))

    def show (n : Name) : Doc =
      n match {
        case Local(l)  => value (l)
        case Global(g) => value (g)
        case Quote(i)  => value (i)
      }

    def pretty (e : TermInfer) : String =
      super.pretty (show(0,e)._2)

    val vars : Stream[String] =
      for {
        n <- "" #:: (Stream.from(1).map { i => i.toString } )
        c <- Stream('x','y','z') ++ Stream.range('a', 'x')
      } yield ( c.toString ++ n )


    // introduce a little Haskell list syntax here
    implicit class Vars(val s : Stream[String]) extends AnyVal {
      private def element(s : Stream[String], i : Int) : String =
        if (i <= 0) s.head else element(s.tail, i-1)

      def !!(i: Int) = element(s, i)
    }

    def show (i : Int, e : TermInfer) : (Int, Doc) =
      e match {
        case Ann(e,t) => {
          val tmp  = show(i, e)
          (tmp._1, tmp._2 <+> ":" <+> show(i, t)._2)
        }
        case Star() => (i, "*")
        case Nat() => (i, "Nat")
        case Zero() => (i, "0")
        case Succ(n) =>
          // special case printing complex (but "real") natural numbers
          if (canConvertToInt(Succ(n)))
            (i, value(toInt(Eval.eval(Succ(n), (Vector(),Vector())) )))
          else {
            val tmp = show(i,n)
            (tmp._1, "Succ(" <> tmp._2 <> ")")
          }
    
        case NatElim(t1,t2,t3,t4) => {
          val tmp1 = show(i, t1)
          val tmp2 = show(tmp1._1, t2)
          val tmp3 = show(tmp2._1, t3)
          val tmp4 = show(tmp3._1, t4)

          (tmp4._1, "natElim" <+> parens(tmp1._2) <> " " <+> parens(tmp2._2)
                    <> " " <+> parens(tmp3._2) <> " " <+> parens(tmp1._2))
        }

        case Pi(t1, t2) => {
          val (i1, d1) = show(i, t1)
          val (i2, d2) = show(i+1,t2)
          (i2, ("forall" <+> parens((vars !! i) <+> ":" <+> d1) <+> "." <+> parens( d2 ) ))
        }

        case Bound(ii) => (i, vars !! (i - ii - 1))
        case Free(n)  => (i, show(n))

        case App(lhs, rhs) =>
          (i, parens( show(i, lhs)._2 ) <+> parens( show(i, rhs)._2 ))
      }

    def pretty (e : TermCheck) : String =
      super.pretty (show(0,e)._2)

    def show(i : Int, e : TermCheck ) : (Int, Doc) =
      e match {
        case Inf(t) => show(i, t)
        case Lam(l) => {
          val (ii,d) = show(i, l)
          (ii+1, "\\" <> (vars !! ii) <> "." <+> d)
        }
      }

    def pretty (v : Value) : String =
      super.pretty (show (v))

    def show( v : Value ) : Doc =
//      if (canConvertToInt(v)) value(toInt(v))
      show(0, Eval.quote(v))._2
  }
} // package object lambdapi


package object commands {
  import org.kiama.attribution.Attributable
  import org.kiama.util.ParserUtilities
  import org.lambdapi._

  // evaluation environment
  var env     : Vector[(Name,Value)] = Vector()

  // the last expr evaluated and its type
  var last    : (Value,Value) = (VNat(), VStar())

  // type context
  var context : Context = Vector()

  /*
   *  Following in the sprit of the orignal work we support a 
   *  simple, Gofer inspired, interpreter
   */
  sealed abstract class Command extends Attributable
  case class CExpr( t : TermInfer )             extends Command
  case class CLet( n : Name, t : TermInfer )    extends Command
  case class CAssume( as : List[(Name, TermCheck)] ) extends Command
  case class CTypeOf( t : TermInfer )           extends Command
  case class CBrowse()                          extends Command
  case class CLoad ( filename : String )        extends Command
  case class CHelp ()                           extends Command
  case class CNull ()                           extends Command

  trait CommandParser extends ParserUtilities with org.lambdapi.Parser {
    import scala.collection.immutable.Seq
    import scala.language.postfixOps

    lazy val parser =
      phrase (command)

    lazy val command : PackratParser[Command] =
       assume | let | cexpr |  internal

    lazy val cexpr = pTermInfer(List()) ^^
       { case t => CExpr(t) }

    lazy val assume = ("assume" | "a") ~ bindings(false, List()) ^^ {
      case a ~ bs => CAssume( (bs._1 zip bs._2) map (v => (Global(v._1), v._2)) )
    }

    lazy val let = ("let" | "l") ~ variable ~ "=" ~ pTermInfer(List()) ^^ {
      case l ~ v ~ "=" ~ e => CLet(Global(v), e)
    }

    lazy val internal = ":" ~> (help | browse | typeOf | load)

    lazy val load = ("load" | "l") ~> filepath ~ filename ^^ { case p ~ fn => CLoad(p + fn) }

    lazy val filepath : Parser[String] = "[\\w/]*/".r
    lazy val filename : Parser[String] = "[\\w]+\\.lpi".r

    lazy val help   = ("help" | "h" | "?")  ^^ { _ => CHelp() }
    lazy val typeOf = ("type" | "t") ~ pTermInfer(List()) ^^ { case s ~ t => CTypeOf(t) } 
    lazy val browse = ("browse" | "b") ^^ { _ => CBrowse() }
  }

} // package object commands

// Finally we define the REPL based on Kiama's
object Main extends org.kiama.util.ParsingREPL[org.commands.Command]
            with org.commands.CommandParser {
  import org.commands._
  import org.kiama.util.REPLConfig

  private def displayHelp() : Unit = {
    println(
      """List of commands:  
      | Any command may be abbreviated to :c where
      | c is the first character in the full name.
      |
      | <expr>                  evaluate expression 
      |                         ($$ refers to the last expr evaluated)
      |
      | let <var> = <expr>      define variable
      | assume <var> :: <expr>  assume variable
      |
      | :type <expr>            print type of expression
      | :browse                 browse names in scope
      | :load <file>            load program from file
      | :^D                     exit interpreter
      | :help, :?               display this list of commands""".stripMargin)
  }

  val banner =
    """Lambda Pi - fun with dependent types.
    | Type :? for help and ^D to exit""".stripMargin

  override def prompt = "LP> "

  override def process (c : Command, config : REPLConfig) {
    val output = config.output
    c match {
      case CHelp()    => displayHelp()

      case CExpr(e)   => org.lambdapi.Typing.typeTerm(
        (org.lambdapi.Global(org.lambdapi.Parser.lastStr), last._2) +: context, e) match {
        case scala.util.Success(t)  => {
          val ev = org.lambdapi.Eval.eval(e,
            ((org.lambdapi.Global(org.lambdapi.Parser.lastStr), last._1) +: env, Vector()))
          last = (ev, t)
          println(
            org.lambdapi.Printer.pretty(ev) +
            " : " +
            org.lambdapi.Printer.pretty(t)
          )
        }
        case scala.util.Failure(ex) => println(s"ERROR: ${ex.getMessage}")
      }

      case CAssume(as) => 
        as map ( a => {
        val e = org.lambdapi.Ann( a._2, (org.lambdapi.Inf(org.lambdapi.Star())) )
        org.lambdapi.Typing.typeTerm(context, e) match {
          case scala.util.Success(t)  =>
            context = (a._1, org.lambdapi.Eval.eval(a._2, (env, Vector()))) +: context
          case scala.util.Failure(ex) => println(s"ERROR: ${ex.getMessage}")
        }
        })

      case CLet(n, e) => org.lambdapi.Typing.typeTerm(context, e) match {
        case scala.util.Success(t)  => {
          env = (n, org.lambdapi.Eval.eval(e, (env, Vector()))) +: env
          context = (n, t) +: context
          println(
            org.lambdapi.Printer.pretty(n) + " : " + org.lambdapi.Printer.pretty(t)
          )
        }
        case scala.util.Failure(ex) => println(s"ERROR: ${ex.getMessage}")
      }
 
      case CBrowse() => {
        context.foldRight( () ) ( (c,b) =>
          println(org.lambdapi.Printer.pretty(c._1) + " : " + org.lambdapi.Printer.pretty(c._2)) )
      }

      case CLoad(fn) => println(fn)

      case CTypeOf(e) => org.lambdapi.Typing.typeTerm(context, e) match {
        case scala.util.Success(t)  => println(org.lambdapi.Printer.pretty(t))
        case scala.util.Failure(ex) => println(s"ERROR: ${ex.getMessage}")
      }
        // still need to add the remaining commands...

      case _ => throw new RuntimeException // Should not happen
    }
  }
}
