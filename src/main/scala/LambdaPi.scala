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
 *  to Scala, hence it seemed interesing to reimplement their work in Scala.
 * 
 */
package org

package object utils {
  object Parser extends org.kiama.output.PrettyPrinter {
    def parensIf( b : Boolean , d : Doc ) : Doc = if (b) parens(d) else d
  }
}

package object lambdapi {

//  import scala.util.parsing.combinator._
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
        case Ann(e, t)  => eval(e, env)
        case Star()     => VStar()
        case Pi(t1, t2) => VPi(eval(t1, env), (x) => eval(t2, x +: env))
        case Free(x)    => vfree(x)
        case Bound(i)   => env(i)
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
      case Lam(e) => VLam ((x) => eval( e, x +: env ))
    }

    def quote( v : Value ) : TermCheck = quote(0, v)

    def quote( i : Int, v : Value ) : TermCheck =
      v match {
        case VLam(f)     => Lam( quote(i+1, f(vfree(Quote(i))) ) )
        case VStar()     => Inf( Star() )
        case VPi(v,f)  => Inf( Pi(quote(i, v), quote(i+1, f(vfree(Quote(i))) ) ))
        case VNeutral(n) => Inf( neutralQuote(i,n) )
      }

    def neutralQuote( i : Int, n : Neutral ) : TermInfer =
      n match {
        case NFree(x)  => boundfree(i, x)
        case NApp(n,v) => App( neutralQuote(i, n), quote(i,v) )
      }


    def boundfree (i : Int, n : Name) : TermInfer =
      n match {
        case Quote(k) => Bound(i - k - 1)
        case x        => Free(x)
      }
  }

  type Result[A] = Try[A]
  type Type = Value
  type Context = Vector[(Name,Type)]

  object Typing {

    def lookup ( k : Name, c : Context) : Result[Type] =
      c match {
        case IndexedSeq() => throw ErrorException.create("undefined identifier")
        case a +: cs      => if (a._1 == k) Success(a._2) else lookup(k,cs)
      }

    def typeTerm ( c : Context, t : TermInfer ) : Result[Type] =
      typeTerm(0, c, t)

    def dummy ( s : String ) : Result[Type] = {
      println(s)
      Success(VStar())
    }

    def typeTerm ( i : Int, c : Context, t : TermInfer ) : Result[Type] =
      t match {
        case Ann(e, p)     => for {
          _ <- dummy("before")
          _ <- typeTerm(i, c, p, VStar())
          _ <- dummy("after")
          val t = Eval.eval(p, Vector())  
          tt <- typeTerm(i, c, e, t)
        } yield(t)

        case Star()        => Success(VStar())

        case Pi(p1, p2)    => for {
          _ <- typeTerm(i, c, p1, VStar())
          val t = Eval.eval(p1, Vector())
          _ <- typeTerm(i+1, (Local(i),t) +: c, subst(0,Free(Local(i)), p2), VStar())
        } yield(VStar())

        case Bound(i)     =>
          throw ErrorException.create("typeTerm should not have received bound")

        case Free(n)      =>
          lookup(n,c) match {
            case Success(ty) => Success(ty)
            case _          => throw ErrorException.create("undefined identifier")
          }

        case App(e1,e2) => for {
          s <- typeTerm(i, c, e1)
          r <- s match {
            case VPi(t1, t2) => for {
              tt <- typeTerm(i, c, e2, t1)
            } yield( t2( Eval.eval(e2,Vector()) ) )
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
                 else throw ErrorException.create("type mismatch")
          } yield(r)
        case (Lam(e),VPi(t1,t2)) =>
          typeTerm(
            i+1,
            (Local(i),t1) +: c,
            subst(0, Free(Local(i)), e),
            t2(vfree(Local(i))) )
        case (_,_) =>
          throw ErrorException.create("type mismatch")
      }

    def subst( i : Int, r : TermInfer, t : TermInfer ) : TermInfer =
      t match {
        case Ann(e,t)   => Ann(subst(i, r, e), subst(i, r, t))
        case Star()     => Star()
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

  trait Parser extends PositionedParserUtilities {
    import scala.collection.immutable.Seq
    import scala.language.postfixOps

    class Bindings( e: List[String] )
        extends PackratParser[(List[String], List[TermCheck])] {

      // parse one or more parens bindings
      class BindingsRec( e: List[String], ts: List[TermCheck] )
        extends PackratParser[(List[String], List[TermCheck])] {

        lazy val pp : PackratParser[(String,TermCheck)] = parens (
          variable ~ (":" : Parser[String]) ~ pTermCheck(e) ^^
            { case v ~ ":" ~ e => (v,e) })

        def apply(s: org.lambdapi.Parser.Input) = pp(s) match {
          case Success(a, rem) =>
            (new BindingsRec(a._1 :: e, a._2 :: ts))(rem) match {
              case Success(aa, remm) => Success(aa,remm)
              case _                 => Success((a._1 :: e, a._2 :: ts), rem)
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
        new BindingsRec(e, List())(s) match {
          case Success(a, rem) => Success(a,rem)
          case f: Failure => {
            alt(s)
          }
          case _ => throw new RuntimeException // remove warnings
      }
    }

    def bindings(e : List[String]) :
        PackratParser[(List[String], List[TermCheck])] = new Bindings(e)

    def pTermInfer ( e : List[String] ) : PackratParser[TermInfer] = 
     presZero(e)

    def presZero ( e : List[String] ) : PackratParser[TermInfer] =
      forall(e) | funarrow(e) | presOne(e)

    def forall ( e : List[String] ) : PackratParser[TermInfer] =
      Parser[TermInfer] { in =>
        ("forall" ~  new Bindings(e))(in) match {
          case Success("forall" ~ bs, rem) => ("." ~ pTermCheck(bs._1) ^^
              { case "." ~ t =>
                bs._2.tail.foldLeft(Pi(bs._2 head,t)) ((a,b) => Pi(bs._2 head, Inf(a)))
              } )(rem)
          case f : Failure => f
          case _ => throw new RuntimeException // remove warnings
        }
      }

    def funarrow ( e : List[String] ) : PackratParser[TermInfer] = {
      presOne(e) ~ "->" ~ pTermCheck("" :: e) ^^ {
        case ti ~ "->" ~ tc => Pi(Inf(ti), tc) }
    }

    def presOne ( e : List[String] ) : PackratParser[TermInfer] =
      annLambda(e) | presTwo(e)

    def annLambda ( e : List[String] ) : PackratParser[TermInfer] =
      (presTwo(e) ~ "::" ~ pTermCheck(e) ^^ {
        case ti ~ "::" ~ tc => Ann(Inf(ti), tc)
      }) | (parens(pLambda(e)) ~ "::" ~ pTermCheck(e) ^^ {
        case tc1 ~ "::" ~ tc2 => Ann(tc1,tc2)
      })

    def presTwo ( e : List[String] ) : PackratParser[TermInfer] =
      presThree(e) ~ rep(pTermCheck(e)) ^^ {
        case t ~ ts => ts.foldLeft(t) ((a,b) => a $$ b) } | presThree(e)

    def presThree ( e : List[String] ) : PackratParser[TermInfer] =
      parens( pTermInfer(e) ) | star | identifier(e)

    def identifier ( e : List[String] ) : PackratParser[TermInfer] =
      variable ^^ { v => e.indexOf(v) match {
        case -1 => Free(Global (v))
        case n  => Bound(n)
      } }

    def  pTermCheck ( e : List[String] ) : PackratParser[TermCheck] =
      pLambda(e) | pTermInfer(e) ^^ { t => Inf(t) } | parens( pLambda(e) )

    // maybe I'm being dumb but it would be nice if Monad syntax worked here!!
    def pLambda(e : List[String] ) : PackratParser[TermCheck] =
      Parser[TermCheck] { in =>
        ("\\" ~ rep1(variable))(in) match {
          case Success("\\" ~ xs, rem) => ("." ~ pTermCheck(xs.reverse ++ e) ^^
            { case "." ~ t => xs.foldRight(t)((a,b) => Lam(b)) } )(rem)
          case f : Failure => f
          case _ => throw new RuntimeException // remove warnings
        }
      }

    lazy val star = "*" ^^ { _ => Star() }

    lazy val variable : PackratParser[String] =
      idn

    lazy val idn : PackratParser[String] =
      not (keyword) ~> "[a-zA-Z][a-zA-Z0-9]*".r

    lazy val keyword : Parser[String] =
      "let" | "assume" | "forall"

    def parens[A]( p : PackratParser[A] ) : PackratParser[A] =
      "(" ~> p <~ ")"

  }

  object Parser extends Parser

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

    def show (i : Int, e : TermInfer) : (Int, Doc) =
      e match {
        case Ann(e,t) => {
          val tmp  = show(i, e)
          (tmp._1, tmp._2 <+> ":" <+> show(i, t)._2)
        }
        case Star() => (i, "*")
        case Pi(t1, t2) => {
          val (i1, d1) = show(i, t1)
          val (i2, d2) = show(i1+1,t2)
          (i2, ("forall" <+> parens(i1.toString <+> ":" <+> d1) <+> "." <+> parens( d2 ) ))
        }
        case Bound(ii) => (i, value("x" + ii.toString))
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
          (ii+1, "\\x" <> ii.toString <> "." <+> d)
        }
      }

    def pretty (v : Value) : String =
      super.pretty (show (v))

    def show( v : Value ) : Doc = show(0, Eval.quote(v))._2

  }

  val id = Lam ( Lam ( Inf( Bound( 0 ) )) )
  val const = Lam (Lam (Inf (Bound (1))))
  val tfree = (a : String)  => Free (Global(a))
  val free  = (x : String ) => Inf (Free (Global(x)))

  val term2 = Ann ( id, (Inf  (Pi  (Inf (Star()), (Inf (Pi  (Inf(Bound(0)),  (Inf (Bound (1))))))))))
  val term3 = term2 $$ free("A")
  val term4 = term3 $$ free("y")

 val env1 : Context = Vector(
   (Global("y"), vfree(Global("A"))),
   (Global("A"), VStar()) )

} // package object lambdapi


package object commands {
  import org.kiama.attribution.Attributable
  import org.kiama.util.ParserUtilities
  import org.lambdapi._

  /*
   *  Following in the sprit of the orignal work we support a 
   *  simple, Gofer inspired, interpreter
   */
  sealed abstract class Command extends Attributable
  case class CExpr( t : TermCheck )             extends Command
  case class CLet( n : Name, t : TermCheck )    extends Command
  case class CAssume( n : Name, t : TermCheck ) extends Command
  case class CType( t : TermCheck )             extends Command
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
       cexpr | internal

    lazy val cexpr = pTermCheck(List()) ^^
       { case t => CExpr(t) }

    lazy val internal = ":" ~> (help | browse)
    lazy val help   = ("help" | "h" | "?")  ^^ { _ => CHelp() }
    lazy val browse = ("browse" | "b") ^^ { _ => CBrowse() }
  }

} // package object commands

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
      case CHelp() => displayHelp()
      case CExpr(e) => println(e.toString)
      case _ => throw new RuntimeException // Should not happen
    }
  }
}
