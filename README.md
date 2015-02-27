LambdaPi
========

This repo provides a simple implementation of a dependently typed
lambda calculus. It is implemented in Scala and based on the Haskell
described implementation of dependent types in the paper:

    A Tutorial Implementation of a Dependently Typed Lambda Calculus
    Andres Löh, Conor McBride and Wouter Swierstra
    http://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
 
It really offers nothing more, currently at least, than the original
paper, rather I wanted to better understand how to implement a system
with dependent types, as I've been using them a lot recently (well one
in particular, Agda). There is nothing like implementing an idea to
help you better understand it!  And along the way I was forced to
develop a better understanding of Scala too.


Build
=====

Assuming you have SBT (http://www.scala-sbt.org/) installed, then it
is simply a matter of running sbt and typing compile. The necessary
packages will be downloaded as required.

Run
===

From within SBT simple type run and you will enter the REPL loop and look like this:

    Lambda Pi - fun with dependent types.
      Type :? for help and ^D to exit
    LP> 

The following commands are supported:

    <expr>                  evaluate expression 
                            ($$ refers to the last expr evaluated)
 
    let <var> = <expr>      define variable
    assume <var> :: <expr>  assume variable

    :type <expr>            print type of expression
    :browse                 browse names in scope
    :load <file>            load program from file
    :^D                     exit interpreter
    :help, :?               display this list of commands

Any command may be abbreviated to :c where c is the first character in
the full name.

Some simple examples are:

    LP> let id    = (\ a x . x) : forall (a : *) . a -> a 
    id : forall (x : *) . (forall (y : x) . (x))

    LP> assume (Boolean : *) (true : Boolean) (false : Boolean)

    LP> id Boolean true
    true : Boolean

Natural numbers are supported, but currently no general syntax for
defining inductive types:

    LP> 10
    10 : Nat

    LP> 20
    20 : Nat

    LP> let plus = (\x . natElim (\x . Nat -> Nat) (\n . n) (\k rec n . Succ(rec n)) x) : forall (x : Nat) (y : Nat) . Nat
    plus : forall (x : Nat) . (forall (y : Nat) . (Nat))

    LP> plus 10 $$
    30 : Nat

    LP> let mul = (\x y . natElim (\x . Nat -> Nat) (\n . n) (\k rec n . plus y (rec k)) x y) : forall (x : Nat) (y : Nat) . Nat
    mul : forall (x : Nat) . (forall (y : Nat) . (Nat))
    LP> mul 20 10
    200 : Nat

$$ is used to access the last command evaluated


