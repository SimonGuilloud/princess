/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010-2020 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.parser

import ap.Signature
import ap.basetypes.IdealInt
import ap.theories.{TheoryRegistry, BitShiftMultiplication, ADT,
                    ModuloArithmetic, MulTheory}
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import IExpression.Sort
import Sort.:::
import ap.util.Seqs

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the Princess format
 */
object PrincessLineariser {

  def apply(formula : IFormula, signature : Signature) = {
    val order = signature.order

    println("// Generated by Princess (http://www.philipp.ruemmer.org/princess.shtml) }")

    // declare the various kinds of constants
    for ((name, consts) <- List(("universalConstants", signature.universalConstants),
    		                    ("existentialConstants", signature.existentialConstants),
                                ("functions", signature.nullaryFunctions)))
      if (!consts.isEmpty) {
        println("\\" + name + " {")
        for (c <- consts)
          println("int " + c.name + ";")
        println("}")
      }
    
    // declare the required predicates
    if (!order.orderedPredicates.isEmpty) {
      println("\\predicates {")
      for (pred <- order.orderedPredicates) {
        print(pred.name)
        if (pred.arity > 0) {
          print("(")
          print((for (_ <- List.range(0, pred.arity)) yield "int") mkString ", ")
          print(")")
        }
        println(";")
      }
      println("}")
    }
    
    println("\\problem {")
    printExpression(formula)
    println
    println("}")
  }
  
  def printExpression(e : IExpression) = {
    val enriched = EnrichingVisitor.visit(e, ())
    AbsyPrinter.visit(enriched, PrintContext(List(), "", 0))
  }

  def asString(e : IExpression) : String =
    ap.DialogUtil.asString { printExpression(e) }

  private def fun2Identifier(fun : IFunction) = fun.name

  //////////////////////////////////////////////////////////////////////////////

  private val NonEqPredicate   = new Predicate ("!=", 2)
  private val GeqPredicate     = new Predicate (">=", 2)
  private val LtPredicate      = new Predicate ("<", 2)
  private val MinusFunction    = new IFunction ("-", 2, false, false)
  
  private object EnrichingVisitor extends CollectingVisitor[Unit, IExpression] {

    override def preVisit(t : IExpression,
                          oldCtxt : Unit) : PreVisitResult = t match {
      case IExpression.Difference(NonNegTerm(s), NonNegTerm(t)) =>
        TryAgain(IFunApp(MinusFunction, List(s, t)), ())

      case INot(IExpression.Eq(s, t)) =>
        TryAgain(IAtom(NonEqPredicate, List(s, t)), ())
      case IExpression.Geq(s, t) =>
        TryAgain(IAtom(GeqPredicate, List(s, t)), ())
      case INot(IExpression.Geq(s, t)) =>
        TryAgain(IAtom(LtPredicate, List(s, t)), ())

      case _ : IEquation =>
        KeepArg
      case IExpression.Eq(s, t) =>
        TryAgain(IEquation(s, t), ())

      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression,
                  ctxt : Unit, subres : Seq[IExpression]) : IExpression =
      t update subres
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private case class PrintContext(vars : List[String],
                                  parentOp : String,
                                  outerPrec : Int) {
    def pushVar(name : String)          = PrintContext(name :: vars, parentOp, outerPrec)
    def setParentOp(op : String)        = PrintContext(vars, op, outerPrec)
    def addParentOp(op : String)        = PrintContext(vars, op + parentOp, outerPrec)
    def setOpPrec(op : String, l : Int) = PrintContext(vars, op, l)
    def addOpPrec(op : String, l : Int) = PrintContext(vars, op + parentOp, l)
    def setPrecLevel(l : Int)           = PrintContext(vars, parentOp, l)
  }
  
  private object AtomicTerm {
    def unapply(t : IExpression) : Option[ITerm] = t match {
      case t : IConstant => Some(t)
      case t : IVariable => Some(t)
      case t@IFunApp(_, Seq()) => Some(t)
      case _ => None
    }
  }
    
  private def atomicTerm(t : ITerm,
                         ctxt : PrintContext,
                         cast2Int : Boolean = false) : String = t match {
    case IConstant(c) ::: SortNeedingIntCast(_) if cast2Int =>
      c.name + ".\\as[int]"
    case IConstant(c) =>
      c.name
    case IVariable(index) => {
      var vs = ctxt.vars
      var ind = index

      while (ind > 0 && !vs.isEmpty) {
        vs = vs.tail
        ind = ind - 1
      }

      if (vs.isEmpty)
        "_" + ind
      else
        vs.head
    }
    case IFunApp(f, Seq()) ::: SortNeedingIntCast(_) if cast2Int =>
      f.name + ".\\as[int]"
    case IFunApp(f, Seq()) =>
      f.name
  }

  private object SortNeedingIntCast {
    def unapply(sort : Sort) : Option[Sort] = sort match {
      case Sort.Numeric(_) => None
      case _               => Some(sort)
    }
  }

  private object NonNegTerm {
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case ITimes(coeff, s) if coeff.signum < 0 => None
      case IIntLit(value)   if value.signum < 0 => None
      case _                                    => Some(t)
    }
  }

  private def needsIntCast(t : ITerm) : Boolean = t match {
    case (_ : IConstant) ::: SortNeedingIntCast(_)       => true
    case IFunApp(MulTheory.Mul(), _)                     => false
    case (_ : IFunApp) ::: SortNeedingIntCast(_)         => true
    case _                                               => false
  }

  private def maybeInsertIntCast(t : ITerm,
                                 ctxt : PrintContext) : PrintContext =
    if (needsIntCast(t))
      insertIntCast(ctxt)
    else
      ctxt

  private def insertIntCast(ctxt : PrintContext) : PrintContext =
    ctxt.addOpPrec(".\\as[int]", 10)

  private def relation(rel : IIntRelation.Value) = rel match {
    case IIntRelation.EqZero => "="
    case IIntRelation.GeqZero => ">="
  }

  private def precLevel(e : IExpression) : Int = e match {
    case IBinFormula(IBinJunctor.Eqv, _, _)             => 0
    case IBinFormula(IBinJunctor.Or, _, _)              => 0
    case IBinFormula(IBinJunctor.And, _, _)             => 0
    case _ : ITermITE | _ : IFormulaITE                 => 1
    case _ : INot | _ : IQuantified | _ : INamedPart |
         _ : ITrigger | _ : IEpsilon                    => 3
    case _ : IIntFormula | _ : IEquation |
         IAtom(NonEqPredicate | GeqPredicate |
               LtPredicate, _)                          => 4
    case IFunApp(MinusFunction, _)                      => 5
    case _ : IPlus                                      => 5
    case _ : ITimes | IFunApp(MulTheory.Mul(), _)       => 7
    case IIntLit(v) if (v.signum < 0)                   => 8
    case _ : ITerm | _ : IBoolLit | _ : IAtom           => 10
  }

  //////////////////////////////////////////////////////////////////////////////

  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    
    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
                List(ctxt setParentOp lastOp))
    }
    
    private def noParentOp(ctxt : PrintContext) = UniSubArgs(ctxt setParentOp "")
    
    private def shortCut(ctxt : PrintContext) = {
      print(ctxt.parentOp)
      ShortCutResult(())
    }

    private def tryAgainWithCast(s : ITerm, ctxt : PrintContext) =
      TryAgain(s, maybeInsertIntCast(s, ctxt))

    override def preVisit(t : IExpression,
                          oldCtxt : PrintContext) : PreVisitResult = {
      // first use the precedence level of operators to determine whether we
      // have to insert parentheses

      val newPrecLevel = precLevel(t)

      val ctxt =
        if (newPrecLevel > oldCtxt.outerPrec) {
          oldCtxt setPrecLevel newPrecLevel
        } else if (newPrecLevel < oldCtxt.outerPrec) {
          // then we need parentheses
          print("(")
          return TryAgain(t, oldCtxt.setOpPrec(")" + oldCtxt.parentOp, newPrecLevel))
        } else {
          oldCtxt
        }
                            
      t match {
        // Terms

/*
        case IPlus(IIntLit(value), s) => {
          val offset =
            if (value.signum >= 0)
              " + " + value
            else
              " - " + (-value)
          tryAgainWithCast(s, ctxt addParentOp offset)
        }
        
        case IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t))) => {
          tryAgainWithCast(s, ctxt addParentOp (" - " + atomicTerm(t, ctxt, true)))
        }
        case IPlus(s, ITimes(coeff, AtomicTerm(t))) if (coeff.signum < 0) => {
          tryAgainWithCast(s, ctxt addParentOp (" - " + coeff.abs + "*" + atomicTerm(t, ctxt, true)))
        }
        case IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s) => {
          tryAgainWithCast(s, ctxt addParentOp (" - " + atomicTerm(t, ctxt, true)))
        }
        case IPlus(ITimes(coeff, AtomicTerm(t)), s) if (coeff.signum < 0) => {
          tryAgainWithCast(s, ctxt addParentOp (" - " + coeff.abs + "*" + atomicTerm(t, ctxt, true)))
        }
 */
    
        case AtomicTerm(t) => {
          print(atomicTerm(t, ctxt))
          noParentOp(ctxt)
        }
        case IIntLit(value) => {
          print(value)
          noParentOp(ctxt)
        }

        case IPlus(t1, t2) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " + "),
                       maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MulTheory.Mul(), Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " * "),
                       maybeInsertIntCast(t2, ctxt setParentOp "")))
        }
        case IFunApp(MinusFunction, Seq(t1, t2)) => {
          SubArgs(List(maybeInsertIntCast(t1, ctxt setParentOp " - "),
                       maybeInsertIntCast(t2, ctxt setParentOp "" setPrecLevel 6)))
        }

        case ITimes(coeff, s) => {
          print(coeff + "*")
          // noParentOp(ctxt)
          UniSubArgs(maybeInsertIntCast(s, ctxt setParentOp ""))
        }
      
        case IFunApp(ADT.TermSize(adt, num), Seq(t ::: tSort))
               if (adt sorts num) == tSort => {
          print("\\size(")
          allButLast(ctxt setPrecLevel 0, ", ", ")", 1)
        }

        case IFunApp(ModuloArithmetic.mod_cast,
                     Seq(IIntLit(lower), IIntLit(upper), t)) =>
          TryAgain(t, ctxt.addOpPrec(".\\as[" +
                                     ModuloArithmetic.ModSort(lower, upper) +
                                     "]", 10))

        case IFunApp(ModuloArithmetic.int_cast, Seq(t)) =>
          TryAgain(t, insertIntCast(ctxt))

        case IFunApp(ModuloArithmetic.bv_extract,
                     Seq(IIntLit(upper), IIntLit(lower), t)) =>
          TryAgain(t, ctxt.addOpPrec("[" + upper + ":" + lower + "]", 10))

        case IFunApp(fun, _) => {
          print(fun2Identifier(fun))
          if (fun.arity > 0) {
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", fun.arity)
          } else {
            KeepArg
          }
        }
        
        case _ : ITermITE | _ : IFormulaITE => {
          print("\\if (")
          SubArgs(List(ctxt setParentOp ") \\ then (",
                       ctxt setParentOp ") \\ else (",
                       ctxt setParentOp ")"))
        }

        // General formulae

        case IBinFormula(IBinJunctor.Or, INot(left : IAtom), right) => {
          left match {
            case IAtom(pred, Seq()) =>
              print(pred.name)
            case left =>
              // In this special case, recursively print the antecedent
              AbsyPrinter.visit(left, ctxt.setOpPrec("", 1))
          }

          print(" -> ")

          val newRightCtxt = right match {
            case IBinFormula(IBinJunctor.Or, INot(_), _) =>
              ctxt
            case _ =>
              ctxt setPrecLevel 1
          }

          TryAgain(right, newRightCtxt)
        }
        
        case IBinFormula(junctor, left, right) => {
          val op = junctor match {
            case IBinJunctor.And => " & "
            case IBinJunctor.Or => " | "
            case IBinJunctor.Eqv => " <-> "
          }
          
          val newLeftCtxt = left match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec(op, 1)
            case _ =>
              ctxt setParentOp op
          }
          val newRightCtxt = right match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec("", 1)
            case _ =>
              ctxt setParentOp ""
          }
          
          SubArgs(List(newLeftCtxt, newRightCtxt))
        }
        
        case IBoolLit(value) => {
          print(value)
          noParentOp(ctxt)
        }

        // ADT expressions

        case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
                               num) => {
          print("is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
                "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case INot(IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
                                    num)) => {
          print("!is_" + adt.getCtorPerSort(sortNum, num.intValueSafe).name +
                "(")
          TryAgain(arg, ctxt addParentOp (")"))
        }

        case IExpression.Eq(t, ADT.BoolADT.True) =>
          TryAgain(t, ctxt)

        case IExpression.Eq(t, ADT.BoolADT.False) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case INot(IExpression.Eq(t, ADT.BoolADT.True)) => {
          print("!")
          TryAgain(t, ctxt)
        }

        case INot(IExpression.Eq(t, ADT.BoolADT.False)) =>
          TryAgain(t, ctxt)

        // Some special rule for negated equations
        
/*
        case INot(IEquation(s, t)) =>
          TryAgain(IAtom(NonEqPredicate, List(s, t)), ctxt)

        case INot(IIntFormula(IIntRelation.EqZero,
                              ITimes(IdealInt.MINUS_ONE, t))) => {
          TryAgain(IAtom(NonEqPredicate, List(IIntLit(0), t)), ctxt)
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(s, ITimes(IdealInt.MINUS_ONE, t)))) => {
          TryAgain(IAtom(NonEqPredicate, List(s, t)), ctxt)
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(s, ITimes(coeff, t)))) if (coeff.signum < 0) => {
          TryAgain(IAtom(NonEqPredicate, List(s, ITimes(-coeff, t))), ctxt)
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(ITimes(IdealInt.MINUS_ONE, t), s))) => {
          TryAgain(IAtom(NonEqPredicate, List(t, s)), ctxt)
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(ITimes(coeff, t), s))) if (coeff.signum < 0) => {
          TryAgain(IAtom(NonEqPredicate, List(ITimes(-coeff, t), s)), ctxt)
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(IIntLit(value), s))) => {
          TryAgain(s, ctxt addParentOp (" != " + (-value)))
        }
        case INot(IIntFormula(IIntRelation.EqZero,
                              IPlus(s, IIntLit(value)))) => {
          TryAgain(s, ctxt addParentOp (" != " + (-value)))
        }
      
        case INot(IIntFormula(IIntRelation.EqZero, s)) => {
          TryAgain(s, ctxt addParentOp " != 0")
        }
 */
        // Positive equations
      

/*
        case IIntFormula(IIntRelation.EqZero,
                         ITimes(IdealInt.MINUS_ONE, t)) => {
          TryAgain(IEquation(IIntLit(0), t), ctxt)
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(s, ITimes(IdealInt.MINUS_ONE, t))) => {
          TryAgain(IEquation(s, t), ctxt)
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(s, ITimes(coeff, t))) if (coeff.signum < 0) => {
          TryAgain(IEquation(s, ITimes(-coeff, t)), ctxt)
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(ITimes(IdealInt.MINUS_ONE, t), s)) => {
          TryAgain(IEquation(t, s), ctxt)
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(ITimes(coeff, t), s)) if (coeff.signum < 0) => {
          TryAgain(IEquation(ITimes(-coeff, t), s), ctxt)
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(IIntLit(value), s)) => {
          TryAgain(s, ctxt addParentOp (" = " + (-value)))
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(s, IIntLit(value))) => {
          TryAgain(s, ctxt addParentOp (" = " + (-value)))
        }
 */

        // Equation predicates

        case IAtom(NonEqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " != ", "", 2)
        case IAtom(GeqPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " >= ", "", 2)
        case IAtom(LtPredicate, _) =>
          allButLast(ctxt setPrecLevel 1, " < ", "", 2)

        case IEquation(s, t) =>
          allButLast(ctxt setPrecLevel 1, " = ", "", 2)

        // Atoms

        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }

        // Non-negated relations

/*
        case IIntFormula(rel, ITimes(IdealInt.MINUS_ONE, t)) => {
          print("0 " + relation(rel) + " ")
          TryAgain(t, ctxt)
        }
        case IIntFormula(rel, IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " + atomicTerm(t, ctxt)))
        }
        case IIntFormula(rel, IPlus(s, ITimes(coeff, AtomicTerm(t)))) if (coeff.signum < 0) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " +
                                        coeff.abs + "*" + atomicTerm(t, ctxt, true)))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " + atomicTerm(t, ctxt)))
        }
        case IIntFormula(rel, IPlus(ITimes(coeff, AtomicTerm(t)), s)) if (coeff.signum < 0) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " +
                                        coeff.abs + "*" + atomicTerm(t, ctxt, true)))
        }
        case IIntFormula(rel, IPlus(IIntLit(value), s)) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " + (-value)))
        }
        case IIntFormula(rel, IPlus(s, IIntLit(value))) => {
          TryAgain(s, ctxt addParentOp (" " + relation(rel) + " " + (-value)))
        }
 */

        case IIntFormula(rel, _) => {
          UniSubArgs(ctxt setParentOp (" " + relation(rel) + " 0"))
        }
      
        case INot(subF) => {
          print("!")
          noParentOp(
            subF match {
              case _ : IIntFormula =>
                ctxt setPrecLevel 10
              case _ =>
                ctxt
            })
        }

        case ISortedQuantified(quan, sort, subF) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => "\\forall"
            case Quantifier.EX => "\\exists"
          })
          print(" " + sort + " " + varName)

          var newCtxt = ctxt pushVar varName

          var sub = subF
          while (sub.isInstanceOf[IQuantified] &&
                 sub.asInstanceOf[IQuantified].quan == quan &&
                 sub.asInstanceOf[IQuantified].sort == sort) {
            val varName2 = "v" + newCtxt.vars.size
            newCtxt = newCtxt pushVar varName2
            print(", " + varName2)
            val IQuantified(_, newSub) = sub
            sub = newSub
          }

          print("; ")
          TryAgain(sub, newCtxt)
        }

        case ISortedEpsilon(sort, _) => {
          val varName = "v" + ctxt.vars.size
          print("\\eps " + sort + " " + varName + "; ")
          noParentOp(ctxt pushVar varName)
        }
        case INamedPart(name, _) => {
          if (name != PartName.NO_NAME)
            print("\\part[" + name + "] ")
          noParentOp(ctxt)
        }
        case ITrigger(trigs, _) => {
          print("{")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
                     yield (ctxt setParentOp ", ")) ++
                  List(ctxt setParentOp "} ", ctxt setParentOp ""))
        }
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)
  
  }
  
}
