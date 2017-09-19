/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.inequalities;

import ap.terfor._
import ap.terfor.linearcombination.{LinearCombination,
                                    LinearCombination0,
                                    LinearCombination1}
import ap.terfor.arithconj.{ArithConj, ReduceWithAC}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.basetypes.IdealInt
import ap.terfor.substitutions.VariableShiftSubst
import ap.util.{Debug, Logic, Seqs, FilterIt, LRUCache}

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}

object ReduceWithInEqs {
  
  protected[inequalities] val AC = Debug.AC_PROPAGATION

  def apply(inEqs : InEqConj, order : TermOrder) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, inEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (inEqs.isTrue)
      new ReduceWithEmptyInEqs(order)
    else
      new ReduceWithInEqsImpl(inEqs.findLowerBound _,
                              !inEqs.variables.isEmpty,
                              order)
  }
  
}

/**
 * Reduce certain terms or formulas drawing information from inequalities that
 * are assumed as facts.
 */
abstract class ReduceWithInEqs {

  /**
   * Check whether the known inequalities imply a lower bound of the given term.
   */
  def lowerBound(t : Term) : Option[IdealInt]

  /**
   * Check whether the known inequalities imply an upper bound of the given
   * term.
   */
  def upperBound(t : Term) : Option[IdealInt]

  def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs
  
  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithInEqs
  
  def apply(conj : EquationConj) : EquationConj

  /**
   * Reduce a conjunction of negated equations by removing all equations from
   * which we know that they hold anyway. This will also turn
   * disequalities into inequalities if possible.
   */
  def apply(conj : NegEquationConj,
            logger : ComputationLogger) : (NegEquationConj, InEqConj)

  /**
   * Reduce a conjunction of negated equations by removing all equations from
   * which we know that they hold anyway. This will also turn
   * disequalities into inequalities if possible.
   */
  def apply(conj : NegEquationConj) : (NegEquationConj, InEqConj) =
    apply(conj, ComputationLogger.NonLogger)

  /**
   * Reduce a conjunction of inequalities. This means that subsumed inequalities
   * are removed, contradictions are detected, and possibly further equations
   * are inferred.
   */
  def apply(conj : InEqConj) : InEqConj

  /**
   * Reduce a conjunction of inequalities without implied equations.
   * (i.e., <code>conj.equalityInfs.isEmpty</code>)
   */
  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj
}

/**
 * The implementation for the trivial case that there are no inequalities
 * (this is realised as an own class for performance reasons)
 */
class ReduceWithEmptyInEqs protected[inequalities]
                           (order : TermOrder) extends ReduceWithInEqs {

  def lowerBound(t : Term) : Option[IdealInt] = t match {
    case t : LinearCombination0 =>
      Some(t.constant)
    case _ =>
      None
  }

  def upperBound(t : Term) : Option[IdealInt] = t match {
    case t : LinearCombination0 =>
      Some(t.constant)
    case _ =>
      None
  }

  def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, furtherInEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (furtherInEqs.isTrue)
      this
    else
      new ReduceWithInEqsImpl(furtherInEqs.findLowerBound _,
                              !furtherInEqs.variables.isEmpty,order)
  }
  
  def passQuantifiers(num : Int) : ReduceWithInEqs = this
  
  def apply(conj : EquationConj) : EquationConj = conj

  def apply(conj : NegEquationConj,
            logger : ComputationLogger) : (NegEquationConj, InEqConj) =
    (conj, InEqConj.TRUE)

  def apply(conj : InEqConj) : InEqConj = conj

  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj = conj
}

/**
 * The standard implementation
 */
class ReduceWithInEqsImpl protected[inequalities]
                          (ineqLowerBound :
                            (LinearCombination) => Option[IdealInt],
                           containsVariables : Boolean,
                           order : TermOrder)
      extends ReduceWithInEqs {

  override def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, furtherInEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (furtherInEqs.isTrue)
      this
    else
      new ReduceWithInEqsImpl((lc:LinearCombination) => (
                              // we compute the maximum of all known lower bounds
                              max(ineqLowerBound(lc),
                                  furtherInEqs findLowerBound lc)),
                              containsVariables ||
                                !furtherInEqs.variables.isEmpty,
                              order)
  }

  private def max(a : Option[IdealInt],
                  b : Option[IdealInt]) : Option[IdealInt] = (a, b) match {
    case (Some(c), Some(d)) => Some(c max d)
    case (x@Some(_), _) => x
    case (_, x@Some(_)) => x
    case _ => None
  }

  private def min(a : Option[IdealInt],
                  b : Option[IdealInt]) : Option[IdealInt] = (a, b) match {
    case (Some(c), Some(d)) => Some(c min d)
    case (x@Some(_), _) => x
    case (_, x@Some(_)) => x
    case _ => None
  }

  /**
   * Check whether the known inequalities imply a lower bound of the given term.
   */
  def lowerBound(t : Term) : Option[IdealInt] = t match {
    case OneTerm => {
      Some(IdealInt.ONE)
    }
    case _ : VariableTerm | _ : ConstantTerm => lowerBoundsCache(t) {
      ineqLowerBound(LinearCombination(t, order))
    }
    case t : LinearCombination0 => {
      Some(t.constant)
    }
    case t : LinearCombination1 =>
      if (t.coeff0.isOne && t.constant.isZero) {
        lowerBound(t.term0)
      } else {
        toOption(coeffBound(t.coeff0, t.term0, t.constant, false))
      }
    case t : LinearCombination => lowerBoundsCache(t) {
      max(linCompBound(t, false), ineqLowerBound(t))
    }
  }

  /**
   * Check whether the known inequalities imply an upper bound of the given
   * term.
   */
  def upperBound(t : Term) : Option[IdealInt] = t match {
    case OneTerm => {
      Some(IdealInt.ONE)
    }
    case _ : VariableTerm | _ : ConstantTerm => upperBoundsCache(t) {
      for (b <- ineqLowerBound(-LinearCombination(t, order))) yield -b
    }
    case t : LinearCombination0 => {
      Some(t.constant)
    }
    case t : LinearCombination1 =>
      if (t.coeff0.isOne && t.constant.isZero) {
        upperBound(t.term0)
      } else {
        toOption(coeffBound(t.coeff0, t.term0, t.constant, true))
      }
    case t : LinearCombination => upperBoundsCache(t) {
      min(linCompBound(t, true), for (b <- ineqLowerBound(-t)) yield -b)
    }
  }

  private def deriveBoundIneq(lc : LinearCombination,
                              upper : Boolean,
                              logger : ComputationLogger) : Unit = lc match {
    case _ : LinearCombination0 => // nothing
    case _ : LinearCombination1 => // nothing
    case lc =>
      if ((!upper && ineqLowerBound(lc) != lowerBound(lc)) ||
          (upper && (for (b <- ineqLowerBound(-lc)) yield -b) != upperBound(lc))) {
        val bounds = for ((coeff, t : ConstantTerm) <- lc.pairIterator) yield {
          if (coeff.signum > 0 != upper)
            (coeff.abs,
             LinearCombination(Array((IdealInt.ONE, t),
                                     (-lowerBound(t).get, OneTerm)),
                               order))
          else
            (coeff.abs,
             LinearCombination(Array((IdealInt.MINUS_ONE, t),
                                     (upperBound(t).get, OneTerm)),
                               order))
        }

        val (coeff1, lc1) = bounds.next
        val (coeff2, lc2) = bounds.next
        val initIneq =
          LinearCombination.sum(Array((coeff1, lc1), (coeff2, lc2)), order)
        logger.combineInequalities(coeff1, lc1, coeff2, lc2,
                                   initIneq, initIneq, order)

        (initIneq /: bounds) {
          case (s, (c, lc)) => {
            val newS = 
              LinearCombination.sum(Array((IdealInt.ONE, s), (c, lc)), order)
            logger.combineInequalities(IdealInt.ONE, s, c, lc,
                                       newS, newS, order)
            newS
          }
        }
      }
  }

  /**
   * Returns null if there is no lower bound.
   */
  private def coeffBound(coeff : IdealInt, term : Term,
                         offset : IdealInt, upper : Boolean) : IdealInt =
    (if ((coeff.signum > 0) != upper)
       lowerBound(term)
     else
       upperBound(term)) match {
      case Some(b) => b * coeff + offset
      case None => null
    }

  private def linCompBound(t : LinearCombination,
                           upper : Boolean) : Option[IdealInt] = {
    var bound = IdealInt.ZERO
    var i = 0
    while (i < t.lcSize && bound != null) {
      bound = coeffBound(t getCoeff i, t getTerm i, bound, upper)
      i = i + 1        
    }
    toOption(bound)
  }

  private def toOption(n : IdealInt) : Option[IdealInt] =
    if (n == null) None else Some(n)

  private val lowerBoundsCache, upperBoundsCache =
    new LRUCache[Term, Option[IdealInt]](5000)

  def passQuantifiers(num : Int) : ReduceWithInEqs =
    if (containsVariables && num > 0) {
      val downShifter =
        VariableShiftSubst.downShifter[LinearCombination](num, order)
      new ReduceWithInEqsImpl((lc:LinearCombination) =>
                                (if (downShifter isDefinedAt lc)
                                  ineqLowerBound(downShifter(lc))
                                else
                                  None),
                              true,
                              order)
    } else {
      this
    }

  
  def apply(conj : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // the only possible inference is that the conjunction of equations is
    // unsatisfiable
    val res =
      if (conj exists (isNonZero(_)))
        EquationConj.FALSE
      else
        conj

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Determine whether we can derive from the known inequalities that the value
   * of <code>lc</code> is not zero
   */
  private def isNonZero(lc : LinearCombination) : Boolean = nonZeroCache(lc) {
    isPositive(lowerBound(lc)) || isNegative(upperBound(lc))
  }

  private val nonZeroCache = new LRUCache[LinearCombination, Boolean] (5000)
    
  private def isPositive(opt : Option[IdealInt]) : Boolean = opt match {
    case Some(d) => d.signum > 0
    case _ => false
  }
  
  private def isNegative(opt : Option[IdealInt]) : Boolean = opt match {
    case Some(d) => d.signum < 0
    case _ => false
  }
  
  /**
   * Reduce a conjunction of disequalities; sometimes, this will turn
   * disequalities into inequalities.
   */
  def apply(conj : NegEquationConj,
            logger : ComputationLogger) : (NegEquationConj, InEqConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (conj.isTrue || conj.isFalse) {
        (conj, InEqConj.TRUE)
      } else {
        val newInEqs = new ArrayBuffer[LinearCombination]
        val negEqsToRemove = new MHashSet[LinearCombination]

        val remainingNegEqs = conj filter ((lc:LinearCombination) =>
          !(negEqsToRemove contains lc) &&
          (lowerBound(lc) match {
            case Some(b) if b.signum > 0 => {
              // disequality can be dropped
              false
            }
            case Some(b) if b.isZero => {
              // disequality can be turned into an inequality
              newInEqs += strengthenIneqWithNegEqs(conj, lc, false,
                                                   negEqsToRemove, logger)
              false
            }
            case _ => upperBound(lc) match {
              case Some(b) if b.signum < 0 => {
                // disequality can be dropped
                false
              }
              case Some(b) if b.isZero => {
                // disequality can be turned into an inequality
                newInEqs += strengthenIneqWithNegEqs(conj, lc, true,
                                                     negEqsToRemove, logger)
                false
              }
              case _ =>
                true
            }
          }))

        val inEqs =
          if (newInEqs.isEmpty)
            InEqConj.TRUE
          else
            InEqConj(newInEqs.iterator, logger, order)

        if (inEqs.isFalse) {
          (NegEquationConj.FALSE, InEqConj.TRUE)
        } else {
          val remainingNegEqs2 =
            if (negEqsToRemove.isEmpty)
              remainingNegEqs
            else
              remainingNegEqs filterNot negEqsToRemove

          (conj.updateEqsSubset(remainingNegEqs2)(order), inEqs)
        }
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC,
                     ((res._1 eq conj) && res._2.isTrue) || (res._1 != conj))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  private def strengthenIneqWithNegEqs(
                conj : NegEquationConj,
                negEq : LinearCombination,
                upper : Boolean,
                negEqsToRemove : MHashSet[LinearCombination],
                logger : ComputationLogger) : LinearCombination = {
    val boundIneq = if (upper) -negEq else negEq
    var newBoundIneq = boundIneq + IdealInt.MINUS_ONE

    if (logger.isLogging) {
      deriveBoundIneq(negEq, upper, logger)
      logger.directStrengthen(boundIneq, negEq, newBoundIneq, order)
    }

    var shiftedNegEq = if (upper) (negEq + IdealInt.ONE) else newBoundIneq

    while (conj contains shiftedNegEq) {
      negEqsToRemove += shiftedNegEq
      val newIneq = newBoundIneq + IdealInt.MINUS_ONE
      logger.directStrengthen(newBoundIneq, shiftedNegEq, newIneq, order)
      newBoundIneq = newIneq
      shiftedNegEq = if (upper) (shiftedNegEq + IdealInt.ONE) else newBoundIneq
    }

    newBoundIneq
  }

  def apply(conj : InEqConj) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (conj.equalityInfs.isEmpty) {
        reduceNoEqualityInfs(conj)
      } else {
        val reducer = ReduceWithAC(this, order)
        val ac = ArithConj(EquationConj.TRUE,
                           NegEquationConj.TRUE,
                           conj,
                           order)
        val acRes = reducer(ac)

        if (acRes eq ac) {
          conj
        } else {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(ReduceWithInEqs.AC,
                          acRes.negativeEqs.isEmpty &&
                          acRes.inEqs.equalityInfs.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          val res =
            InEqConj(acRes.inEqs.iterator ++
                     (for (lc <- acRes.positiveEqs.iterator;
                           a <- Seqs.doubleIterator(lc, -lc))
                      yield a), order)

          if (res == conj)
            conj
          else
            res
        }
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC,
                    (conj isSortedBy order) && conj.equalityInfs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      if (conj.isTrue || conj.isFalse) {
        conj
      } else try {
        val newLCs = new ArrayBuffer[LinearCombination]
        var changed = false

        val lcIt = conj.iterator
        while (lcIt.hasNext) {
          val lc = lcIt.next

          upperBound(lc) match {
            case Some(d) if (d.signum < 0) =>
              // contradiction
              throw CONTRADICTION_EXCEPTION
            case x => // we also need to check lower bounds
                      (lowerBound(lc), x) match {
                        case (Some(d), _) if (d.signum >= 0) => {
                          // the inequality is subsumed by a known inequality,
                          // can be removed
                          changed = true
                        }
                        case (_, Some(IdealInt.ZERO)) => {
                          // we can infer an equation from an inequality
                          // by inserting an upper bound as well
                          newLCs += lc
                          newLCs += -lc
                          changed = true
                        }
                        case _ => {
                          // we have to keep the inequality
                          newLCs += lc
                        }
                      }
          }
        }

        if (changed)
          InEqConj(newLCs, order)
        else
          conj
      } catch {
        case CONTRADICTION_EXCEPTION => InEqConj.FALSE
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
}

private object CONTRADICTION_EXCEPTION extends Exception
