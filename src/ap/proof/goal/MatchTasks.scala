/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.goal

import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.Vocabulary
import ap.terfor.conjunctions.Conjunction
import ap.parameters.Param
import ap.util.Debug

private object MatchFunctions {
  
  def isIrrelevantInstance(instance : Conjunction,
                           voc : Vocabulary,
                           reversePropagation : Boolean) =
    reversePropagation && 
    (!(AddFactsTask isCoveredFormula instance) &&
     voc.constantFreedom.isShielded(instance, voc.bindingContext))
  
  def updateMatcher(goal : Goal,
                    ptf : ProofTreeFactory,
                    eager : Boolean) : ProofTree = {
    val order = goal.order
    val collector = goal.getInferenceCollector
    val oldMatcher = goal.compoundFormulas quantifierClauses eager

    val reducerObj : Conjunction => Conjunction = goal.reduceWithFacts.apply _

    // first check whether any of the clauses has to be updated
    val (removedClauses, reducedMatcher) =
      if (collector.isLogging) {
        // if we are producing proofs, we mostly check for subsumed clauses
        // that can be removed

        def clauseReducer(c : Conjunction) =
          if (reducerObj(c).isFalse) Conjunction.FALSE else c
      
        oldMatcher.reduceClauses(clauseReducer _, reducerObj, order)
      } else {
        oldMatcher.reduceClauses(reducerObj, reducerObj, order)
      }

    if (removedClauses.isEmpty) {
      val voc = goal.vocabulary
  
      val reverseProp = Param.REVERSE_FUNCTIONALITY_PROPAGATION(goal.settings)
      val (instances, newMatcher) =
        reducedMatcher.updateFacts(goal.facts.predConj,
                                   goal.mayAlias,
                                   goal.reduceWithFacts,
                                   (isIrrelevantInstance(_, voc, reverseProp)),
                                   reverseProp,
                                   collector, order)

      val newCF = goal.compoundFormulas.updateQuantifierClauses(eager, newMatcher)
      val newTasks =
        if (collector.isLogging)
          // if we are producing proofs, we have to treat the instances
          // separately (to log all performed simplifications)
          for (f <- instances; t <- goal.formulaTasks(f)) yield t
        else
          for (t <- goal.formulaTasks(Conjunction.disj(instances, order))) yield t

      ptf.updateGoal(newCF, newTasks, collector.getCollection, goal)
    } else {
      val newTasks =
        (for (c <- removedClauses; t <- goal formulaTasks c) yield t) ++
        (if (eager)
           List()
         else
           List(new LazyMatchTask (goal.age, Param.MATCHING_BASE_PRIORITY(goal.settings))))
      val newCF = goal.compoundFormulas.updateQuantifierClauses(eager, reducedMatcher)
      ptf.updateGoal(newCF, newTasks, collector.getCollection, goal)
    }
  }
  
}

////////////////////////////////////////////////////////////////////////////////

case object EagerMatchTask extends EagerTask {
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    MatchFunctions.updateMatcher(goal, ptf, true)
}

////////////////////////////////////////////////////////////////////////////////

object LazyMatchTask {
  
  private val AC = Debug.AC_CLAUSE_MATCHER
  
  def addTask(goal : Goal) : Seq[PrioritisedTask] =
    if (goal.tasks.taskInfos.containsLazyMatchTask)
      List()
    else
      List(new LazyMatchTask (goal.age,
                              Param.MATCHING_BASE_PRIORITY(goal.settings)))
}

class LazyMatchTask(age : Int, basePriority : Int)
      extends PrioritisedTask {
  
  val priority : Int = - basePriority + age

  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                : Seq[PrioritisedTask] = List(this)

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LazyMatchTask.AC,
                    !(goal.compoundFormulas.eagerQuantifiedClauses factsAreOutdated
                                                           goal.facts.predConj))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    MatchFunctions.updateMatcher(goal, ptf, false)
  }
  
  override def toString = "LazyMatchTask(" + priority + ")"
}
