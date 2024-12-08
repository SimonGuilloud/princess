package ap.proof.certificates


import ap.util.Debug
import ap.{Prover, AbstractFileProver}
import ap.parser.{TPTPLineariser, IExpression}
import ap.terfor.preds.Predicate
import ap.parser.{PartName, TPTPLineariser, SMTLineariser, PrincessLineariser,
                  Internal2InputAbsy, IFunction, Transform2NNF,
                  VariableSortInferenceVisitor, TPTPTParser}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TermOrder

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}
import scala.util.Sorting

object SCTPTP {

}


object SCTPTPWriter {
  
  def apply(cert : Certificate, prover: AbstractFileProver, filename: String) = {

    println("filename: " + filename)

    if (filename endsWith ".p") {
      val reader = new java.io.BufferedReader (new java.io.FileReader(new java.io.File (filename)))
      // print content of file
      var line = reader.readLine()  
      while (line != null) {
        println(line)
        line = reader.readLine()
      }
      
    }

    // input
    {
      import IExpression._
      //println("TPTPLineariser(prover.rawInputFormula, filename)\n")
      //TPTPLineariser(prover.rawInputFormula, filename)
      //println("\n\n\n\n\n\n")
    }


    prover.getInputFormulaParts
    
    val rawFormulaParts = prover.getFormulaParts
    val predTranslation = prover.getPredTranslation

    val formulaParts = rawFormulaParts mapValues {
      f => CertFormula(f.negate)
    }
    val dagCert = DagCertificateConverter(cert)

    val printer = new SCTPTPPrettyPrinter(predTranslation)

    println()
    println("------------------")
    println()
    println("printer(dagCert, formulaParts)\n")
    printer(dagCert, prover)

    //proof


    cert.assumedFormulas.foreach { f =>
      println("-__--__")
      println(f)
    }
  }


  def certificateToTPTP(cert : Certificate) : String = {
    ???
  }




  def header {
    println("%------------------------------------------------------------------------------")
    println("% File     : ")
    println("% Domain   : <The domain of the problem, from the TPTP domains>")
    println("% Problem  : <A one line description of the problem>")
    println("% Version  : <If this is a different form of an existing problem, why it is ")
    println("%             different>")
    println("% English  : <A full description of the problem>")
    println("")
    println("% Refs     : <Relevant references>")
    println("% Source   : <The Ref where the formulae originate from>")
    println("% Names    : <The name(s) of this problem in the literature>")
    println("")
    println("% Status   : <A value from the SZS ontology>")
    println("% Rating   : <Don't worry about this one - we'll do it automatically>")
    println("% Syntax   : <Don't worry about this one - we'll do it automatically>")
    println("% SPC      : <Don't worry about this one - we'll do it automatically>")
    println("")
    println("% Comments : <Anything else that might be useful>")
    println("%            Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("%------------------------------------------------------------------------------")
  }

  class SCTPTPPrettyPrinter(predTranslation : Map[Predicate, IFunction]) {

    

    import CertificatePrettyPrinter._
    import PartName.{predefNames, predefNamesSet}

    val formulaPrinter = new CertificatePrettyPrinter.TPTPFormulaPrinter (
          predTranslation
        )

    def apply(dagCertificate : Seq[Certificate], prover: AbstractFileProver) : Unit = {
      val givenFormulas = prover.getInputFormulaParts.mapValues {
        f => f //CertFormula(f) // f.negate
      }


      val initialFormulas = prover.getFormulaParts.mapValues {
        f => CertFormula(f.negate)
      }

      val 
      
      certificateNum = dagCertificate.size
      val assumedFormulas = dagCertificate.last.assumedFormulas

      val partNamesSet = initialFormulas.keySet
      val partNames =
        (partNamesSet filterNot predefNamesSet).toIndexedSeq.sortBy(_.toString) ++
        (predefNames filter partNamesSet).toIndexedSeq

      val (usedNames, unusedNames) = partNames partition {
        name => assumedFormulas contains initialFormulas(name)
      }

      println("Assumptions after simplification:")
      println("---------------------------------")

      push
      try {
        for (name <- usedNames) {
          println()
          val label = name match {
            case PartName.NO_NAME         => "input"
            case PartName.FUNCTION_AXIOMS => "function-axioms"
            case PartName.THEORY_AXIOMS   => "theory-axioms"
            case _                        => formulaPrinter.partName2String(name)
          }
          introduceFormula(initialFormulas(name), label)
        }

        if (!(unusedNames forall PartName.predefNamesSet)) {
          println()
          println("Further assumptions not needed in the proof:")
          println("--------------------------------------------")
          printlnPrefBreaking("",
                              (unusedNames filterNot PartName.predefNamesSet)
                                .map(formulaPrinter.partName2String _)
                                .mkString(", "))
        }

        println()
        println("Those formulas are unsatisfiable:")
        println("---------------------------------")

        println()
        println("Begin of proof")
        addPrefix("| ")
        printCertificate(dagCertificate.last)
        printlnPref
      } finally {
        reset
      }
      println("End of proof")

      for (id <- (certificateNum - 2) to 0 by -1) {
        val cert = dagCertificate(id)

        println()
        println("Sub-proof #" + (certificateNum - id - 1) +
                " shows that the following formulas are inconsistent:")
        println("----------------------------------------------------------------")

        push
        try {
          for (f <- cert.assumedFormulas)
            introduceFormula(f)

          println()
          println("Begin of proof")
          addPrefix("| ")
          printCertificate(cert)
          printlnPref
        } finally {
          reset
        }
        println("End of proof")
      }
    }

    private var certificateNum = 0

    //////////////////////////////////////////////////////////////////////////////

    private var prefix = ""

    private def addPrefix(s : String) : Unit =
      prefix = prefix + s

    private def printlnPref : Unit =
      println(prefix)

    private def printPref : Unit =
      print(prefix)

    private def printlnPref(o : Any) : Unit = {
      print(prefix)
      println(o)
    }

    private def printPref(o : Any) : Unit = {
      print(prefix)
      print(o)
    }

    private def printlnPrefBreaking(label : String, o : Any) : Unit = {
      val remLineWidth = (LINE_WIDTH - prefix.size - label.size) max 50
      val text = "" + o

      printPref(label)

      if (text.size <= remLineWidth) {
        println(text)
      } else {
        var cnt = 0
        var parenNum = 0

        var curSplitPos = 0
        var curSplitParenNum = 0
        var lastSplitPos = 0
        var lastSplitParenNum = 0

        while (cnt < text.size) {
          text(cnt) match {
            case '(' | '{' | '[' => parenNum = parenNum + 1
            case ')' | '}' | ']' => parenNum = parenNum - 1
            case ' ' => {
              // this is where we might split
              curSplitPos = cnt
              curSplitParenNum = parenNum
            }
            case _ => // nothing
          }

          if (cnt - lastSplitPos > remLineWidth - 2*lastSplitParenNum - 1 &&
              curSplitPos > lastSplitPos) {
            println(text.substring(lastSplitPos, curSplitPos))

            lastSplitPos = curSplitPos + 1
            lastSplitParenNum = curSplitParenNum

            if (lastSplitPos < text.size)
              printPref(" " * label.size + "  " * curSplitParenNum)
          }

          cnt = cnt + 1
        }

        if (lastSplitPos < cnt)
          println(text.substring(lastSplitPos, cnt))
      }
    }

    //////////////////////////////////////////////////////////////////////////////

    private val formulaLabel = new LinkedHashMap[CertFormula, String]
    private var formulaCounter : Int = 1

    private def introduceFormula(f : CertFormula, label : String = "") : Unit =
      if (label == "") {
        printlnPrefBreaking("  (" + formulaCounter + ")  ",
                            formulaPrinter for2String f)
        formulaLabel.put(f, "" + formulaCounter)
        formulaCounter = formulaCounter + 1
      } else {
        printlnPref("  (" + label + ")")
        printlnPrefBreaking("  ", formulaPrinter for2String f)
        formulaLabel.put(f, label)
        printPref
      }


    private def introduceFormulaIfNeeded
                  (f : CertFormula, assumedFormulas : Set[CertFormula]) : Unit = {
      if (!(formulaLabel contains f) && (assumedFormulas contains f))
        introduceFormula(f)
    }

    private def introduceFormulasIfNeeded
                  (fs : Iterable[CertFormula],
                   assumedFormulas : Set[CertFormula],
                   order : TermOrder) : Unit = {
      var neededFors = 
        (for (f <- fs.iterator;
              if (!(formulaLabel contains f) && (assumedFormulas contains f)))
         yield f).toArray

      // if possible (and necessary), sort the list of formulas
      if (neededFors.size > 1 &&
          (neededFors forall (order isSortingOf _))) {
        implicit val o = CertFormula certFormulaOrdering order
        Sorting stableSort neededFors
      }

      for (f <- neededFors) introduceFormula(f)
    }

    private def l(f : CertFormula) : String = "(" + formulaLabel(f) + ")"

    private def l(fs : Iterable[CertFormula]) : String =
      ((fs.toSeq map (l(_))).sortBy {
        case NUMERIC_LABEL(num) => "(" + ("0" * (9 - num.size)) + num + ")"
        case label => label
      }) mkString ", "

    //////////////////////////////////////////////////////////////////////////////

    private val branchStack = new ArrayStack[(Int, String)]

    private def push : Unit =
      branchStack push ((formulaLabel.size, prefix))

    private def pop : Unit = {
      val (oldFormulaLabelSize, oldPrefix) = branchStack.pop
      while (formulaLabel.size > oldFormulaLabelSize)
        formulaLabel -= formulaLabel.last._1
      prefix = oldPrefix
    }

    private def reset : Unit = {
      branchStack.clear
      formulaLabel.clear
      prefix = ""
      formulaCounter = 1
    }

    //////////////////////////////////////////////////////////////////////////////

    private def printCertificate(cert : Certificate) : Unit = cert match {

      case BranchInferenceCertificate(inferences, child, _) => {
        val assumptions =
          computeAssumptions(inferences.toList.tail, child.assumedFormulas)

        for ((inf, assumptions) <- inferences.iterator zip assumptions.iterator)
          printInference(inf, assumptions, child.order)

        printCertificate(child)
      }

      case cert : BetaCertificate => {
        printlnPref
        printlnPref("BETA: splitting " +
                    l(cert.localAssumedFormulas) + " gives:")
        printCases(cert)
      }

      case cert : CutCertificate => {
        printlnPref
        printlnPref("CUT: with " +
                    (formulaPrinter for2String cert.cutFormula) + ":")
        printCases(cert)
      }

      case cert : SplitEqCertificate => {
        printlnPref
        printlnPref("SPLIT-EQ: splitting " +
                    l(cert.localAssumedFormulas) + " gives:")
        printCases(cert)
      }

      case StrengthenCertificate(ineq, _, _, _) => {
        printlnPref
        printlnPrefBreaking("STRENGTHEN: ",
                      "tightening of inequality " + l(ineq) + " gives:")
        printCases(cert)
      }

      case cert : OmegaCertificate => {
        printlnPref
        printlnPref("OMEGA: resolving " +
                    l(cert.localAssumedFormulas) + " by considering:")
        printCases(cert)
      }

      case cert : CloseCertificate => {
        printlnPref
        printlnPrefBreaking("CLOSE: ",
                    l(cert.localAssumedFormulas) + " " +
                    (if (cert.localAssumedFormulas.size == 1) "is" else "are") +
                    " inconsistent.")
      }

      case DagCertificateConverter.ReferenceCertificate(id, localAssumed,
                                                        _, _, _) => {
        printlnPref
        printlnPrefBreaking("REF_CLOSE: ",
                            l(localAssumed) + " " +
                            (if (localAssumed.size == 1) "is" else "are") +
                            " inconsistent by sub-proof #" +
                            (certificateNum - id - 1) + ".")
      }
    }

    private def printCases(cert : Certificate) : Unit = {
      var num = 0
      printlnPref
      for (subCert <- cert.subCertificates) {
        push
        try {
          printlnPref("Case " + (num + 1) + ":")
          addPrefix("| ")
          printlnPref
          introduceFormulasIfNeeded(cert localProvidedFormulas num,
                                    subCert.assumedFormulas,
                                    subCert.order)
          printCertificate(subCert)
          printlnPref
        } finally {
          pop
        }
        num = num + 1
      }
      printlnPref("End of split")
    }

    private def computeAssumptions(infs : List[BranchInference],
                                   childAssumptions : Set[CertFormula])
                                  : List[Set[CertFormula]] = infs match {
      case List() => List(childAssumptions)
      case inf :: remInfs => {
        val subRes@(lastA :: _) =
          computeAssumptions(remInfs, childAssumptions)
        (lastA -- inf.providedFormulas ++ inf.assumedFormulas) :: subRes
      }
    }

    private def printInference(inf : BranchInference,
                               nextAssumedFormulas : Set[CertFormula],
                               childOrder : TermOrder) : Unit = {
      if (inf == ReusedProofMarker ||
          (inf.localBoundConstants.isEmpty &&
           (inf.providedFormulas forall {
             f => (formulaLabel contains f) || !(nextAssumedFormulas contains f)
           })))
        return

      printlnPref

      inf match {
        case _ : AlphaInference =>
          printRewritingRule("ALPHA", inf)
        case _ : ReducePredInference | _ : ReduceInference =>
          printRewritingRule("REDUCE", inf)
        case _ : SimpInference =>
          printRewritingRule("SIMP", inf)
        case _ : PredUnifyInference =>
          printRewritingRule("PRED_UNIFY", inf)
        case _ : CombineEquationsInference =>
          printRewritingRule("COMBINE_EQS", inf)
        case _ : CombineInequalitiesInference =>
          printRewritingRule("COMBINE_INEQS", inf)
        case _ : DirectStrengthenInference =>
          printRewritingRule("STRENGTHEN", inf)
        case _ : AntiSymmetryInference =>
          printRewritingRule("ANTI_SYMM", inf)
        case _ : DivRightInference =>
          printRewritingRule("DIV_RIGHT", inf)
        case inf : TheoryAxiomInference =>
          printRewritingRule("THEORY_AXIOM " + inf.theory, inf)
        case QuantifierInference(quantifiedFormula, newConstants, _, _) =>
          printlnPrefBreaking("DELTA: ",
                      "instantiating " +  l(quantifiedFormula) +
                      " with fresh " +
                      (if (newConstants.size > 1) "symbols" else "symbol") + " " +
                      (newConstants mkString ", ") + " gives:")
        case GroundInstInference(quantifiedFormula, instanceTerms,
                                 _, dischargedAtoms, _, _) =>
          printlnPrefBreaking("GROUND_INST: ",
                      "instantiating " +  l(quantifiedFormula) + " with " +
                      ((for (t <- instanceTerms.reverse)
                       yield (formulaPrinter term2String t)) mkString ", ") +
                      (if (!dischargedAtoms.isEmpty)
                         ", simplifying with " + l(dischargedAtoms)
                       else
                         "") +
                      " gives:")
        case ColumnReduceInference(_, newSymbol, definingEq, _, _) =>
          printlnPrefBreaking("COL_REDUCE: ",
                      "introducing fresh symbol " + newSymbol +
                      " defined by:")
      }

      introduceFormulasIfNeeded(inf.providedFormulas,
                                nextAssumedFormulas,
                                childOrder)
    }

    private def printRewritingRule(name : String, inf : BranchInference) : Unit =
      printlnPrefBreaking(name + ": ",
                          l(inf.assumedFormulas) +
                          (inf.assumedFormulas.size match {
                            case 0 => ""
                            case 1 => " implies:"
                            case _ => " imply:"
                           }))

  }


}
