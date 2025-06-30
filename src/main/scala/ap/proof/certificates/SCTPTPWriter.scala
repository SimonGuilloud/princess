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
import ap.parameters.{Param, GlobalSettings}

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}
import scala.util.Sorting
import _root_.ap.proof.certificates.CertFormula.certFormulaOrdering




object SCTPTPWriter {
  
  def apply(cert : Certificate, prover: AbstractFileProver, filename: String, settings: GlobalSettings) = {

    Param.ORIGINAL_FILES(settings) match {
      case Seq(of) if of endsWith ".p" => {
        val reader = new java.io.BufferedReader (new java.io.FileReader(new java.io.File (of)))
        // print content of file
        var line = reader.readLine()  
        while (line != null) {
          println(line)
          line = reader.readLine()
        }
      }
      case _ => {
        println("No original file found: " + Param.ORIGINAL_FILES(settings))
        println("")
        import IExpression._
        //println("TPTPLineariser(prover.rawInputFormula, filename)\n")
        //TPTPLineariser(prover.rawInputFormula, filename)
        //println("\n\n\n\n\n\n")
      
      }
    }


    // input
    {
      //import IExpression._
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

    printer(dagCert, prover)

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

      val certificateNum = dagCertificate.size
      val assumedFormulas = dagCertificate.last.assumedFormulas

      val partNamesSet = initialFormulas.keySet
      val partNames =
        (partNamesSet filterNot predefNamesSet).toIndexedSeq.sortBy(_.toString) ++
        (predefNames filter partNamesSet).toIndexedSeq

      val (usedNames, unusedNames) = partNames partition {
        name => assumedFormulas contains initialFormulas(name)
      }

      println("% Assumptions after simplification:")

      var left = List[CertFormula]()
      try {
        for (name <- usedNames) {
          val f = initialFormulas(name)
          val label = name match {
            case PartName.NO_NAME         => 
              val label = "input"
              introduceFormula(f, label, List())
              label
            case PartName.FUNCTION_AXIOMS => 
              val label = "function-axioms"
              println(s"tff($label, plain,")
              println("  " + (formulaPrinter for2String f))
              println("  " + s"inference(functionAxioms, [], [])")
              println(").")
              formulaLabel.put(f, label)
              label
            case PartName.THEORY_AXIOMS   => 
              val label = "theory-axioms"
              introduceFormula(f, label, Nil)
              label
            case _                        => 
              val prevlabel = formulaPrinter.partName2String(name)
              val label = prevlabel + "_"
              val seq = if (prevlabel.size > 0 && prevlabel(0) == 'c') {
                left = f :: left
                val seq = 
                mkSequent(List(f), List(f))
                let(f, label)
                seq
              } else mkSequent(List(), List(f))
              println(s"tff($label, plain,")
              formulaLabel.put(f, label)
              println(s"  $seq,")
              println("  " + s"inference(princessSimplification, [], [$prevlabel])")
              println(s").")
          }
          
          // introduceFormula(initialFormulas(name), label)
        }


        println()
        println("% Those formulas are unsatisfiable:")


        println()
        println("% Begin of proof")
        certificateToSCTPTP(dagCertificate.last, left)

      } finally { ()
      }
      println("% End of proof")

      for (id <- (certificateNum - 2) to 0 by -1) {
        val cert = dagCertificate(id)

        println()
        println("% Sub-proof #" + (certificateNum - id - 1) +
                "%  shows that the following formulas are inconsistent:")
        println("% ----------------------------------------------------------------")

        try {
          for (f <- cert.assumedFormulas)
            introduceFormula(f, "unknownInference", left)

          println()
          println("% Begin of proof")
          certificateToSCTPTP(cert, left)
        } finally {
        }
        println("% End of proof")
      }
    }

    private var certificateNum = 0

    //////////////////////////////////////////////////////////////////////////////

    //////////////////////////////////////////////////////////////////////////////

    private val formulaLabel = new LinkedHashMap[CertFormula, String]
    private val letMap = new LinkedHashMap[CertFormula, String]

    private def let(f : CertFormula, name: String) : Unit = {
      println(s"let(#$name, ${dol}tff(${formulaPrinter for2String f})).")
      letMap.put(f, name)
    }
    private def letOrPretty(f : CertFormula) : String = {
      if (letMap contains f) "#" + letMap(f)
      else formulaPrinter for2String f
    }
    private var formulaCounter : Int = 1

    private def introduceFormula(f : CertFormula, inference: String, left: List[CertFormula]) : Unit = {
      val seq = mkSequent(left, List(f))
      println(s"tff(f$formulaCounter, plain, $seq, $inference).")
      formulaLabel.put(f, "f" + formulaCounter)
      formulaCounter = formulaCounter + 1
    }


    private def introduceFormulaIfNeeded
                  (f : CertFormula, assumedFormulas : List[CertFormula], left: List[CertFormula]) : Unit = {
      if (!(formulaLabel contains f) && (assumedFormulas contains f))
        introduceFormula(f, "", left)
    }

    private def introduceFormulasIfNeeded
                  (fs : Iterable[CertFormula],
                   assumedFormulas : List[CertFormula],
                   order : TermOrder, inference: String, left: List[CertFormula]) : Unit = {
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

      for (f <- neededFors) introduceFormula(f, inference, left)
    }

    private def l(f : CertFormula) : String = formulaLabel(f)

    private def l(fs : Iterable[CertFormula]) : String =
      (fs.toSeq map l) mkString ", "

    private val dolfalse = "$false"
    private val dol = "$"

    def mkSequent(left : List[CertFormula], right : List[CertFormula]) : String = {
      val leftStr = (left map letOrPretty) mkString ", "
      val rightStr = right map (formulaPrinter for2String _) mkString ", "
      s"[$leftStr] --> [$rightStr]"
    }
    //////////////////////////////////////////////////////////////////////////////

    private def certificateToSCTPTP(cert : Certificate, left: List[CertFormula]) : Unit = {

      cert match {

      case BranchInferenceCertificate(inferences, child, _) => {

        val assumptions =
          computeAssumptions(inferences.toList.tail, child.assumedFormulas.toList)

        val infsAndAssump = inferences.iterator zip assumptions.iterator
        val (inf, assums) = infsAndAssump.next

        printInference(inf, assums, child.order, child, left, infsAndAssump, child)

        //for ((inf, assumptions) <- (inferences.iterator zip assumptions.iterator))
          
        //certificateToSCTPTP(child, left)
      }
/*
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
*/
      case cert : CloseCertificate => {

        val seq = mkSequent(left, List())
        
        println(s"tff(f$formulaCounter, plain, $seq, inference(CLOSE, [], [${l(cert.localAssumedFormulas)}])).")

      }
/*
      case DagCertificateConverter.ReferenceCertificate(id, localAssumed,
                                                        _, _, _) => {
        printlnPref
        printlnPrefBreaking("REF_CLOSE: ",
                            l(localAssumed) + " " +
                            (if (localAssumed.size == 1) "is" else "are") +
                            " inconsistent by sub-proof #" +
                            (certificateNum - id - 1) + ".")
      }
      */
      case _ => println("remaining cert:" + cert.getClass().getName())
    }}

    private def printCases(cert : Certificate, left: List[CertFormula]) : Unit = {
      var num = 0
      for (subCert <- cert.subCertificates) {
        try {
          introduceFormulasIfNeeded(cert localProvidedFormulas num,
                                    subCert.assumedFormulas.toList,
                                    subCert.order, "unknownInference", left)
          certificateToSCTPTP(subCert, left)
        } finally {
        }
        num = num + 1
      }
    }

    private def computeAssumptions(infs : List[BranchInference],
                                   childAssumptions : List[CertFormula])
                                  : List[List[CertFormula]] = infs match {
      case List() => List(childAssumptions)
      case inf :: remInfs => {
        val subRes@(lastA :: _) =
          computeAssumptions(remInfs, childAssumptions)
        (lastA.filterNot( inf.providedFormulas contains _) ++ inf.assumedFormulas) :: subRes
      }
    }

    private def printInference(inf : BranchInference,
                               nextAssumedFormulas : List[CertFormula],
                               childOrder : TermOrder, child: Certificate, left: List[CertFormula],
                               remainingInferences: Iterator[(BranchInference, List[CertFormula])], nextCert: Certificate
                               ) : Unit = {
      if (inf == ReusedProofMarker ||
          (inf.localBoundConstants.isEmpty &&
           (inf.providedFormulas forall {
             f => (formulaLabel contains f) || !(nextAssumedFormulas contains f)
           })))
        return
      def next(nextleft: List[CertFormula] = left) = {
        if (remainingInferences.hasNext) {
          val (inf, nextAssumedFormulas) = remainingInferences.next
          printInference(inf, nextAssumedFormulas, childOrder, nextCert, nextleft, remainingInferences, nextCert)
        } else {
          certificateToSCTPTP(nextCert, left)
        }
      }

      inf match {
        case _ : AlphaInference =>
          val inference = printRewritingRule("ALPHA", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : ReducePredInference | _ : ReduceInference =>
          val inference = printRewritingRule("REDUCE", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : SimpInference =>
          val inference = printRewritingRule("SIMP", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : PredUnifyInference =>
          val inference = printRewritingRule("PRED_UNIFY", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : CombineEquationsInference =>
          val inference = printRewritingRule("COMBINE_EQS", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : CombineInequalitiesInference =>
          val inference = printRewritingRule("COMBINE_INEQS", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : DirectStrengthenInference =>
          val inference = printRewritingRule("STRENGTHEN", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : AntiSymmetryInference =>
          val inference = printRewritingRule("ANTI_SYMM", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case _ : DivRightInference =>
          val inference = printRewritingRule("DIV_RIGHT", inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case inf : TheoryAxiomInference =>
          val inference = printRewritingRule("THEORY_AXIOM " + inf.theory, inf)
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
        case QuantifierInference(quantifiedFormula, newConstants, _, _) =>

          val inference = s"inference(hyp, [${newConstants mkString ", "}]," +
            s"[${l(quantifiedFormula)}])"
          println("% Start of DELTA step: ")
          let(inf.providedFormulas.head, "f" + (formulaCounter))
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, inf.providedFormulas.head :: left)
          next(inf.providedFormulas.head :: left)
          println("% End of DELTA step: ")
          val exInf = s"inference(leftExists, [${newConstants.head}], [${formulaCounter - 1}])"
          val seq = mkSequent(quantifiedFormula :: left, List())
          println(s"tff(f$formulaCounter, $seq, $exInf).")
          formulaCounter = formulaCounter + 1
          val cutInf = s"inference(cut, [${left.size-1}], [${l(quantifiedFormula)}, f${formulaCounter - 1}])"
          val cutSeq = mkSequent(left, List())
          println(s"tff(f$formulaCounter, $cutSeq, $cutInf).")
          formulaCounter = formulaCounter + 1
        case GroundInstInference(quantifiedFormula, instanceTerms,
                                 _, dischargedAtoms, _, _) =>

          val prems = (l(quantifiedFormula)) + (if (!dischargedAtoms.isEmpty)
                          ", " + l(dischargedAtoms)
                        else
                          "")
          val params = instanceTerms.reverse.map(formulaPrinter term2String) mkString ","
          val inference = s"inference(GROUND_INST, [${instanceTerms mkString ", "}]," +
            s"[$prems])"
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            next()
          /*printlnPrefBreaking("GROUND_INST: ",
                      "instantiating " +  l(quantifiedFormula) + " with " +
                      ((for (t <- instanceTerms.reverse)
                       yield (formulaPrinter term2String t)) mkString ", ") +
                      (if (!dischargedAtoms.isEmpty)
                         ", simplifying with " + l(dischargedAtoms)
                       else
                         "") +
                      " gives:")*/
        case ColumnReduceInference(_, newSymbol, definingEq, _, _) =>
          /*printlnPrefBreaking("COL_REDUCE: ",
                      "introducing fresh symbol " + newSymbol +
                      " defined by:")
                      */
          val inference = s"inference(ColumnReduceInference, [], [])"
          introduceFormulasIfNeeded(inf.providedFormulas,
            nextAssumedFormulas,
            childOrder, inference, left)
            certificateToSCTPTP(child, left)
            next()
      }


    }

    private def printRewritingRule(name : String, inf : BranchInference) : String =
      s"inference($name, [], [${l(inf.assumedFormulas)}])"

  }


}
