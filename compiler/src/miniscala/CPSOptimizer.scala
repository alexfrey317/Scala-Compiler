package miniscala

import scala.collection.mutable.{Map => MutableMap}

abstract class CPSOptimizer[T <: CPSTreeModule {type Name = Symbol}]
(val treeModule: T) {

  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  def print(msg: String, tree: Tree): Unit = {
    val f = CPSTreeFormatter.SymbolicCPSTreeFormatter
    val writer = new java.io.PrintWriter(System.out)
    writer.println(msg)
    f.toDocument(tree.asInstanceOf[SymbolicCPSTreeModule.Tree]).format(80, writer)
    writer.println()
    writer.flush()
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
                            /* How many times a symbol is encountered in the Tree. Note: The
                             * census for the whole program gets calculated once in the
                             * beginning, and passed to the initial state.
                             */
                            census: Map[Name, Count],
                            // Name substitution that needs to be applied to the current tree
                            subst: Substitution[Name] = Substitution.empty,
                            // Names that have a constant value
                            lEnv: Map[Name, Literal] = Map.empty,
                            // The inverse of lEnv
                            lInvEnv: Map[Literal, Name] = Map.empty,
                            // A known block mapped to its tag and length
                            bEnv: Map[Name, (Literal, Name)] = Map.empty,
                            // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
                            // Note: useful for common-subexpression elimination
                            eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
                            // Continuations that will be inlined
                            cEnv: Map[Name, CntDef] = Map.empty,
                            // Functions that will be inlined
                            fEnv: Map[Name, FunDef] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true

    // Checks whether a symbols is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Addas a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))

    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))

    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))

    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))

    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))

    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))

    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))

    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))

    /*
     * The same state, with empty inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit state: State): Tree = tree match {
      case LetL(name: Name, value: Literal, body: Tree) => {
        //Dead code
        if (state.dead(name)) {
          shrinkT(body)
        }
        //Common Subexpression Elimination
        else if (state.lInvEnv.contains(value)) {
          val nState = state.withSubst(name, state.lInvEnv(value))
          shrinkT(body subst nState.subst)(nState)
        }
        //No-Opt
        else {
          LetL(name, value, shrinkT(body)(state.withLit(name, value)))
        }
      }

      case LetP(name: Name, prim: ValuePrimitive, args: Seq[Name], body: Tree) => {
        val unst = this.unstable(prim)
        val imp = this.impure(prim)

        def noOpt(): Tree = LetP(name, prim, args, shrinkT(body)(state.withExp(name, prim, args)))


        //Dead Code
        if (state.dead(name) && !imp) {
          shrinkT(body)
        }
        //Common Subexpression Elimination
        else if (!unst && !imp && state.eInvEnv.contains((prim, args))) {
          val nState = state.withSubst(name, state.eInvEnv((prim, args)));
          shrinkT(body subst nState.subst)(nState)
        }
        //Identity
        else if (identity == prim) {
          val nState = state.withSubst(name, args(0))
          shrinkT(body subst nState.subst)(nState)
        }
        //Block Alloc
        else if (blockAllocTag.isDefinedAt(prim)) {
          LetP(name, prim, args, shrinkT(body)(state.withBlock(name, blockAllocTag(prim), args(0))))
        }
        //Block Length
        else if (prim == blockLength && (state.bEnv contains args(0))) {
          shrinkT(LetP(name, identity, Seq(state.bEnv(args(0))._2), body))
        }
        //Block Tag
        else if (prim == blockTag && (state.bEnv contains args(0))) {
          shrinkT(LetL(name, state.bEnv(args(0))._1, body))
        }
        //Block Get
        else if (prim == blockGet && state.bEnv.contains(args(0)) && state.bEnv(args(0))._1 == IntLit(BlockTag.Function.id)) {
          //Get where block was set
          val sourceBlockSet = state.eInvEnv find { case ((prim, blockArgs), _) =>
            prim == blockSet && blockArgs(0) == args(0) && blockArgs(1) == args(1)
          }

          //Block Get Grab value used to set
          if (sourceBlockSet.isDefined) {
            shrinkT(LetP(name, identity, Seq(sourceBlockSet.get._1._2(2)), body))
          }
          //No-Opt
          else {
            noOpt()
          }


        }
        //Constant Folding
        else if (!unst && !imp && (args forall { arg => state.lEnv contains (arg) })) {
          val eval = vEvaluator((prim, args map { arg => state.lEnv(arg) }))
          LetL(name, eval, shrinkT(body)(state.withLit(name, eval)))
        }
        //Same Args Reduce
        else if (args.length == 2 && sameArgReduce.isDefinedAt(prim) && args(0) == args(1)) {
          shrinkT(LetL(name, sameArgReduce(prim), body))
        }
        //Neutral/Absorbing Left
        else if (!unst && !imp && args.length == 2 && (state.lEnv contains args(0))) {
          val leftLit = state.lEnv(args(0))

          //Neutral
          if (leftNeutral((leftLit, prim))) {
            shrinkT(LetP(name, identity, Seq(args(1)), body))
          }
          //Absorbing
          else if (leftAbsorbing((leftLit, prim))) {
            shrinkT(LetP(name, identity, Seq(args(0)), body))
          }
          //No-Opt
          else {
            noOpt()
          }
        }
        //Neutral/Absorbing Right
        else if (!unst && !imp && args.length == 2 && (state.lEnv contains args(1))) {
          val rightLit = state.lEnv(args(1))

          //Neutral
          if (rightNeutral((prim, rightLit))) {
            shrinkT(LetP(name, identity, Seq(args(0)), body))
          }
          //Absorbing
          else if (rightAbsorbing((prim, rightLit))) {
            shrinkT(LetP(name, identity, Seq(args(1)), body))
          }
          //No-Opt
          else {
            noOpt()
          }
        }
        //No-Opt
        else {
          noOpt()
        }
      }

      case LetC(cnts: Seq[CntDef], body: Tree) => {
        //Dead Code
        val liveCnts = cnts filter {
          cnt => !state.dead(cnt.name)
        }
        val inlineCnts = liveCnts filter (cnt => state.appliedOnce(cnt.name))
        val nCnts = liveCnts map { case CntDef(name, args, body) =>
          CntDef(name, args, shrinkT(body)(state.withEmptyInvEnvs.withCnts(inlineCnts)))
        }

        //Check for any continuations
        if (nCnts.isEmpty) {
          shrinkT(body)
        } else {
          LetC(nCnts, shrinkT(body)(state.withCnts(inlineCnts)))
        }
      }

      case LetF(funs: Seq[FunDef], body: Tree) => {
        //Dead Code
        val liveFuns = funs filter {
          fun => !state.dead(fun.name)
        }
        val inlineFuns = liveFuns filter (fun => state.appliedOnce(fun.name))
        val nFuns = liveFuns map { case FunDef(name, retC, args, body) =>
          FunDef(name, retC, args, shrinkT(body)(state.withEmptyInvEnvs.withFuns(inlineFuns)))
        }


        //Check for any functions
        if (nFuns.isEmpty) {
          shrinkT(body)
        } else {
          LetF(nFuns, shrinkT(body)(state.withFuns(inlineFuns)))
        }
      }

      case AppC(name: Name, args: Seq[Name]) => {
        //Shrinking Inlining
        if (state.cEnv contains (name)) {
          val cntDef = state.cEnv(name)
          val nState = state.withSubst(cntDef.args, args)
          shrinkT(cntDef.body subst nState.subst)(nState)
        }
        //No-Opt
        else {
          tree
        }
      }

      case AppF(name: Name, retC: Name, args: Seq[Name]) => {
        //Shrinking Inlining
        if (state.fEnv contains (name)) {
          val funDef = state.fEnv(name)
          val nState = state.withSubst(funDef.args, args).withSubst(funDef.retC, retC)
          shrinkT(funDef.body subst nState.subst)(nState)
        }
        //No-Opt
        else {
          tree
        }
      }

      case If(cond: TestPrimitive, args: Seq[Name], thenC: Name, elseC: Name) => {
        //Same Args
        if (args.length == 2 && sameArgReduceC.isDefinedAt(cond) && args(0) == args(1)) {
          if (sameArgReduceC(cond)) {
            shrinkT(AppC(thenC, Seq()))
          }
          else {
            shrinkT(AppC(elseC, Seq()))
          }
        }
        //Constant Folding Literal Args
        else if (args forall { arg => state.lEnv contains arg }) {
          if (cEvaluator((cond, args map { arg => state.lEnv(arg) }))) {
            shrinkT(AppC(thenC, Seq()))
          } else {
            shrinkT(AppC(elseC, Seq()))
          }
        }
        //No-Opt
        else {
          tree
        }
      }

      case _ => tree
    }

    shrinkT(tree)(State(census(tree)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = Stream.iterate((0, tree), fibonacci.length + 1) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit state: State): Tree = tree match {
        case LetC(cnts: Seq[CntDef], body: Tree) => {
          //Calculate new continuations and those to inline
          val inlineCnts = cnts filter { cnt =>
            size(cnt.body) <= cntLimit
          }

          //Check for no continuations
          if (cnts.isEmpty) {
            inlineT(body)(state.withCnts(inlineCnts))
          } else {
            LetC(cnts, inlineT(body)(state.withCnts(inlineCnts)))
          }
        }

        case LetF(funs: Seq[FunDef], body: Tree) => {
          //Calculate new functions and those to inline
          val inlineFuns = funs filter { fun =>
            size(fun.body) <= funLimit
          }

          //Check for no funs
          if (funs.isEmpty) {
            inlineT(body)(state.withFuns(inlineFuns))
          } else {
            LetF(funs, inlineT(body)(state.withFuns(inlineFuns)))
          }
        }

        case AppC(name, args) => {
          //General Inlining
          if (state.cEnv.contains(name)) {
            val cntDef = state.cEnv(name)
            val toReplace = getNames(cntDef.body)
            val nState = state
              .withSubst(toReplace, toReplace map (_.copy))
              .withSubst(cntDef.args, args)
            inlineT(cntDef.body subst nState.subst)(nState)
          }
          //No-Opt
          else {
            tree
          }
        }

        case AppF(name, retC, args) => {
          //General Inlining
          if (state.fEnv.contains(name)) {
            val funDef = state.fEnv(name)
            val toReplace = getNames(funDef.body)
            val nState = state
              .withSubst(toReplace, toReplace map (_.copy))
              .withSubst(funDef.args, args)
              .withSubst(funDef.retC, retC)
            inlineT(funDef.body subst nState.subst)(nState)
          }
          //No-Opt
          else {
            tree
          }
        }

        case LetL(name, value, body) => {
          //No-Opt
          LetL(name, value, inlineT(body)(state.withLit(name, value)))
        }

        case LetP(name, prim, args, body) => {
          //No-Opt
          LetP(name, prim, args, inlineT(body)(state.withExp(name, prim, args)))
        }

        case _ => tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile { case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def getNames(tree: Tree): Seq[Name] = {
    tree match {
      case LetL(name, value, body) => name +: getNames(body)
      case LetP(name, prim, args, body) => name +: getNames(body)
      case LetC(cnts, body) => cnts.flatMap(cnt => cnt.name +: getNames(cnt.body)) ++ getNames(body)
      case LetF(funs, body) => funs.flatMap(fun => fun.name +: getNames(fun.body)) ++ getNames(body)
      case _ => Seq()
    }
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimitive on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Return true for the block get primitive
  protected val blockGet: ValuePrimitive
  // Return true for the block set primitive
  protected val blockSet: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean]
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
  with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {

  import treeModule._

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean =
    Set(MiniScalaBlockSet, MiniScalaByteRead, MiniScalaByteWrite)

  // Returns whether different applications of a ValuePrimitive on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean = {
    case MiniScalaBlockAlloc(_) | MiniScalaBlockGet | MiniScalaByteRead => true
    case _ => false
  }

  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case MiniScalaBlockAlloc(tag) => IntLit(tag)
  }

  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive = MiniScalaBlockTag

  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive = MiniScalaBlockLength

  // Return true for the block get primitive
  protected val blockGet: ValuePrimitive = MiniScalaBlockGet

  // Return true for the block set primitive
  protected val blockSet: ValuePrimitive = MiniScalaBlockSet

  // Returns true for the identity primitive
  protected val identity: ValuePrimitive = MiniScalaId

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set(
      (IntLit(0), MiniScalaIntAdd),
      (IntLit(1), MiniScalaIntMul),
      (IntLit(~0), MiniScalaIntBitwiseAnd),
      (IntLit(0), MiniScalaIntBitwiseOr),
      (IntLit(0), MiniScalaIntBitwiseXOr)
    )

  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set(
      (MiniScalaIntAdd, IntLit(0)),
      (MiniScalaIntSub, IntLit(0)),
      (MiniScalaIntMul, IntLit(1)),
      (MiniScalaIntDiv, IntLit(1)),
      (MiniScalaIntArithShiftLeft, IntLit(0)),
      (MiniScalaIntArithShiftRight, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(~0)),
      (MiniScalaIntBitwiseOr, IntLit(0)),
      (MiniScalaIntBitwiseXOr, IntLit(0))
    )

  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set(
      (IntLit(0), MiniScalaIntMul),
      (IntLit(0), MiniScalaIntBitwiseAnd),
      (IntLit(~0), MiniScalaIntBitwiseOr),
      (IntLit(0), MiniScalaIntArithShiftLeft),
      (IntLit(0), MiniScalaIntArithShiftRight),
    )

  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set(
      (MiniScalaIntMul, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(0)),
      (MiniScalaIntBitwiseOr, IntLit(~0)),
    )

  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] =
    Map(
      MiniScalaIntSub -> IntLit(0),
      MiniScalaIntDiv -> IntLit(1),
      MiniScalaIntMod -> IntLit(0),
      MiniScalaIntBitwiseXOr -> IntLit(0)
    )

  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case MiniScalaIntLe | MiniScalaIntGe | MiniScalaEq => true
    case MiniScalaIntLt | MiniScalaIntGt | MiniScalaNe => false
  }

  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal] = {
    //Int ValuePrimitives
    case (MiniScalaIntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (MiniScalaIntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (MiniScalaIntSub, Seq(IntLit(x))) => IntLit(-x)
    case (MiniScalaIntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (MiniScalaIntDiv, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorDiv(x, y))
    case (MiniScalaIntMod, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorMod(x, y))

    //Bit ValuePrimitives
    case (MiniScalaIntArithShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (MiniScalaIntArithShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y);
    case (MiniScalaIntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (MiniScalaIntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y);
    case (MiniScalaIntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)

    //Other
    case (MiniScalaCharToInt, Seq(CharLit(x))) => IntLit(x.toInt)
    case (MiniScalaIntToChar, Seq(IntLit(x))) => CharLit(x.toChar)

    //Block
    case (MiniScalaBlockTag, _) => IntLit(-1)
  }

  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean] = {
    //Type check
    case (MiniScalaIntP, Seq(IntLit(_))) => true
    case (MiniScalaIntP, Seq(_)) => false
    case (MiniScalaBoolP, Seq(BooleanLit(_))) => true
    case (MiniScalaBoolP, Seq(_)) => false
    case (MiniScalaCharP, Seq(CharLit(_))) => true
    case (MiniScalaCharP, Seq(_)) => false
    case (MiniScalaUnitP, Seq(UnitLit)) => true
    case (MiniScalaUnitP, Seq(_)) => false
    case (MiniScalaBlockP, Seq(_)) => false

    //Int Compare
    case (MiniScalaIntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (MiniScalaIntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (MiniScalaEq, Seq(IntLit(x), IntLit(y))) => x == y
    case (MiniScalaNe, Seq(IntLit(x), IntLit(y))) => x != y
    case (MiniScalaIntGe, Seq(IntLit(x), IntLit(y))) => x >= y
    case (MiniScalaIntGt, Seq(IntLit(x), IntLit(y))) => x > y

    //Char compare
    case (MiniScalaEq, Seq(CharLit(x), CharLit(y))) => x == y
    case (MiniScalaNe, Seq(CharLit(x), CharLit(y))) => x != y

    //Bool compare
    case (MiniScalaEq, Seq(BooleanLit(x), BooleanLit(y))) => x == y
    case (MiniScalaNe, Seq(BooleanLit(x), BooleanLit(y))) => x != y
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
  with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {

  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }

  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength
  protected val blockGet: ValuePrimitive = CPSBlockGet
  protected val blockSet: ValuePrimitive = CPSBlockSet

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
      (CPSArithShiftL, 0), (CPSArithShiftR, 0),
      (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean] = {

    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
