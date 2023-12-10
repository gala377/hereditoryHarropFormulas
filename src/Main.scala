import scala.annotation.newMain
import scala.collection.mutable.HashMap
import scala.collection.mutable
import scala.util.boundary
type VarIndex = Int
type UniverseIndex = Int

case class UnificationError(msg: String) extends Exception(msg)

enum Atom:
  case Var(id: VarIndex)
  case SynthesisedConst(id: VarIndex)
  case Functor(name: String, args: List[Atom])
  case Const(name: String)

  def substitute(substitution: Map[VarIndex, Atom]): Atom =
    this match
      case Atom.Var(id) =>
        substitution.get(id) match
          case Some(atom) =>
            // ? We need to do this to avoid the case when
            // ? var gets substituted by another var
            atom.substitute(substitution)
          case None => this
      case Atom.Functor(name, args) =>
        Atom.Functor(
          name,
          args.map((a) => a.substitute(substitution))
        )
      case a => a

  def substituteConst(substitution: Map[String, Atom]): Atom =
    this match
      case Atom.Const(name) =>
        substitution.get(name) match
          case Some(atom) => atom
          case None       => this
      case Atom.Functor(name, args) =>
        Atom.Functor(
          name,
          args.map((a) => a.substituteConst(substitution))
        )
      case a => a

  def containsVar(id: VarIndex): Boolean =
    this match
      case Atom.Var(id1) if id == id1 => true
      case Atom.Functor(_, args)      => args.exists(_.containsVar(id))
      case _                          => false

  /** Check if variable with given id occurs in this atom */
  def occurenceCheck(id: VarIndex): Boolean =
    this match
      case Atom.Var(id1) if id == id1 => true
      case Atom.Functor(_, args)      => args.exists(_.occurenceCheck(id))
      case _                          => false

  /** Check if there is any constant within this atom with universe index
    * greater than the universe index of the given variable
    *
    * @return
    *   true if there is any constant violating the check, false if otherwise
    */
  def universeCheck(
      id: VarIndex,
      labeling: (VarIndex) => UniverseIndex
  ): Boolean =
    this match
      case Atom.Const(_) => false
      case Atom.Functor(_, args) =>
        args.exists((a) => a.universeCheck(id, labeling))
      case Atom.Var(_)                  => false
      case Atom.SynthesisedConst(varid) => labeling(id) < labeling(varid)

  def minUniverseVar(
      labeling: (VarIndex) => UniverseIndex
  ): UniverseIndex =
    this match
      case Atom.Const(_) => 0
      case Atom.Functor(_, args) =>
        args.map((a) => a.minUniverseVar(labeling)).min
      case Atom.Var(varid)              => labeling(varid)
      case Atom.SynthesisedConst(varid) => 0

/** */
enum Clause:
  case Fact(head: Atom)
  case Rule(head: Atom, body: List[Goal])
  case Forall(vars: List[String], clause: Clause)

  def substitute(substitution: Map[VarIndex, Atom]): Clause =
    this match
      case Clause.Fact(head) =>
        Clause.Fact(head.substitute(substitution))
      case Clause.Rule(head, body) =>
        Clause.Rule(
          head.substitute(substitution),
          body.map(_.substitute(substitution))
        )
      case Clause.Forall(vars, clause) =>
        Clause.Forall(vars, clause.substitute(substitution))

  def substituteConst(substitution: Map[String, Atom]): Clause =
    this match
      case Clause.Fact(head) =>
        Clause.Fact(head.substituteConst(substitution))
      case Clause.Rule(head, body) =>
        Clause.Rule(
          head.substituteConst(substitution),
          body.map(_.substituteConst(substitution))
        )
      case Clause.Forall(vars, clause) =>
        Clause.Forall(vars, clause.substituteConst(substitution))

enum DomainGoal:
  case Eq(a: Atom, b: Atom)

  def substitute(substitution: Map[VarIndex, Atom]): DomainGoal =
    this match
      case DomainGoal.Eq(a, b) =>
        DomainGoal.Eq(a.substitute(substitution), b.substitute(substitution))

  def substituteConst(substitution: Map[String, Atom]): DomainGoal =
    this match
      case DomainGoal.Eq(a, b) =>
        DomainGoal.Eq(
          a.substituteConst(substitution),
          b.substituteConst(substitution)
        )

enum Goal:
  case GAtom(atom: Atom)
  case And(goals: List[Goal])
  case Or(goals: List[Goal])
  case Exists(vars: List[String], goal: Goal)
  case Forall(vars: List[String], goal: Goal)
  case Implication(cond: List[Clause], goal: Goal)
  case Domain(domain: DomainGoal)

  def substitute(substitution: Map[VarIndex, Atom]): Goal =
    this match
      case Goal.GAtom(atom) =>
        Goal.GAtom(atom.substitute(substitution))
      case Goal.And(goals) =>
        Goal.And(goals.map(_.substitute(substitution)))
      case Goal.Or(goals) =>
        Goal.Or(goals.map(_.substitute(substitution)))
      case Goal.Exists(vars, goal) =>
        Goal.Exists(vars, goal.substitute(substitution))
      case Goal.Forall(vars, goal) =>
        Goal.Forall(vars, goal.substitute(substitution))
      case Goal.Implication(cond, goal) =>
        Goal.Implication(
          cond.map(_.substitute(substitution)),
          goal.substitute(substitution)
        )
      case Goal.Domain(domain) =>
        Goal.Domain(domain.substitute(substitution))

  def substituteConst(substitution: Map[String, Atom]): Goal =
    this match
      case Goal.GAtom(atom) =>
        Goal.GAtom(atom.substituteConst(substitution))
      case Goal.And(goals) =>
        Goal.And(goals.map(_.substituteConst(substitution)))
      case Goal.Or(goals) =>
        Goal.Or(goals.map(_.substituteConst(substitution)))
      case Goal.Exists(vars, goal) =>
        Goal.Exists(vars, goal.substituteConst(substitution))
      case Goal.Forall(vars, goal) =>
        Goal.Forall(vars, goal.substituteConst(substitution))
      case Goal.Implication(cond, goal) =>
        Goal.Implication(
          cond.map(_.substituteConst(substitution)),
          goal.substituteConst(substitution)
        )
      case Goal.Domain(domain) =>
        Goal.Domain(domain.substituteConst(substitution))

case class PendingGoal(
    assumptions: List[Clause],
    goal: Goal,
    universeIndex: Int
)

case class MachineState(
    program: List[Clause],
    goals: List[PendingGoal],
    labelingFunction: HashMap[VarIndex, UniverseIndex],
    // Substitutions made to the original goal to make it canonical
    // they need to be reversed in order to show solution in a comprehensible manner
    substitution: Map[VarIndex, Atom]
)

case class Machine(program: List[Clause]):
  val initialLabelingFunction = HashMap.empty[VarIndex, UniverseIndex]
  var nextVarIndex: VarIndex = 0

  def solve(goal: Goal): Option[Seq[Map[String, Atom]]] =
    val initialState = MachineState(
      program = program,
      goals = List.empty,
      labelingFunction = initialLabelingFunction,
      substitution = Map.empty
    )
    println("... making canon goal")
    val Canonical(cgoal, universe, substitutions) =
      makeCanonicalGoal(
        MachineState(
          program = program,
          goals = List.empty,
          labelingFunction = initialLabelingFunction,
          substitution = Map.empty
        ),
        goal,
        0,
        Map.empty
      )
    println("Inital labaeling function is " + initialState.labelingFunction)
    val unmap = substitutions.map((k, v) =>
      v match {
        case Atom.Var(id)              => id -> k
        case Atom.SynthesisedConst(id) => id -> k
        case _                         => throw Exception("Impossible")
      }
    )

    println("Program is " + program)
    println("Goal is " + cgoal)
    println("Unmap is " + unmap)
    val solutions = solve_(
      initialState.copy(goals = List(PendingGoal(List.empty, cgoal, universe)))
    )
    val ss: Seq[Map[String, Atom]] = solutions.map((s) =>
      s.filter((k, v) => unmap.contains(k))
        .filter((k, v) => !v.isInstanceOf[Atom.SynthesisedConst])
        .map((k, v) => unmap(k) -> v)
    )
    if ss.isEmpty then None
    else if ss.map(_.isEmpty).reduce(_ && _) then Some(Seq.empty)
    else Some(ss)

  private def solve_(state: MachineState): Seq[Map[VarIndex, Atom]] =
    state.goals.headOption match
      case None => Seq(state.substitution)
      case Some(PendingGoal(assumptions, goal, universeIndex)) =>
        println("Solving goal: " + goal)
        goal match
          case Goal.And(goals) =>
            solve_(
              state.copy(
                goals = goals.map((g) =>
                  PendingGoal(assumptions, g, universeIndex)
                ) ++ state.goals.tail
              )
            )
          case Goal.Or(goals) =>
            val restOfGoals = state.goals.tail
            val results = for (g <- goals) yield
              val newGoals =
                PendingGoal(assumptions, g, universeIndex) :: state.goals.tail
              solve_(state.copy(goals = newGoals))
            results.flatten
          case Goal.Implication(cond, goal) =>
            solve_(
              state.copy(
                goals = PendingGoal(
                  assumptions ++ cond,
                  goal,
                  universeIndex
                ) :: state.goals.tail
              )
            )
          case Goal.GAtom(atom) =>
            val matches = findMatching(state, assumptions, atom, universeIndex)
            val solutions = for (match_ <- matches) yield
              val (unification, conditions) = match_
              val newGoals = conditions.map((c) =>
                PendingGoal(
                  assumptions,
                  c,
                  universeIndex
                )
              ) ++ state.goals.tail
              solve_(
                state.copy(
                  goals = newGoals.toList,
                  substitution = state.substitution ++ unification
                )
              )
            println("Solutions: " + solutions)
            solutions.flatten.toList
          case Goal.Domain(domain) =>
            solveDomain_(state, assumptions, domain)
          case Goal.Exists(_, _) | Goal.Forall(_, _) =>
            throw Exception("Goal should be in canonical form")

  def solveDomain_(
      state: MachineState,
      assumptions: Seq[Clause],
      goal: DomainGoal
  ) = goal match
    case DomainGoal.Eq(a, b) =>
      unify(state, a, b) match
        case None => Seq()
        // todo: should we add value to the substitution or is it not needed?
        case Some(value) => Seq(state.substitution ++ value)

  def findMatching(
      state: MachineState,
      assumptions: Seq[Clause],
      goal: Atom,
      universe: UniverseIndex
  ): Seq[(Map[VarIndex, Atom], Seq[Goal])] =
    val matches = scala.collection.mutable.ListBuffer
      .empty[(Map[VarIndex, Atom], Seq[Goal])]
    val allClauses = assumptions ++ state.program
    for clause <- allClauses.map(inUniverse(state, universe)) do
      println("Find matching looking at clause: " + clause)
      boundary:
        println(" withing boundary")
        val (toUnify, conditions) = clause match
          case Clause.Fact(head)       => (head, mutable.ListBuffer.empty[Goal])
          case Clause.Rule(head, body) => (head, mutable.ListBuffer(body*))
          case Clause.Forall(vars, clause) =>
            throw Exception("Should be in canonical form")
        val unification = unify(state, toUnify, goal).getOrElse {
          boundary.break()
        }
        println(" . Unification: " + unification)
        val substitutedConditions =
          conditions.map((g) => g.substitute(unification))
        matches.addOne(unification, substitutedConditions.toSeq)
    println(" . returning matches: " + matches)
    matches.toSeq

  def unify(state: MachineState, atom_1: Atom, atom_2: Atom) =
    val stack = scala.collection.mutable.Stack.empty[(Atom, Atom)]
    stack.push((atom_1, atom_2))
    val unification: HashMap[VarIndex, Atom] = HashMap.empty

    def substitute(id: VarIndex, atom: Atom): Unit =
      unification.mapValuesInPlace((_, a) => a.substitute(Map(id -> atom)))
      stack.mapInPlace((a1, a2) =>
        (a1.substitute(Map(id -> atom)), a2.substitute(Map(id -> atom)))
      )
      // label adjustment
      val varUniverse = state.labelingFunction(id)
      state.labelingFunction.mapValuesInPlace((varId, universe) =>
        if atom.containsVar(varId) then universe min varUniverse
        else universe
      )

    try
      println("Stack is " + stack)
      while !stack.isEmpty do
        val (a, b) = stack.pop()
        println(" . Unifying " + a + " with " + b)
        (a, b) match
          case (Atom.Functor(h1, args1), Atom.Functor(h2, args2)) if h1 == h2 =>
            if args1.length != args2.length then
              throw UnificationError("Unification failed")
            else for (a1, a2) <- args1.zip(args2) do stack.push((a1, a2))
          case (Atom.Const(c1), Atom.Const(c2)) if c1 == c2 => ()
          case (Atom.SynthesisedConst(c1), Atom.SynthesisedConst(c2))
              if c1 == c2 =>
            ()
          case (Atom.SynthesisedConst(c1), Atom.Var(v1)) =>
            val constantUniverse = state.labelingFunction(c1)
            val varUniverse = state.labelingFunction(v1)
            println(" . . Constant universe: " + constantUniverse)
            println(" . . Var universe: " + varUniverse)
            // if varUniverse > constantUniverse then its okay
            // what is the reverse of this condition?
            if varUniverse < constantUniverse then
              println(" . . . Unification failed, labeling function")
              throw UnificationError(
                "Unification failed, labeling function"
              )
            substitute(v1, Atom.SynthesisedConst(c1))
            unification(v1) = Atom.SynthesisedConst(c1)
          case (v @ Atom.Var(_), c @ Atom.SynthesisedConst(_)) =>
            stack.push((c, v))
          case (Atom.Var(v1), Atom.Var(v2)) if v1 == v2 => ()
          case (Atom.Var(v1), other) =>
            if other.occurenceCheck(v1) then
              throw UnificationError("Unification failed, occurence check")
            if other.universeCheck(v1, state.labelingFunction) then
              throw UnificationError("Unification failed, universe check")
            substitute(v1, other)
            unification(v1) = other
          case (other, v @ Atom.Var(_)) => stack.push((v, other))
          case _ => throw UnificationError("Unification failed")
      Some(unification.toMap)
    catch case UnificationError(_) => None
    end try

  private def newVarIndex(): VarIndex =
    val result = nextVarIndex
    nextVarIndex += 1
    result

  def makeCanonicalGoal(
      state: MachineState,
      goal: Goal,
      currentUniverseIndex: UniverseIndex,
      canonSubstitutions: Map[String, Atom]
  ): Canonical[Goal] =
    println("Making canonical goal: " + goal)
    println("Current universe index: " + currentUniverseIndex)
    goal match
      case Goal.Exists(vars, goal) =>
        val newSubstitutions = vars.map { v =>
          val id = newVarIndex()
          state.labelingFunction += (id -> currentUniverseIndex)
          v -> Atom.Var(id)
        }.toMap
        makeCanonicalGoal(
          state,
          goal,
          currentUniverseIndex,
          canonSubstitutions ++ newSubstitutions
        )
      case Goal.Forall(vars, goal) =>
        val newSubstitutions = vars.map { v =>
          val id = newVarIndex()
          state.labelingFunction += (id -> (currentUniverseIndex + 1))
          v -> Atom.SynthesisedConst(id)
        }.toMap
        makeCanonicalGoal(
          state,
          goal,
          currentUniverseIndex + 1,
          canonSubstitutions ++ newSubstitutions
        )
      case Goal.Implication(cond, goal) =>
        // ? Skip the condition, it will be handled later
        val Canonical(canonicalGoal, u1, s1) =
          makeCanonicalGoal(
            state,
            goal,
            currentUniverseIndex,
            canonSubstitutions
          )
        Canonical(Goal.Implication(cond, canonicalGoal), u1, s1)
      case Goal.And(goals) =>
        val (g, u, s) = goals.foldLeft(
          (List.empty[Goal], currentUniverseIndex, canonSubstitutions)
        )((acc, g) => {
          val (gs, u1, s1) = acc
          val Canonical(canonicalGoal, u2, s2) =
            makeCanonicalGoal(
              state,
              g,
              u1,
              s1
            )
          (canonicalGoal :: gs, u1 max u2, s1 ++ s2)
        })
        Canonical(Goal.And(g.reverse), u, s)
      case Goal.Or(goals) =>
        val (g, u, s) = goals.foldLeft(
          (List.empty[Goal], currentUniverseIndex, canonSubstitutions)
        )((acc, g) => {
          val (gs, u1, s1) = acc
          val Canonical(canonicalGoal, u2, s2) =
            makeCanonicalGoal(
              state,
              g,
              u1,
              s1
            )
          (canonicalGoal :: gs, u1 max u2, s1 ++ s2)
        })
        Canonical(Goal.Or(g.reverse), u, s)
      case Goal.GAtom(atom) =>
        Canonical(
          Goal.GAtom(atom.substituteConst(canonSubstitutions)),
          currentUniverseIndex,
          canonSubstitutions
        )
      case Goal.Domain(domain) =>
        domain match
          case DomainGoal.Eq(a, b) =>
            val a2 = a.substituteConst(canonSubstitutions)
            val b2 = b.substituteConst(canonSubstitutions)
            Canonical(
              Goal.Domain(DomainGoal.Eq(a2, b2)),
              currentUniverseIndex,
              canonSubstitutions
            )

  def inUniverse(state: MachineState, universe: UniverseIndex)(
      clause: Clause
  ): Clause =
    clause match
      case Clause.Forall(vars, clause) =>
        val substitution = vars.map { v =>
          val id = newVarIndex()
          state.labelingFunction += (id -> universe)
          v -> Atom.Var(id)
        }.toMap
        inUniverse(state, universe)(clause.substituteConst(substitution))
      case c => c

case class Canonical[T](
    res: T,
    maxUniverse: UniverseIndex,
    substitution: Map[String, Atom]
)

@main
def main =
  val program = List(
    Clause.Fact(Atom.Functor("foo", List(Atom.Const("a")))),
    Clause.Fact(Atom.Functor("bar", List(Atom.Const("b")))),
    Clause.Forall(
      List("X"),
      Clause.Rule(
        Atom.Functor("foo", List(Atom.Const("X"))),
        List(Goal.GAtom(Atom.Functor("bar", List(Atom.Const("X")))))
      )
    )
  )
  val goal_1 = Goal.Forall(
    List("X"),
    Goal.Implication(
      cond = List(
        Clause.Forall(
          List("Y"),
          Clause.Fact(Atom.Functor("bar", List(Atom.Const("Y"))))
        )
      ),
      goal = Goal.GAtom(Atom.Functor("foo", List(Atom.Const("X"))))
    )
  )
  val goal_2 = Goal.Forall(
    List("a"),
    Goal.Exists(
      List("b"),
      Goal.Domain(DomainGoal.Eq(Atom.Const("a"), Atom.Const("b")))
    )
  )
  val goal_3 = Goal.Exists(
    List("a"),
    Goal.Forall(
      List("b"),
      Goal.Domain(DomainGoal.Eq(Atom.Const("a"), Atom.Const("b")))
    )
  )
  val goal_4 = Goal.Exists(
    List("a"),
    Goal.GAtom(Atom.Functor("foo", List(Atom.Const("a"))))
  )
  val machine = Machine(program)
  machine.solve(goal_4) match
    case None =>
      println("No solutions")
    case Some(solutions) if solutions.isEmpty =>
      println("Provable")
    case Some(solutions) =>
      println("Solutions:")
      for (solution <- solutions) do
        for ((k, v) <- solution) do println(k + " = " + v)
