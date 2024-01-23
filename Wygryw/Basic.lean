-- import Mathlib.Tactic.Find
-- import Mathlib.Tactic.LibrarySearch

inductive Player: Type 0 where
  | First: Player
  | Second: Player

@[simp] def Player.other: Player → Player
  | Player.First => Player.Second
  | Player.Second => Player.First

@[simp] def Player.beq : Player → Player → Bool
  | Player.First, Player.First => true
  | Player.Second, Player.Second => true
  | _, _ => false

@[simp] instance: BEq Player where
  beq := Player.beq

-- can reduce any deterministic game to this
-- note that finite by definition
-- TODO: prove the reduction
inductive BinaryGameTree: Type 0 where
  | FirstPlayerWins: BinaryGameTree
  | SecondPlayerWins: BinaryGameTree
  | PlayerDecision: Player → BinaryGameTree → BinaryGameTree → BinaryGameTree
  --| Draw -- TODO support drawable games

inductive SimpleMoveChoice
  | Left
  | Right

def Strategy := BinaryGameTree → BinaryGameTree → SimpleMoveChoice

def determineWinner (root: BinaryGameTree) (strategies: Player → Strategy ): Player :=
  match root with
  | BinaryGameTree.FirstPlayerWins => Player.First
  | BinaryGameTree.SecondPlayerWins => Player.Second
  | BinaryGameTree.PlayerDecision p a b =>
    match strategies p a b with
      | SimpleMoveChoice.Left => determineWinner a strategies
      | SimpleMoveChoice.Right => determineWinner b strategies

def hasWinningPath (p : Player) (b: BinaryGameTree): Bool :=
match b with
| BinaryGameTree.FirstPlayerWins => p == Player.First
| BinaryGameTree.SecondPlayerWins => p == Player.Second
| BinaryGameTree.PlayerDecision pp a b =>
  let wa := hasWinningPath pp a
  let wb := hasWinningPath pp b
  if pp == p then wa || wb else !(wa || wb)

def bestStrategy (player :Player) : Strategy := ( λ  (a: BinaryGameTree) (_ : BinaryGameTree) =>
  (if hasWinningPath player a then SimpleMoveChoice.Left else SimpleMoveChoice.Right))


theorem oneWinning game player : hasWinningPath player game = !hasWinningPath player.other game := by
  induction game
  case FirstPlayerWins =>
    cases player <;> simp [hasWinningPath]
  case SecondPlayerWins =>
    cases player <;> simp [hasWinningPath]
  case PlayerDecision decidingPlayer a b Ha Hb =>
    unfold hasWinningPath
    cases player <;> cases decidingPlayer <;> simp

theorem orFalse a b : (a || b) = false → a = false ∧ b = false := by
  intro H; constructor <;> revert H <;> cases a <;> cases b <;> simp

theorem winPathAnd p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p.other a b)):
  hasWinningPath p a ∧ hasWinningPath p b := by
  rw [hasWinningPath, Player.other] at H
  constructor <;> cases p <;>
  · simp at H
    rw [oneWinning]; simp
    have bothFalse := (orFalse _ _ H)
    first | apply bothFalse.left | apply bothFalse.right

theorem winPathOr p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p a b)):
  hasWinningPath p a ∨ hasWinningPath p b := by
  rw [hasWinningPath] at H
  cases p <;> simp at H <;> assumption

-- There should be a lemma for it, but proving is easier than searching :/
theorem orB a b (H: a = true ∨ b = true) (Ha : a = false) : b = true := by
  rw [Ha] at H; simp at H; exact H

-- Much copy-pasta, to simplify
theorem havingWinningPathWins game p (H: hasWinningPath p game) :
 ∃ strat, ∀ otherStrat, determineWinner game (λ l => if l == p then strat else otherStrat) = p := by
  exists bestStrategy p
  intro otherStrat
  induction game
  case FirstPlayerWins =>
    cases p
    · rw [determineWinner]
    · rw [hasWinningPath] at H; simp at H
  case SecondPlayerWins =>
    cases p
    · rw [hasWinningPath] at H; simp at H
    · rw [determineWinner]
  case PlayerDecision decicingPlayer pathA pathB Ha Hb  =>
    cases decicingPlayer
    · cases p
      · have winOr := winPathOr _ _ _ H
        rw [determineWinner]
        simp  [bestStrategy]
        generalize H: hasWinningPath Player.First pathA = firstCanWin
        cases firstCanWin <;> simp <;> conv =>
          rhs; first | rw [← Hb (orB _ _ winOr H)] | rw [← Ha H]
      · have winAnd := winPathAnd _ _ _ H
        rw [determineWinner]
        simp
        cases (otherStrat pathA pathB) <;> simp
        · conv => rhs; rw [← Ha winAnd.left ]
        · conv => rhs; rw [← Hb winAnd.right ]
    · cases p
      · have winAnd := winPathAnd _ _ _ H
        rw [determineWinner]
        simp
        cases (otherStrat pathA pathB) <;> simp
        · conv => rhs; rw [← Ha winAnd.left ]
        · conv => rhs; rw [← Hb winAnd.right ]
      · have winOr := winPathOr _ _ _ H
        rw [determineWinner]
        simp  [bestStrategy]
        generalize H: hasWinningPath Player.Second pathA = secondCanWin
        cases secondCanWin <;> simp <;> conv =>
          rhs; first | rw [← Hb (orB _ _ winOr H)] | rw [← Ha H]

theorem deterministicGamesHaveWinningStrategy (game: BinaryGameTree):
∃ p, ∃ sp, ∀ sop,
(determineWinner game (λ l => if l == p then sp else sop)) = p := by
  generalize H₁: hasWinningPath Player.First game = firstWins
  cases firstWins
  · have H₂ := oneWinning game Player.Second
    simp only [Player.other] at H₂; rw [H₁] at H₂; simp at H₂
    exists Player.Second
    apply havingWinningPathWins; assumption
  · exists Player.First
    apply havingWinningPathWins; assumption


--------------------
-- WIP part below
--------------------
inductive NextAction
 | NeedsToMove : Player → NextAction
 | GameOver : Player → NextAction

structure GameState (Board:Type) where
  board: Board
  nextAction: NextAction

structure Game (Board: Type) where
  initialState: GameState Board
  possibleMoves: GameState Board → List (GameState Board)

def finishState {B} (gs : GameState B) : Prop :=
  ∃ p, gs.nextAction = NextAction.GameOver p

inductive FiniteGameState {B} (game: Game B) : GameState B → Prop where
  | FinishedIsFinite: ∀ g : GameState B, finishState g → FiniteGameState game g
  | FiniteFutures : ∀ g: GameState B, ∀ next : GameState B,
      next ∈ game.possibleMoves g → FiniteGameState game next → FiniteGameState game g

def finiteGame {B} (g: Game B) : Prop := FiniteGameState g g.initialState

inductive ReachableGameState {B} (game: Game B) : GameState B → Prop where
  | InitialReachable: ReachableGameState game game.initialState
  | ReachableByMove: ∀ gs, ReachableGameState game gs →
    ∀ next, next ∈ game.possibleMoves gs → ReachableGameState game next

def playersHaveChoice {B} (game: Game B) : Prop :=
  ∀ gs: GameState B, ReachableGameState game gs →
  finishState gs ∨ (game.possibleMoves gs).length ≥ 2
