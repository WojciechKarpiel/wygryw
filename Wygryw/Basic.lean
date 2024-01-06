-- import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch

-- doesn't work?
-- #find _ || _

inductive Player: Type 0 where
  | First: Player
  | Second: Player

def Player.beq : Player → Player → Bool
  | Player.First, Player.First => true
  | Player.Second, Player.Second => true
  | _, _ => false

def Player.other : Player →Player
  | Player.First => Player.Second
  | Player.Second => Player.First

instance: BEq Player where
  beq := Player.beq

-- can reduce any deterministic game to this
-- note that finite by definition
-- TODO: prove the reduction
inductive BinaryGameTree: Type 0 where
  | FirstPlayerWins: BinaryGameTree
  | SecondPlayerWins: BinaryGameTree
  | PlayerDecision: Player → BinaryGameTree → BinaryGameTree → BinaryGameTree
  --| Draw

def height : BinaryGameTree → Nat
  | BinaryGameTree.FirstPlayerWins => 0
  | BinaryGameTree.SecondPlayerWins => 0
  | BinaryGameTree.PlayerDecision _ a b => (max (height a) (height b))+1

-- define trace ofgame and then strategy for the tree

--trace:
-- initial board state
-- next state + proof that it's a child of prev

inductive SimpleMoveChoice
  | Left
  | Right

-- moves so far, choice L, choice R
def Strategy := /- List BinaryGameTree -> -/ BinaryGameTree → BinaryGameTree → SimpleMoveChoice


def determineWinner (root: BinaryGameTree)
(strategies: Player → Strategy )
-- (trace: List BinaryGameTree)
 : Player :=  match root with
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
    cases player -- todo how to dedup, mechanism like Coq?
    · simp [Player.other, hasWinningPath, BEq.beq, Player.beq]
    · simp [Player.other, hasWinningPath, BEq.beq, Player.beq]
  case SecondPlayerWins => -- todo how to dedup, mechanism like Coq?
    cases player
    · simp [Player.other, hasWinningPath, BEq.beq, Player.beq]
    · simp [Player.other, hasWinningPath, BEq.beq, Player.beq]
  case PlayerDecision decidingPlayer a b Ha Hb =>
    unfold hasWinningPath
    cases player -- TODO DEDUP!!!!!!!!!!!!!!!!!
    · cases decidingPlayer
      . simp [Player.other, BEq.beq, Player.beq]
      . simp [Player.other, BEq.beq, Player.beq]
    · cases decidingPlayer
      . simp [Player.other, BEq.beq, Player.beq]
      . simp [Player.other, BEq.beq, Player.beq]

theorem wtfICantFindLemmaForIt a b : (a || b) = false → a = false := by
  cases a
  cases b -- todo how to dedup this thing like in coq
  simp
  simp
  simp

theorem wtfICantFindLemmaForIt2 a b : (a || b) = false → b = false := by
  cases a
  cases b -- todo how to dedup this thing like in coq
  simp
  simp
  simp

theorem winPathAnd1 p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p.other a b)):
  hasWinningPath p a := by
  rw [hasWinningPath, Player.other] at H
  cases p
  · simp at H
    simp only [BEq.beq, Player.beq] at H
    simp at H
    rw [oneWinning]
    simp
    revert H
    apply wtfICantFindLemmaForIt
  · simp at H -- TODO how to run this twice no copy-paste?
    simp only [BEq.beq, Player.beq] at H
    simp at H
    rw [oneWinning]
    simp
    revert H
    apply wtfICantFindLemmaForIt

theorem winPathAnd2 p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p.other a b)):
  hasWinningPath p b := by
  rw [hasWinningPath, Player.other] at H
  cases p
  · simp at H
    simp only [BEq.beq, Player.beq] at H
    simp at H
    rw [oneWinning]
    simp
    revert H
    apply wtfICantFindLemmaForIt2
  · simp at H -- TODO how to run this twice no copy-paste?
    simp only [BEq.beq, Player.beq] at H
    simp at H
    rw [oneWinning]
    simp
    revert H
    apply wtfICantFindLemmaForIt2

theorem winPathAnd p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p.other a b)):
  hasWinningPath p a ∧ hasWinningPath p b := by
  -- refine Iff.mpr (Bool.and_eq_true_iff (hasWinningPath p a) (hasWinningPath p b)) ?_
  constructor
  exact winPathAnd1 p a b H
  exact winPathAnd2 p a b H

theorem winPathOr p a b
  (H : hasWinningPath p (BinaryGameTree.PlayerDecision p a b)):
  hasWinningPath p a ∨ hasWinningPath p b := by
  rw [hasWinningPath] at H
  cases p
  · simp [BEq.beq, Player.beq] at H
    exact H
  · simp [BEq.beq, Player.beq] at H
    exact H

theorem bbbb gaem p (H: hasWinningPath p gaem) :
 ∃ strat, ∀ otherStrat, determineWinner gaem (λ l => if l == p then strat else otherStrat) = p := by
  exists bestStrategy p
  intro otherStrat
  induction gaem
  case FirstPlayerWins =>
    cases p
    · rw [determineWinner]
    · rw [hasWinningPath] at H
      simp only [BEq.beq, Player.beq] at H
  case SecondPlayerWins =>
    cases p
    · rw [hasWinningPath] at H
      simp only [BEq.beq, Player.beq] at H
    · rw [determineWinner]
  case PlayerDecision dpl da ab Ha Hb  =>
    cases dpl
    · cases p
      ·
    sorry
-- def moveD nextPlayer nextA nextB adv trc : determineWinnerQ
--  (BinaryGameTree.PlayerDecision nextPlayer nextA nextB) (bestMove winner) adv trc =

-- thm DET_OR w(DXab)=X => Wa=A or WB = X
-- thm Codet_OR w(DYab)=X => Wa=X and AB=X

-- THM: If straregy A wins, then bestStrategy wins too

-- theorem bestStrategyisbest1 game str1 str2 (H: (determineWinner game str1 str2) = Player.First):
  -- determineWinner game (bestMove Player.First) str2 = Player.First := by


-- THM : has winning path -> has winning strategy

-- now prove that bestmove strategy always works for one og the players
theorem thmGTT (game: BinaryGameTree) : ∃ p, ∃ sp, ∀ sop, (determineWinner game sp sop) = p := by
  let best1 := bestStrategy Player.First
  let best2 := bestStrategy Player.Second
  let winner := determineWinner game best1 best2
  exists winner
  exists bestMove winner
  intro adverstaryStrategy
  induction game
  case FirstPlayerWins => rfl
  case SecondPlayerWins => rfl
  case PlayerDecision nextP nextA nextB hA hB =>
    rw [determineWinner]
    cases nextP
    case First =>
      simp
        -- rw [hA]
      sorry
    case Second => sorry
