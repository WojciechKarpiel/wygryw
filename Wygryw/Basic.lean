-- import Mathlib.Tactic.Find
-- import Mathlib.Tactic.LibrarySearch

-- #find _ + _ = _ + _
-- #find (_ : ℕ) + _ = _ + _
-- #find ℕ → ℕ
-- #find (_ : nat) + _ = _ + _
-- #find _ + _ = _ + _
-- #find _ (_ + _) → _ + _ = _ + _   -- TODO(Mario): no results
-- #find add_group _ → _ + _ = _ + _ -- TODO(Mario): no results
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

theorem havingWinningPathWins gaem p (H: hasWinningPath p gaem) :
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
  case PlayerDecision dpl da db Ha Hb  =>
    cases dpl
    · cases p
      · have xDD :=winPathOr _ _ _ H
        induction xDD
        case inl xd =>
          have Hh := Ha xd
          -- rewrite [← Hh]
          rw [determineWinner]
          simp  [BEq.beq, Player.beq]
          simp [bestStrategy, xd]
          conv =>
            rhs
            rw [←Hh ]
        case inr xd =>
          have Hh := Hb xd
          rw [determineWinner]
          simp  [BEq.beq, Player.beq]
          -- have notFirst := oneWinning  da Player.First
          simp [bestStrategy]
          --have Hq : (hasWinningPath Player.First da) = (hasWinningPath Player.First da) := by rfl
          --revert Hq
          generalize H: hasWinningPath Player.First da = ddd
          cases ddd
          simp
          conv =>
            rhs
            rw [←Hh ]
          simp
          conv =>
            rhs
            rw [← Ha H ]
      · have xDD :=winPathAnd _ _ _ H
        have XDa := xDD.left
        have XDb := xDD.right
        rw [determineWinner]
        simp  [BEq.beq, Player.beq]
        cases (otherStrat da db)
        · simp
          conv =>
            rhs
            rw [← Ha XDa ]
        · simp
          conv =>
            rhs
            rw [← Hb XDb ]
    · cases p
      · have xDD :=winPathAnd _ _ _ H
        have XDa := xDD.left
        have XDb := xDD.right
        rw [determineWinner]
        simp  [BEq.beq, Player.beq]
        cases (otherStrat da db)
        · simp
          conv =>
            rhs
            rw [← Ha XDa ]
        · simp
          conv =>
            rhs
            rw [← Hb XDb ]
      · induction winPathOr _ _ _ H
        · case inl xD  =>
          rw [determineWinner]
          simp  [BEq.beq, Player.beq]
          rw [bestStrategy, xD]
          simp
          conv =>
            rhs
            rw [← Ha xD ]
        · case inr xD  =>
          rw [determineWinner]
          simp  [BEq.beq, Player.beq]
          rw [bestStrategy]
          generalize H: hasWinningPath Player.Second da = ddd
          cases ddd
          · simp
            conv =>
              rhs
              rw [← Hb xD ]
          · simp
            conv =>
              rhs
              rw [← Ha H ]

theorem deterministicGamesHaveWinningStrategy (game: BinaryGameTree):
∃ p, ∃ sp, ∀ sop,
(determineWinner game (λ l => if l == p then sp else sop)) = p := by
  generalize H₁: hasWinningPath Player.First game = firstWins
  cases firstWins
  · have H₂ := oneWinning game Player.Second
    simp only [Player.other] at H₂; rw [H₁] at H₂; simp at H₂
    exists Player.Second
    apply havingWinningPathWins
    simp only [H₂]
  · exists Player.First
    apply havingWinningPathWins
    simp only [H₁]
