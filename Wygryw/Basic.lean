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
def strategy := List BinaryGameTree -> BinaryGameTree → BinaryGameTree → SimpleMoveChoice


def determineWinnerQ (root: BinaryGameTree)
(strategy1 : strategy)
(stratefy2 : strategy)
(trace: List BinaryGameTree) : Player :=  match root with
  | BinaryGameTree.FirstPlayerWins => Player.First
  | BinaryGameTree.SecondPlayerWins => Player.Second
  | BinaryGameTree.PlayerDecision p a b =>
    let s := match p with
      | Player.First => strategy1
      | Player.Second => stratefy2
    let newn := root :: trace
    let move := s trace a b
    match move with
      | SimpleMoveChoice.Left => determineWinnerQ a strategy1 stratefy2 newn
      | SimpleMoveChoice.Right => determineWinnerQ b strategy1 stratefy2 newn


def wins (p : Player) (b: BinaryGameTree): Bool :=
match b with
| BinaryGameTree.FirstPlayerWins => p == Player.First
| BinaryGameTree.SecondPlayerWins => p == Player.Second
| BinaryGameTree.PlayerDecision pp a b =>
  let wa := wins pp a
  let wb := wins pp b
  if pp == p then wa || wb else !(wa || wb)
def bestMove (player :Player) : strategy := λ _ a _ =>
  if wins player a then SimpleMoveChoice.Left else SimpleMoveChoice.Right

-- now prove that bestmove strategy always works for one og the players
