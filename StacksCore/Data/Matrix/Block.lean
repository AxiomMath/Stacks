module

public import Mathlib.Data.Matrix.Block
public import StacksCore.Logic.Equiv.Defs

/-! # Block diagonal matrices -/

@[expose] public section

/-- The `i`-th square block (along the second-projection partition) of `blockDiagonal M`
is `M i`, reindexed by `equivSndEq m i` on each side. -/
@[simp] theorem Matrix.toSquareBlock_blockDiagonal
    {m o R : Type*} [DecidableEq o] [Zero R] (M : o → Matrix m m R) (i : o) :
    (blockDiagonal M).toSquareBlock Prod.snd i =
      (M i).reindex (equivSndEq m i) (equivSndEq m i) := ext fun p q ↦ by
  simp [Matrix.toSquareBlock_def, blockDiagonal_apply, p.2, q.2]
