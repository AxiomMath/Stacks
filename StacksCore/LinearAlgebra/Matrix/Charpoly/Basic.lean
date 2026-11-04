module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import StacksCore.Data.Matrix.Block
import StacksCore.Tactic.StacksAttribute

/-! # Characteristic polynomials -/

add_to_stacks 00DX Matrix.aeval_self_charpoly

@[expose] public section

/-- The characteristic polynomial of a block diagonal matrix is the product of the
characteristic polynomials of its blocks. -/
@[simp] theorem Matrix.charpoly_blockDiagonal
    {m o R : Type*} [Fintype o] [DecidableEq o] [Fintype m] [DecidableEq m]
    [CommRing R] (M : o → Matrix m m R) :
    (blockDiagonal M).charpoly = ∏ i : o, (M i).charpoly := by
  obtain ⟨_, _⟩ := exists_wellFoundedLT o
  obtain _ | _ := isEmpty_or_nonempty m
  · simp
  simp [(blockTriangular_blockDiagonal _).charpoly,
    Finset.image_univ_of_surjective Prod.snd_surjective, -reindex_apply, charpoly_reindex]
