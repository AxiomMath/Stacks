module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import StacksCore.Tactic.StacksAttribute

/-! # Adjoining elements inside a field extension -/

@[expose] public section

add_to_stacks 09FZ "finitely generated field extension: correctness" IntermediateField.fg_top_iff

open IntermediateField

theorem IntermediateField.iSup_toSubalgebra_of_isAlgebraic
    {K L ι : Type*} [Finite ι] [Field K] [Field L] [Algebra K L]
    {E : ι → IntermediateField K L} [hE : ∀ i, Algebra.IsAlgebraic K (E i)] :
    (⨆ i, E i).toSubalgebra = ⨆ i, (E i).toSubalgebra := by
  classical
  have := Fintype.ofFinite ι
  simp_rw [← Finset.sup_univ_eq_iSup]
  generalize Finset.univ (α := ι) = s
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ _ ih => simp [sup_toSubalgebra_of_isAlgebraic_left, ih]
