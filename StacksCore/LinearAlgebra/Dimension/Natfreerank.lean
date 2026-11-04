module

public import Mathlib.LinearAlgebra.Dimension.Free

/-! The free rank of a module -/

@[expose] public section

namespace Module

/-- The natural-number-valued free rank of an `R`-module `M`: the least `n : ℕ` such that
`M` admits a basis indexed by `Fin n`, or `0` if no such `n` exists. Unlike `Module.finrank`,
this is defined directly from the existence of a finite basis without going through cardinals,
and agrees with `Module.finrank` whenever `M` is free of finite type over a ring with the
strong rank condition. -/
noncomputable def natfreerank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  open scoped Classical in
  if h : ∃ n : ℕ, Nonempty (Basis (Fin n) R M) then Nat.find h else 0

/-- The natural free rank of a subsingleton module is `0`, witnessed by the empty basis. -/
@[simp] theorem natfreerank_of_subsingleton (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [Subsingleton M] : natfreerank R M = 0 := by
  classical rw [natfreerank, dite_eq_left ⟨0, ⟨Basis.empty _⟩⟩, Nat.find_eq_zero]
  exact ⟨Basis.empty _⟩

/-- The natural free rank of any module over a subsingleton (i.e. trivial) ring is `0`. -/
@[simp] theorem natfreerank_of_subsingleton' (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [Subsingleton R] : natfreerank R M = 0 :=
  have := MulActionWithZero.subsingleton R M
  natfreerank_of_subsingleton R M

/-- The natural free rank is bounded above by the cardinal-valued `Module.rank`: the basis
witnessing `natfreerank` is in particular a linearly independent family. -/
theorem natfreerank_le_rank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    natfreerank R M ≤ Module.rank R M := by
  nontriviality R
  rw [natfreerank]
  split_ifs with h
  · classical
    obtain ⟨e⟩ := Nat.find_spec h
    exact Module.le_rank_iff.mpr ⟨_, e.linearIndependent⟩
  · simp

/-- For a free module of finite type, a basis indexed by `Fin (natfreerank R M)`. Compared to
`Module.finBasis`, this version is indexed by the `ℕ`-valued `natfreerank` rather than the
`finrank`, and so is available without the strong rank condition on `R`. -/
noncomputable def finBasis' (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Free R M] [Module.Finite R M] : Basis (Fin (natfreerank R M)) R M := by
  refine Nonempty.some ?_
  have b := Module.Free.chooseBasis R M
  have e := Fintype.equivFin (Free.ChooseBasisIndex R M)
  rw [natfreerank, dite_eq_left ⟨_, ⟨b.reindex e⟩⟩]
  generalize_proofs h
  classical exact Nat.find_spec h

/-- For a free module of finite type over a ring satisfying the strong rank condition, the
natural-number-valued `natfreerank` agrees with `Module.finrank`. -/
@[simp] theorem natfreerank_eq_finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Free R M] [Module.Finite R M] [StrongRankCondition R] : natfreerank R M = finrank R M := by
  simpa using Fintype.card_congr ((finBasis' R M).indexEquiv (finBasis R M))

end Module
