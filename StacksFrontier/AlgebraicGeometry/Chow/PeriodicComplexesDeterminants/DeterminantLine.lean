module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension

/-!
# Generators of the determinant line

The determinant of a finite-length module over a local ring is a one-dimensional vector space
over the residue field. This file collects the consequences of that fact used throughout the
theory of periodic determinants: a finite-length module always has an admissible sequence with
nonzero symbol, a symbol is nonzero exactly when its sequence spans, and a self-equivalence of
a one-dimensional space is multiplication by its determinant.

## Main results

* `AlgebraicGeometry.exists_nonzero_symbol`: some admissible sequence has a nonzero symbol.
* `AlgebraicGeometry.symbol_ne_zero_of_span_eq_top` and
  `AlgebraicGeometry.symbol_ne_zero_of_span_top`: two criteria for a symbol to be nonzero.
* `AlgebraicGeometry.exists_spanning_symbol`: some admissible sequence both spans and has a
  nonzero symbol.
* `AlgebraicGeometry.linearEquiv_eq_det_smul_id`: a self-equivalence of a one-dimensional
  vector space is its determinant times the identity.

## Implementation notes

The converse of `AlgebraicGeometry.symbol_ne_zero_of_span_top` is
`Module.FiniteLength.span_eq_top_of_symbol_ne_zero`; the two together say that a symbol
vanishes exactly when its sequence fails to span.

## References

* [Stacks Project, Tag 02P9](https://stacks.math.columbia.edu/tag/02P9)
-/

@[expose] public section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

/-- An admissible sequence whose symbol generates the determinant line has nonzero symbol. -/
theorem symbol_ne_zero_of_span_eq_top (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M)
    (h : (IsLocalRing.ResidueField R) ∙ symbol e = ⊤) : symbol e ≠ 0 := by
  intro hzero
  have hbot : (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R M)) = ⊤ := by
    simpa [hzero] using h
  have hfin := finrank_determinant_eq_one hM
  let : Module.Finite (IsLocalRing.ResidueField R) (determinant R M) :=
    Module.finite_of_finrank_eq_succ hfin
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hfin]; norm_num)
  apply hz
  have hzbot : z ∈ (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R M)) := by
    rw [hbot]
    exact Submodule.mem_top
  simpa using hzbot

/-- An admissible sequence that spans has nonzero symbol. -/
theorem symbol_ne_zero_of_span_top (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M)
    (he : Submodule.span R (Set.range e.1) = ⊤) : symbol e ≠ 0 :=
  symbol_ne_zero_of_span_eq_top hM e (span_symbol_eq_top hM e he)

/-- A finite-length module has an admissible sequence with nonzero symbol. -/
theorem exists_nonzero_symbol (hM : IsFiniteLength R M) :
    ∃ e : AdmissibleSequence R M, symbol e ≠ 0 := by
  by_contra h
  push Not at h
  have hfin := finrank_determinant_eq_one hM
  let : Module.Finite (IsLocalRing.ResidueField R) (determinant R M) :=
    Module.finite_of_finrank_eq_succ hfin
  let : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_pos (by rw [hfin]; norm_num)
  have hall : ∀ e : AdmissibleSequence R M,
      symbol e ∈ (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R M)) := by
    intro e
    rw [h e]
    exact Submodule.zero_mem _
  exact bot_ne_top (eq_top_of_symbols_mem ⊥ hall)

/-- A finite-length module has an admissible sequence that spans and has nonzero symbol. -/
theorem exists_spanning_symbol (hM : IsFiniteLength R M) :
    ∃ e : AdmissibleSequence R M,
      symbol e ≠ 0 ∧ Submodule.span R (Set.range e.1) = ⊤ := by
  obtain ⟨e, he⟩ := exists_nonzero_symbol hM
  exact ⟨e, he, span_eq_top_of_symbol_ne_zero hM e he⟩

/-- A self-equivalence of a one-dimensional vector space is its determinant times the
identity. -/
theorem linearEquiv_eq_det_smul_id
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 1) (f : V ≃ₗ[K] V) :
    f.toLinearMap = (f.det : K) • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hV f.toLinearMap
  have hdet : (f.det : K) = c := by
    rw [LinearEquiv.coe_det, hc, LinearMap.det_smul, LinearMap.det_id, hV]
    simp
  rw [hc, hdet]

end AlgebraicGeometry
