module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine covering number of an open subscheme

The affine covering number `t(U)` of an open subscheme `U` of a scheme `X` is the least number
of affine opens needed to cover `U`.

## Main definitions

* `AlgebraicGeometry.minimalAffineCoverCardinality`: the affine covering number.

## Main results

* `AlgebraicGeometry.exists_fin_affine_cover_of_isCompact`: a quasi-compact open has a finite
  affine open cover.
* `AlgebraicGeometry.exists_affine_cover_card_eq`: the infimum defining the affine covering
  number of a quasi-compact open is attained.
* `AlgebraicGeometry.minimalAffineCoverCardinality_bot`: the affine covering number of the empty
  open is zero.
* `AlgebraicGeometry.minimalAffineCoverCardinality_top_le`: the affine covering number of an open
  subscheme, computed in the subscheme, is at most its affine covering number in the ambient
  scheme.

## Implementation notes

Finite covers are indexed by `Fin n`, and the covering number is the infimum of the set of such
`n`. If `U` has no finite affine open cover the infimum convention gives zero, so results about
the covering number assume `U` quasi-compact.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The least number of affine opens in a finite affine open cover of an open subscheme `U`,
and zero if `U` has no finite affine open cover. -/
noncomputable def minimalAffineCoverCardinality {X : Scheme.{u}} (U : X.Opens) : ℕ :=
  sInf {n : ℕ | ∃ V : Fin n → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ iSup V = U}

add_to_stacks 01XI "affine covering number" AlgebraicGeometry.minimalAffineCoverCardinality

/-- A quasi-compact open subscheme has a finite affine open cover indexed by a `Fin`. -/
theorem exists_fin_affine_cover_of_isCompact {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ n, ∃ V : Fin n → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ iSup V = U := by
  classical
  obtain ⟨Us, hUs, hUs_finite, hUs_sup⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact hU
  let _ : Fintype Us := hUs_finite.fintype
  let e := Fintype.equivFin Us
  refine ⟨Fintype.card Us, (fun i ↦ (e.symm i).val), fun i ↦ hUs (e.symm i).property, ?_⟩
  refine le_antisymm ?_ ?_
  · rw [hUs_sup, sSup_eq_iSup]
    exact iSup_le fun i ↦ le_iSup_of_le (e.symm i).val
      (le_iSup_of_le (e.symm i).property le_rfl)
  · rw [hUs_sup, sSup_eq_iSup]
    refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
    exact le_iSup_of_le (e ⟨V, hV⟩) (by simp)

/-- The infimum defining the affine covering number of a quasi-compact open subscheme is
attained: there is an affine open cover indexed by `Fin (t U)`. -/
theorem exists_affine_cover_card_eq {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ V : Fin (minimalAffineCoverCardinality U) → X.Opens,
      (∀ i, IsAffineOpen (V i)) ∧ iSup V = U :=
  Nat.sInf_mem (exists_fin_affine_cover_of_isCompact U hU)

/-- The affine covering number of the empty open subscheme is zero. -/
@[simp]
theorem minimalAffineCoverCardinality_bot (X : Scheme.{u}) :
    minimalAffineCoverCardinality (⊥ : X.Opens) = 0 :=
  Nat.eq_zero_of_le_zero
    (Nat.sInf_le ⟨Fin.elim0, fun i ↦ Fin.elim0 i, by simp⟩)

/-- The affine covering number of an open subscheme `U`, computed in `U` regarded as a scheme in
its own right, is at most the affine covering number of `U` in the ambient scheme. -/
theorem minimalAffineCoverCardinality_top_le {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    minimalAffineCoverCardinality (⊤ : (U : Scheme).Opens) ≤
      minimalAffineCoverCardinality U := by
  classical
  obtain ⟨V, hV, hVcover⟩ := exists_affine_cover_card_eq U hU
  have hVle (i : _) : V i ≤ (U.ι).opensRange := by
    rw [Scheme.Opens.opensRange_ι, ← hVcover]
    exact le_iSup V i
  refine Nat.sInf_le ⟨fun i ↦ U.ι ⁻¹ᵁ V i, fun i ↦ (hV i).preimage_of_isOpenImmersion _ (hVle i),
    ?_⟩
  rw [← Scheme.Hom.preimage_iSup, hVcover]
  simp

end AlgebraicGeometry

end
