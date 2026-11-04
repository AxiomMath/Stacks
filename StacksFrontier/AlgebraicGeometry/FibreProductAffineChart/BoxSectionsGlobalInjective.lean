module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxSectionsAffinePair
public import StacksFrontier.LinearAlgebra.TensorProduct.FiniteJointInjective

/-!
# The global box-section comparison is injective

Let `k` be a field, let `a : X ⟶ Spec k` and `b : Y ⟶ Spec k` with `X` and `Y`
**quasi-compact**, and let `P` and `Q` be quasi-coherent. Then

`Γ(X, P) ⊗_k Γ(Y, Q) ⟶ Γ(X ×_k Y, P ⊠ Q)`

is injective.

Quasi-compactness is spent exactly once, and it is not a convenience. `X` and `Y` have *finite*
affine coverings `U i` and `V j`; the opens `pr₁⁻¹(U i) ⊓ pr₂⁻¹(V j)` cover `X ×_k Y`, over each
of them the comparison is bijective by
`AlgebraicGeometry.bijective_boxSectionMapOpens_of_isAffineOpen`, and the comparison is natural,
so an element of the kernel is killed by every `res ⊗ res`. For *finite* index types that forces
it to vanish — `TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective`, which runs through
`TensorProduct.piRight` — and for infinite ones the argument has no analogue.

## Main results

* `AlgebraicGeometry.exists_finite_isAffineOpen_iSup_eq_top`: a quasi-compact scheme has a finite
  affine covering.
* `AlgebraicGeometry.map_sectionsOverFieldRestrict_eq_zero_of_boxSectionMapOpens`: an element of
  `Γ(X, P) ⊗_k Γ(Y, Q)` which the comparison kills restricts to zero on every pair of affine
  opens.
* `AlgebraicGeometry.injective_globalBoxSectionMap_of_affineCovers`: **the comparison is
  injective**, given two finite affine coverings.
* `AlgebraicGeometry.injective_globalBoxSectionMap`: the same for `X` and `Y` quasi-compact.

## Implementation notes

The two flatness hypotheses of `TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective` are
discharged by instance search: over a field every module is free and so flat.

The covering is carried as two hypotheses rather than derived inside the injectivity argument, so
that a consumer which already has a preferred affine covering — a chart cover, say — can use it.
`AlgebraicGeometry.injective_globalBoxSectionMap` is the specialisation that derives one from
`CompactSpace`.

## References

* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open AlgebraicGeometry CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact scheme has a finite affine covering.** -/
theorem exists_finite_isAffineOpen_iSup_eq_top (X : Scheme.{u}) [CompactSpace X] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
  have hc : IsCompact (⊤ : X.Opens).carrier := by
    rw [show (⊤ : X.Opens).carrier = Set.univ from rfl]; exact isCompact_univ
  obtain ⟨s, hs, hsU⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp hc
  refine ⟨↥s, hs.to_subtype, fun i => ((i : X.affineOpens) : X.Opens),
    fun i => (i : X.affineOpens).2, Eq.trans ?_ hsU.symm⟩
  exact le_antisymm (iSup_le fun i => le_iSup₂_of_le (i : X.affineOpens) i.2 le_rfl)
    (iSup₂_le fun i hi => le_iSup_of_le ⟨i, hi⟩ le_rfl)

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (a : X ⟶ Spec (.of k))
  (b : Y ⟶ Spec (.of k)) (P : X.Modules) (Q : Y.Modules)
  [P.IsQuasicoherent] [Q.IsQuasicoherent]

/-- An element of `Γ(X, P) ⊗_k Γ(Y, Q)` which the comparison map kills restricts to zero in
`Γ(P, U) ⊗_k Γ(Q, V)` for every pair of affine opens. -/
theorem map_sectionsOverFieldRestrict_eq_zero_of_boxSectionMapOpens
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (z : TensorProduct k ↑(globalSectionsOverField k a P) ↑(globalSectionsOverField k b Q))
    (hz : globalBoxSectionMap k a b P Q z = 0) :
    TensorProduct.map (sectionsOverFieldRestrict k a P (le_top (a := U)))
      (sectionsOverFieldRestrict k b Q (le_top (a := V))) z = 0 := by
  refine (bijective_boxSectionMapOpens_of_isAffineOpen k a b P Q hU hV
    (W := pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V) rfl inf_le_left inf_le_right).1 ?_
  rw [map_zero, ← sectionsOverFieldRestrict_boxSectionMapOpens k a b P Q (le_top (a := U))
    (le_top (a := V)) (le_top (a := pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V))
    (boxTopFst k a b) (boxTopSnd k a b) inf_le_left inf_le_right z]
  exact congrArg _ hz |>.trans (map_zero _)

/-- **The global box-section comparison is injective**, given a finite affine covering of each
factor. -/
theorem injective_globalBoxSectionMap_of_affineCovers {I J : Type*} [Finite I] [Finite J]
    {U : I → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hUcov : ⨆ i, U i = ⊤)
    {V : J → Y.Opens} (hV : ∀ j, IsAffineOpen (V j)) (hVcov : ⨆ j, V j = ⊤) :
    Function.Injective (globalBoxSectionMap k a b P Q) := by
  intro z z' h
  rw [← sub_eq_zero]
  refine TensorProduct.eq_zero_of_map_eq_zero_of_jointly_injective
    (fun i => sectionsOverFieldRestrict k a P (le_top (a := U i)))
    (fun j => sectionsOverFieldRestrict k b Q (le_top (a := V j)))
    (fun x hx => eq_zero_of_sectionsOverFieldRestrict_eq_zero k a P hUcov x hx)
    (fun y hy => eq_zero_of_sectionsOverFieldRestrict_eq_zero k b Q hVcov y hy) (z - z')
    fun i j => ?_
  exact map_sectionsOverFieldRestrict_eq_zero_of_boxSectionMapOpens k a b P Q (hU i) (hV j)
    (z - z') (by rw [map_sub, h, sub_self])

/-- **The global box-section comparison is injective** for `X` and `Y` quasi-compact. -/
theorem injective_globalBoxSectionMap [CompactSpace X] [CompactSpace Y] :
    Function.Injective (globalBoxSectionMap k a b P Q) := by
  obtain ⟨I, hI, U, hU, hUcov⟩ := exists_finite_isAffineOpen_iSup_eq_top X
  obtain ⟨J, hJ, V, hV, hVcov⟩ := exists_finite_isAffineOpen_iSup_eq_top Y
  exact injective_globalBoxSectionMap_of_affineCovers k a b P Q hU hUcov hV hVcov

end AlgebraicGeometry

end
