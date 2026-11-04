module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafBaseChangeAffine

/-!
# Tag 0E7K: flatness of `f_* 𝒪_X` and the commutation of its formation with base change

Let `X ⟶ Y ⟶ S` be a commutative triangle of schemes with `X ⟶ S` flat, `f : X ⟶ Y` proper,
`dim(X_y) ≤ 1` for every `y ∈ Y` and `R¹ f_* 𝒪_X = 0`. [Stacks, Tag 0E7K] asserts

* (a) `f_* 𝒪_X` is flat over `S`, and
* (b) formation of `f_* 𝒪_X` commutes with arbitrary base change `S' ⟶ S`.

Both are proved here with no hypothesis beyond the source's.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isFlatOver_directImageStructureSheaf_of_fibreDimension_le_one`: **clause (a)**.
* `isIso_baseChangeNatTrans_structureSheaf_of_flat`: for a cartesian square `X' ⟶ X` over
  `Y' ⟶ Y` whose lower edge is itself the base change of `Y ⟶ S` along some `S' ⟶ S`, the
  canonical comparison `g^* f_* 𝒪_X ⟶ f'_* (g')^* 𝒪_X` is an isomorphism.
* `isIso_directImageStructureSheafBaseChangeMap_of_flat`: **clause (b)**, at the comparison
  `directImageStructureSheafBaseChangeMap` of `StructureSheafSurjectivityBaseChange.lean`, for
  `Y' = Y ×_S S'`.

## Proof

Clause (a) is `isFlatOver_directImageStructureSheaf` of `DirectImageStructureSheafFlat.lean`
with its vanishing input discharged by [Stacks, Tag 0E7D] at `d = 1`
(`cohomologyVanishesAboveOne` of `ProperFibreDimensionVanishing.lean`).

For clause (b) the source's proof is followed. The assertion is local on `Y'`
(`AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cover`), and `Y'` is covered by the opens
`V ×_W W'` with `V ⊆ Y`, `W ⊆ S`, `W' ⊆ S'` affine, `V` over `W` and `W'` over `W`. Over such an
open the square restricts to a square of the same shape with all four lower corners affine, and
there `isIso_baseChangeNatTrans_structureSheaf_of_affine` (`StructureSheafBaseChangeAffine.lean`)
applies; its vanishing input, `H¹(f⁻¹V, -) = 0` on globally generated quasi-coherent modules, is
clause (4) of [Stacks, Tag 0E7H] for `f ∣_ V`, which needs `H¹(f⁻¹V, 𝒪) = 0` (from
`R¹ f_* 𝒪_X = 0`) and [Stacks, Tag 0E7D] at `d = 1`.

## References

* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **The commutation of the formation of `f_* 𝒪_X` with base change, for a cartesian square
over a base change of `Y ⟶ S`.** Let
```
X' --g'--> X
|f'        |f
Y' --g---> Y
|q'        |q
S' --h---> S
```
be two cartesian squares with `X ⟶ S` flat, `f` proper, `dim(X_y) ≤ 1` for `y ∈ Y` and
`R¹ f_* 𝒪_X = 0`. Then `g^* f_* 𝒪_X ⟶ f'_* (g')^* 𝒪_X` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_structureSheaf_of_flat {X Y S X' Y' S' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (hw : IsPullback g' f' f g)
    {q' : Y' ⟶ S'} {q : Y ⟶ S} {h : S' ⟶ S} (hY : IsPullback g q' q h)
    [Flat (f ≫ q)] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    IsIso ((AffinePushforward.baseChangeNatTrans hw.w).app (Scheme.unitModule X)) := by
  let I := {d : Y.Opens × S.Opens × S'.Opens // IsAffineOpen d.1 ∧ IsAffineOpen d.2.1 ∧
    IsAffineOpen d.2.2 ∧ d.1 ≤ q ⁻¹ᵁ d.2.1 ∧ d.2.2 ≤ h ⁻¹ᵁ d.2.1}
  let U : I → Y'.Opens := fun i => g ⁻¹ᵁ i.1.1 ⊓ q' ⁻¹ᵁ i.1.2.2
  have hU : IsOpenCover U := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨W, hW, hmW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show q (g y) ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hmV, hVW⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show g y ∈ q ⁻¹ᵁ W from hmW)
    have hhq : h (q' y) = q (g y) := by
      rw [← Scheme.Hom.comp_apply, ← hY.w, Scheme.Hom.comp_apply]
    obtain ⟨W', hW', hmW', hW'W⟩ := Opens.isBasis_iff_nbhd.mp S'.isBasis_affineOpens
      (show q' y ∈ h ⁻¹ᵁ W from by simpa [hhq] using hmW)
    exact Opens.mem_iSup.mpr
      ⟨⟨(V, W, W'), hV, hW, hW', hVW, hW'W⟩, ⟨hmV, hmW'⟩⟩
  refine AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cover hw.w _ U hU fun i => ?_
  obtain ⟨⟨V, W, W'⟩, hV, hW, hW', hVW, hW'W⟩ := i
  have hle : g ⁻¹ᵁ V ⊓ q' ⁻¹ᵁ W' ≤ g ⁻¹ᵁ V := inf_le_left
  refine AffineBaseChangeIso.isIso_baseChangeNatTrans_comp_restrictSquare hw _ hle ?_
  refine isIso_app_of_iso _ (Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ V).ι) ?_
  have hY₀ := Scheme.Hom.isPullback_resLE hY (US := W) (UT := W') (UX := V) hW'W hVW
    (UY := g ⁻¹ᵁ V ⊓ q' ⁻¹ᵁ W') rfl
  have : IsAffine (V : Scheme.{u}) := hV
  have : IsAffine (W : Scheme.{u}) := hW
  have : IsAffine (W' : Scheme.{u}) := hW'
  have : IsAffine ((g ⁻¹ᵁ V ⊓ q' ⁻¹ᵁ W' : Y'.Opens) : Scheme.{u}) :=
    IsAffine.of_isIso hY₀.isoPullback.hom
  have hcomp : (f ∣_ V) ≫ q.resLE W V hVW = (f ≫ q).resLE W (f ⁻¹ᵁ V)
      ((f.preimage_mono hVW).trans_eq (Scheme.Hom.comp_preimage f q W).symm) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
  have : Flat ((f ∣_ V) ≫ q.resLE W V hVW) := by
    rw [hcomp]
    infer_instance
  exact isIso_baseChangeNatTrans_structureSheaf_of_affine
      (AffineBaseChangeIso.innerIsPullback hw hle) hY₀ fun G hG σ =>
    have := hG
    isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one
      cohomologyVanishesAboveOne (f ∣_ V)
      (topologicalKrullDim_fiber_morphismRestrict_le f V 1 fun y _ => hdim y)
      (isZero_firstCohomology_preimage_of_isZero_firstDirectImage f V hR) G σ

/-- **[Stacks, Tag 0E7K], clause (b).** Let `X ⟶ Y ⟶ S` be a commutative triangle of schemes with
`X ⟶ S` flat, let `f : X ⟶ Y` be proper with `dim(X_y) ≤ 1` for every `y ∈ Y`, and suppose
`R¹ f_* 𝒪_X = 0`. Then formation of `f_* 𝒪_X` commutes with arbitrary base change `S' ⟶ S`:
for `Y' = Y ×_S S'` and `X' = X ×_Y Y'`, the canonical comparison
`(Y' ⟶ Y)^* f_* 𝒪_X ⟶ f'_* 𝒪_{X'}` is an isomorphism. -/
@[stacks 0E7K "clause (b): formation of f_* 𝒪_X commutes with arbitrary base change S' ⟶ S"]
theorem isIso_directImageStructureSheafBaseChangeMap_of_flat {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (q : Y ⟶ S) [Flat (f ≫ q)] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) {S' : Scheme.{u}} (h : S' ⟶ S) :
    IsIso (directImageStructureSheafBaseChangeMap f (pullback.fst q h)) :=
  (isIso_directImageStructureSheafBaseChangeMap_iff f (pullback.fst q h)).mpr
    (isIso_baseChangeNatTrans_structureSheaf_of_flat (IsPullback.of_hasPullback f _)
      (IsPullback.of_hasPullback q h) hdim hR)

/-- **[Stacks, Tag 0E7K], clause (a).** Let `X ⟶ Y ⟶ S` be a commutative triangle of schemes with
`X ⟶ S` flat, let `f : X ⟶ Y` be proper with `dim(X_y) ≤ 1` for every `y ∈ Y`, and suppose
`R¹ f_* 𝒪_X = 0`. Then `f_* 𝒪_X` is flat over `S`. -/
@[stacks 0E7K "clause (a): f_* 𝒪_X is flat over S"]
theorem isFlatOver_directImageStructureSheaf_of_fibreDimension_le_one {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ S) [Flat (f ≫ q)] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    IsFlatOver q.toLRSHom.toShHom (directImageStructureSheaf f) :=
  isFlatOver_directImageStructureSheaf cohomologyVanishesAboveOne f q hdim hR

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
