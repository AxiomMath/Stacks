module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageCoefficientMap
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquaresProof
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceOfStepSquares
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceVanishing
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.CategoryTheory.Shift.ShiftSequenceCommShift

/-!
# The first page of 0FMM in the flat case, through the shift of the derived direct image

Let `f : X ⟶ Y` be quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, with flat de Rham
cohomology sheaves `ℋ^q_dR(X/Y)`. The remark [Stacks, Tag 0FMN] identifies the first page of the
spectral sequence of [Stacks, Tag 0FMM] with `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`. This file constructs
that identification, with the shift `[-p]` of the graded piece
`gr^pΩ^•_{X/S} = f^{-1}Ω^p_{Y/S}[-p] ⊗ Ω^•_{X/Y}` read through the shift of the unbounded derived
direct image `Rf_*`. The unshifted part is the comparison
`M ⊗ ℋ^q_dR(X/Y) ≅ R^qf_*(f^{-1}M ⊗ Ω^•_{X/Y})` for an arbitrary `𝒪_Y`-module `M`, given by
conclusion (4) of [Stacks, Tag 0FML] and a change of coefficients.

## Main definitions

* `Stacks.DeRhamSmooth.coefficientFirstPageMapZero`: `M ⊗ ℋ^q ⟶ R^qf_*(f^{-1}M ⊗ Ω^•_{X/Y})`,
  for every `M`; an isomorphism `coefficientFirstPageIsoZero` for quasi-coherent `M`.
* `Stacks.DeRhamSmooth.coefficientFirstPageShiftMap`:
  `M ⊗ ℋ^q ⟶ R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`; an isomorphism
  `coefficientFirstPageShiftIso` for quasi-coherent `M`.
* `Stacks.DeRhamSmooth.higherDirectImageGradedPieceFlatIso`: **the first page in the flat case**,
  `R^{p + q}f_*gr^pΩ^•_{X/S} ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`.

## Main results

* `Stacks.DeRhamSmooth.coefficientFirstPageMapZero_naturality` and
  `Stacks.DeRhamSmooth.coefficientFirstPageShiftMap_naturality`: both comparisons are natural in
  the module `M`.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
-- `hasSheafifyOpensMax` leaves its second universe undetermined; once the flatness hypothesis is
-- in context, instance search picks it for `Y` and the kernel rejects the resulting term.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The unbounded derived direct image along `relativeBase` of the change of coefficients of a
complex of `f^{-1}𝒪_Y`-modules. -/
abbrev coefficientDerivedDirectImage :
    CochainComplex (Modules (inverseImageBase f)) ℤ ⥤
      DerivedCategory (Modules (inverseImageBase g)) :=
  (coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
    derivedRelativePushforward f g

/-! ### The comparison with an arbitrary coefficient module, through the shift -/

section Comparison

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]
  (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q))

/-- **The unshifted first-page comparison with an arbitrary coefficient module**:
`M ⊗_{𝒪_Y} ℋ^q_dR(X/Y) ⟶ R^qf_*(f^{-1}M ⊗ Ω^•_{X/Y})`, read over `g^{-1}𝒪_S`: the degeneration
of the derived tensor product with flat cohomology (`flatDegenerateDerivedTensor`), the
commutativity constraint, conclusion (4) of [Stacks, Tag 0FML] (`coefficientProjectionFormulaMap`)
and the change of coefficients (`higherDirectImageCoefficientRestrictionIso`). -/
def coefficientFirstPageMapZero (q : ℤ) (M : Modules Y.toRingedSpace) :
    (coefficientFirstPageFlat f g q).obj M ⟶
      higherDirectImage (derivedRelativePushforward f g)
        (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coefficientTargetTensor f).obj M)) q :=
  (pushforward (toInverseImageBase g)).map
      ((flatDegenerateDerivedTensor Y M (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f))
          (fun i => hflat i) q).inv ≫ coefficientFirstPageTensorMap f q M) ≫
    (higherDirectImageCoefficientRestrictionIso f g _ q).inv

/-- `coefficientFirstPageMapZero` as an isomorphism, for quasi-coherent `M`. -/
def coefficientFirstPageIsoZero (q : ℤ) (M : Modules Y.toRingedSpace) (hM : M.IsQuasicoherent) :
    (coefficientFirstPageFlat f g q).obj M ≅
      higherDirectImage (derivedRelativePushforward f g)
        (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((coefficientTargetTensor f).obj M)) q :=
  (pushforward (toInverseImageBase g)).mapIso
      ((flatDegenerateDerivedTensor Y M (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f))
          (fun i => hflat i) q).symm ≪≫
        (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).mapIso
          (((((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                  Y.toRingedSpace.sheaf).obj
                ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj M)).mapIso
              (AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso
                f) ≪≫
            (((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
                (Stacks.RingedSpace.toRingedSite Y.toRingedSpace)
                (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
                  Y.toRingedSpace.sheaf)).app _).app _).symm) ≪≫
            deRhamOrdinaryProjectionFormulaIso f M hM) ≪≫
            (derivedPushforward (inverseImageBaseProjection f)).mapIso
              (DerivedCategory.Q.mapIso (coefficientTargetTensorIsoTensorComplex f M).symm))) ≪≫
    (higherDirectImageCoefficientRestrictionIso f g _ q).symm

/-- The forward map of `coefficientFirstPageIsoZero` is `coefficientFirstPageMapZero`. -/
theorem coefficientFirstPageIsoZero_hom (q : ℤ) (M : Modules Y.toRingedSpace)
    (hM : M.IsQuasicoherent) :
    (coefficientFirstPageIsoZero f g hflat q M hM).hom =
      coefficientFirstPageMapZero f g hflat q M :=
  rfl

/-- The shape of the naturality square of `coefficientFirstPageMapZero`. -/
private theorem paste_naturality_zero {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {E₀ E₀' E₁ E₁' E₂ E₂' : C} {G G' : D}
    (X : E₀ ⟶ E₀') (A : E₀ ⟶ E₁) (A' : E₀' ⟶ E₁') (t₁ : E₁ ⟶ E₁')
    (T : E₁ ⟶ E₂) (T' : E₁' ⟶ E₂') (t₂ : E₂ ⟶ E₂')
    (c : P.obj E₂ ⟶ G) (c' : P.obj E₂' ⟶ G') (r : G ⟶ G')
    (h₁ : A ≫ t₁ = X ≫ A') (h₂ : t₁ ≫ T' = T ≫ t₂) (h₄ : P.map t₂ ≫ c' = c ≫ r) :
    P.map X ≫ P.map (A' ≫ T') ≫ c' = (P.map (A ≫ T) ≫ c) ≫ r := by
  rw [← P.map_comp_assoc, ← reassoc_of% h₁, h₂, ← Category.assoc, P.map_comp_assoc, h₄,
    Category.assoc]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`coefficientFirstPageMapZero` is natural in the module.** -/
theorem coefficientFirstPageMapZero_naturality (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    (coefficientFirstPageFlat f g q).map φ ≫ coefficientFirstPageMapZero f g hflat q M' =
      coefficientFirstPageMapZero f g hflat q M ≫
        (DerivedCategory.homologyFunctor _ q).map ((derivedRelativePushforward f g).map
          (DerivedCategory.Q.map (((coefficientRestriction f g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ((coefficientTargetTensor f).map φ)))) :=
  paste_naturality_zero (pushforward (toInverseImageBase g)) _ _ _ _ _ _ _ _ _ _
    (flatDegenerateDerivedTensor_inv_naturality Y φ
      (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) (fun i => hflat i) q)
    (coefficientFirstPageTensorMap_naturality f q φ)
    (inv_comp_eq_comp_inv_of_hom _ _ _ _
      (higherDirectImageCoefficientRestrictionIso_hom_naturality f g
        ((coefficientTargetTensor f).map φ) q)).symm

/-- **The first-page comparison through the shift of the derived direct image**:
`M ⊗_{𝒪_Y} ℋ^q_dR(X/Y) ⟶ R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`, the unshifted comparison
`coefficientFirstPageMapZero` followed by the identification `R^qf_*C ≅ R^{k + q}f_*(C[-k])`
given by the commutation of `coefficientDerivedDirectImage` with the shifts and the shift
sequence of the cohomology functors (`Functor.shiftSequenceCommShiftIso`). -/
def coefficientFirstPageShiftMap (k : ℕ) (q : ℤ) (M : Modules Y.toRingedSpace) :
    (coefficientFirstPageFlat f g q).obj M ⟶ (coefficientFirstPageSource f g k q).obj M :=
  coefficientFirstPageMapZero f g hflat q M ≫
    (Functor.shiftSequenceCommShiftIso (coefficientDerivedDirectImage f g)
      (DerivedCategory.homologyFunctor _ 0) ((coefficientTargetTensor f).obj M) (-(k : ℤ)) q
      ((k : ℤ) + q) (by omega)).hom

/-- `coefficientFirstPageShiftMap` as an isomorphism, for quasi-coherent `M`. -/
def coefficientFirstPageShiftIso (k : ℕ) (q : ℤ) (M : Modules Y.toRingedSpace)
    (hM : M.IsQuasicoherent) :
    (coefficientFirstPageFlat f g q).obj M ≅ (coefficientFirstPageSource f g k q).obj M :=
  coefficientFirstPageIsoZero f g hflat q M hM ≪≫
    Functor.shiftSequenceCommShiftIso (coefficientDerivedDirectImage f g)
      (DerivedCategory.homologyFunctor _ 0) ((coefficientTargetTensor f).obj M) (-(k : ℤ)) q
      ((k : ℤ) + q) (by omega)

/-- The forward map of `coefficientFirstPageShiftIso` is `coefficientFirstPageShiftMap`. -/
theorem coefficientFirstPageShiftIso_hom (k : ℕ) (q : ℤ) (M : Modules Y.toRingedSpace)
    (hM : M.IsQuasicoherent) :
    (coefficientFirstPageShiftIso f g hflat k q M hM).hom =
      coefficientFirstPageShiftMap f g hflat k q M :=
  rfl

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **`coefficientFirstPageShiftMap` is natural in the module.** -/
theorem coefficientFirstPageShiftMap_naturality (k : ℕ) (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    (coefficientFirstPageFlat f g q).map φ ≫ coefficientFirstPageShiftMap f g hflat k q M' =
      coefficientFirstPageShiftMap f g hflat k q M ≫
        (coefficientFirstPageSource f g k q).map φ := by
  dsimp only [coefficientFirstPageShiftMap]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (coefficientFirstPageMapZero_naturality f g hflat q φ)).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Functor.shiftSequenceCommShiftIso_hom_naturality
      (coefficientDerivedDirectImage f g) (DerivedCategory.homologyFunctor _ 0)
      ((coefficientTargetTensor f).map φ) (-(k : ℤ)) q ((k : ℤ) + q) (by omega))).trans
      (Category.assoc _ _ _).symm)))

/-! ### The identification of the first page -/

/-- **The first page of [Stacks, Tag 0FMM] in the flat case, at a natural-number cut**:
`R^{k + q}f_*gr^kΩ^•_{X/S} ≅ Ω^k_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, the identification of the graded
piece with `f^{-1}Ω^k_{Y/S}[-k] ⊗ Ω^•_{X/Y}` of Section 0FMK followed by the inverse of
`coefficientFirstPageShiftMap` at `Ω^k_{Y/S}`. -/
def higherDirectImageGradedPieceFlatIsoNat (k : ℕ) (q : ℤ) :
    higherDirectImage (derivedRelativePushforward f g)
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g))
          ((k : ℤ) + q) ≅
      deRhamFirstPageFlat f g (k : ℤ) q :=
  (DerivedCategory.homologyFunctor _ ((k : ℤ) + q)).mapIso
      ((derivedRelativePushforward f g).mapIso (DerivedCategory.Q.mapIso
        (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
          (stepSquares f g k).2))) ≪≫
    (coefficientFirstPageShiftIso f g hflat k q
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))
      (AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms g k)).symm

/-- **The first page of [Stacks, Tag 0FMM] in the flat case of [Stacks, Tag 0FMN]**:
`R^{p + q}f_*gr^pΩ^•_{X/S} ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)` for all `p, q`, when the
`ℋ^q_dR(X/Y)` are flat. For `p ≥ 0` it is `higherDirectImageGradedPieceFlatIsoNat`; for `p < 0`
both sides vanish. -/
def higherDirectImageGradedPieceFlatIso (p q : ℤ) :
    higherDirectImage (derivedRelativePushforward f g)
        (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) (p + q) ≅
      deRhamFirstPageFlat f g p q :=
  if hp : p < 0 then
    (isZero_higherDirectImage_gradedPiece_of_neg f g p (p + q) hp).iso
      ((isZero_deRhamFirstPage_of_neg f g p q hp).of_iso
        (deRhamFirstPageIsoOfIsFlat f g hflat p q).symm)
  else
    eqToIso (by rw [Int.toNat_of_nonneg (not_lt.1 hp)]) ≪≫
      higherDirectImageGradedPieceFlatIsoNat f g hflat p.toNat q ≪≫
      eqToIso (by rw [Int.toNat_of_nonneg (not_lt.1 hp)])

/-- Transport of a family of isomorphisms along an equality of indices. -/
private theorem eqToIso_trans_family_eq {ι C : Type*} [Category C] (A B : ι → C)
    (F : ∀ i, A i ≅ B i) {i j : ι} (e : i = j) {P Q : C} (h₁ : P = A i) (h₂ : B i = Q)
    (h₁' : P = A j) (h₂' : B j = Q) :
    eqToIso h₁ ≪≫ F i ≪≫ eqToIso h₂ = eqToIso h₁' ≪≫ F j ≪≫ eqToIso h₂' := by
  subst e
  rfl

/-- At a natural-number cut, `higherDirectImageGradedPieceFlatIso` is
`higherDirectImageGradedPieceFlatIsoNat`. -/
theorem higherDirectImageGradedPieceFlatIso_natCast (k : ℕ) (q : ℤ) :
    higherDirectImageGradedPieceFlatIso f g hflat (k : ℤ) q =
      higherDirectImageGradedPieceFlatIsoNat f g hflat k q := by
  rw [higherDirectImageGradedPieceFlatIso, dite_eq_right (by omega),
    eqToIso_trans_family_eq (fun i : ℕ => higherDirectImage (derivedRelativePushforward f g)
        (gradedPiece (inverseImageBase (f ≫ g)) (i : ℤ) (deRhamSmoothFiltration f g)) ((i : ℤ) + q))
      (fun i : ℕ => deRhamFirstPageFlat f g (i : ℤ) q)
      (fun i => higherDirectImageGradedPieceFlatIsoNat f g hflat i q) (Int.toNat_natCast k) _ _
      rfl rfl, eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

end Comparison

end Stacks.DeRhamSmooth

end
