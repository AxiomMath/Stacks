module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageCoefficientProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlatNaturality

/-!
# The first-page comparison with an arbitrary coefficient module

For `f : X ⟶ Y` quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, with flat de Rham
cohomology sheaves `ℋ^q_dR(X/Y)`, the first page of [Stacks, Tag 0FMM] is identified in
[Stacks, Tag 0FMN] with `Ω^k_{Y/S} ⊗ ℋ^q_dR(X/Y)`. This file builds the comparison

`M ⊗_{𝒪_Y} ℋ^q_dR(X/Y) ⟶ R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`

for every `𝒪_Y`-module `M`, natural in `M`, which at `M = Ω^k_{Y/S}` is the inverse of the
identification of [Stacks, Tag 0FMN].

## Main definitions

* `Stacks.DeRhamSmooth.coefficientFirstPageMap`: the comparison.

## Main results

* `Stacks.DeRhamSmooth.coefficientFirstPageMap_naturality`: it is natural in `M`.
* `Stacks.DeRhamSmooth.coefficientFirstPageMap_relativeDifferentialForms`: at `Ω^k_{Y/S}` it is
  `(higherDirectImageGradedTargetIso f g k q ≪≫ deRhamFirstPageIsoOfIsFlat f g hflat k q).inv`.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
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

section Comparison

open Stacks.DerivedTensor.RingedSite

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f]
  (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q))

/-- The morphism `H^q(M ⊗^𝐋 Rf_*Ω^•_{X/Y}) ⟶ H^q(Rf_*(f^{-1}M ⊗ Ω^•_{X/Y}))` induced by the
commutativity constraint and the projection-formula morphism `coefficientProjectionFormulaMap`. -/
def coefficientFirstPageTensorMap (q : ℤ) (M : Modules Y.toRingedSpace) :
    (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) q).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.obj
          ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) 0).obj
            M)).obj (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f))) ⟶
      (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj ((coefficientTargetTensor f).obj M))) :=
  (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).map
    (((((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).obj M)).map
        (AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso f).hom ≫
      (((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
            (Stacks.RingedSpace.toRingedSite Y.toRingedSpace)
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              Y.toRingedSpace.sheaf)).app _).app _).inv) ≫
      coefficientProjectionFormulaMap f M) ≫
      (derivedPushforward (inverseImageBaseProjection f)).map
        (DerivedCategory.Q.map (coefficientTargetTensorIsoTensorComplex f M).inv))

/-- A functor preserves a commutative square. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' Z : C} {a : A ⟶ B} {b : B ⟶ Z} {c : A ⟶ B'} {d : B' ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- Pasting four commutative squares. -/
private theorem paste_four {C : Type*} [Category C] {A₀ A₀' A₁ A₁' A₂ A₂' A₃ A₃' A₄ A₄' : C}
    (t₀ : A₀ ⟶ A₀') (t₁ : A₁ ⟶ A₁') (t₂ : A₂ ⟶ A₂') (t₃ : A₃ ⟶ A₃') (t₄ : A₄ ⟶ A₄')
    (x₁ : A₀ ⟶ A₁) (x₁' : A₀' ⟶ A₁') (x₂ : A₁ ⟶ A₂) (x₂' : A₁' ⟶ A₂')
    (x₃ : A₂ ⟶ A₃) (x₃' : A₂' ⟶ A₃') (x₄ : A₃ ⟶ A₄) (x₄' : A₃' ⟶ A₄')
    (h₁ : x₁ ≫ t₁ = t₀ ≫ x₁') (h₂ : t₁ ≫ x₂' = x₂ ≫ t₂) (h₃ : t₂ ≫ x₃' = x₃ ≫ t₃)
    (h₄ : t₃ ≫ x₄' = x₄ ≫ t₄) :
    t₀ ≫ (((x₁' ≫ x₂') ≫ x₃') ≫ x₄') = (((x₁ ≫ x₂) ≫ x₃) ≫ x₄) ≫ t₄ := by
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- `coefficientFirstPageTensorMap` is natural in the module. -/
theorem coefficientFirstPageTensorMap_naturality (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    (DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) q).map
          (((Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.map
            ((DerivedCategory.singleFunctor _ 0).map φ)).app
              (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f))) ≫
        coefficientFirstPageTensorMap f q M' =
      coefficientFirstPageTensorMap f q M ≫
        (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).map
          ((derivedPushforward (inverseImageBaseProjection f)).map
            (DerivedCategory.Q.map ((coefficientTargetTensor f).map φ))) := by
  have h₄ := coefficientTargetTensorIsoTensorComplex_hom_naturality f φ
  have h₄' : DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
            (deRhamCochainComplex f)).map
          ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).map
            ((modulePullback (inverseImageBaseProjection f)).map φ))) ≫
        DerivedCategory.Q.map (coefficientTargetTensorIsoTensorComplex f M').inv =
      DerivedCategory.Q.map (coefficientTargetTensorIsoTensorComplex f M).inv ≫
        DerivedCategory.Q.map ((coefficientTargetTensor f).map φ) :=
    map_comp_eq_map_comp _
      (inv_comp_eq_comp_inv_of_hom (coefficientTargetTensorIsoTensorComplex f M)
        (coefficientTargetTensorIsoTensorComplex f M') _ _ h₄).symm
  have h₄'' := map_comp_eq_map_comp (derivedPushforward (inverseImageBaseProjection f)) h₄'
  have n₁ := ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.toRingedSpace.sheaf).tensor.map
    ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ)).naturality
    (AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso f).hom
  have n₂ := ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
      (Stacks.RingedSpace.toRingedSite Y.toRingedSpace)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        Y.toRingedSpace.sheaf)).inv.app
      (AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnbounded
        f)).naturality
    ((DerivedCategory.singleFunctor (Modules Y.toRingedSpace) 0).map φ)
  have key := paste_four _ _ _ _ _ _ _ _ _ _ _ _ _ n₁ n₂
    (coefficientProjectionFormulaMap_naturality f φ) h₄''
  exact map_comp_eq_map_comp (DerivedCategory.homologyFunctor _ q) key

/-- A commutative square, followed by a further morphism. -/
private theorem square_assoc {C : Type*} [Category C] {A B B' D E : C} {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ B'} {d : B' ⟶ D} (h : a ≫ b = c ≫ d) (e : D ⟶ E) : a ≫ b ≫ e = c ≫ d ≫ e :=
  (reassoc_of% h) e

omit [QuasiCompact f] [QuasiSeparated f] [Smooth f] in
/-- The shift isomorphism `H^q(Rf_* C) ≅ H^{k + q}(Rf_*(C[-k]))` is natural in the complex `C`. -/
theorem coefficientFirstPageShift_naturality (k : ℕ) (q : ℤ)
    {C C' : CochainComplex (Modules (inverseImageBase f)) ℤ} (c : C ⟶ C') :
    letI : (derivedPushforward (inverseImageBaseProjection f)).CommShift ℤ :=
      (derivedAdjunction (inverseImageBaseProjection f)).rightAdjointCommShift ℤ
    (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).map
        ((derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map c)) ≫
        ((((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) 0).shiftIso
            (-(k : ℤ)) ((k : ℤ) + q) q (by omega)).app _).inv ≫
          ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)).mapIso
            ((derivedPushforward (inverseImageBaseProjection f)).mapIso
                ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).app C') ≪≫
              ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
                (-(k : ℤ))).app _)).inv) =
      ((((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) 0).shiftIso
            (-(k : ℤ)) ((k : ℤ) + q) q (by omega)).app _).inv ≫
          ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)).mapIso
            ((derivedPushforward (inverseImageBaseProjection f)).mapIso
                ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).app C) ≪≫
              ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
                (-(k : ℤ))).app _)).inv) ≫
        (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)).map
          ((derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map
            ((CategoryTheory.shiftFunctor (CochainComplex (Modules (inverseImageBase f)) ℤ)
              (-(k : ℤ))).map c))) := by
  let : (derivedPushforward (inverseImageBaseProjection f)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection f)).rightAdjointCommShift ℤ
  have h₁ := ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) 0).shiftIso
    (-(k : ℤ)) ((k : ℤ) + q) q (by omega)).inv.naturality
      ((derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map c))
  have h₂ := ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
    (-(k : ℤ))).inv.naturality (DerivedCategory.Q.map c)
  have h₃ := (DerivedCategory.Q.commShiftIso (-(k : ℤ))).inv.naturality c
  have h₃' := map_comp_eq_map_comp (derivedPushforward (inverseImageBaseProjection f)) h₃
  dsimp only [Functor.comp_map] at h₁ h₂ h₃'
  have key : ((CategoryTheory.shiftFunctor (DerivedCategory (Modules Y.toRingedSpace))
          (-(k : ℤ))).map
        ((derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map c))) ≫
        ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso (-(k : ℤ))).inv.app _ ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
          ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).inv.app C') =
      (((derivedPushforward (inverseImageBaseProjection f)).commShiftIso (-(k : ℤ))).inv.app _ ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
          ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).inv.app C)) ≫
        (derivedPushforward (inverseImageBaseProjection f)).map (DerivedCategory.Q.map
            ((CategoryTheory.shiftFunctor (CochainComplex (Modules (inverseImageBase f)) ℤ)
              (-(k : ℤ))).map c)) :=
    (square_assoc h₂ _).trans ((congrArg (_ ≫ ·) h₃').trans (Category.assoc _ _ _).symm)
  have key' := map_comp_eq_map_comp
    (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)) key
  simp only [Functor.map_comp] at key'
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp]
  exact (square_assoc h₁ _).trans (congrArg (_ ≫ ·) key')

/-- **The first-page comparison with an arbitrary coefficient module** `M`:
`M ⊗_{𝒪_Y} ℋ^q_dR(X/Y) ⟶ R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`, the inverse of the
identification of the first page of [Stacks, Tag 0FMM] in the flat case read with `M` in place
of `Ω^k_{Y/S}`. -/
def coefficientFirstPageMap (k : ℕ) (q : ℤ) (M : Modules Y.toRingedSpace) :
    (coefficientFirstPageFlat f g q).obj M ⟶ (coefficientFirstPageSource f g k q).obj M :=
  letI : (derivedPushforward (inverseImageBaseProjection f)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection f)).rightAdjointCommShift ℤ
  (pushforward (toInverseImageBase g)).map
      (flatDegenerateDerivedTensor Y M (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f))
          (fun i => hflat i) q).inv ≫
    ((pushforward (toInverseImageBase g)).map
      ((coefficientFirstPageTensorMap f q M ≫
          (((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) 0).shiftIso
            (-(k : ℤ)) ((k : ℤ) + q) q (by omega)).app _).inv) ≫
        ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)).mapIso
          ((derivedPushforward (inverseImageBaseProjection f)).mapIso
              ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).app
                ((coefficientTargetTensor f).obj M)) ≪≫
            ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
              (-(k : ℤ))).app _)).inv) ≫
    (higherDirectImageCoefficientRestrictionIso f g _ _).inv)

/-- At `M = Ω^k_{Y/S}`, `coefficientFirstPageMap` is the inverse of the identification of the
first page in the flat case. -/
theorem coefficientFirstPageMap_relativeDifferentialForms (k : ℕ) (q : ℤ) :
    coefficientFirstPageMap f g hflat k q
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      (higherDirectImageGradedTargetIso f g k q ≪≫ deRhamFirstPageIsoOfIsFlat f g hflat k q).inv :=
  rfl

/-- Pasting commutative squares along a composite of three morphisms, followed by a functor and a
further square. -/
private theorem paste_naturality {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {E₀ E₀' E₁ E₁' E₂ E₂' E₃ E₃' E₄ E₄' : C} {G G' : D}
    (X : E₀ ⟶ E₀') (A : E₀ ⟶ E₁) (A' : E₀' ⟶ E₁') (t₁ : E₁ ⟶ E₁')
    (T : E₁ ⟶ E₂) (T' : E₁' ⟶ E₂') (t₂ : E₂ ⟶ E₂')
    (s : E₂ ⟶ E₃) (s' : E₂' ⟶ E₃') (m : E₃ ⟶ E₄) (m' : E₃' ⟶ E₄') (t₃ : E₄ ⟶ E₄')
    (c : P.obj E₄ ⟶ G) (c' : P.obj E₄' ⟶ G') (r : G ⟶ G')
    (h₁ : A ≫ t₁ = X ≫ A') (h₂ : t₁ ≫ T' = T ≫ t₂) (h₃ : t₂ ≫ s' ≫ m' = (s ≫ m) ≫ t₃)
    (h₄ : P.map t₃ ≫ c' = c ≫ r) :
    P.map X ≫ P.map A' ≫ P.map ((T' ≫ s') ≫ m') ≫ c' =
      (P.map A ≫ P.map ((T ≫ s) ≫ m) ≫ c) ≫ r := by
  have key : X ≫ A' ≫ (T' ≫ s') ≫ m' = A ≫ ((T ≫ s) ≫ m) ≫ t₃ := by
    simp only [Category.assoc] at h₃ ⊢
    rw [← reassoc_of% h₁, reassoc_of% h₂, h₃]
  have key' := congrArg P.map key
  simp only [Functor.map_comp, Category.assoc] at key' ⊢
  rw [reassoc_of% key', h₄]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **The first-page comparison is natural in the coefficient module**: for every morphism
`φ : M ⟶ M'` of `𝒪_Y`-modules, `φ ⊗ 1` on `M ⊗ ℋ^q_dR(X/Y)` corresponds to the map induced by
`φ` on `R^{k + q}f_*(f^{-1}M[-k] ⊗ Ω^•_{X/Y})`. -/
theorem coefficientFirstPageMap_naturality (k : ℕ) (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    (coefficientFirstPageFlat f g q).map φ ≫ coefficientFirstPageMap f g hflat k q M' =
      coefficientFirstPageMap f g hflat k q M ≫ (coefficientFirstPageSource f g k q).map φ := by
  let : (derivedPushforward (inverseImageBaseProjection f)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection f)).rightAdjointCommShift ℤ
  have h₁ := flatDegenerateDerivedTensor_inv_naturality Y φ
    (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) (fun i => hflat i) q
  have h₂ := coefficientFirstPageTensorMap_naturality f q φ
  have h₃ := coefficientFirstPageShift_naturality f k q ((coefficientTargetTensor f).map φ)
  have h₄ := higherDirectImageCoefficientRestrictionIso_hom_naturality f g
    ((CategoryTheory.shiftFunctor (CochainComplex (Modules (inverseImageBase f)) ℤ)
      (-(k : ℤ))).map ((coefficientTargetTensor f).map φ)) ((k : ℤ) + q)
  have h₄' := inv_comp_eq_comp_inv_of_hom _ _ _ _ h₄
  exact paste_naturality (pushforward (toInverseImageBase g)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h₁ h₂ h₃ h₄'.symm

end Comparison

end Stacks.DeRhamSmooth

end
