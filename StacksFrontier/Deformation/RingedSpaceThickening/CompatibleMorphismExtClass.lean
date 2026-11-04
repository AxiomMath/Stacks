module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismGluingDescent
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismNaiveCotangentN
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackNaiveCotangentMap
public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackTwoTerm
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClassification
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationFlatDegreeZero

/-!
# Compatible morphisms of thickenings and the classes of the extensions

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, `ℱ`
an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module and `c : ℱ ⟶ g_*𝒢` a `g`-map. Let `0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0`
be an extension of `f⁻¹𝒪_S`-algebras with class `ξ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, ℱ)` and
`0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of `g⁻¹f⁻¹𝒪_S`-algebras with class
`ζ ∈ Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)` (the classes of the bijection of Stacks 0GPZ). This file proves
Stacks 0GQ1: an `S`-morphism `Y' ⟶ X'` compatible with `g` and `c` exists if and only if `ξ` and
`ζ` have the same image in `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)`, the maps being
`Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢` on coefficients and `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` on the complexes.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.nonempty_compatibleMorphism_iff_pullbackExtClass_eq`:
  Stacks 0GQ1.

## Implementation notes

As in the proof of Stacks 0GQ1, both sides are read on the presentations `α_X : 𝒪_{X'} ⟶ 𝒪_X`
and `α_Y : 𝒪_{Y'} ⟶ 𝒪_Y` by the underlying sheaves of sets, so that `ξ` and `ζ` are the classes
of `𝒥_X/𝒥_X² ⟶ ℱ` and `𝒥_Y/𝒥_Y² ⟶ 𝒢` (Stacks 0GQ0). The degree `0` term of `𝖭𝖫(α_X)` is flat,
so `Lg^*𝖭𝖫(α_X) ⟶ g^*𝖭𝖫(α_X)` is injective on `Ext¹(-, 𝒢)` and the condition becomes an equality
of classes on `g^*𝖭𝖫(α_X)`. A compatible morphism gives a map `g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫(α_Y)` carrying
one class to the other. Conversely, on the termwise fibre product
`N = g^*𝖭𝖫(α_X) ×_{𝖭𝖫_{Y/S}} 𝖭𝖫(α_Y)` the equality says that the difference homomorphism
`(a, b) ↦ c(δ_X a) - δ_Y b` on the degree `-1` term factors through the differential, and such a
factorization glues to a compatible morphism
(`AlgebraicGeometry.RingedSpaceThickening.LiftGluing.compatibleMorphismOfFactorization`).

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction HomologicalComplex
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)
open AlgebraicGeometry.RingedSpaceThickening.CompatibleMorphism (comparisonX comparisonY)

universe u v w

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

-- The finite (co)products of the derived category are those of its triangulated structure, not
-- those of the instances of Stacks 07D9 (stated for the locally small model).
attribute [-instance] Stacks.Injectives.hasCoproducts_derivedCategory
  Stacks.Injectives.hasProducts_derivedCategory

namespace AlgebraicGeometry.RingedSpaceThickening

/-- **The class of a homomorphism after an arbitrary chain map of two-term complexes**: for a
chain map `φ : (X₀ ⟶ X₁) ⟶ (Y₀ ⟶ Y₁)` of complexes in degrees `-1` and `0` and `δ : Y₀ ⟶ H`, the
class of `δ` pulled back along `φ` is the class of `δ` after the degree `-1` component of `φ`. -/
theorem Q_map_comp_conormalExtClass_ofDoubleNegOne' {C : Type*} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {X₀ X₁ Y₀ Y₁ : C} {d : X₀ ⟶ X₁} {e : Y₀ ⟶ Y₁}
    (φ : double d ComplexShape.upIntRelNegOneZero ⟶ double e ComplexShape.upIntRelNegOneZero)
    (H : C) (δ : Y₀ ⟶ H) :
    DerivedCategory.Q.map φ ≫ (NaiveCotangentTwoTerm.ofDoubleNegOne e).conormalExtClass H δ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass H
        (((doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv ≫ φ.f (-1) ≫
          (doubleXIso₀ e ComplexShape.upIntRelNegOneZero).hom) ≫ δ) := by
  have h := LiftGluing.Q_map_comp_conormalExtClass_ofDoubleNegOne
    (a₀ := (doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv ≫ φ.f (-1) ≫
      (doubleXIso₀ e ComplexShape.upIntRelNegOneZero).hom)
    (a₁ := (doubleXIso₁ d ComplexShape.upIntRelNegOneZero (by decide)).inv ≫ φ.f 0 ≫
      (doubleXIso₁ e ComplexShape.upIntRelNegOneZero (by decide)).hom) φ
    (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc])
    (by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]) H δ
  exact h

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} (g : Y ⟶ X)

/-- **The map `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` is the comparison of Stacks 06YJ followed by the canonical
map** `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
theorem derivedPullbackNaiveCotangentMap_eq :
    derivedPullbackNaiveCotangentMap g f =
      derivedPullbackComparisonOnComplex g
          (PresentedSquareZeroExtension.relativeComplex f :
            CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) ≫
        DerivedCategory.Q.map (pullbackNaiveCotangentMap g f) := by
  have e : ((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      (PresentedSquareZeroExtension.relativeComplex f :
        CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) = 𝟙 _ := rfl
  have e' : DerivedCategory.Qh.map (((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom.app
      (PresentedSquareZeroExtension.relativeComplex f :
        CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map e).trans (DerivedCategory.Qh.map_id _)
  unfold derivedPullbackNaiveCotangentMap derivedPullbackComparisonOnComplex
  rw [e']
  simp only [Category.assoc]
  exact congrArg _ (congrArg _ (congrArg (· ≫ _) (Category.id_comp _).symm))

namespace LiftGluing

variable {F : SheafOfModules.{u} (structureSheafRing X)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}
  (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
  (c : F ⟶ (modulePushforward g).obj G)

/-- The class of `𝒪_{X'}` read on `𝖭𝖫(α_X)` is the class of `δ_X : 𝒥_X/𝒥_X² ⟶ ℱ`. -/
theorem Q_map_compX_comp_extClass :
    DerivedCategory.Q.map (compX P) ≫ P.extClass =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dX P)).conormalExtClass F (δX P) := by
  have h := (PresentedSquareZeroExtension.naiveCotangentIso f P.generators
    P.generatorsMap).hom_inv_id_assoc
    ((PresentedSquareZeroExtension.twoTerm f P.generators P.generatorsMap).conormalExtClass F
      P.conormalToIdeal)
  unfold compX δX dX
  exact h

/-- The class of `𝒪_{Y'}` read on `𝖭𝖫(α_Y)` is the class of `δ_β : 𝒥_β/𝒥_β² ⟶ 𝒢`. -/
theorem Q_map_compY_comp_extClass :
    DerivedCategory.Q.map (compY g Q) ≫ Q.extClass =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dβ g Q)).conormalExtClass G (δβ g Q) := by
  have h := (PresentedSquareZeroExtension.naiveCotangentIso (g ≫ f) Q.generators
    Q.generatorsMap).hom_inv_id_assoc
    ((PresentedSquareZeroExtension.twoTerm (g ≫ f) Q.generators Q.generatorsMap).conormalExtClass
      G Q.conormalToIdeal)
  unfold compY δβ dβ
  exact h

/-- The degree `0` term `𝛺_X` of `𝖭𝖫(α_X)` is flat. -/
theorem isFlat_bX : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (bX P) :=
  KX_X_zero P ▸ Stacks.SheafOfModules.isFlat_presentationNaiveCotangentComplex_X_zero
    (inverseImageBaseRing f) X.sheaf (structureRingMap f) P.generators P.generatorsMap

/-- **The image of `ξ` read on `𝖭𝖫(α_X)`**: the comparison `Lg^*𝖭𝖫(α_X) ⟶ g^*𝖭𝖫(α_X)` followed by
the class of `g^*(𝒥_X/𝒥_X²) ⟶ g^*ℱ ⟶ 𝒢`. -/
theorem map_Q_compX_comp_pullbackExtClass :
    (derivedPullback g).map (DerivedCategory.Q.map (compX P)) ≫
        pullbackExtClass g f (cAdj g c) P.extClass =
      derivedPullbackComparisonOnComplex g (KX P) ≫
        DerivedCategory.Q.map (mapDoubleIso g (dX P)).hom ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
          ((modulePullback g).map (δX P) ≫ cAdj g c) := by
  have h := pullbackExtClass_conormalExtClass g (dX P) (δX P) (cAdj g c)
  have e : (derivedPullback g).map (DerivedCategory.Q.map (compX P)) ≫
      (derivedPullback g).map P.extClass = (derivedPullback g).map
        ((NaiveCotangentTwoTerm.ofDoubleNegOne (dX P)).conormalExtClass F (δX P)) :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg (derivedPullback g).map (Q_map_compX_comp_extClass P))
  unfold pullbackExtClass
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans h)

/-- **The image of `ζ` read on `𝖭𝖫(α_X)`**: the comparison `Lg^*𝖭𝖫(α_X) ⟶ g^*𝖭𝖫(α_X)` followed by
`g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫_{Y/S}` and `ζ`. -/
theorem map_Q_compX_comp_restrictDerivedExtClass :
    (derivedPullback g).map (DerivedCategory.Q.map (compX P)) ≫
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f) Q.extClass =
      derivedPullbackComparisonOnComplex g (KX P) ≫ DerivedCategory.Q.map (pullX g P) ≫
        Q.extClass := by
  have h := derivedPullbackComparisonOnComplex_naturality'_assoc g (compX P)
    (DerivedCategory.Q.map (pullbackNaiveCotangentMap g f) ≫ Q.extClass)
  unfold restrictDerivedExtClass
  rw [derivedPullbackNaiveCotangentMap_eq]
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (h.trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Q.extClass)
      ((Functor.map_comp _ _ _).symm.trans (congrArg DerivedCategory.Q.map (pullX_eq g P).symm))))))

/-- The difference of the two classes on `g^*𝖭𝖫(α_X)`. -/
def classDiff : DerivedCategory.Q.obj (((modulePullback g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (KX P)) ⟶
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
      G)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (mapDoubleIso g (dX P)).hom ≫
      (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
        ((modulePullback g).map (δX P) ≫ cAdj g c) -
    DerivedCategory.Q.map (pullX g P) ≫ Q.extClass

/-- **The two images agree exactly when the difference on `g^*𝖭𝖫(α_X)` vanishes**: the
comparison `Lg^*𝖭𝖫(α_X) ⟶ g^*𝖭𝖫(α_X)` is injective on `Ext¹(-, 𝒢)`, the degree `0` term of
`𝖭𝖫(α_X)` being flat. -/
theorem pullbackExtClass_eq_iff_classDiff_eq_zero :
    pullbackExtClass g f (cAdj g c) P.extClass =
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f) Q.extClass ↔
      classDiff g P Q c = 0 := by
  have : IsIso (DerivedCategory.Q.map (compX P)) := by
    unfold compX comparisonX
    exact PresentedSquareZeroExtension.isIso_Q_map_comparison f P.generators P.generatorsMap
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine eq_zero_of_derivedPullbackComparisonOnComplex_comp g (dX P) (isFlat_bX P) _ ?_
    unfold classDiff
    rw [Preadditive.comp_sub, ← map_Q_compX_comp_pullbackExtClass,
      ← map_Q_compX_comp_restrictDerivedExtClass, h, sub_self]
  · refine (cancel_epi ((derivedPullback g).map (DerivedCategory.Q.map (compX P)))).1 ?_
    unfold classDiff at h
    rw [map_Q_compX_comp_pullbackExtClass, map_Q_compX_comp_restrictDerivedExtClass,
      sub_eq_zero.1 h]

/-! ### A compatible morphism makes the difference vanish -/

section Necessity

variable {g P Q c}

/-- The transposed chain map `g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫(α_Y)` of a compatible morphism, with source and
target written through `double`. -/
def pullMap (h : CompatibleMorphism P Q c) :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (KX P) ⟶ KY g Q :=
  h.pullbackPresentationMap

/-- `pullMap` in degree `-1` is the transposed map of conormal sheaves. -/
theorem pullMap_f_negOne (h : CompatibleMorphism P Q c) : (pullMap h).f (-1) =
    (modulePullback g).map (doubleXIso₀ (dX P) ComplexShape.upIntRelNegOneZero).hom ≫
      h.pullbackConormalMap ≫ (doubleXIso₀ (dβ g Q) ComplexShape.upIntRelNegOneZero).inv := by
  have e := Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne g.hom.base
    (structureRingMap_comp_structureComorphism g f) h.generatorsMap_comp
  refine (mapHomologicalComplex_homEquiv_symm_f _ _ _).trans ?_
  refine (congrArg ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm e).trans ?_
  refine ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_left_symm _ _).trans ?_
  exact congrArg (_ ≫ ·) ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_right_symm
    _ _)

/-- `pullX` factors through `pullMap`. -/
theorem pullMap_comp_compY (h : CompatibleMorphism P Q c) : pullMap h ≫ compY g Q = pullX g P :=
  h.pullbackPresentationMap_comp_comparison.trans (pullX_eq g P).symm

/-- `double (g^*d_X) ⟶ g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫(α_Y)` in degree `-1`, read through the identifications of
the terms, is the transposed map of conormal sheaves. -/
theorem mapDoubleIso_inv_comp_pullMap_f_negOne (h : CompatibleMorphism P Q c) :
    (doubleXIso₀ ((modulePullback g).map (dX P)) ComplexShape.upIntRelNegOneZero).inv ≫
        ((mapDoubleIso g (dX P)).inv ≫ pullMap h).f (-1) ≫
          (doubleXIso₀ (dβ g Q) ComplexShape.upIntRelNegOneZero).hom =
      h.pullbackConormalMap := by
  rw [HomologicalComplex.comp_f, pullMap_f_negOne]
  simp only [mapDoubleIso, Iso.symm_inv, doubleMapFunctorIso, asIso_hom, doubleMapFunctorHom,
    mkHomFromDouble_f₀, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.assoc _ _ _).trans ((congrArg (h.pullbackConormalMap ≫ ·)
    (Iso.inv_hom_id _)).trans (Category.comp_id _))

/-- **A compatible morphism carries the class of `𝒪_{X'}` to that of `𝒪_{Y'}`** on
`g^*𝖭𝖫(α_X)`. -/
theorem Q_map_mapDoubleIso_inv_comp_pullX_comp_extClass (h : CompatibleMorphism P Q c) :
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map
      (mapDoubleIso g (dX P)).inv ≫ DerivedCategory.Q.map (pullX g P) ≫
        Q.extClass =
      (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
        ((modulePullback g).map (δX P) ≫ cAdj g c) := by
  have e₁ : (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map
      (pullX g P) ≫ Q.extClass =
      (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map (pullMap h) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne (dβ g Q)).conormalExtClass G (δβ g Q) :=
    (congrArg (fun t ↦ DerivedCategory.Q.map t ≫ Q.extClass) (pullMap_comp_compY h).symm).trans
      ((congrArg (· ≫ Q.extClass) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Q_map_compY_comp_extClass g Q))))
  have e₂ := Q_map_comp_conormalExtClass_ofDoubleNegOne' ((mapDoubleIso g (dX P)).inv ≫ pullMap h)
    G (δβ g Q)
  have e₃ : h.pullbackConormalMap ≫ δβ g Q = (modulePullback g).map (δX P) ≫ cAdj g c :=
    h.pullbackConormalMap_comp_conormalToIdeal
  exact (congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).symm.trans (e₂.trans
      (congrArg ((NaiveCotangentTwoTerm.ofDoubleNegOne
        ((modulePullback g).map (dX P))).conormalExtClass G)
        ((congrArg (· ≫ δβ g Q) (mapDoubleIso_inv_comp_pullMap_f_negOne h)).trans e₃)))))

/-- **A compatible morphism makes the difference of the classes vanish.** -/
theorem classDiff_eq_zero (h : CompatibleMorphism P Q c) : classDiff g P Q c = 0 := by
  refine (cancel_epi (DerivedCategory.Q.map (mapDoubleIso g (dX P)).inv)).1 ?_
  have e₄ : (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map
      (mapDoubleIso g (dX P)).inv ≫ DerivedCategory.Q.map (mapDoubleIso g (dX P)).hom ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
          ((modulePullback g).map (δX P) ≫ cAdj g c) =
      (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
          ((modulePullback g).map (δX P) ≫ cAdj g c) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (Iso.inv_hom_id _)).trans
        (CategoryTheory.Functor.map_id _ _)))).trans
        (Category.id_comp _))
  unfold classDiff
  exact (Preadditive.comp_sub _ _ _).trans ((congrArg₂ (· - ·) e₄
    (Q_map_mapDoubleIso_inv_comp_pullX_comp_extClass h)).trans ((sub_self _).trans comp_zero.symm))

end Necessity

/-! ### The vanishing of the difference gives a compatible morphism -/

section Sufficiency

/-- The projection `N ⟶ g^*𝖭𝖫(α_X)` followed by the isomorphism
`g^*𝖭𝖫(α_X) ≅ double (g^*d_X)` is the projection `N ⟶ double (g^*d_X)`. -/
theorem fstN_comp_mapDoubleIso_hom : fstN g P Q ≫ (mapDoubleIso g (dX P)).hom = fstN' g P Q :=
  (Category.assoc _ _ _).trans ((congrArg (fstN' g P Q ≫ ·)
    (Iso.hom_inv_id (pullDoubleIso g P))).trans (Category.comp_id _))

/-- **On `N` the difference of the two classes is the class of the difference homomorphism**
`Δ : N₀ ⟶ 𝒢`, `(a, b) ↦ c(δ_X a) - δ_β b`. -/
theorem Q_map_fstN_comp_classDiff :
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map (fstN g P Q) ≫
        classDiff g P Q c =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dN g P Q)).conormalExtClass G (Δ g P Q c) := by
  have a : (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map
      (fstN g P Q) ≫ DerivedCategory.Q.map (mapDoubleIso g (dX P)).hom ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass G
          ((modulePullback g).map (δX P) ≫ cAdj g c) =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dN g P Q)).conormalExtClass G
        (pullback.fst _ _ ≫ (modulePullback g).map (δX P) ≫ cAdj g c) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans
      (congrArg DerivedCategory.Q.map (fstN_comp_mapDoubleIso_hom g P Q)))).trans
        (Q_map_fstN'_comp_conormalExtClass g P Q _))
  have b : (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).map
      (fstN g P Q) ≫ DerivedCategory.Q.map (pullX g P) ≫ Q.extClass =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dN g P Q)).conormalExtClass G
        (pullback.snd _ _ ≫ δβ g Q) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.extClass)
      ((Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Q.map
        (fstN_comp_pullX g P Q)).trans (Functor.map_comp _ _ _)))).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Q_map_compY_comp_extClass g Q)).trans
        (Q_map_sndN_comp_conormalExtClass g P Q _))))
  unfold classDiff
  exact (Preadditive.comp_sub _ _ _).trans ((congrArg₂ (· - ·) a b).trans
    (conormalExtClass_sub _ G _ _).symm)

/-- **If the difference of the classes vanishes, a compatible morphism exists**: the difference
homomorphism on `N₀` then factors through the differential of `N`, and the factorization glues. -/
theorem nonempty_compatibleMorphism_of_classDiff_eq_zero (h : classDiff g P Q c = 0) :
    Nonempty (CompatibleMorphism P Q c) := by
  have e := (Q_map_fstN_comp_classDiff g P Q c).symm.trans
    ((congrArg (_ ≫ ·) h).trans comp_zero)
  obtain ⟨θ, hθ⟩ := (NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff _ G _).1 e
  exact ⟨compatibleMorphismOfFactorization g P Q c θ hθ⟩

end Sufficiency

end LiftGluing

variable {F : SheafOfModules.{u} (structureSheafRing X)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}

open SquareZeroAlgebraExtension in
/-- **Stacks Project, Tag 0GQ1.** Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be
morphisms of ringed spaces, `ℱ` an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module and `c : ℱ ⟶ g_*𝒢` a
`g`-map. Let `P : 0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` be an extension of `f⁻¹𝒪_S`-algebras corresponding to
`ξ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, ℱ)` and `Q : 0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of
`g⁻¹f⁻¹𝒪_S`-algebras corresponding to `ζ ∈ Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)` under the bijections of
Stacks 0GPZ. Then there is an `S`-morphism `g' : Y' ⟶ X'` compatible with `g` and `c` if and
only if `ξ` and `ζ` map to the same element of `Ext¹_{𝒪_Y}(Lg^*𝖭𝖫_{X/S}, 𝒢)`: `ξ` through `Lg^*`
and the coefficient map `Lg^*ℱ ⟶ g^*ℱ ⟶ 𝒢` (the last map the adjoint of `c`), and `ζ` through
the canonical map `Lg^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
@[stacks 0GQ1]
theorem nonempty_compatibleMorphism_iff_pullbackExtClass_eq (P : SquareZeroAlgebraExtension f F)
    (Q : SquareZeroAlgebraExtension (g ≫ f) G) (c : F ⟶ (modulePushforward g).obj G) :
    Nonempty (CompatibleMorphism P Q c) ↔
      pullbackExtClass g f (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c)
          (isomorphismClassesEquivExt f F (Quotient.mk _ P)) =
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap g f)
          (isomorphismClassesEquivExt (g ≫ f) G (Quotient.mk _ Q)) :=
  ⟨fun ⟨h⟩ ↦ (LiftGluing.pullbackExtClass_eq_iff_classDiff_eq_zero g P Q c).2
      (LiftGluing.classDiff_eq_zero h),
    fun e ↦ LiftGluing.nonempty_compatibleMorphism_of_classDiff_eq_zero g P Q c
      ((LiftGluing.pullbackExtClass_eq_iff_classDiff_eq_zero g P Q c).1 e)⟩

end AlgebraicGeometry.RingedSpaceThickening

end
