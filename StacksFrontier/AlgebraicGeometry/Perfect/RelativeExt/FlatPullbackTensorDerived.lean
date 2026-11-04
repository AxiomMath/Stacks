module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.FlatPullbackTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentDerivedFlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion

/-!
# `Φ` is the derived functor `Lf^*(-) ⊗^L 𝒢`

Let `f : X ⟶ Y` be a morphism of ringed spaces and `𝒢` a bounded complex of `𝒪_X`-modules flat
over `Y`. The functor `Φ = pullbackTensorDerivedFunctor : D(𝒪_Y) ⥤ D(𝒪_X)`, the descent of
`K ↦ Tot(f^*K ⊗ 𝒢)`, is isomorphic to `N ↦ Lf^*N ⊗^L_{𝒪_X} 𝒢`, the derived pullback followed by
the derived tensor product of [Stacks, Tag 06YU] with `𝒢`.

The comparison is the canonical one: on a complex `K` it is the comparison `Lf^*K ⟶ f^*K` of
the derived pullback, followed by the natural map `f^*K ⊗^L 𝒢 ⟶ Tot(f^*K ⊗ 𝒢)` from the derived
to the ordinary tensor product. On a K-flat complex `K` both are invertible: the first because
derived pullback is computed on K-flat complexes, the second because `f^*K` is again K-flat
([Stacks, Tag 06YC]). Every object of `D(𝒪_Y)` is represented by a K-flat complex.

## Main definitions

* `Stacks.Cohomology.RelativeExt.derivedPullbackTensorFunctor`: `N ↦ Lf^*N ⊗^L 𝒢`.
* `Stacks.Cohomology.RelativeExt.derivedPullbackTensorIso`: `Lf^*(-) ⊗^L 𝒢 ≅ Φ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- **`N ↦ Lf^*N ⊗^L_{𝒪_X} 𝒢`**, the derived pullback followed by the derived tensor product of
[Stacks, Tag 06YU] with `𝒢` placed in the second variable. -/
abbrev derivedPullbackTensorFunctor :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  derivedPullback f ⋙
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
      (DerivedCategory.Q.obj G)

variable {f G}

/-- The comparison `Lf^*K ⊗^L 𝒢 ⟶ Φ(K)` on a complex `K`: the comparison of the derived pullback,
then the map from the derived to the ordinary tensor product, then the identification of `Φ`
on complexes. -/
def toPullbackTensorDerivedFunctorOnComplex (hG : IsBoundedFlatOver f G)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullbackTensorFunctor f G).obj (DerivedCategory.Q.obj P) ⟶
      (pullbackTensorDerivedFunctor hG).obj (DerivedCategory.Q.obj P) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
      (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f P)).app
      (DerivedCategory.Q.obj G) ≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) G ≫
    (pullbackTensorDerivedFunctorFactors hG).inv.app P

/-- The comparison on complexes is natural in the complex. -/
theorem toPullbackTensorDerivedFunctorOnComplex_naturality (hG : IsBoundedFlatOver f G)
    {P P' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (φ : P ⟶ P') :
    (derivedPullbackTensorFunctor f G).map (DerivedCategory.Q.map φ) ≫
        toPullbackTensorDerivedFunctorOnComplex hG P' =
      toPullbackTensorDerivedFunctorOnComplex hG P ≫
        (pullbackTensorDerivedFunctor hG).map (DerivedCategory.Q.map φ) := by
  have h₁ := StacksDraft.UnitPullbackComposition.derivedPullbackComparisonOnComplex_naturality f φ
  have h₂ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) (𝟙 G)
  have h₃ := (pullbackTensorDerivedFunctorFactors hG).inv.naturality φ
  have e₀ : ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).tensor.obj
      (DerivedCategory.Q.obj (((modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P'))).map (DerivedCategory.Q.map (𝟙 G)) = 𝟙 _ :=
    (congrArg _ (DerivedCategory.Q.map_id G)).trans (CategoryTheory.Functor.map_id _ _)
  rw [e₀, Category.id_comp] at h₂
  have e₁ : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        ((derivedPullback f).map (DerivedCategory.Q.map φ))).app (DerivedCategory.Q.obj G) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f P')).app
          (DerivedCategory.Q.obj G) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f P)).app
          (DerivedCategory.Q.obj G) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
        (DerivedCategory.Q.map (((modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ))).app (DerivedCategory.Q.obj G) := by
    have h := congrArg (fun t => ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      X.sheaf).map t).app (DerivedCategory.Q.obj G)) h₁
    simp only [CategoryTheory.Functor.map_comp] at h
    exact h
  simp only [toPullbackTensorDerivedFunctorOnComplex, Functor.comp_map, Functor.flip_obj_map,
    Category.assoc]
  rw [← Category.assoc _ (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    X.sheaf).map _).app _), e₁, Category.assoc]
  congr 1
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₃).trans (Category.assoc _ _ _).symm)))

/-- **The comparison `Lf^*(-) ⊗^L 𝒢 ⟶ Φ`**, as a natural transformation of functors
`D(𝒪_Y) ⥤ D(𝒪_X)`: the descent of the comparison on complexes along the localization. -/
def toPullbackTensorDerivedFunctor (hG : IsBoundedFlatOver f G) :
    derivedPullbackTensorFunctor f G ⟶ pullbackTensorDerivedFunctor hG :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      _).preimage
    { app := toPullbackTensorDerivedFunctorOnComplex hG
      naturality := fun _ _ φ => toPullbackTensorDerivedFunctorOnComplex_naturality hG φ }

/-- The component of `toPullbackTensorDerivedFunctor` at the image of a complex `P` in the
derived category is the comparison `toPullbackTensorDerivedFunctorOnComplex` at `P`. -/
theorem toPullbackTensorDerivedFunctor_app_Q (hG : IsBoundedFlatOver f G)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (toPullbackTensorDerivedFunctor hG).app (DerivedCategory.Q.obj P) =
      toPullbackTensorDerivedFunctorOnComplex hG P :=
  NatTrans.congr_app ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      _).map_preimage _) P

/-- The comparison on complexes is invertible at a K-flat complex. -/
theorem isIso_toPullbackTensorDerivedFunctorOnComplex (hG : IsBoundedFlatOver f G)
    (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y P) :
    IsIso (toPullbackTensorDerivedFunctorOnComplex hG P) := by
  have :=
    Stacks.NaiveCotangentDerivedFlatBaseChange.isIso_derivedPullbackComparisonOnComplex_of_kFlat
      f P hP
  have hfP := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f P hP
  have e := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      X.sheaf).toTensor_eq_comparisonLeft
    (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) G hfP
  unfold toPullbackTensorDerivedFunctorOnComplex
  rw [e]
  have h₀ : IsIso ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
      (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f P)) :=
    Functor.map_isIso _ _
  have : IsIso (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
      (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex f P)).app
        (DerivedCategory.Q.obj G)) := NatIso.isIso_app_of_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (Iso.isIso_hom ((pullbackTensorDerivedFunctorFactors hG).app P).symm))

/-- **`Lf^*(-) ⊗^L 𝒢 ≅ Φ`**: the comparison is invertible at every object, every object of
`D(𝒪_Y)` being represented by a K-flat complex. -/
instance isIso_toPullbackTensorDerivedFunctor (hG : IsBoundedFlatOver f G) :
    IsIso (toPullbackTensorDerivedFunctor hG) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun E => ?_)
  refine (NatTrans.isIso_app_iff_of_iso _
    (Stacks.SheafOfModules.DerivedTensorStalk.kFlatModelIso Y.sheaf E)).1 ?_
  rw [toPullbackTensorDerivedFunctor_app_Q]
  exact isIso_toPullbackTensorDerivedFunctorOnComplex hG _
    (Stacks.SheafOfModules.DerivedTensorStalk.kFlat_kFlatModel Y.sheaf E)

/-- **`Lf^*N ⊗^L 𝒢 ≅ Φ(N)`**, naturally in `N ∈ D(𝒪_Y)`. -/
def derivedPullbackTensorIso (hG : IsBoundedFlatOver f G) :
    derivedPullbackTensorFunctor f G ≅ pullbackTensorDerivedFunctor hG :=
  asIso (toPullbackTensorDerivedFunctor hG)

end Stacks.Cohomology.RelativeExt

end
