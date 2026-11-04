module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblemSections
public import StacksFrontier.Deformation.ToposThickening.RebaseSiteTransportGenerators

/-!
# The section `1 ⊗ m` of `𝒪_X ⊗_R M` on the model of the small étale site

Let `X` be an algebraic space and `φ : R →+* Γ(model, 𝒪)` a base ring of the model of its small
étale site. The base-ring tensor module `𝒪_X ⊗_R M` of `X` is that of the model carried back by
the Comparison Lemma, and the counit of the Comparison Lemma identifies its restriction to the
model with the base-ring tensor module of the model
(`AlgebraicGeometry.Space.ProperFlatLift.modelBaseRingTensorCounitIso`). This file shows that the
counit carries the restriction of the section `1 ⊗ m` to the section `1 ⊗ m`, as an equation of
morphisms out of the free module of rank one.

## Main results

* `moduleResUnitHom_baseRingTensorSection_comp_modelBaseRingTensorCounitIso_hom`: the counit
  carries the restriction of the section `1 ⊗ m` to the section `1 ⊗ m`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

open Deformation.ToposThickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Model

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The section `1 ⊗ m` of `𝒪_X ⊗_R M`, restricted to the model**: the restriction of the
section `1 ⊗ m` of the base-ring tensor module, followed by the counit of the Comparison Lemma, is
the section `1 ⊗ m` of the base-ring tensor module of the model. -/
theorem moduleResUnitHom_baseRingTensorSection_comp_modelBaseRingTensorCounitIso_hom
    (M : ModuleCat.{u} R) (m : M) :
    moduleResUnitHom (X := smallEtaleRingedTopos B S hS X) (T := (smallEtaleRingedTopos B S hS X).O)
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
        (baseRingTensorSection B S hS X φ M m) ≫
          (ProperFlatLift.modelBaseRingTensorCounitIso X φ M).hom =
      (SheafOfModules.unitHomEquiv ((baseRingTensorFunctor.{u, u, u, u} φ).obj M)).symm
        ((baseRingTensorUnit.{u, u, u, u} φ M).hom m) :=
  unit_hom_ext fun U =>
    ((congrArg (((ProperFlatLift.modelBaseRingTensorCounitIso X φ M).hom).val.app U)
      (moduleResUnitHom_val_app_one (X := smallEtaleRingedTopos B S hS X)
        (T := (smallEtaleRingedTopos B S hS X).O)
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
        (baseRingTensorSection B S hS X φ M m) U)).trans
      (counitIso_hom_val_app_baseRingTensorSection X φ M m U)).trans
      (unitHomEquiv_symm_val_app_one _ U).symm

/-- **A restricted global section through `G^s(b) ≪≫ c`**, for modules on the small étale site of
the algebraic space `X` (`Deformation.ToposThickening.moduleResUnitHom_comp_mapIso_trans_hom`
for `𝒪_X`-modules). -/
theorem moduleResUnitHom_comp_mapIso_trans_hom_of_modules {M N : Modules.{u, u} B S hS X.1 X.2}
    {P : SheafOfModules.{u} ((sheafCompose (smallEtaleModelTopology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((Deformation.AlgebraExtension.ringRes (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X).inverse).obj (smallEtaleRingedTopos B S hS X).O))}
    (τ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ M) (b : M ≅ N)
    (c : (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquiv B S hS X).inverse (smallEtaleRingedTopos B S hS X).O).obj N ≅ P)
    {σ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ N}
    {d : SheafOfModules.unit ((sheafCompose (smallEtaleModelTopology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((Deformation.AlgebraExtension.ringRes (smallEtaleModelTopology B S hS X.1)
          (smallEtaleModelEquiv B S hS X).inverse).obj (smallEtaleRingedTopos B S hS X).O)) ⟶ P}
    (hσ : τ ≫ b.hom = σ)
    (hd : moduleResUnitHom (X := smallEtaleRingedTopos B S hS X)
      (T := (smallEtaleRingedTopos B S hS X).O) (smallEtaleModelTopology B S hS X.1)
      (smallEtaleModelEquiv B S hS X) σ ≫ c.hom = d) :
    moduleResUnitHom (X := smallEtaleRingedTopos B S hS X) (T := (smallEtaleRingedTopos B S hS X).O)
        (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X) τ ≫
      ((Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS X.1)
        (smallEtaleModelEquiv B S hS X).inverse (smallEtaleRingedTopos B S hS X).O).mapIso b ≪≫
          c).hom = d :=
  moduleResUnitHom_comp_mapIso_trans_hom (X := smallEtaleRingedTopos B S hS X)
    (T := (smallEtaleRingedTopos B S hS X).O) (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquiv B S hS X) τ b c hσ hd

end Model

end AlgebraicGeometry.Space
