module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTargetData
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp

/-!
# `Ψ₀ ∘ f_* ≅ (f ≫ g)_*` read over the structure sheaves is Stacks 03LU

For a morphism `D : ThickeningTargetMorphism i₁ i₂` of the targets of two thickenings and an
isomorphism `E : Ψ₀ ∘ i₂_* ≅ i₁_*` of direct images over the bases which is a given map `θ` of
sheaves of sets, the composite `j_*i₂_*M ≅ Ψ₀ i₂_*M ≅ i₁_*M` of modules over `O_{Y₁}` (through
`Deformation.ToposThickening.ThickeningTargetMorphism.restrictIso`) is every comparison
`j_*i₂_* ≅ i₁_*` of direct images of modules which is `θ` on underlying sheaves of sets
(`Deformation.ToposThickening.ThickeningTargetMorphism.restrictIso_hom_comp_map_hom_app_eq`).

For the small étale ringed topoi of `f : X ⟶ Y` and `g : Y ⟶ Z` this identifies the comparison
`AlgebraicGeometry.Space.smallEtaleThickenedModulesCompIso` with the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso'` of Stacks 03LU
(`AlgebraicGeometry.Space.restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app`).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules (hom_ext_moduleSheafFunctor)

universe v u v₁ u₁ v₂ u₂ w

namespace Deformation.ToposThickening.ThickeningTargetMorphism

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)

/-- **`j_*i₂_*M ≅ Ψ₀ i₂_*M ≅ i₁_*M` is any comparison `j_*i₂_* ≅ i₁_*` with the same underlying
map of sheaves of sets.** -/
theorem restrictIso_hom_comp_map_hom_app_eq
    (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (hE : ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
          (E.hom.app M) =
        θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
    (C : i₂.pushforwardModules ⋙ D.j.pushforwardModules ≅ i₁.pushforwardModules)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hC : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)).map
          (C.hom.app M) =
        θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    (D.restrictIso ((thickenedModulesFunctor i₂).obj M)).hom ≫
        (structureRestrict i₁).map (E.hom.app M) = C.hom.app M := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_))
  exact (congrArg (fun φ ↦ φ.hom.app U y) (hE M)).trans
    (congrArg (fun φ ↦ φ.hom.app U y) hC).symm

end Deformation.ToposThickening.ThickeningTargetMorphism

namespace AlgebraicGeometry.Space

open Deformation.ToposThickening

universe u'

variable {B : BigFppfSite.{u'}} {S : Scheme.{u'}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **`g_*f_* ≅ (f ≫ g)_*` of Stacks 03LU is `g_*f_* ≅ (f ≫ g)_*` on underlying sheaves of
sets.** -/
theorem moduleSheafFunctor_map_modulePushforwardCompIso'_hom_app
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u'} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    (Sheaf.moduleSheafFunctor.{u', u', u' + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Z).O)).map
          ((modulePushforwardCompIso' B S hS f g).hom.app M) =
      (smallEtaleThickeningTargetPushforwardIso f g (f ≫ g) rfl).hom.app
        (Sheaf.moduleSheaf.{u', u', u' + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O) M) := by
  have h1 := RingedToposHom.moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) M
  have h2 := RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app
      (compRingedToposHom B S hS f g) (smallEtaleRingedToposHom B S hS (f ≫ g))
      (compToposPushforwardIso B S hS f g) (compStructureRingMap B S hS f g)
      (ringSheafMap_compStructureRingMap B S hS f g) (structureRingMap_comp B S hS f g) M
  exact ((Sheaf.moduleSheafFunctor.{u', u', u' + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS Z).O)).map_comp _ _).trans ((congrArg₂ (· ≫ ·) h1 h2).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- **`j_*` of `X ⊂ Y` followed by `Ψ₀ ∘ f_* ≅ (f ≫ g)_*` is `g_*f_* ≅ (f ≫ g)_*` of
Stacks 03LU.** -/
theorem restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u'} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    ((smallEtaleThickeningTargetOfEq f g (f ≫ g) rfl).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)).hom ≫
      (structureRestrict (smallEtaleRingedToposHom B S hS (f ≫ g))).map
        ((smallEtaleThickenedModulesCompIso f g (f ≫ g) rfl).hom.app M) =
    (modulePushforwardCompIso' B S hS f g).hom.app M :=
  (smallEtaleThickeningTargetOfEq f g (f ≫ g) rfl).restrictIso_hom_comp_map_hom_app_eq
    (smallEtaleThickenedModulesCompIso f g (f ≫ g) rfl)
    (smallEtaleThickeningTargetPushforwardIso f g (f ≫ g) rfl)
    (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app f g (f ≫ g) rfl)
    (modulePushforwardCompIso' B S hS f g) M
    (moduleSheafFunctor_map_modulePushforwardCompIso'_hom_app f g M)

end AlgebraicGeometry.Space

end
