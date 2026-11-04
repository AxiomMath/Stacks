module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningIdealMapMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison

/-!
# The structure maps of a composite of morphisms of small étale ringed topoi

For morphisms of algebraic spaces `f : X ⟶ Y`, `g : Y ⟶ Z`, `k : X ⟶ Z` with `f ≫ g = k`, the
unit-module structure map `𝒪_Z ⟶ g_*𝒪_Y ⟶ g_*f_*𝒪_X`, read through the comparison
`g_*f_* ≅ k_*` of Stacks 03LU (`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`), is the
structure map `𝒪_Z ⟶ k_*𝒪_X`.

## Main results

Both in the namespace `AlgebraicGeometry`.

* `RingedToposHom.unitStructureMap_comp_pushforwardModulesIsoOfPushforwardIso_hom_app`:
  the transport of direct images of modules along a comparison of direct images compatible with
  the structure maps carries the unit-module structure map to the unit-module structure map.
* `Space.unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq`:
  the structure map of `k = f ≫ g` is that of `g` followed by `g_*` of that of `f`, read through
  `g_*f_* ≅ k_*`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (hom_ext_moduleSheafFunctor)

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  (F H : RingedToposHom X Y)

/-- **The unit-module structure map is carried to the unit-module structure map** by the
transport of direct images of modules along a comparison of direct images of sheaves of sets
compatible with the structure maps. -/
theorem unitStructureMap_comp_pushforwardModulesIsoOfPushforwardIso_hom_app
    (θ : F.toToposHom.pushforward ≅ H.toToposHom.pushforward)
    (β : pullbackRingSheaf Y.J F.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⟶
      pullbackRingSheaf Y.J H.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    (hβ : (sheafCompose Y.J (forget RingCat.{w₂})).map β =
      θ.hom.app (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
    (hstruct : F.structureRingMap ≫ β = H.structureRingMap) :
    unitStructureMap F ≫ (pushforwardModulesIsoOfPushforwardIso F H θ β hβ hstruct).hom.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) =
      unitStructureMap H := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_unitStructureMap,
    moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app,
    moduleSheafFunctor_map_unitStructureMap]
  exact (congrArg (_ ≫ ·) hβ.symm).trans
    (((sheafCompose Y.J (forget RingCat.{w₂})).map_comp _ _).symm.trans
      (congrArg (sheafCompose Y.J (forget RingCat.{w₂})).map hstruct))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The structure map of `k = f ≫ g` is that of `g` followed by `g_*` of that of `f`**, read
through the comparison `g_*f_* ≅ k_*` of Stacks 03LU. -/
theorem unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS g) ≫
        (smallEtaleRingedToposHom B S hS g).pushforwardModules.map
          (RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS f)) ≫
        (modulePushforwardCompIsoOfEq f g k hk).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS X).O)) =
      RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS k) := by
  subst hk
  have h1 := RingedToposHom.unitStructureMap_comp (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom B S hS f)
  have h2 := RingedToposHom.unitStructureMap_comp_pushforwardModulesIsoOfPushforwardIso_hom_app
    (compRingedToposHom B S hS f g) (smallEtaleRingedToposHom B S hS (f ≫ g))
    (compToposPushforwardIso B S hS f g) (compStructureRingMap B S hS f g)
    (ringSheafMap_compStructureRingMap B S hS f g) (structureRingMap_comp B S hS f g)
  rw [← Category.assoc, ← h1]
  simp only [modulePushforwardCompIsoOfEq, modulePushforwardCompIso', Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.assoc]
  exact h2

end AlgebraicGeometry.Space

end
