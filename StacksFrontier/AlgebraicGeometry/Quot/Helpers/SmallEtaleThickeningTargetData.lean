module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComp
public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetModulesIso

/-!
# The comparison of direct images for the thickened small étale topoi of a factorization

For morphisms of algebraic spaces `f : X ⟶ Y`, `g : Y ⟶ Z` and `k : X ⟶ Z` with `f ≫ g = k`, the
morphism of small étale ringed topoi of `g` relates those of `f` and of `k`
(`AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq`). This file supplies the comparison
`g_*f_* ≅ k_*` of direct images of sheaves of sets of Stacks 03G8, the map of direct images of
`𝒪_X` lying over it, and the compatibility with the structure maps, which is the input of
`Deformation.ToposThickening.ThickeningTargetMorphism.thickenedModulesCompIso`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq`.
* `AlgebraicGeometry.Space.smallEtaleThickeningTargetPushforwardIso`.
* `AlgebraicGeometry.Space.smallEtaleThickeningTargetRingMap`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)
open Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The morphism of small étale ringed topoi of `g`, relating those of `f` and of `k`**, for
`f ≫ g = k`: `smallEtaleThickeningTarget f g` read along `f ≫ g = k`. -/
def smallEtaleThickeningTargetOfEq (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    ThickeningTargetMorphism.{u, u + 1, u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS k) (smallEtaleRingedToposHom B S hS f) where
  j := smallEtaleRingedToposHom B S hS g
  ρ := eqToHom (congrArg (fun m : X ⟶ Z =>
      baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS m)) hk.symm) ≫
    smallEtaleCompBaseMap f g
  comm := by
    subst hk
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (fSharp_comp_smallEtaleCompBaseMap f g)

/-- **The comparison `g_*f_* ≅ k_*` of direct images of sheaves of sets** (Stacks 03G8), read
along `f ≫ g = k`. -/
def smallEtaleThickeningTargetPushforwardIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) :
    ((smallEtaleThickeningTargetOfEq f g k hk).baseHom.comp
        (pushforwardRingToposHom (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedTopos B S hS X).O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom (smallEtaleRingedToposHom B S hS k)
        (smallEtaleRingedTopos B S hS X).O).toToposHom.pushforward :=
  compToposPushforwardIso B S hS f g ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z =>
      (smallEtaleRingedToposHom B S hS m).toToposHom.pushforward) hk)

/-- The map of direct images of `𝒪_X` lying over
`AlgebraicGeometry.Space.smallEtaleThickeningTargetPushforwardIso`. -/
def smallEtaleThickeningTargetRingMap (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :=
  Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans (smallEtaleRingedTopos B S hS Z).J
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (reshape (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS X).O).O)
    (smallEtaleThickeningTargetPushforwardIso f g k hk).hom

/-- **The structure maps are compatible**: the structure map of `g ∘ f` on the thickened bases,
followed by `AlgebraicGeometry.Space.smallEtaleThickeningTargetRingMap`, is that of `k`. -/
theorem structureRingMap_comp_smallEtaleThickeningTargetRingMap (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hk : f ≫ g = k) :
    ((smallEtaleThickeningTargetOfEq f g k hk).baseHom.comp
        (pushforwardRingToposHom (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedTopos B S hS X).O)).structureRingMap ≫
        smallEtaleThickeningTargetRingMap f g k hk =
      (pushforwardRingToposHom (smallEtaleRingedToposHom B S hS k)
        (smallEtaleRingedTopos B S hS X).O).structureRingMap := by
  subst hk
  refine ThickeningTargetMorphism.structureRingMap_comp_pullbackRingSheafMapOfNatTrans
    (smallEtaleThickeningTargetOfEq f g (f ≫ g) rfl)
    (smallEtaleThickeningTargetPushforwardIso f g (f ≫ g) rfl) ?_
  have h2 : (sheafCompose (smallEtaleRingedTopos B S hS Z).J (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
        (smallEtaleRingedTopos B S hS X).O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
    Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
  have h3 : (sheafCompose (smallEtaleRingedTopos B S hS Z).J (forget CommRingCat.{u})).map
        ((smallEtaleRingedToposHom_compRingIso B S hS f g).inv.app
          (smallEtaleRingedTopos B S hS X).O) ≫
      (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) = 𝟙 _ :=
    (congrArg (_ ≫ ·) h2.symm).trans (((sheafCompose (smallEtaleRingedTopos B S hS Z).J
      (forget CommRingCat.{u})).map_comp _ _).symm.trans ((congrArg (sheafCompose
        (smallEtaleRingedTopos B S hS Z).J (forget CommRingCat.{u})).map
        (Iso.inv_hom_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))
  simp only [smallEtaleThickeningTargetOfEq, smallEtaleCompBaseMap,
    smallEtaleThickeningTargetPushforwardIso, pushforwardStructureCompIso, Category.assoc,
    eqToHom_refl, Category.id_comp, eqToIso_refl, compToposPushforwardIso]
  refine Eq.trans ?_ h3
  exact congrArg₂ (· ≫ ·) (congrArg _ ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
    (Category.comp_id _))) (Category.comp_id _)


/-- **`Ψ₀ ∘ f_* ≅ k_*` on modules** for `f ≫ g = k`, together with its value
`g_*f_* ≅ k_*` on underlying sheaves of sets. -/
def smallEtaleThickenedModulesCompIsoWithSheafMap (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) :=
  (smallEtaleThickeningTargetOfEq f g k hk).thickenedModulesCompIsoWithSheafMap
    (smallEtaleThickeningTargetPushforwardIso f g k hk)
    (smallEtaleThickeningTargetRingMap f g k hk)
    (Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans
      (smallEtaleRingedTopos B S hS Z).J (Stacks.SheafOfModules.Tensor.ringSheaf
        (reshape (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS X).O).O)
      (smallEtaleThickeningTargetPushforwardIso f g k hk).hom)
    (structureRingMap_comp_smallEtaleThickeningTargetRingMap f g k hk)

/-- **`Ψ₀ ∘ f_* ≅ k_*` on modules** for `f ≫ g = k`. -/
def smallEtaleThickenedModulesCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f) ⋙
        (smallEtaleThickeningTargetOfEq f g k hk).basePushforward ≅
      thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k) :=
  (smallEtaleThickenedModulesCompIsoWithSheafMap f g k hk).1

/-- **`Ψ₀ ∘ f_* ≅ k_*` is `g_*f_* ≅ k_*` on underlying sheaves of sets.** -/
theorem moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (J := (smallEtaleRingedTopos B S hS Z).J)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (baseRing.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k)))).map
        ((smallEtaleThickenedModulesCompIso f g k hk).hom.app M) =
      (smallEtaleThickeningTargetPushforwardIso f g k hk).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (J := (smallEtaleRingedTopos B S hS X).J)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) M) :=
  (smallEtaleThickenedModulesCompIsoWithSheafMap f g k hk).2 M

end AlgebraicGeometry.Space

end
