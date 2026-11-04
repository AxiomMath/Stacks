module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleUnderivedPullbackCompMates

/-!
# The degreewise functors of algebraic spaces in the ringed-topos spelling

The degreewise pullback and direct image of complexes of modules along a morphism of algebraic
spaces, `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy` and
`AlgebraicGeometry.Space.smallEtalePushforwardMapHomotopy`, have their types spelled through
`AlgebraicGeometry.Space.ringedToposStructureRingSheaf`. The same functors
`Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy` and
`Stacks.Cohomology.DerivedPushforward.pushforwardMapHomotopy` of the small étale ringed topoi
have their types spelled through `AlgebraicGeometry.Space.smallEtaleRingedTopos` and
`Stacks.SheafOfModules.Tensor.ringSheaf`.

The two spellings are definitionally equal. This file records the identification of each
functor, natural transformation and isomorphism separately, together with the composition
isomorphisms typed in the ringed-topos spelling.

## Main definitions

* `AlgebraicGeometry.Space.ringedToposPushforwardMapHomotopyCompIso`: the isomorphism
  `f_* ⋙ g_* ≅ h_*` of degreewise direct images for `f ≫ g = h`.
* `AlgebraicGeometry.Space.ringedToposPullbackMapHomotopyCompIso`: the isomorphism
  `g^* ⋙ f^* ≅ h^*` of degreewise pullbacks for `f ≫ g = h`.

## Main results

* `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy_eq`,
  `AlgebraicGeometry.Space.smallEtalePushforwardMapHomotopy_eq`,
  `AlgebraicGeometry.Space.smallEtaleMapHomotopyAdjunction_counit_eq`: the functors and counits.
* `AlgebraicGeometry.Space.smallEtalePushforwardMapHomotopyCompIso_inv_eq`,
  `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso_trans_congr_hom_eq`: the
  composition isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (pullbackMapHomotopy pushforwardMapHomotopy
  pullbackAdjPushforwardMapHomotopy)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The composition isomorphism `f_* ⋙ g_* ≅ h_*` of degreewise direct images for
`f ≫ g = h`, typed in the ringed-topos spelling. -/
def ringedToposPushforwardMapHomotopyCompIso (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS f) ⋙
        pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS g) ≅
      pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS h) :=
  Functor.mapHomotopyCategoryCompIso (modulePushforwardCompIso' B S hS f g ≪≫
    eqToIso (congrArg (fun k ↦ (smallEtaleRingedToposHom B S hS k).pushforwardModules) w))
    (ComplexShape.up ℤ)

/-- The composition isomorphism `g^* ⋙ f^* ≅ h^*` of degreewise pullbacks for `f ≫ g = h`,
`smallEtaleUnderivedPullbackCompIso` followed by the transport along `f ≫ g = h`, typed in the
ringed-topos spelling. -/
def ringedToposPullbackMapHomotopyCompIso (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    pullbackMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS g) ⋙
        pullbackMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS f) ≅
      pullbackMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS h) :=
  smallEtaleUnderivedPullbackCompIso B S hS f g ≪≫ smallEtaleUnderivedPullbackCongr B S hS w

/-- Degreewise pullback in the two spellings. -/
theorem smallEtalePullbackMapHomotopy_eq (f : X ⟶ Y) :
    smallEtalePullbackMapHomotopy B S hS f =
      pullbackMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS f) := rfl

/-- Degreewise direct image in the two spellings. -/
theorem smallEtalePushforwardMapHomotopy_eq (f : X ⟶ Y) :
    smallEtalePushforwardMapHomotopy B S hS f =
      pushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1} (smallEtaleRingedToposHom B S hS f) := rfl

/-- The counit of the degreewise adjunction in the two spellings. -/
theorem smallEtaleMapHomotopyAdjunction_counit_eq (f : X ⟶ Y) :
    (smallEtaleMapHomotopyAdjunction B S hS f).counit =
      (pullbackAdjPushforwardMapHomotopy.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f)).counit := rfl

/-- The composition isomorphism of degreewise direct images in the two spellings. -/
theorem smallEtalePushforwardMapHomotopyCompIso_inv_eq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    (smallEtalePushforwardMapHomotopyCompIso B S hS f g w).inv =
      (ringedToposPushforwardMapHomotopyCompIso B S hS f g w).inv := rfl

/-- The composition isomorphism of degreewise pullbacks in the two spellings. -/
theorem smallEtaleUnderivedPullbackCompIso_trans_congr_hom_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) :
    (smallEtaleUnderivedPullbackCompIso B S hS f g ≪≫
      smallEtaleUnderivedPullbackCongr B S hS w).hom =
      (ringedToposPullbackMapHomotopyCompIso B S hS f g w).hom := rfl

end AlgebraicGeometry.Space

end
