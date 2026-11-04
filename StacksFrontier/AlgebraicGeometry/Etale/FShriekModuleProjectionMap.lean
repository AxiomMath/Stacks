module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensorPresheafMap

/-!
# The comparison map of the projection formula

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The source of
[Stacks, Tag 0GKF] builds its comparison

`can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)`

by sheafifying a map of presheaves out of the finite-support direct image `f_{p!}`. That map of
presheaves is `AlgebraicGeometry.SmallEtale.modFiniteSupportTensorPresheafMap`; this file
sheafifies it.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekModTensorSheafifyIso` — `f_!F ⊗_Λ G` is the
  sheafification of `f_{p!}F ⊗_Λ G`.
* `AlgebraicGeometry.SmallEtale.modFShriekProjectionMap` — **the comparison map `can` of
  [Stacks, Tag 0GKF]**.

## Implementation notes

No `J.W`-localization argument is needed to see that `f_!F ⊗_Λ G` is the sheafification of
`f_{p!}F ⊗_Λ G`: sheafification is monoidal, so the sheafification of `f_{p!}F ⊗_Λ G` is the
tensor product of the sheafifications, and those are `f_!F` by
`AlgebraicGeometry.SmallEtale.fShriekModSheafifyIso` and `G` by the counit of the sheafification
adjunction, which is an isomorphism on a sheaf.

Nothing here carries a `stacks` attribute: [Stacks, Tag 0GKF] asserts that `can` is an
*isomorphism*, which is
`AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`. This file only builds the map.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **`f_!F ⊗_Λ G` is the sheafification of `f_{p!}F ⊗_Λ G`.** Sheafification is monoidal, and
the sheafifications of `f_{p!}F` and of the sections of `G` are `f_!F` and `G`. -/
public def fShriekModTensorSheafifyIso (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G ≅
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) v} Λ)).obj
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) :=
  tensorIso (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f F)
      (asIso ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
        (ModuleCat.{max (u + 1) v} Λ)).counit.app G)).symm ≪≫
    Functor.Monoidal.μIso
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) v} Λ))
      ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F) G.obj

/-- **The comparison map of [Stacks, Tag 0GKF]**,
`can : f_!F ⊗_Λ G ⟶ f_!(F ⊗_Λ f^{-1}G)`: the sheafification of the source's map of presheaves
`AlgebraicGeometry.SmallEtale.modFiniteSupportTensorPresheafMap`, read through the
identifications of both sides with sheafifications of presheaves built from `f_{p!}`. -/
public def modFShriekProjectionMap (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) :
    (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G ⟶
      (fShriekMod.{u, v, max (u + 1) v} B Λ f).obj
        (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :=
  (fShriekModTensorSheafifyIso B Λ f F G).hom ≫
    (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) v} Λ)).map
      (modFiniteSupportTensorPresheafMap B Λ f F G) ≫
    (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
      (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))).inv

end AlgebraicGeometry.SmallEtale

end
