module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionMap

/-!
# The germ of the comparison map of the projection formula

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The comparison
`can` of [Stacks, Tag 0GKF] is
`AlgebraicGeometry.SmallEtale.modFShriekProjectionMap`. This file reduces the assertion that
`can` is an isomorphism to a statement about the presheaf map it was sheafified from, and
computes what that map does to a germ.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_modFShriekProjectionMap_of_W` — **`can` is an isomorphism
  as soon as the source's map of presheaves is a local isomorphism.** Both of the
  identifications `can` is assembled from are isomorphisms, so this is
  `CategoryTheory.GrothendieckTopology.W_iff`.
* `AlgebraicGeometry.SmallEtale.toPresheafFiber_modFiniteSupportTensorPresheafMap` — **the germ
  of the projection map.** On the stalk at a geometric point `ȳ` of `Y`, the germ of a section
  over a pointed étale neighbourhood `V` goes to the germ of its image under the recipe.

## Implementation notes

The stalk functor used here is the fibre of the point of the site attached to the geometric
point, on *presheaves*: `CategoryTheory.GrothendieckTopology.Point.presheafFiber`. That is the
right one for this purpose — it is monoidal with an explicit formula on germs
(`CategoryTheory.GrothendieckTopology.Point.tensorHom_comp_toPresheafFiber_μ`), it inverts
`J.W`, and the stalk of a sheafification is the stalk of the presheaf by
`CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`, whose comparison
is a monoidal natural transformation. So the three comparisons the stalk of `can` has to be
pushed through — monoidality of sheafification, stalk-of-sheafification against
stalk-of-presheaf, and monoidality of the stalk functor — are all absorbed by working with
`presheafFiber` and `J.W` instead of with the sheaf stalks.

The germ formula is stated for an arbitrary section of the pointwise tensor product rather
than for a pure tensor, which is both more general and free: it is the naturality of germs. The
pure-tensor form, `germ(x) ⊗ germ(t) ↦ germ(x ⊗ f^{-1}t)`, follows by composing with
`CategoryTheory.GrothendieckTopology.Point.tensorHom_comp_toPresheafFiber_μ`, Mathlib's germ
formula for the monoidality of the fibre functor on presheaves.

Nothing here carries a `stacks` attribute: [Stacks, Tag 0GKF] asserts that `can` is an
isomorphism, which is `AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`. This file only supplies the
reduction and the germ formula that proof consumes.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SmallEtale

universe u v

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **`can` is an isomorphism as soon as the source's map of presheaves is a local
isomorphism.** The two identifications `can` is assembled from are isomorphisms, and a map of
presheaves is inverted by sheafification exactly when it lies in `J.W`. -/
public theorem isIso_modFShriekProjectionMap_of_W
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    (h : (SmallEtale.topology B Y.obj Y.property).W (modFiniteSupportTensorPresheafMap B Λ f F G)) :
    IsIso (modFShriekProjectionMap B Λ f F G) := by
  have := ((SmallEtale.topology B Y.obj Y.property).W_iff
    (modFiniteSupportTensorPresheafMap B Λ f F G)).1 h
  change IsIso ((fShriekModTensorSheafifyIso B Λ f F G).hom ≫
    (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) v} Λ)).map
      (modFiniteSupportTensorPresheafMap B Λ f F G) ≫
    (fShriekModSheafifyIso.{u, v, max (u + 1) v} B Λ f
      (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))).inv)
  infer_instance

/-- The projection map of presheaves is the bilinear recipe over each test object. -/
public theorem modFiniteSupportTensorPresheafMap_app
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property) :
    (modFiniteSupportTensorPresheafMap B Λ f F G).app (op V) =
      modFiniteSupportTensorBilinear B Λ f F G V :=
  rfl

/-- **The germ of the projection map.** At a geometric point `ȳ` of `Y`, the stalk of
`AlgebraicGeometry.SmallEtale.modFiniteSupportTensorPresheafMap` sends the germ at a pointed
étale neighbourhood `V` of `ȳ` of a section of `f_{p!}F ⊗_Λ G` over `V` to the germ of its
image. Composed with
`CategoryTheory.GrothendieckTopology.Point.tensorHom_comp_toPresheafFiber_μ`, which says that
the germ of a pure tensor is the tensor of the germs, this is the source's germ-level
description: the germ of `x ⊗ t` goes to the germ of `x ⊗ f^{-1}t`. -/
public theorem toPresheafFiber_modFiniteSupportTensorPresheafMap
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (s : GeometricPoint Y.obj)
    (V : SmallEtale B Y.obj Y.property)
    (y : (geometricPointFiber B Y.obj Y.property s).obj V) :
    (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V y
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj F ⊗ G.obj) ≫
        (geometricPointSitePoint B Y.obj Y.property s).presheafFiber.map
          (modFiniteSupportTensorPresheafMap B Λ f F G) =
      modFiniteSupportTensorBilinear B Λ f F G V ≫
        (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V y
          ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
            (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G))) :=
  ((geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber_naturality
    (modFiniteSupportTensorPresheafMap B Λ f F G) V y).trans
      (congrArg (fun m => m ≫ (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V y
        ((modFiniteSupportPresheaf.{u, v, max (u + 1) v} B Λ f).obj
          (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)))
        (modFiniteSupportTensorPresheafMap_app B Λ f F G V))

end AlgebraicGeometry.SmallEtale

end
