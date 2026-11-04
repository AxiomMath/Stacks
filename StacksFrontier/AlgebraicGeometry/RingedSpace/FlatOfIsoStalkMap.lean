module

public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback

/-!
# Morphisms of ringed spaces with invertible germ maps are flat

A morphism of ringed spaces is flat when every germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` is a flat ring
homomorphism (`AlgebraicGeometry.IsFlat`). An invertible ring homomorphism is flat, so a morphism
whose germ maps are *isomorphisms* is flat.

This supplies inhabitants of the flatness hypothesis of Tags 02N4 and 02N5 that are not
isomorphisms of ringed spaces. The canonical one is the projection
`(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` attached to an arbitrary continuous map `i : Z ⟶ X`, whose germ maps
are isomorphisms by
`AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection` with no hypothesis on `i`
whatsoever, and which is as far from an isomorphism as `i` is: for `Z` a point it is the
inclusion of the local ring `𝒪_{X,x}` as a one-point ringed space over `X`, and `f_*` is then
the skyscraper functor.

## Main results

* `AlgebraicGeometry.isFlatAt_of_isIso_stalkMap` and `AlgebraicGeometry.isFlat_of_isIso_stalkMap`:
  invertible germ maps give flatness.
* `AlgebraicGeometry.RingedSpace.isFlat_inverseImageProjection`: the projection
  `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` is flat, for every continuous `i`.
* `RingedSpaceModuleAdjunction.preservesInjectiveObjects_modulePushforward_inverseImageProjection`:
  Tag 02N5 at that morphism — pushing an injective `i⁻¹𝒪_X`-module forward to `X` gives an
  injective `𝒪_X`-module.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of ringed spaces is flat at `x` as soon as its germ map at `x` is invertible:
a bijective ring homomorphism is flat. -/
theorem isFlatAt_of_isIso_stalkMap {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (x : X.carrier) (h : IsIso (f.hom.stalkMap x)) : AlgebraicGeometry.IsFlatAt f x :=
  RingHom.Flat.of_bijective ((ConcreteCategory.isIso_iff_bijective _).mp h)

/-- A morphism of ringed spaces all of whose germ maps are invertible is flat. -/
theorem isFlat_of_isIso_stalkMap {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (h : ∀ x : X.carrier, IsIso (f.hom.stalkMap x)) : AlgebraicGeometry.IsFlat f :=
  fun x => isFlatAt_of_isIso_stalkMap f x (h x)

namespace RingedSpace

/-- **The inverse-image projection is flat.** For any continuous map `i : Z ⟶ X` of topological
spaces, the canonical morphism of ringed spaces `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` is flat: its germ map
at `z` is the comparison `𝒪_{X, i z} ⟶ (i⁻¹𝒪_X)_z`, which is an isomorphism.

No hypothesis is placed on `i`, so this inhabits the flatness hypothesis of Tags 02N4 and 02N5
for every ringed space and every continuous map into its underlying space. -/
theorem isFlat_inverseImageProjection (X : AlgebraicGeometry.RingedSpace.{u, u})
    {Z : TopCat.{u}} (i : Z ⟶ X.carrier) :
    AlgebraicGeometry.IsFlat (AlgebraicGeometry.RingedSpace.inverseImageProjection X i) :=
  AlgebraicGeometry.isFlat_of_isIso_stalkMap _
    (AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection X i)

end RingedSpace

end AlgebraicGeometry

namespace RingedSpaceModuleAdjunction

/-- **Tag 02N5 at the inverse-image projection.** For any continuous `i : Z ⟶ X`, pushforward
along `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` carries injective `i⁻¹𝒪_X`-modules to injective
`𝒪_X`-modules. -/
theorem preservesInjectiveObjects_modulePushforward_inverseImageProjection
    (X : AlgebraicGeometry.RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier) :
    (modulePushforward
        (AlgebraicGeometry.RingedSpace.inverseImageProjection X i)).PreservesInjectiveObjects :=
  modulePushforward_preservesInjectiveObjects _
    (AlgebraicGeometry.RingedSpace.isFlat_inverseImageProjection X i)

end RingedSpaceModuleAdjunction

end
