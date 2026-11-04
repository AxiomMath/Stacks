module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPushforward

/-!
# `(Ri_*E)|_U ≅ R(i|_V)_*(E|_V)`: the restriction square on derived categories

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding, let `U` be an open subspace of `X` and let `V = i⁻¹U`. The module-level square
`AlgebraicGeometry.RingedSpace.restrictPushforwardIso` says that pushing an `𝒪_Z`-module forward
along `i` and restricting it to `U` is restricting it to `V` and pushing it forward along
`i|_V : Z|_V ⟶ X|_U`. All four functors in that square are exact, so the square descends to
derived categories, and this file proves the descended form.

That is the shape the induction of Stacks 09VA needs. The induction lives in `D(𝒪_Z)`, while
the pseudo-coherence predicate it has to establish on `X` is local on `X` and phrased through
restriction to an open subspace; the square below is what turns a statement about `E|_V` on the
open subspace `V` of `Z` into a statement about `(Ri_*E)|_U` on the open subspace `U` of `X`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardIso`:
  `Ri_* ⋙ (·)|_U ≅ (·)|_V ⋙ R(i|_V)_*` as functors `D(𝒪_Z) ⥤ D(𝒪_{X|U})`.
* `AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardObjIso`: the same at an object,
  `(Ri_*E)|_U ≅ R(i|_V)_*(E|_V)`, which is the form a consumer applies.

## Implementation notes

Nothing is computed. Both legs of the derived square are the functor induced on derived
categories by a composite of two exact functors, and
`CategoryTheory.Functor.mapDerivedCategoryCompIso` identifies such a functor with the composite
of the two induced functors. Applying it to the module-level square on one side and to the
identity isomorphism on the other gives two descriptions of
`(restrictModules Z V ⋙ pushforwardOXMod (i|_V)).mapDerivedCategory`, and the square is their
difference.

The exactness of the composite `restrictModules Z V ⋙ pushforwardOXMod (i|_V)` has to be
introduced as a local instance: `CategoryTheory.Limits.comp_preservesFiniteLimits` and
`CategoryTheory.Limits.comp_preservesFiniteColimits` are lemmas and not instances. Right
exactness of `(i|_V)_*` needs the restricted morphism to be a closed embedding, which is
`AlgebraicGeometry.RingedSpace.isClosedEmbedding_restrictHom`.

`AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` is used as the canonical `Ri_*` and
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` as the canonical derived restriction;
neither is rebuilt here, because `CategoryTheory.Limits.PreservesFiniteColimits` is data and a
rebuilt functor would not be provably the same one.

Universes: the derived categories of `Z` and of `X` share one universe parameter and those of
`Z|_V` and `X|_U` share another, because
`AlgebraicGeometry.RingedSpace.derivedPushforwardOXMod` is stated with a single universe for
source and target.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (U : Opens X.carrier)
  [HasDerivedCategory.{d} (OXMod.{u, u} Z)] [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
  [HasDerivedCategory.{d'}
    (OXMod.{u, u} (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding))]

/-- **`(Ri_*E)|_U ≅ R(i|_V)_*(E|_V)`**, naturally in the object `E` of `D(𝒪_Z)`: the derived
form of `AlgebraicGeometry.RingedSpace.restrictPushforwardIso`.

Pushing forward along a morphism of ringed spaces `i : Z ⟶ X` whose underlying map is a closed
embedding, and restricting to an open subspace `U` of `X`, agrees on derived categories with
restricting to `V = i⁻¹U` and pushing forward along `i|_V : Z|_V ⟶ X|_U`.

Both legs are the derived functor of one and the same exact composite
`restrictModules Z V ⋙ pushforwardOXMod (i|_V)`: the left leg by the module-level square, the
right leg by definition. -/
public def derivedRestrictPushforwardIso (hi : Topology.IsClosedEmbedding i.hom.base) :
    derivedPushforwardOXMod i hi ⋙ derivedRestrictModules X U ≅
      derivedRestrictModules Z ((Opens.map i.hom.base).obj U) ⋙
        derivedPushforwardOXMod (restrictHom i U) (isClosedEmbedding_restrictHom i U hi) := by
  haveI := preservesFiniteColimits_pushforwardOXMod i hi
  haveI := preservesFiniteColimits_pushforwardOXMod (restrictHom i U)
    (isClosedEmbedding_restrictHom i U hi)
  haveI : PreservesFiniteLimits (restrictModules Z ((Opens.map i.hom.base).obj U) ⋙
      pushforwardOXMod (restrictHom i U)) := comp_preservesFiniteLimits _ _
  haveI : PreservesFiniteColimits (restrictModules Z ((Opens.map i.hom.base).obj U) ⋙
      pushforwardOXMod (restrictHom i U)) := comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIso (restrictPushforwardIso i U) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl
      (restrictModules Z ((Opens.map i.hom.base).obj U) ⋙
        pushforwardOXMod (restrictHom i U)))).symm

/-- **`(Ri_*E)|_U ≅ R(i|_V)_*(E|_V)`** at a single object `E` of `D(𝒪_Z)`.

This is `AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardIso` evaluated at `E`, the
form in which a localization step consumes the square: pseudo-coherence of `Ri_*E` on `X` is
tested on open subspaces `U` of `X`, and this identifies the object to be approximated there
with the pushforward along `i|_V` of the restriction of `E` to `V = i⁻¹U`. -/
public def derivedRestrictPushforwardObjIso (hi : Topology.IsClosedEmbedding i.hom.base)
    (E : DerivedCategory (OXMod.{u, u} Z)) :
    (derivedRestrictModules X U).obj ((derivedPushforwardOXMod i hi).obj E) ≅
      (derivedPushforwardOXMod (restrictHom i U)
          (isClosedEmbedding_restrictHom i U hi)).obj
        ((derivedRestrictModules Z ((Opens.map i.hom.base).obj U)).obj E) :=
  (derivedRestrictPushforwardIso i U hi).app E

end AlgebraicGeometry.RingedSpace

end
