module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The inverse image of modules along an isomorphism of algebraic spaces

Let `e : X ≅ Y` be an isomorphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Pullback of `𝒪`-modules along `e.hom` is then an equivalence
`Modules Y ≌ Modules X`, with `e.inv` inducing the inverse.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_modulePullback_of_iso`: **the inverse image of
  `𝒪`-modules along an isomorphism of algebraic spaces is an equivalence of categories**, with no
  hypothesis whatever.

## Implementation notes

**The two unit laws of [Stacks Project, Tag 03LU] are all that is used**, and both are already
unconditional here: the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` and the identity comparison
`AlgebraicGeometry.Space.modulePullbackIdIso`.  Composing them along `e.inv_hom_id` and
`e.hom_inv_id` exhibits `e.inv^*` as a two-sided inverse of `e.hom^*` up to natural isomorphism,
and `CategoryTheory.Functor.IsEquivalence.mk'` turns that into an equivalence without asking for
the triangle identity.

**This is the unconditional form of a statement the tree had only conditionally.**
`AlgebraicGeometry.Space.modulePullbackEquivalence`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`) produces the
same equivalence from an `AlgebraicGeometry.Space.ModulePushforwardCoherence`.  That structure
**is** constructed unconditionally, by `AlgebraicGeometry.Space.modulePushforwardCoherence`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardIdIso.lean`), which assembles
it from the identity isomorphisms through
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso`.
Nothing of that coherence is needed for an isomorphism, so the conditional version is left where
it is and this one is stated beside it rather than replacing it; a consumer that only has an
isomorphism should use this.

The same statement for *ringed spaces* is
`Stacks.Cohomology.modulePullbackIso_isEquivalence`
(`StacksFrontier/Topology/Sheaves/Cohomology/CechAndResolutions/KInjectiveRestriction.lean`), and
this is its transcription to the small étale site of an algebraic space; the ringed-space one
does not apply here, `AlgebraicGeometry.Space.modulePullback` being a different functor on a
different site.

It is stated as a **theorem and not an instance**, following
`Stacks.Cohomology.modulePullbackIso_isEquivalence`: a consumer introduces it with `haveI`.  An
instance would be consulted by every search for `Functor.IsEquivalence` of a `modulePullback`,
and the universe behaviour of searches in this neighbourhood is delicate enough without one.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of `𝒪`-modules along an isomorphism of algebraic spaces is an
equivalence of categories**, unconditionally.

The inverse is the inverse image along `e.inv`: the two composition comparisons of [Stacks
Project, Tag 03LU] identify the two round trips with the inverse images along `e.inv ≫ e.hom`
and `e.hom ≫ e.inv`, which are identities, and the identity comparison identifies those with
the identity functors.

No `AlgebraicGeometry.Space.ModulePushforwardCoherence` is needed; see the module documentation
on `AlgebraicGeometry.Space.modulePullbackEquivalence`, which assumes one. -/
theorem isEquivalence_modulePullback_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) :
    (modulePullback B S hS e.hom).IsEquivalence := by
  let η : 𝟭 (Modules.{u, u} B S hS Y.1 Y.2) ≅
      modulePullback B S hS e.hom ⋙ modulePullback B S hS e.inv :=
    (modulePullbackIdIso B S hS Y).symm ≪≫
      (eqToIso (congrArg (modulePullback B S hS) e.inv_hom_id)).symm ≪≫
        (modulePullbackCompIso B S hS e.inv e.hom).symm
  let ε : modulePullback B S hS e.inv ⋙ modulePullback B S hS e.hom ≅
      𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
    modulePullbackCompIso B S hS e.hom e.inv ≪≫
      eqToIso (congrArg (modulePullback B S hS) e.hom_inv_id) ≪≫
        modulePullbackIdIso B S hS X
  exact Functor.IsEquivalence.mk' (modulePullback B S hS e.inv) η ε

end AlgebraicGeometry.Space

end
