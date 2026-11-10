module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexOfAFamily

/-!
# The sheaf-level Čech complex at the small étale site

Let `S` be a scheme of a big étale site, let `X` be an object of its small étale site and let
`{U_i → X}` be a family of morphisms of that site.  This file instantiates the sheaf-level Čech
complex of `Stacks.CechSite.SheafLevel.complexFunctor` at `(X_étale, 𝒪_X)`: a cochain complex
of `𝒪`-modules on the small étale site of `S` whose degree-`p` term is

`∏_{(i_0, …, i_p)} j_{U_{i_0} ×_X ⋯ ×_X U_{i_p}, *} j^{-1} ℱ`,

the product over the `(p+1)`-tuples of members of the family of the direct images of the
restrictions of `ℱ` to the iterated fibre products.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafLevelCechComplex`: the complex, as a functor of the
  `𝒪`-module.

## Why this is here

It is the complex the Čech route to the étale half of [Stacks, Tag 071N] above degree zero
needs, and it records that the general construction *reaches this site*: every instance the
general statement asks for is found here, namely `HasBinaryProducts` on the small étale site
(`AlgebraicGeometry.SmallEtale.hasBinaryProducts_smallEtale`, itself assembled from the
terminal object and fibre products), sheafification and local bijectivity of abelian groups on
each localized topology, products in the category of `𝒪`-modules, and the iterated fibre
products of the family in the slice.  The universes do not collide: the objects of the small
étale site sit one universe above its modules, and the general construction leaves the module
universe free.

**This is the complex, not a resolution.**  The augmentation `ℱ[0] ⟶ K` is instantiated in
the module
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafLevelCechAugmentation`,
and is a quasi-isomorphism *when the family covers the final object* — which the construction
below does not require of it — by
`AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSheafLevelCechExactness.lean`.
That is what supplies the `[QuasiIso ε]` hypothesis of
`AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic`.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Products of `𝒪`-modules on the small étale site, supplied directly: instance search for
them times out under Lean v4.35.0. -/
local instance : HasProducts.{u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  fun J => SheafOfModules.hasLimitsOfShape (Discrete J) _

/-- **The sheaf-level Čech complex of a family of morphisms of the small étale site.**  For a
family `{U_i → X}` of morphisms of `X_étale` with fixed target, the cochain complex of
`𝒪`-modules whose degree-`p` term is the product, over the `(p+1)`-tuples `(i_0, …, i_p)`, of
the direct image of the restriction of the module to `U_{i_0} ×_X ⋯ ×_X U_{i_p}`, with the
alternating Čech differential; functorially in the module.

No hypothesis is placed on the family: it is not required to be covering, nor finite.  Those
enter only when one asks for the augmentation to be a quasi-isomorphism, which is not proved
anywhere. -/
noncomputable abbrev sheafLevelCechComplex {X : SmallEtale B S hS}
    (E : PreZeroHypercover.{u} X) :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤
      CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℕ :=
  Stacks.CechSite.SheafLevel.complexFunctor (structureSheaf B S hS) E

end AlgebraicGeometry.SmallEtale

end
