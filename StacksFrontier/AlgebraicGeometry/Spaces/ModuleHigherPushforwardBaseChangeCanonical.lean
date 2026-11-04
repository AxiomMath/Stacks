module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# The canonical base-change comparison for higher direct images of modules

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Stacks 03LX and Stacks 071Z assert `R^n f'_*(F|_{X'}) = (R^n f_*F)|_{Y'}`.
Read strictly, an equality of functors asserted by a source of this kind is the statement that
the *canonical comparison map* between the two sides is invertible — not merely that the two
sides are isomorphic by some map.  This file writes that canonical map down, in the degree in
which Stacks 071Z states it, and reduces its invertibility to a single underived statement.

`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`) carries
`@[stacks 071Z]` and has the right endpoints, but is not identified with the canonical map; its
own docstring records that, and so do the docstrings of the ordinary clause
(`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`) and of Stacks 03LR, part (1)
(`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso`).  Nothing here changes that
attribute: the declarations below do not close the gap, they localize it.

## Main definitions

* `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison`: the canonical base-change
  comparison `(f_*F)|_{Y'} ⟶ f'_*(F|_{X'})` of the square, in the étale-restriction spelling
  in which Stacks 03LX and Stacks 071Z are stated.
* `AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeComparison`: the canonical
  comparison `(R^n f_*F)|_{Y'} ⟶ R^n f'_*(F|_{X'})` in every degree `n`, built from the
  previous one by canonical steps only.

## Main results

* `AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison`: **the
  reduction.**  If the underived canonical comparison is invertible, then so is the canonical
  comparison in every degree.  So the whole of Stacks 071Z, read as a statement about the
  canonical map, follows from the single underived statement
  `IsIso (moduleEtaleBaseChangeComparison …)`, which is Stacks 03LX for the ordinary direct
  image read the same way.

## Implementation notes

*Why the underived map is the repo's own mate and not a new one.*
`AlgebraicGeometry.Space.moduleBaseChangeMap` is already the mate, across the two adjunctions
of Stacks 03LU, of the comparison of the two composite direct images around the square, and
`AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mateEquiv` records that.  It is stated with
`AlgebraicGeometry.Space.modulePullback` in the two horizontal slots, whereas Stacks 03LX and
Stacks 071Z are stated with `AlgebraicGeometry.Space.etaleModulePullback`, étale restriction.
The two agree by `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is
Stacks 03LW and is itself pinned as the canonical identification by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`; conjugating by it
therefore introduces no twist, and `moduleEtaleBaseChangeComparison` is the canonical map in
the spelling the two tags use.

*Why the derived comparison needs no further choice.*  Each of its three factors is canonical.
`CategoryTheory.Functor.rightDerivedCompIso` pulls an exact functor out of a right derived
functor; `CategoryTheory.NatTrans.rightDerived` is the functoriality of `rightDerived` in its
functor argument; and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` is the comparison of Stacks
015Z for a functor that is exact and preserves injectives, which is pinned on an arbitrary
injective resolution by
`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_eq` and in degree zero
by `Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_zero`.  So the derived
comparison is canonical as a function of the underived one, and the gap at Stacks 071Z is
exactly the gap at the ordinary clause of Stacks 03LX — it does not acquire a second,
independent component in positive degree.

*What is still owed, precisely.*  `IsIso (moduleEtaleBaseChangeComparison …)`.  It is reduced
further in `StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeUnitSquare.lean`:
`AlgebraicGeometry.Space.isIso_moduleEtaleBaseChangeComparison_of_unitSquare` derives it from a
single equation between two morphisms `f_*F ⟶ g_*f'_*(F|_{X'})` of `𝒪_Y`-modules, the square
made by the *units* of the two étale adjunctions of Stacks 03LU with the base-change
isomorphism `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` and the comparison of
the two composite direct images.  In particular no counit of
`AlgebraicGeometry.Space.modulePullbackAdjunction` is needed, which is what
`CategoryTheory.mateEquiv_symm_eq_of_unit` buys: the mate is recognised from its unit square.

At the level of sheaves of sets on the small étale *topoi* the statement corresponding to the
present one is proved — `AlgebraicGeometry.Space.isIso_properBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/SmallEtaleBaseChangeMate.lean`) is Stacks
03LR, part (1) for the canonical map — but that development lives at `Type (u + 1)`, whereas
the modules consume the `Type u` copies
`AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso` and
`AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso`, for which no mate characterization
exists; so it is not a route to the unit square either.

*The degree.*  The degree runs over `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, as in
`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`.

*Two local priority raises.*  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`, two global
instances stated at module universe `max u v r w` capture instance search for `Abelian` and
`EnoughInjectives` at module universe `u` and then fail on the universe constraint; raising the
priority of Mathlib's applicable instances sends search the right way.  Both attributes are
`local`.

## References

* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **The canonical base-change comparison of the ordinary direct images, in the
étale-restriction spelling.**  For a cartesian square of algebraic spaces whose bottom arrow `g`
is étale, the canonical map

`(f_*F)|_{Y'} ⟶ f'_*(F|_{X'})`,

natural in the `𝒪_X`-module `F`.

This is `AlgebraicGeometry.Space.moduleBaseChangeMap` — the mate, across the two adjunctions of
Stacks 03LU, of the comparison of the two composite direct images around the square — conjugated
into the étale-restriction spelling of Stacks 03LX by Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.  Since that identification is
itself canonical, this is the canonical comparison and not a twist of it.

Stacks 03LX for the ordinary direct image, read as a statement about the canonical map, is the
assertion that this is an isomorphism.  That assertion is not proved in this development;
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` is an isomorphism with these
endpoints which is not identified with this map. -/
noncomputable def moduleEtaleBaseChangeComparison (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    modulePushforward B S hS f ⋙ etaleModulePullback B S hS g hg ⟶
      etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        modulePushforward B S hS f' :=
  Functor.whiskerLeft (modulePushforward B S hS f)
      (modulePullbackIsoEtaleModulePullback B S hS g hg).inv ≫
    moduleBaseChangeMap f g f' i sq.w ≫
    Functor.whiskerRight
      (modulePullbackIsoEtaleModulePullback B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).hom
      (modulePushforward B S hS f')

/-- **The canonical base-change comparison of the higher direct images.**  For a cartesian
square of algebraic spaces whose bottom arrow `g` is étale, and with étale restriction along `i`
carrying injective `𝒪_X`-modules to injective `𝒪_{X'}`-modules, the canonical map

`(R^n f_*F)|_{Y'} ⟶ R^n f'_*(F|_{X'})`

for every `n`, natural in the `𝒪_X`-module `F`.

It is the composite of three canonical steps and introduces no choice of its own: pull the exact
functor `(-)|_{Y'}` out of the derived functor by
`CategoryTheory.Functor.rightDerivedCompIso`, apply `CategoryTheory.NatTrans.rightDerived` to the
underived canonical comparison `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison`, and
then move the exact injective-preserving functor `(-)|_{X'}` out of the derived functor by the
comparison of Stacks 015Z,
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.

Stacks 071Z, read as a statement about the canonical map, is the assertion that this is an
isomorphism; by
`AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison` that follows
from the underived assertion alone. -/
noncomputable def moduleHigherPushforwardEtaleBaseChangeComparison (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (h03F3 : (etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).PreservesInjectiveObjects)
    (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    (modulePushforward B S hS f).rightDerived n ⋙ etaleModulePullback B S hS g hg ⟶
      etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        (modulePushforward B S hS f').rightDerived n := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have := etaleModulePullback_additive B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := etaleModulePullback_additive B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteColimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  have := h03F3
  have : (etaleModulePullback B S hS g hg).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact (Functor.rightDerivedCompIso (modulePushforward B S hS f)
        (etaleModulePullback B S hS g hg) n).inv ≫
      NatTrans.rightDerived (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg) n ≫
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
        (etaleModulePullback B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (modulePushforward B S hS f') n).hom

/-- **Stacks 071Z reduces to the ordinary clause of Stacks 03LX, for the canonical maps.**  If
the canonical base-change comparison of the *ordinary* direct images is an isomorphism, then the
canonical base-change comparison of the higher direct images is an isomorphism in every degree.

All three factors of
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeComparison` are then invertible:
the outer two are components of isomorphisms, and the middle one is
`CategoryTheory.NatTrans.rightDerived` applied to an isomorphism, which is the hom of
`CategoryTheory.Functor.rightDerivedIsoOfNatIso`.

So nothing in positive degree is owed beyond the underived statement: the derived comparison
acquires no independent content. -/
theorem isIso_moduleHigherPushforwardEtaleBaseChangeComparison (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (h03F3 : (etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).PreservesInjectiveObjects)
    (hβ : IsIso (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg)) (n : ℕ) :
    IsIso (moduleHigherPushforwardEtaleBaseChangeComparison B S hS i f' f g sq hg h03F3 n) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
  have := etaleModulePullback_additive B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := etaleModulePullback_additive B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteColimits_etaleModulePullback B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  have := h03F3
  have : (etaleModulePullback B S hS g hg).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hmid : IsIso (NatTrans.rightDerived
      (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg) n) :=
    inferInstanceAs (IsIso (Functor.rightDerivedIsoOfNatIso
      (asIso (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg)) n).hom)
  exact inferInstanceAs (IsIso (_ ≫ _ ≫ _))

end AlgebraicGeometry.Space

end
