module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

@[expose] public section

/-!
# Tor dimension of a module over a commutative ring

This module states the single tor-dimension predicate needed to define the weak dimension of a
commutative ring, namely "the module `M` has tor dimension at most `d`", meaning that `M`
placed in degree zero has tor amplitude in `[-d, 0]`.

## Main definitions

* `HasTorDimensionLE`: the cohomology of `M[0] ⊗ᴸ N[0]` vanishes in every degree outside
  `[-d, 0]`, for every module `N`.

## Main results

There are no results beyond the defining predicate.

## Implementation notes

This is a *local* statement of the tor-dimension predicate, pending a conceptual provider for
Stacks Tag 0652, which states tor amplitude and tor dimension for an object of the derived
category `D(R)`. Tag 0652 belongs to a different chapter cluster, so its content is not
re-homed here: only the one predicate that weak dimension is defined against is stated, and
`HasTorDimensionLE` is **deliberately left untagged** so that Tag 0652's home stays free for
that cluster's own conceptual module.

Mathlib does not currently package the derived tensor product on `D(R)`. The predicate
therefore takes a bifunctor together with a comparison to termwise ordinary tensor product and
the universal property saying that each functor `- ⊗ᴸ N[0]` is its total left derived functor.
This characterizes the supplied bifunctor as the derived tensor product, rather than allowing
an arbitrary operation. Vanishing of a cohomology module is expressed categorically by
`IsZero`. The universal property is not consumed by the vanishing condition itself, so the
corresponding argument is named with a leading underscore.

The tor-amplitude condition is written out inline rather than factored through a separate
tor-amplitude predicate, which again belongs to Tag 0652. Doing so is faithful: the body below
is the `[-d, 0]` instance of tor amplitude for `M[0]`, and is the same proposition by `rfl`.

## References

* [The Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

/-- An `R`-module `M` has tor dimension at most `d` if `M[0]` has tor amplitude in `[-d, 0]`,
that is, if the cohomology of `M[0] ⊗ᴸ[R] N[0]` vanishes in every degree outside `[-d, 0]`
for every `R`-module `N`.

This is a local statement of the tor-dimension predicate, pending a conceptual provider for
Stacks Tag 0652, which is where tor amplitude and tor dimension in `D(R)` properly live. It is
deliberately left untagged so that Tag 0652's home stays free for the cluster that owns it.

The `comparison` and `_isLeftDerived` arguments certify that `derivedTensor` is the total left
derived functor of ordinary tensor product in the second variable. -/
def HasTorDimensionLE {R : Type u} [CommRing R]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        ((tensoringRight (ModuleCat.{u} R)).obj N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (_isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{u} R) (d : ℤ) : Prop :=
  ∀ (N : ModuleCat.{u} R) (i : ℤ), i ∉ Set.Icc (-d) 0 →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((derivedTensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)))

end
