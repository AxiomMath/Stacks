module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.WeakDimension.TorDimension

@[expose] public section

/-!
# Weak dimension of a ring

A commutative ring has weak dimension at most `d` when every module over it has Tor
dimension at most `d`.

## Main definitions

* `HasWeakDimensionLE`: every module over a ring has Tor dimension bounded by a fixed
  nonnegative integer.

## Main results

There are no results beyond the defining predicate.

## Implementation notes

The source assumes that the integer bound is nonnegative. Accordingly, the bound is indexed
by a natural number and coerced to an integer when passed to `HasTorDimensionLE`. As in that
definition, a derived tensor product is supplied together with its comparison map and
universal property.

Tor dimension is supplied by `StacksFrontier.RingTheory.WeakDimension.TorDimension`, which states
that one predicate locally pending a conceptual provider for Stacks Tag 0652; that tag belongs
to a different chapter cluster, so the overlay is deliberately untagged.

## References

* [The Stacks Project, Tag 092D](https://stacks.math.columbia.edu/tag/092D)
* [The Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

/-- A commutative ring has weak dimension at most `d` if every module over it has Tor
dimension at most `d`. -/
@[stacks 092D]
def HasWeakDimensionLE {A : Type u} [CommRing A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        ((tensoringRight (ModuleCat.{u} A)).obj N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (d : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} A,
    HasTorDimensionLE derivedTensor comparison isLeftDerived M d
