module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.TorAmplitude.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Objects perfect relative to a base ring

Let `R → A` be a flat ring map of finite presentation. An object of `D(A)` is *perfect relative
to `R`* when it is pseudo-coherent over `A` and its restriction of scalars to `R` has finite Tor
dimension. This file introduces the predicate; the closure properties of the resulting class
(Stacks 0DHT–0GHJ) sit beside it.

## Main definitions

* `PseudoCoherence.IsRelativelyPerfect` (Stacks 0DHS).

## Implementation notes

Restriction from `A` to `R` is induced on derived categories by the exact restriction-of-scalars
functor. The ring, algebra and module carrier universes are independent; both module categories
use the common carrier universe `max u v w`.

Both notions this definition is built from belong to Chapter 15 section 65/66:
pseudo-coherence over `A` is `StacksDraft.PseudoCoherence.IsPseudoCoherent`
(tag 064Q (2)) and finite Tor dimension over `R` is
`StacksDraft.TorAmplitude.HasFiniteTorDimension` (tag 0652 (2)). This module cites those rather
than restating either, so there is one provider of each in the tree.

The derived tensor product is not yet packaged canonically, so finite Tor dimension carries its
functor, comparison transformation and universal property as arguments: a
datum certified as a *total left derived* functor of termwise tensoring, not merely a
triangulated one.

## References

* [The Stacks Project, Definition 15.85.1 (0DHS)](https://stacks.math.columbia.edu/tag/0DHS)
-/

open CategoryTheory

namespace PseudoCoherence

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0DHS.** For a flat, finitely presented ring map `R → A`, an object `K` of `D(A)` is
perfect relative to `R` if it is pseudo-coherent over `A` and its restriction of scalars has
finite Tor dimension over `R`. -/
@[stacks 0DHS, sga "6 III 4.1" "affine, flat f.p. case"]
public def IsRelativelyPerfect
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{max u v w} R) ⥤
        DerivedCategory (ModuleCat.{max u v w} R) ⥤ DerivedCategory (ModuleCat.{max u v w} R))
    (comparison : ∀ M : ModuleCat.{max u v w} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{max u v w} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{max u v w} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{max u v w} A)) : Prop :=
  StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
    StacksDraft.TorAmplitude.HasFiniteTorDimension derivedTensor comparison isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)

end PseudoCoherence
