module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Extensions
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Coreflection

/-!
# The adequate functors are a weak Serre subcategory

Let `A` be a ring. The adequate module-valued functors on the commutative `A`-algebras form a
weak Serre subcategory of all module-valued functors: they are a strictly full subcategory, they
contain the zero functor, and they are closed under kernels, cokernels and extensions. This is
the third assertion of part (1) of [Stacks, Tag 06Z7], the two others — that the inclusion `i` is
fully faithful and exact — being `AdequateFunctor.fullyFaithful_adequateInclusion`,
`AdequateFunctor.preservesFiniteLimits_adequateInclusion` and
`AdequateFunctor.preservesFiniteColimits_adequateInclusion`.

## Main results

* `AdequateFunctor.adequate_isClosedUnderExtensions` — the adequate functors are closed under
  extensions, which is [Stacks, Tag 06V8] read as a closure property of
  `AdequateFunctor.adequate`.
* `AdequateFunctor.adequate_isWeakSerreClass` — the image of `i` is a weak Serre subcategory.

## Implementation notes

Four of the five closure conditions of `CategoryTheory.ObjectProperty.IsWeakSerreClass` are
already instances on `AdequateFunctor.adequate`: containing zero and closure under isomorphisms,
kernels ([Stacks, Tag 06V3]) and cokernels ([Stacks, Tag 06V2]). Only closure under extensions
was missing, and it is [Stacks, Tag 06V8].

The value universe and the universe of the algebra carriers are both the universe of the base
ring, as in `AdequateFunctor.isAdequate_of_shortExact`. This is the instantiation in which the
source reads the lemma: for `A : Type u`, the source's `Alg_A` is the category of `A`-algebras,
which is `CommAlgCat.{u} A`, and `adequate.{u, u, u} A` is adequacy as a property of the
module-valued functors on exactly that category.

The three other assertions of part (1) are proved in
`StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Coreflection` at the wider
`adequate.{u, v, max u v w}`, where the algebra carriers may lie in a universe above that of `A`
and the values in a universe above that again. That extra generality goes beyond the source
rather than being demanded by it, and it is not available for closure under extensions:
[Stacks, Tag 06V8] rests on the splitting of [Stacks, Tag 06V7], whose proof evaluates the
functors on test algebras built from a presentation and is therefore written with the values and
the algebra carriers in one universe. `adequateInclusion_fullyFaithful_exact_isWeakSerreClass`
records that all four assertions nevertheless hold simultaneously for one and the same category,
which is what part (1) asserts.

## References

* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-- The adequate functors are closed under extensions: this is [Stacks, Tag 06V8] stated as a
closure property of the object property `AdequateFunctor.adequate`. -/
public instance adequate_isClosedUnderExtensions :
    (adequate.{u, u, u} A).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := isAdequate_of_shortExact _ hS h₁ h₃

/-- **Stacks Project, Tag 06Z7**, part (1), the image of `i` is a weak Serre subcategory. The
adequate module-valued functors are a strictly full subcategory containing the zero functor and
closed under kernels, cokernels and extensions, which is the characterisation of a weak Serre
subcategory of [Stacks, Tag 0754]. -/
@[stacks 06Z7 "part (1), the image of i is a weak Serre subcategory"]
public instance adequate_isWeakSerreClass :
    (adequate.{u, u, u} A).IsWeakSerreClass where

/-- **Stacks Project, Tag 06Z7**, part (1), in full and at one instantiation: the inclusion `i`
of the adequate module-valued functors into all module-valued functors on `Alg_A` is fully
faithful and exact, and its image is a weak Serre subcategory.

The three conjuncts other than the last are instantiations of
`AdequateFunctor.fullyFaithful_adequateInclusion`,
`AdequateFunctor.preservesFiniteLimits_adequateInclusion` and
`AdequateFunctor.preservesFiniteColimits_adequateInclusion`, which hold at the wider
`adequate.{u, v, max u v w}`; the last holds at the universes of
`AdequateFunctor.isAdequate_of_shortExact`. This conjunction records that all four are
simultaneously available for one and the same category, namely the module-valued functors on the
`A`-algebras whose carriers lie in the universe of `A`. -/
@[stacks 06Z7 "part (1)"]
public theorem adequateInclusion_fullyFaithful_exact_isWeakSerreClass :
    (adequate.{u, u, u} A).ι.Full ∧ (adequate.{u, u, u} A).ι.Faithful ∧
      PreservesFiniteLimits (adequate.{u, u, u} A).ι ∧
      PreservesFiniteColimits (adequate.{u, u, u} A).ι ∧
      (adequate.{u, u, u} A).IsWeakSerreClass :=
  ⟨(fullyFaithful_adequateInclusion.{u, u, u} A).full,
    (fullyFaithful_adequateInclusion.{u, u, u} A).faithful,
    preservesFiniteLimits_adequateInclusion.{u, u, u} A,
    preservesFiniteColimits_adequateInclusion.{u, u, u} A,
    adequate_isWeakSerreClass A⟩

end AdequateFunctor

end
