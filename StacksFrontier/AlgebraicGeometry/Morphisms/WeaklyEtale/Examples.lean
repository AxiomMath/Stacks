module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# Examples of weakly étale morphisms

A morphism of schemes `f : X ⟶ Y` is weakly étale if `f` and its diagonal
`X ⟶ X ×_Y X` are flat. This file records the basic sources of weakly étale morphisms:
a morphism `f` is weakly étale if it is

1. a flat monomorphism, since then the diagonal is an isomorphism;
2. an open immersion, as a special case of (1);
3. flat and unramified, since then the diagonal is an open immersion;
4. étale, since an étale morphism is flat and unramified.

## Main results

* `AlgebraicGeometry.WeaklyEtale.of_flat_of_mono`: a flat monomorphism is weakly étale.
* `AlgebraicGeometry.WeaklyEtale.of_isOpenImmersion`: an open immersion is weakly étale.
* `AlgebraicGeometry.WeaklyEtale.of_flat_of_formallyUnramified`: a flat, formally unramified
  morphism locally of finite type is weakly étale.
* `AlgebraicGeometry.WeaklyEtale.of_etale`: an étale morphism is weakly étale.

## Implementation notes

An unramified morphism of schemes in the sense of the Stacks Project is one that is locally of
finite type with vanishing sheaf of relative differentials; it is expressed here as the
conjunction of `AlgebraicGeometry.FormallyUnramified` and
`AlgebraicGeometry.LocallyOfFiniteType`.

## References

* [Stacks Project, Tag 094X](https://stacks.math.columbia.edu/tag/094X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.WeaklyEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A flat monomorphism of schemes is weakly étale: its diagonal is an isomorphism. -/
@[stacks 094X "(1) flat monomorphism"]
instance (priority := 900) of_flat_of_mono [Flat f] [Mono f] : WeaklyEtale f where

/-- An open immersion of schemes is weakly étale. -/
@[stacks 094X "(2) open immersion"]
theorem of_isOpenImmersion [IsOpenImmersion f] : WeaklyEtale f :=
  inferInstance

/-- A flat unramified morphism of schemes is weakly étale: its diagonal is an open immersion. -/
@[stacks 094X "(3) flat and unramified"]
instance (priority := 900) of_flat_of_formallyUnramified [Flat f] [FormallyUnramified f]
    [LocallyOfFiniteType f] : WeaklyEtale f where

/-- An étale morphism of schemes is weakly étale. -/
@[stacks 094X "(4) étale"]
theorem of_etale [Etale f] : WeaklyEtale f :=
  of_flat_of_formallyUnramified f

end AlgebraicGeometry.WeaklyEtale
