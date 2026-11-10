module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The images of a cocone on a direct system in a Noetherian module stabilize

Let `G` be a direct system of modules over a ring `R`, indexed by `ℕ`, and let `β n : G n → L`
be a compatible family of maps into a single `R`-module `L`. The images of the `β n` increase
with `n`, so if `L` is Noetherian they are constant from some index on.

This is the one place a *uniform* index enters an argument about a direct system: the index
depends on `L` and on the cocone, and not on any term of the system, so it may be chosen before
anything is said about the individual terms.

## Main results

* `Stacks.exists_range_stabilizes` — the images of a compatible family of maps into a Noetherian
  module are eventually constant.

## Implementation notes

The hypothesis is `IsNoetherian R L` rather than `Module.Finite R L`: Noetherianness of the
receiving module is all the argument uses, and it is what the chain condition
`monotone_stabilizes_iff_noetherian` is stated against. For a finite module over a Noetherian
ring the instance is found by `inferInstance`.

`L` is an ordinary module rather than an object of `ModuleCat R`, and its universe is free of
the system's: a cocone whose vertex is a module over a *larger* ring, Noetherian there and not
over `R`, is reached by applying this with `R` that larger ring, which is how the route of
[Stacks, Tag 0EHK] uses it — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisDualModel` for why no vertex
Noetherian over the base ring exists there.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks

/-- **The images of a cocone on a direct system in a Noetherian module are eventually
constant.** For a direct system `G` of `R`-modules indexed by `ℕ` and maps `β n : G n → L`
compatible with the transition maps, the submodules `im(β n)` of `L` form an ascending chain, so
if `L` is Noetherian there is an index `a` beyond which they do not grow. -/
theorem exists_range_stabilizes {R : Type u} [Ring R] (G : ℕ ⥤ ModuleCat.{v} R) {L : Type w}
    [AddCommGroup L] [Module R L] [IsNoetherian R L] (β : ∀ n : ℕ, G.obj n →ₗ[R] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m) :
    ∃ a : ℕ, ∀ (n : ℕ), a ≤ n → LinearMap.range (β a) = LinearMap.range (β n) :=
  monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R L)
    ⟨fun n => LinearMap.range (β n), fun m n h => by
      change LinearMap.range (β m) ≤ LinearMap.range (β n)
      rw [← hβ m n h]
      exact LinearMap.range_comp_le_range _ _⟩

end Stacks

end
