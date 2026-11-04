module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.WeakAssPushforward

/-!
# Associated points of a pushforward outside the image

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F` be a
quasi-coherent `𝒪_X`-module. A point of `S` outside the image of `f` is not associated to
`f_* F`.

This is [Stacks, Tag 0EY0] part (2).

## Main results

* `not_isAssociatedPoint_pushforward_of_not_mem_range`: **[Stacks, Tag 0EY0] part (2)**, a point
  outside the image is not associated to the pushforward.

## Implementation notes

The pushforward is Mathlib's `Scheme.Modules.pushforward`, association is
`Stacks.Divisors.IsAssociatedPoint` and weak association is
`Stacks.Divisors.IsWeaklyAssociatedPoint`.

The source states part (2) for `𝒪_{S,s}` Noetherian, where it deduces the claim from part (1)
through the agreement of the associated and the weakly associated points over a finitely
generated maximal ideal, [Stacks, Tag 05AR]. Noetherianity is not assumed here: only the easy
inclusion `Ass(F) ⊆ WeakAss(F)` of [Stacks, Tag 05AM] is needed, which holds at every point of
every scheme. Dropping a hypothesis the conclusion does not need is a strengthening.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0AVN](https://stacks.math.columbia.edu/tag/0AVN)
* [Stacks Project, Tag 05AM](https://stacks.math.columbia.edu/tag/05AM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.PushforwardRegularity

/-- Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F` be a
quasi-coherent `𝒪_X`-module. A point of `S` outside the image of `f` is not an associated point
of `f_* F`. -/
@[stacks 0EY0 "outside_association"]
public theorem not_isAssociatedPoint_pushforward_of_not_mem_range {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (s : S)
    (hs : s ∉ Set.range f) :
    ¬ Stacks.Divisors.IsAssociatedPoint ((Scheme.Modules.pushforward f).obj F) s := fun h =>
  WeakAssPushforward.not_isWeaklyAssociatedPoint_pushforward_of_not_mem_range f F s hs
    (_root_.AlgebraicGeometry.associatedPoints_subset_weaklyAssociatedPoints _ h)

end Stacks.AlgebraicGeometry.PushforwardRegularity

end
