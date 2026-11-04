module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of the fibre product of a scheme with itself

For a morphism of schemes `f : X ⟶ S`, writing `|X|` for the underlying set of `X`, the natural
map `|X ×_S X| → |X| ×_{|S|} |X|` is surjective: any two points of `X` with the same image in
`S` are the two projections of a single point of the scheme-theoretic fibre product.

## Main results

* `AlgebraicGeometry.Scheme.pullbackComparison_forget_self_surjective` — surjectivity of the
  comparison map on underlying sets.
* `AlgebraicGeometry.Scheme.exists_preimage_pullback_self` — the same statement read pointwise.

## Implementation notes

Both results are the diagonal case `g = f` of Mathlib's
`AlgebraicGeometry.Scheme.pullbackComparison_forget_surjective` and
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`, which are stated for an arbitrary
pair of morphisms with target `S`. The source states the surjectivity of the comparison map and
then its pointwise reading, so both spellings are recorded here.

## References

* [Stacks Project, Tag 02KI](https://stacks.math.columbia.edu/tag/02KI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- **Stacks 02KI.** For a morphism of schemes `f : X ⟶ S` the natural map
`|X ×_S X| → |X| ×_{|S|} |X|` of underlying sets is surjective. -/
@[stacks 02KI]
public theorem pullbackComparison_forget_self_surjective {X S : Scheme.{u}} (f : X ⟶ S) :
    Function.Surjective (pullbackComparison forget f f) :=
  pullbackComparison_forget_surjective f f

/-- Stacks 02KI read pointwise: two points of `X` with the same image in `S` are the two
projections of a point of `X ×_S X`. -/
public theorem exists_preimage_pullback_self {X S : Scheme.{u}} (f : X ⟶ S) (x y : X)
    (h : f x = f y) :
    ∃ z : ↑(pullback f f), pullback.fst f f z = x ∧ pullback.snd f f z = y :=
  Pullback.exists_preimage_pullback x y h

end AlgebraicGeometry.Scheme

end
