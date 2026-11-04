module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# An effective Cartier divisor loses a dimension

Let `X` be a scheme whose underlying space is Noetherian and let `D ⊆ X` be an effective Cartier
divisor.  If `dim X ≤ d + 1` then `dim D ≤ d`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor`: if the
  underlying space of `X` is Noetherian of dimension at most `d + 1`, an effective Cartier
  divisor on `X` has dimension at most `d`.

## Implementation notes

The drop is proved topologically: the support of `D` is closed and nowhere dense
(`AlgebraicGeometry.isNowhereDense_supportSet_of_isEffectiveCartierDivisor`), a closed nowhere
dense subset of a Noetherian space of dimension at most `d + 1` has dimension at most `d`
(`IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ`), and the subscheme `D` is
homeomorphic to its support.  Krull's principal ideal theorem gives the drop in the local ring at
a generic point of a component of `D` — Tag 0BCN
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`) and, in local
topological form, Tag 056N (`AlgebraicGeometry.topologicalKrullDimAt_subscheme_lt`) — and
assembling either into a bound on `dim D` still needs the component count that
`IsNowhereDense.topologicalKrullDim_add_one_le` performs.  So the nonzerodivisor hypothesis is
used here only through the empty interior.

Noetherianness of the space is necessary: the dimension of a nowhere dense closed subset of a
non-Noetherian space need not drop, and `IsNowhereDense.topologicalKrullDim_add_one_le` assumes
it.  No hypothesis on `X` is needed for the nowhere-density statement itself.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **An effective Cartier divisor on a scheme with Noetherian space of dimension at most
`d + 1` has dimension at most `d`.** -/
@[ega "IV 4.1.2.1" "rare ⇒ dim(Z) < dim(Y)", ega "IV 5.2.4" "special case"]
theorem topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [NoetherianSpace X] (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I) (d : ℕ)
    (hX : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim I.subscheme ≤ (d : WithBot ℕ∞) := by
  have hsupp : topologicalKrullDim I.supportSet ≤ (d : WithBot ℕ∞) :=
    IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ
      (isNowhereDense_supportSet_of_isEffectiveCartierDivisor I hI) I.isClosed_supportSet d hX
  have he : I.subscheme ≃ₜ (I.supportSet : Set X) :=
    I.subschemeι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr
        (show Set.range I.subschemeι.base = I.supportSet from I.range_subschemeι))
  exact le_of_eq_of_le (IsHomeomorph.topologicalKrullDim_eq _ he.isHomeomorph) hsupp

end AlgebraicGeometry

end
