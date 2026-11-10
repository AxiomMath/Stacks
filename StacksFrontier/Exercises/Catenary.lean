module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.RingTheory.Localization.Ideal
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Relative height and catenary rings and spaces

For prime ideals `q ≤ p` of a commutative ring `A`, the *relative height* of `p` over `q` is
the height of `p/q` in `A/q`. It is computed by two localizations: it is the Krull dimension of
`Aₚ/qAₚ`, which is proved below, and it is the Krull dimension of `(A/q)_(p/q)`, which is
Mathlib's `IsLocalization.AtPrime.ringKrullDim_eq_height`. The two localizations of `A/q`
appearing in the source are the same localization, because localizing at `p` inverts the image
of `A \ p`, the complement of `p/q`.

A Noetherian ring, or a topological space, is *catenary* when relative heights are additive
along chains of inclusions. The predicates recorded here state this by equality of lengths of
saturated chains, between prime ideals for `Ring.IsCatenary` and between irreducible closed
subsets for `TopologicalSpace.IsTopologicallyCatenary`. For a Noetherian ring that is the
additivity of the relative height in the source: the height of `p/q` is the supremum of the
lengths of the chains from `q` to `p`, and saturated chains from `p₁` to `p₂` and from `p₂` to
`p₃` concatenate to one from `p₁` to `p₃`. No separate relative-height function is needed; the
height of the image `p.map (Ideal.Quotient.mk q)` is Mathlib's `Ideal.height`.

## Main results

* `Ideal.ringKrullDim_quotient_localization_eq_height_map`: the Krull dimension of `Aₚ/qAₚ` is
  the height of `p/q`.

## References

* [Stacks Project, Tag 027O](https://stacks.math.columbia.edu/tag/027O)
-/

@[expose] public section

add_to_stacks 027O "relative_height" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_ega "0 16.1.3" "dim(A_p) = ht(p)" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_ega "0 16.3.1" "more general" IsLocalization.AtPrime.ringKrullDim_eq_height
add_to_stacks 027O "ring_catenary" Ring.IsCatenary
add_to_stacks 027O "space_catenary" TopologicalSpace.IsTopologicallyCatenary

namespace Ideal

/-- For `q ≤ p` with `p` prime, the Krull dimension of `Aₚ/qAₚ` is the height of the prime
ideal `p/q` of `A/q`. -/
@[stacks 027O "relative_height", ega "0 16.1.3" "(16.1.3.2)", ega "0 16.3.1" "more general"]
theorem ringKrullDim_quotient_localization_eq_height_map
    {A : Type*} [CommRing A] (q p : Ideal A) [p.IsPrime] (hqp : q ≤ p) :
    ringKrullDim
        (Localization.AtPrime p ⧸ q.map (algebraMap A (Localization.AtPrime p))) =
      ((p.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) := by
  let pbar := p.map (Ideal.Quotient.mk q)
  let : pbar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let : pbar.LiesOver p := ⟨by
    change p = pbar.comap (algebraMap A (A ⧸ q))
    simp [pbar, Ideal.Quotient.algebraMap_eq, Ideal.comap_map_mk hqp]⟩
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (A ⧸ q) p.primeCompl) (Localization.AtPrime pbar) := by
    rw [Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective pbar p
      Ideal.Quotient.mk_surjective]
    infer_instance
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.quotientEquiv p.primeCompl q
    (Localization.AtPrime p) (Localization.AtPrime pbar)).toRingEquiv]
  simpa [pbar] using
    (IsLocalization.AtPrime.ringKrullDim_eq_height pbar (Localization.AtPrime pbar))

end Ideal

end
