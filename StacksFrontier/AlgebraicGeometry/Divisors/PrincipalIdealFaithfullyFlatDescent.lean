module

public import Mathlib.RingTheory.Ideal.Span
public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of membership in a principal ideal along a faithfully flat ring map

Let `R → S` be a faithfully flat ring map and let `a : R`. An element of `R` whose image in `S`
is a multiple of the image of `a` is already a multiple of `a`; consequently the principal ideal
`(a)` is recovered from its extension `(a)S` by contraction, and an ideal of `R` whose extension
to `S` is contained in `(a)S` is contained in `(a)`.

This is the elementwise half of faithfully flat descent for ideals, and it is what the étale
descent of local principality consumes: the defining ideal of a closed subspace on an affine
étale chart becomes a multiple of a single generator only after a further étale covering, and a
covering family of affine charts makes the product of their rings of global functions faithfully
flat over the ring of the chart, so each individual membership descends.

No finiteness of the ideal is needed anywhere: membership descends one element at a time.

## Main results

* `Stacks.Divisors.mem_span_singleton_of_map_mem_span_singleton`: membership in a principal ideal
  descends along a faithfully flat ring map.
* `Stacks.Divisors.comap_map_span_singleton`: the contraction of the extension of a principal
  ideal along a faithfully flat ring map is that principal ideal again.
* `Stacks.Divisors.le_span_singleton_of_map_le_span_singleton`: an ideal whose extension lands in
  the extension of a principal ideal lands in that principal ideal.

## Implementation notes

The descent is `Module.Descent.mem_range_of_one_tmul_mem_range`, which detects membership in the
image of an `R`-linear map by a faithfully flat base change. The principal ideal `(a)` is the
image of multiplication by `a`, `LinearMap.span_singleton_eq_range`, and the hypothesis is
transported to the required membership of `1 ⊗ₜ t` in the image of the base change by the
identification `S ⊗[R] R ≅ S` of `TensorProduct.rid`: it takes `1 ⊗ₜ t` to the image of `t` and
`c ⊗ₜ a` to `c` times the image of `a`, so the two pure tensors agree exactly when the given
factorisation holds in `S`.

## References

* [Stacks Project, Tag 05AY](https://stacks.math.columbia.edu/tag/05AY)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Divisors

/-- **Membership in a principal ideal descends along a faithfully flat ring map.** If the image
of `t` in `S` is a multiple of the image of `a`, then `t` is a multiple of `a` in `R`. -/
theorem mem_span_singleton_of_map_mem_span_singleton
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {a t : R}
    (h : algebraMap R S t ∈ Ideal.span ({algebraMap R S a} : Set S)) :
    t ∈ Ideal.span ({a} : Set R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have hrange : Ideal.span ({a} : Set R) = LinearMap.range (LinearMap.toSpanSingleton R R a) := by
    rw [← LinearMap.span_singleton_eq_range]
  rw [hrange]
  refine Module.Descent.mem_range_of_one_tmul_mem_range R S _ ⟨c ⊗ₜ[R] (1 : R), ?_⟩
  have h1 : (LinearMap.lTensor S (LinearMap.toSpanSingleton R R a)) (c ⊗ₜ[R] (1 : R))
      = c ⊗ₜ[R] a := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    simp
  rw [h1]
  refine (TensorProduct.rid R S).injective ?_
  rw [TensorProduct.rid_tmul, TensorProduct.rid_tmul, Algebra.smul_def, Algebra.smul_def,
    mul_one, ← hc]
  ring

/-- **The contraction of the extension of a principal ideal along a faithfully flat ring map is
that ideal.** -/
@[ega "0 6.6.1" "(a), special case"]
theorem comap_map_span_singleton
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (a : R) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (Ideal.span ({a} : Set R))) =
      Ideal.span ({a} : Set R) := by
  refine le_antisymm (fun t ht => ?_) (fun t ht => Ideal.mem_comap.2 (Ideal.mem_map_of_mem _ ht))
  refine mem_span_singleton_of_map_mem_span_singleton S ?_
  have ht' := Ideal.mem_comap.1 ht
  rwa [Ideal.map_span, Set.image_singleton] at ht'

/-- **An ideal whose extension along a faithfully flat ring map lies in the extension of a
principal ideal lies in that principal ideal.** -/
theorem le_span_singleton_of_map_le_span_singleton
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {a : R} {I : Ideal R}
    (h : ∀ t ∈ I, algebraMap R S t ∈ Ideal.span ({algebraMap R S a} : Set S)) :
    I ≤ Ideal.span ({a} : Set R) :=
  fun _ ht => mem_span_singleton_of_map_mem_span_singleton S (h _ ht)

end Stacks.Divisors

end
