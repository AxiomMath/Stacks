module

public import Mathlib.Algebra.Regular.SMul
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# A module on which the maximal ideal acts injectively has no closed-point associated prime

Let `R` be a local ring with maximal ideal `𝔪` and let `M` be an `R`-module. If some element of
`𝔪` acts injectively on `M`, then `𝔪` is not an associated prime of `M` in the sense of
[Stacks, Tag 00LA]: an `𝔪`-torsion element of `M` is, in particular, torsion for that one element,
hence zero, and then the annihilator of the zero element is all of `R`, not the proper ideal `𝔪`.

## Main results

* `not_isAssociatedPrimeStacks_maximalIdeal_of_isSMulRegular`: if `f ∈ 𝔪` acts regularly on `M`,
  then `𝔪` is not an associated prime of `M`.

## Implementation notes

This is the keystone of extending a section of a coherent triple's punctured-spectrum member
across the closed point one level up, in `Spec A` rather than in the closed fibre `Spec (A/fA)`:
the element `f` whose triple is being formed already acts injectively there by the triple's own
torsion-freeness, so this lemma applies with no further hypothesis, where the corresponding
statement for the closed-fibre member can genuinely fail. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertInduction`.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **The maximal ideal is not an associated prime of a module some element of it acts
regularly on.** If `f ∈ 𝔪` and multiplication by `f` is injective on `M`, then `𝔪` is not of the
form `Ann(m)` for any `m : M`: such an `m` would be killed by `f`, hence be zero, but the
annihilator of `0` is all of `R`, not the proper ideal `𝔪`. -/
public theorem not_isAssociatedPrimeStacks_maximalIdeal_of_isSMulRegular
    {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M f) :
    ¬ IsAssociatedPrimeStacks R M (IsLocalRing.maximalIdeal R) := by
  rintro ⟨-, m, hm⟩
  have hfmem : f ∈ (⊥ : Submodule R M).colon (Submodule.span R {m}) := by rw [hm]; exact hf
  have hfm0 : f • m = f • (0 : M) :=
    (Submodule.mem_colon_span_singleton.mp hfmem).trans (smul_zero f).symm
  have hm0 : m = 0 := hreg hfm0
  apply (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [← hm, hm0]
  ext r
  simp

end
