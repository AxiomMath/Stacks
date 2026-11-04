module

public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
import StacksCore.Tactic.StacksAttribute

/-!
# Principality of the determinantal ideals does not depend on the representative

Let `A` be a ring, `f ∈ A` a nonzerodivisor, and let `M^•` and `N^•` be bounded complexes of
finite free `A`-modules representing the same object of `D(A)`. Tag 0GSS identifies the
determinantal ideals up to a power of `f`: `f^m · I_i(M^•, f) = f^n · I_i(N^•, f)` for suitable
exponents. Since `f` is a nonzerodivisor, that identification transports principality in both
directions, so "the determinantal ideals are principal" is a property of the object of `D(A)`
rather than of the complex chosen to represent it.

## Main results

* `Ideal.isPrincipal_of_pow_mul_eq`: if `f` is a nonzerodivisor and `f^m · I = f^n · J` with `I`
  principal, then `J` is principal.
* `Stacks.Eta.DeterminantalIdeal.isPrincipal_idealI_of_derived_iso`: principality of the
  determinantal ideals is inherited by any other representative of the same object of `D(A)`.

## Implementation notes

The cancellation is elementary and stated for arbitrary ideals, with no reference to complexes:
a generator of `J` is extracted from the element of `f^n · J` corresponding to `f^m` times a
generator of `I`, and the comparison of an arbitrary element of `J` with it is cancelled by the
nonzerodivisor `f^n`. No nontriviality of `A` is assumed, so the cancellation goes through the
defining property of `nonZeroDivisors` rather than through `mul_left_cancel₀`.

The exponents that Tag 0GSS requires are constrained only by an equation between integers, so
they can always be chosen: taking the two truncated differences of the alternating rank sums
satisfies it whichever of the two is larger.

## References

* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 0F7V](https://stacks.math.columbia.edu/tag/0F7V)
-/

@[expose] public section

open CategoryTheory

universe u

/-- If `f` is a nonzerodivisor and `f^m · I = f^n · J` as ideals, then `J` is principal as soon
as `I` is: a generator of `J` is the element whose product with `f^n` is `f^m` times a generator
of `I`. -/
public theorem Ideal.isPrincipal_of_pow_mul_eq {A : Type u} [CommRing A] {f : A}
    (hf : f ∈ nonZeroDivisors A) {I J : Ideal A} {m n : ℕ}
    (h : Ideal.span {f ^ m} * I = Ideal.span {f ^ n} * J)
    (hI : I.IsPrincipal) : J.IsPrincipal := by
  obtain ⟨a, rfl⟩ := hI
  have hmem : f ^ m * a ∈ Ideal.span {f ^ n} * J := by
    rw [← h]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Submodule.mem_span_singleton_self a)
  obtain ⟨b, hbJ, hb⟩ := Ideal.mem_span_singleton_mul.1 hmem
  refine ⟨b, le_antisymm (fun x hxJ => ?_) (Submodule.span_le.2 (Set.singleton_subset_iff.2 hbJ))⟩
  have hx : f ^ n * x ∈ Ideal.span {f ^ m} * Submodule.span A {a} := by
    rw [h]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hxJ
  obtain ⟨y, hyI, hy⟩ := Ideal.mem_span_singleton_mul.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyI
  refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
  rw [smul_eq_mul] at hy ⊢
  rw [eq_comm, ← sub_eq_zero]
  exact (mem_nonZeroDivisors_iff.1 (pow_mem hf n)).2 _ (by linear_combination -c * hb - hy)

namespace Stacks.Eta.DeterminantalIdeal

attribute [local instance] HasDerivedCategory.standard

/-- **Principality of the determinantal ideals is a property of the object of `D(A)`.** If two
bounded complexes of finite free modules represent the same object of the derived category and
the determinantal ideals of one are principal, then so are those of the other. -/
public theorem isPrincipal_idealI_of_derived_iso {A : Type u} [CommRing A] (f : A)
    (hf : f ∈ nonZeroDivisors A) (M N : BoundedComplex A) (i : ℤ)
    (hMN : Nonempty ((DerivedCategory.Q).obj M.toCochainComplex ≅
      (DerivedCategory.Q).obj N.toCochainComplex))
    (hM : (idealI M f i).IsPrincipal) : (idealI N f i).IsPrincipal := by
  obtain ⟨m, n, hmn⟩ : ∃ m n : ℕ, (m : ℤ) + M.tailEulerCharacteristic i
      = (n : ℤ) + N.tailEulerCharacteristic i :=
    ⟨(N.tailEulerCharacteristic i - M.tailEulerCharacteristic i).toNat,
     (M.tailEulerCharacteristic i - N.tailEulerCharacteristic i).toNat, by omega⟩
  exact Ideal.isPrincipal_of_pow_mul_eq hf
    (pow_mul_idealI_eq_of_derived_iso f hf M N i m n hMN hmn) hM

end Stacks.Eta.DeterminantalIdeal

end
