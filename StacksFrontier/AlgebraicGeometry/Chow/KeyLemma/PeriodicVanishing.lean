module

public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Defs

/-!
# The periodic complex of a pair of nonzerodivisors modulo their product

Let `A` be a commutative ring and `a, b ∈ A` nonzerodivisors. Multiplication by `a` and by `b`
are two endomorphisms of `A / abA` which annihilate each other, so they assemble into a
two-periodic complex

`A / abA --a--> A / abA --b--> A / abA`.

Its cohomology vanishes: the kernel of multiplication by `a` on `A / abA` is exactly the image
of multiplication by `b`, because `a z ∈ abA` forces `z ∈ bA` once `a` is a nonzerodivisor, and
symmetrically. Consequently its multiplicity — the additive Herbrand quotient
`AlgebraicGeometry.periodicLength` — is zero.

This is the step `e_A(A / abA, a, b) = 0` of the proof of the reciprocity relation
Stacks 0EAW: the whole sum of tame-symbol orders is compared against this vanishing
multiplicity, through the comparison map of Stacks 0EA9.

## Main results

* `AlgebraicGeometry.ker_lsmul_eq_range_lsmul` — the kernel of multiplication by `a` on
  `A / abA` is the image of multiplication by `b`.
* `AlgebraicGeometry.periodicLength_quotient_mul_eq_zero` — the multiplicity of the
  two-periodic complex `(A / abA, a, b)` is zero.
* `AlgebraicGeometry.isFiniteLength_homology_quotient_mul` — its cohomology has finite length,
  which is the hypothesis the comparison result of Stacks 0EA9 asks for.

## Implementation notes

The product is carried as a variable `c` together with the equation `c = a * b`, so that the
statements apply to both orderings of the two elements without rewriting inside a quotient
type. Multiplication by an element is Mathlib's `LinearMap.lsmul`, which is the shape the
two-periodic complex of `AlgebraicGeometry.twoPeriodicComplex` expects; the hypotheses that the
two differentials annihilate each other are supplied by
`AlgebraicGeometry.lsmul_mul_lsmul_eq_zero` and are left as arguments of the vanishing
statement so that it applies to any proofs of them.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Tag 0EA9](https://stacks.math.columbia.edu/tag/0EA9)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The multiplicity of a two-periodic complex, written out. This is `rfl`, and is stated so
that the definition is never unfolded by a rewrite: unfolding it generates an equation lemma in
the namespace of `AlgebraicGeometry.periodicLength`, which another module already carries. -/
private theorem periodicLength_eq_sub {R : Type u} [Ring R]
    (C : CochainComplex (ModuleCat.{v} R) (ZMod 2)) :
    periodicLength C = ((Module.length R (C.homology (0 : ZMod 2))).toNat : ℤ) -
      ((Module.length R (C.homology (1 : ZMod 2))).toNat : ℤ) := rfl

variable {A : Type u} [CommRing A]

/-- **The kernel of multiplication by `a` on `A / abA` is the image of multiplication by `b`.**
One inclusion is the vanishing of `ab`; for the other, `a z ∈ abA` says `a z = ab w`, and
cancelling the nonzerodivisor `a` gives `z = b w`. -/
theorem ker_lsmul_eq_range_lsmul {c : A} (a b : A) (ha : a ∈ nonZeroDivisors A)
    (hc : c = a * b) :
    LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {c}) a) =
      LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {c}) b) := by
  subst hc
  have key (d : A) (x : A ⧸ Ideal.span ({a * b} : Set A)) :
      LinearMap.lsmul A (A ⧸ Ideal.span ({a * b} : Set A)) d x =
        Ideal.Quotient.mk (Ideal.span ({a * b} : Set A)) d * x := by
    rw [LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  ext x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [LinearMap.mem_ker, LinearMap.mem_range, key, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩
    have hzw : z = b * w :=
      sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ha).2 _ (by
        rw [sub_mul, mul_comm z a, hw]; ring))
    exact ⟨Ideal.Quotient.mk _ w, by rw [← map_mul, hzw]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, Ideal.Quotient.eq] at hy
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hy
    have hz : z = b * d - a * b * g := by rw [← hg]; ring
    exact ⟨d - a * g, by rw [hz]; ring⟩

/-- Multiplication by `a` and by `b` annihilate each other on `A / abA`. -/
theorem lsmul_mul_lsmul_eq_zero (a b : A) :
    LinearMap.lsmul A (A ⧸ Ideal.span ({a * b} : Set A)) a *
      LinearMap.lsmul A (A ⧸ Ideal.span ({a * b} : Set A)) b = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Module.End.mul_apply, LinearMap.lsmul_apply, LinearMap.zero_apply, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.mpr ⟨z, by ring⟩

/-- **The cohomology of the two-periodic complex `(A / abA, a, b)` vanishes** in both degrees,
for `a` and `b` nonzerodivisors. -/
theorem length_homology_quotient_mul_eq_zero {c : A} (a b : A) (ha : a ∈ nonZeroDivisors A)
    (hb : b ∈ nonZeroDivisors A) (hc : c = a * b) (hfg hgf) (i : ZMod 2)
    (hi : i = 0 ∨ i = 1) :
    Module.length A ((twoPeriodicComplex
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) a)
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) b) hfg hgf).homology i) = 0 := by
  have h := homology_length_eq_ker_quotient
    (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) a)
    (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) b) hfg hgf i hi
  rcases hi with rfl | rfl
  · rw [h, Submodule.comap_subtype_eq_top.2 (ker_lsmul_eq_range_lsmul a b ha hc).le]
    simp [Module.length_eq_zero]
  · rw [h, Submodule.comap_subtype_eq_top.2
      (ker_lsmul_eq_range_lsmul b a hb (by rw [hc]; ring)).le]
    simp [Module.length_eq_zero]

/-- The cohomology of the two-periodic complex `(A / abA, a, b)` has finite length, which is
what the comparison result of Stacks 0EA9 asks of it. -/
theorem isFiniteLength_homology_quotient_mul {c : A} (a b : A) (ha : a ∈ nonZeroDivisors A)
    (hb : b ∈ nonZeroDivisors A) (hc : c = a * b) (hfg hgf) (i : ZMod 2) :
    IsFiniteLength A ((twoPeriodicComplex
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) a)
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) b) hfg hgf).homology i) := by
  have hall : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  rw [← Module.length_ne_top_iff,
    length_homology_quotient_mul_eq_zero a b ha hb hc hfg hgf i (hall i)]
  exact ENat.zero_ne_top

/-- **The multiplicity of the two-periodic complex `(A / abA, a, b)` is zero** for `a` and `b`
nonzerodivisors: its cohomology vanishes in both degrees. This is the step
`e_A(A / abA, a, b) = 0` of the proof of the reciprocity relation Stacks 0EAW. -/
theorem periodicLength_quotient_mul_eq_zero {c : A} (a b : A) (ha : a ∈ nonZeroDivisors A)
    (hb : b ∈ nonZeroDivisors A) (hc : c = a * b) (hfg hgf) :
    periodicLength (twoPeriodicComplex
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) a)
      (LinearMap.lsmul A (A ⧸ Ideal.span ({c} : Set A)) b) hfg hgf) = 0 := by
  rw [periodicLength_eq_sub,
    length_homology_quotient_mul_eq_zero a b ha hb hc hfg hgf 0 (Or.inl rfl),
    length_homology_quotient_mul_eq_zero a b ha hb hc hfg hgf 1 (Or.inr rfl)]
  simp

end AlgebraicGeometry

end
