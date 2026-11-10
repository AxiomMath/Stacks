module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sum of effective Cartier divisors

Chapter 31, Divisors. Let `S` be a scheme and let `D₁`, `D₂` be effective Cartier divisors on
`S`, presented as `AlgebraicGeometry.Scheme.IdealSheafData` satisfying
`Stacks.Divisors.IsEffectiveCartierDivisor`. Their *sum* `D = D₁ + D₂` is the closed subscheme
cut out by the product `𝓘_{D₁} 𝓘_{D₂}` of their sheaves of ideals, and the same product
expresses the sum `∑ nᵢ Dᵢ` of finitely many effective Cartier divisors with nonnegative
integer multiplicities as `∏ i ∈ s, 𝓘_{Dᵢ} ^ nᵢ`.

**The construction is Mathlib's.** `AlgebraicGeometry.Scheme.IdealSheafData` is an
`IdemCommSemiring`, so the product of two quasi-coherent sheaves of ideals and the `n`-th power
of one are already available, as are associativity, commutativity and the unit `⊤` — and
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` turns the result back into a closed
subscheme. So nothing is constructed here; the three Mathlib declarations that carry the content
of [Stacks, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT) are recorded with
`add_to_stacks` below, and what this file adds is the theorem that makes the definition useful,
[Stacks, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU).

**A warning on notation.** Mathlib's `Add` on `IdealSheafData` is `⊔`, which
on closed subschemes is the scheme-theoretic *intersection*, not the sum of divisors. The sum of
effective Cartier divisors is the `Mul`, and `n • D` in the divisor sense is `𝓘_D ^ n`, never
`n • 𝓘_D`. Every statement below is phrased in `*` and `^` for that reason.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_mul`: **Stacks Tag 01WU**, the sum of two effective
  Cartier divisors is an effective Cartier divisor.
* `Stacks.Divisors.isEffectiveCartierDivisor_pow`: the `n`-fold sum `nD` of an effective Cartier
  divisor is an effective Cartier divisor, for every `n`, including `n = 0` where it is the empty
  divisor. This is the form the proof of
  [Stacks, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27) consumes, where `nx` is the
  `n`-fold sum of a closed point.
* `Stacks.Divisors.isEffectiveCartierDivisor_prod`: the general sum `∑ nᵢ Dᵢ` of the remark
  following Tag 01WT is an effective Cartier divisor.
The base case of both inductions, `Stacks.Divisors.isEffectiveCartierDivisor_top`, is not
proved here: it is `StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections`, which this
module imports.
* `AlgebraicGeometry.Scheme.IdealSheafData.ideal_finsetProd_eq_prod`: the defining ideal of
  `∑ nᵢ Dᵢ` on an affine open is the product of the defining ideals there.
* `AlgebraicGeometry.Scheme.IdealSheafData.mul_le_left`,
  `AlgebraicGeometry.Scheme.IdealSheafData.pow_le_pow_right_of_le`: each summand is contained in
  the sum, and `mD ⊆ nD` for `m ≤ n`. Containment of closed subschemes is the *reverse*
  inequality of ideal sheaves, which is why these read as upper bounds.

## Implementation notes

Tag 01WU is affine-local and the whole of it is the source's own one-line proof: a product of
two nonzerodivisors is a nonzerodivisor. Both directions of the affine-local characterization
[Stacks, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS) are available in the form that takes
and produces a principal ideal with a nonzerodivisor generator,
`Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor` and
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen`, so no quotient chart and
no pullback square appears here: the two generators are produced on two affine opens, shrunk onto
a common basic open with `AlgebraicGeometry.exists_basicOpen_le_affine_inter`, and stay
nonzerodivisors there because the sections of a basic open are a localization —
`Stacks.Divisors.isRegular_res_of_eq_basicOpen`. The ideal of the product on that basic open is
the product of the two principal ideals by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul` together with
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`, and
`Ideal.span_singleton_mul_span_singleton` makes it principal on the product of the generators.

The power and the finite product are then inductions on `Mathlib`'s `pow_succ` and
`Finset.cons_induction`, with `Stacks.Divisors.isEffectiveCartierDivisor_top` as the base case,
since `𝓘 ^ 0 = 1 = ⊤` is the empty subscheme. No separate definition of `∑ nᵢ Dᵢ` is introduced:
it is `∏ i ∈ s, D i ^ n i` in Mathlib's commutative monoid, and a named wrapper would be a second
spelling of one operation.

## References

* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-! ### Tag 01WT: the construction, which is Mathlib's

The sum `D₁ + D₂` of two effective Cartier divisors is the closed subscheme cut out by the
product of their sheaves of ideals; the product of quasi-coherent sheaves of ideals is Mathlib's
`Mul` on `IdealSheafData`, the `n`-fold sum is its `Pow`, and
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` is the passage back to a closed subscheme.
-/

add_to_stacks 01WT "the sum of two effective Cartier divisors, as the product of their sheaves
of ideals" AlgebraicGeometry.Scheme.IdealSheafData.instMul

add_to_stacks 01WT "the `n`-fold sum `nD` of the remark following the definition; the general
sum `∑ nᵢ Dᵢ` is the `Finset` product of these" AlgebraicGeometry.Scheme.IdealSheafData.instPowNat
add_to_sga "1 III 7.1" "partial" AlgebraicGeometry.Scheme.IdealSheafData.instPowNat

add_to_stacks 01WT "the defining ideal of the sum on an affine open is the product of the two
defining ideals, so the construction computes what the definition says"
AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The sections of a finite product of quasi-coherent ideal sheaves on an affine open are the
product of their sections: the general sum `∑ nᵢ Dᵢ` is computed on an affine open by the product
of the defining ideals. -/
theorem ideal_finsetProd_eq_prod {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Ideal.one_eq_top.symm
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]

/-- **Each summand is contained in the sum.** Containment of closed subschemes reverses the
inequality of their sheaves of ideals, so `D₁ ⊆ D₁ + D₂` reads `𝓘_{D₁} 𝓘_{D₂} ≤ 𝓘_{D₁}`. -/
theorem mul_le_left (I J : X.IdealSheafData) : I * J ≤ I :=
  le_def.2 fun U => by
    change I.ideal U * J.ideal U ≤ I.ideal U
    exact Ideal.mul_le_left

/-- **Each summand is contained in the sum**, on the right. -/
theorem mul_le_right (I J : X.IdealSheafData) : I * J ≤ J :=
  (mul_comm I J) ▸ mul_le_left J I

/-- **`mD ⊆ nD` for `m ≤ n`.** The smaller multiple of an effective Cartier divisor is a closed
subscheme of the larger one, which on sheaves of ideals is `𝓘 ^ n ≤ 𝓘 ^ m`. -/
theorem pow_le_pow_right_of_le (I : X.IdealSheafData) {m n : ℕ} (h : m ≤ n) :
    I ^ n ≤ I ^ m :=
  le_def.2 fun U => by
    change I.ideal U ^ n ≤ I.ideal U ^ m
    exact Ideal.pow_le_pow_right h

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **A common principal chart for two effective Cartier divisors.** Around every point there is
one affine open on which both sheaves of ideals are generated by a single nonzerodivisor; hence
the product is generated by the product of the two generators, again a nonzerodivisor. -/
theorem exists_affineOpen_ideal_mul_eq_span (I J : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (hJ : IsEffectiveCartierDivisor J) (x : X) :
    ∃ (W : X.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      ∃ h : Γ(X, W), IsRegular h ∧ (I * J).ideal ⟨W, hW⟩ = Ideal.span {h} := by
  obtain ⟨U, hU, hxU, f, hf, hIf⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI x
  obtain ⟨V, hV, hxV, g, hg, hJg⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  obtain ⟨a, b, hab, hxW⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hV x ⟨hxU, hxV⟩
  let U' : X.affineOpens := ⟨U, hU⟩
  let V' : X.affineOpens := ⟨V, hV⟩
  let a' : Γ(X, U'.1) := a
  let b' : Γ(X, V'.1) := b
  let W : X.affineOpens := X.affineBasicOpen a'
  have hWU : W ≤ U' := X.affineBasicOpen_le a'
  have hWV : W.1 ≤ V'.1 := hab.trans_le (X.affineBasicOpen_le b')
  let fW : Γ(X, W.1) := (X.presheaf.map (homOfLE hWU).op).hom f
  let gW : Γ(X, W.1) := (X.presheaf.map (homOfLE hWV).op).hom g
  refine ⟨W.1, W.2, hxW, fW * gW,
    (isRegular_res_of_eq_basicOpen hWU a' f rfl hf).mul
      (isRegular_res_of_eq_basicOpen hWV b' g hab hg), ?_⟩
  change I.ideal W * J.ideal W = _
  rw [← I.map_ideal hWU, ← J.map_ideal hWV, hIf, hJg, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
  rfl

/-- **The `n`-fold sum of an effective Cartier divisor is an effective Cartier divisor.** This is
the remark following Tag 01WT in the case of one divisor, and the form the proof of Tag 0A27
consumes: for a closed point `x` whose local ring is a discrete valuation ring, `nx` is an
effective Cartier divisor for every `n`. -/
theorem isEffectiveCartierDivisor_pow {I : X.IdealSheafData}
    (hI : IsEffectiveCartierDivisor I) (n : ℕ) :
    IsEffectiveCartierDivisor (I ^ n) := by
  induction n with
  | zero => simpa [Scheme.IdealSheafData.one_eq_top] using
      (isEffectiveCartierDivisor_top (X := X))
  | succ n ih => simpa [pow_succ] using AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ ih hI

/-- **The general sum `∑ nᵢ Dᵢ` is an effective Cartier divisor.** This is the remark following
Tag 01WT: finitely many effective Cartier divisors `Dᵢ` and nonnegative integers `nᵢ` have a sum,
and it is again an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_prod {ι : Type*} (s : Finset ι)
    (D : ι → X.IdealSheafData) (n : ι → ℕ)
    (hD : ∀ i ∈ s, IsEffectiveCartierDivisor (D i)) :
    IsEffectiveCartierDivisor (∏ i ∈ s, D i ^ n i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa [Scheme.IdealSheafData.one_eq_top] using
      (isEffectiveCartierDivisor_top (X := X))
  | cons i s hi ih =>
    rw [Finset.prod_cons]
    exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
      (isEffectiveCartierDivisor_pow (hD i (Finset.mem_cons_self i s)) (n i))
      (ih fun j hj => hD j (Finset.mem_cons_of_mem hj))

end Stacks.Divisors

end
