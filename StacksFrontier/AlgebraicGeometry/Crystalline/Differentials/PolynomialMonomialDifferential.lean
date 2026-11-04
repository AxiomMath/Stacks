module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexed

/-!
# The differential of a divided power monomial over a nontrivial divided power base

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩` carry the divided power ideal
`IP + P₊` of [Stacks, Tag 07H6].  This module computes the universal divided power differential
`d : P → Ω¹_{P/A,δ'}` of [Stacks, Tag 07HZ] on a divided power monomial:

`d (x^{[K]}) = ∑_{w ∈ supp K} x^{[K - e_w]} · d x_w`.

Here `x^{[K]} = ∏_w x_w^{[K w]}` and `K - e_w` is written `K.erase w + single w (K w - 1)`, the
spelling in which the two factors of the monomial are visibly disjoint.

The base `(B, I, δ)` is arbitrary.  The same computation for `I = ⊥` is carried out, privately,
inside the proof of the absolute Poincaré lemma
(`StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`, around the private
`dividedPowerDifferential_monomial_shift`), where it is the step that turns the de Rham
differential into exterior multiplication by `∑_{w ∈ supp K} e_w` on each sector.  That use is
what this module is for: the sector argument has to be redone relative to `Ω^*_{B/A,δ}` once `I`
is nontrivial, and the monomial computation is the part of it that is unchanged — the variables
`x_w` are divided power elements of `P` whatever `I` is, and `d` obeys the same two rules.

## Main results

* `Crystalline.DividedPowerPolynomial.dividedPowerDifferential_finsetProd` — the Leibniz rule
  for a finite product, which is what the monomial computation runs on.
* `Crystalline.DividedPowerPolynomial.dividedPowerDifferential_variableMonomial` —
  `d (x_w^{[n+1]}) = x_w^{[n]} · d x_w`.
* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialMonomial_erase_add_single` — the
  monomial `x^{[K.erase w + single w n]}` factors as `x^{[K.erase w]} · x_w^{[n]}`.
* `Crystalline.DividedPowerPolynomial.dividedPowerDifferential_monomial` — the differential of a
  monomial as a sum over the support, with the Leibniz cofactors left as products.
* `Crystalline.DividedPowerPolynomial.dividedPowerDifferential_monomial_shift` — **the same sum
  with each cofactor folded back into a single monomial**, which is the form the sector argument
  uses.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
-/

@[expose] public section

open DividedPowers

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### The Leibniz rule for a finite product -/

/-- **The Leibniz rule for a finite product.**  The universal divided power differential of
`∏_{i ∈ s} f i` is `∑_{i ∈ s} (∏_{j ≠ i} f j) · d (f i)`.

Stated for `Crystalline.dividedPowerDifferential` rather than for an abstract `Derivation`, so
that it applies directly: `d` is a quotient of the Kähler differential and is not itself a
bundled derivation. -/
public theorem dividedPowerDifferential_finsetProd {A : Type uA} {C : Type*} [CommRing A]
    [CommRing C] [Algebra A C] {J : Ideal C} (hJ : DividedPowers J) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → C) :
    dividedPowerDifferential (A := A) hJ (∏ i ∈ s, f i) =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • dividedPowerDifferential (A := A) hJ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, dividedPowerDifferential_one, Finset.sum_empty]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, dividedPowerDifferential_mul, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.smul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hia : a ≠ i := fun h ↦ ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia,
      Finset.prod_insert (fun h ↦ ha (Finset.mem_of_mem_erase h)), mul_smul]

/-! ### The differential of a monomial -/

section Monomial

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- **The differential of a divided power power of a variable**: `d (x_w^{[n+1]}) =
x_w^{[n]} · d x_w`.  This is the divided power rule of [Stacks, Tag 07HZ] applied to the
variable `x_w`, which lies in the divided power ideal `IP + P₊` of `P` whatever the ideal `I`
of the base is. -/
public theorem dividedPowerDifferential_variableMonomial (w : W) (n : ℕ) :
    dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
        (dividedPowerPolynomialVariableMonomial (B : Type uB) w (n + 1)) =
      dividedPowerPolynomialVariableMonomial (B : Type uB) w n •
        dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w) := by
  rw [← setIndexedDividedPowerPolynomialDividedPowers_dpow_variable B w (n + 1),
    ← setIndexedDividedPowerPolynomialDividedPowers_dpow_variable B w n]
  exact dividedPowerDifferential_dpow (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W)
    ⟨dividedPowerPolynomialVariable (B : Type uB) w, variable_mem_polynomialIdeal B w⟩ n

/-- The monomial `x^{[K.erase w + single w n]}` is the product of `x^{[K.erase w]}`, which does
not involve `x_w`, and `x_w^{[n]}`.  The two exponent vectors have disjoint supports, which is
what makes the divided power monomial of their sum the product of their monomials. -/
public theorem dividedPowerPolynomialMonomial_erase_add_single {W : Type uW} (K : W →₀ ℕ)
    (w : W) (n : ℕ) :
    dividedPowerPolynomialMonomial (B : Type uB) (K.erase w + Finsupp.single w n) =
      dividedPowerPolynomialMonomial (B : Type uB) (K.erase w) *
        dividedPowerPolynomialVariableMonomial (B : Type uB) w n := by
  classical
  have hd : Disjoint (K.erase w).support (Finsupp.single w n).support := by
    refine Finset.disjoint_left.mpr fun a ha hna ↦ ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at ha
    rw [Finsupp.mem_support_iff, Finsupp.single_apply_ne_zero] at hna
    exact ha.1 hna.1
  unfold dividedPowerPolynomialMonomial dividedPowerPolynomialVariableMonomial
  rw [Finsupp.prod_add_index_of_disjoint hd,
    Finsupp.prod_single_index (by simp [DividedPowerAlgebra.dp_zero])]

/-- **The differential of a divided power monomial**, with the Leibniz cofactors left as
products: `d (x^{[K]}) = ∑_{w ∈ supp K} (∏_{u ≠ w} x_u^{[K u]}) · d (x_w^{[K w]})`. -/
public theorem dividedPowerDifferential_monomial [DecidableEq W] (K : W →₀ ℕ) :
    dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
        (dividedPowerPolynomialMonomial (B : Type uB) K) =
      ∑ w ∈ K.support,
        (∏ u ∈ K.support.erase w,
            dividedPowerPolynomialVariableMonomial (B : Type uB) u (K u)) •
          dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (dividedPowerPolynomialVariableMonomial (B : Type uB) w (K w)) := by
  classical
  have hprod : dividedPowerPolynomialMonomial (B : Type uB) K =
      ∏ w ∈ K.support, dividedPowerPolynomialVariableMonomial (B : Type uB) w (K w) := rfl
  rw [hprod]
  exact dividedPowerDifferential_finsetProd (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W) K.support
    fun w ↦ dividedPowerPolynomialVariableMonomial (B : Type uB) w (K w)

/-- **The differential of a divided power monomial over a nontrivial divided power base:**

`d (x^{[K]}) = ∑_{w ∈ supp K} x^{[K - e_w]} · d x_w`,

each cofactor folded back into a single monomial.  This is the form the sector decomposition of
the de Rham complex runs on: it says that `d` lowers the exponent vector by one standard basis
vector and produces the corresponding `d x_w`, so the total multi-index
`K + (the wedge's subset)` is preserved. -/
public theorem dividedPowerDifferential_monomial_shift (K : W →₀ ℕ) :
    dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
        (dividedPowerPolynomialMonomial (B : Type uB) K) =
      ∑ w ∈ K.support,
        dividedPowerPolynomialMonomial (B : Type uB)
            (K.erase w + Finsupp.single w (K w - 1)) •
          dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (dividedPowerPolynomialVariable (B : Type uB) w) := by
  classical
  rw [dividedPowerDifferential_monomial]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  have hKw : K w - 1 + 1 = K w :=
    Nat.sub_add_cancel (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw))
  conv_lhs => rw [← hKw]
  rw [dividedPowerDifferential_variableMonomial A B W w (K w - 1), smul_smul]
  refine congrArg
    (· • dividedPowerDifferential (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W)
      (dividedPowerPolynomialVariable (B : Type uB) w)) ?_
  have hprod : (K.erase w).prod (fun u m ↦
        DividedPowerAlgebra.dp (B : Type uB) m (Finsupp.single u (1 : (B : Type uB)))) =
      ∏ u ∈ K.support.erase w,
        dividedPowerPolynomialVariableMonomial (B : Type uB) u (K u) := by
    rw [Finsupp.prod, Finsupp.support_erase]
    refine Finset.prod_congr rfl fun u hu ↦ ?_
    simp only [dividedPowerPolynomialVariableMonomial,
      Finsupp.erase_ne (Finset.mem_erase.mp hu).1]
  rw [← hprod]
  exact (dividedPowerPolynomialMonomial_erase_add_single B K w (K w - 1)).symm

end Monomial

end DividedPowerPolynomial

end Crystalline

end
