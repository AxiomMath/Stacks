module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedGrading
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import all StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# The associated graded ring of a regular local ring is a graded polynomial algebra

Proof of the graded-*ring* form of [StacksProject 00NO]: if `(R, 𝔪, κ)` is a regular local ring of
dimension `d` and `xs = x_1, …, x_d` is a minimal set of generators of `𝔪`, then the canonical map
of graded rings
`κ[X_1, …, X_d] → Gr_𝔪(R) = ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)`, `X_i ↦ x_i mod 𝔪^2`,
is an isomorphism carrying the degree-`n` homogeneous polynomials onto `𝔪^n/𝔪^(n+1)`.

`IsRegularLocalRing.isQuasiRegular` records 00NO as bijectivity of the canonical map of graded
`κ[X_1, …, X_d]`-*modules* `κ[X_1, …, X_d] ⊗_κ (R/𝔪) → ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)` of
[StacksProject 061N]. That is the same
mathematical content, but it is a statement about modules: it does not exhibit a homomorphism of
*rings*, and a ring homomorphism is what is needed to compare `Proj` of the associated graded ring
with projective space — for instance in [StacksProject 0AGQ], where the exceptional divisor of the
blowup of a two-dimensional regular local ring is identified with `P^1_κ` by taking `Proj` of
`κ ⊗_A ⨁_{n ≥ 0} 𝔪^n = ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)`. This file supplies that ring homomorphism and
proves it is a degree-preserving bijection.

## Main definitions

* `AssociatedGraded.degreeZeroRingHom`: the ring map `A → Gr_I(A)` placing an element of `A` in
  degree `0`.
* `AssociatedGraded.quotientRingHom`: the induced ring map `A/I → Gr_I(A)`.
* `AssociatedGraded.polyGradedHom`: the ring map `(A/I)[X_1, …, X_c] → Gr_I(A)` determined by a
  sequence `x_1, …, x_c` of elements of `I`, sending `X_i` to the class of `x_i` in degree one.
  This is the surjection named in the source.
* `IsRegularLocalRing.gradedRingEquivMvPolynomial`: the resulting isomorphism of rings
  `κ[X_1, …, X_d] ≅ Gr_𝔪(R)` for a regular local ring.

## Main results

* `AssociatedGraded.polyGradedHom_mem_grading`: `polyGradedHom` is a map of *graded* rings — a
  homogeneous polynomial of degree `n` lands in the degree-`n` part `AssociatedGraded.grading I n`.
  This holds for any sequence of elements of `I`, with no regularity hypothesis.
* `AssociatedGraded.mem_grading_iff_exists_isHomogeneous`: `polyGradedHom` carries the degree-`n`
  homogeneous polynomials *onto* `I^n/I^(n+1)`, as soon as `x_1, …, x_c` generates `I`.
* `AssociatedGraded.bijective_polyGradedHom`: `polyGradedHom` is bijective as soon as
  `x_1, …, x_c` generates `I` and the canonical map of [StacksProject 061N] is injective, that is,
  as soon as `x_1, …, x_c` is a quasi-regular sequence.
* `IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra`: the statement of
  [StacksProject 00NO] in its graded-ring form.

## Implementation notes

The source's `Gr_I(A)` is `AssociatedGraded.gradedRing I`, an *external* direct sum
`⨁_{n ≥ 0} I^n/I^(n+1)` carrying a `DirectSum.GCommRing` structure, and its internal grading by
additive subgroups is `AssociatedGraded.grading I`; the latter is what `AlgebraicGeometry.Proj`
consumes. Being an isomorphism of graded rings is therefore recorded as two statements —
bijectivity, and `mem_grading_iff_exists_isHomogeneous`, that the degree-`n` part of `Gr_I(A)` is
exactly the image of the degree-`n` homogeneous polynomials — rather than as an isomorphism of a
single bundled structure: no bundled type of graded ring isomorphisms between an external and an
internal grading is available, and the two statements together say exactly that the degree-`n`
homogeneous polynomials are carried bijectively onto `I^n/I^(n+1)`. The weaker one-sided form
`polyGradedHom_mem_grading` is kept separately because it needs no hypothesis on `x` beyond
`x i ∈ I`.

The map is *defined*, not merely asserted to exist, and the source's description of it is its
definition: `polyGradedHom` is `MvPolynomial.eval₂Hom` of the degree-zero coefficient map
`A/I → Gr_I(A)` together with the assignment `X_i ↦ x_i mod I^2`. Being an `eval₂Hom` it is a ring
homomorphism by construction, so no multiplicativity has to be checked; what the quasi-regularity
input supplies is injectivity, and what `I = (x_1, …, x_c)` supplies is surjectivity.

Injectivity is deduced from
`Stacks.RegularLocalRing.Domain.coeff_mem_of_isHomogeneous_of_eval_mem` — quasi-regularity in
its degreewise elementary form, that a homogeneous polynomial of degree `n` over `A` whose value
at `x` lies in `I^(n+1)` has all its coefficients in `I`. Surjectivity is
`Ideal.mem_span_pow_iff_exists_isHomogeneous`: an element of `I^n = (x_1, …, x_c)^n` is the value
at `x` of a homogeneous polynomial of degree `n`.

## References

* [StacksProject 00NO](https://stacks.math.columbia.edu/tag/00NO)
* [StacksProject 061P](https://stacks.math.columbia.edu/tag/061P), for quasi-regular sequences
* [StacksProject 07VD](https://stacks.math.columbia.edu/tag/07VD), for the associated graded ring
-/

namespace AssociatedGraded

open DirectSum

variable {A : Type u} [CommRing A]

/-! ### Products of homogeneous classes -/

/-- A product of elements of the ideal powers `I ^ d i` lies in `I ^ ∑ d i`: `Ideal.prod_mem_prod`
read through `Finset.prod_pow_eq_pow_sum`. -/
theorem prod_mem_pow_sum (I : Ideal A) {c : ℕ} (d : Fin c → ℕ) (y : Fin c → A)
    (hy : ∀ i, y i ∈ I ^ d i) (s : Finset (Fin c)) :
    ∏ i ∈ s, y i ∈ I ^ ∑ i ∈ s, d i :=
  Finset.prod_pow_eq_pow_sum s d I ▸ Ideal.prod_mem_prod fun i _ => hy i

/-- The class of an element of an ideal power depends only on the degree and the element. -/
theorem classOfPow_congr (I : Ideal A) {m n : ℕ} (hmn : m = n) {a : ↥(I ^ m)}
    {b : ↥(I ^ n)} (hab : (a : A) = (b : A)) : classOfPow I m a = classOfPow I n b := by
  cases hmn
  exact DFunLike.congr_arg _ (Subtype.ext hab)

/-- The class of `1` in degree `0` is the unit of the associated graded ring. -/
theorem classOfPow_zero_one (I : Ideal A) (h : (1 : A) ∈ I ^ 0) :
    classOfPow I 0 ⟨1, h⟩ = 1 := rfl

/-- The `k`-th power of the degree-one class of `a ∈ I` is the degree-`k` class of `a ^ k`. -/
theorem classOfPow_one_pow (I : Ideal A) {a : A} (h1 : a ∈ I ^ 1) (k : ℕ)
    (hk : a ^ k ∈ I ^ k) : (classOfPow I 1 ⟨a, h1⟩) ^ k = classOfPow I k ⟨a ^ k, hk⟩ := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact (classOfPow_zero_one I (by simp)).symm.trans
      (classOfPow_congr I rfl (by simp))
  | succ k ih =>
    rw [pow_succ, ih (by simpa [pow_one] using Ideal.pow_mem_pow (by simpa [pow_one] using h1) k),
      ← classOfPow_mul]
    exact classOfPow_congr I rfl (pow_succ a k).symm

/-- A product of homogeneous classes is the class of the product, in the sum of the degrees. -/
theorem prod_classOfPow (I : Ideal A) {c : ℕ} (d : Fin c → ℕ) (y : Fin c → A)
    (hy : ∀ i, y i ∈ I ^ d i) :
    ∀ (s : Finset (Fin c)) (n : ℕ) (z : A) (hz : z ∈ I ^ n), ∑ i ∈ s, d i = n →
      ∏ i ∈ s, y i = z →
      ∏ i ∈ s, classOfPow I (d i) ⟨y i, hy i⟩ = classOfPow I n ⟨z, hz⟩ := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro n z hz hn hzz
    rw [Finset.sum_empty] at hn
    rw [Finset.prod_empty] at hzz
    subst hn
    subst hzz
    rw [Finset.prod_empty]
    exact (classOfPow_zero_one I hz).symm
  | insert a s ha ih =>
    intro n z hz hn hzz
    rw [Finset.sum_insert ha] at hn
    rw [Finset.prod_insert ha] at hzz
    rw [Finset.prod_insert ha, ih _ _ (prod_mem_pow_sum I d y hy _) rfl rfl, ← classOfPow_mul]
    exact classOfPow_congr I hn hzz

/-! ### The degree-zero coefficient map -/

/-- **The ring map `A → Gr_I(A)`** placing an element of `A` in degree `0`. Composed with the
inclusion of `AssociatedGraded.grading I 0` it is `AssociatedGraded.gradeZeroHom`. -/
noncomputable def degreeZeroRingHom (I : Ideal A) : A →+* gradedRing I where
  toFun a := classOfPow I 0 ⟨a, by simp⟩
  map_one' := classOfPow_zero_one I (by simp)
  map_mul' a b := classOfPow_mul I 0 0 ⟨a, by simp⟩ ⟨b, by simp⟩
  map_zero' := map_zero (classOfPow I 0)
  map_add' a b := map_add (classOfPow I 0) ⟨a, by simp⟩ ⟨b, by simp⟩

/-- `degreeZeroRingHom I a` is the class of `a` in degree `0`. -/
theorem degreeZeroRingHom_apply (I : Ideal A) (a : A) (h : a ∈ I ^ 0) :
    degreeZeroRingHom I a = classOfPow I 0 ⟨a, h⟩ := rfl

/-- **The ring map `A/I → Gr_I(A)`** onto the degree-zero part: an element of `I` has zero class
in degree `0`, so the degree-zero coefficient map factors through `A/I`. -/
noncomputable def quotientRingHom (I : Ideal A) : (A ⧸ I) →+* gradedRing I :=
  Ideal.Quotient.lift I (degreeZeroRingHom I) fun a ha => by
    have hval : degreeZeroRingHom I a
        = DirectSum.of (fun n => piece (M := A) I n) 0 (gradeZeroMk I a) := rfl
    rw [hval, (gradeZeroMk_eq_zero_iff I a).2 ha, map_zero]

/-- `quotientRingHom I` sends the residue class of `a` to the class of `a` in degree `0`. -/
theorem quotientRingHom_mk (I : Ideal A) (a : A) (h : a ∈ I ^ 0) :
    quotientRingHom I (Ideal.Quotient.mk I a) = classOfPow I 0 ⟨a, h⟩ := rfl

/-! ### The polynomial presentation -/

variable {c : ℕ}

/-- **The canonical graded ring map `(A/I)[X_1, …, X_c] → Gr_I(A)`** of [StacksProject 00NO],
determined by a sequence `x_1, …, x_c` of elements of `I`: the coefficients are placed in degree
`0` and `X_i` is sent to the class of `x_i` in degree `1`. -/
noncomputable def polyGradedHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I) :
    MvPolynomial (Fin c) (A ⧸ I) →+* gradedRing I :=
  MvPolynomial.eval₂Hom (quotientRingHom I) fun i =>
    classOfPow I 1 ⟨x i, by rw [pow_one]; exact hx i⟩

/-- A monomial `x^e` of degree `n` in elements of `I` lies in `I ^ n`. -/
private theorem prod_pow_mem_pow_of_sum_eq (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (e : Fin c →₀ ℕ) {n : ℕ} (hn : ∑ i, e i = n) : ∏ i, x i ^ e i ∈ I ^ n :=
  hn ▸ prod_mem_pow_sum I (fun i => e i) (fun i => x i ^ e i)
    (fun i => Ideal.pow_mem_pow (hx i) _) Finset.univ

/-- The value of `polyGradedHom` on a monomial `X^e` with coefficient the class of `a : A`: it is
the class of `a x^e` in degree `|e|`. -/
theorem polyGradedHom_monomial (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (e : Fin c →₀ ℕ) (a : A) {n : ℕ} (hn : ∑ i, e i = n)
    (hmem : a * ∏ i, x i ^ e i ∈ I ^ n) :
    polyGradedHom I x hx (MvPolynomial.monomial e (Ideal.Quotient.mk I a))
      = classOfPow I n ⟨a * ∏ i, x i ^ e i, hmem⟩ := by
  classical
  have hone : ∀ i, x i ∈ I ^ 1 := fun i => by rw [pow_one]; exact hx i
  have hpow : ∀ i, x i ^ e i ∈ I ^ e i := fun i => Ideal.pow_mem_pow (hx i) _
  have hmem' := prod_pow_mem_pow_of_sum_eq I x hx e hn
  have hprod : ∏ i, (classOfPow I 1 ⟨x i, hone i⟩) ^ (e i)
      = classOfPow I n ⟨∏ i, x i ^ e i, hmem'⟩ := by
    rw [Finset.prod_congr rfl fun i _ => classOfPow_one_pow I (hone i) (e i) (hpow i)]
    exact prod_classOfPow I (fun i => e i) (fun i => x i ^ e i) hpow Finset.univ n _ hmem' hn rfl
  rw [polyGradedHom, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ fun i => pow_zero _, hprod, quotientRingHom_mk I a (by simp),
    ← classOfPow_mul]
  exact classOfPow_congr I (zero_add n) rfl

/-- The value at `x` of a homogeneous polynomial of degree `n` lies in `I ^ n`, when every `x i`
lies in `I`. -/
theorem eval_mem_pow_of_isHomogeneous (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I) {n : ℕ}
    {P : MvPolynomial (Fin c) A} (hP : P.IsHomogeneous n) : MvPolynomial.eval x P ∈ I ^ n := by
  classical
  rw [MvPolynomial.eval_eq']
  refine Submodule.sum_mem _ fun e he => ?_
  exact Ideal.mul_mem_left _ _ (prod_pow_mem_pow_of_sum_eq I x hx e
    (Stacks.RegularLocalRing.Domain.qrMdeg_eq_of_mem_support hP he))

/-- **The value of `polyGradedHom` on the reduction of a homogeneous polynomial over `A`**: it is
the class in degree `n` of the value of that polynomial at `x`. -/
theorem polyGradedHom_map (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I) {n : ℕ}
    {P : MvPolynomial (Fin c) A} (hP : P.IsHomogeneous n) :
    polyGradedHom I x hx (P.map (Ideal.Quotient.mk I))
      = classOfPow I n ⟨MvPolynomial.eval x P, eval_mem_pow_of_isHomogeneous I x hx hP⟩ := by
  classical
  have hterm : ∀ e ∈ P.support, P.coeff e * ∏ i, x i ^ e i ∈ I ^ n := fun e he =>
    Ideal.mul_mem_left _ _ (prod_pow_mem_pow_of_sum_eq I x hx e
      (Stacks.RegularLocalRing.Domain.qrMdeg_eq_of_mem_support hP he))
  have hsum : (∑ e ∈ P.support.attach,
        (⟨P.coeff e.1 * ∏ i, x i ^ e.1 i, hterm e.1 e.2⟩ : ↥(I ^ n)))
      = ⟨MvPolynomial.eval x P, eval_mem_pow_of_isHomogeneous I x hx hP⟩ := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum,
      Finset.sum_attach P.support fun e => P.coeff e * ∏ i, x i ^ e i]
    exact (MvPolynomial.eval_eq' x P).symm
  calc polyGradedHom I x hx (P.map (Ideal.Quotient.mk I))
      = ∑ e ∈ P.support.attach,
          classOfPow I n ⟨P.coeff e.1 * ∏ i, x i ^ e.1 i, hterm e.1 e.2⟩ := by
        conv_lhs => rw [P.as_sum]
        simp only [map_sum]
        rw [← Finset.sum_attach P.support fun e => polyGradedHom I x hx
          (MvPolynomial.map (Ideal.Quotient.mk I) (MvPolynomial.monomial e (P.coeff e)))]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [MvPolynomial.map_monomial]
        exact polyGradedHom_monomial I x hx e.1 (P.coeff e.1)
          (Stacks.RegularLocalRing.Domain.qrMdeg_eq_of_mem_support hP e.2) (hterm e.1 e.2)
    _ = classOfPow I n (∑ e ∈ P.support.attach,
          ⟨P.coeff e.1 * ∏ i, x i ^ e.1 i, hterm e.1 e.2⟩) := (map_sum (classOfPow I n) _ _).symm
    _ = classOfPow I n ⟨MvPolynomial.eval x P, eval_mem_pow_of_isHomogeneous I x hx hP⟩ := by
        rw [hsum]

/-! ### `polyGradedHom` is a map of graded rings -/

/-- **`polyGradedHom` preserves degrees**: a homogeneous polynomial of degree `n` is sent into the
degree-`n` part `AssociatedGraded.grading I n` of the associated graded ring. No hypothesis beyond
`x i ∈ I` is needed. -/
theorem polyGradedHom_mem_grading (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I) {n : ℕ}
    {p : MvPolynomial (Fin c) (A ⧸ I)} (hp : p.IsHomogeneous n) :
    polyGradedHom I x hx p ∈ grading I n := by
  classical
  have hexp : polyGradedHom I x hx p
      = ∑ e ∈ p.support, polyGradedHom I x hx (MvPolynomial.monomial e (p.coeff e)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hexp]
  refine AddSubgroup.sum_mem _ fun e he => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (p.coeff e)
  rw [← ha, polyGradedHom_monomial I x hx e a
    (Stacks.RegularLocalRing.Domain.qrMdeg_eq_of_mem_support hp he)
    (Ideal.mul_mem_left _ _ (prod_pow_mem_pow_of_sum_eq I x hx e
      (Stacks.RegularLocalRing.Domain.qrMdeg_eq_of_mem_support hp he)))]
  exact of_mem_grading I _

/-- An element of `I^n/I^(n+1)` is the value of `polyGradedHom` on a homogeneous polynomial of
degree `n`, when `x_1, …, x_c` generates `I`. -/
private theorem exists_isHomogeneous_polyGradedHom_eq (I : Ideal A) (x : Fin c → A)
    (hx : ∀ i, x i ∈ I) (hI : Ideal.span (Set.range x) = I) (n : ℕ) (a : piece (M := A) I n) :
    ∃ p : MvPolynomial (Fin c) (A ⧸ I), p.IsHomogeneous n ∧
      polyGradedHom I x hx p = DirectSum.of (fun k => piece (M := A) I k) n a := by
  classical
  induction a using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨P, hPhom, hPev⟩ :=
      (Ideal.mem_span_pow_iff_exists_isHomogeneous x (z : A)).1
        (by rw [hI]; simpa only [ring_power_eq] using z.2)
    refine ⟨P.map (Ideal.Quotient.mk I), hPhom.map _, ?_⟩
    have hz' : (z : A) ∈ I ^ n := by simpa only [ring_power_eq] using z.2
    have hstep : classOfPow I n ⟨MvPolynomial.eval x P,
        eval_mem_pow_of_isHomogeneous I x hx hPhom⟩ = classOfPow I n ⟨(z : A), hz'⟩ :=
      classOfPow_congr I rfl hPev
    rw [polyGradedHom_map I x hx hPhom, hstep]
    rfl

/-- **`polyGradedHom` is onto each graded piece.** When `x_1, …, x_c` generates `I`, the degree-`n`
part `AssociatedGraded.grading I n` of the associated graded ring consists exactly of the values of
`polyGradedHom` on the homogeneous polynomials of degree `n`. Together with
`bijective_polyGradedHom` this is the assertion that `polyGradedHom` is an isomorphism of *graded*
rings: it is a bijection, and it carries the degree-`n` homogeneous polynomials onto
`I^n/I^(n+1)`. No quasi-regularity is needed here. -/
theorem mem_grading_iff_exists_isHomogeneous (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I) (n : ℕ) (y : gradedRing I) :
    y ∈ grading I n ↔
      ∃ p : MvPolynomial (Fin c) (A ⧸ I), p.IsHomogeneous n ∧ polyGradedHom I x hx p = y := by
  classical
  refine ⟨fun hy => ?_, fun ⟨p, hp, hpy⟩ => hpy ▸ polyGradedHom_mem_grading I x hx hp⟩
  obtain ⟨a, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.1 hy
  exact exists_isHomogeneous_polyGradedHom_eq I x hx hI n a

/-! ### Bijectivity -/

/-- **`polyGradedHom` is injective** when the canonical map of [StacksProject 061N] is injective,
that is, when `x_1, …, x_c` is a quasi-regular sequence generating `I`. -/
theorem injective_polyGradedHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hqr : Function.Injective (quasiRegularCanonicalMap (M := A) x)) :
    Function.Injective (polyGradedHom I x hx) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro p hp
  set N := p.totalDegree + 1 with hN
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  set P : ℕ → MvPolynomial (Fin c) A := fun m => MvPolynomial.homogeneousComponent m q with hP
  have hPhom : ∀ m, (P m).IsHomogeneous m := fun m =>
    MvPolynomial.homogeneousComponent_isHomogeneous m q
  have hPmap : ∀ m, (P m).map (Ideal.Quotient.mk I) = MvPolynomial.homogeneousComponent m p :=
    fun m => MvPolynomial.ext _ _ fun e => by
      rw [← hq, MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent,
        MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_map]
      split_ifs <;> simp
  -- the image of `p` is the sum of the images of its homogeneous components
  have hsum : ∑ m ∈ Finset.range N, DirectSum.of (fun k => piece (M := A) I k) m
      (mk I m ⟨MvPolynomial.eval x (P m),
        by simpa only [ring_power_eq] using eval_mem_pow_of_isHomogeneous I x hx (hPhom m)⟩)
      = 0 := by
    rw [← hp]
    conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hPmap m, polyGradedHom_map I x hx (hPhom m)]
    rfl
  -- hence each homogeneous component vanishes
  have hzero : ∀ m, MvPolynomial.homogeneousComponent m p = 0 := by
    intro m
    by_cases hm : m ∈ Finset.range N
    · have hcomp := congrArg (homogeneousPart (fun k => piece (M := A) I k) m) hsum
      rw [map_sum, map_zero] at hcomp
      rw [Finset.sum_congr rfl
        (fun j _ => homogeneousPart_of (fun k => piece (M := A) I k) m j _),
        Finset.sum_ite_eq' (Finset.range N) m _, ite_eq_left hm] at hcomp
      have hval : mk I m ⟨MvPolynomial.eval x (P m),
          by simpa only [ring_power_eq] using eval_mem_pow_of_isHomogeneous I x hx (hPhom m)⟩
          = 0 := by
        have := congrArg (fun z => z m) hcomp
        simpa using this
      have hmem : MvPolynomial.eval x (P m) ∈ I ^ (m + 1) := by
        rw [mk, Submodule.Quotient.mk_eq_zero] at hval
        simpa only [Submodule.mem_comap, Submodule.coe_subtype, ring_power_eq] using hval
      have hcoeff : ∀ e, MvPolynomial.coeff e (P m) ∈ I := fun e => by
        have := Stacks.RegularLocalRing.Domain.coeff_mem_of_isHomogeneous_of_eval_mem hqr
          (hPhom m) (by rwa [show Jid x = I from hI]) e
        rwa [show Jid x = I from hI] at this
      rw [← hPmap m]
      refine MvPolynomial.ext _ _ fun e => ?_
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hcoeff e
    · exact MvPolynomial.homogeneousComponent_eq_zero _ _ (by
        simp only [Finset.mem_range, hN] at hm
        omega)
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  exact Finset.sum_eq_zero fun m _ => hzero m

/-- **`polyGradedHom` is surjective** when `x_1, …, x_c` generates `I`: an element of
`I^n/I^(n+1)` is represented by an element of `I^n = (x_1, …, x_c)^n`, hence by the value at `x` of
a homogeneous polynomial of degree `n`. -/
theorem surjective_polyGradedHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I) : Function.Surjective (polyGradedHom I x hx) := by
  classical
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n a =>
    obtain ⟨p, -, hp⟩ := exists_isHomogeneous_polyGradedHom_eq I x hx hI n a
    exact ⟨p, hp⟩
  | add u v hu hv =>
    obtain ⟨pu, hpu⟩ := hu
    obtain ⟨pv, hpv⟩ := hv
    exact ⟨pu + pv, by rw [map_add, hpu, hpv]⟩

/-- **`polyGradedHom` is bijective** when `x_1, …, x_c` is a quasi-regular sequence generating
`I`. -/
theorem bijective_polyGradedHom (I : Ideal A) (x : Fin c → A) (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hqr : Function.Injective (quasiRegularCanonicalMap (M := A) x)) :
    Function.Bijective (polyGradedHom I x hx) :=
  ⟨injective_polyGradedHom I x hx hI hqr, surjective_polyGradedHom I x hx hI⟩

end AssociatedGraded

/-! ### Stacks 00NO in its graded-ring form -/

open IsLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (xs : List R)

/-- **Stacks 00NO, in the form of a graded-ring isomorphism.** Let `(R, 𝔪, κ)` be a regular local
ring of dimension `d` and let `xs = x_1, …, x_d` be a minimal set of generators of `𝔪`, that is, a
list generating `𝔪` whose length is the minimal number of generators of `𝔪` (which equals `dim R`).
Then the canonical map of graded rings
`κ[X_1, …, X_d] → ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)`, `X_i ↦ x_i mod 𝔪^2`,
is bijective (first clause) and carries the homogeneous polynomials of degree `n` onto the
degree-`n` part `𝔪^n/𝔪^(n+1)` (second clause). Together: the graded ring
`⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)` is the graded polynomial algebra `κ[X_1, …, X_d]` over the residue
field, as graded rings. -/
@[stacks 00NO "The graded-RING form: the canonical ring map \
`κ[X_1, …, X_d] → ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)`, `X_i ↦ x_i mod 𝔪^2`, of a minimal generating sequence \
of the maximal ideal is bijective, and carries the degree-`n` homogeneous polynomials exactly onto \
`𝔪^n/𝔪^(n+1)`; that is the source's isomorphism of the graded ring with the graded polynomial \
algebra, with the isomorphism pinned to the source's own map rather than merely asserted. \
See also `IsRegularLocalRing.isQuasiRegular` for the graded-module form (Tag 061N/061P)."]
public theorem gradedRing_maximalIdeal_isPolynomialAlgebra
    (hxs : Ideal.ofList xs = maximalIdeal R)
    (hmin : xs.length = (maximalIdeal R).spanFinrank)
    (hx : ∀ i : Fin xs.length, xs[i] ∈ maximalIdeal R) :
    Function.Bijective
        (AssociatedGraded.polyGradedHom (maximalIdeal R) (fun i : Fin xs.length => xs[i]) hx) ∧
      ∀ (n : ℕ) (y : AssociatedGraded.gradedRing (maximalIdeal R)),
        y ∈ AssociatedGraded.grading (maximalIdeal R) n ↔
          ∃ p : MvPolynomial (Fin xs.length) (R ⧸ maximalIdeal R), p.IsHomogeneous n ∧
            AssociatedGraded.polyGradedHom (maximalIdeal R)
              (fun i : Fin xs.length => xs[i]) hx p = y := by
  have hI : Ideal.span (Set.range fun i : Fin xs.length => xs[i]) = maximalIdeal R :=
    (Stacks.QuasiregularSequence.ofList_eq_span_range xs).symm.trans hxs
  refine ⟨AssociatedGraded.bijective_polyGradedHom _ _ hx hI
    (IsRegularLocalRing.isQuasiRegular xs hxs hmin).injective,
    fun n y => AssociatedGraded.mem_grading_iff_exists_isHomogeneous _ _ hx hI n y⟩

/-- **The graded-ring isomorphism of Stacks 00NO**: for a minimal set of generators `x_1, …, x_d`
of the maximal ideal of a regular local ring, the canonical ring map
`κ[X_1, …, X_d] → ⨁_{n ≥ 0} 𝔪^n/𝔪^(n+1)` sending `X_i` to the class of `x_i` is an isomorphism.
It carries homogeneous polynomials of degree `n` into `𝔪^n/𝔪^(n+1)` by
`AssociatedGraded.polyGradedHom_mem_grading`. -/
@[sga "1 II 4.14" "partial"]
noncomputable def gradedRingEquivMvPolynomial (hxs : Ideal.ofList xs = maximalIdeal R)
    (hmin : xs.length = (maximalIdeal R).spanFinrank)
    (hx : ∀ i : Fin xs.length, xs[i] ∈ maximalIdeal R) :
    MvPolynomial (Fin xs.length) (R ⧸ maximalIdeal R) ≃+*
      AssociatedGraded.gradedRing (maximalIdeal R) :=
  RingEquiv.ofBijective _ (gradedRing_maximalIdeal_isPolynomialAlgebra xs hxs hmin hx).1

end IsRegularLocalRing

end
