module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential trace of a degree-`p` purely inseparable extension

Let `R` be a commutative ring of prime characteristic `p`. On the relative differentials of
`R[X] / (X ^ p - a)` the differential trace sends `x ^ i • dx` to zero for `i < p - 1` and sends
`x ^ (p - 1) • dx` to `da`. This rule determines the trace, and it is independent of the chosen
presentation of the algebra.

## Main definitions

* `KaehlerDifferential.IsPthRootDifferentialTrace` records the defining values of this trace.
* `KaehlerDifferential.pthRootDifferentialTrace` is the trace itself, bundled with those values.

## Main results

* `KaehlerDifferential.pthRootDifferentialTrace_eq_comp_map` states that an algebra map between
  two such presentations intertwines their differential traces.

## Implementation notes

The quotient `R[X] / (X ^ p - a)` is represented by `AdjoinRoot (X ^ p - C a)`. The source
defines the trace by its values on the displayed `R`-basis, and the predicate
`IsPthRootDifferentialTrace` records exactly those values. In the conclusion, `φ` acts on
relative Kähler differentials through `KaehlerDifferential.map`.

## References

* [Stacks Project, Tag 0ADZ](https://stacks.math.columbia.edu/tag/0ADZ)
-/

@[expose] public section

open Polynomial
open scoped KaehlerDifferential TensorProduct

universe u

namespace KaehlerDifferential

/-- Over the universal coefficient ring, `k` times the `p * k`-th coefficient of `Q ^ p` is the
`(p * k - 1)`-st coefficient of `Q ^ (p - 1) * Q'`. -/
private theorem coeff_divided_deriv_univ (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (Q : Polynomial (MvPolynomial ℕ ℤ)) :
    (k : MvPolynomial ℕ ℤ) * (Q ^ p).coeff (p * k) =
      (Q ^ (p - 1) * Polynomial.derivative Q).coeff (p * k - 1) := by
  have hh := congrArg (fun f : Polynomial (MvPolynomial ℕ ℤ) => f.coeff (p * k - 1))
    (Polynomial.derivative_pow Q p)
  rw [Polynomial.coeff_derivative, mul_assoc, Polynomial.coeff_C_mul] at hh
  have hn : p * k - 1 + 1 = p * k := Nat.sub_add_cancel (Nat.mul_pos hp hk)
  have hfac : (↑(p * k - 1) : MvPolynomial ℕ ℤ) + 1 = (p : MvPolynomial ℕ ℤ) * k := by
    rw [← Nat.cast_add_one, hn, Nat.cast_mul]
  rw [hfac, hn] at hh
  have hpM : (p : MvPolynomial ℕ ℤ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (fun _ : ℕ => 0)) h
    have hz : (p : ℤ) = 0 := by simpa using he
    have : p = 0 := by exact_mod_cast hz
    omega
  refine mul_left_cancel₀ hpM ?_
  rw [← hh]
  ring

/-- The characteristic-`p` form of the divided-derivative identity: for a polynomial over a ring
of characteristic `p`, `k` times the `p * k`-th coefficient of `q ^ p` is the `(p * k - 1)`-st
coefficient of `q ^ (p - 1) * q'`. -/
private theorem coeff_divided_deriv {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [CharP R p] (q : Polynomial R) (k : ℕ) (hk : 0 < k) :
    (k : R) * (q ^ p).coeff (p * k) =
      (q ^ (p - 1) * Polynomial.derivative q).coeff (p * k - 1) := by
  classical
  let e : MvPolynomial ℕ ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) q.coeff
  let Q : Polynomial (MvPolynomial ℕ ℤ) :=
    ∑ n ∈ q.support, Polynomial.C (MvPolynomial.X n) * Polynomial.X ^ n
  have hmap : Q.map e = q := by
    ext n
    by_cases hn : q.coeff n = 0 <;> simp [Q, e, hn]
  have hcoeff (f : Polynomial (MvPolynomial ℕ ℤ)) (n : ℕ) :
      e (f.coeff n) = (Polynomial.map e f).coeff n := by simp
  have hcoeffQ : e ((Q ^ p).coeff (p * k)) = (q ^ p).coeff (p * k) := by
    rw [hcoeff, Polynomial.map_pow, hmap]
  calc
    (k : R) * (q ^ p).coeff (p * k) =
        e ((k : MvPolynomial ℕ ℤ) * (Q ^ p).coeff (p * k)) := by
      rw [map_mul, ← hcoeffQ]
      simp
    _ = e ((Q ^ (p - 1) * Polynomial.derivative Q).coeff (p * k - 1)) :=
      congrArg e (coeff_divided_deriv_univ p k (Fact.out : p.Prime).pos hk Q)
    _ = (q ^ (p - 1) * Polynomial.derivative q).coeff (p * k - 1) := by
      rw [hcoeff, Polynomial.map_mul, Polynomial.map_pow,
        ← Polynomial.derivative_map, hmap]

/-- The defining rule for the differential trace on
`R[X] / (X ^ p - a)`: it extracts the `X ^ (p - 1) dX` coefficient and
multiplies it by the absolute differential `da`. -/
def IsPthRootDifferentialTrace (p : ℕ) {R : Type u} [CommRing R] (a : R)
    (tr : Ω[AdjoinRoot (X ^ p - C a)⁄R] →ₗ[R] Ω[R⁄ℤ]) : Prop :=
  ∀ i < p,
    tr ((AdjoinRoot.root (X ^ p - C a)) ^ i •
      KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
        (AdjoinRoot.root (X ^ p - C a))) =
      if i = p - 1 then KaehlerDifferential.D ℤ R a else 0

/-- The differential trace of a degree-`p` purely inseparable algebra, together
with its values on the standard differential basis. -/
noncomputable def pthRootDifferentialTrace (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p] (a : R) :
    {tr : Ω[AdjoinRoot (X ^ p - C a)⁄R] →ₗ[R] Ω[R⁄ℤ] //
      IsPthRootDifferentialTrace p a tr} := by
  classical
  let P := Polynomial R
  let f : P := X ^ p - C a
  let A := AdjoinRoot f
  let x : A := AdjoinRoot.root f
  letI : Algebra P A := (AdjoinRoot.mkₐ f).toRingHom.toAlgebra
  letI : Algebra R P := inferInstance
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Nontrivial R := CharP.nontrivial_of_char_ne_one
    (Fact.out : Nat.Prime p).ne_one
  have hf : f.Monic := monic_X_pow_sub_C a (Fact.out : Nat.Prime p).ne_zero
  have hnat : f.natDegree = p := natDegree_X_pow_sub_C
  have hsurj : Function.Surjective (algebraMap P A) := by
    intro y
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (g := f) y
    exact ⟨q, by change AdjoinRoot.mk f q = y; exact hq⟩
  have hker : RingHom.ker (algebraMap P A) = Ideal.span {f} := by
    ext q
    change AdjoinRoot.mk f q = 0 ↔ q ∈ Ideal.span {f}
    rw [AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have hdf : KaehlerDifferential.D R P f = 0 := by
    apply (KaehlerDifferential.polynomialEquiv R).injective
    rw [KaehlerDifferential.polynomialEquiv_D]
    simp [f, derivative_X_pow]
  have hcot (z : (RingHom.ker (algebraMap P A)).Cotangent) :
      KaehlerDifferential.kerCotangentToTensor R P A z = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ z
    have hy : (y : P) ∈ Ideal.span {f} := hker ▸ y.2
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hy
    have hyq : (y : P) = f * q := hq
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent, hyq,
      (KaehlerDifferential.D R P).leibniz, hdf]
    have hfA' : algebraMap P A f = 0 := by
      change AdjoinRoot.mk f f = 0
      exact AdjoinRoot.mk_self
    have hfA : (f : P) • (1 : A) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact hfA'
    simp only [smul_zero, add_zero]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change ((f : P) • (1 : A)) ⊗ₜ[P] KaehlerDifferential.D R P q = 0
    rw [hfA]
    simp
  have hmap_inj : Function.Injective (KaehlerDifferential.mapBaseChange R P A) := by
    intro v w hvw
    apply sub_eq_zero.mp
    have hzero : KaehlerDifferential.mapBaseChange R P A (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    obtain ⟨z, hz⟩ :=
      ((KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R P A hsurj)
        (v - w)).mp hzero
    rw [← hz]
    exact hcot z
  let e := LinearEquiv.ofBijective (KaehlerDifferential.mapBaseChange R P A)
    ⟨hmap_inj, KaehlerDifferential.mapBaseChange_surjective R P A hsurj⟩
  let PB := AdjoinRoot.powerBasis' hf
  let β := PB.basis
  let values : Fin PB.dim → Ω[R⁄ℤ] := fun i =>
    if (i : ℕ) = p - 1 then KaehlerDifferential.D ℤ R a else 0
  let coeffMap : A →ₗ[R] Ω[R⁄ℤ] := β.constr R values
  let tensorCoeff : A ⊗[P] Ω[P⁄R] →ₗ[P] A :=
    (TensorProduct.rid P A).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : A →ₗ[P] A)
        (KaehlerDifferential.polynomialEquiv R).toLinearMap)
  let trace : Ω[A⁄R] →ₗ[R] Ω[R⁄ℤ] :=
    coeffMap.comp ((tensorCoeff.restrictScalars R).comp
      (e.symm.restrictScalars R).toLinearMap)
  refine ⟨trace, ?_⟩
  intro i hi
  have hi' : i < PB.dim := by simpa [PB, AdjoinRoot.powerBasis', hnat] using hi
  let j : Fin PB.dim := ⟨i, hi'⟩
  have hbasis : β j = x ^ i := (PB.basis_eq_pow j).trans (by simp [PB, x, j])
  have hinv : e.symm (KaehlerDifferential.D R A x) =
      1 ⊗ₜ[P] KaehlerDifferential.D R P X := by
    rw [LinearEquiv.symm_apply_eq]
    change _ = KaehlerDifferential.mapBaseChange R P A _
    rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    exact (one_smul _ _).symm
  have hcoeff : tensorCoeff (x ^ i • (1 ⊗ₜ[P] KaehlerDifferential.D R P X)) = x ^ i := by
    rw [TensorProduct.smul_tmul']
    change (TensorProduct.rid P A)
      ((TensorProduct.map (LinearMap.id : A →ₗ[P] A)
        (KaehlerDifferential.polynomialEquiv R).toLinearMap)
        ((x ^ i • (1 : A)) ⊗ₜ[P] KaehlerDifferential.D R P X)) = x ^ i
    rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
      KaehlerDifferential.polynomialEquiv_D]
    simp
  change coeffMap (tensorCoeff (e.symm
    (x ^ i • KaehlerDifferential.D R A x))) = _
  rw [map_smul, hinv, hcoeff]
  change (β.constr R values) (x ^ i) = _
  rw [← hbasis, β.constr_basis]

/-- A derivation applied to the evaluation of a polynomial with coefficients in the base ring is
the evaluation of its derivative, scaled by the derivation of the point. -/
private theorem deriv_eval₂ {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    (D : Derivation R S M) (x : S) (P : Polynomial R) :
    D (P.eval₂ (algebraMap R S) x) =
      (P.derivative.eval₂ (algebraMap R S) x) • D x := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      simp [Polynomial.eval₂_add, Polynomial.derivative_add, ihP, ihQ, add_smul]
  | monomial n c =>
      simp [Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
        D.leibniz, D.map_algebraMap, D.leibniz_pow]
      module

/-- The class of `X` in `R[X] / (X ^ p - a)` is a `p`-th root of `a`. -/
private theorem adjoinRoot_root_pow_eq {R : Type*} [CommRing R] (p : ℕ) (a : R) :
    (AdjoinRoot.root (X ^ p - C a)) ^ p = algebraMap R (AdjoinRoot (X ^ p - C a)) a := by
  have h := AdjoinRoot.eval₂_root (X ^ p - C a)
  change (X ^ p - C a).eval₂ (AdjoinRoot.of (X ^ p - C a))
    (AdjoinRoot.root (X ^ p - C a)) = 0 at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  simpa [AdjoinRoot.algebraMap_eq] using h

/-- The differentials `x ^ i • dx` for `i < p` span the relative differentials of
`R[X] / (X ^ p - a)` over `R`. -/
private theorem pthRootDifferential_span (p : ℕ) [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] (a : R) :
    Submodule.span R (Set.range fun i : Fin p =>
      (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) •
        KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
          (AdjoinRoot.root (X ^ p - C a))) = ⊤ := by
  classical
  let f : Polynomial R := X ^ p - C a
  let A := AdjoinRoot f
  let x : A := AdjoinRoot.root f
  let dx : Ω[A⁄R] := KaehlerDifferential.D R A x
  let gen : Fin p → Ω[A⁄R] := fun i => x ^ (i : ℕ) • dx
  let M : Submodule R Ω[A⁄R] := Submodule.span R (Set.range gen)
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hxpow : x ^ p = algebraMap R A a := adjoinRoot_root_pow_eq p a
  have hdx : dx ∈ M := Submodule.subset_span ⟨⟨0, hp⟩, by simp [gen, dx]⟩
  have hgen : ∀ i : Fin p, x • gen i ∈ M := by
    intro i
    by_cases hi : (i : ℕ) + 1 < p
    · let j : Fin p := ⟨(i : ℕ) + 1, hi⟩
      have hj : x • gen i = gen j := by
        simp [gen, j, pow_succ, mul_smul, mul_comm]
      rw [hj]
      exact Submodule.subset_span ⟨j, rfl⟩
    · have heq : (i : ℕ) + 1 = p := by omega
      have hj : x • gen i = (algebraMap R A a) • dx := by
        change x • (x ^ (i : ℕ) • dx) = (algebraMap R A a) • dx
        rw [← mul_smul, ← pow_succ', heq, hxpow]
      rw [hj, algebraMap_smul A a]
      exact M.smul_mem a hdx
  have hxstable : ∀ v, v ∈ M → x • v ∈ M := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => x • v ∈ M) ?_ ?_ ?_ ?_ hv
    · rintro y ⟨i, rfl⟩
      exact hgen i
    · simp
    · intro y z hy hz ihy ihz
      simpa [smul_add] using M.add_mem ihy ihz
    · intro c y hy ih
      rw [smul_comm]
      exact M.smul_mem c ih
  have hpowstable : ∀ n v, v ∈ M → x ^ n • v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
        intro v hv
        rw [pow_succ', mul_smul]
        exact hxstable (x ^ n • v) (ih v hv)
  have hpolyStable : ∀ P : Polynomial R, ∀ v, v ∈ M →
      (P.eval₂ (algebraMap R A) x) • v ∈ M := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q ihP ihQ =>
        intro v hv
        rw [Polynomial.eval₂_add, add_smul]
        exact M.add_mem (ihP v hv) (ihQ v hv)
    | monomial n c =>
        intro v hv
        rw [Polynomial.eval₂_monomial, mul_smul, algebraMap_smul A c]
        exact M.smul_mem c (hpowstable n v hv)
  have hscalarStable : ∀ s : A, ∀ v, v ∈ M → s • v ∈ M := by
    intro s v hv
    induction s using AdjoinRoot.induction_on with
    | ih P =>
        rw [← AdjoinRoot.aeval_eq (f := f) P, Polynomial.aeval_def]
        exact hpolyStable P v hv
  have hD : ∀ t : A, KaehlerDifferential.D R A t ∈ M := by
    intro t
    induction t using AdjoinRoot.induction_on with
    | ih P =>
        rw [← AdjoinRoot.aeval_eq (f := f) P, Polynomial.aeval_def,
          deriv_eval₂]
        exact hscalarStable _ dx hdx
  let N : Submodule A Ω[A⁄R] :=
    { carrier := M
      zero_mem' := M.zero_mem
      add_mem' := M.add_mem
      smul_mem' := fun s v hv => hscalarStable s v hv }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation R A, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hD t
  change M = ⊤
  simpa [N] using hN

/-- Two linear maps obeying the defining rule for the differential trace are equal. -/
private theorem pthRootDifferentialTrace_unique (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p] (a : R)
    (tr₁ tr₂ : Ω[AdjoinRoot (X ^ p - C a)⁄R] →ₗ[R] Ω[R⁄ℤ])
    (h₁ : IsPthRootDifferentialTrace p a tr₁)
    (h₂ : IsPthRootDifferentialTrace p a tr₂) : tr₁ = tr₂ := by
  refine LinearMap.ext fun z => ?_
  have hz : z ∈ Submodule.span R (Set.range fun i : Fin p =>
      (AdjoinRoot.root (X ^ p - C a)) ^ (i : ℕ) •
        KaehlerDifferential.D R (AdjoinRoot (X ^ p - C a))
          (AdjoinRoot.root (X ^ p - C a))) := by
    rw [pthRootDifferential_span p a]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro y ⟨i, rfl⟩
    exact h₁ (i : ℕ) i.isLt |>.trans (h₂ (i : ℕ) i.isLt).symm
  · simp
  · intro x y hx hy ihx ihy
    simp [ihx, ihy]
  · intro c x hx ih
    simp [ih]

/-- The `p`-th Cartier operator on polynomials: it keeps the coefficients whose degree is
congruent to `p - 1` modulo `p` and re-indexes them by the quotient. -/
private noncomputable def pthCartierPolynomial {R : Type*} [CommSemiring R] (p : ℕ)
    (P : Polynomial R) : Polynomial R :=
  P.sum fun n c => if n % p = p - 1 then Polynomial.monomial (n / p) c else 0

/-- The coefficients of the `p`-th Cartier operator applied to `P`. -/
private theorem coeff_pthCartierPolynomial {R : Type*} [CommSemiring R] (p : ℕ)
    (hp : 0 < p)
    (P : Polynomial R) (k : ℕ) :
    (pthCartierPolynomial p P).coeff k = P.coeff (p * k + (p - 1)) := by
  classical
  unfold pthCartierPolynomial
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff]
  change (∑ n ∈ P.support,
    (if n % p = p - 1 then Polynomial.monomial (n / p) (P.coeff n) else 0).coeff k) = _
  rw [Finset.sum_eq_single (p * k + (p - 1))]
  · have hlt : p - 1 < p := by omega
    have hmod : (p * k + (p - 1)) % p = p - 1 := by
      rw [Nat.add_mod, Nat.mul_mod_right]
      simp [Nat.mod_eq_of_lt hlt]
    have hdiv : (p * k + (p - 1)) / p = k := by
      have hsum : (p * k) % p + (p - 1) % p < p := by
        rw [Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
        simpa using hlt
      rw [Nat.add_div_eq_of_add_mod_lt hsum, Nat.mul_div_cancel_left k hp, Nat.div_eq_of_lt hlt,
        add_zero]
    simp [hmod, hdiv]
  · intro n hn hne
    by_cases hmod : n % p = p - 1
    · by_cases hdiv : n / p = k
      · have hindex : n = p * k + (p - 1) := by
          rw [← Nat.mod_add_div n p, hmod, hdiv]
          ring
        exact (hne hindex).elim
      · simp only [ite_eq_left hmod, Polynomial.coeff_monomial]
        simp [hdiv]
    · simp [hmod]
  · intro hnot
    have hc : P.coeff (p * k + (p - 1)) = 0 := by
      simpa [Polynomial.mem_support_iff] using hnot
    simp [hc]

/-- The value of a differential trace on `P(x) • dx`, computed through the Cartier operator. -/
private theorem trace_polynomial_eval {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] (b : R)
    (tr : Ω[AdjoinRoot (X ^ p - C b)⁄R] →ₗ[R] Ω[R⁄ℤ])
    (htr : IsPthRootDifferentialTrace p b tr) (P : Polynomial R) :
    tr ((P.eval₂ (algebraMap R (AdjoinRoot (X ^ p - C b)))
      (AdjoinRoot.root (X ^ p - C b))) •
        KaehlerDifferential.D R (AdjoinRoot (X ^ p - C b))
          (AdjoinRoot.root (X ^ p - C b))) =
      (pthCartierPolynomial p P).eval b • KaehlerDifferential.D ℤ R b := by
  classical
  let B := AdjoinRoot (X ^ p - C b)
  let y : B := AdjoinRoot.root (X ^ p - C b)
  let dy : Ω[B⁄R] := KaehlerDifferential.D R B y
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hy : y ^ p = algebraMap R B b := adjoinRoot_root_pow_eq p b
  have hterm (n : ℕ) (c : R) :
      tr ((algebraMap R B c * y ^ n) • dy) =
        (if n % p = p - 1 then c * b ^ (n / p) else 0) •
          KaehlerDifferential.D ℤ R b := by
    have hpow : y ^ n = algebraMap R B (b ^ (n / p)) * y ^ (n % p) := by
      rw [map_pow, ← hy, ← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hpow, ← mul_assoc, ← map_mul, mul_smul, algebraMap_smul B, LinearMap.map_smul,
      htr (n % p) (Nat.mod_lt _ hp)]
    by_cases hr : n % p = p - 1 <;> simp [hr]
  have hterm' (n : ℕ) (c : R) :
      tr ((algebraMap R (AdjoinRoot (X ^ p - C b)) c *
        (AdjoinRoot.root (X ^ p - C b)) ^ n) •
          KaehlerDifferential.D R (AdjoinRoot (X ^ p - C b))
            (AdjoinRoot.root (X ^ p - C b))) =
        (if n % p = p - 1 then c * b ^ (n / p) else 0) •
          KaehlerDifferential.D ℤ R b := by
    simpa [B, y, dy] using hterm n c
  have hEval (n : ℕ) (c : R) :
      (if n % p = p - 1 then Polynomial.monomial (n / p) c else 0).eval b =
        if n % p = p - 1 then c * b ^ (n / p) else 0 := by
    by_cases hn : n % p = p - 1 <;> simp [hn, Polynomial.eval_monomial]
  conv_lhs => rw [P.as_sum_support]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    Finset.sum_smul, map_sum]
  change (∑ n ∈ P.support,
    tr ((algebraMap R (AdjoinRoot (X ^ p - C b)) (P.coeff n) *
      (AdjoinRoot.root (X ^ p - C b)) ^ n) •
        KaehlerDifferential.D R (AdjoinRoot (X ^ p - C b))
          (AdjoinRoot.root (X ^ p - C b)))) = _
  simp_rw [hterm']
  unfold pthCartierPolynomial
  rw [Polynomial.sum_def, Polynomial.eval_finsetSum]
  simp_rw [hEval]
  simp [Finset.sum_smul]

/-- The `p`-th Cartier operator annihilates `Q ^ i * Q'` when `i + 1 < p`. -/
private theorem pthCartier_deriv_power_lt {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [CharP R p] (Q : Polynomial R) (i : ℕ) (hi : i + 1 < p) :
    pthCartierPolynomial p (Q ^ i * Polynomial.derivative Q) = 0 := by
  classical
  apply Polynomial.ext
  intro k
  rw [coeff_pthCartierPolynomial p (Fact.out : Nat.Prime p).pos]
  have ndef : p * k + (p - 1) + 1 = p * (k + 1) := by
    have := (Fact.out : p.Prime).pos
    rw [mul_add_one]
    omega
  have hpoly : Polynomial.derivative (Q ^ (i + 1)) =
      Polynomial.C (i + 1 : R) * (Q ^ i * Polynomial.derivative Q) := by
    simpa [mul_assoc] using (Polynomial.derivative_pow Q (i + 1))
  have hcoeff := congrArg (fun f : Polynomial R => f.coeff (p * k + (p - 1))) hpoly
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul] at hcoeff
  have hcast : (↑(p * k + (p - 1)) : R) + 1 = (p : R) * (k + 1 : R) := by
    have htmp := congrArg (fun n : ℕ => (n : R)) ndef
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using htmp
  rw [hcast] at hcoeff
  simp only [CharP.cast_eq_zero R p, zero_mul, mul_zero] at hcoeff
  have hnotdvd : ¬ p ∣ i + 1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hi
  have hunitNat : IsUnit ((i + 1 : ℕ) : R) :=
    (CharP.isUnit_natCast_iff (R := R) (Fact.out : Nat.Prime p)).2 hnotdvd
  have hunit : IsUnit ((i : R) + 1) := by
    simpa [Nat.cast_add] using hunitNat
  exact hunit.mul_left_cancel (show (i + 1 : R) *
    (Q ^ i * Polynomial.derivative Q).coeff (p * k + (p - 1)) =
    (i + 1 : R) * 0 by simpa using hcoeff.symm)

/-- In characteristic `p`, `Q ^ p` is the Frobenius twist of `Q` composed with `X ^ p`. -/
private theorem pow_eq_comp_map_frobenius {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    [CharP R p] (Q : Polynomial R) :
    Q ^ p = (Q.map (frobenius R p)).comp (X ^ p) :=
  calc
    Q ^ p = Polynomial.map (frobenius R p) (Polynomial.expand R p Q) :=
      (Polynomial.map_frobenius_expand (p := p) Q).symm
    _ = Polynomial.expand R p (Q.map (frobenius R p)) := by rw [Polynomial.map_expand]
    _ = (Q.map (frobenius R p)).comp (X ^ p) :=
      Polynomial.expand_eq_comp_X_pow (R := R) (p := p)

/-- On `Q ^ (p - 1) * Q'` the `p`-th Cartier operator gives the derivative of the Frobenius
twist of `Q`. -/
private theorem pthCartier_deriv_power_eq_map_frobenius {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p] (Q : Polynomial R) :
    pthCartierPolynomial p (Q ^ (p - 1) * Polynomial.derivative Q) =
      Polynomial.derivative (Q.map (frobenius R p)) := by
  classical
  let G := Q.map (frobenius R p)
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  apply Polynomial.ext
  intro k
  rw [coeff_pthCartierPolynomial p hp]
  have hidx : p * (k + 1) - 1 = p * k + (p - 1) := by
    calc
      p * (k + 1) - 1 = (p * k + p) - 1 := by rw [Nat.mul_add, mul_one]
      _ = p * k + (p - 1) := by omega
  have hdiv := coeff_divided_deriv Q (k + 1) (Nat.succ_pos k)
  rw [hidx] at hdiv
  have hfrob : Q ^ p = G.comp (Polynomial.X ^ p) := pow_eq_comp_map_frobenius Q
  have hcoeff : (Q ^ p).coeff (p * (k + 1)) = G.coeff (k + 1) := by
    rw [hfrob, ← Polynomial.expand_eq_comp_X_pow]
    simpa [Nat.mul_comm] using Polynomial.coeff_expand_mul hp G (k + 1)
  rw [hcoeff] at hdiv
  rw [Polynomial.coeff_derivative]
  simpa [G, Nat.cast_add, mul_comm] using hdiv.symm

/-- A derivation annihilating every coefficient of `P` sends `P.eval x` to
`P.derivative.eval x • D x`. -/
private theorem deriv_eval_of_coeff_deriv_zero {R M : Type*} [CommRing R]
    [AddCommMonoid M] [Module ℤ M] [Module R M] [IsScalarTower ℤ R M]
    (D : Derivation ℤ R M) (P : Polynomial R) (x : R)
    (hcoeff : ∀ n, D (P.coeff n) = 0) :
    D (P.eval x) = (P.derivative.eval x) • D x := by
  classical
  conv_lhs => rw [P.as_sum_support]
  conv_rhs => rw [P.as_sum_support]
  rw [Polynomial.eval_finsetSum, map_sum, Polynomial.derivative_sum,
    Polynomial.eval_finsetSum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Polynomial.eval_monomial, D.leibniz, hcoeff n, D.leibniz_pow,
    Polynomial.derivative_monomial]
  module

/-- Composing a differential trace for `b` with the map on differentials induced by `φ` again
obeys the defining rule, now for `a`. -/
private theorem pthRootDifferentialTrace_comp_is (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p] (a b : R)
    (φ : AdjoinRoot (X ^ p - C a) →ₐ[R] AdjoinRoot (X ^ p - C b))
    (trY : Ω[AdjoinRoot (X ^ p - C b)⁄R] →ₗ[R] Ω[R⁄ℤ])
    (hY : IsPthRootDifferentialTrace p b trY) :
    letI : Algebra (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C b)) :=
      φ.toRingHom.toAlgebra
    IsPthRootDifferentialTrace p a (trY.comp ((KaehlerDifferential.map R R
      (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C b))).restrictScalars R)) := by
  classical
  let A := AdjoinRoot (X ^ p - C a)
  let B := AdjoinRoot (X ^ p - C b)
  let x : A := AdjoinRoot.root (X ^ p - C a)
  let y : B := AdjoinRoot.root (X ^ p - C b)
  let f : Polynomial R := X ^ p - C a
  let g : Polynomial R := X ^ p - C b
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  let : Algebra A B := φ.toRingHom.toAlgebra
  have hmap_inj : Function.Injective (algebraMap R B) := by
    by_cases hR : Nontrivial R
    · let : Nontrivial R := hR
      have hdeg : 0 < g.degree := by
        change 0 < (X ^ p - C b).degree
        rw [degree_X_pow_sub_C hp]
        exact_mod_cast hp
      intro r s hrs
      apply (AdjoinRoot.of.injective_of_monic_of_degree_pos
        (monic_X_pow_sub_C b hp.ne') hdeg)
      rw [AdjoinRoot.algebraMap_eq] at hrs
      exact hrs
    · let : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      intro r s _
      exact Subsingleton.elim _ _
  let tr : Ω[A⁄R] →ₗ[R] Ω[R⁄ℤ] := trY.comp
    ((KaehlerDifferential.map R R A B).restrictScalars R)
  have hxp : x ^ p = algebraMap R A a := adjoinRoot_root_pow_eq p a
  have hyp : y ^ p = algebraMap R B b := adjoinRoot_root_pow_eq p b
  intro i hi
  change tr (x ^ i • KaehlerDifferential.D R A x) =
    (if i = p - 1 then KaehlerDifferential.D ℤ R a else 0)
  have hdx : KaehlerDifferential.map R R A B
      (KaehlerDifferential.D R A x) =
      KaehlerDifferential.D R B (algebraMap A B x) :=
    KaehlerDifferential.map_D R R A B x
  have hgen : tr (x ^ i • KaehlerDifferential.D R A x) =
      trY ((algebraMap A B x) ^ i •
        KaehlerDifferential.D R B (algebraMap A B x)) := by
    change trY ((KaehlerDifferential.map R R A B)
      (x ^ i • KaehlerDifferential.D R A x)) = _
    rw [map_smul, hdx, ← IsScalarTower.algebraMap_smul (R := A) (A := B) (r := x ^ i), map_pow]
  rw [hgen]
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective (g := g) (algebraMap A B x)
  have hQeval : Q.eval₂ (algebraMap R B) y = algebraMap A B x := by
    rw [← Polynomial.aeval_def, AdjoinRoot.aeval_eq, hQ]
  let G : Polynomial R := Q.map (frobenius R p)
  have hfrob : Q ^ p = G.comp (X ^ p) := pow_eq_comp_map_frobenius Q
  have hpowQ : (Q.eval₂ (algebraMap R B) y) ^ p =
      algebraMap R B (G.eval b) := by
    calc
      (Q.eval₂ (algebraMap R B) y) ^ p =
          (Q ^ p).eval₂ (algebraMap R B) y := by rw [eval₂_pow]
      _ = (G.comp (X ^ p)).eval₂ (algebraMap R B) y := by rw [hfrob]
      _ = G.eval₂ (algebraMap R B) (y ^ p) := by
        rw [eval₂_comp, eval₂_X_pow]
      _ = G.eval₂ (algebraMap R B) (algebraMap R B b) := by rw [hyp]
      _ = algebraMap R B (G.eval b) := by simp [eval₂_at_apply]
  have hpowx : (algebraMap A B x) ^ p = algebraMap R B a := by
    calc
      (algebraMap A B x) ^ p = algebraMap A B (x ^ p) := by rw [map_pow]
      _ = algebraMap A B (algebraMap R A a) := by rw [hxp]
      _ = algebraMap R B a := by simp [IsScalarTower.algebraMap_eq R A B]
  have hGa : G.eval b = a := by
    apply hmap_inj
    rw [← hpowQ, hQeval, hpowx]
  have hcoeff : ∀ n, (KaehlerDifferential.D ℤ R) (G.coeff n) = 0 := by
    intro n
    rw [show G.coeff n = (frobenius R p) (Q.coeff n) by simp [G]]
    simp only [frobenius_def]
    rw [(KaehlerDifferential.D ℤ R).leibniz_pow, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero R p,
      zero_smul]
  have hzero (j : ℕ) (hj : j + 1 < p) :
      pthCartierPolynomial p (Q ^ j * derivative Q) = 0 :=
    pthCartier_deriv_power_lt Q j hj
  have htop : pthCartierPolynomial p (Q ^ (p - 1) * derivative Q) = derivative G := by
    simpa [G] using pthCartier_deriv_power_eq_map_frobenius Q
  have hderiv : (KaehlerDifferential.D ℤ R) (G.eval b) =
      (derivative G).eval b • KaehlerDifferential.D ℤ R b :=
    deriv_eval_of_coeff_deriv_zero (KaehlerDifferential.D ℤ R) G b hcoeff
  have hDa : KaehlerDifferential.D ℤ R a =
      (derivative G).eval b • KaehlerDifferential.D ℤ R b := by
    rw [← hGa]
    exact hderiv
  have htrace_formula : ∀ j : ℕ,
      trY ((Q.eval₂ (algebraMap R B) y) ^ j •
        (derivative Q).eval₂ (algebraMap R B) y •
          KaehlerDifferential.D R B y) =
      (pthCartierPolynomial p (Q ^ j * derivative Q)).eval b •
        KaehlerDifferential.D ℤ R b := by
    intro j
    calc
      trY (Q.eval₂ (algebraMap R B) y ^ j •
          (derivative Q).eval₂ (algebraMap R B) y •
            KaehlerDifferential.D R B y) =
          trY (((Q ^ j * derivative Q).eval₂ (algebraMap R B) y) •
            KaehlerDifferential.D R B y) := by
        congr 1
        simp [eval₂_mul, eval₂_pow, mul_smul]
      _ = (pthCartierPolynomial p (Q ^ j * derivative Q)).eval b •
          KaehlerDifferential.D ℤ R b :=
        trace_polynomial_eval b trY hY (Q ^ j * derivative Q)
  have hderivQ : KaehlerDifferential.D R B (Q.eval₂ (algebraMap R B) y) =
      (derivative Q).eval₂ (algebraMap R B) y • KaehlerDifferential.D R B y :=
    deriv_eval₂ (KaehlerDifferential.D R B) y Q
  rw [← hQeval, hderivQ, htrace_formula]
  by_cases hiTop : i = p - 1
  · subst i
    rw [htop, hDa]
    simp
  · have hi' : i + 1 < p := by omega
    rw [hzero i hi']
    simp [hiTop]

/-- Differential traces for two presentations of a degree-`p` purely inseparable algebra
are intertwined by every `R`-algebra homomorphism between the presentations. -/
@[stacks 0ADZ]
theorem pthRootDifferentialTrace_eq_comp_map (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] [CharP R p] (a b : R)
    (φ : AdjoinRoot (X ^ p - C a) →ₐ[R] AdjoinRoot (X ^ p - C b))
    (trX : Ω[AdjoinRoot (X ^ p - C a)⁄R] →ₗ[R] Ω[R⁄ℤ])
    (trY : Ω[AdjoinRoot (X ^ p - C b)⁄R] →ₗ[R] Ω[R⁄ℤ])
    (hX : IsPthRootDifferentialTrace p a trX)
    (hY : IsPthRootDifferentialTrace p b trY) :
    letI : Algebra (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C b)) :=
      φ.toRingHom.toAlgebra
    trX = trY.comp ((KaehlerDifferential.map R R
      (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C b))).restrictScalars R) := by
  let : Algebra (AdjoinRoot (X ^ p - C a)) (AdjoinRoot (X ^ p - C b)) :=
    φ.toRingHom.toAlgebra
  exact pthRootDifferentialTrace_unique p a trX _ hX
    (pthRootDifferentialTrace_comp_is p a b φ trY hY)

end KaehlerDifferential
