module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBlowup
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# The normal cone inside the blowup at infinity

Let `X` be a scheme, let `ℐ` be a quasi-coherent sheaf of ideals with closed subscheme
`Z ⊆ X`, and let `b : W ⟶ 𝐏¹_X` be the blowup at infinity of
`StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBlowup`, with exceptional divisor `E ⊆ W`,
fibre at infinity `W_∞ ⊆ W` and strict transform `X' ⊆ W`. Clause (7) of Stacks 0FBG, which is
Stacks 0FBH, reads

  `E ∖ X' = E ∖ (X' ∩ E) = Spec_Z(𝒞_{Z/X,*}) = C_ZX`.

This file supplies the first equality and the affine computation on which the source bases the
remaining two.

The first equality is a statement about supports: `X' ∩ E` is cut out on `E` by the inverse image
of the ideal sheaf of `X'`, so the open subscheme of `E` it misses is the inverse image of the
open `W ∖ X'`.

The remaining two equalities are proved in the source on the chart `D₊(S) ⊆ W` over an affine open
`Spec A ⊆ X` with `Z ∩ Spec A` cut out by `I ⊆ A`: there `W` is the blowup of `A[s]` in
`J = (I, s)`, the chart is the spectrum of the affine blowup algebra `A[s][J/s]`, the element `s`
cuts out both `E` and `W_∞` on it, and the quotient of `A[s][J/s]` by `s` is the conormal algebra
`A/I ⊕ I/I² ⊕ I²/I³ ⊕ ⋯`. That last identification is the mathematical content of the clause, and
it is proved here as an isomorphism of rings.

## Main definitions

* `Stacks.Chow.strictTransformIdealAtInfinity` — the ideal sheaf of `X' ⊆ W`, and
  `Stacks.Chow.strictTransformIdealOnExceptional` the ideal sheaf of `X' ∩ E ⊆ E`.
* `Stacks.Chow.infinityChartIdeal` — the ideal `J = (I, s) ⊆ A[s]` whose blowup `W` is over an
  affine chart `Spec A` of `X`.
* `Stacks.Chow.infinityChartAlgebra` — the affine blowup algebra `A[s][J/s]`, the chart `D₊(S)`,
  with `Stacks.Chow.infinityChartFibreIdeal` the ideal `(s)` cutting out `E` on it.
* `Stacks.Chow.conormalToInfinityChartFibre` — the comparison ring map from the associated graded
  ring of `I` to `A[s][J/s] ⧸ (s)`.

## Main results

* `Stacks.Chow.support_compl_strictTransformIdealOnExceptional` — the first equality of the
  clause: `E ∖ (X' ∩ E) = E ∖ X'` as open subschemes of `E`.
* `Stacks.Chow.mem_pow_infinityChartIdeal_iff` — the description of the powers of `J = (I, s)`:
  `f ∈ Jᵐ` exactly when the coefficient of `sʲ` in `f` lies in `I^(m - j)` for every `j`.
* `Stacks.Chow.infinityChartMk_mem_fibreIdeal_iff` — on the chart, `p/sᴺ` is divisible by `s`
  exactly when `p ∈ J^(N+1)`; equivalently `s` cuts the chart down to the associated graded ring.
* `Stacks.Chow.conormalEquivInfinityChartFibre` — the quotient of `A[s][J/s]` by `s` is the
  conormal algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` of `I` in `A`, as graded rings.

## What is not proved here

The last two equalities of the clause are not obtained globally. The affine charts of a blowup are
available — `Stacks.Blowup.blowUpAffineChart` presents the part of `W` over an affine open
`U ⊆ 𝐏¹_X` as the union of the spectra of the affine blowup algebras `Γ(𝐏¹_X, U)[ℐ(U)/a]` — and so
is the chart computation below, so two things separate them from
`E ∖ X' = Spec_Z(𝒞_{Z/X,*}) = C_ZX`. The isomorphism below has to be shown compatible with the
restriction maps between affine opens, and matched against the chart description of the relative
spectrum of `𝒞_{Z/X,*}` over `Z`; and the open `E ∖ X'` has to be identified with the union of the
charts attached to the sections `s`, which in the source rests on clause (5) of Stacks 0FBG, the
presentation of `E` as the relative `Proj` of `𝒞_{Z/X,*}[S]`. Clause (5) is not in the library, and
neither is clause (4), `W_∞ = X' + E`, which is what makes the complement of `X'` in `W_∞` an open
subscheme of `E` in the first place. The normal cone `Stacks.Conormal.normalCone` with its
projection to `Z` does exist, so the target of the comparison is available.

## References

* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### The strict transform inside the exceptional divisor -/

section Geometry

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The ideal sheaf of the strict transform `X' ⊆ W`: the kernel of the closed immersion of the
blowup of `X` in `Z` into the blowup at infinity. -/
def strictTransformIdealAtInfinity : (blowupAtInfinity ℐ).IdealSheafData :=
  (blowUpToBlowupAtInfinity ℐ).ker

/-- The exceptional divisor `E ⊆ W` of the blowup at infinity, as a scheme. -/
abbrev exceptionalDivisorAtInfinity : Scheme.{u} :=
  (exceptionalIdealAtInfinity ℐ).subscheme

/-- The ideal sheaf of `X' ∩ E ⊆ E`: the inverse image on `E` of the ideal sheaf of `X'`. -/
def strictTransformIdealOnExceptional :
    (exceptionalDivisorAtInfinity ℐ).IdealSheafData :=
  (strictTransformIdealAtInfinity ℐ).comap (exceptionalIdealAtInfinity ℐ).subschemeι

/-- The open subscheme `E ∖ (X' ∩ E)` of the exceptional divisor is the inverse image of the open
`W ∖ X'`, so `E ∖ (X' ∩ E) = E ∖ X'`. -/
@[stacks 0FBH "E ∖ (X' ∩ E) = E ∖ X' as open subschemes of E"]
theorem support_compl_strictTransformIdealOnExceptional :
    (strictTransformIdealOnExceptional ℐ).support.compl =
      (exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
        (strictTransformIdealAtInfinity ℐ).support.compl := by
  rw [strictTransformIdealOnExceptional, Scheme.IdealSheafData.support_comap]
  rfl

end Geometry

/-! ### The chart `D₊(S)` and the powers of `J = (I, s)` -/

section Chart

open Polynomial

variable {A : Type*} [CommRing A]

/-- The centre `J = (I, s) ⊆ A[s]` of the blowup at infinity over an affine chart `Spec A` of
`X` on which `Z` is cut out by `I`. -/
def infinityChartIdeal (I : Ideal A) : Ideal A[X] :=
  I.map (C : A →+* A[X]) ⊔ Ideal.span {(X : A[X])}

/-- The variable `s` lies in `J = (I, s)`. -/
theorem X_mem_infinityChartIdeal (I : Ideal A) : (X : A[X]) ∈ infinityChartIdeal I := by
  rw [infinityChartIdeal]
  exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)

/-- The power `sᵈ` lies in `Jᵈ`. -/
theorem X_pow_mem_pow_infinityChartIdeal (I : Ideal A) (d : ℕ) :
    (X : A[X]) ^ d ∈ infinityChartIdeal I ^ d :=
  Ideal.pow_mem_pow (X_mem_infinityChartIdeal I) d

/-- If `p ∈ Kᵃ` and `q ∈ Kᵇ`, then `p * q ∈ Kᴺ` whenever `N ≤ a + b`. -/
private theorem mul_mem_pow_of_le_add {R : Type*} [CommRing R] {K : Ideal R} {a b N : ℕ} {p q : R}
    (hp : p ∈ K ^ a) (hq : q ∈ K ^ b) (h : N ≤ a + b := by omega) : p * q ∈ K ^ N :=
  Ideal.pow_le_pow_right h (by rw [pow_add]; exact Ideal.mul_mem_mul hp hq)

/-- The ideal of polynomials whose coefficient of `sʲ` lies in `I^(m - j)` for every `j`. It is
the `m`-th power of `J = (I, s)`, by `mem_pow_infinityChartIdeal_iff`. -/
def coeffFiltration (I : Ideal A) (m : ℕ) : Ideal A[X] where
  carrier := {f | ∀ j, f.coeff j ∈ I ^ (m - j)}
  add_mem' {f g} hf hg := by intro j; simpa using add_mem (hf j) (hg j)
  zero_mem' := by intro j; simp
  smul_mem' c f hf := by
    intro j
    rw [smul_eq_mul, Polynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx2 : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (hf x.2))

/-- A polynomial lies in `coeffFiltration I m` exactly when its coefficient of `sʲ` lies in
`I^(m - j)` for every `j`. -/
theorem mem_coeffFiltration {I : Ideal A} {m : ℕ} {f : A[X]} :
    f ∈ coeffFiltration I m ↔ ∀ j, f.coeff j ∈ I ^ (m - j) := Iff.rfl

/-- The `0`-th step of the coefficient filtration is the whole ring. -/
theorem coeffFiltration_zero (I : Ideal A) : coeffFiltration I 0 = ⊤ := by
  ext f; simp [mem_coeffFiltration]

/-- The coefficient filtration is multiplicative: its `m`-th and `n`-th steps multiply into the
`(m + n)`-th. -/
theorem coeffFiltration_mul_coeffFiltration (I : Ideal A) (m n : ℕ) :
    coeffFiltration I m * coeffFiltration I n ≤ coeffFiltration I (m + n) := by
  rw [Ideal.mul_le]
  intro f hf g hg j
  rw [Polynomial.coeff_mul]
  refine Ideal.sum_mem _ fun x hx => ?_
  have hx2 : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
  exact mul_mem_pow_of_le_add (hf x.1) (hg x.2)

/-- The ideal `J = (I, s)` is contained in the first step of the coefficient filtration. -/
theorem infinityChartIdeal_le_coeffFiltration_one (I : Ideal A) :
    infinityChartIdeal I ≤ coeffFiltration I 1 := by
  rw [infinityChartIdeal, sup_le_iff]
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha j
    match j with
    | 0 => simpa using ha
    | (j + 1) => simp
  · rw [Ideal.span_le]
    rintro _ rfl j
    match j with
    | 0 => simp
    | 1 => simp
    | (n + 2) => simp

/-- The power `Jᵐ` is contained in the `m`-th step of the coefficient filtration. -/
theorem pow_infinityChartIdeal_le_coeffFiltration (I : Ideal A) (m : ℕ) :
    infinityChartIdeal I ^ m ≤ coeffFiltration I m := by
  induction m with
  | zero => rw [pow_zero, coeffFiltration_zero]; exact le_top
  | succ m ih =>
      calc infinityChartIdeal I ^ (m + 1)
            = infinityChartIdeal I ^ m * infinityChartIdeal I := by rw [pow_succ]
        _ ≤ coeffFiltration I m * coeffFiltration I 1 :=
            Ideal.mul_mono ih (infinityChartIdeal_le_coeffFiltration_one I)
        _ ≤ coeffFiltration I (m + 1) := coeffFiltration_mul_coeffFiltration I m 1

/-- If `x ∈ Iⁿ` and `N ≤ n + j`, then `x sʲ ∈ Jᴺ`. -/
private theorem C_mul_X_pow_mem_pow_infinityChartIdeal {I : Ideal A} {n j N : ℕ} {x : A}
    (hx : x ∈ I ^ n) (h : N ≤ n + j := by omega) :
    C x * (X : A[X]) ^ j ∈ infinityChartIdeal I ^ N := by
  have h1 : (C x : A[X]) ∈ infinityChartIdeal I ^ n := by
    have h' := Ideal.mem_map_of_mem (C : A →+* A[X]) hx
    rw [Ideal.map_pow] at h'
    exact Ideal.pow_right_mono le_sup_left _ h'
  exact mul_mem_pow_of_le_add h1 (X_pow_mem_pow_infinityChartIdeal I j) h

/-- The `m`-th step of the coefficient filtration is contained in the power `Jᵐ`. -/
theorem coeffFiltration_le_pow_infinityChartIdeal (I : Ideal A) (m : ℕ) :
    coeffFiltration I m ≤ infinityChartIdeal I ^ m := by
  intro f hf
  rw [Polynomial.as_sum_support_C_mul_X_pow f]
  exact Ideal.sum_mem _ fun j _ => C_mul_X_pow_mem_pow_infinityChartIdeal (hf j)

/-- **The powers of `J = (I, s)`.** A polynomial lies in `Jᵐ` exactly when its coefficient of
`sʲ` lies in `I^(m - j)` for every `j`, so `Jᵐ = Iᵐ ⊕ sI^(m-1) ⊕ ⋯ ⊕ sᵐA ⊕ s^(m+1)A ⊕ ⋯`. -/
@[stacks 0FBH "the powers of J = (I, s): the coefficient of s^j lies in I^(m-j)"]
theorem mem_pow_infinityChartIdeal_iff {I : Ideal A} {m : ℕ} {f : A[X]} :
    f ∈ infinityChartIdeal I ^ m ↔ ∀ j, f.coeff j ∈ I ^ (m - j) :=
  ⟨fun h => pow_infinityChartIdeal_le_coeffFiltration I m h,
    fun h => coeffFiltration_le_pow_infinityChartIdeal I m h⟩

/-- A constant `x ∈ Iⁿ` lies in `Jⁿ`. -/
theorem C_mem_pow_infinityChartIdeal {I : Ideal A} {n : ℕ} {x : A} (hx : x ∈ I ^ n) :
    (C x : A[X]) ∈ infinityChartIdeal I ^ n := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro j
  match j with
  | 0 => simpa using hx
  | (j + 1) => simp

/-- The chart `D₊(S) ⊆ W` over an affine chart `Spec A` of `X`: the affine blowup algebra
`A[s][J/s]`, where `J = (I, s)`. -/
abbrev infinityChartAlgebra (I : Ideal A) :
    Subalgebra A[X] (Localization.Away (X : A[X])) :=
  affineBlowup (infinityChartIdeal I) (X : A[X])

/-- The element `p/sⁿ` of the chart, for `p ∈ Jⁿ`. -/
def infinityChartMk (I : Ideal A) (n : ℕ) (p : A[X]) (hp : p ∈ infinityChartIdeal I ^ n) :
    infinityChartAlgebra I :=
  ⟨Localization.mk p (⟨(X : A[X]) ^ n, n, rfl⟩ : Submonoid.powers (X : A[X])),
    mk_mem_affineBlowup_of_mem_pow _ _ hp⟩

/-- The underlying element of `infinityChartMk I n p hp` in the localization at `s` is the
fraction `p/sⁿ`. -/
theorem infinityChartMk_val (I : Ideal A) (n : ℕ) (p : A[X])
    (hp : p ∈ infinityChartIdeal I ^ n) :
    (infinityChartMk I n p hp : Localization.Away (X : A[X])) =
      Localization.mk p (⟨(X : A[X]) ^ n, n, rfl⟩ : Submonoid.powers (X : A[X])) := rfl

/-- Every element of the chart is a fraction `p/sᵐ` with `p ∈ Jᵐ`. -/
private theorem exists_infinityChartMk (I : Ideal A) (z : infinityChartAlgebra I) :
    ∃ (m : ℕ) (p : A[X]) (hp : p ∈ infinityChartIdeal I ^ m), z = infinityChartMk I m p hp := by
  obtain ⟨m, p, hp, hzp⟩ := (affineBlowup_mem_iff (infinityChartIdeal I) (X : A[X])
    (X_mem_infinityChartIdeal I) z.1).mp z.2
  exact ⟨m, p, hp, Subtype.ext hzp⟩

/-- The ideal `(s)` of the chart: the ideal cutting out the exceptional divisor `E`, and equally
the fibre at infinity `W_∞`, on `D₊(S)`. -/
def infinityChartFibreIdeal (I : Ideal A) : Ideal (infinityChartAlgebra I) :=
  Ideal.span {algebraMap A[X] (infinityChartAlgebra I) (X : A[X])}

/-- The image of `s` in the chart is the fraction `s/s⁰`. -/
theorem algebraMap_X_eq_infinityChartMk (I : Ideal A) :
    algebraMap A[X] (infinityChartAlgebra I) (X : A[X]) = infinityChartMk I 0 X (by simp) := by
  apply Subtype.ext
  rw [infinityChartMk_val]
  change Localization.mk (X : A[X]) 1 = _
  congr 1

/-- Two fractions on the chart agree exactly when they agree after clearing denominators: `s` is
a nonzerodivisor in `A[s]`, so no torsion intervenes. -/
theorem infinityChartMk_eq_iff {I : Ideal A} {n m : ℕ} {p q : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ n) (hq : q ∈ infinityChartIdeal I ^ m) :
    infinityChartMk I n p hp = infinityChartMk I m q hq ↔
      (X : A[X]) ^ m * p = (X : A[X]) ^ n * q := by
  rw [Subtype.ext_iff, infinityChartMk_val, infinityChartMk_val, affineBlowup_repr_eq_iff]
  refine ⟨fun ⟨k, hk⟩ => ?_, fun h => ⟨0, by rw [h]; ring⟩⟩
  exact sub_eq_zero.mp
    ((mul_left_mem_nonZeroDivisors_eq_zero_iff
      (pow_mem Polynomial.X_mem_nonZeroDivisors k)).mp hk)

/-- The fraction `p/sⁿ` depends only on `n` and `p`, not on the proof that `p ∈ Jⁿ`. -/
theorem infinityChartMk_congr {I : Ideal A} {n n' : ℕ} {p p' : A[X]} (hn : n = n')
    (hpp : p = p') {hp : p ∈ infinityChartIdeal I ^ n} {hp' : p' ∈ infinityChartIdeal I ^ n'} :
    infinityChartMk I n p hp = infinityChartMk I n' p' hp' := by
  subst hn hpp
  rfl

/-- `p/sⁿ + q/sⁿ = (p + q)/sⁿ` on the chart. -/
theorem infinityChartMk_add {I : Ideal A} {n : ℕ} {p q : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ n) (hq : q ∈ infinityChartIdeal I ^ n) :
    infinityChartMk I n p hp + infinityChartMk I n q hq =
      infinityChartMk I n (p + q) (add_mem hp hq) := by
  apply Subtype.ext
  change Localization.mk p _ + Localization.mk q _ = _
  rw [Localization.add_mk_self]
  rfl

/-- `p/sⁿ - q/sⁿ = (p - q)/sⁿ` on the chart. -/
theorem infinityChartMk_sub {I : Ideal A} {n : ℕ} {p q : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ n) (hq : q ∈ infinityChartIdeal I ^ n) :
    infinityChartMk I n p hp - infinityChartMk I n q hq =
      infinityChartMk I n (p - q) (sub_mem hp hq) := by
  refine (eq_sub_of_add_eq ?_).symm
  rw [infinityChartMk_add]
  exact infinityChartMk_congr rfl (sub_add_cancel p q)

/-- `(p/sⁿ) * (q/sᵐ) = pq/sⁿ⁺ᵐ` on the chart. -/
theorem infinityChartMk_mul {I : Ideal A} {n m : ℕ} {p q : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ n) (hq : q ∈ infinityChartIdeal I ^ m) :
    infinityChartMk I n p hp * infinityChartMk I m q hq =
      infinityChartMk I (n + m) (p * q) (by rw [pow_add]; exact Ideal.mul_mem_mul hp hq) := by
  apply Subtype.ext
  change Localization.mk p _ * Localization.mk q _ = _
  rw [Localization.mk_mul, infinityChartMk_val]
  congr 1
  exact Subtype.ext (pow_add (X : A[X]) n m).symm

/-- The fraction `1/s⁰` is the unit of the chart. -/
theorem infinityChartMk_one (I : Ideal A) : infinityChartMk I 0 1 (by simp) = 1 := by
  apply Subtype.ext
  change Localization.mk (1 : A[X]) _ = 1
  rw [show (⟨(X : A[X]) ^ 0, 0, rfl⟩ : Submonoid.powers (X : A[X])) = 1 from
    Subtype.ext (pow_zero _)]
  exact Localization.mk_one

/-- The fraction `0/sᴺ` is zero. -/
theorem infinityChartMk_zero (I : Ideal A) (N : ℕ) :
    infinityChartMk I N 0 (Submodule.zero_mem _) = 0 := by
  apply Subtype.ext
  change Localization.mk (0 : A[X]) _ = 0
  exact Localization.mk_zero _

/-- `p/sⁿ = psᵈ/sⁿ⁺ᵈ` on the chart. -/
theorem infinityChartMk_shift {I : Ideal A} {n : ℕ} {p : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ n) (d : ℕ) :
    infinityChartMk I n p hp =
      infinityChartMk I (n + d) (p * (X : A[X]) ^ d)
        (by
          rw [pow_add]
          exact Ideal.mul_mem_mul hp (X_pow_mem_pow_infinityChartIdeal I d)) := by
  rw [infinityChartMk_eq_iff, pow_add]
  ring

/-- `s * (p/sᵐ) = ps/sᵐ` on the chart. -/
theorem algebraMap_X_mul_infinityChartMk {I : Ideal A} {m : ℕ} {p : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ m) :
    algebraMap A[X] (infinityChartAlgebra I) (X : A[X]) * infinityChartMk I m p hp =
      infinityChartMk I m (p * (X : A[X])) (Ideal.mul_mem_right _ _ hp) := by
  rw [algebraMap_X_eq_infinityChartMk, mul_comm, infinityChartMk_mul]
  rfl

/-- If `p ∈ Jᵐ` and `sᵐ q = s^(N+1) p`, then `q ∈ J^(N+1)`. -/
theorem mem_pow_succ_of_X_pow_mul_eq {I : Ideal A} {N m : ℕ} {q p : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ m)
    (h : (X : A[X]) ^ m * q = (X : A[X]) ^ (N + 1) * p) :
    q ∈ infinityChartIdeal I ^ (N + 1) := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro d
  have h1 : q.coeff d = (p * (X : A[X]) ^ (N + 1)).coeff (d + m) := by
    have h2 := congrArg (fun f : A[X] => f.coeff (d + m)) h
    simpa [Polynomial.coeff_X_pow_mul, mul_comm] using h2
  rw [Polynomial.coeff_mul_X_pow'] at h1
  split at h1
  · rename_i hle
    have hmem := (mem_pow_infinityChartIdeal_iff.mp hp) (d + m - (N + 1))
    rw [h1]
    exact Ideal.pow_le_pow_right (by omega) hmem
  · rw [h1]; simp

/-- **`s` cuts the chart down to the associated graded ring.** The fraction `p/sᴺ` on the chart
`A[s][J/s]` is divisible by `s` exactly when `p` lies in `J^(N+1)`. -/
@[stacks 0FBH "on D₊(S) the ideal (s) consists of the fractions p/s^N with p in J^(N+1)"]
theorem infinityChartMk_mem_fibreIdeal_iff {I : Ideal A} {N : ℕ} {q : A[X]}
    (hq : q ∈ infinityChartIdeal I ^ N) :
    infinityChartMk I N q hq ∈ infinityChartFibreIdeal I ↔
      q ∈ infinityChartIdeal I ^ (N + 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [infinityChartFibreIdeal, Ideal.mem_span_singleton'] at h
    obtain ⟨z, hz⟩ := h
    obtain ⟨m, p, hp, rfl⟩ := exists_infinityChartMk I z
    rw [ mul_comm, algebraMap_X_mul_infinityChartMk, infinityChartMk_eq_iff] at hz
    refine mem_pow_succ_of_X_pow_mul_eq hp ?_
    rw [← hz]; ring
  · rw [infinityChartFibreIdeal, Ideal.mem_span_singleton']
    refine ⟨infinityChartMk I (N + 1) q h, ?_⟩
    rw [mul_comm, algebraMap_X_mul_infinityChartMk, infinityChartMk_eq_iff]
    ring

/-! ### The fibre of the chart is the conormal algebra -/

/-- If `xₙ ∈ Iⁿ` for every `n`, then `∑ₙ xₙ s^(N - n)` lies in `Jᴺ`. -/
theorem sum_C_mul_X_pow_mem_pow_infinityChartIdeal (I : Ideal A) (s : Finset ℕ) (x : ℕ → A)
    (hx : ∀ n, x n ∈ I ^ n) (N : ℕ) :
    (∑ n ∈ s, C (x n) * (X : A[X]) ^ (N - n)) ∈ infinityChartIdeal I ^ N := by
  exact Ideal.sum_mem _ fun n _ => C_mul_X_pow_mem_pow_infinityChartIdeal (hx n)

/-- For `xₙ ∈ Iⁿ` and indices `n ≤ N`, the sum `∑ₙ xₙ/sⁿ` on the chart is the single fraction
`(∑ₙ xₙ s^(N - n))/sᴺ`. -/
theorem sum_infinityChartMk_C (I : Ideal A) (x : ℕ → A) (hx : ∀ n, x n ∈ I ^ n) (N : ℕ)
    (s : Finset ℕ) (hN : ∀ n ∈ s, n ≤ N) :
    ∑ n ∈ s, infinityChartMk I n (C (x n)) (C_mem_pow_infinityChartIdeal (hx n)) =
      infinityChartMk I N (∑ n ∈ s, C (x n) * (X : A[X]) ^ (N - n))
        (sum_C_mul_X_pow_mem_pow_infinityChartIdeal I s x hx N) := by
  induction s using Finset.induction_on with
  | empty => simpa using (infinityChartMk_zero I N).symm
  | insert a s ha ih =>
      have hle : a ≤ N := hN a (Finset.mem_insert_self a s)
      have h1 : infinityChartMk I a (C (x a)) (C_mem_pow_infinityChartIdeal (hx a)) =
          infinityChartMk I N (C (x a) * (X : A[X]) ^ (N - a))
            (C_mul_X_pow_mem_pow_infinityChartIdeal (hx a)) :=
        (infinityChartMk_shift (C_mem_pow_infinityChartIdeal (hx a)) (N - a)).trans
          (infinityChartMk_congr (by omega) rfl)
      rw [Finset.sum_insert ha, h1, ih (fun n hn => hN n (Finset.mem_insert_of_mem hn)),
        infinityChartMk_add]
      exact infinityChartMk_congr rfl
        (Finset.sum_insert (f := fun n => C (x n) * (X : A[X]) ^ (N - n)) ha).symm

/-- The class of `x/sⁿ`, for `x ∈ Iⁿ`, in the fibre `A[s][J/s] ⧸ (s)` of the chart over the
exceptional divisor. -/
def infinityChartClass (I : Ideal A) (n : ℕ) (x : A) (hx : x ∈ I ^ n) :
    infinityChartAlgebra I ⧸ infinityChartFibreIdeal I :=
  Ideal.Quotient.mk (infinityChartFibreIdeal I)
    (infinityChartMk I n (C x) (C_mem_pow_infinityChartIdeal hx))

/-- The class of `x/sⁿ` depends only on `x`, not on the proof that `x ∈ Iⁿ`. -/
theorem infinityChartClass_congr {I : Ideal A} {n : ℕ} {x x' : A} (h : x = x')
    {hx : x ∈ I ^ n} {hx' : x' ∈ I ^ n} :
    infinityChartClass I n x hx = infinityChartClass I n x' hx' := by
  subst h; rfl

/-- The class of `x/sⁿ` vanishes exactly when `x ∈ Iⁿ⁺¹`, so the degree `n` part of the fibre is
`Iⁿ/Iⁿ⁺¹`. -/
theorem infinityChartClass_eq_zero_iff {I : Ideal A} {n : ℕ} {x : A} (hx : x ∈ I ^ n) :
    infinityChartClass I n x hx = 0 ↔ x ∈ I ^ (n + 1) := by
  rw [infinityChartClass, Ideal.Quotient.eq_zero_iff_mem, infinityChartMk_mem_fibreIdeal_iff]
  exact ⟨fun h => by simpa using (mem_pow_infinityChartIdeal_iff.mp h) 0,
    fun h => C_mem_pow_infinityChartIdeal h⟩

/-- The class of `x/sⁿ` is additive in `x`. -/
theorem infinityChartClass_add {I : Ideal A} {n : ℕ} {x y : A} (hx : x ∈ I ^ n)
    (hy : y ∈ I ^ n) :
    infinityChartClass I n x hx + infinityChartClass I n y hy =
      infinityChartClass I n (x + y) (add_mem hx hy) := by
  rw [infinityChartClass, infinityChartClass, infinityChartClass, ← RingHom.map_add]
  exact congrArg _ ((infinityChartMk_add _ _).trans
    (infinityChartMk_congr rfl (map_add C x y).symm))

/-- The product of the classes of `x/sⁿ` and `y/sᵐ` is the class of `xy/sⁿ⁺ᵐ`. -/
theorem infinityChartClass_mul {I : Ideal A} {n m : ℕ} {x y : A} (hx : x ∈ I ^ n)
    (hy : y ∈ I ^ m) :
    infinityChartClass I n x hx * infinityChartClass I m y hy =
      infinityChartClass I (n + m) (x * y)
        (by rw [pow_add]; exact Ideal.mul_mem_mul hx hy) := by
  rw [infinityChartClass, infinityChartClass, infinityChartClass, ← map_mul]
  exact congrArg _ ((infinityChartMk_mul _ _).trans
    (infinityChartMk_congr rfl (map_mul C x y).symm))

/-- The class of `1/s⁰` is the unit of the fibre. -/
theorem infinityChartClass_one (I : Ideal A) : infinityChartClass I 0 1 (by simp) = 1 := by
  rw [infinityChartClass]
  refine (congrArg _ ?_).trans (map_one (Ideal.Quotient.mk (infinityChartFibreIdeal I)))
  exact (infinityChartMk_congr rfl (map_one C)).trans (infinityChartMk_one I)

/-- A finite sum of classes `xₙ/sⁿ` is the class of the single fraction `(∑ₙ xₙ s^(N - n))/sᴺ`,
for indices `n ≤ N`. -/
private theorem sum_infinityChartClass_eq_mk {I : Ideal A} (x : ℕ → A) (hx : ∀ n, x n ∈ I ^ n)
    (s : Finset ℕ) (N : ℕ) (hN : ∀ n ∈ s, n ≤ N) :
    ∑ n ∈ s, infinityChartClass I n (x n) (hx n) =
      Ideal.Quotient.mk (infinityChartFibreIdeal I)
        (infinityChartMk I N (∑ n ∈ s, C (x n) * (X : A[X]) ^ (N - n))
          (sum_C_mul_X_pow_mem_pow_infinityChartIdeal I s x hx N)) := by
  rw [← sum_infinityChartMk_C I x hx N s hN]
  exact (map_sum (Ideal.Quotient.mk (infinityChartFibreIdeal I)).toAddMonoidHom _ _).symm

/-- The classes of the different degrees are independent: a vanishing finite sum of classes
`xₙ/sⁿ` forces every `xₙ` into `Iⁿ⁺¹`. -/
theorem mem_pow_succ_of_sum_infinityChartClass_eq_zero {I : Ideal A} (x : ℕ → A)
    (hx : ∀ n, x n ∈ I ^ n) (s : Finset ℕ)
    (h : ∑ n ∈ s, infinityChartClass I n (x n) (hx n) = 0) :
    ∀ n ∈ s, x n ∈ I ^ (n + 1) := by
  classical
  set N := s.sup id with hNdef
  have hN : ∀ n ∈ s, n ≤ N := fun n hn => Finset.le_sup (f := id) hn
  rw [sum_infinityChartClass_eq_mk x hx s N hN, Ideal.Quotient.eq_zero_iff_mem,
    infinityChartMk_mem_fibreIdeal_iff, mem_pow_infinityChartIdeal_iff] at h
  intro n hn
  have hcoeff : (∑ k ∈ s, C (x k) * (X : A[X]) ^ (N - k)).coeff (N - n) = x n := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem n hn]
    · simp
    · intro k hk hkn
      have hne : N - n ≠ N - k := by
        have h1 := hN n hn
        have h2 := hN k hk
        omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  have hres := h (N - n)
  rw [hcoeff] at hres
  have hrw : N + 1 - (N - n) = n + 1 := by have := hN n hn; omega
  rwa [hrw] at hres

/-- The part of `p` of degree at most `m`, written as `∑_{n ≤ m} p_{m-n} s^(m - n)`. -/
def truncateDegreeLE (p : A[X]) (m : ℕ) : A[X] :=
  ∑ n ∈ Finset.range (m + 1), C (p.coeff (m - n)) * (X : A[X]) ^ (m - n)

/-- The coefficient of `sʲ` in `truncateDegreeLE p m` is that of `p` for `j ≤ m`, and `0`
otherwise. -/
theorem coeff_truncateDegreeLE (p : A[X]) (m j : ℕ) :
    (truncateDegreeLE p m).coeff j = if j ≤ m then p.coeff j else 0 := by
  classical
  rw [truncateDegreeLE, Polynomial.finsetSum_coeff]
  by_cases hj : j ≤ m
  · rw [Finset.sum_eq_single_of_mem (m - j) (Finset.mem_range.mpr (by omega))]
    · have h1 : m - (m - j) = j := by omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h1, hj]
    · intro k hk hkj
      have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
      have hne : j ≠ m - k := by omega
      simp [hne]
  · have hzero : (if j ≤ m then p.coeff j else 0) = 0 := by simp [hj]
    rw [hzero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    have hne : j ≠ m - k := by omega
    simp [hne]

/-- The part of `p` of degree above `m` lies in `J^(m+1)`. -/
theorem sub_truncateDegreeLE_mem {I : Ideal A} {m : ℕ} (p : A[X]) :
    p - truncateDegreeLE p m ∈ infinityChartIdeal I ^ (m + 1) := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro j
  by_cases hj : j ≤ m
  · simp [Polynomial.coeff_sub, coeff_truncateDegreeLE, hj]
  · have hz : m + 1 - j = 0 := by omega
    simp [hz]

/-- If `p ∈ Jᵐ`, then its part of degree at most `m` also lies in `Jᵐ`. -/
theorem truncateDegreeLE_mem {I : Ideal A} {m : ℕ} {p : A[X]}
    (hp : p ∈ infinityChartIdeal I ^ m) :
    truncateDegreeLE p m ∈ infinityChartIdeal I ^ m := by
  rw [mem_pow_infinityChartIdeal_iff]
  intro j
  rw [coeff_truncateDegreeLE]
  by_cases hj : j ≤ m
  · have hval : (if j ≤ m then p.coeff j else 0) = p.coeff j := by simp [hj]
    rw [hval]
    exact (mem_pow_infinityChartIdeal_iff.mp hp) j
  · have hval : (if j ≤ m then p.coeff j else 0) = 0 := by simp [hj]
    rw [hval]
    exact Submodule.zero_mem _

/-- Every element of the fibre of the chart is a finite sum of classes `xₙ/sⁿ` with
`xₙ ∈ Iⁿ`. -/
theorem exists_sum_infinityChartClass {I : Ideal A}
    (z : infinityChartAlgebra I ⧸ infinityChartFibreIdeal I) :
    ∃ (s : Finset ℕ) (x : ℕ → A) (hx : ∀ n, x n ∈ I ^ n),
      z = ∑ n ∈ s, infinityChartClass I n (x n) (hx n) := by
  classical
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨m, p, hp, rfl⟩ := exists_infinityChartMk I w
  have hx : ∀ n, (if n ≤ m then p.coeff (m - n) else 0) ∈ I ^ n := by
    intro n
    by_cases hn : n ≤ m
    · rw [ite_eq_left hn]
      have h := (mem_pow_infinityChartIdeal_iff.mp hp) (m - n)
      have hrw : m - (m - n) = n := by omega
      rwa [hrw] at h
    · simp [hn]
  refine ⟨Finset.range (m + 1), _, hx, ?_⟩
  rw [sum_infinityChartClass_eq_mk _ hx (Finset.range (m + 1)) m
    (fun n hn => by simpa [Nat.lt_succ_iff] using hn)]
  have heq : (∑ n ∈ Finset.range (m + 1),
      C (if n ≤ m then p.coeff (m - n) else 0) * (X : A[X]) ^ (m - n)) =
      truncateDegreeLE p m := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ m := by simpa [Nat.lt_succ_iff] using hn
    simp [hn']
  rw [Ideal.Quotient.eq]
  have hdiff : infinityChartMk I m p hp -
      infinityChartMk I m (∑ n ∈ Finset.range (m + 1),
        C (if n ≤ m then p.coeff (m - n) else 0) * (X : A[X]) ^ (m - n))
        (sum_C_mul_X_pow_mem_pow_infinityChartIdeal I _ _ hx m) =
      infinityChartMk I m (p - truncateDegreeLE p m)
        (sub_mem hp (truncateDegreeLE_mem hp)) := by
    rw [infinityChartMk_sub]
    exact infinityChartMk_congr rfl (by rw [heq])
  rw [hdiff, infinityChartMk_mem_fibreIdeal_iff]
  exact sub_truncateDegreeLE_mem p

/-- An element of the `n`-th step of the `I`-adic filtration of `A` lies in `Iⁿ`. -/
theorem mem_pow_of_mem_associatedGradedPower {I : Ideal A} {n : ℕ} {x : A}
    (hx : x ∈ AssociatedGraded.power (M := A) I n) : x ∈ I ^ n := by
  rwa [AssociatedGraded.ring_power_eq] at hx

/-- The degree `n` part `Iⁿ/Iⁿ⁺¹` of the conormal algebra, mapped into the fibre of the chart by
`x ↦ x/sⁿ`. -/
def conormalPieceToInfinityChartFibre (I : Ideal A) (n : ℕ) :
    AssociatedGraded.piece (M := A) I n →+
      (infinityChartAlgebra I ⧸ infinityChartFibreIdeal I) :=
  AddMonoidHom.mk'
    (fun c => Quotient.liftOn c
      (fun y => infinityChartClass I n (y : A) (mem_pow_of_mem_associatedGradedPower y.2))
      (by
        intro y z hyz
        have h : ((y : A) - (z : A)) ∈ AssociatedGraded.power (M := A) I (n + 1) := by
          have h' := (Submodule.Quotient.eq
            ((AssociatedGraded.power (M := A) I (n + 1)).comap
              (Submodule.subtype (AssociatedGraded.power (M := A) I n)))).mp
            (Quotient.sound hyz)
          exact h'
        have h0 : infinityChartClass I n ((y : A) - (z : A))
            (sub_mem (mem_pow_of_mem_associatedGradedPower y.2)
              (mem_pow_of_mem_associatedGradedPower z.2)) = 0 :=
          (infinityChartClass_eq_zero_iff _).mpr (mem_pow_of_mem_associatedGradedPower h)
        have h1 := infinityChartClass_add (I := I) (n := n)
          (sub_mem (mem_pow_of_mem_associatedGradedPower y.2)
            (mem_pow_of_mem_associatedGradedPower z.2))
          (mem_pow_of_mem_associatedGradedPower z.2)
        rw [h0, zero_add] at h1
        rw [h1]
        exact infinityChartClass_congr (by ring)))
    (by
      intro c d
      induction c using Quotient.inductionOn with
      | _ y =>
        induction d using Quotient.inductionOn with
        | _ z =>
          change infinityChartClass I n ((y : A) + (z : A)) _ =
            infinityChartClass I n (y : A) _ + infinityChartClass I n (z : A) _
          rw [infinityChartClass_add])

/-- The map `Iⁿ/Iⁿ⁺¹ → A[s][J/s] ⧸ (s)` sends the class of `y` to the class of `y/sⁿ`. -/
theorem conormalPieceToInfinityChartFibre_mk (I : Ideal A) (n : ℕ)
    (y : AssociatedGraded.power (M := A) I n) :
    conormalPieceToInfinityChartFibre I n (AssociatedGraded.mk I n y) =
      infinityChartClass I n (y : A) (mem_pow_of_mem_associatedGradedPower y.2) := rfl

/-- The comparison ring map from the conormal algebra `⨁ₙ Iⁿ/Iⁿ⁺¹` to the fibre
`A[s][J/s] ⧸ (s)` of the chart. -/
def conormalToInfinityChartFibre (I : Ideal A) :
    AssociatedGraded.gradedRing I →+*
      (infinityChartAlgebra I ⧸ infinityChartFibreIdeal I) :=
  DirectSum.toSemiring (conormalPieceToInfinityChartFibre I)
    (by
      have hone : (GradedMonoid.GOne.one : AssociatedGraded.piece (M := A) I 0) =
          AssociatedGraded.mk I 0 ⟨1, by simp [AssociatedGraded.power]⟩ := rfl
      rw [hone, conormalPieceToInfinityChartFibre_mk]
      exact infinityChartClass_one I)
    (by
      intro i j ai aj
      induction ai using Quotient.inductionOn with
      | _ a =>
        induction aj using Quotient.inductionOn with
        | _ m =>
          have ha : (a : A) ∈ I ^ i := mem_pow_of_mem_associatedGradedPower a.2
          have hm : (m : A) ∈ I ^ j := mem_pow_of_mem_associatedGradedPower m.2
          have h1 : infinityChartClass I i (a : A) ha * infinityChartClass I j (m : A) hm =
              infinityChartClass I (i + j) ((a : A) * (m : A))
                (by rw [pow_add]; exact Ideal.mul_mem_mul ha hm) :=
            infinityChartClass_mul ha hm
          have h2 : infinityChartClass I (i + j) ((a : A) * (m : A))
                (by rw [pow_add]; exact Ideal.mul_mem_mul ha hm) =
              infinityChartClass I (i + j) ((a : A) • (m : A))
                (by rw [smul_eq_mul, pow_add]; exact Ideal.mul_mem_mul ha hm) :=
            infinityChartClass_congr (smul_eq_mul _ _).symm
          exact (h1.trans h2).symm)

/-- On the degree `n` summand, the comparison map is `conormalPieceToInfinityChartFibre I n`. -/
theorem conormalToInfinityChartFibre_of (I : Ideal A) (n : ℕ)
    (c : AssociatedGraded.piece (M := A) I n) :
    conormalToInfinityChartFibre I
        (DirectSum.of (fun k => AssociatedGraded.piece (M := A) I k) n c) =
      conormalPieceToInfinityChartFibre I n c :=
  DirectSum.toSemiring_of _ _ _ n c

/-- The comparison map from the conormal algebra to the fibre of the chart is injective. -/
theorem conormalToInfinityChartFibre_injective (I : Ideal A) :
    Function.Injective (conormalToInfinityChartFibre I) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro g hg
  have hrep : ∀ n, ∃ y : AssociatedGraded.power (M := A) I n,
      AssociatedGraded.mk I n y = g n := fun n => Quotient.exists_rep (g n)
  choose y hy using hrep
  have hgsum : g = ∑ n ∈ DFinsupp.support g,
      DirectSum.of (fun k => AssociatedGraded.piece (M := A) I k) n (g n) :=
    (DirectSum.sum_support_of g).symm
  have hzero : ∑ n ∈ DFinsupp.support g,
      infinityChartClass I n ((y n : A))
        (mem_pow_of_mem_associatedGradedPower (y n).2) = 0 := by
    have heval : conormalToInfinityChartFibre I g = ∑ n ∈ DFinsupp.support g,
        infinityChartClass I n ((y n : A))
          (mem_pow_of_mem_associatedGradedPower (y n).2) := by
      conv_lhs => rw [hgsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [conormalToInfinityChartFibre_of, ← hy n, conormalPieceToInfinityChartFibre_mk]
    rw [← heval, hg]
  have hkey := mem_pow_succ_of_sum_infinityChartClass_eq_zero (I := I)
    (fun n => (y n : A)) (fun n => mem_pow_of_mem_associatedGradedPower (y n).2) _ hzero
  ext n
  by_cases hn : n ∈ DFinsupp.support g
  · rw [← hy n]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    change ((y n : A)) ∈ AssociatedGraded.power (M := A) I (n + 1)
    rw [AssociatedGraded.ring_power_eq]
    exact hkey n hn
  · simpa using DFinsupp.notMem_support_iff.mp hn

/-- The comparison map from the conormal algebra to the fibre of the chart is surjective. -/
theorem conormalToInfinityChartFibre_surjective (I : Ideal A) :
    Function.Surjective (conormalToInfinityChartFibre I) := by
  classical
  intro z
  obtain ⟨s, x, hx, hz⟩ := exists_sum_infinityChartClass z
  refine ⟨∑ n ∈ s, DirectSum.of (fun k => AssociatedGraded.piece (M := A) I k) n
      (AssociatedGraded.mk I n ⟨x n, (AssociatedGraded.ring_power_eq I n).ge (hx n)⟩), ?_⟩
  rw [map_sum, hz]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [conormalToInfinityChartFibre_of, conormalPieceToInfinityChartFibre_mk]

/-- The quotient of the affine blowup algebra `A[s][J/s]`, `J = (I, s)`, by the element `s`
cutting out the exceptional divisor is the conormal algebra `A/I ⊕ I/I² ⊕ I²/I³ ⊕ ⋯` of `I` in
`A`. -/
@[stacks 0FBH "the quotient of A[s][J/s] by s is the conormal algebra of I in A"]
def conormalEquivInfinityChartFibre (I : Ideal A) :
    AssociatedGraded.gradedRing I ≃+*
      (infinityChartAlgebra I ⧸ infinityChartFibreIdeal I) :=
  RingEquiv.ofBijective (conormalToInfinityChartFibre I)
    ⟨conormalToInfinityChartFibre_injective I, conormalToInfinityChartFibre_surjective I⟩

end Chart

end Stacks.Chow

end
