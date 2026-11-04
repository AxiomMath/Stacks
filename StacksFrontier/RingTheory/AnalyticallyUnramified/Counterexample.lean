module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Nagata.PthRoot

/-!
# A one-dimensional Noetherian local domain of characteristic two with nonreduced completion

Stacks 00PB asserts that a Noetherian local domain need not be analytically unramified. This file
produces the witness, over a countable coefficient field, and so supplies the existential form of
the tag that Stacks 07NZ consumes.

Let `k` be a countable field of characteristic two. The power series field `k((x))` is
uncountable, so it contains a series `f` transcendental over the rational function field `k(x)`
(`exists_transcendental_series`). Send the variable of `k(x)(y)` to `f`; this embeds `k(x)(y)` into
`k((x))`, and restricting to the subfield `K = k(x)(y²)` gives an embedding `e : K → k((x))` whose
image misses `f` while containing `f²` (`variable_not_mem_squares`). Let `A ⊆ K` be the valuation
ring of the valuation pulled back along `e`; it is a discrete valuation ring because `x` has
valuation `exp (-1)` (`valuation_dvr`). Polynomial truncations of `f` form a Cauchy sequence in `A`
whose limit is a square root of `f²` in the completion of `A` (`completion_root_of_embedding`),
while `f²` has no square root in `K`. So `R = A[T]/(T² - f²)` is a one-dimensional Noetherian local
domain, and the difference of the two square roots of `f²` in the completion of `R` is a nonzero
square-zero element (`AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq`).

## Main results

* `exists_noetherianLocalDomain_adicCompletion_not_reduced`: there is a prime `p` and a
  one-dimensional Noetherian local domain of characteristic `p` which is not analytically
  unramified.

## Implementation notes

The mechanism is the purely inseparable one, at `p = 2` and over `k = ULift (ZMod 2)`, so the
witness is produced in any requested universe. The completion is the canonical `AdicCompletion` at
the maximal ideal, which is what `IsAnalyticallyUnramified` is stated with.

The ring `A[T]/(T² - f²)` and the nonreduced completion are the general `p`-th root machinery of
`StacksFrontier.RingTheory.Nagata.PthRoot`, used here at `p = 2`; only the construction of the
embedding `e` and of the square root in the completion of `A` is specific to this file.

`StacksFrontier.RingTheory.AnalyticallyUnramified.Examples` gives a different witness, valid whenever
`[k : k^p] = ∞`: the ring of power series whose coefficients generate a finite extension of `k^p`.
That family is stated for an arbitrary such `k`, so it is not by itself an existence statement;
this file's countable-field construction needs no hypothesis on `k` beyond countability and so
closes the existential.

## References

* [Stacks Project, Tag 00PB](https://stacks.math.columbia.edu/tag/00PB)
* [Stacks Project, Tag 07NZ](https://stacks.math.columbia.edu/tag/07NZ), which consumes it
-/

@[expose] public section

open scoped PowerSeries LaurentSeries RatFunc
open LaurentSeries
open Polynomial IsLocalRing WithZero
open AdicCompletion
open Stacks.Nagata.PthRootDescent

universe u v

section Construction

variable (k : Type u) [Field k]

/-- The sequences in a field form an uncountable type: there are at least `2 ^ ℵ₀` of them. -/
private theorem uncountable_sequences : Uncountable (ℕ → k) := by
  apply Cardinal.aleph0_lt_mk_iff.mp
  simp only [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_aleph0]
  exact (Cardinal.cantor Cardinal.aleph0).trans_le
    (Cardinal.power_le_power_right (Cardinal.two_le_iff.mpr ⟨0, 1, zero_ne_one⟩))

/-- Countability of the algebraic elements leaves a transcendental power series. -/
private theorem exists_transcendental_series [Countable k] :
    ∃ f : PowerSeries k, Transcendental (RatFunc k) (f : LaurentSeries k) := by
  have : Uncountable (ℕ → k) := uncountable_sequences k
  by_contra! h
  have : Countable k[X] := Function.Injective.countable Polynomial.toFinsupp_injective
  have : Countable (RatFunc k) := Function.Surjective.countable
    (f := fun pq : k[X] × k[X] => algebraMap k[X] (RatFunc k) pq.1 /
      algebraMap k[X] (RatFunc k) pq.2)
    (fun q => ⟨(q.num, q.denom), RatFunc.num_div_denom q⟩)
  have : Countable {x : LaurentSeries k // IsAlgebraic (RatFunc k) x} :=
    (Algebraic.countable (RatFunc k) (LaurentSeries k)).to_subtype
  have hcount : Countable (PowerSeries k) := Function.Injective.countable
    (f := fun f : PowerSeries k =>
      (⟨(f : LaurentSeries k), by simpa only [Transcendental, not_not] using h f⟩ :
        {x : LaurentSeries k // IsAlgebraic (RatFunc k) x}))
    (fun a b hab => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val hab))
  have : Countable (ℕ → k) := Function.Injective.countable
    (f := PowerSeries.mk) (fun a b h => by
      funext n
      simpa using congrArg (PowerSeries.coeff n) h)
  exact not_countable (α := ℕ → k) this

/-- The rational variable has degree two over the field generated by its square. -/
private theorem variable_not_mem_squares (F : Type u) [Field F] :
    (RatFunc.X : RatFunc F) ∉ IntermediateField.adjoin F {(RatFunc.X : RatFunc F) ^ 2} := by
  intro hx
  have htop : IntermediateField.adjoin F {(RatFunc.X : RatFunc F) ^ 2} = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X]
    exact IntermediateField.adjoin_le_iff.mpr (by simpa using hx)
  have hdim := RatFunc.finrank_eq_max_natDegree ((RatFunc.X : RatFunc F) ^ 2)
  rw [htop] at hdim
  change Module.finrank (⊤ : IntermediateField F (RatFunc F)) (RatFunc F) = _ at hdim
  simp only [RatFunc.X] at hdim
  rw [← map_pow] at hdim
  simp only [RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_pow,
    natDegree_X, natDegree_one, mul_one, max_eq_left (show 0 ≤ 2 from by omega)] at hdim
  norm_num at hdim

/-- A power series has valuation at most one as a Laurent series. -/
private theorem valuation_powerSeries_le_one (g : PowerSeries k) :
    Valued.v (g : LaurentSeries k) ≤ (1 : ℤᵐ⁰) :=
  (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨g, rfl⟩

/-- Power series whose coefficients agree below `m` differ by something of valuation at most
`exp (-m)`. -/
private theorem valuation_coe_sub_le (g h : PowerSeries k) (m : ℕ)
    (H : ∀ i < m, PowerSeries.coeff i g = PowerSeries.coeff i h) :
    Valued.v ((g : LaurentSeries k) - h) ≤ exp (-(m : ℤ)) := by
  rw [← PowerSeries.coe_sub]
  refine (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero k _).2 fun i hi => ?_
  simp [H i hi]

/-- An element of a field mapping to `x` in `k((x))` has pulled-back valuation `exp (-1)`. -/
private theorem comap_valuation_eq_exp_neg_one {K : Type*} [Field K] (e : K →+* LaurentSeries k)
    (x : K) (hx : e x = (PowerSeries.X : PowerSeries k)) :
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e x = exp (-1 : ℤ) := by
  simpa [hx] using LaurentSeries.valuation_X_pow k 1

/-- Evaluating a polynomial at an element mapping to `x` agrees, after the embedding into
`k((x))`, with the polynomial viewed as a power series. -/
private theorem eval₂RingHom_eq_coe {K : Type*} [Field K] (e : K →+* LaurentSeries k)
    (r : k →+* K) (x : K) (hx : e x = (PowerSeries.X : PowerSeries k))
    (hr : ∀ c, e (r c) = algebraMap k (LaurentSeries k) c) (q : k[X]) :
    e (Polynomial.eval₂RingHom r x q) = ((q : PowerSeries k) : LaurentSeries k) := by
  have H : e.comp (Polynomial.eval₂RingHom r x) =
      (HahnSeries.ofPowerSeries ℤ k).comp Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa [LaurentSeries.algebraMap_apply] using hr c
    · simpa using hx
  exact RingHom.congr_fun H q

/-- The valuation ring of a subfield of `k((x))` containing an element mapping to `x` is a
discrete valuation ring: that element has valuation `exp (-1)`, so the valuation is nontrivial. -/
private theorem valuation_dvr {K : Type*} [Field K] (e : K →+* LaurentSeries k) (x : K)
    (hx : e x = (PowerSeries.X : PowerSeries k)) :
    IsDiscreteValuationRing
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring := by
  let v : Valuation K ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e
  have hvx : v x = exp (-1 : ℤ) := comap_valuation_eq_exp_neg_one k e x hx
  have : v.IsNontrivial := ⟨x, by simp [hvx], by simp [hvx]⟩
  show IsDiscreteValuationRing v.valuationSubring
  infer_instance

/-- In that valuation ring, valuation at most `exp (-n)` means membership in the `n`-th power of
the maximal ideal, `x` being a uniformizer. -/
private theorem valuation_mem_pow {K : Type*} [Field K] (e : K →+* LaurentSeries k) (x : K)
    (hx : e x = (PowerSeries.X : PowerSeries k))
    (z : ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring)
    (n : ℕ) (hz : Valued.v (e z) ≤ exp (-(n : ℤ))) :
    z ∈ maximalIdeal
      ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring ^ n := by
  let v : Valuation K ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e
  have hvx : v x = exp (-1 : ℤ) := comap_valuation_eq_exp_neg_one k e x hx
  have : v.IsNontrivial := ⟨x, by simp [hvx], by simp [hvx]⟩
  let π : v.valuationSubring := ⟨x, by change v x ≤ 1; simp [hvx]⟩
  have hπ : v.IsUniformizer (π : K) := by
    rw [Valuation.IsUniformizer, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      (show exp (-1 : ℤ) ∈ Set.range v from ⟨x, hvx⟩)]
    exact hvx
  show z ∈ maximalIdeal v.valuationSubring ^ n
  rw [hπ.is_generator, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (Valuation.valuationSubring.integers v).dvd_iff_le]
  show v (z : K) ≤ v (x ^ n)
  rw [map_pow, hvx, ← exp_nsmul]
  simpa only [v, Valuation.comap_apply, nsmul_eq_mul, mul_neg, mul_one] using hz

/-- Polynomial truncations give a square root in the completion of the valuation ring. -/
private theorem completion_root_of_embedding
    {K : Type*} [Field K] [CharP k 2] [CharP K 2]
    (e : K →+* LaurentSeries k) (r : k →+* K) (x a : K)
    (hx : e x = (PowerSeries.X : PowerSeries k))
    (hr : ∀ c, e (r c) = algebraMap k (LaurentSeries k) c)
    (f : PowerSeries k) (ha : e a = (f : LaurentSeries k) ^ 2) :
    ∃ a₀ : ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring,
      (a₀ : K) = a ∧
      ∃ α : AdicCompletion (maximalIdeal
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring)
          ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring,
        α ^ 2 = algebraMap _ _ a₀ := by
  have : CharP (LaurentSeries k) 2 := charP_of_injective_algebraMap
    (algebraMap k (LaurentSeries k)).injective 2
  let v : Valuation K ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e
  let A := v.valuationSubring
  have : IsDiscreteValuationRing A := valuation_dvr k e x hx
  let φ : k[X] →+* K := Polynomial.eval₂RingHom r x
  have hφ (q : k[X]) : e (φ q) = ((q : PowerSeries k) : LaurentSeries k) :=
    eval₂RingHom_eq_coe k e r x hx hr q
  let seq : ℕ → A := fun n => ⟨φ (f.trunc n), by
    show Valued.v (e (φ (f.trunc n))) ≤ 1
    rw [hφ]
    exact valuation_powerSeries_le_one k _⟩
  have hseq (n : ℕ) : e (seq n : K) = ((f.trunc n : PowerSeries k) : LaurentSeries k) :=
    hφ _
  let a₀ : A := ⟨a, by
    show Valued.v (e a) ≤ 1
    rw [ha, ← PowerSeries.coe_pow]
    exact valuation_powerSeries_le_one k _⟩
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      seq m ≡ seq n [SMOD ((maximalIdeal A) ^ m • (⊤ : Submodule A A))] := by
    intro m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    apply valuation_mem_pow k e x hx
    show Valued.v (e ((seq m : K) - (seq n : K))) ≤ _
    rw [map_sub, hseq, hseq]
    exact valuation_coe_sub_le k _ _ m fun i hi => by
      simp [PowerSeries.coeff_trunc, hi, hi.trans_le hmn]
  let α := AdicCompletion.mk (maximalIdeal A) A ⟨seq, hcauchy⟩
  refine ⟨a₀, rfl, α, ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  show AdicCompletion.evalₐ (maximalIdeal A) n (α ^ 2) =
    AdicCompletion.evalₐ (maximalIdeal A) n (AdicCompletion.of (maximalIdeal A) A a₀)
  rw [map_pow, AdicCompletion.evalₐ_of]
  show (Ideal.Quotient.mk ((maximalIdeal A) ^ n) (seq n)) ^ 2 = _
  rw [← map_pow, Ideal.Quotient.eq]
  apply valuation_mem_pow k e x hx
  show Valued.v (e ((seq n : K) ^ 2 - a)) ≤ _
  rw [map_sub, map_pow, ha, hseq, ← sub_pow_char, map_pow]
  have hb := valuation_coe_sub_le k (f.trunc n) f n fun i hi => by
    simp [PowerSeries.coeff_trunc, hi]
  calc
    _ ≤ (exp (-(n : ℤ))) ^ 2 := pow_le_pow_left₀ zero_le hb 2
    _ ≤ exp (-(n : ℤ)) := by
      rw [pow_two]
      exact mul_le_of_le_one_right zero_le (by simp)

end Construction

/-- A square root missing from the subfield but present in the completion of its valuation ring
exhibits the valuation ring as a characteristic-two discrete valuation ring in which the given
element becomes a square only after completion. -/
private theorem dvr_square_root_of_embedding
    {k : Type u} [Field k] [CharP k 2]
    {K : Type v} [Field K] [CharP K 2]
    (e : K →+* LaurentSeries k) (r : k →+* K) (x a : K)
    (hx : e x = (PowerSeries.X : PowerSeries k))
    (hr : ∀ c, e (r c) = algebraMap k (LaurentSeries k) c)
    (f : PowerSeries k) (ha : e a = (f : LaurentSeries k) ^ 2)
    (hf : (f : LaurentSeries k) ∉ Set.range e) :
    ∃ (D : Type v) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D)
      (_ : IsNoetherianRing D) (_ : IsDiscreteValuationRing D) (_ : CharP D 2)
      (_ : Algebra D K) (_ : IsFractionRing D K) (a₀ : D)
      (α : AdicCompletion (maximalIdeal D) D),
      α ^ 2 = algebraMap D (AdicCompletion (maximalIdeal D) D) a₀ ∧
        ∀ y : K, y ^ 2 ≠ algebraMap D K a₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (LaurentSeries k) 2 := charP_of_injective_algebraMap
    (algebraMap k (LaurentSeries k)).injective 2
  let A := ((Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap e).valuationSubring
  have : IsDiscreteValuationRing A := valuation_dvr k e x hx
  have : CharP A 2 := (algebraMap A K).charP (IsFractionRing.injective A K) 2
  obtain ⟨a₀, ha₀, α, hα⟩ := completion_root_of_embedding k e r x a hx hr f ha
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, a₀, α, hα, fun y hy => ?_⟩
  have hy' : e y = (f : LaurentSeries k) := by
    refine sub_eq_zero.mp (IsNilpotent.eq_zero ⟨2, ?_⟩)
    rw [sub_pow_char, ← map_pow, hy]
    show e (a₀ : K) - (f : LaurentSeries k) ^ 2 = 0
    rw [ha₀, ha, sub_self]
  exact hf ⟨y, hy'⟩

/-- An element of a characteristic-two discrete valuation ring which is a square in the
completion but not in the fraction field gives an analytically ramified one-dimensional
Noetherian local domain: adjoin the square root. -/
private theorem bad_ring_of_square_root {D K : Type v} [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [IsDiscreteValuationRing D] [CharP D 2]
    [Field K] [Algebra D K] [IsFractionRing D K] (a : D)
    {α : AdicCompletion (maximalIdeal D) D}
    (hα : α ^ 2 = algebraMap D (AdicCompletion (maximalIdeal D) D) a)
    (hK : ∀ y : K, y ^ 2 ≠ algebraMap D K a) :
    ∃ (R : Type v) (_ : CommRing R) (_ : CharP R 2) (_ : IsLocalRing R)
      (_ : IsNoetherianRing R) (_ : IsDomain R),
      ringKrullDim R = 1 ∧ ¬ IsAnalyticallyUnramified R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := AdjoinRoot (X ^ 2 - C a)
  have : IsDomain R := isDomain_adjoinRoot_of_monic (K := K)
    (monic_X_pow_sub_C a (by decide)) (by
      simpa using X_pow_sub_C_irreducible_of_prime Nat.prime_two hK)
  have : IsLocalRing R := isLocalRing_adjoinRoot (p := 2) a
  have : CharP R 2 := charP_of_injective_algebraMap
    (algebraMap_adjoinRoot_injective (by decide) a) 2
  have : Algebra.IsIntegral D R :=
    AdjoinRoot.isIntegral_of_monic (monic_X_pow_sub_C a (by decide))
  have : FaithfulSMul D R := (faithfulSMul_iff_algebraMap_injective D R).mpr
    (algebraMap_adjoinRoot_injective (by decide) a)
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Algebra.IsIntegral.ringKrullDim_eq D R]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one D
  · exact AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq hα

attribute [-instance] RatFunc.liftAlgebra in
/-- **A characteristic-two discrete valuation ring with a square root only in its completion.**
Embed `k(x)(y)` into `k((x))` by sending `y` to a series `f` transcendental over `k(x)`, and
restrict to the subfield `K = k(x)(y²)`; the valuation ring `D` of the pulled-back valuation is a
discrete valuation ring, the element of `K` corresponding to `y²` is a square in the completion
of `D` — the truncations of `f` converge to a square root — and it is not a square in `K`,
because `f` itself is not in the image of the embedding.

The lifted rational-function algebra is disabled locally so that it does not compete with the
coefficient algebra on the second rational-function field; the Laurent-series algebra is
installed explicitly. -/
theorem exists_charTwo_isDiscreteValuationRing_sq_in_adicCompletion_not_in_fractionField
    (k : Type u) [Field k] [Countable k] [CharP k 2] :
    ∃ (D K : Type u) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D)
      (_ : IsNoetherianRing D) (_ : IsDiscreteValuationRing D) (_ : CharP D 2)
      (_ : Field K) (_ : Algebra D K) (_ : IsFractionRing D K) (a : D)
      (α : AdicCompletion (maximalIdeal D) D),
      α ^ 2 = algebraMap D (AdicCompletion (maximalIdeal D) D) a ∧
        ∀ y : K, y ^ 2 ≠ algebraMap D K a := by
  let : Algebra (RatFunc k) (LaurentSeries k) := RatFunc.liftAlgebra k (LaurentSeries k)
  obtain ⟨f, hf⟩ := exists_transcendental_series k
  let F := RatFunc k
  let L := RatFunc F
  have : CharP L 2 := inferInstance
  let S : IntermediateField F L := IntermediateField.adjoin F {(RatFunc.X : L) ^ 2}
  let : Algebra F S := S.toSubalgebra.algebra
  let j : L →ₐ[F] LaurentSeries k :=
    (IntermediateField.adjoin F {(f : LaurentSeries k)}).val.comp
      (RatFunc.algEquivOfTranscendental (f : LaurentSeries k) hf).toAlgHom
  have hjX : j RatFunc.X = (f : LaurentSeries k) :=
    RatFunc.algEquivOfTranscendental_X _ hf
  let e : S →+* LaurentSeries k := j.toRingHom.comp S.val.toRingHom
  let r : k →+* S := (algebraMap F S).comp (algebraMap k F)
  let x : S := algebraMap F S RatFunc.X
  let a : S := ⟨(RatFunc.X : L) ^ 2, IntermediateField.subset_adjoin F _ (by simp)⟩
  have hx : e x = (PowerSeries.X : PowerSeries k) := by
    show j (algebraMap F L RatFunc.X) = _
    rw [j.commutes]
    simpa only [PowerSeries.coe_X] using (RatFunc.coe_X (F := k))
  have hr (c : k) : e (r c) = algebraMap k (LaurentSeries k) c := by
    show j (algebraMap F L (algebraMap k F c)) = _
    rw [j.commutes, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C]
    show IsFractionRing.lift
      (FaithfulSMul.algebraMap_injective k[X] (LaurentSeries k))
      (algebraMap k[X] F (Polynomial.C c)) = _
    rw [IsFractionRing.lift_algebraMap]
    simp only [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
      PowerSeries.coe_C, LaurentSeries.algebraMap_apply]
  have ha : e a = (f : LaurentSeries k) ^ 2 := by
    dsimp -zeta only [e, a, RingHom.comp_apply, IntermediateField.val]
    exact (map_pow j (RatFunc.X : L) 2).trans (congrArg (fun y : LaurentSeries k => y ^ 2) hjX)
  have hnot : (f : LaurentSeries k) ∉ Set.range e := by
    rintro ⟨s, hs⟩
    have heq : (s : L) = RatFunc.X := j.injective (hs.trans hjX.symm)
    exact variable_not_mem_squares F (by simpa only [heq] using s.property)
  have : CharP S 2 := S.val.toRingHom.charP S.val.injective 2
  obtain ⟨D, _, _, _, _, _, _, _, _, a₀, α, hα, hK⟩ :=
    dvr_square_root_of_embedding e r x a hx hr f ha hnot
  exact ⟨D, S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, a₀, α, hα, hK⟩

/-- **Stacks 00PB.** There is a one-dimensional Noetherian local domain of positive prime
characteristic whose completion at its maximal ideal is nonreduced, i.e. which is not analytically
unramified. -/
@[stacks 00PB "The existential form of the tag, which is what Stacks 07NZ consumes: the source's
`k` is any countable field of characteristic two, here `ULift (ZMod 2)`, so that the witness lands
in an arbitrary universe. `StacksFrontier.RingTheory.AnalyticallyUnramified.Examples` carries the
source's other construction, over a field with `[k : k^p] = ∞`."]
public theorem exists_noetherianLocalDomain_adicCompletion_not_reduced :
    ∃ (p : ℕ), p.Prime ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : CharP R p) (_ : IsLocalRing R)
        (_ : IsNoetherianRing R) (_ : IsDomain R),
        ringKrullDim R = 1 ∧ ¬ IsAnalyticallyUnramified R := by
  let k := ULift.{u} (ZMod 2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := inferInstance
  have : Countable k := inferInstance
  obtain ⟨D, K, _, _, _, _, _, _, _, _, _, a, α, hα, hK⟩ :=
    exists_charTwo_isDiscreteValuationRing_sq_in_adicCompletion_not_in_fractionField k
  exact ⟨2, Nat.prime_two, bad_ring_of_square_root (K := K) a hα hK⟩

end
