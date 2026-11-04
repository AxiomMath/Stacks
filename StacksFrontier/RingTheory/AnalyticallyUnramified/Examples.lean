module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
import StacksFrontier.RingTheory.Nagata.AnalyticallyUnramified
public import StacksFrontier.RingTheory.Nagata.PthRoot

/-!
# A one-dimensional Noetherian local domain with nonreduced completion

Let `k` be a field of characteristic `p > 0` with `[k : k^p] = ∞`. Stacks 00PB considers the ring
`A ⊆ k[[x]]` of power series whose coefficients generate a finite extension of the subfield `k^p`
of `p`-th powers. It is a discrete valuation ring with completion `k[[x]]`, the extension of
fraction fields `k((x)) / Frac(A)` is purely inseparable (and of infinite degree), and for
`f ∈ k[[x]]` outside `A` the ring `R = A[f] ⊆ k[[x]]` is a one-dimensional Noetherian local domain
whose completion is not reduced.

## Main definitions

* `PowerSeries.pthPowerSubfield`: the subfield `k^p` of `k`.
* `PowerSeries.finiteCoeffSubring`: the ring `A`.
* `PowerSeries.adjoinSubalgebra`: the ring `R = A[f]`.

## Main results

* `PowerSeries.isDiscreteValuationRing_finiteCoeffSubring`: `A` is a discrete valuation ring.
* `PowerSeries.nonempty_algEquiv_adicCompletion_finiteCoeffSubring`: the completion of `A` is
  `k[[x]]`, as an `A`-algebra.
* `PowerSeries.isPurelyInseparable_laurentSeries`,
  `PowerSeries.not_finiteDimensional_laurentSeries`: `k((x))` is purely inseparable over the
  fraction field of `A`, of infinite degree when `[k : k^p] = ∞`.
* `PowerSeries.exists_not_mem_finiteCoeffSubring`: if `[k : k^p] = ∞` there is `f ∈ k[[x]]` with
  `f ∉ A`.
* `PowerSeries.isLocalRing_adjoinSubalgebra`, `PowerSeries.isNoetherianRing_adjoinSubalgebra`,
  `PowerSeries.ringKrullDim_adjoinSubalgebra`,
  `PowerSeries.not_isAnalyticallyUnramified_adjoinSubalgebra`: for `f ∉ A`, the ring `A[f]` is a
  Noetherian local domain of dimension one whose completion is not reduced.

## Implementation notes

The statements about `A` and `R` hold for every field `k` of characteristic `p`; the hypothesis
`[k : k^p] = ∞` is only needed for `A ≠ k[[x]]`, i.e. for some `f ∉ A` to exist
(`PowerSeries.exists_not_mem_finiteCoeffSubring`), and for the infinite degree of
`k((x)) / Frac(A)`. For the latter, choose `t₀, t₁, … ∈ k` with `tₙ ∉ k^p(t₀, …, t_{n-1})`; the
exchange property of `k / k^p` (`PowerSeries.mem_adjoin_simple_of_mem_adjoin_simple`) makes the
sequence `p`-independent (`PowerSeries.outsideSeq_not_mem_adjoin_ne`). The series
`f_j = ∑ₙ t_{⟨j, n⟩} xⁿ` then satisfy `f_m ∉ Frac(A)(f_0, …, f_{m-1})`, since every element of the
latter has its coefficients in an extension of finite degree of `k^p(t_{⟨j, n⟩} : j < m)`
(`PowerSeries.coeffSubfield`), so the degrees of `Frac(A)(f_0, …, f_{m-1})` are unbounded.

`A` is the union of the rings `K[[x]]` over the intermediate fields `k^p ⊆ K ⊆ k` of finite degree
over `k^p`; its units are the series with nonzero constant term and every nonzero element is
`x ^ n` times a unit, which makes it a discrete valuation ring. Its quotients `A / x ^ n A` are
those of `k[[x]]`, since polynomials lie in `A`, which gives the completion. For `f ∉ A` the
element `f ^ p` lies in `A` but has no `p`-th root in `Frac(A)`, so `R ≅ A[T] / (T ^ p - f ^ p)`;
this ring is local because `p`-th powers land in `A`, it is integral over `A`, hence of dimension
one, and since `f` is a `p`-th root of `f ^ p` in the completion `k[[x]]` of `A`, the completion of
`R` contains the nonzero nilpotent `T - f` (`AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq`).

## References

* [Stacks Project, Tag 00PB](https://stacks.math.columbia.edu/tag/00PB)
-/

@[expose] public section

open PowerSeries

namespace PowerSeries

variable (k : Type*) [Field k] (p : ℕ) [ExpChar k p]

/-- The subfield `k^p` of `p`-th powers of `k`. -/
abbrev pthPowerSubfield : Subfield k := (frobenius k p).fieldRange

/-- The power series over `k` whose coefficients all lie in one intermediate field of `k / k^p`
of finite degree over `k^p`; equivalently (`mem_finiteCoeffSubring_iff`), whose coefficients
generate a finite extension of `k^p`. -/
def finiteCoeffSubring : Subring k⟦X⟧ where
  carrier := {f | ∃ K : IntermediateField (pthPowerSubfield k p) k,
    FiniteDimensional (pthPowerSubfield k p) K ∧ ∀ n, coeff n f ∈ K}
  mul_mem' := by
    rintro f g ⟨K, hK, hf⟩ ⟨L, hL, hg⟩
    refine ⟨K ⊔ L, inferInstance, fun n => ?_⟩
    rw [coeff_mul]
    exact sum_mem fun x _ => mul_mem ((le_sup_left : K ≤ K ⊔ L) (hf x.1))
      ((le_sup_right : L ≤ K ⊔ L) (hg x.2))
  one_mem' := ⟨⊥, inferInstance, fun n => by
    rw [coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨K, hK, hf⟩ ⟨L, hL, hg⟩
    refine ⟨K ⊔ L, inferInstance, fun n => ?_⟩
    rw [map_add]
    exact add_mem ((le_sup_left : K ≤ K ⊔ L) (hf n)) ((le_sup_right : L ≤ K ⊔ L) (hg n))
  zero_mem' := ⟨⊥, inferInstance, fun n => by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro f ⟨K, hK, hf⟩
    exact ⟨K, hK, fun n => by rw [map_neg]; exact neg_mem (hf n)⟩

variable {k p}

/-- A power series whose coefficients lie in an intermediate field of finite degree over `k^p`
lies in `finiteCoeffSubring k p`. -/
theorem mem_finiteCoeffSubring_of_coeff_mem (K : IntermediateField (pthPowerSubfield k p) k)
    [FiniteDimensional (pthPowerSubfield k p) K] {f : k⟦X⟧} (hf : ∀ n, coeff n f ∈ K) :
    f ∈ finiteCoeffSubring k p :=
  ⟨K, inferInstance, hf⟩

/-- A power series lies in `finiteCoeffSubring k p` exactly when its coefficients generate a
finite extension of `k^p`. -/
theorem mem_finiteCoeffSubring_iff {f : k⟦X⟧} :
    f ∈ finiteCoeffSubring k p ↔ FiniteDimensional (pthPowerSubfield k p)
      (IntermediateField.adjoin (pthPowerSubfield k p) (Set.range fun n => coeff n f)) := by
  refine ⟨fun ⟨K, hK, hf⟩ => ?_, fun h => ⟨_, h, fun n => IntermediateField.subset_adjoin _ _
    ⟨n, rfl⟩⟩⟩
  have hle : IntermediateField.adjoin (pthPowerSubfield k p) (Set.range fun n => coeff n f) ≤ K :=
    IntermediateField.adjoin_le_iff.mpr (Set.range_subset_iff.mpr hf)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

/-- The constant power series lie in `finiteCoeffSubring k p`: an element `c` of `k` is a root of
`X ^ p - c ^ p` over `k^p`. -/
theorem C_mem_finiteCoeffSubring (c : k) : C c ∈ finiteCoeffSubring k p := by
  have hc : IsIntegral (pthPowerSubfield k p) c := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ⟨c ^ p, c, rfl⟩,
      Polynomial.monic_X_pow_sub_C _ (expChar_pos k p).ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
    rfl
  have := IntermediateField.adjoin.finiteDimensional hc
  refine mem_finiteCoeffSubring_of_coeff_mem
    (IntermediateField.adjoin (pthPowerSubfield k p) {c}) fun n => ?_
  rw [coeff_C]
  split_ifs
  · exact IntermediateField.mem_adjoin_simple_self _ c
  · exact zero_mem _

/-- The variable `x` lies in `finiteCoeffSubring k p`. -/
theorem X_mem_finiteCoeffSubring : (X : k⟦X⟧) ∈ finiteCoeffSubring k p :=
  mem_finiteCoeffSubring_of_coeff_mem ⊥ fun n => by
    rw [coeff_X]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

/-- The `p`-th power of any power series lies in `finiteCoeffSubring k p`: its coefficients are
`p`-th powers. -/
theorem pow_mem_finiteCoeffSubring (f : k⟦X⟧) : f ^ p ∈ finiteCoeffSubring k p := by
  rw [← map_frobenius_expand p (expChar_pos k p).ne']
  refine mem_finiteCoeffSubring_of_coeff_mem ⊥ fun n => ?_
  rw [coeff_map]
  exact IntermediateField.mem_bot.mpr ⟨⟨_, _, rfl⟩, rfl⟩

/-- The coefficients of the inverse of a power series lie in any subfield containing those of
the series. -/
theorem inv_mem_finiteCoeffSubring {f : k⟦X⟧} (hf : f ∈ finiteCoeffSubring k p) :
    f⁻¹ ∈ finiteCoeffSubring k p := by
  obtain ⟨K, hK, hc⟩ := hf
  by_cases h0 : constantCoeff f = 0
  · rw [PowerSeries.inv_eq_zero.mpr h0]
    exact zero_mem _
  let g : K⟦X⟧ := mk fun n => ⟨coeff n f, hc n⟩
  have hg : map K.val.toRingHom g = f := ext fun n => by simp [g]
  have hg0 : constantCoeff g ≠ 0 := fun h => h0 (by
    rw [← hg, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      h, map_zero])
  have hinv : f⁻¹ = map K.val.toRingHom g⁻¹ := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one h0, ← hg, ← map_mul, PowerSeries.inv_mul_cancel _ hg0,
      map_one]
  refine ⟨K, hK, fun n => ?_⟩
  rw [hinv, coeff_map]
  exact (coeff n g⁻¹).2

/-- Removing the first `m` coefficients of a power series in `finiteCoeffSubring k p` keeps it in
`finiteCoeffSubring k p`. -/
theorem mk_coeff_add_mem_finiteCoeffSubring {f : k⟦X⟧} (hf : f ∈ finiteCoeffSubring k p)
    (m : ℕ) : mk (fun n => coeff (n + m) f) ∈ finiteCoeffSubring k p := by
  obtain ⟨K, hK, hc⟩ := hf
  exact ⟨K, hK, fun n => by simpa using hc (n + m)⟩

/-- An element of `finiteCoeffSubring k p` with nonzero constant coefficient is a unit there. -/
theorem isUnit_of_constantCoeff_ne_zero {f : finiteCoeffSubring k p}
    (hf : constantCoeff (f : k⟦X⟧) ≠ 0) : IsUnit f :=
  isUnit_iff_exists_inv.mpr ⟨⟨_, inv_mem_finiteCoeffSubring f.2⟩,
    Subtype.ext (PowerSeries.mul_inv_cancel _ hf)⟩

/-- Every nonzero element of `finiteCoeffSubring k p` is a power of `X` times a unit. -/
theorem exists_eq_X_pow_mul_unit {f : finiteCoeffSubring k p} (hf : f ≠ 0) :
    ∃ (n : ℕ) (u : (finiteCoeffSubring k p)ˣ),
      (f : k⟦X⟧) = X ^ n * ((u : finiteCoeffSubring k p) : k⟦X⟧) := by
  have hf' : (f : k⟦X⟧) ≠ 0 := fun h => hf (Subtype.ext h)
  set m := (f : k⟦X⟧).order.toNat
  let u : finiteCoeffSubring k p := ⟨_, mk_coeff_add_mem_finiteCoeffSubring f.2 m⟩
  have hu : constantCoeff (u : k⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact coeff_order hf'
  refine ⟨m, (isUnit_of_constantCoeff_ne_zero hu).unit, ext fun n => ?_⟩
  rw [IsUnit.unit_spec, coeff_X_pow_mul']
  split_ifs with h
  · simp [u, Nat.sub_add_cancel h]
  · have hm : ((m : ℕ) : ℕ∞) = order (f : k⟦X⟧) :=
      ENat.natCast_toNat (order_finite_iff_ne_zero.mpr hf').ne
    exact coeff_of_lt_order _ (hm ▸ by exact_mod_cast not_le.mp h)

/-- The uniformizer `x` of `finiteCoeffSubring k p`. -/
noncomputable def uniformizer : finiteCoeffSubring k p := ⟨X, X_mem_finiteCoeffSubring⟩

/-- The uniformizer is the variable `x`. -/
@[simp]
theorem coe_uniformizer : ((uniformizer : finiteCoeffSubring k p) : k⟦X⟧) = X := rfl

/-- The uniformizer is irreducible in `finiteCoeffSubring k p`: in a factorization `X = a * b`
one factor has order zero, hence nonzero constant coefficient, hence is a unit. -/
theorem irreducible_uniformizer : Irreducible (uniformizer : finiteCoeffSubring k p) := by
  refine ⟨fun hx => ?_, fun a b hab => ?_⟩
  · have := (hx.map (finiteCoeffSubring k p).subtype).map constantCoeff
    simp [uniformizer] at this
  · have h := congrArg (fun y : finiteCoeffSubring k p => order (y : k⟦X⟧)) hab
    simp only [coe_uniformizer, Subring.coe_mul, order_X, order_mul] at h
    by_contra! hne
    have hord (y : finiteCoeffSubring k p) (hy : ¬IsUnit y) : 1 ≤ order (y : k⟦X⟧) :=
      Order.one_le_iff_ne_zero.mpr fun h0 => hy (isUnit_of_constantCoeff_ne_zero fun hc =>
        (order_ne_zero_iff_constCoeff_eq_zero.mpr hc) h0)
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add (hord a hne.1) (hord b hne.2)).trans h.symm.le
    exact absurd h2 (by decide)

/-- **Stacks 00PB: `A` is a discrete valuation ring**, with uniformizer `x`. -/
@[stacks 00PB "The ring `A` is a discrete valuation ring."]
theorem isDiscreteValuationRing_finiteCoeffSubring :
    IsDiscreteValuationRing (finiteCoeffSubring k p) :=
  .ofHasUnitMulPowIrreducibleFactorization ⟨uniformizer, irreducible_uniformizer, fun {f} hf => by
    obtain ⟨n, u, hu⟩ := exists_eq_X_pow_mul_unit hf
    exact ⟨n, u, Subtype.ext (by simp [hu])⟩⟩

/-- `A` is a discrete valuation ring. -/
instance : IsDiscreteValuationRing (finiteCoeffSubring k p) :=
  isDiscreteValuationRing_finiteCoeffSubring

/-- The maximal ideal of `A` is generated by `x`. -/
theorem maximalIdeal_finiteCoeffSubring :
    IsLocalRing.maximalIdeal (finiteCoeffSubring k p) = Ideal.span {uniformizer} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp irreducible_uniformizer

/-- An element of `finiteCoeffSubring k p` is divisible by `x ^ n` exactly when its first `n`
coefficients vanish. -/
theorem uniformizer_pow_dvd_iff {n : ℕ} {a : finiteCoeffSubring k p} :
    uniformizer ^ n ∣ a ↔ ∀ m < n, coeff m (a : k⟦X⟧) = 0 := by
  refine ⟨fun ⟨b, hb⟩ => X_pow_dvd_iff.mp ⟨b, by simp [hb]⟩, fun h => ?_⟩
  refine ⟨⟨_, mk_coeff_add_mem_finiteCoeffSubring a.2 n⟩, Subtype.ext (ext fun m => ?_)⟩
  rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_uniformizer, coeff_X_pow_mul']
  split_ifs with hm
  · rw [coeff_mk, Nat.sub_add_cancel hm]
  · exact h m (not_le.mp hm)

/-- Polynomials lie in `finiteCoeffSubring k p`. -/
theorem coe_polynomial_mem_finiteCoeffSubring (q : Polynomial k) :
    (q : k⟦X⟧) ∈ finiteCoeffSubring k p := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => rw [Polynomial.coe_add]; exact add_mem hq hr
  | monomial n a =>
    rw [Polynomial.coe_monomial, monomial_eq_C_mul_X_pow]
    exact mul_mem (C_mem_finiteCoeffSubring a) (pow_mem X_mem_finiteCoeffSubring n)

/-- The truncations of a power series, as a Cauchy sequence in `finiteCoeffSubring k p` for the
`x`-adic topology. -/
noncomputable def truncCauchy (g : k⟦X⟧) :
    AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal (finiteCoeffSubring k p))
      (finiteCoeffSubring k p) :=
  AdicCompletion.AdicCauchySequence.mk _ _
    (fun n => ⟨trunc n g, coe_polynomial_mem_finiteCoeffSubring _⟩)
    fun n => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, maximalIdeal_finiteCoeffSubring,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton, uniformizer_pow_dvd_iff]
      intro m hm
      simp [coeff_trunc, hm, hm.trans (Nat.lt_succ_self n)]

/-- **Stacks 00PB: the completion of `A` is `k[[x]]`.** The inclusion `A ⊆ k[[x]]` induces an
isomorphism of `A`-algebras from the completion of `A` to `k[[x]]`. -/
@[stacks 00PB "The completion of `A` is `k[[x]]`: an isomorphism of `A`-algebras
`A^ ≃ k[[x]]`."]
theorem nonempty_algEquiv_adicCompletion_finiteCoeffSubring :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (finiteCoeffSubring k p))
      (finiteCoeffSubring k p) ≃ₐ[finiteCoeffSubring k p] k⟦X⟧) := by
  set A := finiteCoeffSubring k p
  let J : Ideal k⟦X⟧ := Ideal.span {X}
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A k⟦X⟧) ≤ J := by
    rw [maximalIdeal_finiteCoeffSubring, Ideal.map_span, Set.image_singleton]
    rfl
  let ψ := Stacks.Nagata.PthRootDescent.mapAdicCompletion (IsLocalRing.maximalIdeal A) J hmap
  let e := AdicCompletion.ofAlgEquiv J (S := k⟦X⟧)
  have hψ (y) (n : ℕ) (a : A)
      (ha : AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n y = Ideal.Quotient.mk _ a) :
      AdicCompletion.evalₐ J n (ψ y) = Ideal.Quotient.mk _ (a : k⟦X⟧) := by
    rw [Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion, ha, Ideal.quotientMap_mk]
    rfl
  let φ : AdicCompletion (IsLocalRing.maximalIdeal A) A →ₐ[A] k⟦X⟧ :=
    { e.symm.toRingEquiv.toRingHom.comp ψ with
      commutes' := fun a =>
        (congrArg e.symm (Stacks.Nagata.PthRootDescent.mapAdicCompletion_of hmap a)).trans
          (e.symm_apply_apply _) }
  refine ⟨AlgEquiv.ofBijective φ ⟨(injective_iff_map_eq_zero φ).mpr fun y hy => ?_, fun g => ?_⟩⟩
  · have hy' : ψ y = 0 := by
      have h1 : e (φ y) = ψ y := e.apply_symm_apply _
      rw [← h1, hy, map_zero]
    refine AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ n y)
    have h0 := hψ y n a ha.symm
    rw [hy', map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at h0
    rw [← ha, map_zero, Ideal.Quotient.eq_zero_iff_mem, maximalIdeal_finiteCoeffSubring,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, uniformizer_pow_dvd_iff]
    exact X_pow_dvd_iff.mp h0
  · refine ⟨AdicCompletion.mk _ _ (truncCauchy g), e.injective ?_⟩
    refine AdicCompletion.ext_evalₐ fun n => ?_
    have h1 : e (φ (AdicCompletion.mk _ _ (truncCauchy g))) =
        ψ (AdicCompletion.mk _ _ (truncCauchy g)) := e.apply_symm_apply _
    rw [h1, hψ _ n _ (AdicCompletion.evalₐ_mk _ _ _), AdicCompletion.ofAlgEquiv_apply,
      AdicCompletion.evalₐ_of, Ideal.Quotient.eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, X_pow_dvd_iff]
    intro m hm
    simp [truncCauchy, coeff_trunc, hm]

/-- If `[k : k^p] = ∞`, then `finiteCoeffSubring k p ≠ k[[x]]`: a power series whose coefficients
are infinitely many `k^p`-linearly independent elements of `k` does not lie in it. So the ring
`R = A[f]` of Stacks 00PB exists. -/
theorem exists_not_mem_finiteCoeffSubring
    (h : ¬ FiniteDimensional (pthPowerSubfield k p) k) :
    ∃ f : k⟦X⟧, f ∉ finiteCoeffSubring k p := by
  let b := Module.Basis.ofVectorSpace (pthPowerSubfield k p) k
  have : Infinite (Module.Basis.ofVectorSpaceIndex (pthPowerSubfield k p) k) := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact h (Module.Finite.of_basis b)
  let e := Infinite.natEmbedding (Module.Basis.ofVectorSpaceIndex (pthPowerSubfield k p) k)
  refine ⟨mk fun n => b (e n), fun ⟨K, hK, hc⟩ => ?_⟩
  let c : ℕ → K := fun n => ⟨b (e n), by simpa using hc n⟩
  have hli : LinearIndependent (pthPowerSubfield k p) c :=
    .of_comp K.val.toLinearMap (b.linearIndependent.comp e e.injective)
  have := hli.finite_of_isNoetherian
  exact not_finite ℕ

/-! ### The ring `R = A[f]` -/

section Adjoin

/-- The element `f ^ p` of `finiteCoeffSubring k p`. -/
noncomputable def pthPower (f : k⟦X⟧) : finiteCoeffSubring k p :=
  ⟨f ^ p, pow_mem_finiteCoeffSubring f⟩

variable [Fact p.Prime] [CharP k p]

/-- If `f ∉ A`, then `f ^ p` is not a `p`-th power in the fraction field of `A`: a `p`-th root
`a / b` would give `a = f b` in `k[[x]]`, and dividing by the power of `x` in `b` would put `f`
in `A`. -/
theorem pow_ne_algebraMap_pthPower {f : k⟦X⟧} (hf : f ∉ finiteCoeffSubring k p)
    (y : FractionRing (finiteCoeffSubring k p)) :
    y ^ p ≠ algebraMap _ _ (pthPower (p := p) f) := by
  intro hy
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (finiteCoeffSubring k p)) y
  have hb0 : (b : finiteCoeffSubring k p) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have h1 : pthPower (p := p) f * (b : finiteCoeffSubring k p) ^ p = a ^ p := by
    refine FaithfulSMul.algebraMap_injective _ (FractionRing (finiteCoeffSubring k p)) ?_
    rw [map_mul, map_pow, map_pow, ← hy, ← hab, mul_pow]
  have : CharP k⟦X⟧ p := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective p
  have h2 : f * (b : k⟦X⟧) = (a : k⟦X⟧) := by
    refine frobenius_inj k⟦X⟧ p ?_
    simpa [frobenius_def, mul_pow, pthPower] using congrArg Subtype.val h1
  obtain ⟨n, u, hu⟩ := exists_eq_X_pow_mul_unit hb0
  obtain ⟨c, hc⟩ : uniformizer ^ n ∣ a := uniformizer_pow_dvd_iff.mpr fun m hm => by
    rw [← h2, hu, mul_left_comm, coeff_X_pow_mul',
      ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr hm)]
  have h3 : f * ((u : finiteCoeffSubring k p) : k⟦X⟧) = (c : k⟦X⟧) := by
    have h4 : (X : k⟦X⟧) ^ n * (f * ((u : finiteCoeffSubring k p) : k⟦X⟧)) =
        X ^ n * (c : k⟦X⟧) := by
      rw [mul_left_comm, ← hu, h2, hc]
      simp
    exact mul_left_cancel₀ (pow_ne_zero n X_ne_zero) h4
  have hu1 : ((u : finiteCoeffSubring k p) : k⟦X⟧) *
      (((u⁻¹ : (finiteCoeffSubring k p)ˣ) : finiteCoeffSubring k p) : k⟦X⟧) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  refine hf ?_
  have : f = (c : k⟦X⟧) * (((u⁻¹ : (finiteCoeffSubring k p)ˣ) : finiteCoeffSubring k p) : k⟦X⟧) :=
    by rw [← h3, mul_assoc, hu1, mul_one]
  rw [this]
  exact mul_mem c.2 ((u⁻¹ : (finiteCoeffSubring k p)ˣ) : finiteCoeffSubring k p).2

/-- The polynomial `T ^ p - f ^ p` over `A`. -/
noncomputable abbrev pthRootPoly (f : k⟦X⟧) : Polynomial (finiteCoeffSubring k p) :=
  Polynomial.X ^ p - Polynomial.C (pthPower (p := p) f)

/-- The evaluation `A[T] ⧸ (T ^ p - f ^ p) → k[[x]]`, `T ↦ f`. -/
noncomputable def adjoinRootHom (f : k⟦X⟧) :
    AdjoinRoot (pthRootPoly (p := p) f) →ₐ[finiteCoeffSubring k p] k⟦X⟧ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) f (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
    rfl)

/-- If `f ∉ A`, the evaluation `A[T] ⧸ (T ^ p - f ^ p) → k[[x]]` is injective: its kernel is a
prime of an integral extension of `A` lying over `0`. -/
theorem adjoinRootHom_injective {f : k⟦X⟧} (hf : f ∉ finiteCoeffSubring k p) :
    Function.Injective (adjoinRootHom (p := p) f) := by
  have hmon : (pthRootPoly (p := p) f).Monic :=
    Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  have := hmon.finite_adjoinRoot
  have : IsDomain (AdjoinRoot (pthRootPoly (p := p) f)) :=
    Stacks.Nagata.PthRootDescent.isDomain_adjoinRoot _ (pow_ne_algebraMap_pthPower hf)
  rw [injective_iff_map_eq_zero]
  intro y hy
  have hker : RingHom.ker (adjoinRootHom (p := p) f).toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := finiteCoeffSubring k p) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes] at ha
    exact (Ideal.mem_bot).mpr (Subtype.ext ha)
  have : y ∈ RingHom.ker (adjoinRootHom (p := p) f).toRingHom := RingHom.mem_ker.mpr hy
  rwa [hker] at this

/-- The ring `R = A[f] ⊆ k[[x]]`. -/
noncomputable abbrev adjoinSubalgebra (f : k⟦X⟧) : Subalgebra (finiteCoeffSubring k p) k⟦X⟧ :=
  Algebra.adjoin (finiteCoeffSubring k p) {f}

/-- If `f ∉ A`, then `A[f] ≅ A[T] ⧸ (T ^ p - f ^ p)`. -/
noncomputable def adjoinSubalgebraEquiv {f : k⟦X⟧} (hf : f ∉ finiteCoeffSubring k p) :
    adjoinSubalgebra (p := p) f ≃ₐ[finiteCoeffSubring k p]
      AdjoinRoot (pthRootPoly (p := p) f) :=
  ((AlgEquiv.ofInjective _ (adjoinRootHom_injective hf)).trans (Subalgebra.equivOfEq _ _ (by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin_singleton,
      adjoinRootHom, AdjoinRoot.liftAlgHom_root]))).symm

/-- `A` has characteristic `p`. -/
instance : CharP (finiteCoeffSubring k p) p :=
  have : CharP k⟦X⟧ p := charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective p
  (finiteCoeffSubring k p).subtype.charP Subtype.val_injective p

/-- For every `f ∈ k[[x]]`, the ring `A[T] ⧸ (T ^ p - f ^ p)` is local. -/
instance (f : k⟦X⟧) : IsLocalRing (AdjoinRoot (pthRootPoly (p := p) f)) :=
  Stacks.Nagata.PthRootDescent.isLocalRing_adjoinRoot _

/-- **Stacks 00PB: `R = A[f]` is local.** -/
@[stacks 00PB "For `f ∉ A` the ring `R = A[f] ⊆ k[[x]]` is local."]
theorem isLocalRing_adjoinSubalgebra {f : k⟦X⟧} (hf : f ∉ finiteCoeffSubring k p) :
    IsLocalRing (adjoinSubalgebra (p := p) f) :=
  IsLocalRing.of_surjective' (adjoinSubalgebraEquiv hf).symm.toRingEquiv.toRingHom
    (adjoinSubalgebraEquiv hf).symm.surjective

omit [Fact p.Prime] [CharP k p] in
/-- **Stacks 00PB: `R = A[f]` is Noetherian.** It is of finite type over the Noetherian ring
`A`. -/
@[stacks 00PB "The ring `R = A[f] ⊆ k[[x]]` is Noetherian."]
theorem isNoetherianRing_adjoinSubalgebra (f : k⟦X⟧) :
    IsNoetherianRing (adjoinSubalgebra (p := p) f) := by
  have : Algebra.FiniteType (finiteCoeffSubring k p) (adjoinSubalgebra (p := p) f) :=
    (Subalgebra.fg_iff_finiteType _).mp (by simpa using Subalgebra.fg_adjoin_finset {f})
  exact Algebra.FiniteType.isNoetherianRing (finiteCoeffSubring k p) _

/-- **Stacks 00PB: `R = A[f]` has dimension one.** It is integral over `A`, with the same Krull
dimension. -/
@[stacks 00PB "For `f ∉ A` the ring `R = A[f] ⊆ k[[x]]` has Krull dimension one."]
theorem ringKrullDim_adjoinSubalgebra {f : k⟦X⟧} (hf : f ∉ finiteCoeffSubring k p) :
    ringKrullDim (adjoinSubalgebra (p := p) f) = 1 := by
  have hmon : (pthRootPoly (p := p) f).Monic :=
    Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero
  have := hmon.finite_adjoinRoot
  have : FaithfulSMul (finiteCoeffSubring k p) (AdjoinRoot (pthRootPoly (p := p) f)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Stacks.Nagata.PthRootDescent.algebraMap_adjoinRoot_injective (Fact.out : p.Prime).ne_zero _)
  rw [ringKrullDim_eq_of_ringEquiv (adjoinSubalgebraEquiv hf).toRingEquiv,
    ← Algebra.IsIntegral.ringKrullDim_eq (finiteCoeffSubring k p),
    IsDiscreteValuationRing.ringKrullDim_eq_one]

/-- **Stacks 00PB: the completion of `R = A[f]` is not reduced.** The series `f` is a `p`-th root
of `f ^ p ∈ A` in the completion `k[[x]]` of `A`, while `R = A[T] ⧸ (T ^ p - f ^ p)`; so the
completion of `R` contains the nonzero nilpotent `T - f`
(`AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq`). -/
@[stacks 00PB "For `f ∉ A` the completion of `R = A[f]` is not reduced, i.e. `R` is not
analytically unramified (Definition 032X)."]
theorem not_isAnalyticallyUnramified_adjoinSubalgebra {f : k⟦X⟧}
    (hf : f ∉ finiteCoeffSubring k p) :
    letI := isLocalRing_adjoinSubalgebra hf
    ¬ IsAnalyticallyUnramified (adjoinSubalgebra (p := p) f) := by
  let := isLocalRing_adjoinSubalgebra hf
  intro h
  obtain ⟨E⟩ := nonempty_algEquiv_adicCompletion_finiteCoeffSubring (k := k) (p := p)
  have hα : (E.symm f) ^ p = algebraMap _ _ (pthPower (p := p) f) := by
    rw [← map_pow, ← E.symm.commutes]
    rfl
  exact AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq hα
    (IsAnalyticallyUnramified.of_ringEquiv (adjoinSubalgebraEquiv hf).symm.toRingEquiv h)

end Adjoin

/-! ### The fraction field of `A` inside `k((x))` -/

section Fraction

/-- The embedding of the fraction field of `A` into `k((x))`, extending `A ⊆ k[[x]] ⊆ k((x))`. -/
noncomputable def fractionRingToLaurentSeries :
    FractionRing (finiteCoeffSubring k p) →+* LaurentSeries k :=
  IsFractionRing.lift (K := FractionRing (finiteCoeffSubring k p))
    (g := (HahnSeries.ofPowerSeries ℤ k).comp (finiteCoeffSubring k p).subtype)
    (HahnSeries.ofPowerSeries_injective.comp Subtype.val_injective)

/-- The embedding of the fraction field of `A` extends the inclusion `A ⊆ k((x))`. -/
theorem fractionRingToLaurentSeries_algebraMap (a : finiteCoeffSubring k p) :
    fractionRingToLaurentSeries (algebraMap _ (FractionRing (finiteCoeffSubring k p)) a) =
      HahnSeries.ofPowerSeries ℤ k a :=
  IsFractionRing.lift_algebraMap _ a

/-- The integer powers of `x` lie in the image of the fraction field of `A`. -/
theorem single_one_mem_range (m : ℤ) :
    HahnSeries.single m (1 : k) ∈ (fractionRingToLaurentSeries (k := k) (p := p)).range := by
  have hn (n : ℕ) : HahnSeries.single (n : ℤ) (1 : k) ∈
      (fractionRingToLaurentSeries (k := k) (p := p)).range :=
    ⟨algebraMap _ _ (uniformizer ^ n), by
      rw [fractionRingToLaurentSeries_algebraMap, SubmonoidClass.coe_pow, coe_uniformizer,
        HahnSeries.ofPowerSeries_X_pow]⟩
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · exact hn n
  · have h1 : HahnSeries.single (-(n : ℤ)) (1 : k) = (HahnSeries.single (n : ℤ) (1 : k))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      rfl
    obtain ⟨z, hz⟩ := hn n
    exact ⟨z⁻¹, by rw [map_inv₀, hz, h1]⟩

variable [Fact p.Prime] [CharP k p]

/-- **Stacks 00PB: `k((x))` is purely inseparable over the fraction field of `A`.** The `p`-th
power of `x ^ m g`, `g ∈ k[[x]]`, is `x ^ (p m) g ^ p` with `g ^ p ∈ A`. -/
@[stacks 00PB "The extension `k((x))` of the fraction field of `A` is purely inseparable; that it
has infinite degree is `PowerSeries.not_finiteDimensional_laurentSeries`."]
theorem isPurelyInseparable_laurentSeries :
    letI := (fractionRingToLaurentSeries (k := k) (p := p)).toAlgebra
    IsPurelyInseparable (FractionRing (finiteCoeffSubring k p)) (LaurentSeries k) := by
  let := (fractionRingToLaurentSeries (k := k) (p := p)).toAlgebra
  have : CharP (FractionRing (finiteCoeffSubring k p)) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective (finiteCoeffSubring k p)
      (FractionRing (finiteCoeffSubring k p))) p
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro y
  refine ⟨1, ?_⟩
  rw [pow_one, RingHom.algebraMap_toAlgebra, ← y.single_order_mul_powerSeriesPart, mul_pow]
  refine mul_mem (pow_mem (single_one_mem_range _) p) ⟨algebraMap _ _ (pthPower (p := p)
    y.powerSeriesPart), ?_⟩
  rw [fractionRingToLaurentSeries_algebraMap, ← map_pow]
  rfl

end Fraction

/-! ### The degree of `k((x))` over the fraction field of `A` -/

section Degree

variable [Fact p.Prime]

variable {B : Type*} [Field B] [Algebra B k]

omit [Fact p.Prime] [ExpChar k p] in
/-- Over a field `B` whose image in `k` contains all `p`-th powers, every element of `k` is
integral: it is a root of `X ^ p - x ^ p`. -/
theorem isIntegral_of_pow_mem (hp : p ≠ 0) (hB : ∀ x : k, ∃ b : B, algebraMap B k b = x ^ p)
    (x : k) : IsIntegral B x := by
  obtain ⟨b, hb⟩ := hB x
  refine ⟨Polynomial.X ^ p - Polynomial.C b, Polynomial.monic_X_pow_sub_C _ hp, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hb, sub_self]

omit [ExpChar k p] in
/-- Adjoining one element to such a field `B` gives an extension of degree at most `p`. -/
theorem finrank_adjoin_simple_le (hB : ∀ x : k, ∃ b : B, algebraMap B k b = x ^ p) (x : k) :
    Module.finrank B (IntermediateField.adjoin B {x}) ≤ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨b, hb⟩ := hB x
  rw [IntermediateField.adjoin.finrank (isIntegral_of_pow_mem hp hB x)]
  refine (Polynomial.natDegree_le_of_dvd (minpoly.dvd B x ?_)
    (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hp) b)).trans
    Polynomial.natDegree_X_pow_sub_C.le
  simp [hb]

/-- Adjoining to such a field `B` an element not in `B` gives an extension of degree `p`: the
polynomial `X ^ p - x ^ p` has no root in `B`, hence is irreducible. -/
theorem finrank_adjoin_simple_eq (hB : ∀ x : k, ∃ b : B, algebraMap B k b = x ^ p) {x : k}
    (hx : x ∉ (⊥ : IntermediateField B k)) :
    Module.finrank B (IntermediateField.adjoin B {x}) = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨b, hb⟩ := hB x
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C b) :=
    X_pow_sub_C_irreducible_of_prime hp fun y hy => hx (IntermediateField.mem_bot.mpr
      ⟨y, frobenius_inj k p (by rw [frobenius_def, frobenius_def, ← map_pow, hy, hb])⟩)
  rw [IntermediateField.adjoin.finrank (isIntegral_of_pow_mem hp.ne_zero hB x),
    ← minpoly.eq_of_irreducible_of_monic hirr (by simp [hb])
      (Polynomial.monic_X_pow_sub_C _ hp.ne_zero), Polynomial.natDegree_X_pow_sub_C]

/-- **The exchange property of `p`-independence.** Over a field `B` whose image in `k` contains
all `p`-th powers, if `t ∈ B(s)` and `t ∉ B` then `s ∈ B(t)`: both extensions have degree `p`. -/
theorem mem_adjoin_simple_of_mem_adjoin_simple (hB : ∀ x : k, ∃ b : B, algebraMap B k b = x ^ p)
    {s t : k} (ht : t ∈ IntermediateField.adjoin B {s})
    (htB : t ∉ (⊥ : IntermediateField B k)) : s ∈ IntermediateField.adjoin B {t} := by
  have hle : IntermediateField.adjoin B {t} ≤ IntermediateField.adjoin B {s} :=
    IntermediateField.adjoin_simple_le_iff.mpr ht
  have := IntermediateField.adjoin.finiteDimensional
    (isIntegral_of_pow_mem (Fact.out : p.Prime).ne_zero hB s)
  rw [IntermediateField.eq_of_le_of_finrank_le hle (by
    rw [finrank_adjoin_simple_eq hB htB]; exact finrank_adjoin_simple_le hB s)]
  exact IntermediateField.mem_adjoin_simple_self B s

omit [Fact p.Prime] [ExpChar k p] in
/-- A finite-dimensional extension cannot contain a sequence `s₀, s₁, …` with each `sᵣ` outside
the field generated by the earlier ones: their degrees would increase without bound. -/
theorem not_forall_not_mem_adjoin_image {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : IntermediateField K L) [FiniteDimensional K V] (s : ℕ → L) (hs : ∀ r, s r ∈ V)
    (hind : ∀ r, s r ∉ IntermediateField.adjoin K (s '' Set.Iio r)) : False := by
  let H (r : ℕ) := IntermediateField.adjoin K (s '' Set.Iio r)
  have hHV (r : ℕ) : H r ≤ V :=
    IntermediateField.adjoin_le_iff.mpr (Set.image_subset_iff.mpr fun i _ => hs i)
  have hfin (r : ℕ) : FiniteDimensional K (H r) := by
    have : Finite (s '' Set.Iio r) := ((Set.finite_Iio r).image s).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x hx =>
      (IsIntegral.of_finite K (⟨x, hHV r (IntermediateField.subset_adjoin K _ hx)⟩ : V)).map
        (IsScalarTower.toAlgHom K V L)
  have hlt (r : ℕ) : Module.finrank K (H r) < Module.finrank K (H (r + 1)) := by
    have hle : H r ≤ H (r + 1) := IntermediateField.adjoin.mono _ _ _
      (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ r)))
    by_contra! h
    refine hind r (show s r ∈ H r from ?_)
    rw [IntermediateField.eq_of_le_of_finrank_le hle h]
    exact IntermediateField.subset_adjoin K _ ⟨r, Nat.lt_succ_self r, rfl⟩
  have hge (r : ℕ) : r ≤ Module.finrank K (H r) := by
    induction r with
    | zero => exact Nat.zero_le _
    | succ r ih => exact (Nat.succ_le_succ ih).trans (hlt r)
  have := IntermediateField.finrank_le_of_le_right (hHV (Module.finrank K V + 1))
  have := hge (Module.finrank K V + 1)
  omega

omit [Fact p.Prime] in
/-- Every intermediate field of `k / k^p` contains the `p`-th powers. -/
theorem exists_algebraMap_eq_pow (E : IntermediateField (pthPowerSubfield k p) k) (x : k) :
    ∃ b : E, algebraMap E k b = x ^ p :=
  ⟨⟨x ^ p, E.algebraMap_mem ⟨x ^ p, x, frobenius_def p x⟩⟩, rfl⟩

omit [Fact p.Prime] in
/-- `k^p` contains the `p`-th powers. -/
theorem exists_algebraMap_eq_pow' (x : k) :
    ∃ b : pthPowerSubfield k p, algebraMap (pthPowerSubfield k p) k b = x ^ p :=
  ⟨⟨x ^ p, x, frobenius_def p x⟩, rfl⟩

/-- Over a field `B` whose image in `k` contains all `q`-th powers, a finite set generates a
finite-dimensional extension. -/
private theorem finiteDimensional_adjoin_of_pow_mem {q : ℕ} [Fact q.Prime]
    (hB : ∀ x : k, ∃ b : B, algebraMap B k b = x ^ q) (S : Set k) [Finite S] :
    FiniteDimensional B (IntermediateField.adjoin B S) :=
  IntermediateField.finiteDimensional_adjoin fun x _ =>
    isIntegral_of_pow_mem (Fact.out : q.Prime).ne_zero hB x

/-- If `[k : k^p] = ∞`, no finite set generates `k` over `k^p`. -/
theorem exists_not_mem_adjoin (hk : ¬ FiniteDimensional (pthPowerSubfield k p) k)
    {S : Set k} (hS : S.Finite) :
    ∃ t : k, t ∉ IntermediateField.adjoin (pthPowerSubfield k p) S := by
  by_contra! h
  have := hS.to_subtype
  have := finiteDimensional_adjoin_of_pow_mem (exists_algebraMap_eq_pow' (p := p)) S
  rw [show IntermediateField.adjoin (pthPowerSubfield k p) S = ⊤ from
    eq_top_iff.mpr fun x _ => h x] at this
  exact hk (IntermediateField.topEquiv.toLinearEquiv.finiteDimensional)

open Classical in
variable (k p) in
/-- An element of `k` outside `k^p(L)`, if there is one. -/
noncomputable def nextOutside (L : List k) : k :=
  if h : ∃ t : k, t ∉ IntermediateField.adjoin (pthPowerSubfield k p) {x | x ∈ L} then h.choose
  else 0

variable (k p) in
/-- The lists `[t₀, …, t_{n-1}]` of the sequence `outsideSeq`. -/
noncomputable def outsideList : ℕ → List k
  | 0 => []
  | n + 1 => outsideList n ++ [nextOutside k p (outsideList n)]

variable (k p) in
/-- A sequence `t₀, t₁, …` in `k` with each `tₙ` outside `k^p(t₀, …, t_{n-1})`, when
`[k : k^p] = ∞`. -/
noncomputable def outsideSeq (n : ℕ) : k := nextOutside k p (outsideList k p n)

omit [Fact p.Prime] in
/-- The list `outsideList k p n` holds `t₀, …, t_{n-1}`. -/
theorem setOf_mem_outsideList (n : ℕ) :
    {x | x ∈ outsideList k p n} = outsideSeq k p '' Set.Iio n := by
  induction n with
  | zero => simp [outsideList]
  | succ n ih =>
    ext x
    have hx := Set.ext_iff.mp ih x
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Iio] at hx ⊢
    rw [outsideList, List.mem_append, hx, List.mem_singleton]
    constructor
    · rintro (⟨m, hm, rfl⟩ | rfl)
      · exact ⟨m, by omega, rfl⟩
      · exact ⟨n, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact Or.inl ⟨m, hm, rfl⟩
      · exact Or.inr rfl

/-- Each `tₙ` lies outside `k^p(t₀, …, t_{n-1})`. -/
theorem outsideSeq_not_mem (hk : ¬ FiniteDimensional (pthPowerSubfield k p) k) (n : ℕ) :
    outsideSeq k p n ∉
      IntermediateField.adjoin (pthPowerSubfield k p) (outsideSeq k p '' Set.Iio n) := by
  have hex := exists_not_mem_adjoin hk (List.finite_toSet (outsideList k p n))
  rw [← setOf_mem_outsideList]
  unfold outsideSeq nextOutside
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- Adjoining `S` to an intermediate field `B` is adjoining `B ∪ S` over the base field. -/
private theorem mem_adjoin_iff_mem_adjoin_union {F : Type*} [Field F] [Algebra F k]
    (B : IntermediateField F k) (x : k) (S : Set k) :
    x ∈ IntermediateField.adjoin B S ↔ x ∈ IntermediateField.adjoin F ((B : Set k) ∪ S) := by
  rw [← IntermediateField.restrictScalars_adjoin, IntermediateField.mem_restrictScalars]

/-- **The sequence is `p`-independent.** Each `tₙ` lies outside the field generated over `k^p` by
all the other terms. If not, take `M` least with `tₙ ∈ k^p(tₘ : m ≠ n, m < M)`; then `n < M - 1`
and the exchange property puts `t_{M-1}` in `k^p(t₀, …, t_{M-2})`. -/
theorem outsideSeq_not_mem_adjoin_ne (hk : ¬ FiniteDimensional (pthPowerSubfield k p) k)
    (n : ℕ) : outsideSeq k p n ∉
      IntermediateField.adjoin (pthPowerSubfield k p) (outsideSeq k p '' {m | m ≠ n}) := by
  classical
  set F0 := pthPowerSubfield k p
  set t := outsideSeq k p
  let Q (M : ℕ) : Prop := t n ∈ IntermediateField.adjoin F0 (t '' ({m | m ≠ n} ∩ Set.Iio M))
  have hsmall (M : ℕ) (hM : M ≤ n + 1) : ¬ Q M := fun h => outsideSeq_not_mem hk n
    (IntermediateField.adjoin.mono _ _ _ (Set.image_mono fun m hm => by
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio] at hm
      exact Set.mem_Iio.mpr (by omega)) h)
  intro h
  have hQ : ∃ M, Q M := by
    obtain ⟨T, hT, hTn⟩ := IntermediateField.exists_finset_of_mem_adjoin h
    obtain ⟨S, hS, hSfin, hSn⟩ := (Set.exists_subset_image_finite_and
      (p := fun X => t n ∈ IntermediateField.adjoin F0 X)).mp ⟨T, hT, T.finite_toSet, hTn⟩
    obtain ⟨M, hM⟩ := hSfin.bddAbove
    refine ⟨M + 1, IntermediateField.adjoin.mono _ _ _ (Set.image_mono fun m hm => ?_) hSn⟩
    exact ⟨hS hm, Set.mem_Iio.mpr (Nat.lt_succ_of_le (hM hm))⟩
  obtain ⟨M', hM'⟩ : ∃ M', Nat.find hQ = M' + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => hsmall 0 (Nat.zero_le _)
      (h0 ▸ Nat.find_spec hQ))
  have hnM : n < M' := by
    by_contra! hle
    exact hsmall (M' + 1) (by omega) (hM' ▸ Nat.find_spec hQ)
  have hQM : Q (M' + 1) := hM' ▸ Nat.find_spec hQ
  have hnQ : ¬ Q M' := Nat.find_min hQ (by omega)
  set G := IntermediateField.adjoin F0 (t '' ({m | m ≠ n} ∩ Set.Iio M'))
  have h1 : t n ∈ IntermediateField.adjoin G {t M'} := by
    rw [mem_adjoin_iff_mem_adjoin_union]
    refine IntermediateField.adjoin.mono _ _ _ ?_ hQM
    rintro _ ⟨m, ⟨hmn, hm⟩, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact Or.inl (IntermediateField.subset_adjoin _ _ ⟨m, ⟨hmn, hm⟩, rfl⟩)
    · exact Or.inr rfl
  have h2 : t n ∉ (⊥ : IntermediateField G k) := fun hb => by
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hb
    exact hnQ (show t n ∈ G by rw [← hy]; exact y.2)
  have h3 := mem_adjoin_simple_of_mem_adjoin_simple (exists_algebraMap_eq_pow G) h1 h2
  rw [mem_adjoin_iff_mem_adjoin_union] at h3
  refine outsideSeq_not_mem hk M' (IntermediateField.adjoin_le_iff.mpr ?_ h3)
  rintro _ (hx | rfl)
  · exact (IntermediateField.adjoin.mono _ _ _ (Set.image_mono fun m hm => hm.2)
      : G ≤ IntermediateField.adjoin F0 (t '' Set.Iio M')) hx
  · exact IntermediateField.subset_adjoin _ _ ⟨n, hnM, rfl⟩

omit [ExpChar k p] [Fact p.Prime] in
variable (k) in
/-- A field homomorphism `G → k` induces a ring homomorphism of Laurent series. -/
noncomputable def laurentSeriesMap {G : Type*} [Field G] (f : G →+* k) :
    LaurentSeries G →+* LaurentSeries k where
  toFun z := z.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toAddMonoidHom.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

omit [ExpChar k p] [Fact p.Prime] in
/-- The `n`-th coefficient of the image of `z` under `laurentSeriesMap k f` is `f` applied to the
`n`-th coefficient of `z`. -/
@[simp]
theorem coeff_laurentSeriesMap {G : Type*} [Field G] (f : G →+* k) (z : LaurentSeries G) (n : ℤ) :
    (laurentSeriesMap k f z).coeff n = f (z.coeff n) := rfl

omit [Fact p.Prime] in
/-- A Laurent series whose coefficients lie in a subfield `G` of `k` comes from `G((x))`. -/
theorem exists_laurentSeriesMap_eq (G : IntermediateField (pthPowerSubfield k p) k)
    {y : LaurentSeries k} (hy : ∀ n, y.coeff n ∈ G) :
    ∃ z : LaurentSeries G, laurentSeriesMap k G.val.toRingHom z = y :=
  ⟨⟨fun n => ⟨y.coeff n, hy n⟩, y.isPWO_support.mono fun _ hn h0 => hn (Subtype.ext h0)⟩,
    HahnSeries.ext rfl⟩

omit [Fact p.Prime] in
variable (k p) in
/-- The Laurent series whose coefficients lie in `E ⊔ K` for an intermediate field `K` of
`k / k^p` of finite degree. -/
def coeffSubfield (E : IntermediateField (pthPowerSubfield k p) k) :
    Subfield (LaurentSeries k) where
  carrier := {y | ∃ K : IntermediateField (pthPowerSubfield k p) k,
    FiniteDimensional (pthPowerSubfield k p) K ∧ ∀ n, y.coeff n ∈ E ⊔ K}
  zero_mem' := ⟨⊥, inferInstance, fun n => by rw [HahnSeries.coeff_zero]; exact zero_mem _⟩
  one_mem' := ⟨⊥, inferInstance, fun n => by
    rw [HahnSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩
  add_mem' := by
    rintro x y ⟨K, hK, hx⟩ ⟨K', hK', hy⟩
    refine ⟨K ⊔ K', inferInstance, fun n => ?_⟩
    rw [HahnSeries.coeff_add]
    exact add_mem (sup_le_sup_left le_sup_left E (hx n))
      (sup_le_sup_left le_sup_right E (hy n))
  mul_mem' := by
    rintro x y ⟨K, hK, hx⟩ ⟨K', hK', hy⟩
    refine ⟨K ⊔ K', inferInstance, fun n => ?_⟩
    rw [HahnSeries.coeff_mul]
    exact sum_mem fun i _ => mul_mem (sup_le_sup_left le_sup_left E (hx _))
      (sup_le_sup_left le_sup_right E (hy _))
  neg_mem' := by
    rintro x ⟨K, hK, hx⟩
    exact ⟨K, hK, fun n => by rw [HahnSeries.coeff_neg]; exact neg_mem (hx n)⟩
  inv_mem' := by
    rintro y ⟨K, hK, hy⟩
    obtain ⟨z, rfl⟩ := exists_laurentSeriesMap_eq (E ⊔ K) hy
    refine ⟨K, hK, fun n => ?_⟩
    rw [← map_inv₀, coeff_laurentSeriesMap]
    exact ((z⁻¹).coeff n).2

omit [Fact p.Prime] in
/-- The power series in `A` lie in `coeffSubfield k p E`. -/
theorem coe_mem_coeffSubfield (E : IntermediateField (pthPowerSubfield k p) k) {g : k⟦X⟧}
    (hg : g ∈ finiteCoeffSubring k p) : (g : LaurentSeries k) ∈ coeffSubfield k p E := by
  obtain ⟨K, hK, hc⟩ := hg
  refine ⟨K, hK, fun n => ?_⟩
  rw [PowerSeries.coeff_coe]
  split_ifs
  · exact zero_mem _
  · exact (le_sup_right : K ≤ E ⊔ K) (hc _)

omit [Fact p.Prime] in
/-- The fraction field of `A` lies in `coeffSubfield k p E`. -/
theorem fieldRange_le_coeffSubfield (E : IntermediateField (pthPowerSubfield k p) k) :
    (fractionRingToLaurentSeries (k := k) (p := p)).fieldRange ≤ coeffSubfield k p E := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := finiteCoeffSubring k p) q
  rw [map_div₀, fractionRingToLaurentSeries_algebraMap, fractionRingToLaurentSeries_algebraMap]
  exact div_mem (coe_mem_coeffSubfield E a.2) (coe_mem_coeffSubfield E b.2)

variable (k p) in
/-- The power series `f_j = ∑ₙ t_{⟨j, n⟩} xⁿ`, whose coefficients are disjoint parts of the
`p`-independent sequence `outsideSeq`. -/
noncomputable def indepSeries (j : ℕ) : k⟦X⟧ := mk fun n => outsideSeq k p (Nat.pair j n)

variable (k p) in
/-- The subfield `k^p(t_{⟨j, n⟩} : j < m)` of `k` generated by the coefficients of the `f_j`,
`j < m`. -/
noncomputable def indepField (m : ℕ) : IntermediateField (pthPowerSubfield k p) k :=
  IntermediateField.adjoin (pthPowerSubfield k p) (outsideSeq k p '' {i | (Nat.unpair i).1 < m})

omit [Fact p.Prime] in
/-- For `j < m`, the series `f_j` lies in `coeffSubfield k p (indepField k p m)`. -/
theorem coe_indepSeries_mem {j m : ℕ} (hj : j < m) :
    (indepSeries k p j : LaurentSeries k) ∈ coeffSubfield k p (indepField k p m) := by
  refine ⟨⊥, inferInstance, fun n => ?_⟩
  rw [PowerSeries.coeff_coe]
  split_ifs
  · exact zero_mem _
  · refine (le_sup_left : indepField k p m ≤ _) (IntermediateField.subset_adjoin _ _ ?_)
    rw [indepSeries, coeff_mk]
    exact ⟨_, by rwa [Set.mem_ofPred_eq, Nat.unpair_pair], rfl⟩

/-- `f_m` does not lie in `coeffSubfield k p (indepField k p m)`: its coefficients would lie in an
extension of `k^p(t_{⟨j, n⟩} : j < m)` of finite degree, which the `p`-independent elements
`t_{⟨m, 0⟩}, t_{⟨m, 1⟩}, …` rule out. -/
theorem coe_indepSeries_not_mem (hk : ¬ FiniteDimensional (pthPowerSubfield k p) k) (m : ℕ) :
    (indepSeries k p m : LaurentSeries k) ∉ coeffSubfield k p (indepField k p m) := by
  rintro ⟨K, hK, hc⟩
  set B := indepField k p m
  set t := outsideSeq k p
  obtain ⟨U, hU⟩ := IntermediateField.fg_of_fg_toSubalgebra K
    (Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).mpr hK))
  have := finiteDimensional_adjoin_of_pow_mem (exists_algebraMap_eq_pow B) (U : Set k)
  refine not_forall_not_mem_adjoin_image (IntermediateField.adjoin B (U : Set k))
    (fun r => t (Nat.pair m r)) (fun r => ?_) fun r hr => ?_
  · have h := hc r
    rw [LaurentSeries.coeff_coe_powerSeries, indepSeries, coeff_mk] at h
    rw [mem_adjoin_iff_mem_adjoin_union, IntermediateField.adjoin_union,
      IntermediateField.adjoin_self, hU]
    exact h
  · rw [mem_adjoin_iff_mem_adjoin_union] at hr
    refine outsideSeq_not_mem_adjoin_ne hk (Nat.pair m r)
      (IntermediateField.adjoin_le_iff.mpr ?_ hr)
    rintro _ (hx | ⟨r', hr', rfl⟩)
    · refine (IntermediateField.adjoin.mono _ _ _ (Set.image_mono fun i hi => ?_) : B ≤ _) hx
      rintro rfl
      rw [Set.mem_ofPred_eq, Nat.unpair_pair] at hi
      exact lt_irrefl _ hi
    · refine IntermediateField.subset_adjoin _ _ ⟨_, fun h => ?_, rfl⟩
      exact (Nat.ne_of_lt hr') (Nat.pair_eq_pair.mp h).2

/-- **Stacks 00PB: `k((x))` has infinite degree over the fraction field of `A`**, when
`[k : k^p] = ∞`. The series `f_j = ∑ₙ t_{⟨j, n⟩} xⁿ` built from a `p`-independent sequence
`(tᵢ)` in `k` satisfy `f_m ∉ Frac(A)(f_0, …, f_{m-1})`. -/
@[stacks 00PB "The extension `k((x))` of the fraction field of `A` has infinite degree when
`[k : k^p] = ∞`."]
theorem not_finiteDimensional_laurentSeries
    (hk : ¬ FiniteDimensional (pthPowerSubfield k p) k) :
    letI := (fractionRingToLaurentSeries (k := k) (p := p)).toAlgebra
    ¬ FiniteDimensional (FractionRing (finiteCoeffSubring k p)) (LaurentSeries k) := by
  let := (fractionRingToLaurentSeries (k := k) (p := p)).toAlgebra
  intro hfin
  have : FiniteDimensional (FractionRing (finiteCoeffSubring k p))
      (⊤ : IntermediateField (FractionRing (finiteCoeffSubring k p)) (LaurentSeries k)) :=
    IntermediateField.topEquiv.symm.toLinearEquiv.finiteDimensional
  refine not_forall_not_mem_adjoin_image (K := FractionRing (finiteCoeffSubring k p)) ⊤
    (fun m => (indepSeries k p m : LaurentSeries k))
    (fun _ => trivial) fun m hm => coe_indepSeries_not_mem hk m ?_
  have hle : (IntermediateField.adjoin (FractionRing (finiteCoeffSubring k p))
      ((fun m => (indepSeries k p m : LaurentSeries k)) '' Set.Iio m)).toSubfield ≤
      coeffSubfield k p (indepField k p m) := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨q, rfl⟩
      exact fieldRange_le_coeffSubfield _ ⟨q, rfl⟩
    · rintro _ ⟨j, hj, rfl⟩
      exact coe_indepSeries_mem hj
  exact hle hm

end Degree

end PowerSeries
