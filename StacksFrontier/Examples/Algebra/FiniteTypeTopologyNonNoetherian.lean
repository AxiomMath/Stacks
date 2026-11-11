module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs

/-!
# A non-Noetherian local map with no quasi-finite quotients

Let `A → B` be a local map of local domains, essentially of finite type, with finite residue
field extension. If `A` is Noetherian and some prime of `B` does not lie over `m_A`, then some
quotient of `B` by a nonmaximal prime is a localization of a quasi-finite `A`-algebra
(Stacks 05GT). This file gives the example of Stacks 05JI showing that this fails without the
Noetherian hypothesis.

Let `k` be a field and `K` a field containing `k[y]`. Following Stacks, set
`A = k + x K[[x]]`, `C = k[y] + x K[[x]] = A[y]` and `B = k[y]_{(y)} + x K[[x]]`, the
localization of `C` at the maximal ideal `yC + x K[[x]]`. Stacks takes `K = k((y))`; we take
for `K` the fraction field of `k[y]_{(y)}`, which changes nothing in the argument. The ring `A`
is a local domain which is not Noetherian (its maximal ideal `x K[[x]]` is not finitely
generated), and `(0) ⊂ B` lies over `(0) ≠ m_A`. A nonzero prime of `B` contains `x K[[x]]`, so
the primes of `B` are `(0)`, `x K[[x]]` and `m_B`. If `q ≠ m_B` then `q ⊆ x K[[x]]`, so `B/q`
maps onto `k[y]_{(y)}`, whose two primes `(0) ⊂ (y)` both lie over `m_A`; this is impossible for
a localization of a quasi-finite `A`-algebra, whose fibres are discrete.

## Main results

* `Stacks.Examples.exists_localHom_not_isNoetherianRing_no_quasiFinite_quotient`: Stacks 05JI,
  with the witness of Stacks: `A` is not Noetherian and some prime of `B` does not lie over `m_A`.

## Implementation notes

As in the definition of essential finite type, a localization of a quasi-finite ring map is
expressed by an intermediate finite-type algebra, a submonoid, and an `IsLocalization` instance.
The separate finite-type condition is necessary because Mathlib's `Algebra.QuasiFinite` only
requires finite fibres.

## References

* [Stacks Project, Tag 05JI](https://stacks.math.columbia.edu/tag/05JI)
* [Stacks Project, Tag 05GT](https://stacks.math.columbia.edu/tag/05GT)
-/

@[expose] public section

universe u

namespace Stacks.Examples

noncomputable section

section OriginLocalization

variable (k : Type u) [Field k]

/-- The ideal `(X)` of `k[X]`. -/
private def originIdeal : Ideal (Polynomial k) :=
  RingHom.ker (Polynomial.evalRingHom (0 : k))

private lemma originIdeal_isMaximal : (originIdeal k).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro x
  exact ⟨Polynomial.C x, by simp⟩

private instance instIsPrimeOriginIdealField : (originIdeal k).IsPrime :=
  RingHom.ker_isPrime (Polynomial.evalRingHom (0 : k))

/-- The local ring `k[X]_{(X)}`. -/
private abbrev localizedAtOrigin : Type u := Localization.AtPrime (originIdeal k)

private lemma localizedAtOrigin_maximalIdeal_ne_bot :
    IsLocalRing.maximalIdeal (localizedAtOrigin k) ≠ (⊥ : Ideal (localizedAtOrigin k)) := by
  intro h
  have hx : algebraMap (Polynomial k) (localizedAtOrigin k) Polynomial.X ∈
      IsLocalRing.maximalIdeal (localizedAtOrigin k) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (localizedAtOrigin k) (originIdeal k)
      Polynomial.X).2 (by simp [originIdeal])
  rw [h, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero
    ((FaithfulSMul.algebraMap_injective (Polynomial k) (localizedAtOrigin k))
      (by rw [map_zero]; exact hx))

private lemma residue_algebraMap_surjective :
    Function.Surjective
      (algebraMap k (IsLocalRing.ResidueField (localizedAtOrigin k))) := by
  intro z
  let : (originIdeal k).IsMaximal := originIdeal_isMaximal k
  obtain ⟨r, rfl⟩ := (originIdeal k).algebraMap_residueField_surjective z
  refine ⟨Polynomial.eval 0 r, ?_⟩
  have hzero := (Ideal.algebraMap_residueField_eq_zero (I := originIdeal k)).2
    (show r - Polynomial.C (Polynomial.eval 0 r) ∈ originIdeal k by
      change Polynomial.evalRingHom 0 (r - Polynomial.C (Polynomial.eval 0 r)) = 0
      simp)
  rw [map_sub, sub_eq_zero] at hzero
  exact (IsScalarTower.algebraMap_apply k (Polynomial k)
    (IsLocalRing.ResidueField (localizedAtOrigin k)) _).trans hzero.symm

end OriginLocalization

/-! ### Power series with constant coefficient in a subring -/

section ConstCoeffSubring

open PowerSeries

variable {K D : Type*} [Field K] [CommRing D]

/-- The power series over `K` whose constant coefficient lies in the image of `ι : D →+* K`. -/
private def constCoeffSubring (ι : D →+* K) : Subring K⟦X⟧ :=
  ι.range.comap constantCoeff

private lemma mem_constCoeffSubring {ι : D →+* K} {f : K⟦X⟧} :
    f ∈ constCoeffSubring ι ↔ ∃ d, ι d = constantCoeff f := by
  simp only [constCoeffSubring, Subring.mem_comap, RingHom.mem_range]

private lemma mem_constCoeffSubring_of_constantCoeff_eq_zero {ι : D →+* K} {f : K⟦X⟧}
    (hf : constantCoeff f = 0) : f ∈ constCoeffSubring ι :=
  mem_constCoeffSubring.2 ⟨0, by rw [map_zero, hf]⟩

private lemma constCoeffSubring_mono {D' : Type*} [CommRing D'] {ι : D →+* K} {ι' : D' →+* K}
    (h : ∀ d, ∃ d', ι' d' = ι d) : constCoeffSubring ι ≤ constCoeffSubring ι' := by
  intro f hf
  obtain ⟨d, hd⟩ := mem_constCoeffSubring.1 hf
  obtain ⟨d', hd'⟩ := h d
  exact mem_constCoeffSubring.2 ⟨d', hd'.trans hd⟩

/-- The constant coefficient of an element of `constCoeffSubring ι`, as an element of `D`. -/
private noncomputable def constCoeffHom {ι : D →+* K} (hι : Function.Injective ι) :
    constCoeffSubring ι →+* D :=
  ((RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun _ _ h => hι (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩).symm :
      ι.range →+* D).comp
    (constantCoeff.restrict (constCoeffSubring ι) ι.range fun _ hx => hx)

private lemma apply_constCoeffHom {ι : D →+* K} (hι : Function.Injective ι)
    (f : constCoeffSubring ι) : ι (constCoeffHom hι f) = constantCoeff (f : K⟦X⟧) :=
  congrArg Subtype.val ((RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun _ _ h => hι (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩).apply_symm_apply
    ⟨constantCoeff (f : K⟦X⟧), f.2⟩)

private lemma constCoeffHom_eq_zero_iff {ι : D →+* K} (hι : Function.Injective ι)
    (f : constCoeffSubring ι) : constCoeffHom hι f = 0 ↔ constantCoeff (f : K⟦X⟧) = 0 := by
  rw [← apply_constCoeffHom hι, map_eq_zero_iff ι hι]

/-- The constant power series with value in the image of `ι`. -/
private def constSection (ι : D →+* K) : D →+* constCoeffSubring ι :=
  ((C).comp ι).codRestrict _ fun d => mem_constCoeffSubring.2 ⟨d, by simp⟩

private lemma constCoeffHom_constSection {ι : D →+* K} (hι : Function.Injective ι) (d : D) :
    constCoeffHom hι (constSection ι d) = d :=
  hι (by rw [apply_constCoeffHom hι]; simp [constSection])

private lemma constCoeffHom_surjective {ι : D →+* K} (hι : Function.Injective ι) :
    Function.Surjective (constCoeffHom hι) :=
  fun d => ⟨constSection ι d, constCoeffHom_constSection hι d⟩

private lemma isUnit_constCoeffSubring_iff {ι : D →+* K} (hι : Function.Injective ι)
    (f : constCoeffSubring ι) : IsUnit f ↔ IsUnit (constCoeffHom hι f) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  obtain ⟨u, hu⟩ := h
  have h0 : constantCoeff (f : K⟦X⟧) ≠ 0 := by
    rw [← apply_constCoeffHom hι, ← hu]
    exact (u.isUnit.map ι).ne_zero
  have hinv : (f : K⟦X⟧)⁻¹ ∈ constCoeffSubring ι := by
    refine mem_constCoeffSubring.2 ⟨↑u⁻¹, ?_⟩
    rw [PowerSeries.constantCoeff_inv, ← apply_constCoeffHom hι, ← hu]
    exact map_units_inv ι u
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (PowerSeries.mul_inv_cancel _ h0)⟩

private lemma isLocalRing_constCoeffSubring {ι : D →+* K} (hι : Function.Injective ι)
    [IsLocalRing D] : IsLocalRing (constCoeffSubring ι) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => by
    simp only [isUnit_constCoeffSubring_iff hι, map_sub, map_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

/-- A nonzero prime of `constCoeffSubring ι` contains every power series with zero constant
coefficient. -/
private lemma ker_constCoeffHom_le {ι : D →+* K} (hι : Function.Injective ι)
    (q : Ideal (constCoeffSubring ι)) [hq : q.IsPrime] (hq0 : q ≠ ⊥) :
    RingHom.ker (constCoeffHom hι) ≤ q := by
  obtain ⟨g, hgq, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  intro h hh
  rw [RingHom.mem_ker, constCoeffHom_eq_zero_iff] at hh
  obtain ⟨h', hh'⟩ := PowerSeries.X_dvd_iff.2 hh
  set n := (g : K⟦X⟧).order.toNat
  set u := divXPowOrder (g : K⟦X⟧)
  have hu : constantCoeff u ≠ 0 := by
    rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]
    exact fun h => hg0 (Subtype.ext h)
  have hg : (g : K⟦X⟧) = X ^ n * u := X_pow_order_mul_divXPowOrder.symm
  have hw : X * u⁻¹ * h' ^ (n + 1) ∈ constCoeffSubring ι :=
    mem_constCoeffSubring_of_constantCoeff_eq_zero (by simp)
  have key : h ^ (n + 1) = g * ⟨_, hw⟩ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul]
    rw [hh', hg]
    linear_combination (-(X ^ (n + 1) * h' ^ (n + 1))) * PowerSeries.mul_inv_cancel u hu
  exact hq.mem_of_pow_mem (n + 1) (key ▸ q.mul_mem_right _ hgq)

/-- If every nonzero prime of `D` is maximal, then every prime of `constCoeffSubring ι` other than
the maximal ideal consists of power series with zero constant coefficient. -/
private lemma le_ker_constCoeffHom {ι : D →+* K} (hι : Function.Injective ι) [IsLocalRing D]
    [Ring.DimensionLEOne D] (q : Ideal (constCoeffSubring ι)) [q.IsPrime]
    (hq : q ≠ @IsLocalRing.maximalIdeal _ _ (isLocalRing_constCoeffSubring hι)) :
    q ≤ RingHom.ker (constCoeffHom hι) := by
  let := isLocalRing_constCoeffSubring hι
  by_cases h0 : q = ⊥
  · rw [h0]
    exact bot_le
  have hker := ker_constCoeffHom_le hι q h0
  have hsurj := constCoeffHom_surjective hι
  have : (q.map (constCoeffHom hι)).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  by_cases hmap : q.map (constCoeffHom hι) = ⊥
  · intro x hx
    rw [RingHom.mem_ker, ← Ideal.mem_bot, ← hmap]
    exact Ideal.mem_map_of_mem _ hx
  · exfalso
    apply hq
    have hmax : (q.map (constCoeffHom hι)).IsMaximal := Ideal.IsPrime.isMaximal ‹_› hmap
    have hq' : q = (q.map (constCoeffHom hι)).comap (constCoeffHom hι) := by
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hker]
    rw [hq']
    have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := q.map (constCoeffHom hι))
    exact IsLocalRing.eq_maximalIdeal this

end ConstCoeffSubring

/-! ### The Stacks example -/

section StacksExample

open PowerSeries

variable (k : Type u) [Field k]

/-- The field `K`, the fraction field of `k[y]_{(y)}`. -/
private abbrev fractionField : Type u := FractionRing (localizedAtOrigin k)

private lemma injective_algebraMap_field :
    Function.Injective (algebraMap k (fractionField k)) :=
  (algebraMap k (fractionField k)).injective

private lemma injective_algebraMap_polynomial :
    Function.Injective (algebraMap (Polynomial k) (fractionField k)) := by
  rw [IsScalarTower.algebraMap_eq (Polynomial k) (localizedAtOrigin k) (fractionField k)]
  exact (IsFractionRing.injective (localizedAtOrigin k) (fractionField k)).comp
    (FaithfulSMul.algebraMap_injective _ _)

private lemma injective_algebraMap_localizedAtOrigin :
    Function.Injective (algebraMap (localizedAtOrigin k) (fractionField k)) :=
  IsFractionRing.injective _ _

/-- The ring `A = k + x K[[x]]`. -/
private abbrev ringA : Subring (PowerSeries (fractionField k)) :=
  constCoeffSubring (algebraMap k (fractionField k))

/-- The ring `C = k[y] + x K[[x]]`. -/
private abbrev ringC : Subring (PowerSeries (fractionField k)) :=
  constCoeffSubring (algebraMap (Polynomial k) (fractionField k))

/-- The ring `B = k[y]_{(y)} + x K[[x]]`. -/
private abbrev ringB : Subring (PowerSeries (fractionField k)) :=
  constCoeffSubring (algebraMap (localizedAtOrigin k) (fractionField k))

/-- The constant coefficient on `A`, with values in `k`. -/
private abbrev constCoeffA : ringA k →+* k := constCoeffHom (injective_algebraMap_field k)

/-- The constant coefficient on `C`, with values in `k[y]`. -/
private abbrev constCoeffC : ringC k →+* Polynomial k :=
  constCoeffHom (injective_algebraMap_polynomial k)

/-- The constant coefficient on `B`, with values in `k[y]_{(y)}`. -/
private abbrev constCoeffB : ringB k →+* localizedAtOrigin k :=
  constCoeffHom (injective_algebraMap_localizedAtOrigin k)

private lemma ringA_le_ringC : ringA k ≤ ringC k :=
  constCoeffSubring_mono fun a => ⟨algebraMap k (Polynomial k) a,
    (IsScalarTower.algebraMap_apply k (Polynomial k) (fractionField k) a).symm⟩

private lemma ringC_le_ringB : ringC k ≤ ringB k :=
  constCoeffSubring_mono fun p => ⟨algebraMap (Polynomial k) (localizedAtOrigin k) p,
    (IsScalarTower.algebraMap_apply (Polynomial k) (localizedAtOrigin k) (fractionField k)
      p).symm⟩

private lemma ringA_le_ringB : ringA k ≤ ringB k := (ringA_le_ringC k).trans (ringC_le_ringB k)

private instance instIsLocalRingRingA : IsLocalRing (ringA k) :=
  isLocalRing_constCoeffSubring (injective_algebraMap_field k)

private instance instIsLocalRingRingB : IsLocalRing (ringB k) :=
  isLocalRing_constCoeffSubring (injective_algebraMap_localizedAtOrigin k)

private instance instDimensionLEOneLocalizedAtOrigin : Ring.DimensionLEOne (localizedAtOrigin k) :=
  Ring.DimensionLEOne.localization (localizedAtOrigin k) (M := (originIdeal k).primeCompl)
    (originIdeal k).primeCompl_le_nonZeroDivisors

private instance instAlgebraRingARingC : Algebra (ringA k) (ringC k) :=
  (Subring.inclusion (ringA_le_ringC k)).toAlgebra

private instance instAlgebraRingCRingB : Algebra (ringC k) (ringB k) :=
  (Subring.inclusion (ringC_le_ringB k)).toAlgebra

private lemma constCoeffB_inclusion_ringA (a : ringA k) :
    constCoeffB k (Subring.inclusion (ringA_le_ringB k) a) =
      algebraMap k (localizedAtOrigin k) (constCoeffA k a) := by
  apply injective_algebraMap_localizedAtOrigin k
  rw [apply_constCoeffHom, ← IsScalarTower.algebraMap_apply k (localizedAtOrigin k)
    (fractionField k), apply_constCoeffHom]
  rfl

private lemma constCoeffB_algebraMap_ringC (c : ringC k) :
    constCoeffB k (algebraMap (ringC k) (ringB k) c) =
      algebraMap (Polynomial k) (localizedAtOrigin k) (constCoeffC k c) := by
  apply injective_algebraMap_localizedAtOrigin k
  rw [apply_constCoeffHom, ← IsScalarTower.algebraMap_apply (Polynomial k)
    (localizedAtOrigin k) (fractionField k), apply_constCoeffHom]
  rfl

private lemma mem_maximalIdeal_ringA_iff (a : ringA k) :
    a ∈ IsLocalRing.maximalIdeal (ringA k) ↔ constCoeffA k a = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_constCoeffSubring_iff (injective_algebraMap_field k), isUnit_iff_ne_zero, not_not]

private lemma isLocalHom_inclusion : IsLocalHom (Subring.inclusion (ringA_le_ringB k)) :=
  ⟨fun a ha => by
    rw [isUnit_constCoeffSubring_iff (injective_algebraMap_localizedAtOrigin k)] at ha
    change IsUnit (constCoeffB k (Subring.inclusion (ringA_le_ringB k) a)) at ha
    rw [constCoeffB_inclusion_ringA] at ha
    rw [isUnit_constCoeffSubring_iff (injective_algebraMap_field k), isUnit_iff_ne_zero]
    intro h
    change constCoeffA k a = 0 at h
    rw [h, map_zero] at ha
    exact not_isUnit_zero ha⟩

private lemma constSection_mem_adjoin (p : Polynomial k) :
    constSection (algebraMap (Polynomial k) (fractionField k)) p ∈ Algebra.adjoin (ringA k)
      {constSection (algebraMap (Polynomial k) (fractionField k)) Polynomial.X} := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : constSection (algebraMap (Polynomial k) (fractionField k)) (Polynomial.C a) =
        algebraMap (ringA k) (ringC k) (constSection _ a) := by
      apply Subtype.ext
      change PowerSeries.C (algebraMap (Polynomial k) (fractionField k) (Polynomial.C a)) =
        PowerSeries.C (algebraMap k (fractionField k) a)
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (fractionField k) a,
        Polynomial.algebraMap_eq]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul]
    exact mul_mem h (Algebra.subset_adjoin rfl)

private instance instFiniteTypeRingARingC : Algebra.FiniteType (ringA k) (ringC k) := by
  classical
  refine ⟨⟨{constSection (algebraMap (Polynomial k) (fractionField k)) Polynomial.X},
    eq_top_iff.2 fun c _ => ?_⟩⟩
  rw [Finset.coe_singleton]
  have hc₀ : constCoeffC k (constSection (algebraMap (Polynomial k) (fractionField k))
      (constCoeffC k c)) = constCoeffC k c :=
    constCoeffHom_constSection _ _
  have hx : ((c - constSection _ (constCoeffC k c) : ringC k) :
      PowerSeries (fractionField k)) ∈ ringA k :=
    mem_constCoeffSubring_of_constantCoeff_eq_zero (by
      rw [← constCoeffHom_eq_zero_iff (injective_algebraMap_polynomial k)]
      change constCoeffC k (c - _) = 0
      rw [map_sub, hc₀, sub_self])
  have hc : c = constSection _ (constCoeffC k c) + algebraMap (ringA k) (ringC k) ⟨_, hx⟩ := by
    rw [show algebraMap (ringA k) (ringC k) ⟨_, hx⟩ = c - constSection _ (constCoeffC k c)
      from rfl, add_sub_cancel]
  rw [hc]
  exact add_mem (constSection_mem_adjoin k _) (Subalgebra.algebraMap_mem _ _)

/-- The elements of `C` that become units in `B`. -/
private def submonoidC : Submonoid (ringC k) :=
  (IsUnit.submonoid (ringB k)).comap (algebraMap (ringC k) (ringB k))

private lemma isLocalization_ringB : IsLocalization (submonoidC k) (ringB k) := by
  rw [isLocalization_iff]
  refine ⟨fun y => y.2, fun z => ?_, fun {x y} h =>
    ⟨1, by rw [Subring.inclusion_injective (ringC_le_ringB k) h]⟩⟩
  obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (originIdeal k).primeCompl (constCoeffB k z)
  have hmem : (z : PowerSeries (fractionField k)) *
      (constSection (algebraMap (Polynomial k) (fractionField k)) (s : Polynomial k) :
        PowerSeries (fractionField k)) ∈ ringC k := by
    refine mem_constCoeffSubring.2 ⟨p, ?_⟩
    change _ = constantCoeff ((z : PowerSeries (fractionField k)) *
      PowerSeries.C (algebraMap (Polynomial k) (fractionField k) (s : Polynomial k)))
    rw [map_mul, constantCoeff_C,
      ← apply_constCoeffHom (injective_algebraMap_localizedAtOrigin k) z,
      IsScalarTower.algebraMap_apply (Polynomial k) (localizedAtOrigin k) (fractionField k),
      IsScalarTower.algebraMap_apply (Polynomial k) (localizedAtOrigin k) (fractionField k)
        (s : Polynomial k), ← map_mul]
    exact congrArg _ hps.symm
  refine ⟨⟨⟨_, hmem⟩, ⟨constSection _ (s : Polynomial k), ?_⟩⟩, Subtype.ext rfl⟩
  change IsUnit (algebraMap (ringC k) (ringB k) (constSection _ (s : Polynomial k)))
  rw [isUnit_constCoeffSubring_iff (injective_algebraMap_localizedAtOrigin k)]
  change IsUnit (constCoeffB k (algebraMap (ringC k) (ringB k) _))
  rw [constCoeffB_algebraMap_ringC]
  rw [constCoeffHom_constSection]
  exact IsLocalization.map_units (localizedAtOrigin k) s

/-- `A = k + x K[[x]]` is not Noetherian: its maximal ideal `x K[[x]]` is not finitely
generated, since its image under the coefficient of `x` is all of `K`, which is infinite
dimensional over `k`. -/
private lemma not_isNoetherianRing_ringA : ¬ IsNoetherianRing (ringA k) := by
  classical
  intro hN
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (IsLocalRing.maximalIdeal (ringA k))
  let φ : ringA k → fractionField k := fun g => coeff 1 (g : PowerSeries (fractionField k))
  have key : ∀ a ∈ Submodule.span (ringA k) (s : Set (ringA k)),
      a ∈ IsLocalRing.maximalIdeal (ringA k) ∧ φ a ∈ Submodule.span k (φ '' s) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg =>
      exact ⟨hs ▸ Submodule.subset_span hg, Submodule.subset_span ⟨g, hg, rfl⟩⟩
    | zero => exact ⟨zero_mem _, by simp [φ]⟩
    | add x y _ _ hx hy =>
      refine ⟨add_mem hx.1 hy.1, ?_⟩
      have : φ (x + y) = φ x + φ y := by simp [φ]
      rw [this]
      exact add_mem hx.2 hy.2
    | smul r x _ hx =>
      refine ⟨Ideal.mul_mem_left _ r hx.1, ?_⟩
      have hx0 : constantCoeff (x : PowerSeries (fractionField k)) = 0 := by
        rw [← constCoeffHom_eq_zero_iff (injective_algebraMap_field k)]
        exact (mem_maximalIdeal_ringA_iff k x).1 hx.1
      have : φ (r • x) = constCoeffA k r • φ x := by
        rw [smul_eq_mul, Algebra.smul_def, apply_constCoeffHom]
        change coeff 1 ((r : PowerSeries (fractionField k)) *
          (x : PowerSeries (fractionField k))) = _
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
        simp [coeff_zero_eq_constantCoeff_apply, hx0, φ]
      rw [this]
      exact Submodule.smul_mem _ _ hx.2
  have htop : Submodule.span k (φ '' s) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : X * PowerSeries.C z ∈ ringA k :=
      mem_constCoeffSubring_of_constantCoeff_eq_zero (by simp)
    have hmax : (⟨_, hz⟩ : ringA k) ∈ Submodule.span (ringA k) (s : Set (ringA k)) := by
      rw [hs, mem_maximalIdeal_ringA_iff, constCoeffHom_eq_zero_iff]
      simp
    simpa [φ, coeff_succ_X_mul] using (key _ hmax).2
  have : Module.Finite k (fractionField k) :=
    ⟨⟨s.image φ, by rw [Finset.coe_image]; exact htop⟩⟩
  have : Module.Finite k (Polynomial k) :=
    Module.Finite.of_injective
      (IsScalarTower.toAlgHom k (Polynomial k) (fractionField k)).toLinearMap
      (injective_algebraMap_polynomial k)
  have : Algebra.IsIntegral k (Polynomial k) := Algebra.IsIntegral.of_finite k _
  exact Polynomial.transcendental_X k
    (Algebra.IsIntegral.isIntegral (Polynomial.X : Polynomial k)).isAlgebraic

private lemma residueField_map_surjective :
    letI : IsLocalHom (Subring.inclusion (ringA_le_ringB k)) := isLocalHom_inclusion k
    Function.Surjective
      (IsLocalRing.ResidueField.map (Subring.inclusion (ringA_le_ringB k))) := by
  let : IsLocalHom (Subring.inclusion (ringA_le_ringB k)) := isLocalHom_inclusion k
  intro z
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨c, hc⟩ := residue_algebraMap_surjective k
    (IsLocalRing.residue (localizedAtOrigin k) (constCoeffB k b))
  refine ⟨IsLocalRing.residue _ (constSection _ c), ?_⟩
  have hmem : constCoeffB k (Subring.inclusion (ringA_le_ringB k) (constSection _ c) - b) ∈
      IsLocalRing.maximalIdeal (localizedAtOrigin k) := by
    rw [map_sub, constCoeffB_inclusion_ringA]
    change algebraMap k (localizedAtOrigin k) (constCoeffA k (constSection _ c)) - _ ∈ _
    rw [constCoeffHom_constSection, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero,
      ← hc, IsScalarTower.algebraMap_apply k (localizedAtOrigin k)
        (IsLocalRing.ResidueField (localizedAtOrigin k)), IsLocalRing.ResidueField.algebraMap_eq]
  have hmem' : Subring.inclusion (ringA_le_ringB k) (constSection _ c) - b ∈
      IsLocalRing.maximalIdeal (ringB k) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_constCoeffSubring_iff (injective_algebraMap_localizedAtOrigin k)]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact hmem
  rw [IsLocalRing.ResidueField.map_residue]
  exact Ideal.Quotient.eq.2 hmem'

private lemma under_bot_eq_under_maximalIdeal :
    letI : Algebra (ringA k) (localizedAtOrigin k) :=
      ((constCoeffB k).comp (Subring.inclusion (ringA_le_ringB k))).toAlgebra
    (⊥ : Ideal (localizedAtOrigin k)).under (ringA k) =
      (IsLocalRing.maximalIdeal (localizedAtOrigin k)).under (ringA k) := by
  let : Algebra (ringA k) (localizedAtOrigin k) :=
    ((constCoeffB k).comp (Subring.inclusion (ringA_le_ringB k))).toAlgebra
  refine le_antisymm (Ideal.comap_mono bot_le) ?_
  refine (IsLocalRing.le_maximalIdeal
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)).trans ?_
  intro a ha
  rw [mem_maximalIdeal_ringA_iff] at ha
  change constCoeffB k (Subring.inclusion (ringA_le_ringB k) a) ∈ (⊥ : Ideal (localizedAtOrigin k))
  rw [Ideal.mem_bot, constCoeffB_inclusion_ringA, ha, map_zero]

private lemma no_quasiFinite_quotient (q : PrimeSpectrum (ringB k))
    (hq : q.asIdeal ≠ IsLocalRing.maximalIdeal (ringB k)) :
    letI := (Subring.inclusion (ringA_le_ringB k)).toAlgebra
    ¬ ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (ringA k) C)
      (_ : Algebra.FiniteType (ringA k) C) (_ : Algebra.QuasiFinite (ringA k) C)
      (M : Submonoid C) (_ : Algebra C (ringB k ⧸ q.asIdeal)),
      IsScalarTower (ringA k) C (ringB k ⧸ q.asIdeal) ∧
        IsLocalization M (ringB k ⧸ q.asIdeal) := by
  let := (Subring.inclusion (ringA_le_ringB k)).toAlgebra
  rintro ⟨C, hC, hAC, hft, hqf, M, hCB, htower, hloc⟩
  let : CommRing C := hC
  let : Algebra (ringA k) C := hAC
  let : Algebra C (ringB k ⧸ q.asIdeal) := hCB
  have : Algebra.QuasiFinite (ringA k) C := hqf
  have : IsLocalization M (ringB k ⧸ q.asIdeal) := hloc
  have := htower
  have : Algebra.QuasiFinite (ringA k) (ringB k ⧸ q.asIdeal) :=
    Algebra.QuasiFinite.of_isLocalization M
  have hle : q.asIdeal ≤ RingHom.ker (constCoeffB k) :=
    le_ker_constCoeffHom (injective_algebraMap_localizedAtOrigin k) q.asIdeal hq
  let : Algebra (ringA k) (localizedAtOrigin k) :=
    ((constCoeffB k).comp (Subring.inclusion (ringA_le_ringB k))).toAlgebra
  let g : ringB k →ₐ[ringA k] localizedAtOrigin k :=
    { constCoeffB k with commutes' := fun _ => rfl }
  let g' := Ideal.Quotient.liftₐ q.asIdeal g fun b hb => hle hb
  have hg' : Function.Surjective g' := by
    intro d
    obtain ⟨b, rfl⟩ := constCoeffHom_surjective (injective_algebraMap_localizedAtOrigin k) d
    exact ⟨Ideal.Quotient.mk _ b, rfl⟩
  have := Algebra.QuasiFinite.of_surjective_algHom g' hg'
  exact localizedAtOrigin_maximalIdeal_ne_bot k
    (Algebra.QuasiFinite.eq_of_le_of_under_eq _ _ bot_le
      (under_bot_eq_under_maximalIdeal k)).symm

/-- The Stacks example for an arbitrary field `k`. -/
private lemma exists_localHom_not_isNoetherianRing_no_quasiFinite_quotient_aux
    (k : Type u) [Field k] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : IsDomain A) (_ : IsDomain B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (f : A →+* B) (hf : IsLocalHom f),
      IsEssentiallyOfFiniteType A B f ∧
      (letI : IsLocalHom f := hf
       letI := (IsLocalRing.ResidueField.map f).toAlgebra
       Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) ∧
      ¬ IsNoetherianRing A ∧
      (∃ q : PrimeSpectrum B, q.asIdeal.comap f ≠ IsLocalRing.maximalIdeal A) ∧
      (∀ q : PrimeSpectrum B, q.asIdeal ≠ IsLocalRing.maximalIdeal B →
        ¬ (letI := f.toAlgebra
           ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
             (_ : Algebra.FiniteType A C) (_ : Algebra.QuasiFinite A C)
             (M : Submonoid C) (_ : Algebra C (B ⧸ q.asIdeal)),
             IsScalarTower A C (B ⧸ q.asIdeal) ∧ IsLocalization M (B ⧸ q.asIdeal))) := by
  refine ⟨ringA k, ringB k, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Subring.inclusion (ringA_le_ringB k), isLocalHom_inclusion k,
    ?_, ?_, not_isNoetherianRing_ringA k, ?_, no_quasiFinite_quotient k⟩
  · unfold IsEssentiallyOfFiniteType
    let : Algebra (ringA k) (ringB k) := (Subring.inclusion (ringA_le_ringB k)).toAlgebra
    have htower : IsScalarTower (ringA k) (ringC k) (ringB k) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact ⟨ringC k, inferInstance, inferInstance, inferInstance, submonoidC k, inferInstance,
      htower, isLocalization_ringB k⟩
  · let : IsLocalHom (Subring.inclusion (ringA_le_ringB k)) := isLocalHom_inclusion k
    let := (IsLocalRing.ResidueField.map (Subring.inclusion (ringA_le_ringB k))).toAlgebra
    exact RingHom.Finite.of_surjective _ (residueField_map_surjective k)
  · refine ⟨⟨⊥, Ideal.isPrime_bot⟩, fun h => ?_⟩
    have hX : (X : PowerSeries (fractionField k)) ∈ ringA k :=
      mem_constCoeffSubring_of_constantCoeff_eq_zero constantCoeff_X
    have hmem : (⟨X, hX⟩ : ringA k) ∈ IsLocalRing.maximalIdeal (ringA k) := by
      rw [mem_maximalIdeal_ringA_iff, constCoeffHom_eq_zero_iff]
      exact constantCoeff_X
    rw [← h, Ideal.mem_comap, Ideal.mem_bot] at hmem
    exact X_ne_zero (congrArg Subtype.val hmem)

end StacksExample

/-- **Stacks 05JI.** There is a local homomorphism `f : A → B` of local domains, essentially of
finite type, with finite residue field extension, such that for every prime `q ≠ m_B` of `B`
the map `A → B/q` is not a localization of a quasi-finite ring map.

The witness is the one of Stacks: `A` is not Noetherian and some prime of `B` (namely `(0)`)
does not lie over `m_A`. So all hypotheses of Stacks 05GT except the Noetherian one hold, with
`V = Spec B`, while its conclusion fails. -/
@[stacks 05JI]
public theorem exists_localHom_not_isNoetherianRing_no_quasiFinite_quotient :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : IsDomain A) (_ : IsDomain B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (f : A →+* B) (hf : IsLocalHom f),
      IsEssentiallyOfFiniteType A B f ∧
      (letI : IsLocalHom f := hf
       letI := (IsLocalRing.ResidueField.map f).toAlgebra
       Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) ∧
      ¬ IsNoetherianRing A ∧
      (∃ q : PrimeSpectrum B, q.asIdeal.comap f ≠ IsLocalRing.maximalIdeal A) ∧
      (∀ q : PrimeSpectrum B, q.asIdeal ≠ IsLocalRing.maximalIdeal B →
        ¬ (letI := f.toAlgebra
           ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
             (_ : Algebra.FiniteType A C) (_ : Algebra.QuasiFinite A C)
             (M : Submonoid C) (_ : Algebra C (B ⧸ q.asIdeal)),
             IsScalarTower A C (B ⧸ q.asIdeal) ∧ IsLocalization M (B ⧸ q.asIdeal))) :=
  exists_localHom_not_isNoetherianRing_no_quasiFinite_quotient_aux (ULift.{u} ℚ)

end

end Stacks.Examples

end
