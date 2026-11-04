module

public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
import StacksFrontier.RingTheory.CohenMacaulay.SliceDimensionDrop
import StacksFrontier.RingTheory.Depth.FlatLocalDimension
import StacksFrontier.RingTheory.Dualizing.ArtinianGorensteinSocle
import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
import StacksFrontier.RingTheory.Dualizing.GorensteinRegularElement
import StacksFrontier.RingTheory.LocalRing.InfiniteResidueField
import StacksFrontier.RingTheory.LocalRing.SuperficialElement

/-!
# Two-dimensional Gorenstein local rings of minimal multiplicity

Let `(A, 𝔪, κ)` be a two-dimensional Gorenstein local ring whose Hilbert function is
`dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹ = n e + 1` for some `e` (equivalently `ℓ(A/𝔪ⁿ⁺¹) = ℓ(A/𝔪ⁿ) + n e + 1`; the
multiplicity is then `e` and the embedding dimension `e + 1`). Then `e ≤ 2`, so the embedding
dimension is at most three. This is the commutative-algebra input that makes a Gorenstein rational
surface singularity a hypersurface singularity.

## Main results

* `Dualizing.IsGorensteinLocalRing.le_two_of_length_quotient_pow_succ_of_infinite`: the statement
  for an infinite residue field.
* `Dualizing.IsGorensteinLocalRing.le_two_of_length_quotient_pow_succ`: the statement in general.

## The argument

With `κ` infinite choose a superficial element `a ∈ 𝔪` outside the minimal primes
(`IsLocalRing.exists_mem_maximalIdeal_forall_mul_mem_pow_imp_mem_pow`). As `A` is Cohen–Macaulay,
`a` is a nonzerodivisor, `(𝔪ⁿ⁺¹ : a) = 𝔪ⁿ` for large `n`, and `B = A/aA` is a one-dimensional
Gorenstein local ring with `ℓ(B/𝔪_Bⁿ⁺¹) = ℓ(A/𝔪ⁿ⁺¹) − ℓ(A/𝔪ⁿ) = n e + 1` for large `n`. Doing
the same in `B` with an element `b`, the Artinian Gorenstein ring `C = B/bB` has
`ℓ(C/𝔪_Cⁿ⁺¹) = e` for large `n`, hence `ℓ(C) = e`. On the other hand each of the two slices lowers
`ℓ(· / 𝔪²)` by at most one, and `ℓ(A/𝔪²) = e + 2`, so `ℓ(C/𝔪_C²) ≥ e = ℓ(C)`: thus `𝔪_C² = 0`. A
zero-dimensional Gorenstein local ring has one-dimensional socle, so `𝔪_C` is principal and
`e = ℓ(C) ≤ 2`.

For a finite residue field one passes to `A(t) = A[t]_{𝔪A[t]}`, which is flat with closed fibre a
field, so Gorenstein, of the same dimension and with the same lengths `ℓ(· / 𝔪ⁿ)`.
-/

@[expose] public section

open IsLocalRing

universe u

namespace Dualizing

section Helpers

variable {R : Type u} [CommRing R]

/-- The length of a quotient of a quotient ring, over the quotient ring, is the length over the
original ring of the quotient by the sum of the ideals. -/
private theorem length_quotient_map_mk_eq (I J : Ideal R) :
    Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) =
      Module.length R (R ⧸ (I ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := R) (R := R ⧸ I) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv.length_eq

/-- A regular element (for the scalar action) of a commutative ring is a nonzerodivisor. -/
private theorem mem_nonZeroDivisors_of_isSMulRegular {a : R} (h : IsSMulRegular R a) :
    a ∈ nonZeroDivisors R :=
  ((Commute.isRegular_iff fun b => Commute.all a b).mpr h).mem_nonZeroDivisors

variable [IsLocalRing R]

/-- Lengths of `B/𝔪_Bᵏ` for a quotient `B = R/I` of a local ring, read over `R`. -/
private theorem length_quotient_maximalIdeal_pow_eq (I : Ideal R) [IsLocalRing (R ⧸ I)] (k : ℕ) :
    Module.length (R ⧸ I) ((R ⧸ I) ⧸ maximalIdeal (R ⧸ I) ^ k) =
      Module.length R (R ⧸ (I ⊔ maximalIdeal R ^ k)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact length_quotient_map_mk_eq I _

/-- The residue field of a quotient of a local ring with infinite residue field is infinite. -/
private theorem infinite_residueField_quotient [Infinite (ResidueField R)] (I : Ideal R)
    [IsLocalRing (R ⧸ I)] : Infinite (ResidueField (R ⧸ I)) := by
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact Infinite.of_injective _ (ResidueField.map (Ideal.Quotient.mk I)).injective

/-- In a local ring of nonzero dimension no minimal prime contains the maximal ideal. -/
private theorem not_maximalIdeal_le_of_mem_minimalPrimes (hdim : ringKrullDim R ≠ 0)
    {P : Ideal R} (hP : P ∈ minimalPrimes R) : ¬ maximalIdeal R ≤ P := by
  intro hle
  have hPm : maximalIdeal R = P :=
    (maximalIdeal.isMaximal R).eq_of_le hP.1.1.ne_top hle
  have h0 : (maximalIdeal R).height = 0 := Ideal.height_eq_zero_iff.mpr (hPm ▸ hP)
  apply hdim
  rw [← maximalIdeal_height_eq_ringKrullDim, h0]
  rfl

/-- `X + a = a + b` in `ℕ∞` with `a, b` finite forces `X = b`. -/
private theorem enat_eq_of_add_eq {X : ℕ∞} {a b : ℕ} (h : X + a = ((a + b : ℕ) : ℕ∞)) :
    X = b := by
  induction X using ENat.recTopCoe with
  | top =>
    rw [top_add] at h
    exact absurd h.symm (ENat.coe_ne_top _)
  | coe x =>
    norm_cast at h ⊢
    omega

/-- Over a Noetherian local Cohen–Macaulay ring of nonzero dimension with infinite residue
field there is a nonzerodivisor `a ∈ 𝔪`, outside the minimal primes, with `(𝔪ⁿ⁺¹ : a) = 𝔪ⁿ`
for all large `n`. -/
private theorem exists_slice [IsNoetherianRing R] [Infinite (ResidueField R)]
    (hCM : Module.IsMaximalCohenMacaulay R R) (hdim : ringKrullDim R ≠ 0) :
    ∃ a ∈ maximalIdeal R, (∀ P ∈ minimalPrimes R, a ∉ P) ∧ IsSMulRegular R a ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ r : R, a * r ∈ maximalIdeal R ^ (n + 1) →
        r ∈ maximalIdeal R ^ n := by
  classical
  let Ps := (minimalPrimes.finite_of_isNoetherianRing R).toFinset
  obtain ⟨a, ha, haP, N, hN⟩ := exists_mem_maximalIdeal_forall_mul_mem_pow_imp_mem_pow Ps
    fun P hP => not_maximalIdeal_le_of_mem_minimalPrimes hdim
      ((Set.Finite.mem_toFinset _).mp hP)
  have hmin : ∀ P ∈ minimalPrimes R, a ∉ P := fun P hP =>
    haP P ((Set.Finite.mem_toFinset _).mpr hP)
  have hreg := hCM.isSMulRegular_of_notMem_minimalPrimes ha hmin
  obtain ⟨N', hN'⟩ := exists_forall_mul_mem_pow_succ_imp_mem_pow hreg hN
  exact ⟨a, ha, hmin, hreg, N', hN'⟩

/-- The residue field of a local ring has length one. -/
private theorem length_quotient_maximalIdeal_eq_one :
    Module.length R (R ⧸ maximalIdeal R) = 1 := by
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    (isSimpleModule_iff_isCoatom).2 (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
  exact Module.length_eq_one R _

/-- Cutting by an element `a ∈ 𝔪` with `(𝔪ⁿ⁺¹ : a) = 𝔪ⁿ` changes the lengths of `R/𝔪ⁿ` by the
difference of lengths of `R/𝔪ⁿ⁺¹` and `R/𝔪ⁿ`. -/
private theorem length_quotient_slice_pow_succ_eq {a : R} (ha : a ∈ maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {a})] {n k m : ℕ}
    (h : ∀ r : R, a * r ∈ maximalIdeal R ^ (n + 1) → r ∈ maximalIdeal R ^ n)
    (hn : Module.length R (R ⧸ maximalIdeal R ^ n) = k)
    (hn1 : Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) = ((k + m : ℕ) : ℕ∞)) :
    Module.length (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⧸
      maximalIdeal (R ⧸ Ideal.span {a}) ^ (n + 1)) = m := by
  rw [length_quotient_maximalIdeal_pow_eq (Ideal.span {a})]
  have h3 := length_quotient_span_singleton_sup_add_length_quotient_pow ha h
  rw [hn, hn1] at h3
  exact enat_eq_of_add_eq h3

/-- Cutting by an element of `𝔪` lowers `ℓ(R/𝔪²)` by at most one. -/
private theorem length_quotient_pow_two_le_slice {a : R} (ha : a ∈ maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {a})] :
    Module.length R (R ⧸ maximalIdeal R ^ 2) ≤ Module.length (R ⧸ Ideal.span {a})
      ((R ⧸ Ideal.span {a}) ⧸ maximalIdeal (R ⧸ Ideal.span {a}) ^ 2) + 1 := by
  rw [length_quotient_maximalIdeal_pow_eq (Ideal.span {a})]
  refine length_quotient_le_length_quotient_span_singleton_sup_add_one fun c hc => ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul hc ha

/-- Dimension bookkeeping: `d + 1 + 1 = 2` forces `d = 0`. -/
private theorem eq_zero_of_add_one_add_one_eq_two {d : WithBot ℕ∞} (h0 : d ≠ ⊥)
    (h : d + 1 + 1 = 2) : d = 0 := by
  obtain ⟨k, rfl⟩ := WithBot.ne_bot_iff_exists.mp h0
  have h' : k + 1 + 1 = (2 : ℕ∞) := WithBot.coe_injective (by push_cast; exact h)
  induction k using ENat.recTopCoe with
  | top => simp at h'
  | coe x =>
    have : x = 0 := by
      norm_cast at h'
      omega
    simp [this]

omit [IsLocalRing R] in
/-- If `I ≤ I'` and `R/I` has finite length at most that of `R/I'`, then `I' ≤ I`. -/
private theorem le_of_length_quotient_le {I I' : Ideal R} (h : I ≤ I')
    (hfin : Module.length R (R ⧸ I) ≠ ⊤)
    (hle : Module.length R (R ⧸ I) ≤ Module.length R (R ⧸ I')) : I' ≤ I := by
  let g : R ⧸ I →ₗ[R] R ⧸ I' := Submodule.factor h
  have hsum := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (Submodule.injective_subtype _) (Submodule.factor_surjective h)
    (LinearMap.exact_subtype_ker_map g)
  have hker : Module.length R (LinearMap.ker g) = 0 := by
    have hfin' : Module.length R (R ⧸ I') ≠ ⊤ := ne_top_of_le_ne_top hfin
      (by rw [hsum]; exact le_add_self)
    rw [hsum] at hle hfin
    have h' : Module.length R (LinearMap.ker g) + Module.length R (R ⧸ I') ≤
        0 + Module.length R (R ⧸ I') := by rwa [zero_add]
    exact le_antisymm ((WithTop.add_le_add_iff_right hfin').mp h') (by simp)
  have hsub : Subsingleton (LinearMap.ker g) := Module.length_eq_zero_iff.mp hker
  intro x hx
  have hmem : (Submodule.Quotient.mk x : R ⧸ I) ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk x : R ⧸ I') = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  have h0 : (⟨_, hmem⟩ : LinearMap.ker g) = 0 := Subsingleton.elim _ _
  have := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at this
  exact (Submodule.Quotient.mk_eq_zero _).mp this

end Helpers

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **A two-dimensional Gorenstein local ring with Hilbert function `n e + 1` has `e ≤ 2`**, for
an infinite residue field. The hypothesis is phrased with lengths:
`ℓ(R/𝔪ⁿ⁺¹) = ℓ(R/𝔪ⁿ) + n e + 1`. -/
theorem IsGorensteinLocalRing.le_two_of_length_quotient_pow_succ_of_infinite
    [Infinite (ResidueField R)] (hG : IsGorensteinLocalRing R) (hdim : ringKrullDim R = 2)
    (e : ℕ) (hL : ∀ n : ℕ, Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) =
      Module.length R (R ⧸ maximalIdeal R ^ n) + ((n * e + 1 : ℕ) : ℕ∞)) :
    e ≤ 2 := by
  classical
  -- the lengths `ℓ(R/𝔪ⁿ)` are finite
  let L : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, (i * e + 1)
  have hLn : ∀ n, Module.length R (R ⧸ maximalIdeal R ^ n) = (L n : ℕ∞) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      simp only [L, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      exact Module.length_eq_zero_iff.mpr (Ideal.Quotient.subsingleton_iff.mpr rfl)
    | succ n ih =>
      rw [hL, ih, ← Nat.cast_add]
      simp [L, Finset.sum_range_succ]
  have hLsucc : ∀ n, L (n + 1) = L n + (n * e + 1) := fun n => Finset.sum_range_succ _ _
  have hCM : Module.IsMaximalCohenMacaulay R R :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay R).mp
      (IsGorensteinLocalRing.isCohenMacaulayLocalRing R hG)
  have hL2 : L 2 = e + 2 := by simp [L, Finset.sum_range_succ]; ring
  -- first slice
  obtain ⟨a, ha, hamin, haSMul, N₁, hN₁⟩ := exists_slice hCM (by rw [hdim]; decide)
  obtain ⟨hlocB, hCMB, hdimB⟩ := hCM.quotient_span_singleton_of_notMem_minimalPrimes ha hamin
  let B := R ⧸ Ideal.span {a}
  have hGB : IsGorensteinLocalRing B :=
    (isGorensteinLocalRing_quotient_span_singleton_iff R a ha
      (mem_nonZeroDivisors_of_isSMulRegular haSMul)).mp hG
  have : Infinite (ResidueField B) := infinite_residueField_quotient _
  have hdimB' : ringKrullDim B + 1 = 2 := hdimB.trans hdim
  -- lengths over `B`
  have hLB : ∀ n ≥ N₁, Module.length B (B ⧸ maximalIdeal B ^ (n + 1)) = ((n * e + 1 : ℕ) : ℕ∞) := by
    intro n hn
    exact length_quotient_slice_pow_succ_eq ha (hN₁ n hn) (hLn n) (by rw [hLn, hLsucc])
  -- second slice
  obtain ⟨b, hb, hbmin, hbSMul, N₂, hN₂⟩ := exists_slice hCMB (by
    intro h0
    rw [h0] at hdimB'
    exact absurd hdimB' (by decide))
  obtain ⟨hlocC, -, hdimC⟩ := hCMB.quotient_span_singleton_of_notMem_minimalPrimes hb hbmin
  let C := B ⧸ Ideal.span {b}
  have hGC : IsGorensteinLocalRing C :=
    (isGorensteinLocalRing_quotient_span_singleton_iff B b hb
      (mem_nonZeroDivisors_of_isSMulRegular hbSMul)).mp hGB
  have hdimC' : ringKrullDim C = 0 := by
    refine eq_zero_of_add_one_add_one_eq_two
      (ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial) ?_
    rw [hdimC, hdimB']
  -- lengths over `C`, in large degrees
  have hLC : ∀ n ≥ max (N₁ + 1) N₂,
      Module.length C (C ⧸ maximalIdeal C ^ (n + 1)) = (e : ℕ∞) := by
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact length_quotient_slice_pow_succ_eq hb (hN₂ (n' + 1) (by omega)) (hLB n' (by omega))
      (by rw [hLB (n' + 1) (by omega), show (n' + 1) * e + 1 = (n' * e + 1) + e by ring])
  -- `C` is Artinian, so `ℓ(C) = e`
  have : IsArtinianRing C :=
    isArtinianRing_iff_krullDimLE_zero.mpr (Ring.krullDimLE_iff.mpr (by simp [hdimC']))
  obtain ⟨K, hK⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hK
  have hlenC : Module.length C C = (e : ℕ∞) := by
    let n := max (max (N₁ + 1) N₂) K
    have hz : maximalIdeal C ^ (n + 1) = ⊥ := by
      refine le_bot_iff.mp (le_trans (Ideal.pow_le_pow_right (by omega)) (le_of_eq hK))
    have h := hLC n (le_max_left _ _)
    rw [hz] at h
    rwa [(Submodule.quotEquivOfEqBot (⊥ : Ideal C) rfl).length_eq] at h
  -- each slice lowers `ℓ(· / 𝔪²)` by at most one
  have hR2 := length_quotient_pow_two_le_slice ha
  have hB2 := length_quotient_pow_two_le_slice hb
  rw [hLn, hL2] at hR2
  -- hence `𝔪_C² = 0`
  have hsplit := Module.length_eq_add_of_exact (maximalIdeal C ^ 2).subtype
    (maximalIdeal C ^ 2).mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  rw [hlenC] at hsplit
  have hsq : maximalIdeal C ^ 2 = ⊥ := by
    have hz : Module.length C (maximalIdeal C ^ 2 : Ideal C) = 0 := by
      have hle : ((e + 2 : ℕ) : ℕ∞) ≤ Module.length C (C ⧸ maximalIdeal C ^ 2) + 1 + 1 :=
        hR2.trans (by gcongr)
      generalize Module.length C (maximalIdeal C ^ 2 : Ideal C) = z at hsplit ⊢
      generalize Module.length C (C ⧸ maximalIdeal C ^ 2) = c at hsplit hle
      induction z using ENat.recTopCoe with
      | top => simp at hsplit
      | coe z =>
        induction c using ENat.recTopCoe with
        | top => simp at hsplit
        | coe c =>
          norm_cast at hsplit hle ⊢
          omega
    have : Subsingleton (maximalIdeal C ^ 2 : Ideal C) := Module.length_eq_zero_iff.mp hz
    exact Submodule.eq_bot_of_subsingleton
  -- the socle of `C` is one-dimensional
  obtain ⟨x, hx⟩ := hGC.exists_maximalIdeal_eq_span_singleton hdimC' hsq
  have hxm : x ∈ maximalIdeal C := hx ▸ Ideal.mem_span_singleton_self x
  have hfin := length_quotient_le_length_quotient_span_singleton_sup_add_one (J := (⊥ : Ideal C))
    (s := x) fun c hc => by
      have := Ideal.mul_mem_mul hc hxm
      rwa [← pow_two, hsq] at this
  rw [sup_bot_eq, ← hx, (Submodule.quotEquivOfEqBot (⊥ : Ideal C) rfl).length_eq, hlenC] at hfin
  rw [length_quotient_maximalIdeal_eq_one] at hfin
  exact_mod_cast hfin

/-- **A two-dimensional Gorenstein local ring with Hilbert function `n e + 1` has `e ≤ 2`.** The
hypothesis is phrased with lengths: `ℓ(R/𝔪ⁿ⁺¹) = ℓ(R/𝔪ⁿ) + n e + 1`. The case of a finite
residue field reduces to the infinite one through `R[t]_{𝔪R[t]}`. -/
theorem IsGorensteinLocalRing.le_two_of_length_quotient_pow_succ
    (hG : IsGorensteinLocalRing R) (hdim : ringKrullDim R = 2)
    (e : ℕ) (hL : ∀ n : ℕ, Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) =
      Module.length R (R ⧸ maximalIdeal R ^ n) + ((n * e + 1 : ℕ) : ℕ∞)) :
    e ≤ 2 := by
  obtain ⟨S, _, _, _, _, _, hflat, hmap, _⟩ :=
    exists_flat_isNoetherianRing_infinite_residueField R
  -- the closed fibre is the residue field, so `S` is Gorenstein
  have hGS : IsGorensteinLocalRing S := by
    refine (isGorensteinLocalRing_iff_of_flat R S).mpr ⟨hG, ?_⟩
    have hbot : maximalIdeal (S ⧸ (maximalIdeal R).map (algebraMap R S)) = ⊥ := by
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
        ← hmap, Ideal.map_quotient_self]
    have : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by
        rw [hbot, Submodule.spanFinrank_bot]
        exact_mod_cast ringKrullDim_nonneg_of_nontrivial)
    exact IsRegularLocalRing.isGorensteinLocalRing _
  have hdimS : ringKrullDim S = 2 :=
    (Stacks.FlatLocalDimension.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq hmap).symm.trans
      hdim
  -- the lengths `ℓ(· / 𝔪ⁿ)` are unchanged
  have hlen : ∀ n, Module.length S (S ⧸ maximalIdeal S ^ n) =
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
    intro n
    have h1 := IsLocalRing.length_baseChange R S (R ⧸ maximalIdeal R ^ n)
    rw [hmap, length_quotient_maximalIdeal_eq_one, mul_one] at h1
    rw [← h1, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (maximalIdeal R ^ n)).toLinearEquiv.length_eq, Ideal.map_pow, hmap]
  exact hGS.le_two_of_length_quotient_pow_succ_of_infinite hdimS e fun n => by
    rw [hlen, hlen, hL]

end Dualizing
