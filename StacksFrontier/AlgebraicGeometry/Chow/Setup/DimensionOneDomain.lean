module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CohenMacaulayBase
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The one-dimensional domain base for Chow homology

Let `A` be a Noetherian domain of Krull dimension one. Its spectrum, equipped with the
dimension function which is zero at the maximal ideals and one at the generic point, is a base
situation for Chow homology.

## Main definitions

* `AlgebraicGeometry.domainBaseDimensionFunction` is the integer-valued function on the prime
  spectrum of a ring which is zero at the maximal ideals and one elsewhere.

## Main results

* `AlgebraicGeometry.isCohenMacaulayLocalRing_of_ringKrullDim_le_one` — a Noetherian local
  domain of Krull dimension at most one is Cohen--Macaulay.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_isAffine_of_ringKrullDim_le_one` — an affine
  scheme whose ring of global sections is a Noetherian domain of Krull dimension at most one is
  universally catenary.
* `Stacks.Chow.exists_chowSituation_spec_of_ringKrullDim_eq_one` — the Chow situation on the
  spectrum of a Noetherian domain of Krull dimension one, with its specified dimension
  function.

## References

* [Stacks Project, Tag 02QN](https://stacks.math.columbia.edu/tag/02QN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Cohen--Macaulayness in dimension at most one -/

/-- A Noetherian local domain of Krull dimension at most one is Cohen--Macaulay. -/
theorem isCohenMacaulayLocalRing_of_ringKrullDim_le_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] (h : ringKrullDim R ≤ 1) :
    IsCohenMacaulayLocalRing R := by
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self,
    isCohenMacaulayModule_iff_supportDim_eq_depth, Module.supportDim_self_eq_ringKrullDim]
  have hItop : (maximalIdeal R) • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (maximalIdeal.isMaximal R).ne_top
  have hdd : Module.depth R (maximalIdeal R) R = Module.depthSup R (maximalIdeal R) R := by
    rw [Module.depth, ite_eq_right hItop, Module.depthSup_eq_iSup]
  have hle : (Module.depthSup R (maximalIdeal R) R : WithBot ℕ∞) ≤ ringKrullDim R := by
    rw [← hdd, ← Module.supportDim_self_eq_ringKrullDim]
    exact Module.depth_le_supportDim R (maximalIdeal R) R hItop
  rcases eq_or_ne (ringKrullDim R) 0 with h0 | h0
  · rw [h0] at hle ⊢
    exact (le_antisymm (by exact_mod_cast hle) (by simp)).symm
  · have hdim : ringKrullDim R = 1 := by
      obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
      rw [← hn] at h h0 ⊢
      rw [show n = 1 from le_antisymm (by exact_mod_cast h)
        (Order.one_le_iff_ne_zero.mpr (by simpa using h0))]
      rfl
    have hm : maximalIdeal R ≠ ⊥ := fun hbot => by
      simp [← maximalIdeal_height_eq_ringKrullDim, hbot] at hdim
    obtain ⟨a, hamem, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    have hone : (1 : ℕ∞) ≤ Module.depthSup R (maximalIdeal R) R :=
      le_trans le_add_self
        (depth_quotSMulTop_succ_le_depth (mul_right_injective₀ hane) hamem)
    rw [hdim] at hle ⊢
    exact (le_antisymm (by exact_mod_cast hle) (by exact_mod_cast hone)).symm

/-- An affine scheme whose ring of global sections is a Noetherian domain of Krull dimension at
most one is universally catenary. -/
@[ega "IV 10.7.1" "special case"]
theorem Scheme.isUniversallyCatenary_of_isAffine_of_ringKrullDim_le_one (S : Scheme.{u})
    [IsAffine S] [IsLocallyNoetherian S] (hdom : IsDomain Γ(S, (⊤ : S.Opens)))
    (hnoe : IsNoetherianRing Γ(S, (⊤ : S.Opens)))
    (hdim : ringKrullDim Γ(S, (⊤ : S.Opens)) ≤ 1) :
    Scheme.IsUniversallyCatenary S := by
  let := hdom
  let := hnoe
  refine (Scheme.isUniversallyCatenary_iff_stalk_isUniversallyCatenary S).mpr fun s => ?_
  have hU : IsAffineOpen (⊤ : S.Opens) := isAffineOpen_top S
  let : Algebra Γ(S, (⊤ : S.Opens)) (S.presheaf.stalk s) :=
    S.presheaf.algebra_section_stalk (⟨s, trivial⟩ : (⊤ : S.Opens))
  let p : Ideal Γ(S, (⊤ : S.Opens)) := (hU.primeIdealOf ⟨s, trivial⟩).asIdeal
  let : p.IsPrime := (hU.primeIdealOf ⟨s, trivial⟩).isPrime
  let : IsLocalization.AtPrime (S.presheaf.stalk s) p := hU.isLocalization_stalk ⟨s, trivial⟩
  let : IsLocalRing (S.presheaf.stalk s) := IsLocalization.AtPrime.isLocalRing _ p
  let : IsNoetherianRing (S.presheaf.stalk s) :=
    IsLocalization.isNoetherianRing p.primeCompl _ hnoe
  let : IsDomain (S.presheaf.stalk s) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ (Ideal.primeCompl_le_nonZeroDivisors p)
  refine Ring.IsUniversallyCatenary.of_isCohenMacaulayLocalRing
    (isCohenMacaulayLocalRing_of_ringKrullDim_le_one ?_)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (S.presheaf.stalk s)]
  exact (ringKrullDim_le_iff_height_le 1).mp hdim inferInstance

/-! ### The dimension function of a one-dimensional domain -/

/-- The integer-valued function on the prime spectrum of `A` which is zero at the maximal ideals
and one at every other prime. -/
noncomputable def domainBaseDimensionFunction (A : Type u) [CommRing A] :
    PrimeSpectrum A → ℤ := by
  classical exact fun p => if p.asIdeal.IsMaximal then 0 else 1

/-- Along a nontrivial specialization `p ⤳ q` of primes in a ring of Krull dimension at most one,
`domainBaseDimensionFunction` drops by exactly one. -/
theorem domainBaseDimensionFunction_step (A : Type u) [CommRing A] [Ring.KrullDimLE 1 A]
    {p q : PrimeSpectrum A} (hpq : p ⤳ q) (hne : p ≠ q) :
    domainBaseDimensionFunction A p = domainBaseDimensionFunction A q + 1 := by
  classical
  have hpqle : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes p q).mpr hpq
  have hp_not_max : ¬ p.asIdeal.IsMaximal := fun hp_max =>
    hne (PrimeSpectrum.ext (hp_max.eq_of_le q.isPrime.ne_top hpqle))
  have hq_max : q.asIdeal.IsMaximal :=
    (Ring.krullDimLE_one_iff.mp inferInstance q.asIdeal q.isPrime).resolve_left fun h => by
      rw [minimalPrimes_eq_minimals] at h
      exact hne (PrimeSpectrum.ext (h.eq_of_le p.isPrime hpqle))
  simp [domainBaseDimensionFunction, hp_not_max, hq_max]

/-- In a ring of positive Krull dimension the zero ideal is not maximal. -/
theorem not_isMaximal_bot_of_ringKrullDim_pos (A : Type u) [CommRing A]
    (hdim : 0 < ringKrullDim A) : ¬ (⊥ : Ideal A).IsMaximal := by
  intro hbot
  have : Nontrivial A := (subsingleton_or_nontrivial A).resolve_left fun h => by
    let := h; exact hbot.ne_top (Subsingleton.elim _ _)
  refine (not_le.mpr hdim) ((ringKrullDim_le_iff_height_le (0 : WithBot ℕ∞)).mpr ?_)
  intro p hp
  rw [← hbot.eq_of_le hp.ne_top bot_le]
  simp

end AlgebraicGeometry

namespace Stacks.Chow

/-- The spectrum of a Noetherian domain of Krull dimension one, with the dimension function
which is zero at its maximal ideals and one at its generic point, is a base situation for Chow
homology. -/
@[stacks 02QN]
theorem exists_chowSituation_spec_of_ringKrullDim_eq_one (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 1) :
    ∃ (C : ChowSituation.{u}) (hC : C.S = Spec (CommRingCat.of A)),
      (∀ p : PrimeSpectrum A, p.asIdeal.IsMaximal →
        (hC ▸ C.dimensionFunction) p = 0) ∧
      (hC ▸ C.dimensionFunction) (⊥ : PrimeSpectrum A) = 1 := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  obtain ⟨d, hd⟩ : ∃ d : DimensionFunction (PrimeSpectrum A),
      ∀ p, d p = domainBaseDimensionFunction A p :=
    (TopologicalSpace.exists_dimensionFunction_iff (domainBaseDimensionFunction A)).2
      ⟨fun p q hpq hne => by rw [domainBaseDimensionFunction_step A hpq hne]; lia,
        fun p q hpq => domainBaseDimensionFunction_step A hpq.1 hpq.2.1⟩
  have e : Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) ≃+* A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  have hUC : Scheme.IsUniversallyCatenary (Spec (CommRingCat.of A)) :=
    Scheme.isUniversallyCatenary_of_isAffine_of_ringKrullDim_le_one _
      (e.toMulEquiv.isDomain A) (isNoetherianRing_of_ringEquiv A e.symm)
      (by rw [ringKrullDim_eq_of_ringEquiv e, hdim])
  refine ⟨⟨Spec (CommRingCat.of A), hUC, d⟩, rfl, fun p hpmax => ?_, ?_⟩
  · simp [hd p, domainBaseDimensionFunction, hpmax]
  · simp [hd (⊥ : PrimeSpectrum A), domainBaseDimensionFunction,
      not_isMaximal_bot_of_ringKrullDim_pos A (by simp [hdim])]

end Stacks.Chow
