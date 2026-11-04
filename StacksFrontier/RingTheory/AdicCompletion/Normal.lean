module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.JacobsonIntegral
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Normality of the completion of a finite subalgebra

Let `A` be a Noetherian local ring and let `B ⊆ C` be finite `A`-algebras. If `B` is normal and
the completion of `C` along the ideal extended from the maximal ideal of `A` is normal, then the
corresponding completion of `B` is normal.

## Main results

* `isNormalRing_adicCompletion_of_finite_injective` — normality descends to the adic completion
  of the finite subalgebra.

## Implementation notes

The inclusion `B ⊆ C` of the source is an injective `A`-algebra structure map `B → C`, and the
source's `Bˆ` is `AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B`.

The completion `Bˆ` is flat over `B`, so by Serre's criterion normality of `Bˆ` only has to be
checked at primes lying over primes of `B` of height at most one. Over such a prime the
localization of `B` is a local Dedekind domain, and `ofTensorProductAlgEquiv` identifies the
completion of `C` with `Bˆ ⊗[B] C`; faithfully flat descent along a suitable localization of `C`
then gives normality of the localization of `Bˆ`.

## References

* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u v w

/-- Depth along a surjective algebra map: the depth of a module over the source along `I` is its
depth over the target along the image of `I`. -/
private alias depth_eq_depth_map_of_surjective := Module.depth_eq_depth_map_algebraMap

/-- The local form of the forward direction of Serre's criterion: a normal Noetherian local ring
is regular in dimension at most one and satisfies the depth inequality `(S₂)`. -/
private theorem serre_conditions_of_isNormalRing
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : IsNormalRing R) :
    (ringKrullDim R ≤ 1 → IsRegularLocalRing R) ∧
      min 2 (ringKrullDim R) ≤ (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl (fun x hx => not_not.mp hx)
  have h :=
    isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp hR
  constructor
  · intro hdim
    have := h.1 (maximalIdeal R) (by
      exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans_le hdim)
    exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  · have hd := h.2 (maximalIdeal R)
    rwa [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
      ← Module.depth_self_eq_of_ringEquiv e.toRingEquiv] at hd

/-- A normal Noetherian domain of dimension at most one is Dedekind. -/
private theorem isDedekindDomain_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R ≤ 1) : IsDedekindDomain R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have : Ring.DimensionLEOne R := ⟨fun hne hp => hp.isMaximal_of_ne_bot hne⟩
  exact { (inferInstance : IsDomain R), (inferInstance : IsNoetherianRing R),
    (inferInstance : Ring.DimensionLEOne R), (inferInstance : IsIntegrallyClosed R) with }

/-- An injective local map from a Dedekind domain to a domain is faithfully flat. -/
private theorem faithfullyFlat_of_injective_of_isDedekindDomain
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (hinj : Function.Injective (algebraMap R S)) :
    Module.FaithfullyFlat R S := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have : Module.Flat R S := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- An integral normal algebra containing a local Dedekind domain has a localization which is
faithfully flat over the domain. -/
private theorem exists_faithfullyFlat_localization_of_isNormalRing
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsLocalRing R] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (hS : IsNormalRing S) :
    ∃ (q : Ideal S) (_ : q.IsPrime), Module.FaithfullyFlat R (Localization.AtPrime q) := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  obtain ⟨r, -, hr, hrR⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := R) (S := S) (⊥ : Ideal R) (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj])
  have : r.IsPrime := hr
  obtain ⟨q, hrq, hq, hqR⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
    (R := R) (S := S) (maximalIdeal R) r (by rw [hrR]; exact bot_le)
  have : q.IsPrime := hq
  obtain ⟨hd, hi⟩ := hS q
  have hlocal : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
    constructor
    intro x hx
    by_contra hx'
    have hxq : algebraMap R S x ∈ q := by
      show x ∈ q.comap (algebraMap R S)
      rwa [hqR]
    have hxunit : IsUnit (algebraMap S (Localization.AtPrime q) (algebraMap R S x)) := hx
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ q _).mp hxunit hxq
  refine ⟨q, hq, faithfullyFlat_of_injective_of_isDedekindDomain R
    (Localization.AtPrime q) ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q),
    IsLocalization.map_eq_zero_iff q.primeCompl] at hx
  obtain ⟨t, ht⟩ := hx
  have hxr : algebraMap R S x ∈ r :=
    (hr.mem_or_mem (ht ▸ r.zero_mem)).resolve_left (fun h => t.property (hrq h))
  rw [← Ideal.mem_bot, ← hrR]
  exact hxr

/-- Normality descends from an integral normal extension after arbitrary base change from a local
Dedekind domain. -/
private theorem isNormalRing_of_tensorProduct_of_isDedekindDomain
    (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [IsDedekindDomain R] [IsLocalRing R]
    [Algebra.IsIntegral R C] (hinj : Function.Injective (algebraMap R C))
    (hC : IsNormalRing C) (hT : IsNormalRing (D ⊗[R] C)) : IsNormalRing D := by
  obtain ⟨q, hq, hflat⟩ := exists_faithfullyFlat_localization_of_isNormalRing R C hinj hC
  let M := q.primeCompl.map (Algebra.TensorProduct.includeRight : C →ₐ[R] D ⊗[R] C)
  let U := Localization M
  let e := IsLocalization.tensorProductEquivOfMapIncludeRight R D q.primeCompl
    (Localization.AtPrime q) U
  have hU : IsNormalRing U := hT.isLocalization M U
  have hn : IsNormalRing (D ⊗[R] Localization.AtPrime q) :=
    IsNormalRing.congr e.symm.toRingEquiv hU
  exact isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
    (S := D ⊗[R] Localization.AtPrime q) hn

/-- Localizing one factor of a normal tensor product preserves normality. -/
private theorem isNormalRing_tensorProduct_localization
    (R C D D' : Type*) [CommRing R] [CommRing C] [CommRing D] [CommRing D']
    [Algebra R C] [Algebra R D] [Algebra R D'] [Algebra D D'] [IsScalarTower R D D']
    (M : Submonoid D) [IsLocalization M D'] (h : IsNormalRing (D ⊗[R] C)) :
    IsNormalRing (D' ⊗[R] C) := by
  let f : D ⊗[R] C →ₐ[R] D' ⊗[R] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R D D') (AlgHom.id R C)
  let _ : Algebra (D ⊗[R] C) (D' ⊗[R] C) := f.toRingHom.toAlgebra
  have : IsScalarTower D (D ⊗[R] C) (D' ⊗[R] C) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap D D' x ⊗ₜ[R] (1 : C) = f (x ⊗ₜ[R] (1 : C))
      simp [f]
  have : IsLocalization (Algebra.algebraMapSubmonoid (D ⊗[R] C) M) (D' ⊗[R] C) :=
    IsLocalization.tensorProduct_tensorProduct R C M D' (by
      ext x
      show f ((1 : D) ⊗ₜ[R] x) = (1 : D') ⊗ₜ[R] x
      simp [f])
  exact h.isLocalization (Algebra.algebraMapSubmonoid (D ⊗[R] C) M) (D' ⊗[R] C)

/-- For a flat algebra over a normal Noetherian ring, Serre's conditions only need to be checked
over primes of height at most one. -/
private theorem isNormalRing_of_flat_of_serre_conditions_over_height_le_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsNormalRing R)
    (h₁ : ∀ (q : Ideal S) [q.IsPrime], (q.under R).height ≤ 1 → q.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime q))
    (h₂ : ∀ (q : Ideal S) [q.IsPrime], (q.under R).height ≤ 1 →
      min 2 (ringKrullDim (Localization.AtPrime q)) ≤
        (Module.depth (Localization.AtPrime q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :
          WithBot ℕ∞)) : IsNormalRing S := by
  have hR₂ :=
    (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp hR).2
  apply isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mpr
  constructor
  · intro q hq hheight
    apply h₁ q _ hheight
    have heq := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q
    exact (le_add_right (le_refl (q.under R).height)).trans (heq ▸ hheight)
  · intro q hq
    by_cases hp : (q.under R).height ≤ 1
    · exact h₂ q hp
    have hp₂ : (2 : ℕ∞) ≤ (q.under R).height :=
      (ENat.add_one_le_iff (by norm_num)).mpr (lt_of_not_ge hp)
    let _ : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (q.under R) q
    have : IsLocalHom
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) :=
      Localization.isLocalHom_localRingHom _ _ _ _
    have hdepth := hR₂ (q.under R)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R)] at hdepth
    have hdim : (2 : WithBot ℕ∞) ≤ ((q.under R).height : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hp₂
    rw [min_eq_left hdim] at hdepth
    refine (min_le_left _ _).trans (hdepth.trans (WithBot.coe_le_coe.mpr ?_))
    rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
      (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    exact le_self_add

/-- A flat base change of a normal Noetherian ring is normal if an integral normal extension has
normal base change. -/
private theorem isNormalRing_of_flat_of_normal_tensorProduct
    (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [IsNoetherianRing R] [IsNoetherianRing D]
    [Algebra.IsIntegral R C] [Module.Flat R D]
    (hinj : Function.Injective (algebraMap R C))
    (hR : IsNormalRing R) (hC : IsNormalRing C)
    (hT : IsNormalRing (D ⊗[R] C)) : IsNormalRing D := by
  have hlow (q : Ideal D) [q.IsPrime] (hp : (q.under R).height ≤ 1) :
      IsNormalRing (Localization.AtPrime q) := by
    let p := q.under R
    let Rp := Localization.AtPrime p
    let Dq := Localization.AtPrime q
    let Cp := Rp ⊗[R] C
    obtain ⟨hd, hi⟩ := hR p
    have : IsDedekindDomain Rp :=
      isDedekindDomain_of_isIntegrallyClosed_of_ringKrullDim_le_one Rp (by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
        exact_mod_cast hp)
    let _ : Algebra Rp Dq := Localization.AtPrime.algebraOfLiesOver p q
    let _ : Algebra C Cp := Algebra.TensorProduct.rightAlgebra
    have hCp : IsNormalRing Cp := hC.isLocalization (Algebra.algebraMapSubmonoid C p.primeCompl) Cp
    have hinjCp : Function.Injective (algebraMap Rp Cp) :=
      Algebra.TensorProduct.includeLeft_injective (S := Rp) hinj
    have hTq : IsNormalRing (Dq ⊗[R] C) :=
      isNormalRing_tensorProduct_localization R C D Dq q.primeCompl hT
    let e := Algebra.TensorProduct.cancelBaseChange R Rp Dq Dq C
    exact isNormalRing_of_tensorProduct_of_isDedekindDomain Rp Cp Dq hinjCp hCp
      (IsNormalRing.congr e.symm.toRingEquiv hTq)
  apply isNormalRing_of_flat_of_serre_conditions_over_height_le_one hR
  · intro q hq hp hheight
    apply (serre_conditions_of_isNormalRing _ (hlow q hp)).1
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
    exact_mod_cast hheight
  · intro q hq hp
    exact (serre_conditions_of_isNormalRing _ (hlow q hp)).2

/-- **Stacks Project, Tag 0BGH.** Let `A` be a Noetherian local ring and `B ⊆ C` finite
`A`-algebras. If `B` and the `m_A`-adic completion of `C` are normal, then the `m_A`-adic
completion of `B` is normal. -/
@[stacks 0BGH]
theorem isNormalRing_adicCompletion_of_finite_injective
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsNoetherianRing A]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C]
    (hBC : Function.Injective (algebraMap B C))
    (hB : IsNormalRing B)
    (hC : IsNormalRing (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) C)) :
    IsNormalRing (AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  have : Module.Finite B C := Module.Finite.of_restrictScalars_finite A B C
  have hflatC : Module.FaithfullyFlat C
      (AdicCompletion ((maximalIdeal A).map (algebraMap A C)) C) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (Ideal.jacobson_bot (R := C) ▸ map_maximalIdeal_le_jacobson A C)
  have hnC : IsNormalRing C :=
    isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
      (S := AdicCompletion ((maximalIdeal A).map (algebraMap A C)) C) hC
  let I := (maximalIdeal A).map (algebraMap A B)
  have hIC : I.map (algebraMap B C) = (maximalIdeal A).map (algebraMap A C) := by
    dsimp only [I]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  have hT : IsNormalRing (AdicCompletion I B ⊗[B] C) :=
    IsNormalRing.congr (ofTensorProductAlgEquiv I C).symm.toRingEquiv (by rw [hIC]; exact hC)
  exact isNormalRing_of_flat_of_normal_tensorProduct B C (AdicCompletion I B) hBC hB hnC hT

end
