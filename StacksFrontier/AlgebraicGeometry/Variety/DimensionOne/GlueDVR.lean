module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.GluingSituation
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.Jacobson
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing a semilocal ring to a discrete valuation ring

In the semilocal/DVR gluing situation there is a dichotomy governed by the units of the
semilocal ring `A`. If every unit of `A` lies in the intersection `R = A ⊓ B`, then `A` is
integral over `R`, hence contained in `B`, and the discrete valuation ring `B` dominates a
localization of `A` at a maximal ideal; in that case the multiplication map from the tensor
product over the integers is not surjective. If instead some unit of `A` lies outside `R`, its
inverse generates `A` over `R` and a suitable element generates `B`, so the two spectra are
open subschemes covering `Spec R` and the relative tensor product is the common fraction field.

## Main definitions

* `Ring.SemilocalDVRGluingSituation.tensorProductTo` is the canonical multiplication map from
  the relative tensor product to the common fraction field.

## Main results

* `Ring.SemilocalDVRGluingSituation.exists_maximalIdeal_localization_le_of_units_mem_inf` gives
  the dominated local ring.
* `Ring.SemilocalDVRGluingSituation.not_surjective_tensorProduct_of_units_mem_inf` gives failure
  of surjectivity of the canonical multiplication map.
* `Ring.SemilocalDVRGluingSituation.isOpenImmersion_specMap_R_A_of_unit_not_mem_R` and
  `Ring.SemilocalDVRGluingSituation.isOpenImmersion_specMap_R_B_of_unit_not_mem_R` give the two
  open immersions.
* `Ring.SemilocalDVRGluingSituation.range_specMap_R_A_union_R_B_of_unit_not_mem_R` gives the
  covering assertion.
* `Ring.SemilocalDVRGluingSituation.tensorProductTo_bijective_of_unit_not_mem_R` identifies the
  relative tensor product with the common fraction field.

## Implementation notes

The local ring of `A` at a maximal ideal is represented by `LocalSubring.ofPrime`, inside the
common fraction field, and domination is the order on `LocalSubring`. The unadorned tensor
product of the source is the tensor product over the integers, whose canonical map sends a pure
tensor `a ⊗ b` to the product of the images of `a` and `b` in the common field. The source's
condition that `Aˣ` is not contained in `R` is expressed using the coercions from the unit group
of `A` into the common field.

## References

* [Stacks Project, Tag 09N1](https://stacks.math.columbia.edu/tag/09N1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace Ring.SemilocalDVRGluingSituation

private lemma inv_mem_of_isUnit {K : Type*} [Field K] {T : Subring K} {x : T}
    (hx : IsUnit x) : (x : K)⁻¹ ∈ T := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have h : (x : K) * y = 1 := by simpa using congrArg Subtype.val hy
  rw [← eq_inv_of_mul_eq_one_right h]
  exact y.2

private lemma coe_units_zpow {K : Type*} [Field K] {T : Subring K} (q : Tˣ) (n : ℤ) :
    (((q ^ n : Tˣ) : T) : K) = ((q : T) : K) ^ n := by
  have h := congrArg (fun t : Kˣ => (t : K)) (map_zpow (Units.map (algebraMap T K)) q n)
  simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at h
  exact h

private lemma coe_units_inv {K : Type*} [Field K] {T : Subring K} (q : Tˣ) :
    (((q⁻¹ : Tˣ) : T) : K) = ((q : T) : K)⁻¹ := by
  simpa using coe_units_zpow q (-1)

/-- A ring map from `R` that is injective and inverts, and is surjective up to powers of, `r`
is a localization away from `r`. -/
private lemma isLocalization_away_of_injective {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (r : R) (hinj : Function.Injective (algebraMap R T))
    (map_unit : IsUnit (algebraMap R T r))
    (surj : ∀ s, ∃ (n : ℕ) (a : R), s * algebraMap R T r ^ n = algebraMap R T a) :
    IsLocalization.Away r T :=
  IsLocalization.Away.mk r map_unit surj fun _ _ h => ⟨0, by rw [hinj h]⟩

private lemma mul_zpow_mul_pow_cancel {K : Type*} [Field K] (w v p : K) (hp : p ≠ 0)
    (m : ℤ) (k : ℕ) : (w * p ^ m) ^ k * (v * p ^ k) ^ (-m) = w ^ k * v ^ (-m) := by
  have hcancel : (p ^ m) ^ k * (p ^ k) ^ (-m) = 1 := by
    rw [← zpow_natCast (p ^ m), ← zpow_natCast p k, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hp,
      show m * (k : ℤ) + (k : ℤ) * -m = 0 by ring, zpow_zero]
  calc _ = w ^ k * v ^ (-m) * ((p ^ m) ^ k * (p ^ k) ^ (-m)) := by
        rw [mul_pow, mul_zpow]
        ring
    _ = _ := by rw [hcancel, mul_one]

private lemma pos_of_eq_unit_mul_pow {R : Type*} [CommRing R] [IsLocalRing R] {u π : R}
    {v : Rˣ} {k : ℕ} (hu : u ∈ IsLocalRing.maximalIdeal R) (h : u = v * π ^ k) : 0 < k :=
  Nat.pos_of_ne_zero fun hk => (IsLocalRing.mem_maximalIdeal u).mp hu (by simp [h, hk])

private lemma isUnit_add_of_mem_jacobson {A : Type*} [CommRing A] {x u : A}
    (hx : x ∈ Ring.jacobson A) (hu : IsUnit u) : IsUnit (x + u) := by
  obtain ⟨u, rfl⟩ := hu
  have hx' : x ∈ Ideal.jacobson (⊥ : Ideal A) := by rwa [Ideal.jacobson_bot]
  convert ((Ideal.mem_jacobson_bot.mp hx') ↑u⁻¹).mul u.isUnit using 1
  simp [add_mul, mul_assoc]

private lemma exists_unit_quad_mem_jacobson {A : Type*} [CommRing A]
    [Finite (MaximalSpectrum A)] (x : A) :
    ∃ y : A, IsUnit y ∧ x ^ 2 - x * y ∈ Ring.jacobson A := by
  classical
  let f : MaximalSpectrum A → Ideal A := fun p => p.asIdeal
  have hf : Pairwise (fun p q => IsCoprime (f p) (f q)) := fun p q hpq =>
    p.isCoprime_of_ne (by simpa [f] using hpq)
  let z : MaximalSpectrum A → A := fun p => if x ∈ p.asIdeal then 1 else x
  obtain ⟨y, hy⟩ := Ideal.exists_forall_sub_mem_ideal hf z
  have hynot (p : MaximalSpectrum A) : y ∉ p.asIdeal := by
    intro hyp
    by_cases hxp : x ∈ p.asIdeal
    · exact p.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (by simpa [z, hxp] using p.asIdeal.sub_mem hyp (hy p)))
    · exact hxp (by simpa [z, hxp] using p.asIdeal.add_mem hyp (p.asIdeal.neg_mem (hy p)))
  have hyunit : IsUnit y := by
    by_contra hyu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _
      fun h => hyu (Ideal.span_singleton_eq_top.mp h)
    exact hynot ⟨m, hm⟩ (hle (Ideal.mem_span_singleton_self y))
  have hquad (p : MaximalSpectrum A) : x ^ 2 - x * y ∈ p.asIdeal := by
    by_cases hxp : x ∈ p.asIdeal
    · apply p.asIdeal.sub_mem
      · simpa [pow_two] using p.asIdeal.mul_mem_right x hxp
      · simpa [mul_comm] using p.asIdeal.mul_mem_left y hxp
    · have hyx : y - x ∈ p.asIdeal := by
        simpa [z, hxp] using hy p
      have hxy : x - y ∈ p.asIdeal := by
        simpa [sub_eq_add_neg, add_comm] using p.asIdeal.neg_mem hyx
      convert p.asIdeal.mul_mem_left x hxy using 1
      ring
  refine ⟨y, hyunit, ?_⟩
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact Ideal.mem_sInf.mpr fun m hm => hquad ⟨m, hm⟩

variable (S : SemilocalDVRGluingSituation)

private lemma dimensionLEOne_A : Ring.DimensionLEOne S.A := by
  have hdimLE : Ring.KrullDimLE 1 S.A := Ring.krullDimLE_iff.mpr S.ringKrullDimA.le
  exact ⟨fun {q} hq hqprime => (Ring.krullDimLE_one_iff_of_isPrime_bot.mp hdimLE) q hq hqprime⟩

private lemma jacobson_mem_intersection (h_units : ∀ u : S.Aˣ, (((u : S.A) : S.K) ∈ S.R))
    (x : S.A) (hx : x ∈ Ring.jacobson S.A) : (((x : S.A) : S.K) ∈ S.R) := by
  have hu : IsUnit (x + 1) := isUnit_add_of_mem_jacobson hx isUnit_one
  convert S.R.sub_mem (h_units hu.unit) S.R.one_mem using 1
  simp

private lemma integral_A_over_intersection (h_units : ∀ u : S.Aˣ, (((u : S.A) : S.K) ∈ S.R)) :
    ∀ x : S.A, IsIntegral S.R x := by
  intro x
  obtain ⟨y, hyunit, hquad⟩ := exists_unit_quad_mem_jacobson x
  have hyR : (((y : S.A) : S.K)) ∈ S.R := h_units hyunit.unit
  let d : S.A := x ^ 2 - x * y
  let yr : S.R := ⟨(y : S.K), hyR⟩
  let dr : S.R := ⟨(d : S.K), jacobson_mem_intersection S h_units d hquad⟩
  have hyrA : algebraMap S.R S.A yr = y := Subtype.ext rfl
  have hdrA : algebraMap S.R S.A dr = d := Subtype.ext rfl
  refine ⟨X ^ 2 - (C yr * X + C dr), monic_X_pow_sub degree_linear_lt, ?_⟩
  show eval₂ (algebraMap S.R S.A) x (X ^ 2 - (C yr * X + C dr)) = 0
  simp [hyrA, hdrA]
  dsimp [d]
  ring

private noncomputable def dvrValuationSubring :
    ValuationSubring S.K :=
  ValuationSubring.ofSubring S.B (by
    intro z
    rcases (ValuationRing.iff_isInteger_or_isInteger S.B S.K).mp inferInstance z with hz | hz
    · left
      change z ∈ Set.range (algebraMap S.B S.K) at hz
      obtain ⟨b, rfl⟩ := hz
      exact b.2
    · right
      change z⁻¹ ∈ Set.range (algebraMap S.B S.K) at hz
      obtain ⟨b, hb⟩ := hz
      rw [← hb]
      exact b.2)

private lemma dvr_subring_ne_top : S.B ≠ ⊤ := by
  intro h
  have htop : IsField (⊤ : Subring S.K) :=
    Subring.topEquiv.toMulEquiv.isField (Field.toIsField S.K)
  exact IsDiscreteValuationRing.not_isField S.B (h ▸ htop)

private lemma subring_A_le_B (h_units : ∀ u : S.Aˣ, (((u : S.A) : S.K) ∈ S.R)) :
    S.A ≤ S.B := by
  have hKint (a : S.A) : IsIntegral S.R ((a : S.A) : S.K) :=
    (integral_A_over_intersection S h_units a).map (IsScalarTower.toAlgHom S.R S.A S.K)
  let V := dvrValuationSubring S
  intro a ha
  have hai : IsIntegral S.B a := (hKint ⟨a, ha⟩).tower_top
  have hmem : a ∈ V.toSubring :=
    LocalSubring.mem_of_isMax_of_isIntegral (ValuationSubring.isMax_toLocalSubring V) hai
  simpa [V, dvrValuationSubring] using hmem

private lemma coe_inv_not_mem_B (hAB : S.A ≤ S.B) (xA : S.A) (hxA : (xA : S.K) ≠ 0)
    [IsLocalization (Submonoid.powers xA) S.K] : (xA : S.K)⁻¹ ∉ S.B := by
  intro hinv
  refine dvr_subring_ne_top S (top_unique fun z _ => ?_)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers xA) z
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
  have hsK : ((s : S.A) : S.K) = (xA : S.K) ^ n := by
    rw [← hn]
    simp
  have hs' : z * (xA : S.K) ^ n = a := by
    rw [← hsK]
    exact hs
  have hz : z = (a : S.K) * ((xA : S.K)⁻¹) ^ n := by
    rw [← hs', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hxA), mul_one]
  rw [hz]
  exact S.B.mul_mem (hAB a.2) (S.B.pow_mem hinv n)

private lemma ofPrime_comap_maximalIdeal_le (hAB : S.A ≤ S.B) :
    LocalSubring.ofPrime S.A ((IsLocalRing.maximalIdeal S.B).comap (Subring.inclusion hAB)) ≤
      ({ toSubring := S.B } : LocalSubring S.K) := by
  let pI : Ideal S.A := (IsLocalRing.maximalIdeal S.B).comap (Subring.inclusion hAB)
  have hpprime : pI.IsPrime := by
    dsimp [pI]
    infer_instance
  let gB : Localization.AtPrime pI →+* S.B :=
    IsLocalization.lift (M := pI.primeCompl) (S := Localization.AtPrime pI)
      (g := Subring.inclusion hAB) fun s => IsLocalRing.notMem_maximalIdeal.mp fun hs => s.2 hs
  have hgmap : (IsLocalRing.maximalIdeal (Localization.AtPrime pI)).map gB ≤
      IsLocalRing.maximalIdeal S.B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal pI, Ideal.map_map, IsLocalization.lift_comp]
    exact Ideal.map_le_iff_le_comap.mpr le_rfl
  have hgLocal : IsLocalHom gB := ((IsLocalRing.local_hom_TFAE gB).out 3 1).mp hgmap
  let fK : Localization.AtPrime pI →+* S.K :=
    IsLocalization.lift (M := pI.primeCompl) (S := Localization.AtPrime pI)
      (g := S.A.subtype) (by simp [Ideal.primeCompl, not_imp_not])
  have hgcomp : (algebraMap S.B S.K).comp gB = fK := by
    apply IsLocalization.ringHom_ext (M := pI.primeCompl)
    ext a
    have hleft : gB (algebraMap S.A (Localization.AtPrime pI) a) =
        Subring.inclusion hAB a := by
      simp [gB]
    have hfKcomp : fK.comp (algebraMap S.A (Localization.AtPrime pI)) = S.A.subtype :=
      IsLocalization.lift_comp _
    show (algebraMap S.B S.K) (gB (algebraMap S.A (Localization.AtPrime pI) a)) =
      (fK.comp (algebraMap S.A (Localization.AtPrime pI))) a
    rw [hleft, hfKcomp]
    rfl
  have hsub : (LocalSubring.ofPrime S.A pI).toSubring ≤ S.B := by
    intro z hz
    change z ∈ Set.range fK at hz
    obtain ⟨q, rfl⟩ := hz
    rw [← hgcomp]
    exact (gB q).property
  let eAlg : Localization.AtPrime pI ≃ₐ[S.A] (LocalSubring.ofPrime S.A pI).toSubring :=
    LocalSubring.ofPrimeEquiv S.A pI
  let e : Localization.AtPrime pI ≃+* (LocalSubring.ofPrime S.A pI).toSubring :=
    eAlg.toRingEquiv
  let eInvHom := e.symm.toRingHom
  have heq : gB.comp eInvHom = Subring.inclusion hsub := by
    apply IsLocalization.ringHom_ext (M := pI.primeCompl)
    ext a
    simp only [RingHom.comp_apply]
    rw [← eAlg.commutes a]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.symm_toEquiv_eq_symm, AlgEquiv.commutes, RingHom.coe_coe, RingEquiv.coe_mk,
      EquivLike.coe_coe, IsLocalization.lift_eq, Subring.coe_inclusion, gB, eInvHom, e]
    rfl
  have heInvLocal : IsLocalHom eInvHom :=
    ⟨fun a hfa => by simpa [eInvHom] using hfa.map e.toRingHom⟩
  exact ⟨hsub, heq ▸ (inferInstance : IsLocalHom (gB.comp eInvHom))⟩

/-- If every unit of `A` belongs to `A ∩ B`, then the DVR `B` dominates the
localization of `A` at some maximal ideal. -/
@[stacks 09N1 "all_units_in_r"]
theorem exists_maximalIdeal_localization_le_of_units_mem_inf
    (h_units : ∀ u : S.Aˣ, (((u : S.A) : S.K) ∈ S.R)) :
    ∃ p : MaximalSpectrum S.A,
      LocalSubring.ofPrime S.A p.asIdeal ≤
        ({ toSubring := S.B } : LocalSubring S.K) := by
  have hAB := subring_A_le_B S h_units
  obtain ⟨xA, hxAne, hxAj⟩ :=
    Ring.exists_ne_zero_mem_jacobson S.ringKrullDimA
  have := dimensionLEOne_A S
  have : IsLocalization (Submonoid.powers xA) S.K :=
    Ring.isLocalization_powers_of_ne_zero_of_mem_jacobson xA hxAne hxAj
  let xB : S.B := ⟨(xA : S.K), hAB xA.2⟩
  have hxBmax : xB ∈ IsLocalRing.maximalIdeal S.B := by
    by_contra hnot
    exact coe_inv_not_mem_B S hAB xA (fun h => hxAne (Subtype.ext h))
      (inv_mem_of_isUnit (IsLocalRing.notMem_maximalIdeal.mp hnot))
  let pI : Ideal S.A := (IsLocalRing.maximalIdeal S.B).comap (Subring.inclusion hAB)
  have hpx : xA ∈ pI := hxBmax
  have hp0 : pI ≠ ⊥ := fun hp => hxAne (Ideal.mem_bot.mp (hp ▸ hpx))
  have hpprime : pI.IsPrime := by
    dsimp [pI]
    infer_instance
  exact ⟨⟨pI, Ring.DimensionLEOne.maximalOfPrime hp0 hpprime⟩,
    ofPrime_comap_maximalIdeal_le S hAB⟩

/-- If every unit of `A` belongs to `A ∩ B`, then the canonical
multiplication map `A ⊗[ℤ] B → K` is not surjective. -/
@[stacks 09N1 "all_units_in_r"]
theorem not_surjective_tensorProduct_of_units_mem_inf
    (h_units : ∀ u : S.Aˣ, (((u : S.A) : S.K) ∈ S.R)) :
    ¬ Function.Surjective
      (Algebra.TensorProduct.lift (B := S.B) S.A.subtype.toIntAlgHom
        S.B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  let f := Algebra.TensorProduct.lift (B := S.B) S.A.subtype.toIntAlgHom
    S.B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)
  intro hsurj
  have hAB := subring_A_le_B S h_units
  have himage : ∀ t : TensorProduct ℤ S.A S.B, f t ∈ S.B := by
    intro t
    refine TensorProduct.inductionOn t ?_ ?_
    · intro a b
      show ((a : S.K) * (b : S.K)) ∈ S.B
      exact S.B.mul_mem (Subring.inclusion hAB a).property b.property
    · intro x y hx hy
      simpa only [map_add] using S.B.add_mem hx hy
  refine dvr_subring_ne_top S (top_unique fun z _ => ?_)
  obtain ⟨t, rfl⟩ := hsurj z
  exact himage t

/-- The canonical multiplication map from the tensor product over the intersection ring to
the common fraction field. -/
public def tensorProductTo :
    TensorProduct S.R S.A S.B →+* S.K :=
  (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom S.R S.A S.K)
    (IsScalarTower.toAlgHom S.R S.B S.K)).toRingHom

private theorem inverse_mem_dvr_of_not_mem (z : S.K) (hz : z ≠ 0)
    (hzB : z ∉ S.B) : z⁻¹ ∈ S.B := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (S.B) z
  have hyK : (y : S.K) ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hyB : y ≠ 0 := by
    intro hy0
    apply hyK
    exact congrArg (fun q : S.B => (q : S.K)) hy0
  obtain ⟨c, h | h⟩ := ValuationRing.cond x y
  · have hxy' : (x : S.K) * (c : S.K) = (y : S.K) := by
      exact congrArg (fun t : S.B => (t : S.K)) h
    have hxK : (x : S.K) ≠ 0 := by
      intro hx
      have hxB : x = 0 := IsFractionRing.injective (S.B) S.K hx
      have hyB : y = 0 := by rw [← h]; simp [hxB]
      apply hyK
      exact congrArg (fun q : S.B => (q : S.K)) hyB
    have hmul : z * (c : S.K) = 1 := by
      rw [← hxy]
      field_simp [hyB]
      have hxyMap : (algebraMap (S.B) S.K x) * (algebraMap (S.B) S.K c) =
          algebraMap (S.B) S.K y := by
        show (x : S.K) * (c : S.K) = (y : S.K)
        exact hxy'
      exact hxyMap
    have hinv : z⁻¹ = (c : S.K) := by
      calc
        z⁻¹ = z⁻¹ * (z * (c : S.K)) := by rw [hmul]; simp
        _ = (c : S.K) := by field_simp [hz]
    rw [hinv]
    exact SetLike.coe_mem c
  · have hEq : z = (c : S.K) := by
      calc
        z = (x : S.K) / (y : S.K) := hxy.symm
        _ = ((y : S.K) * (c : S.K)) / (y : S.K) := by
          have hmulMap : (algebraMap (S.B) S.K y) * (algebraMap (S.B) S.K c) =
              algebraMap (S.B) S.K x := congrArg (algebraMap (S.B) S.K) h
          show (algebraMap (S.B) S.K x) / (algebraMap (S.B) S.K y) =
            ((algebraMap (S.B) S.K y) * (algebraMap (S.B) S.K c)) /
              (algebraMap (S.B) S.K y)
          rw [hmulMap]
        _ = (c : S.K) := by field_simp [hyK]
    exact False.elim (hzB (hEq ▸ SetLike.coe_mem c))

private theorem exists_unit_outside_B
    (h : ¬ ∀ a : S.Aˣ, (((a : S.A) : S.K) ∈ S.R)) :
    ∃ a : S.Aˣ, (((a : S.A) : S.K) ∉ S.B) := by
  push Not at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun haB => ha (Subring.mem_inf.2 ⟨SetLike.coe_mem (a : S.A), haB⟩)⟩

private theorem dvr_pow_clears_denominator (u : S.B)
    (hu : u ∈ IsLocalRing.maximalIdeal S.B) (hu0 : (u : S.K) ≠ 0) (z : S.K) :
    ∃ n : ℕ, (u : S.K) ^ n * z ∈ S.B := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (S.B)
  have hu0B : (u : S.B) ≠ 0 := fun hz => hu0 (by simp [hz])
  obtain ⟨k, v, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := S.B) hu0B hπ
  have hk : 0 < k := pos_of_eq_unit_mul_pow hu rfl
  obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (S.B)) z
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (R := S.B) (x := b.1) (by simp) hπ
  obtain ⟨c, hc⟩ := hm.dvd.trans (pow_dvd_pow_of_dvd ((dvd_pow_self π hk.ne').mul_left _) m)
  refine ⟨m, ?_⟩
  have hcK : (b.1 : S.K) * (c : S.K) = ((↑v * π ^ k : S.B) ^ m : S.K) := by
    show (algebraMap (S.B) S.K b.1) * (algebraMap (S.B) S.K c) =
      algebraMap (S.B) S.K ((↑v * π ^ k : S.B) ^ m)
    simpa only [map_mul] using (congrArg (algebraMap (S.B) S.K) hc).symm
  change z * (b.1 : S.K) = (a : S.K) at hz
  have heq : ((a * c : S.B) : S.K) = ((↑v * π ^ k : S.B) ^ m : S.K) * z := by
    calc
      ((a * c : S.B) : S.K) = (a : S.K) * (c : S.K) := by simp
      _ = (z * (b.1 : S.K)) * (c : S.K) := by rw [hz]
      _ = z * ((b.1 : S.K) * (c : S.K)) := by ring
      _ = ((↑v * π ^ k : S.B) ^ m : S.K) * z := by rw [hcK]; ring
  rw [← heq]
  exact SetLike.coe_mem (a * c)

private theorem exists_away_A_of_unit_outside_B
    (a : S.Aˣ) (haB : (((a : S.A) : S.K) ∉ S.B)) :
    ∃ r : S.R, ∃ rB : S.B,
      rB ∈ IsLocalRing.maximalIdeal S.B ∧
      (rB : S.K) = (((a : S.A) : S.K)⁻¹) ∧
      (r : S.K) = (rB : S.K) ∧ IsLocalization.Away r S.A := by
  let z : S.K := ((a : S.A) : S.K)
  have hz : z ≠ 0 := by simp [z]
  have hrB : z⁻¹ ∈ S.B := inverse_mem_dvr_of_not_mem S z hz haB
  let rB : S.B := ⟨z⁻¹, hrB⟩
  have hrBmax : rB ∈ IsLocalRing.maximalIdeal S.B :=
    (IsLocalRing.mem_maximalIdeal rB).2 fun hu =>
      haB (by simpa [rB, z] using inv_mem_of_isUnit hu)
  have hrA0 : (((a⁻¹ : S.Aˣ) : S.A) : S.K) = z⁻¹ := coe_units_inv a
  let rA : S.A := ⟨z⁻¹, hrA0 ▸ SetLike.coe_mem ((a⁻¹ : S.Aˣ) : S.A)⟩
  let r : S.R := ⟨z⁻¹, (Subring.mem_inf).2 ⟨SetLike.coe_mem rA, hrB⟩⟩
  refine ⟨r, rB, hrBmax, rfl, rfl, ?_⟩
  refine isLocalization_away_of_injective r
    (fun _ _ h => Subtype.ext (congrArg ((↑) : S.A → S.K) h)) ?_ ?_
  · rw [show algebraMap S.R S.A r = ((a⁻¹ : S.Aˣ) : S.A) from Subtype.ext hrA0.symm]
    exact Units.isUnit (a⁻¹ : S.Aˣ)
  · intro y
    obtain ⟨n, hn⟩ := dvr_pow_clears_denominator S rB hrBmax
      (by simp [rB, z, inv_ne_zero hz]) (y : S.K)
    have hA : (rB : S.K) ^ n * (y : S.K) ∈ S.A := SetLike.coe_mem (rA ^ n * y)
    let t : S.R := ⟨(rB : S.K) ^ n * (y : S.K), (Subring.mem_inf).2 ⟨hA, hn⟩⟩
    refine ⟨n, t, ?_⟩
    apply IsFractionRing.injective (S.A) S.K
    show (y : S.K) * (z⁻¹) ^ n = (rB : S.K) ^ n * (y : S.K)
    simp [rB, z, mul_comm]

private lemma isLocalization_away_B (x : S.R) (xA : S.A) (xB : S.Bˣ)
    (hxB : ((xB : S.B) : S.K) = x) (hxA : (xA : S.K) = x)
    (hxAJac : xA ∈ Ring.jacobson S.A) : IsLocalization.Away x S.B := by
  have hxK : (xA : S.K) = ((xB : S.B) : S.K) := hxA.trans hxB.symm
  have := dimensionLEOne_A S
  refine isLocalization_away_of_injective x
    (fun _ _ h => Subtype.ext (congrArg ((↑) : S.B → S.K) h)) ?_ ?_
  · rw [show algebraMap S.R S.B x = xB from Subtype.ext hxB.symm]
    exact Units.isUnit xB
  · intro b
    obtain ⟨⟨p, d⟩, hbd⟩ := IsLocalization.surj (nonZeroDivisors S.A) (b : S.K)
    have hbd' : (b : S.K) * (d.1 : S.K) = (p : S.K) := hbd
    obtain ⟨n, hspan⟩ := Ring.exists_pow_mem_span_singleton hxAJac (nonZeroDivisors.ne_zero d.2)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hspan
    have hcK : (xA : S.K) ^ n = (d.1 : S.K) * c := by
      simpa using congrArg (fun q : S.A => (q : S.K)) hc
    have hclears : (xA : S.K) ^ n * (b : S.K) ∈ S.A := by
      rw [hcK, mul_comm (d.1 : S.K), mul_assoc, mul_comm (d.1 : S.K), hbd']
      exact SetLike.coe_mem (c * p)
    have hclearsB : (xA : S.K) ^ n * (b : S.K) ∈ S.B := by
      rw [hxK]
      exact SetLike.coe_mem ((xB : S.B) ^ n * b)
    let t : S.R := ⟨(xA : S.K) ^ n * (b : S.K), (Subring.mem_inf).2 ⟨hclears, hclearsB⟩⟩
    refine ⟨n, t, ?_⟩
    apply IsFractionRing.injective (S.B) S.K
    show (b : S.K) * (x : S.K) ^ n = (xA : S.K) ^ n * (b : S.K)
    rw [← hxA]
    ring

private theorem exists_away_B_of_unit_outside_B (a : S.Aˣ)
    (rB : S.B) (hrBmax : rB ∈ IsLocalRing.maximalIdeal S.B)
    (hrBval : (rB : S.K) = (((a : S.A) : S.K)⁻¹)) :
    ∃ x : S.R, ∃ xA : S.A, ∃ xB : S.Bˣ,
      ((xB : S.B) : S.K) = (x : S.K) ∧
      (xA : S.K) = (x : S.K) ∧ xA ∈ Ring.jacobson S.A ∧ IsLocalization.Away x S.B := by
  obtain ⟨y, hy0, hyJac⟩ := Ring.exists_ne_zero_mem_jacobson S.ringKrullDimA
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (S.B)
  have hyK0 : (y : S.K) ≠ 0 := fun h => hy0 (IsFractionRing.injective (S.A) S.K h)
  obtain ⟨m, w, hyform⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := S.B) (K := S.K) hπ hyK0
  have haK : ((a : S.A) : S.K) ≠ 0 := by simp
  have hrB0 : rB ≠ 0 := by
    intro h
    have hK : (rB : S.K) = 0 := congrArg (fun q : S.B => (q : S.K)) h
    rw [hrBval] at hK
    exact (inv_ne_zero haK) hK
  obtain ⟨k, v, hrform⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := S.B) hrB0 hπ
  have hk : 0 < k := pos_of_eq_unit_mul_pow hrBmax hrform
  let uA : S.Aˣ := a⁻¹
  have huAr : ((uA : S.A) : S.K) = (rB : S.K) := by
    rw [hrBval, coe_units_inv]
  have hyformK : (y : S.K) = (w : S.K) * (algebraMap S.B S.K π) ^ m := hyform
  have hrformK : (rB : S.K) = (v : S.K) * (algebraMap S.B S.K π) ^ (k : ℕ) :=
    congrArg (algebraMap S.B S.K) hrform
  let xA : S.A := y ^ k * ((uA ^ (-m) : S.Aˣ) : S.A)
  let xB : S.Bˣ := w ^ k * v ^ (-m)
  have huAzpow : ((uA ^ (-m) : S.Aˣ) : S.K) = (rB : S.K) ^ (-m) := by
    rw [coe_units_zpow, huAr]
  have hxBval : ((xB : S.B) : S.K) = (w : S.K) ^ k * (v : S.K) ^ (-m) := by
    dsimp [xB]
    rw [coe_units_zpow]
  have hπK : (algebraMap S.B S.K) π ≠ 0 := fun h =>
    hπ.ne_zero (IsFractionRing.injective (S.B) S.K h)
  have hxK : (xA : S.K) = ((xB : S.B) : S.K) := by
    show (y : S.K) ^ k * ((uA ^ (-m) : S.Aˣ) : S.K) = ((xB : S.B) : S.K)
    rw [hyformK, huAzpow, hrformK, hxBval]
    exact mul_zpow_mul_pow_cancel _ _ _ hπK m k
  have hxAJac : xA ∈ Ring.jacobson S.A :=
    (Ring.jacobson S.A).mul_mem_right _ ((Ring.jacobson S.A).pow_mem_of_mem hyJac k hk)
  let x : S.R := ⟨(xA : S.K), (Subring.mem_inf).2
    ⟨SetLike.coe_mem xA, hxK ▸ SetLike.coe_mem (xB : S.B)⟩⟩
  exact ⟨x, xA, xB, hxK.symm, rfl, hxAJac,
    isLocalization_away_B S x xA xB hxK.symm rfl hxAJac⟩

/-- If a unit of `A` lies outside `R`, the map from `Spec A` to `Spec R` is an open
immersion. -/
@[stacks 09N1 "unit_outside_r"]
public theorem isOpenImmersion_specMap_R_A_of_unit_not_mem_R
    (h : ¬ ∀ a : S.Aˣ, (((a : S.A) : S.K) ∈ S.R)) :
    IsOpenImmersion
      (Scheme.Spec.map
        (CommRingCat.ofHom ((S.A ⊓ S.B : Subring S.K).inclusion inf_le_left)).op) := by
  obtain ⟨a, haB⟩ := exists_unit_outside_B S h
  obtain ⟨r, -, -, -, -, hloc⟩ :=
    exists_away_A_of_unit_outside_B S a haB
  let _ : IsLocalization.Away r S.A := hloc
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization (R := S.R) (S := S.A) r

/-- If a unit of `A` lies outside `R`, the map from `Spec B` to `Spec R` is an open
immersion. -/
@[stacks 09N1 "unit_outside_r"]
public theorem isOpenImmersion_specMap_R_B_of_unit_not_mem_R
    (h : ¬ ∀ a : S.Aˣ, (((a : S.A) : S.K) ∈ S.R)) :
    IsOpenImmersion
      (Scheme.Spec.map
        (CommRingCat.ofHom ((S.A ⊓ S.B : Subring S.K).inclusion inf_le_right)).op) := by
  obtain ⟨a, haB⟩ := exists_unit_outside_B S h
  obtain ⟨-, rB, hrBmax, hrBval, -, -⟩ :=
    exists_away_A_of_unit_outside_B S a haB
  obtain ⟨x, -, -, -, -, -, hlocB⟩ :=
    exists_away_B_of_unit_outside_B S a rB hrBmax hrBval
  let _ : IsLocalization.Away x S.B := hlocB
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization (R := S.R) (S := S.B) x

/-- If a unit of `A` lies outside `R`, the images of `Spec A` and `Spec B` cover `Spec R`. -/
@[stacks 09N1 "unit_outside_r"]
public theorem range_specMap_R_A_union_R_B_of_unit_not_mem_R
    (h : ¬ ∀ a : S.Aˣ, (((a : S.A) : S.K) ∈ S.R)) :
    Set.range
        (Scheme.Spec.map
          (CommRingCat.ofHom ((S.A ⊓ S.B : Subring S.K).inclusion inf_le_left)).op).base ∪
      Set.range
        (Scheme.Spec.map
          (CommRingCat.ofHom ((S.A ⊓ S.B : Subring S.K).inclusion inf_le_right)).op).base =
      Set.univ := by
  obtain ⟨a, haB⟩ := exists_unit_outside_B S h
  obtain ⟨r, rB, hrBmax, hrBval, hrRval, hlocA⟩ :=
    exists_away_A_of_unit_outside_B S a haB
  obtain ⟨x, xA, xB, hxval, hxAVal, hxJac, hlocB⟩ :=
    exists_away_B_of_unit_outside_B S a rB hrBmax hrBval
  have hsumA : IsUnit (algebraMap S.R S.A (r + x)) := by
    have := isUnit_add_of_mem_jacobson hxJac (IsLocalization.Away.algebraMap_isUnit (S := S.A) r)
    rwa [map_add, add_comm, show algebraMap S.R S.A x = xA from Subtype.ext hxAVal.symm]
  have hsumB : IsUnit (algebraMap S.R S.B (r + x)) := by
    rw [map_add, show algebraMap S.R S.B r = rB from Subtype.ext hrRval,
      show algebraMap S.R S.B x = xB from Subtype.ext hxval.symm]
    exact IsLocalRing.notMem_maximalIdeal.mp fun hmem =>
      IsLocalRing.notMem_maximalIdeal.mpr (Units.isUnit xB)
        (by simpa using (IsLocalRing.maximalIdeal S.B).sub_mem hmem hrBmax)
  have hne : ((r + x : S.R) : S.K) ≠ 0 := fun hz => hsumA.ne_zero (Subtype.ext hz)
  have hq : ((r + x : S.R) : S.K)⁻¹ ∈ S.R :=
    Subring.mem_inf.2 ⟨inv_mem_of_isUnit hsumA, inv_mem_of_isUnit hsumB⟩
  have hsumR : IsUnit (r + x) := isUnit_iff_exists.mpr
    ⟨⟨_, hq⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩
  show Set.range (PrimeSpectrum.comap (algebraMap S.R S.A)) ∪
      Set.range (PrimeSpectrum.comap (algebraMap S.R S.B)) = Set.univ
  rw [PrimeSpectrum.localization_away_comap_range S.A r,
    PrimeSpectrum.localization_away_comap_range S.B x]
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hr : r ∈ p.asIdeal
  · exact Or.inr fun hx =>
      p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (p.asIdeal.add_mem hr hx) hsumR)
  · exact Or.inl hr

/-- If a unit of `A` lies outside `R`, multiplication identifies `A ⊗[R] B` with the
common fraction field. -/
@[stacks 09N1 "unit_outside_r"]
public theorem tensorProductTo_bijective_of_unit_not_mem_R
    (h : ¬ ∀ a : S.Aˣ, (((a : S.A) : S.K) ∈ S.R)) :
    Function.Bijective (tensorProductTo S) := by
  obtain ⟨a, haB⟩ := exists_unit_outside_B S h
  obtain ⟨r, rB, hrBmax, hrBval, hrRval, hlocA⟩ :=
    exists_away_A_of_unit_outside_B S a haB
  have hrB0 : (rB : S.K) ≠ 0 := by simp [hrBval]
  have : IsLocalization.Away rB S.K := by
    refine isLocalization_away_of_injective rB (IsFractionRing.injective S.B S.K)
      (isUnit_iff_ne_zero.mpr hrB0) ?_
    · intro z
      obtain ⟨n, hn⟩ := dvr_pow_clears_denominator S rB hrBmax hrB0 z
      let b : S.B := ⟨(rB : S.K) ^ n * z, hn⟩
      refine ⟨n, b, ?_⟩
      show z * (rB : S.K) ^ n = (b : S.K)
      simp [b, mul_comm]
  have hrmapB : algebraMap S.R S.B r = rB := Subtype.ext hrRval
  let T : Type _ := TensorProduct S.R S.A S.B
  let _ : Algebra S.B T := Algebra.TensorProduct.rightAlgebra
  let _ : IsScalarTower S.R S.B T := Algebra.TensorProduct.right_isScalarTower
  have : IsLocalization.Away rB T := by
    rw [← hrmapB]
    infer_instance
  let eTotal : T ≃ₐ[S.B] S.K :=
    IsLocalization.algEquiv (Submonoid.powers rB) T S.K
  have he : eTotal.toRingHom = tensorProductTo S := by
    apply IsLocalization.ringHom_ext (Submonoid.powers rB)
    ext b
    show eTotal (algebraMap S.B T b) = tensorProductTo S (algebraMap S.B T b)
    rw [eTotal.commutes]
    show algebraMap S.B S.K b =
      Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom S.R S.A S.K)
        (IsScalarTower.toAlgHom S.R S.B S.K) ((1 : S.A) ⊗ₜ[S.R] b)
    rw [Algebra.TensorProduct.productMap_right_apply]
    rfl
  rw [← he]
  exact eTotal.bijective

end Ring.SemilocalDVRGluingSituation
