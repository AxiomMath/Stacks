module

public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.FieldTheory.CardinalEmb
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Adjoin.Field
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.WeaklyEtale.Descent

@[expose] public section

/-!
# Shared correspondences between minimal and maximal primes

This module collects the ring-theoretic correspondences used to compute the branches of a local
ring, both from a henselization and from an adic completion. The results describe how
contraction along a base change behaves on maximal ideals and on minimal primes, when a minimal
prime below a given prime is unique, and when normality is inherited by a tensor product
presented as a filtered colimit of etale algebras or by an integral closure of a finite product.

## Main results

* `bijOn_maximalIdeals_tensorProduct`: contraction is bijective from the maximal ideals of a
  base change to those of the base, given a bijection on residue fields.
* `bijOn_minimalPrimes_integralClosure_tensorProduct`: contraction is bijective on minimal
  primes for the integral closure of a base change.
* `existsUnique_minimalPrime_le_of_isNormalRing`: a maximal ideal of a normal ring contains a
  unique minimal prime.
* `isNormalRing_tensorProduct_of_ind_etale`: a tensor product with an ind-etale algebra of a
  normal ring is normal.
* `isNormalRing_integralClosure_fractionRing_reduction`: the integral closure of a reduction in
  its total ring of fractions is normal.
-/

universe u v w

set_option maxRecDepth 4096

open Topology
open scoped TensorProduct

/-- Maximal ideals of an integral algebra over a local ring are exactly the primes over its
maximal ideal. -/
theorem isMaximal_iff_liesOver_maximalIdeal
    (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    P.IsMaximal ↔ P.LiesOver (IsLocalRing.maximalIdeal R) := by
  constructor
  · intro hP
    constructor
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) P) |>.symm
  · intro hP
    let : P.LiesOver (IsLocalRing.maximalIdeal R) := hP
    exact Ideal.IsMaximal.of_liesOver_isMaximal P (IsLocalRing.maximalIdeal R)

/-- If `S` is integral over `R`, then `S ⊗[R] T` is integral over `T`. -/
theorem integral_tensorProduct_right (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.IsIntegral R S] :
    letI : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    Algebra.IsIntegral T (S ⊗[R] T) := by
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  constructor
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s t =>
    have hs : IsIntegral T (s ⊗ₜ[R] (1 : T)) :=
      (Algebra.IsIntegral.isIntegral s).map_of_comp_eq
        (algebraMap R T) Algebra.TensorProduct.includeLeftRingHom
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
    simpa only [Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
      hs.mul (isIntegral_algebraMap (R := T) (A := S ⊗[R] T) (x := t))
  | add x y hx hy => exact hx.add hy

set_option backward.isDefEq.respectTransparency false

/-- The residue fields at the maximal ideals have the same map as the residue fields of the
local rings. In particular, a residue field isomorphism is also an isomorphism at these points. -/
theorem bijective_residueFieldAtMax_of_bijective
    (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (h : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R S))) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
        (Algebra.ofId R S) (by
          calc
            IsLocalRing.maximalIdeal R =
                (IsLocalRing.maximalIdeal S).comap (algebraMap R S) :=
              (IsLocalRing.maximalIdeal S).over_def (IsLocalRing.maximalIdeal R)
            _ = (IsLocalRing.maximalIdeal S).comap (Algebra.ofId R S).toRingHom := by
              rfl)) := by
  constructor
  · exact RingHom.injective _
  · intro y
    obtain ⟨b, rfl⟩ :=
      Ideal.algebraMap_residueField_surjective (IsLocalRing.maximalIdeal S) y
    obtain ⟨c, hc⟩ := h.2 (IsLocalRing.residue S b)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨algebraMap R (IsLocalRing.maximalIdeal R).ResidueField a, ?_⟩
    rw [Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap]
    have hb : b - algebraMap R S a ∈ IsLocalRing.maximalIdeal S := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, sub_eq_zero]
      exact hc.symm.trans (IsLocalRing.ResidueField.map_residue (algebraMap R S) a)
    have hzero := (Ideal.algebraMap_residueField_eq_zero
      (I := IsLocalRing.maximalIdeal S) (x := b - algebraMap R S a)).mpr hb
    have hbeq := sub_eq_zero.mp (by simpa only [map_sub] using hzero)
    convert hbeq.symm using 1
    rfl

/-- Swapping tensor factors identifies contraction along the left inclusion with contraction
along the right inclusion. -/
theorem comap_tensor_comm_right
    (R : Type u) (B : Type v) (C : Type w) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (P : Ideal (B ⊗[R] C)) :
    Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom
        (Ideal.comap (Algebra.TensorProduct.comm R B C).symm.toRingHom P) =
      Ideal.comap Algebra.TensorProduct.includeLeftRingHom P := by
  ext b
  change (Algebra.TensorProduct.comm R B C).symm (1 ⊗ₜ[R] b) ∈ P ↔
    b ⊗ₜ[R] (1 : C) ∈ P
  simp

/-- An integral algebra has the same maximal ideals after base change along a local map that
is an isomorphism on residue fields. -/
theorem bijOn_maximalIdeals_tensorProduct
    (R : Type u) (Rh : Type v) (B : Type w) [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh] [CommRing B]
    [Algebra R Rh] [Algebra R B] [IsLocalHom (algebraMap R Rh)]
    [Algebra.IsIntegral R B]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R Rh))) :
    Set.BijOn
      (Ideal.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] Rh))
      {P : Ideal (B ⊗[R] Rh) | P.IsMaximal} {p : Ideal B | p.IsMaximal} := by
  let : Algebra.IsIntegral Rh (Rh ⊗[R] B) := Algebra.IsIntegral.tensorProduct R Rh B
  let hF := bijective_residueFieldAtMax_of_bijective R Rh hres
  let e : B ⊗[R] Rh ≃ₐ[R] Rh ⊗[R] B := Algebra.TensorProduct.comm R B Rh
  have hq (P : Ideal (B ⊗[R] Rh)) (hP : P.IsMaximal) :
      let q := P.comap e.symm.toRingHom
      q.IsMaximal ∧ q.LiesOver (IsLocalRing.maximalIdeal Rh) := by
    let q := P.comap e.symm.toRingHom
    have hqm : q.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm.toRingHom
      e.symm.surjective
    exact ⟨hqm, (isMaximal_iff_liesOver_maximalIdeal Rh (Rh ⊗[R] B) q).mp hqm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    let q := P.comap e.symm.toRingHom
    obtain ⟨hqm, hqo⟩ := hq P hP
    let : q.IsPrime := hqm.isPrime
    let : q.LiesOver (IsLocalRing.maximalIdeal Rh) := hqo
    let Q := Ideal.fiberIsoOfBijectiveResidueField (R := R) (R' := Rh) (S := B)
      hF (⟨q, inferInstance, inferInstance⟩)
    have hQmax : (Q : Ideal B).IsMaximal := by
      exact (isMaximal_iff_liesOver_maximalIdeal R B Q.1).mpr Q.2.2
    have hQeq : (Q : Ideal B) = P.comap Algebra.TensorProduct.includeLeftRingHom :=
      (Ideal.comap_fiberIsoOfBijectiveResidueField_apply hF
        (⟨q, inferInstance, inferInstance⟩)).trans (comap_tensor_comm_right R B Rh P)
    exact hQeq ▸ hQmax
  · intro P hP Q hQ heq
    obtain ⟨hPm, hPo⟩ := hq P hP
    obtain ⟨hQm, hQo⟩ := hq Q hQ
    let : (P.comap e.symm.toRingHom).IsPrime := hPm.isPrime
    let : (Q.comap e.symm.toRingHom).IsPrime := hQm.isPrime
    let : (P.comap e.symm.toRingHom).LiesOver (IsLocalRing.maximalIdeal Rh) := hPo
    let : (Q.comap e.symm.toRingHom).LiesOver (IsLocalRing.maximalIdeal Rh) := hQo
    have hc : (P.comap e.symm.toRingHom).comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Rh ⊗[R] B).toRingHom =
        (Q.comap e.symm.toRingHom).comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] Rh ⊗[R] B).toRingHom := by
      calc
        _ = P.comap Algebra.TensorProduct.includeLeftRingHom :=
          comap_tensor_comm_right R B Rh P
        _ = Q.comap Algebra.TensorProduct.includeLeftRingHom := heq
        _ = _ := (comap_tensor_comm_right R B Rh Q).symm
    exact (Ideal.comap_injective_of_surjective e.symm.toRingHom e.symm.surjective)
      (Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hF
        (P.comap e.symm.toRingHom) (Q.comap e.symm.toRingHom) hc)
  · intro p hp
    let : p.IsPrime := hp.isPrime
    let : p.LiesOver (IsLocalRing.maximalIdeal R) :=
      (isMaximal_iff_liesOver_maximalIdeal R B p).mp hp
    let Q := (Ideal.fiberIsoOfBijectiveResidueField (R := R) (R' := Rh) (S := B) hF).symm
      (⟨p, inferInstance, inferInstance⟩)
    let P : Ideal (B ⊗[R] Rh) := Q.1.comap e.toRingHom
    have hQmax : (Q : Ideal (Rh ⊗[R] B)).IsMaximal := by
      exact (isMaximal_iff_liesOver_maximalIdeal Rh (Rh ⊗[R] B) Q.1).mpr Q.2.2
    have hPmax : P.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective
    refine ⟨P, hPmax, ?_⟩
    have hPQ : P.comap e.symm.toRingHom = Q.1 := by
      change Ideal.comap e.symm.toRingHom (Ideal.comap e.toRingHom Q.1) = Q.1
      rw [Ideal.comap_comap]
      have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
        apply RingHom.ext
        intro z
        exact e.apply_symm_apply z
      rw [he, Ideal.comap_id]
    rw [← comap_tensor_comm_right R B Rh P, hPQ]
    exact Ideal.comap_fiberIsoOfBijectiveResidueField_symm hF
      (⟨p, inferInstance, inferInstance⟩)

/-- Every prime of an integral algebra over a henselian local ring is contained in a unique
maximal ideal. -/
theorem existsUnique_maximal_of_integral_henselian
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    (q : Ideal B) (hq : q.IsPrime) :
    ∃! m : Ideal B, m.IsMaximal ∧ q ≤ m := by
  let : q.IsPrime := hq
  have hqint : (algebraMap R (B ⧸ q)).IsIntegral :=
    Algebra.IsIntegral.isIntegral
  obtain ⟨hB, _, _⟩ :=
    RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
      (algebraMap R (B ⧸ q)) hqint
  let : IsLocalRing (B ⧸ q) := hB.toIsLocalRing
  obtain ⟨m, hm, hqm⟩ := q.exists_le_maximal hq.ne_top
  refine ⟨m, ⟨hm, hqm⟩, ?_⟩
  intro n ⟨hn, hqn⟩
  have heq (p : Ideal B) (hp : p.IsMaximal) (hqp : q ≤ p) :
      p.map (Ideal.Quotient.mk q) = IsLocalRing.maximalIdeal (B ⧸ q) := by
    let : p.IsMaximal := hp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by simpa only [Ideal.mk_ker] using hqp))
  have he := congrArg (Ideal.comap (Ideal.Quotient.mk q))
    ((heq n hn hqn).trans (heq m hm hqm).symm)
  simpa only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hqn,
    sup_of_le_left hqm] using he

/-- If the localization at a prime ideal is a domain, precisely one minimal prime lies
under that prime ideal. -/
theorem existsUnique_minimalPrime_le_of_isDomain_atPrime
    (R : Type u) [CommRing R]
    (m : Ideal R) (hm : m.IsPrime)
    (hdom : IsDomain (Localization.AtPrime m)) :
    ∃! q : Ideal R, q ∈ minimalPrimes R ∧ q ≤ m := by
  let : m.IsPrime := hm
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := m) bot_le
  let : IsDomain (Localization.AtPrime m) := hdom
  let f : R →+* Localization.AtPrime m := algebraMap R (Localization.AtPrime m)
  have hunder (q : Ideal R) (hq : q.IsPrime) (hqm : q ≤ m) : (q.map f).under R = q :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ hq
      (Set.disjoint_left.mpr fun _ hx hxq => hx (hqm hxq))
  have hh (q : Ideal R) (hq : q ∈ minimalPrimes R) (hqm : q ≤ m) :
      q.map f = (⊥ : Ideal (Localization.AtPrime m)) := by
    have heq := hunder q hq.isPrime hqm
    have hmem' : q.map f ∈ ((⊥ : Ideal R).map f).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map m.primeCompl (Localization.AtPrime m)]
      simpa only [Set.mem_preimage, heq] using hq
    have hmem : q.map f ∈ minimalPrimes (Localization.AtPrime m) := by
      simpa only [Ideal.map_bot] using hmem'
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hmem
  refine ⟨q, ⟨hq, hqm⟩, ?_⟩
  intro q' ⟨hq', hq'm⟩
  have h : (q.map f).under R = (q'.map f).under R := by rw [hh q hq hqm, hh q' hq' hq'm]
  rw [hunder q hq.isPrime hqm, hunder q' hq'.isPrime hq'm] at h
  exact h.symm

/-- A maximal ideal of a normal ring contains exactly one minimal prime. -/
theorem existsUnique_minimalPrime_le_of_isNormalRing
    (R : Type u) [CommRing R] (hR : IsNormalRing R)
    (m : Ideal R) (hm : m.IsMaximal) :
    ∃! q : Ideal R, q ∈ minimalPrimes R ∧ q ≤ m := by
  let : m.IsPrime := hm.isPrime
  exact existsUnique_minimalPrime_le_of_isDomain_atPrime R m hm.isPrime
    (hR m).1

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The `R'`-algebra isomorphism `R' ⊗[R] colim G i ≃ colim (R' ⊗[R] G i)` expressing that base
change commutes with directed colimits of `R`-algebras. -/
noncomputable def directLimitTensorProductAlgEquiv
    {R : Type u} {R' : Type w} [CommRing R] [CommRing R'] [Algebra R R']
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₐ[R] G j)
    [Algebra R (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j))]
    [Algebra R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    [Algebra R (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    [IsScalarTower R R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
      fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _))]
    (hof : ∀ (i : ι) (r : R),
      Ring.DirectLimit.of G (fun i j h ↦ (f i j h : G i → G j)) i (algebraMap R (G i) r)
        = algebraMap R (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j)) r)
    (hof' : ∀ (i : ι) (r : R'),
      Ring.DirectLimit.of (fun i ↦ TensorProduct R R' (G i))
          (fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)) i
          (algebraMap R' (TensorProduct R R' (G i)) r)
        = algebraMap R' (Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
          fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)) r)
    (i₀ : ι) :
    TensorProduct R R' (Ring.DirectLimit G fun i j h ↦ (f i j h : G i → G j))
      ≃ₐ[R'] Ring.DirectLimit (fun i ↦ TensorProduct R R' (G i))
        fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _) := by
  haveI : Nonempty ι := ⟨i₀⟩
  let f₀ : (i j : ι) → i ≤ j → G i → G j := fun i j h ↦ (f i j h : G i → G j)
  let G' : ι → Type _ := fun i ↦ TensorProduct R R' (G i)
  let f'₀ : (i j : ι) → i ≤ j → G' i → G' j :=
    fun i j h ↦ (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j h) : _ → _)
  let L : Type _ := Ring.DirectLimit G f₀
  let L' : Type _ := Ring.DirectLimit G' f'₀
  change TensorProduct R R' L ≃ₐ[R'] L'
  let ofAlg : (i : ι) → G i →ₐ[R] L := fun i =>
    { Ring.DirectLimit.of G f₀ i with
      commutes' := fun r => hof i r }
  let ofAlg' : (i : ι) → G' i →ₐ[R'] L' := fun i =>
    { Ring.DirectLimit.of G' f'₀ i with
      commutes' := fun r => hof' i r }
  let gComp : (i : ι) → G i →+* L' := fun i =>
    ((ofAlg' i).restrictScalars R).comp Algebra.TensorProduct.includeRight |>.toRingHom
  have hgComp : ∀ (i j : ι) (hij : i ≤ j) (x : G i),
      gComp j (f₀ i j hij x) = gComp i x := by
    intro i j hij x
    simp only [gComp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply]
    have hmap : f'₀ i j hij (1 ⊗ₜ[R] x) = (1 : R') ⊗ₜ[R] (f i j hij x) := by
      change Algebra.TensorProduct.map (AlgHom.id R' R') (f i j hij) (1 ⊗ₜ[R] x)
          = (1 : R') ⊗ₜ[R] (f i j hij x)
      rw [Algebra.TensorProduct.map_tmul]; simp
    change Ring.DirectLimit.of G' f'₀ j ((1 : R') ⊗ₜ[R] (f i j hij x))
        = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] x)
    rw [← hmap]
    exact Ring.DirectLimit.of_f hij _
  let gRing : L →+* L' := Ring.DirectLimit.lift G f₀ L' gComp hgComp
  have htmul_alg : ∀ (i : ι) (r : R),
      (1 : R') ⊗ₜ[R] (algebraMap R (G i) r) = algebraMap R' (G' i) (algebraMap R R' r) := by
    intro i r
    have hL : (1 : R') ⊗ₜ[R] (algebraMap R (G i) r) = algebraMap R (G' i) r := by
      rw [← Algebra.TensorProduct.includeRight_apply]
      exact (Algebra.TensorProduct.includeRight).commutes r
    rw [hL, ← IsScalarTower.algebraMap_apply R R' (G' i)]
  have hgRing_comm : ∀ r : R, gRing (algebraMap R L r) = algebraMap R L' r := by
    intro r
    have h1 : algebraMap R L r = Ring.DirectLimit.of G f₀ i₀ (algebraMap R (G i₀) r) :=
      (hof i₀ r).symm
    rw [h1]
    change Ring.DirectLimit.lift G f₀ L' gComp hgComp
        (Ring.DirectLimit.of G f₀ i₀ (algebraMap R (G i₀) r)) = algebraMap R L' r
    rw [Ring.DirectLimit.lift_of]
    change ofAlg' i₀ (Algebra.TensorProduct.includeRight (algebraMap R (G i₀) r)) = algebraMap R L'
        r
    rw [Algebra.TensorProduct.includeRight_apply, htmul_alg i₀ r]
    change Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) (algebraMap R R' r)) = algebraMap R
        L' r
    rw [hof' i₀ (algebraMap R R' r)]
    exact (IsScalarTower.algebraMap_apply R R' L' r).symm
  let gAlg : L →ₐ[R] L' :=
    { gRing with commutes' := hgRing_comm }
  let Φ : TensorProduct R R' L →ₐ[R'] L' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' L') gAlg
      (fun x y => mul_comm _ _)
  let ψComp : (i : ι) → G' i →+* TensorProduct R R' L := fun i =>
    (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i)).toRingHom
  have hψComp : ∀ (i j : ι) (hij : i ≤ j) (x : G' i),
      ψComp j (f'₀ i j hij x) = ψComp i x := by
    intro i j hij x
    simp only [ψComp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    change Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg j)
        (Algebra.TensorProduct.map (AlgHom.id R' R') (f i j hij) x)
        = Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i) x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      show ofAlg j (f i j hij b) = ofAlg i b
      change Ring.DirectLimit.of G f₀ j (f₀ i j hij b) = Ring.DirectLimit.of G f₀ i b
      exact Ring.DirectLimit.of_f hij _
    | add x y hx hy => simp only [map_add, hx, hy]
  let ψRing : L' →+* TensorProduct R R' L :=
    Ring.DirectLimit.lift G' f'₀ (TensorProduct R R' L) ψComp hψComp
  have hψRing_comm : ∀ r : R', ψRing (algebraMap R' L' r) = algebraMap R' (TensorProduct R R'
      L) r := by
    intro r
    have h1 : algebraMap R' L' r
        = Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) r) := (hof' i₀ r).symm
    rw [h1]
    change ψRing (Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) r))
        = algebraMap R' (TensorProduct R R' L) r
    change Ring.DirectLimit.lift G' f'₀ (TensorProduct R R' L) ψComp hψComp
        (Ring.DirectLimit.of G' f'₀ i₀ (algebraMap R' (G' i₀) r))
        = algebraMap R' (TensorProduct R R' L) r
    rw [Ring.DirectLimit.lift_of]
    change (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i₀)) (algebraMap R' (G' i₀) r)
        = algebraMap R' (TensorProduct R R' L) r
    rw [AlgHom.commutes]
  let Ψ : L' →ₐ[R'] TensorProduct R R' L :=
    { ψRing with commutes' := hψRing_comm }
  have hΨ_of : ∀ (i : ι) (w : G' i),
      Ψ (Ring.DirectLimit.of G' f'₀ i w) = ψComp i w := by
    intro i w
    change ψRing (Ring.DirectLimit.of G' f'₀ i w) = ψComp i w
    exact Ring.DirectLimit.lift_of _ _ _ _ _
  have hΦ_tmul : ∀ (r' : R') (x : L),
      Φ (r' ⊗ₜ[R] x) = algebraMap R' L' r' * gAlg x := by
    intro r' x
    change Algebra.TensorProduct.lift (Algebra.ofId R' L') gAlg _ (r' ⊗ₜ[R] x)
        = algebraMap R' L' r' * gAlg x
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hgAlg_of : ∀ (i : ι) (y : G i),
      gAlg (ofAlg i y) = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y) := by
    intro i y
    change gRing (Ring.DirectLimit.of G f₀ i y) = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y)
    change Ring.DirectLimit.lift G f₀ L' gComp hgComp (Ring.DirectLimit.of G f₀ i y)
        = Ring.DirectLimit.of G' f'₀ i ((1 : R') ⊗ₜ[R] y)
    rw [Ring.DirectLimit.lift_of]
    change ofAlg' i (Algebra.TensorProduct.includeRight y) = Ring.DirectLimit.of G' f'₀ i ((1 :
        R') ⊗ₜ[R] y)
    rw [Algebra.TensorProduct.includeRight_apply]
    rfl
  refine AlgEquiv.ofAlgHom Φ Ψ ?_ ?_
  · apply AlgHom.ext
    intro z
    change Φ (Ψ z) = z
    induction z using Ring.DirectLimit.induction_on with
    | ih i w =>
      rw [hΨ_of i w]
      change Φ (Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i) w)
          = Ring.DirectLimit.of G' f'₀ i w
      induction w using TensorProduct.inductionOn with
      | tmul r' y =>
        rw [Algebra.TensorProduct.map_tmul]
        simp only [AlgHom.id_apply]
        rw [hΦ_tmul, hgAlg_of]
        rw [← hof' i r']
        rw [← map_mul]
        congr 1
        change algebraMap R' (G' i) r' * ((1 : R') ⊗ₜ[R] y) = r' ⊗ₜ[R] y
        rw [Algebra.TensorProduct.algebraMap_apply]
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
      | add w₁ w₂ hw₁ hw₂ => rw [map_add, map_add, map_add, hw₁, hw₂]
  · apply AlgHom.ext
    intro z
    change Ψ (Φ z) = z
    induction z using TensorProduct.inductionOn with
    | tmul r' x =>
      rw [hΦ_tmul]
      induction x using Ring.DirectLimit.induction_on with
      | ih i y =>
        change Ψ (algebraMap R' L' r' * gAlg (ofAlg i y)) = r' ⊗ₜ[R] (ofAlg i y)
        rw [hgAlg_of]
        rw [← hof' i r', ← map_mul]
        have hmul : algebraMap R' (G' i) r' * ((1 : R') ⊗ₜ[R] y) = r' ⊗ₜ[R] y := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        rw [hmul, hΨ_of i (r' ⊗ₜ[R] y)]
        change Algebra.TensorProduct.map (AlgHom.id R' R') (ofAlg i) (r' ⊗ₜ[R] y) = r' ⊗ₜ[R]
            (ofAlg i y)
        rw [Algebra.TensorProduct.map_tmul]
        rfl
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 0 in
-- The two direct-limit presentations require substantial typeclass normalization.
/-- If `N ⊗[R] F i` is normal for every `i` of a directed diagram `F` of `R`-algebras, then
`N ⊗[R] c.pt` is normal for a colimit cocone `c` of `F`. -/
theorem isNormalRing_tensorProduct_of_isColimit_directed
    {R : Type u} [CommRing R] (N : Type w) [CommRing N] [Algebra R N] {ι : Type v} [PartialOrder ι]
    [IsDirectedOrder ι] [Nonempty ι] (F : ι ⥤ CommAlgCat.{v} R)
    (c : Cocone F) (hc : IsColimit c) (hn : ∀ i, IsNormalRing (N ⊗[R] F.obj i)) :
    IsNormalRing (N ⊗[R] c.pt) := by
  classical
  let G : ι → Type v := fun i => F.obj i
  let f : ∀ i j, i ≤ j → G i →ₐ[R] G j :=
    fun i j hij => (F.map (homOfLE hij)).hom
  let hsys : DirectedSystem G (fun i j h => f i j h) :=
    { map_self := fun i x => by
        change (F.map (𝟙 i)).hom x = x
        rw [F.map_id]
        rfl
      map_map := fun i j k hij hjk x => by
        change (F.map (homOfLE hij) ≫ F.map (homOfLE hjk)).hom x = _
        rw [← F.map_comp]
        rfl }
  let D := Ring.DirectLimit G (fun i j h => f i j h)
  let i₀ : ι := Classical.choice inferInstance
  let : Algebra R D :=
    ((Ring.DirectLimit.of G (fun i j h => f i j h) i₀).comp
      (algebraMap R (G i₀))).toAlgebra
  have hcomm (i : ι) (r : R) :
      Ring.DirectLimit.of G (fun i j h => f i j h) i (algebraMap R (G i) r) =
        algebraMap R D r := by
    obtain ⟨j, hij, h₀j⟩ := exists_ge_ge i i₀
    change _ = Ring.DirectLimit.of G (fun i j h => f i j h) i₀ _
    rw [← Ring.DirectLimit.of_f (f := fun i j h => f i j h) hij,
      ← Ring.DirectLimit.of_f (f := fun i j h => f i j h) h₀j]
    congr 1
    exact ((F.map (homOfLE hij)).hom.commutes r).trans
      ((F.map (homOfLE h₀j)).hom.commutes r).symm
  let d : Cocone F :=
    { pt := CommAlgCat.of R D
      ι.app i := CommAlgCat.ofHom
        { __ := Ring.DirectLimit.of G (fun i j h => f i j h) i
          commutes' := hcomm i }
      ι.naturality i j hij := by
        ext x
        exact Ring.DirectLimit.of_f (G := G) (f := fun i j h => f i j h) (leOfHom hij) x }
  let l : D →+* c.pt :=
    Ring.DirectLimit.lift G (fun i j h => f i j h) c.pt
      (fun i => (c.ι.app i).hom.toRingHom)
      (fun i j hij x => ConcreteCategory.congr_hom (c.w (homOfLE hij)) x)
  have hl (i : ι) (x : G i) :
      l (Ring.DirectLimit.of G (fun i j h => f i j h) i x) = (c.ι.app i).hom x :=
    Ring.DirectLimit.lift_of ..
  let la : D →ₐ[R] c.pt :=
    { __ := l
      commutes' := fun r => (hl i₀ _).trans ((c.ι.app i₀).hom.commutes r) }
  let m : c.pt →ₐ[R] D := (hc.desc d).hom
  have hm (i : ι) (x : G i) :
      m ((c.ι.app i).hom x) = Ring.DirectLimit.of G (fun i j h => f i j h) i x :=
    ConcreteCategory.congr_hom (hc.fac d i) x
  have hlm : la.comp m = AlgHom.id R c.pt := by
    change (CommAlgCat.ofHom (la.comp m)).hom =
      (CommAlgCat.ofHom (AlgHom.id R c.pt)).hom
    apply congrArg CommAlgCat.Hom.hom
    apply hc.hom_ext
    intro i
    ext x
    change l (m ((c.ι.app i).hom x)) = (c.ι.app i).hom x
    rw [hm, hl]
  have hml : m.toRingHom.comp l = RingHom.id D := by
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change m (l (Ring.DirectLimit.of G (fun i j h => f i j h) i x)) = _
    rw [hl, hm]
    rfl
  let e : D ≃+* c.pt := RingEquiv.ofRingHom l m.toRingHom
    (congrArg AlgHom.toRingHom hlm) hml
  let ea : D ≃ₐ[R] c.pt := { e with commutes' := la.commutes }
  let G' : ι → Type _ := fun i => TensorProduct R N (G i)
  let f' : (i j : ι) → i ≤ j → G' i →ₐ[N] G' j :=
    fun i j h => Algebra.TensorProduct.map (AlgHom.id N N) (f i j h)
  let f'₀ : (i j : ι) → i ≤ j → G' i → G' j := fun i j h => (f' i j h : G' i → G' j)
  have hsys' : DirectedSystem G' f'₀ := by
    constructor
    · intro i x
      change Algebra.TensorProduct.map (AlgHom.id N N) (f i i (le_refl i)) x = x
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul]
        simp only [AlgHom.id_apply]
        congr 1
        exact hsys.map_self b
      | add x y hx hy => simp only [map_add, hx, hy]
    · intro i j k hij hjk x
      change Algebra.TensorProduct.map (AlgHom.id N N) (f j i hjk)
          (Algebra.TensorProduct.map (AlgHom.id N N) (f k j hij) x)
          = Algebra.TensorProduct.map (AlgHom.id N N) (f k i (le_trans hij hjk)) x
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        congr 1
        exact hsys.map_map hij hjk b
      | add x y hx hy => simp only [map_add, hx, hy]
  let L' : Type _ := Ring.DirectLimit G' f'₀
  have hf'_alg : ∀ (i j : ι) (h : i ≤ j) (r : N),
      f'₀ i j h (algebraMap N (G' i) r) = algebraMap N (G' j) r := by
    intro i j h r
    exact (f' i j h).commutes r
  have hof_eq : ∀ (i j : ι) (r : N),
      Ring.DirectLimit.of G' f'₀ i (algebraMap N (G' i) r)
        = Ring.DirectLimit.of G' f'₀ j (algebraMap N (G' j) r) := by
    intro i j r
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    have key (i k : ι) (hik : i ≤ k) :
        Ring.DirectLimit.of G' f'₀ i (algebraMap N (G' i) r)
          = Ring.DirectLimit.of G' f'₀ k (algebraMap N (G' k) r) := by
      rw [← hf'_alg i k hik r]
      exact (Ring.DirectLimit.of_f hik _).symm
    rw [key i k hik, key j k hjk]
  let algNL' : N →+* L' :=
    (Ring.DirectLimit.of G' f'₀ i₀).comp (algebraMap N (G' i₀))
  let instAlgL' : Algebra N L' := algNL'.toAlgebra
  have hof' : ∀ (i : ι) (r : N),
      Ring.DirectLimit.of G' f'₀ i (algebraMap N (G' i) r) = algebraMap N L' r := by
    intro i r
    change Ring.DirectLimit.of G' f'₀ i (algebraMap N (G' i) r)
        = algNL' r
    simp only [algNL']
    exact hof_eq i i₀ r
  let : Algebra R L' := ((algebraMap N L').comp (algebraMap R N)).toAlgebra
  have : IsScalarTower R N L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let et : (N ⊗[R] D) ≃ₐ[N] L' := directLimitTensorProductAlgEquiv G f hcomm hof' i₀
  have hnorm : IsNormalRing L' :=
    directLimit_isNormalRing G' (fun i j h => (f' i j h).toRingHom) hsys' hn
  exact IsNormalRing.congr
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : N ≃ₐ[N] N) ea).toRingEquiv)
    (IsNormalRing.congr et.symm.toRingEquiv hnorm)

/-- If `N ⊗[R] F i` is normal for every `i` of a filtered diagram `F` of `R`-algebras, then
`N ⊗[R] c.pt` is normal for a colimit cocone `c` of `F`. -/
theorem isNormalRing_tensorProduct_of_isColimit
    {R : Type u} [CommRing R] (N : Type w) [CommRing N] [Algebra R N]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{v} R) (c : Cocone F) (hc : IsColimit c)
    (hn : ∀ i, IsNormalRing (N ⊗[R] F.obj i)) : IsNormalRing (N ⊗[R] c.pt) := by
  obtain ⟨ι, _, _, _, p, hp⟩ := IsFiltered.exists_directed J
  let := hp
  exact isNormalRing_tensorProduct_of_isColimit_directed N (p ⋙ F) (c.whisker p)
    ((Functor.Final.isColimitWhiskerEquiv p c).symm hc) (fun i => hn (p.obj i))

/-- If `N` is a normal `R`-algebra and `S` is an ind-étale `R`-algebra, then `N ⊗[R] S` is
normal. -/
theorem isNormalRing_tensorProduct_of_ind_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (N : Type w) [CommRing N] [Algebra R N] (hN : IsNormalRing N)
    (hind : (CommAlgCat.etale.{v} R).ind.{v} (CommAlgCat.of R S)) :
    IsNormalRing (N ⊗[R] S) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  apply isNormalRing_tensorProduct_of_isColimit N pres.diag pres.cocone pres.isColimit
  intro j
  let : Algebra.Etale R (pres.diag.obj j) := hpres j
  exact Algebra.isNormalRing_of_smooth N (N ⊗[R] pres.diag.obj j) hN

/-- An element of a finite product of `R`-algebras is integral over `R` if and only if each of
its components is. -/
theorem isIntegral_pi_iff_of_finite
    (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
    (K : ι → Type w) [∀ i, CommRing (K i)] [∀ i, Algebra R (K i)] (x : ∀ i, K i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  classical
  constructor
  · intro h i
    exact h.map (Pi.evalAlgHom R K i)
  · intro h
    let := Fintype.ofFinite ι
    choose p hp hz using h
    refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ (fun i _ => hp i), ?_⟩
    apply funext
    intro i
    change (Pi.evalAlgHom R K i) (Polynomial.aeval x (∏ j, p j)) = 0
    rw [← Polynomial.aeval_algHom_apply]
    simp only [Pi.evalAlgHom_apply, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i)

/-- The integral closure of `R` in a finite product of fields is a normal ring. -/
theorem isNormalRing_integralClosure_pi
    (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra R (K i)] :
    IsNormalRing (integralClosure R (∀ i, K i)) := by
  let f : integralClosure R (∀ i, K i) →ₐ[R] (∀ i, integralClosure R (K i)) :=
    { toFun := fun x i => ⟨x.1 i, (isIntegral_pi_iff_of_finite R K x.1).mp x.2 i⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact funext fun i => congrArg Subtype.val (congrFun h i)
    · intro y
      exact ⟨⟨fun i => (y i).1,
        (isIntegral_pi_iff_of_finite R K _).mpr (fun i => (y i).2)⟩, rfl⟩
  apply IsNormalRing.congr (AlgEquiv.ofBijective f hf).symm.toRingEquiv
  apply isNormalRing_pi
  intro i
  have : IsIntegrallyClosed (integralClosure R (K i)) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (R := integralClosure R (K i))
      (S := K i)
  intro p hp
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (R := integralClosure R (K i))
    (Localization.AtPrime p) p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

/-- If `A` has finitely many minimal primes, then so does its reduction `A ⧸ nilradical A`. -/
theorem finite_minimalPrimes_quotient_nilradical
    (A : Type u) [CommRing A] (hmin : (minimalPrimes A).Finite) :
    (minimalPrimes (A ⧸ nilradical A)).Finite := by
  apply Set.Finite.of_finite_image (f := Ideal.comap (Ideal.Quotient.mk (nilradical A)))
  · rw [← Ideal.minimalPrimes_eq_comap]
    simpa [nilradical, Ideal.radical_minimalPrimes, minimalPrimes] using hmin
  · exact (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn

/-- If `A` has finitely many minimal primes, then the integral closure of `A` in the total ring
of fractions of `A ⧸ nilradical A` is a normal ring. -/
theorem isNormalRing_integralClosure_fractionRing_reduction
    (A : Type u) [CommRing A] (hmin : (minimalPrimes A).Finite) :
    IsNormalRing (integralClosure A (FractionRing (A ⧸ nilradical A))) := by
  classical
  let R := A ⧸ nilradical A
  let : IsReduced R := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have hR : (minimalPrimes R).Finite := finite_minimalPrimes_quotient_nilradical A hmin
  let : Finite (minimalPrimes R) := hR
  let (p : minimalPrimes R) : p.1.IsPrime := p.2.isPrime
  let K (p : minimalPrimes R) := @Localization.AtPrime R _ p.1 p.2.isPrime
  let (p : minimalPrimes R) : Field (K p) :=
    (isField_localizationAtPrime_of_minimal R p.1 p.2).toField
  let : IsLocalization (nonZeroDivisors R) (∀ p, K p) :=
    isLocalization_pi_localization_atPrime (fun p : minimalPrimes R => p.1)
      (fun p => p.2) Subtype.val_injective (fun p hp => ⟨⟨p, hp⟩, rfl⟩)
  let e : FractionRing R ≃ₐ[A] (∀ p, K p) :=
    (IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) (∀ p, K p)).restrictScalars A
  let e' : integralClosure A (FractionRing R) ≃ₐ[A] integralClosure A (∀ p, K p) :=
    ((integralClosure A (FractionRing R)).equivMapOfInjective e.toAlgHom e.injective).trans
      (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  exact IsNormalRing.congr e'.symm.toRingEquiv (isNormalRing_integralClosure_pi A K)

/-- If `S` is a localization of `R` with injective algebra map, then contraction is a bijection
from the minimal primes of `S` to those of `R`. -/
theorem bijOn_minimalPrimes_of_injective_localization
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (hi : Function.Injective (algebraMap R S)) :
    Set.BijOn (Ideal.comap (algebraMap R S)) (minimalPrimes S) (minimalPrimes R) := by
  have he : minimalPrimes R = Ideal.comap (algebraMap R S) '' minimalPrimes S := by
    rw [← IsLocalization.minimalPrimes_comap M S, Ideal.comap_bot_of_injective _ hi]
  rw [he]
  exact (Function.LeftInverse.injective (IsLocalization.map_under M S)).injOn.bijOn_image

/-- A subalgebra of an injective localization gives the same minimal primes after any flat
base change. -/
theorem bijOn_minimalPrimes_tensorProduct_subalgebra_localization
    (R : Type u) (Q : Type v) (C : Type w) [CommRing R] [CommRing Q] [CommRing C]
    [Algebra R Q] [Algebra R C] [Module.Flat R C]
    (M : Submonoid R) [IsLocalization M Q]
    (hM : M ≤ nonZeroDivisors R) (B : Subalgebra R Q) :
    Set.BijOn
      (Ideal.comap (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C).toRingHom)
      (minimalPrimes (B ⊗[R] C)) (minimalPrimes C) := by
  let T := B ⊗[R] C
  let U := Q ⊗[R] C
  let f : T →ₐ[R] U := Algebra.TensorProduct.map B.val (AlgHom.id R C)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := C) B.val.toLinearMap
      Subtype.val_injective
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let : Algebra C U := Algebra.TensorProduct.rightAlgebra
  let : Algebra T U := f.toRingHom.toAlgebra
  have hcomp : (algebraMap T U).comp (algebraMap C T) = algebraMap C U := by
    ext c
    change f (1 ⊗ₜ[R] c) = 1 ⊗ₜ[R] c
    exact (Algebra.TensorProduct.map_tmul B.val (AlgHom.id R C) (1 : B) c).trans (by simp)
  let : IsScalarTower C T U := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let MC : Submonoid C := M.map (algebraMap R C)
  let MT : Submonoid T := MC.map (algebraMap C T)
  have hMC : MC ≤ nonZeroDivisors C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    exact (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C) (hM hx)).right_eq_zero_of_smul
      (by simpa only [Algebra.smul_def, mul_comm] using hc)
  let : IsLocalization MC U := IsLocalization.tensorRight (A := Q) (S := C) M
  have hiC : Function.Injective (algebraMap C U) := IsLocalization.injective U hMC
  let : IsLocalization MT U :=
    { map_units := by
        rintro ⟨_, c, hc, rfl⟩
        rw [← IsScalarTower.algebraMap_apply C T U]
        exact IsLocalization.map_units U (⟨c, hc⟩ : MC)
      surj := by
        intro z
        obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj MC z
        refine ⟨⟨algebraMap C T c, ⟨algebraMap C T s, s, s.2, rfl⟩⟩, ?_⟩
        simpa only [Subtype.coe_mk, ← IsScalarTower.algebraMap_apply C T U] using hs
      exists_of_eq := by
        intro x y hxy
        refine ⟨1, ?_⟩
        change (1 : T) * x = (1 : T) * y
        simpa only [one_mul] using hf hxy }
  have hT := bijOn_minimalPrimes_of_injective_localization T U MT hf
  have hC := bijOn_minimalPrimes_of_injective_localization C U MC hiC
  have hc (q : Ideal U) : (q.comap (algebraMap T U)).comap (algebraMap C T) =
      q.comap (algebraMap C U) := by rw [Ideal.comap_comap, hcomp]
  change Set.BijOn (Ideal.comap (algebraMap C T)) (minimalPrimes T) (minimalPrimes C)
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hT.surjOn hp
    rw [hc]
    exact hC.mapsTo hq
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := hT.surjOn hp
    obtain ⟨q', hq', rfl⟩ := hT.surjOn hq
    exact congrArg _ (hC.injOn hp' hq' (by simpa only [hc] using hpq))
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hC.surjOn hp
    exact ⟨q.comap (algebraMap T U), hT.mapsTo hq, hc q⟩

/-- A quotient by a nil ideal induces a bijection on minimal primes. -/
theorem bijOn_minimalPrimes_of_surjective_of_ker_le_nilradical
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R) :
    Set.BijOn (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) := by
  have hrad : (RingHom.ker f).radical = nilradical R := by
    apply le_antisymm
    · exact (Ideal.radical_mono hker).trans_eq (Ideal.radical_idem _)
    · exact Ideal.radical_mono bot_le
  have he : minimalPrimes R = Ideal.comap f '' minimalPrimes S := by
    rw [← Ideal.comap_minimalPrimes_eq_of_surjective hf,
      ← RingHom.ker_eq_comap_bot, ← Ideal.radical_minimalPrimes, hrad]
    exact Ideal.radical_minimalPrimes.symm
  rw [he]
  exact (Ideal.comap_injective_of_surjective f hf).injOn.bijOn_image

/-- A ring isomorphism induces, by contraction, a bijection on minimal primes. -/
theorem bijOn_minimalPrimes_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Set.BijOn (Ideal.comap e.toRingHom) (minimalPrimes S) (minimalPrimes R) := by
  apply bijOn_minimalPrimes_of_surjective_of_ker_le_nilradical e.toRingHom e.surjective
  intro x hx
  have hx0 : x = 0 := e.injective (hx.trans (map_zero e).symm)
  simp [hx0]

/-- Contraction along `C → (A ⧸ nilradical A) ⊗[A] C` is a bijection on minimal primes. -/
theorem bijOn_minimalPrimes_reduction_tensorProduct
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C] :
    Set.BijOn
      (Ideal.comap (Algebra.TensorProduct.includeRight :
        C →ₐ[A] (A ⧸ nilradical A) ⊗[A] C).toRingHom)
      (minimalPrimes ((A ⧸ nilradical A) ⊗[A] C)) (minimalPrimes C) := by
  let Cred := C ⧸ nilradical C
  let g : (A ⧸ nilradical A) →ₐ[A] Cred :=
    Ideal.Quotient.liftₐ (nilradical A) (Algebra.ofId A Cred) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact mem_nilradical.mpr ((mem_nilradical.mp ha).map (algebraMap A C)))
  let l : ((A ⧸ nilradical A) ⊗[A] C) →ₐ[A] Cred :=
    Algebra.TensorProduct.lift g (Ideal.Quotient.mkₐ A (nilradical C)) (fun _ _ => Commute.all _ _)
  apply bijOn_minimalPrimes_of_surjective_of_ker_le_nilradical
  · exact Algebra.TensorProduct.includeRight_surjective C Ideal.Quotient.mk_surjective
  · intro c hc
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := congrArg l hc
    change l (1 ⊗ₜ[A] c) = l 0 at hh
    have heval : l (1 ⊗ₜ[A] c) = Ideal.Quotient.mk (nilradical C) c := by
      exact (Algebra.TensorProduct.lift_tmul g (Ideal.Quotient.mkₐ A (nilradical C))
        (fun _ _ => Commute.all _ _) 1 c).trans (by rw [map_one, one_mul]; rfl)
    exact heval.symm.trans (hh.trans (map_zero l))

/-- For an integral extension `A → R` and an `R`-algebra `Q`, the integral closure of `A` in `Q`
equals, as an `A`-algebra, the integral closure of `R` in `Q`. -/
noncomputable def integralClosureRestrictScalarsEquiv
    (A : Type u) (R : Type v) (Q : Type w) [CommRing A] [CommRing R] [CommRing Q]
    [Algebra A R] [Algebra R Q] [Algebra A Q] [IsScalarTower A R Q]
    [Algebra.IsIntegral A R] :
    integralClosure A Q ≃ₐ[A] (integralClosure R Q) where
  toFun x := ⟨x.1, x.2.tower_top⟩
  invFun x := ⟨x.1, isIntegral_trans (A := R) x.1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

set_option maxHeartbeats 400000 in
-- Fixing the ring structures avoids expensive normalization of localization instances.
/-- Flat base change of normalization induces a bijection on minimal primes. -/
theorem bijOn_minimalPrimes_integralClosure_tensorProduct
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C] [Module.Flat A C] :
    Set.BijOn
      (Ideal.comap (Algebra.TensorProduct.includeRight : C →ₐ[A]
        integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] C).toRingHom)
      (minimalPrimes (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] C))
      (minimalPrimes C) := by
  let R := A ⧸ nilradical A
  let : CommRing R := inferInstance
  let Q := FractionRing R
  let : CommRing Q := inferInstance
  let B := integralClosure R Q
  let : CommRing B := inferInstance
  let B' := integralClosure A Q
  let : CommRing B' := inferInstance
  let D := R ⊗[A] C
  let : CommRing D := inferInstance
  let T := B ⊗[R] D
  let : CommRing T := inferInstance
  let T' := B' ⊗[A] C
  let : CommRing T' := inferInstance
  let eB : B' ≃ₐ[A] B := integralClosureRestrictScalarsEquiv A R Q
  let e : T ≃ₐ[A] T' :=
    ((Algebra.TensorProduct.cancelBaseChange A R R B C).restrictScalars A).trans
      (Algebra.TensorProduct.congr eB.symm (AlgEquiv.refl : C ≃ₐ[A] C))
  have he := bijOn_minimalPrimes_ringEquiv e.toRingEquiv
  have hD := bijOn_minimalPrimes_reduction_tensorProduct A C
  have hT := bijOn_minimalPrimes_tensorProduct_subalgebra_localization R Q D
    (nonZeroDivisors R) le_rfl B
  have h := hD.comp (hT.comp he)
  have hcomp : e.toRingHom.comp
      ((Algebra.TensorProduct.includeRight : D →ₐ[R] T).toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[A] D).toRingHom) =
      (Algebra.TensorProduct.includeRight : C →ₐ[A] T').toRingHom := by
    ext c
    change e (1 ⊗ₜ[R] (1 ⊗ₜ[A] c)) = 1 ⊗ₜ[A] c
    have he1 : (Algebra.TensorProduct.cancelBaseChange A R R B C)
        ((1 : B) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] c)) = (1 : B) ⊗ₜ[A] c :=
      (Algebra.TensorProduct.cancelBaseChange_tmul A R R B C 1 1 c).trans
        (by rw [one_smul])
    dsimp only [e, AlgEquiv.trans_apply, AlgEquiv.coe_restrictScalars]
    rw [he1, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  convert h using 1
  funext p
  change p.comap _ = ((p.comap _).comap _).comap _
  rw [Ideal.comap_comap, Ideal.comap_comap, hcomp]

end
