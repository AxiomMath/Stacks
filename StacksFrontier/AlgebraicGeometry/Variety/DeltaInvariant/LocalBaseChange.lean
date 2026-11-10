module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.IntegralClosure.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# Flat local base change of the normalization of a one-dimensional local ring

A reduced one-dimensional Nagata local ring `A` has a single element of its maximal ideal that
realizes the total ring of fractions as a localization away from it, both before and after
passing to the integral closure. For every flat local base change `A → B` of the same kind
for which that element still cuts out the closed point, the same element realizes the total ring
of fractions of `B`, and the base-changed integral closure embeds in it compatibly with both
tensor factors. That base-changed integral closure is moreover a normal ring whenever `B` is
a henselization of a reduced Noetherian local ring `A`.

## Main results

* `IsLocalRing.exists_common_fractionRing_localization_and_injective_tensorProduct` supplies
  the common element, its two localization properties, and the compatible embedding after base
  change.
* `IsLocalRing.isNormalRing_tensorProduct_integralClosure_of_isHenselization` proves
  normality of the integral closure after base change to a henselization.

## References

* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace IsLocalRing

/-- In a reduced one-dimensional local ring, an element of the maximal ideal cutting out the
closed point realizes the total ring of fractions as the localization away from it. -/
private theorem away_isFractionRing_of_parameter
    {R : Type*} [CommRing R] [IsLocalRing R] [IsReduced R]
    (hdim : ringKrullDim R = 1) {f : R} (hf : f ∈ maximalIdeal R)
    (hrad : (Ideal.span {f}).radical = maximalIdeal R) :
    IsLocalization (Submonoid.powers f) (FractionRing R) := by
  classical
  let S := Localization.Away f
  have hdimle : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, hdim]
    norm_num
  have hmaxnotmin : maximalIdeal R ∉ minimalPrimes R := fun hm => by
    have : ringKrullDim R ≤ 0 := Ring.krullDimLE_iff.mp (Ring.KrullDimLE.mk₀ fun p hp ↦ by
      rw [le_antisymm (le_maximalIdeal hp.ne_top) (hm.2 ⟨hp, bot_le⟩ (le_maximalIdeal hp.ne_top))]
      infer_instance)
    rw [hdim] at this
    norm_num at this
  have hfnotmin : ∀ p ∈ minimalPrimes R, f ∉ p := fun p hp hfp => by
    have hmp : maximalIdeal R ≤ p := by
      rw [← hrad]
      exact hp.isPrime.radical_le_iff.mpr ((Ideal.span_singleton_le_iff_mem p).mpr hfp)
    exact hmaxnotmin (le_antisymm (le_maximalIdeal hp.1.1.ne_top) hmp ▸ hp)
  have hfreg : f ∈ nonZeroDivisors R := by
    by_contra h
    have hz : zeroDivisorSet R f := by
      rcases (notMem_nonZeroDivisors_iff.mp h) with ⟨y, hmul, hy⟩ | ⟨y, hmul, hy⟩
      · exact ⟨y, hy, hmul⟩
      · exact ⟨y, hy, by simpa [mul_comm] using hmul⟩
    obtain ⟨p, hp, hfp⟩ := zeroDivisor_imp_mem_minimalPrime R f hz
    exact hfnotmin p hp hfp
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := Submonoid.powers_le.mpr hfreg
  have hregular_units : ∀ s, s ∈ nonZeroDivisors R → IsUnit (algebraMap R S s) := by
    intro s hs
    by_contra hsunit
    obtain ⟨M, hMmax, hspanM⟩ :=
      Ideal.exists_le_maximal _ (mt Ideal.span_singleton_eq_top.mp hsunit)
    let p := M.comap (algebraMap R S)
    have hp : p.IsPrime := hMmax.isPrime.comap _
    have hsp : s ∈ p := hspanM (Ideal.subset_span (Set.mem_singleton _))
    have hfnotp : f ∉ p := fun hfp => hMmax.ne_top (Ideal.eq_top_of_isUnit_mem M
      (Ideal.mem_comap.mp hfp) (IsLocalization.Away.algebraMap_isUnit f))
    rcases (Ring.krullDimLE_one_iff.mp hdimle) p hp with hpmin | hpmax
    · exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hsp hpmin hs
    · exact hfnotp (eq_maximalIdeal hpmax ▸ hf)
  let : IsLocalization (nonZeroDivisors R) S := IsLocalization.of_le _ _ hpow hregular_units
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f)
    (IsLocalization.algEquiv (nonZeroDivisors R) S (FractionRing R))

/-- A reduced one-dimensional Nagata local ring admits a single element which gives its total
ring of fractions after localization both before and after normalization. For every flat local
base change for which that element cuts out the closed point, the same localization gives the new
total ring of fractions, and the base-changed normalization embeds there compatibly with both
tensor factors. -/
@[ega "IV 18.9.7.8" "special case"]
public theorem exists_common_fractionRing_localization_and_injective_tensorProduct
    {A : Type u} [CommRing A] [IsLocalRing A] [IsReduced A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    ∃ f ∈ maximalIdeal A,
      IsLocalization (Submonoid.powers f) (FractionRing A) ∧
      IsLocalization
        (Submonoid.powers (algebraMap A (integralClosure A (FractionRing A)) f))
        (FractionRing A) ∧
      ∀ (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Flat A B],
        IsReduced B → ringKrullDim B = 1 →
        (Ideal.span {algebraMap A B f}).radical = maximalIdeal B →
        IsLocalization (Submonoid.powers (algebraMap A B f)) (FractionRing B) ∧
          ∃ q : AlgHom A (FractionRing A) (FractionRing B),
          ∃ g : AlgHom A
              (integralClosure A (FractionRing A) ⊗[A] B) (FractionRing B),
            Function.Injective g ∧
              g.comp (Algebra.TensorProduct.includeLeft :
                integralClosure A (FractionRing A) →ₐ[A]
                  (integralClosure A (FractionRing A) ⊗[A] B)) =
                q.comp (integralClosure A (FractionRing A)).val ∧
              g.comp (Algebra.TensorProduct.includeRight :
                B →ₐ[A] (integralClosure A (FractionRing A) ⊗[A] B)) =
      IsScalarTower.toAlgHom A B (FractionRing B) := by
  have : IsNoetherianRing A := hN.1
  obtain ⟨f, hf, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal hdim
  have hlocA : IsLocalization (Submonoid.powers f) (FractionRing A) :=
    away_isFractionRing_of_parameter hdim hf hrad
  let A' := integralClosure A (FractionRing A)
  have hlocA' : IsLocalization
      (Submonoid.powers (algebraMap A A' f)) (FractionRing A) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨n, rfl⟩ := hx
      change IsUnit ((algebraMap A (FractionRing A) f) ^ n)
      exact IsUnit.pow _
        (IsLocalization.map_units (FractionRing A) ⟨f, Submonoid.mem_powers f⟩)
    · intro z
      obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (Submonoid.powers f) z
      obtain ⟨n, hn⟩ := s.2
      refine ⟨⟨algebraMap A A' a,
        ⟨(algebraMap A A' f) ^ n,
          (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩⟩, ?_⟩
      rw [← hn] at hz
      simpa [map_pow, IsScalarTower.algebraMap_apply] using hz
    · exact fun hxy => ⟨1, by simp [Subtype.val_injective hxy]⟩
  refine ⟨f, hf, hlocA, hlocA', fun B _ _ _ _ hredB hdimB hradB => ?_⟩
  have hfB : algebraMap A B f ∈ maximalIdeal B := by
    rw [← hradB]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_singleton _))
  have hlocB : IsLocalization (Submonoid.powers (algebraMap A B f))
      (FractionRing B) := away_isFractionRing_of_parameter hdimB hfB hradB
  let T := B ⊗[A] A
  let eT : T ≃+* B :=
    (Algebra.TensorProduct.comm A B A).toRingEquiv.trans
      (Algebra.TensorProduct.lid A B).toRingEquiv
  have heT : ∀ (b : B) (a : A), eT (b ⊗ₜ[A] a) = a • b := fun b a => by
    change Algebra.TensorProduct.lid A B (Algebra.TensorProduct.comm A B A (b ⊗ₜ[A] a)) = _
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.lid_tmul]
  have hmapT : eT.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      algebraMap A B := by
    ext a
    simp [heT, Algebra.smul_def]
  have hmapT' : eT.toMonoidHom.comp Algebra.TensorProduct.includeRight.toMonoidHom =
      (algebraMap A B).toMonoidHom := congrArg RingHom.toMonoidHom hmapT
  have hM : Submonoid.map eT
      ((Submonoid.powers f).map Algebra.TensorProduct.includeRight) =
        Submonoid.powers (algebraMap A B f) := by
    calc
      _ = (Submonoid.powers f).map
          (eT.toMonoidHom.comp Algebra.TensorProduct.includeRight.toMonoidHom) := by
            change ((Submonoid.powers f).map Algebra.TensorProduct.includeRight.toMonoidHom).map
              eT.toMonoidHom = _
            rw [Submonoid.map_map]
      _ = (Submonoid.powers f).map (algebraMap A B).toMonoidHom := by rw [hmapT']
      _ = _ := by simp
  let : Algebra T (FractionRing B) :=
    (RingHom.comp (algebraMap B (FractionRing B)) eT.toRingHom).toAlgebra
  have hTb : ∀ b : B, algebraMap T (FractionRing B) (b ⊗ₜ[A] 1) = algebraMap B (FractionRing B) b :=
    fun b => by
      change algebraMap B (FractionRing B) (eT (b ⊗ₜ[A] 1)) = _
      rw [heT, one_smul]
  have : IsScalarTower B T (FractionRing B) :=
    IsScalarTower.of_algebraMap_smul (R := B) (A := T) (M := FractionRing B) fun b z => by
      simp only [Algebra.smul_def]
      exact congrArg (· * z) (hTb b)
  have : IsLocalization ((Submonoid.powers f).map Algebra.TensorProduct.includeRight)
      (FractionRing B) :=
    IsLocalization.of_ringEquiv_left eT hM fun _ => rfl
  let eBase := IsLocalization.tensorProductEquivOfMapIncludeRight A B
    (Submonoid.powers f) (FractionRing A) (FractionRing B)
  let e := (Algebra.TensorProduct.comm A (FractionRing A) B).trans
    (eBase.restrictScalars A)
  let q : AlgHom A (FractionRing A) (FractionRing B) :=
    e.toAlgHom.comp Algebra.TensorProduct.includeLeft
  let φ : AlgHom A (A' ⊗[A] B) (FractionRing A ⊗[A] B) :=
    Algebra.TensorProduct.map A'.val (AlgHom.id A B)
  let g : AlgHom A (A' ⊗[A] B) (FractionRing B) := e.toAlgHom.comp φ
  have hφinj : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B)
      (A'.val.toLinearMap : A' →ₗ[A] FractionRing A) Subtype.val_injective
  refine ⟨hlocB, q, g, e.injective.comp hφinj, by ext x; rfl, ?_⟩
  ext b
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
    IsScalarTower.coe_toAlgHom']
  have ht' : eBase (b ⊗ₜ[A] (1 : FractionRing A)) = algebraMap T (FractionRing B)
      (b ⊗ₜ[A] (1 : A)) := by
    simpa using IsLocalization.tensorProductEquivOfMapIncludeRight_tmul
      (R := A) (S := B) A (Submonoid.powers f) (FractionRing A) (FractionRing B) b (1 : A)
  exact ht'.trans (hTb b)

/-- The integral closure in the total ring of fractions of a reduced
Noetherian local ring becomes a normal ring after base change to any henselization. -/
public lemma isNormalRing_tensorProduct_integralClosure_of_isHenselization
    (A : Type u) (H : Type v) (K : Type w)
    [CommRing A] [IsLocalRing A] [IsReduced A] [IsNoetherianRing A]
    [CommRing H] [IsLocalRing H] [Algebra A H]
    [Field K] [Algebra (ResidueField A) K] [IsHenselization A K H] :
    IsNormalRing ((integralClosure A (FractionRing A)) ⊗[A] H) := by
  let B := ↥(integralClosure A (FractionRing A))
  let S := ULift.{u} H
  have hS : IsNormalRing (B ⊗[A] S) :=
    isNormalRing_tensorProduct_of_ind_etale B isNormalRing_integralClosure_fractionRing
      (IsHenselization.ind_etale (R := A) (L := K) (Rh := H))
  let e : (B ⊗[A] H) ≃ₐ[A] (B ⊗[A] S) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B)
      (ULift.algEquiv : ULift.{u} H ≃ₐ[A] H).symm
  exact IsNormalRing.congr e.symm.toRingEquiv hS

end IsLocalRing
