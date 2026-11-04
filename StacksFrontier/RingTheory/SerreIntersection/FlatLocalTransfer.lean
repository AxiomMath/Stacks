module

public import StacksFrontier.RingTheory.SerreIntersection.ComplementaryDimension

/-!
# Lengths and dimensions along a flat local map with trivial closed fibre
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.SerreIntersection

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] [IsLocalRing A] [IsLocalRing R]
  [Module.Flat A R]

/-- A local ring is a simple module over itself modulo its maximal ideal. -/
theorem isSimpleModule_quotient_maximalIdeal (R : Type u) [CommRing R] [IsLocalRing R] :
    IsSimpleModule R (R ⧸ maximalIdeal R) :=
  isSimpleModule_iff_quot_maximal.mpr
    ⟨maximalIdeal R, maximalIdeal.isMaximal R, ⟨LinearEquiv.refl _ _⟩⟩

/-- **Lengths are preserved along a flat local map with trivial closed fibre.** If `A → R` is flat
and `𝔪_A R = 𝔪_R`, then `length_R (R ⊗_A T) = length_A T` for every `A`-module `T` of finite
length: base change is exact and carries the residue field of `A` to that of `R`. -/
theorem length_baseChange (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    (T : Type u) [AddCommGroup T] [Module A T] (hT : IsFiniteLength A T) :
    Module.length R (R ⊗[A] T) = Module.length A T := by
  induction hT with
  | @of_subsingleton T0 _ _ _ =>
    have : Subsingleton (R ⊗[A] T0) := ⟨fun x y => by
      have h0 : ∀ z : R ⊗[A] T0, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul r t => rw [Subsingleton.elim t 0, TensorProduct.tmul_zero]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [h0 x, h0 y]⟩
    rw [Module.length_eq_zero (R := R) (M := R ⊗[A] T0), Module.length_eq_zero (R := A) (M := T0)]
  | @of_simple_quotient T' _ _ P _ _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule A (T' ⧸ P)›
    obtain rfl := IsLocalRing.eq_maximalIdeal hI
    have hex := Module.length_eq_add_of_exact (R := R) (P.subtype.baseChange R) (P.mkQ.baseChange R)
      (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype P))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective P))
      (lTensor_exact R (LinearMap.exact_subtype_mkQ P) (Submodule.mkQ_surjective P))
    have hexA := Module.length_eq_add_of_exact (R := A) P.subtype P.mkQ
      (Submodule.injective_subtype P) (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P)
    have e' : R ⊗[A] (T' ⧸ P) ≃ₗ[R] R ⧸ maximalIdeal R :=
      (e.baseChange A R _ _).trans ((Ideal.qoutMapEquivTensorQout R).symm.trans
        (Submodule.quotEquivOfEq _ _ (by rw [hm])))
    have : IsSimpleModule R (R ⧸ maximalIdeal R) := isSimpleModule_quotient_maximalIdeal R
    rw [hex, ih, e'.length_eq, hexA, Module.length_eq_one (R := R) (M := R ⧸ maximalIdeal R),
      Module.length_eq_one (R := A) (M := T' ⧸ P)]

/-- If `A → R` is flat and `𝔪_A R = 𝔪_R`, then for every `t` the length of
`(R ⊗_A M) / 𝔪_R ^ t (R ⊗_A M)` over `R` equals the length of `M / 𝔪_A ^ t M` over `A`, provided
the latter is finite. -/
theorem length_quotient_baseChange
    (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module A M] (t : ℕ)
    (ht : IsFiniteLength A (M ⧸ (maximalIdeal A) ^ t • (⊤ : Submodule A M))) :
    Module.length R ((R ⊗[A] M) ⧸ (maximalIdeal R) ^ t • (⊤ : Submodule R (R ⊗[A] M))) =
      Module.length A (M ⧸ (maximalIdeal A) ^ t • (⊤ : Submodule A M)) := by
  have hmap : Ideal.map (algebraMap A R) ((maximalIdeal A) ^ t) = (maximalIdeal R) ^ t := by
    rw [Ideal.map_pow, hm]
  rw [← length_baseChange hm _ ht, ← (TensorProduct.tensorQuotMapSMulEquivTensorQuot (S := R)
    (M := M) ((maximalIdeal A) ^ t)).length_eq, hmap]

omit [CommRing R] [Algebra A R] [IsLocalRing R] [Module.Flat A R] in
/-- The reduction of a finite module modulo a power of the maximal ideal has finite length. -/
theorem isFiniteLength_quotient_pow_smul [IsNoetherianRing A] (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (t : ℕ) :
    IsFiniteLength A (M ⧸ (maximalIdeal A) ^ t • (⊤ : Submodule A M)) := by
  by_cases hs : Subsingleton (M ⧸ (maximalIdeal A) ^ t • (⊤ : Submodule A M))
  · exact IsFiniteLength.of_subsingleton
  rw [not_subsingleton_iff_nontrivial] at hs
  have ht : t ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hs
    exact not_subsingleton (M ⧸ (⊤ : Submodule A M))
      ((Submodule.Quotient.subsingleton_iff (p := (⊤ : Submodule A M))).mpr rfl)
  have : Nontrivial M := ((maximalIdeal A) ^ t • (⊤ : Submodule A M)).mkQ_surjective.nontrivial
  have hann : Module.annihilator A M ≤ maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))
  have hdef : IsIdealOfDefinition ((maximalIdeal A) ^ t + Module.annihilator A M) := by
    rw [isIdealOfDefinition_iff]
    refine le_antisymm ((maximalIdeal.isMaximal A).isPrime.radical_le_iff.mpr
      (sup_le (Ideal.pow_le_self ht) hann)) ?_
    calc maximalIdeal A = (maximalIdeal A).radical :=
          (maximalIdeal.isMaximal A).isPrime.radical.symm
      _ = ((maximalIdeal A) ^ t).radical := (Ideal.radical_pow (maximalIdeal A) ht).symm
      _ ≤ ((maximalIdeal A) ^ t + Module.annihilator A M).radical :=
          Ideal.radical_mono le_sup_left
  have hlt := ((Ideal.idealOfDefinition_support_length_tfae ((maximalIdeal A) ^ t) hs).out 1 5).mp
    hdef
  exact Module.length_ne_top_iff.mp hlt.ne

/-- If `A → R` is flat and `𝔪_A R = 𝔪_R`, with `A` Noetherian, then the base change `R ⊗_A M` of a
nonzero finite `A`-module `M` is nonzero. -/
theorem nontrivial_baseChange (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] : Nontrivial (R ⊗[A] M) := by
  have hne := nontrivial_quotient_maximalIdeal_smul (R := A) M
  have hlen := length_quotient_baseChange hm M 1 (isFiniteLength_quotient_pow_smul M 1)
  rw [pow_one, pow_one] at hlen
  have hpos : Module.length A (M ⧸ (maximalIdeal A) • (⊤ : Submodule A M)) ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    exact not_subsingleton _
  rw [← hlen, Ne, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial] at hpos
  exact ((maximalIdeal R) • (⊤ : Submodule R (R ⊗[A] M))).mkQ_surjective.nontrivial

/-- **Dimensions of supports are preserved along a flat local map with trivial closed fibre**:
the Hilbert functions of `M` and of `R ⊗_A M` coincide. -/
theorem supportDim_baseChange (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R)
    [IsNoetherianRing A] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] :
    Module.supportDim R (R ⊗[A] M) = Module.supportDim A M := by
  have := nontrivial_baseChange hm M
  have h0A := supportDim_quotient_maximalIdeal_smul (R := A) M
  have h0R := supportDim_quotient_maximalIdeal_smul (R := R) (R ⊗[A] M)
  obtain ⟨P, hP⟩ := Ideal.exists_computesGeneralizedHilbertPoly (maximalIdeal A) h0A
  have hP' : (maximalIdeal R).ComputesGeneralizedHilbertPoly (R ⊗[A] M) P :=
    hP.mono fun t ⟨p, hl, hv⟩ =>
      ⟨p, by rw [length_quotient_baseChange hm M t (isFiniteLength_quotient_pow_smul M t), hl], hv⟩
  rw [← Ideal.degree_eq_supportDim_of_computesGeneralizedHilbertPoly _ h0R hP',
    Ideal.degree_eq_supportDim_of_computesGeneralizedHilbertPoly _ h0A hP]

section FiniteLengthSupport

variable {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]

/-- For a finite module over a Noetherian local ring, being supported in the closed point is
having finite length. -/
theorem support_subset_closedPoint_iff_length_ne_top (X : Type u) [AddCommGroup X] [Module S X]
    [Module.Finite S X] :
    Module.support S X ⊆ {closedPoint S} ↔ Module.length S X ≠ ⊤ := by
  by_cases hs : Subsingleton X
  · rw [Module.support_eq_empty_iff.mpr hs, Module.length_eq_zero]
    exact ⟨fun _ => ENat.zero_ne_top, fun _ => Set.empty_subset _⟩
  rw [not_subsingleton_iff_nontrivial] at hs
  let e : (X ⧸ (⊥ : Ideal S) • (⊤ : Submodule S X)) ≃ₗ[S] X :=
    (Submodule.quotEquivOfEq _ ⊥ (Submodule.bot_smul ⊤)).trans (Submodule.quotEquivOfEqBot ⊥ rfl)
  have h := (Ideal.idealOfDefinition_support_length_tfae (⊥ : Ideal S) e.toEquiv.nontrivial).out 3 5
  rwa [e.support_eq, e.length_eq, lt_top_iff_ne_top] at h

end FiniteLengthSupport

/-- If `A → R` is flat and `𝔪_A R = 𝔪_R`, with `A` and `R` Noetherian, and `M ⊗_A N` is supported
in the closed point of `Spec A` for finite `A`-modules `M` and `N`, then `(R ⊗_A M) ⊗_R (R ⊗_A N)`
is supported in the closed point of `Spec R`. -/
theorem support_subset_closedPoint_tensor
    (hm : Ideal.map (algebraMap A R) (maximalIdeal A) = maximalIdeal R) [IsNoetherianRing A]
    [IsNoetherianRing R] (M N : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    Module.support R ((R ⊗[A] M) ⊗[R] (R ⊗[A] N)) ⊆ {closedPoint R} := by
  rw [support_subset_closedPoint_iff_length_ne_top] at hMN ⊢
  rwa [← (TensorProduct.AlgebraTensorModule.distribBaseChange A R M N).length_eq,
    length_baseChange hm _ (Module.length_ne_top_iff.mp hMN)]

end Stacks.SerreIntersection
