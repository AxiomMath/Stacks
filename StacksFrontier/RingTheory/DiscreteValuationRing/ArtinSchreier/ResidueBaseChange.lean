module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.WeakSolutionCriteria
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitPolynomial
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitExtension
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.PoleReduction
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ScaledPole
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.WeakSolutionCriteria

/-!
# Eliminating degree-prime ramification: residues that are not `p`-th powers and base change

Weak unramifiedness when the leading residue is not a `p`-th power, the base-changed Laurent
reduction, weak solutions over prepared mixed Laurent orbit extensions, and the Laurent data and
wild support of an Artin--Schreier presentation.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- Let `M = L(z)` with `z ^ p - z = π⁻¹ ^ n * a`, where `π` is a uniformizer of `B`, `n > 0` is
divisible by `p` and the residue of `a` is not a `p`-th power in the residue field of `B`. Then
`B → C` is weakly unramified. -/
theorem isWeaklyUnramified_of_artinSchreier_residue_not_pow
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (π : B) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hpn : p ∣ n)
    (a : B) (ha : ¬∃ y : IsLocalRing.ResidueField B, IsLocalRing.residue B a = y ^ p)
    (hξ : ξ = (algebraMap B L π)⁻¹ ^ n * algebraMap B L a) :
    IsWeaklyUnramified B C := by
  obtain ⟨hfin, hgal, -, -, -, hcase⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier B L M p hp ξ z hz
      hgen π hπ
  let := hfin
  let := hgal
  obtain ⟨hdvr, -, hind, -⟩ := hcase n a hn hpn ha hξ
  let := hdvr
  apply isWeaklyUnramified_of_ramificationIdx'_eq_one B C L M
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm]
  exact hind


private theorem residueField_map_surjective_of_totallyRamified
    (A K E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [IsDiscreteValuationRing (integralClosure A E)]
    [IsLocalHom (algebraMap A (integralClosure A E))]
    (htot : IsTotallyRamifiedWithRespectTo A K E) :
    Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A (integralClosure A E))) := by
  let S := integralClosure A E
  obtain ⟨m, hm, hml, _, hf⟩ := htot
  have heq : m = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hm
  have hfm := heq ▸ hf
  let : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal A) := heq ▸ hml
  let := Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal A)
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let : Module.Free (A ⧸ IsLocalRing.maximalIdeal A) (S ⧸ IsLocalRing.maximalIdeal S) :=
    Module.Free.of_divisionRing _ _
  have hfmax : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
      (S ⧸ IsLocalRing.maximalIdeal S) = 1 := by simpa using hfm
  have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp hfmax
  exact hb.2

private theorem not_exists_pow_of_surjective_field_hom
    {k l : Type*} [Field k] [Field l] (f : k →+* l) (hf : Function.Surjective f)
    (p : ℕ) (x : k) (hx : ¬∃ y : k, x = y ^ p) : ¬∃ y : l, f x = y ^ p := by
  rintro ⟨y, hy⟩
  obtain ⟨z, rfl⟩ := hf y
  apply hx
  exact ⟨z, f.injective (by simpa only [map_pow] using hy)⟩

private theorem isExtension_integralClosure_of_isDiscreteValuationRing
    (A K E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [IsDiscreteValuationRing (integralClosure A E)] :
    IsExtension A (integralClosure A E) := by
  let S := integralClosure A E
  have hinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply IsFractionRing.injective A K
    apply (algebraMap K E).injective
    have he := congrArg Subtype.val h
    change algebraMap A E x = algebraMap A E y at he
    simpa only [IsScalarTower.algebraMap_apply A K E] using he
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  let : IsLocalHom (algebraMap A S) :=
    ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (IsLocalRing.maximalIdeal S)))
  exact {}

private theorem isSeparable_tensorProduct_of_isField
    (K L E : Type*) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    (hF : IsField (L ⊗[K] E)) :
    letI := hF.toField
    Algebra.IsSeparable L (L ⊗[K] E) := by
  let := hF.toField
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  exact Algebra.FormallyUnramified.isSeparable L (L ⊗[K] E)

/-- A composite of extensions of discrete valuation rings is an extension. -/
private theorem isExtension_of_comp
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtension A B] [IsExtension B C] : IsExtension A C := by
  let : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance
  let : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr (by
    rw [IsScalarTower.algebraMap_eq A B C]
    exact (FaithfulSMul.algebraMap_injective B C).comp (FaithfulSMul.algebraMap_injective A B))
  exact {}

/-- If the maximal ideal of `A` generates the maximal ideal of `B`, then `A → B` has ramification
index one. -/
private theorem ramificationIndex_eq_one_of_map_maximalIdeal
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B]
    (h : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B) :
    ramificationIndex A B = 1 := by
  symm
  apply (ramificationIndex_characterization A B).2.2.1 1 (by omega)
  rw [pow_one]
  exact h

private theorem isTotallyRamified_tensorProduct_of_weaklyUnramified
    (A B K L E : Type*) [CommRing A] [CommRing B] [Field K] [Field L] [Field E]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hweak : IsWeaklyUnramified A B)
    (htot : IsTotallyRamifiedWithRespectTo A K E)
    (hF : IsField (L ⊗[K] E)) :
    letI := hF.toField
    letI := isSeparable_tensorProduct_of_isField K L E hF
    ∀ [IsDiscreteValuationRing (integralClosure A E)]
      [IsDiscreteValuationRing (integralClosure B (L ⊗[K] E))]
      (f : integralClosure A E →ₐ[A] integralClosure B (L ⊗[K] E)),
      Function.Injective f →
      Ideal.map f.toRingHom (IsLocalRing.maximalIdeal (integralClosure A E)) =
        IsLocalRing.maximalIdeal (integralClosure B (L ⊗[K] E)) →
      IsTotallyRamifiedWithRespectTo B L (L ⊗[K] E) := by
  let := hF.toField
  let := isSeparable_tensorProduct_of_isField K L E hF
  intro _ _ f hinj hmax
  let R := integralClosure B (L ⊗[K] E)
  let S := integralClosure A E
  let : IsExtension A S := isExtension_integralClosure_of_isDiscreteValuationRing A K E
  let : IsExtension B R :=
    isExtension_integralClosure_of_isDiscreteValuationRing B L (L ⊗[K] E)
  let : Algebra S R := f.toRingHom.toAlgebra
  let : IsScalarTower A S R := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hinj
  let : IsLocalHom (algebraMap S R) := ((IsLocalRing.local_hom_TFAE _).out 3 1).mp hmax.le
  let : IsExtension S R := {}
  let : IsExtension A R := isExtension_of_comp A B R
  have hSR : ramificationIndex S R = 1 :=
    ramificationIndex_eq_one_of_map_maximalIdeal S R hmax
  let : Module.IsTorsionFree A S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A S)
  let : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A S)).symm⟩
  have hAS : ramificationIndex A S = Module.finrank K E := by
    rw [ramificationIndex_eq_ramificationIdx A S,
      ramificationIdx_eq_ramificationIdx'_maximalIdeal]
    exact ramificationIdx_eq_finrank_of_totallyRamified A K E htot _ inferInstance inferInstance
  have hBR : ramificationIndex B R = Module.finrank L (L ⊗[K] E) := by
    have h1 := ramificationIndex_tower A B R
    have h2 := ramificationIndex_tower A S R
    rw [show ramificationIndex A B = 1 from hweak, one_mul] at h1
    rw [hAS, hSR, mul_one] at h2
    rw [Module.finrank_baseChange]
    exact h1.symm.trans h2
  apply isTotallyRamified_of_map_le_pow_finrank B L (L ⊗[K] E) (IsLocalRing.maximalIdeal R)
  rw [← hBR]
  exact (ramificationIndex_characterization B R).2.1.le

/-- Let `α ∈ R` satisfy `α ^ (p ^ r) = π * u` with `u - 1 ∈ (π ^ n)`, and let
`ξ = ∑ i < n, cᵢ * π⁻¹ ^ (n - i) + b`, where `cᵢ - ρᵢ ^ (p ^ dᵢ) ∈ (π ^ n)` and `dᵢ ≤ r`. Then
there are `t ∈ F` and `b₁ ∈ R` with
`ξ - (t ^ p - t) = ∑ i < n, ρᵢ * α⁻¹ ^ ((n - i) * p ^ (r - dᵢ)) + b₁` in `F`. -/
theorem exists_baseChanged_laurent_reduction
    {B R L F : Type*} [CommRing B] [CommRing R] [Field L] [Field F]
    [Algebra B L] [Algebra B R] [Algebra R F] [Algebra B F] [Algebra L F]
    [IsScalarTower B R F] [IsScalarTower B L F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (π : B) (hπ : algebraMap B L π ≠ 0) (α : R) (u : Rˣ) (r n : ℕ)
    (hroot : α ^ (p ^ r) = algebraMap B R π * (u : R))
    (hu : u.val - 1 ∈ Ideal.span {algebraMap B R π ^ n})
    (coeff root : ℕ → B) (depth : ℕ → ℕ)
    (hdepth : ∀ i ∈ Finset.range n, depth i ≤ r)
    (hcoeff : ∀ i ∈ Finset.range n,
      coeff i - root i ^ (p ^ depth i) ∈ Ideal.span {π ^ n})
    (b : B) (ξ : L)
    (hξ : ξ = (∑ i ∈ Finset.range n,
      algebraMap B L (coeff i) * (algebraMap B L π)⁻¹ ^ (n - i)) + algebraMap B L b) :
    ∃ (t η : F) (b₁ : R),
      η = algebraMap L F ξ - (t ^ p - t) ∧
      η = (∑ i ∈ Finset.range n,
        algebraMap B F (root i) * (algebraMap R F α)⁻¹ ^ ((n - i) * p ^ (r - depth i))) +
          algebraMap R F b₁ := by
  classical
  let S := (algebraMap R F).range
  let x : ℕ → F := fun i => algebraMap B F (root i) *
    (algebraMap R F α)⁻¹ ^ ((n - i) * p ^ (r - depth i))
  have hπF : algebraMap B F π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply B L F]
    simpa only [map_zero] using (algebraMap L F).injective.ne hπ
  have hterm : ∀ i ∈ Finset.range n,
      algebraMap B F (coeff i) * (algebraMap B F π)⁻¹ ^ (n - i) - x i ^ (p ^ depth i) ∈ S := by
    intro i hi
    have hdi := hdepth i hi
    have hiN : n - i ≤ n := Nat.sub_le n i
    have hexp : ((n - i) * p ^ (r - depth i)) * p ^ depth i = (p ^ r) * (n - i) := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hdi, mul_comm]
    have hx : x i ^ (p ^ depth i) =
        algebraMap B F (root i ^ (p ^ depth i)) * (algebraMap R F α)⁻¹ ^ ((p ^ r) * (n - i)) := by
      simp only [x, mul_pow, map_pow, ← pow_mul, hexp]
    have hc : algebraMap B F (coeff i - root i ^ (p ^ depth i)) *
        (algebraMap B F π)⁻¹ ^ (n - i) ∈ S := by
      obtain ⟨c, hc⟩ := mul_inv_pow_mem_range_of_mem_span_pow π hπ n (n - i) hiN _ (hcoeff i hi)
      refine ⟨algebraMap B R c, ?_⟩
      simpa only [Algebra.linearMap_apply, map_mul, map_pow, map_inv₀,
        ← IsScalarTower.algebraMap_apply] using congrArg (algebraMap L F) hc
    have hd : (algebraMap B F π)⁻¹ ^ (n - i) -
        (algebraMap R F α)⁻¹ ^ ((p ^ r) * (n - i)) ∈ S := by
      rw [IsScalarTower.algebraMap_apply B R F]
      apply inv_pow_sub_mem_range_of_pow_eq_mul (algebraMap B R π)
        (by simpa only [← IsScalarTower.algebraMap_apply] using hπF) u (algebraMap R F α)
        (p ^ r) n (n - i) _ hu hiN
      simpa only [map_pow, map_mul, ← IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap R F) hroot
    have hm : algebraMap B F (root i ^ (p ^ depth i)) ∈ S :=
      ⟨algebraMap B R _, (IsScalarTower.algebraMap_apply B R F _).symm⟩
    have H := S.add_mem hc (S.mul_mem hm hd)
    rw [hx]
    convert H using 1; simp only [map_sub]; ring
  have hξF : algebraMap L F ξ = (∑ i ∈ Finset.range n,
      algebraMap B F (coeff i) * (algebraMap B F π)⁻¹ ^ (n - i)) + algebraMap B F b := by
    simpa only [map_add, map_sum, map_mul, map_pow, map_inv₀,
      ← IsScalarTower.algebraMap_apply] using congrArg (algebraMap L F) hξ
  have herr : algebraMap L F ξ - ∑ i ∈ Finset.range n, x i ^ (p ^ depth i) ∈ S := by
    rw [hξF]
    have hb : algebraMap B F b ∈ S :=
      ⟨algebraMap B R b, (IsScalarTower.algebraMap_apply B R F b).symm⟩
    have H := S.add_mem (S.sum_mem hterm) hb
    rw [Finset.sum_sub_distrib] at H
    convert H using 1; abel
  obtain ⟨b₁, hb₁⟩ := herr
  let t : F := ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (depth i), x i ^ (p ^ k)
  have ht : t ^ p - t = (∑ i ∈ Finset.range n, x i ^ (p ^ depth i)) -
      ∑ i ∈ Finset.range n, x i := by
    dsimp [t]
    rw [sum_pow_char, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => artinSchreier_sum_pow p (x i) (depth i))
  refine ⟨t, algebraMap L F ξ - (t ^ p - t), b₁, rfl, ?_⟩
  change algebraMap L F ξ - (t ^ p - t) = (∑ i ∈ Finset.range n, x i) + algebraMap R F b₁
  linear_combination -ht - hb₁

/-- The `n`-th power of the maximal ideal lies in the span of the `n`-th power of a uniformizer. -/
private theorem maximalIdeal_pow_le_span_pow_of_irreducible
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] {π : B}
    (hπ : Irreducible π) (n : ℕ) : IsLocalRing.maximalIdeal B ^ n ≤ Ideal.span {π ^ n} := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ, Ideal.span_singleton_pow]

/-- A uniformizer of a discrete valuation ring has nonzero image in its fraction field. -/
private theorem algebraMap_ne_zero_of_irreducible
    {B : Type*} (L : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field L]
    [Algebra B L] [IsFractionRing B L] {π : B} (hπ : Irreducible π) : algebraMap B L π ≠ 0 := by
  simpa only [map_zero] using (IsFractionRing.injective B L).ne hπ.ne_zero

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The base-change, Artin--Schreier and Laurent-expansion constructions assembled here
-- elaborate far more terms than the default budget allows.
set_option synthInstance.maxHeartbeats 200000 in
-- (the larger synthesis budget is explained in the comment just above)
/-- Suppose `L ⊗[K] E` is a field and `f` is an injective map from the integral closure of `A` in
`E` to the integral closure `R` of `B` in `L ⊗[K] E`, carrying the maximal ideal onto the maximal
ideal and compatible with `E → L ⊗[K] E`. Let `M = L(z)` with `z ^ p - z = ξ`, and let
`η = ξ - (t ^ p - t)` satisfy `π ^ n * η = a`, where `π` is a uniformizer of `R`, `p ∣ n`,
`n > 0` and the residue of `a` is not a `p`-th power. Then `E / K` is a weak solution for
`A → C`. -/
theorem exists_isWeakSolution_of_baseChanged_artinSchreier_residue
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (E : Type uK)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field E]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    [IsDomain (L ⊗[K] E)]
    [IsDiscreteValuationRing (integralClosure A E)]
    [IsDiscreteValuationRing (integralClosure B (L ⊗[K] E))]
    [IsFractionRing (integralClosure B (L ⊗[K] E)) (L ⊗[K] E)]
    (hLF : IsField (L ⊗[K] E))
    (f : integralClosure A E →ₐ[A] integralClosure B (L ⊗[K] E))
    (hfinj : Function.Injective f)
    (hfmax : Ideal.map f.toRingHom (IsLocalRing.maximalIdeal (integralClosure A E)) =
      IsLocalRing.maximalIdeal (integralClosure B (L ⊗[K] E)))
    (hfsquare : ∀ a : integralClosure A E,
      (f a : L ⊗[K] E) = (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) (a : E))
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (η t : L ⊗[K] E) (hη : η = algebraMap L (L ⊗[K] E) ξ - (t ^ p - t))
    (π : integralClosure B (L ⊗[K] E)) (hπ : Irreducible π)
    (n : ℕ) (hn : 0 < n) (hpn : p ∣ n) (a : integralClosure B (L ⊗[K] E))
    (ha : ¬∃ y : IsLocalRing.ResidueField (integralClosure B (L ⊗[K] E)),
      IsLocalRing.residue _ a = y ^ p)
    (hparam : (π : L ⊗[K] E) ^ n * η = a) :
    ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
      max uM uK, uK, max uM uK} A C K M E, D.IsWeakSolution := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let L₁ := L ⊗[K] E
  let R := integralClosure B L₁
  let A₁ := integralClosure A E
  let : Field L₁ := hLF.toField
  let : CharP L₁ p := charP_of_injective_algebraMap (algebraMap K L₁).injective p
  let : Algebra A₁ R := f.toRingHom.toAlgebra
  let : IsScalarTower A A₁ R := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : FaithfulSMul A₁ R := (faithfulSMul_iff_algebraMap_injective A₁ R).mpr hfinj
  let : IsLocalHom (algebraMap A₁ R) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp hfmax.le
  let : IsExtension A₁ R := {}
  have hAR : ramificationIndex A₁ R = 1 :=
    ramificationIndex_eq_one_of_map_maximalIdeal A₁ R hfmax
  apply exists_isWeakSolution_of_fieldFactor_ramification A C K M E
  intro Q F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι hqsquare hFgen
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  let : Algebra B Q := ((algebraMap C Q).comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C Q := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra B F := ((algebraMap C F).comp (algebraMap B C)).toAlgebra
  let : IsScalarTower B C F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower B Q F := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B C F, IsScalarTower.algebraMap_apply B C Q,
      ← IsScalarTower.algebraMap_apply C Q F]
  let : IsScalarTower B M F := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B C F, IsScalarTower.algebraMap_apply B C M,
      ← IsScalarTower.algebraMap_apply C M F]
  let : Algebra L F := ((algebraMap M F).comp (algebraMap L M)).toAlgebra
  let : IsScalarTower L M F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K M F, IsScalarTower.algebraMap_apply K L M,
      ← IsScalarTower.algebraMap_apply L M F]
  let : IsScalarTower B L F := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B M F, IsScalarTower.algebraMap_apply B L M,
      ← IsScalarTower.algebraMap_apply L M F]
  let ρ : L₁ →ₐ[K] F := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K L F) ι
    (fun _ _ => Commute.all _ _)
  let : Algebra L₁ F := ρ.toRingHom.toAlgebra
  have hρL (l : L) : ρ (algebraMap L L₁ l) = algebraMap L F l := by
    change Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K L F) ι _ (l ⊗ₜ[K] (1 : E)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hρE (e : E) : ρ ((Algebra.TensorProduct.includeRight : E →ₐ[K] L₁) e) = ι e := by
    change Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K L F) ι _ ((1 : L) ⊗ₜ[K] e) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  let : IsScalarTower B L₁ F := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap B F x = ρ (algebraMap B L₁ x)
    rw [IsScalarTower.algebraMap_apply B L L₁, hρL, ← IsScalarTower.algebraMap_apply B L F]
  let : IsExtension B Q := isExtension_of_comp B C Q
  obtain ⟨g, hginj, hglocal, hgsquare⟩ := exists_integralClosure_embedding_into_dvr B R L₁ Q F
    (IsScalarTower.toAlgHom B L₁ F)
  let : Algebra R Q := g.toRingHom.toAlgebra
  let : IsScalarTower B R Q := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  let : Algebra R F := Subalgebra.toAlgebra (α := F) R
  let : IsScalarTower R L₁ F := inferInstance
  let : IsScalarTower R Q F := IsScalarTower.of_algebraMap_eq fun x => (hgsquare x).symm
  let : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).mpr hginj
  let : IsLocalHom (algebraMap R Q) := hglocal
  let : IsExtension R Q := {}
  let : IsScalarTower A₁ R Q := IsScalarTower.of_algebraMap_eq fun x => by
    apply IsFractionRing.injective Q F
    rw [hqsquare]
    change ι (x : E) = algebraMap Q F (g (f x))
    rw [hgsquare]
    change ι (x : E) = ρ ((f x : R) : L₁)
    rw [hfsquare, hρE]
  have hg : Algebra.adjoin L₁ {algebraMap M F z} = ⊤ :=
    adjoin_singleton_eq_top_of_adjoin_range_eq_top z ι hgen hFgen
      (fun l => ⟨algebraMap L L₁ l, hρL l⟩)
      (fun e => ⟨(Algebra.TensorProduct.includeRight : E →ₐ[K] L₁) e, hρE e⟩)
  have hg' : Algebra.adjoin L₁ {algebraMap M F z - algebraMap L₁ F t} = ⊤ := by
    rw [adjoin_singleton_sub_algebraMap, hg]
  have heq : (algebraMap M F z - algebraMap L₁ F t) ^ p -
      (algebraMap M F z - algebraMap L₁ F t) = algebraMap L₁ F η := by
    have hz' := congrArg (algebraMap M F) hz
    have hη' := congrArg ρ hη
    simp only [map_sub, map_pow, ← IsScalarTower.algebraMap_apply] at hz' hη'
    change ρ η = ρ (algebraMap L L₁ ξ) - (ρ t ^ p - ρ t) at hη'
    rw [hρL] at hη'
    rw [sub_pow_char]
    change _ = ρ η
    linear_combination hz' - hη'
  have hπ0 : algebraMap R L₁ π ≠ 0 := algebraMap_ne_zero_of_irreducible L₁ hπ
  have hparam' : η = (algebraMap R L₁ π)⁻¹ ^ n * algebraMap R L₁ a := by
    apply (mul_left_cancel₀ (pow_ne_zero n hπ0))
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, one_mul]
    exact hparam
  have hRQ : IsWeaklyUnramified R Q :=
    isWeaklyUnramified_of_artinSchreier_residue_not_pow R Q L₁ F p hp η _ heq hg'
      π hπ n hn hpn a ha hparam'
  let : Module.IsTorsionFree R Q := Module.isTorsionFree_iff_algebraMap_injective.mpr hginj
  let : (IsLocalRing.maximalIdeal Q).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R Q)).symm⟩
  rw [Ideal.ramificationIdx_tower (R := A₁) (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal Q),
    (ramificationIndex_eq_ramificationIdx A₁ R).symm.trans hAR,
    (isWeaklyUnramified_iff_ramificationIdx_eq_one R Q).mp hRQ, one_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxHeartbeats 200000 in
-- The prepared tensor-base-change and Laurent-reduction assembly exceeds the default budget.
/-- A prepared mixed Laurent presentation is solved over a prescribed orbit extension.

This is the terminal mixed-coefficient arm of the degree-`p` equal-characteristic
argument.  Unlike `exists_isGalois_totallyRamified_orbitExtension`, this theorem does
not choose an extension: `E / K`, its total ramification, and all orbit-polynomial
data are inputs.  Consequently several Laurent presentations can be prepared first
and then solved over one common extension.

The roots `root i` live in the residue field of the current target DVR `B`.  This is
important after a preceding separable residue extension: roots transported through a
normal residue-field extension need not descend to the residue field that occurred
before that base change.

The input `depth` records the Frobenius depth used for each coefficient.  The caller
has already performed the finite combinatorics and supplies `j` as the unique largest
scaled pole.  Its root is terminal (not a `p`-th power), while `hpow` supplies all
coefficient/root equations.  The orbit data turn the prescribed `E / K` into the
ramified change of uniformizer used by the Laurent reduction. -/
theorem exists_isWeakSolution_of_prepared_mixed_laurent_orbitExtension
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (E : Type uK)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field E]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [IsGalois K E]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hweak : IsWeaklyUnramified A B)
    (xi : L) (z : M) (hz : z ^ p - z = algebraMap L M xi)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (pi : A) (hpi : Irreducible pi)
    (n : ℕ) (hn : 0 < n)
    (lift : IsLocalRing.ResidueField B → B)
    (hlift : ∀ x, IsLocalRing.residue B (lift x) = x)
    (liftMod : IsLocalRing.ResidueField B →+*
      B ⧸ (IsLocalRing.maximalIdeal B) ^ n)
    (hliftMod : ∀ x, Ideal.Quotient.mk _ (lift x) = liftMod x)
    (coeff root : ℕ → IsLocalRing.ResidueField B) (b : B)
    (hexp : xi = (∑ i ∈ Finset.range n,
      algebraMap B L (lift (coeff i)) *
        (algebraMap B L (algebraMap A B pi))⁻¹ ^ (n - i)) + algebraMap B L b)
    (rank : ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ i ∈ Finset.range n, depth i ≤ rank)
    (hpow : ∀ i ∈ Finset.range n, root i ^ (p ^ depth i) = coeff i)
    (j : ℕ) (hj : j ∈ Finset.range n)
    (hterminal : ¬∃ y : IsLocalRing.ResidueField B, root j = y ^ p)
    (hpolePos : 0 < (n - j) * p ^ (rank - depth j))
    (hpoleDvd : p ∣ (n - j) * p ^ (rank - depth j))
    (hpoleMax : ∀ i ∈ Finset.range n, i ≠ j →
      (n - i) * p ^ (rank - depth i) < (n - j) * p ^ (rank - depth j))
    (htot : IsTotallyRamifiedWithRespectTo A K E)
    (hdegree : Module.finrank K E = p ^ rank)
    (V : AddSubgroup A) [Fintype V] (alpha : E)
    (hcard : Fintype.card V = p ^ rank)
    (halpha : IsIntegral A alpha)
    (hV : ∀ v : V, (v : A) ∈ Ideal.span {pi ^ (n + 1)})
    (hprod : ∏ v : V, (alpha - algebraMap A E v) = algebraMap A E pi) :
    ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
      max uM uK, uK, max uM uK} A C K M E, D.IsWeakSolution := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpiB : Irreducible (algebraMap A B pi) :=
    irreducible_algebraMap_of_isWeaklyUnramified hweak hpi
  have hpiL : algebraMap B L (algebraMap A B pi) ≠ 0 := algebraMap_ne_zero_of_irreducible L hpiB
  have hI := maximalIdeal_pow_le_span_pow_of_irreducible hpiB n
  let L₁ := L ⊗[K] E
  let A₁ := integralClosure A E
  let B₁ := integralClosure B L₁
  obtain ⟨hLF, hA₁, hB₁, hfrac, f, hfinj, hfmax, hfsquare⟩ :=
    exists_integralClosure_baseChange_dvr A B K L E hweak htot
  let : Field L₁ := hLF.toField
  let : IsDiscreteValuationRing A₁ := hA₁
  let : IsDiscreteValuationRing B₁ := hB₁
  let : IsFractionRing B₁ L₁ := hfrac
  let : IsFractionRing A₁ E := integralClosure.isFractionRing_of_finite_extension K E
  let : Algebra.IsSeparable L L₁ := isSeparable_tensorProduct_of_isField K L E hLF
  let : IsExtension B B₁ :=
    isExtension_integralClosure_of_isDiscreteValuationRing B L L₁
  let : Module.IsTorsionFree B B₁ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective B B₁)
  let : (IsLocalRing.maximalIdeal B₁).LiesOver (IsLocalRing.maximalIdeal B) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap B B₁)).symm⟩
  have htotB : IsTotallyRamifiedWithRespectTo B L L₁ :=
    isTotallyRamified_tensorProduct_of_weaklyUnramified A B K L E hweak htot hLF
      f hfinj hfmax
  have heB : ramificationIndex B B₁ = p ^ rank := by
    rw [ramificationIndex_eq_ramificationIdx B B₁,
      ramificationIdx_eq_ramificationIdx'_maximalIdeal,
      ramificationIdx_eq_finrank_of_totallyRamified B L L₁ htotB _
        inferInstance inferInstance, Module.finrank_baseChange, hdegree]
  have hresSurj := residueField_map_surjective_of_totallyRamified B L L₁ htotB
  let alphaA : A₁ := ⟨alpha, halpha⟩
  let alphaB : B₁ := f alphaA
  have hprodA : (∏ v : V, (alphaA - algebraMap A A₁ v)) = algebraMap A A₁ pi := by
    apply IsFractionRing.injective A₁ E
    simp only [map_prod, map_sub, ← IsScalarTower.algebraMap_apply]
    exact hprod
  have hprodB : (∏ v : V, (alphaB - algebraMap A B₁ v)) = algebraMap A B₁ pi := by
    have hfc (x : A) : f (algebraMap A A₁ x) = algebraMap A B₁ x := f.commutes x
    simpa only [map_prod, map_sub, hfc] using congrArg f hprodA
  have happrox : alphaB ^ (p ^ rank) - algebraMap B B₁ (algebraMap A B pi) ∈
      Ideal.span {algebraMap B B₁ (algebraMap A B pi) ^ (n + 1)} := by
    simpa only [hcard, ← IsScalarTower.algebraMap_apply] using
      pow_card_sub_mem_span_pow_of_prod_eq V pi (n + 1) hV alphaB hprodB
  obtain ⟨halphaB, u, hroot, hu⟩ := irreducible_of_pow_sub_mem_span_pow
    (algebraMap A B pi) hpiB alphaB (p ^ rank) n (pow_pos hp.pos rank) hn heB happrox
  have hcoeff : ∀ i ∈ Finset.range n,
      lift (coeff i) - lift (root i) ^ (p ^ depth i) ∈
        Ideal.span {algebraMap A B pi ^ n} := by
    intro i hi
    apply hI
    apply Ideal.Quotient.eq.mp
    rw [hliftMod, map_pow, hliftMod]
    simpa only [map_pow] using congrArg liftMod (hpow i hi).symm
  let : CharP L₁ p := charP_of_injective_algebraMap (algebraMap K L₁).injective p
  obtain ⟨t, eta, b₁, heta, hetaexp⟩ :=
    exists_baseChanged_laurent_reduction (F := L₁) p (algebraMap A B pi) hpiL
      alphaB u rank n hroot hu (fun i => lift (coeff i))
      (fun i => lift (root i)) depth hdepth hcoeff b xi hexp
  let pole : ℕ → ℕ := fun i => (n - i) * p ^ (rank - depth i)
  have hnotPow : ¬∃ y : IsLocalRing.ResidueField B₁,
      algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B₁) (root j) = y ^ p :=
    not_exists_pow_of_surjective_field_hom _ hresSurj p (root j) hterminal
  obtain ⟨a₁, hetapole, hres⟩ := exists_laurent_numerator_residue_of_unique_max
    alphaB halphaB (Finset.range n)
    (fun i => algebraMap B B₁ (lift (root i))) pole j hj hpolePos
    (by simpa only [pole] using hpoleMax) b₁ eta
    (by simpa only [pole, ← IsScalarTower.algebraMap_apply] using hetaexp)
  have ha₁ : ¬∃ y : IsLocalRing.ResidueField B₁,
      IsLocalRing.residue B₁ a₁ = y ^ p := by
    rw [hres, ← IsLocalRing.ResidueField.map_residue, hlift]
    exact hnotPow
  apply exists_isWeakSolution_of_baseChanged_artinSchreier_residue A B C K L M E
    hLF f hfinj hfmax hfsquare p hp xi z hz hgen eta t heta alphaB halphaB
    (pole j) (by simpa only [pole] using hpolePos)
    (by simpa only [pole] using hpoleDvd) a₁ ha₁
  have htalpha : algebraMap B₁ L₁ alphaB ≠ 0 := algebraMap_ne_zero_of_irreducible L₁ halphaB
  change algebraMap B₁ L₁ alphaB ^ (pole j) * eta = algebraMap B₁ L₁ a₁
  rw [hetapole, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ htalpha, one_pow, one_mul]

/-- **The `B`-side data of Epp's degree-`p` layer, with no base ring in sight.**

An Artin–Schreier presentation `z ^ p - z = ξ` of `M / L` of minimal pole order with respect to a
prescribed uniformizer `πB` of `B`, together with — when that pole order is positive — a lift `σ`
of the residue field **and its reduction `s` modulo `𝔪_B ^ n`**, the Laurent coefficients of `ξ`,
and the separation property saying that no two coefficients outside `perfectCore κ_B p` sit at pole
orders differing by a `p`-power factor.

**Why `s` is returned and not just `σ`.** `σ` is a set-theoretic section of the residue map, so it
is not additive or multiplicative; what the prepared consumers need is the *ring* homomorphism
`s : κ_B →+* B ⧸ 𝔪_B ^ n` through which `σ` factors, i.e. `hs : ∀ x, Quotient.mk _ (σ x) = s x`.
That is `hlift`/`hliftMod` in
`exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_mixed_laurent`, and it cannot be
reconstructed from `σ` together with the residue section alone: multiplicativity modulo `𝔪_B ^ n`
is extra information, supplied by `exists_residueField_lift_mod_pow` and dropped by an earlier
version of this theorem.

**Why this is worth isolating.** Everything here is a function of `(B, L, M, p, πB)` alone: the
presentation comes from `exists_artinSchreier_presentation_minimal_poleOrder`, the lift from
`exists_residueField_lift_mod_pow (B := B)`, the expansion from `exists_laurent_expansion`, and
the separation from `exists_artinSchreier_laurent_presentation_without_related_poles`.  No base
ring `A`, no `K`.  The finite-support layer derives exactly this data inside its own proof and
then, because it goes on to build a Kummer extension over `A`, can only return the resulting
finite set and depth under an existential — which is what stops a consumer from observing that the
run over `A` and the run over a finite weakly unramified `A₁ ⊆ B` agree.

Exposing the data removes that obstruction without restructuring the layer: a consumer computes
the finite set and the depth from `coeff` and `n` itself, absorbs the finitely many perfect-core
roots into a finite étale `A₁` by
`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`, and then hands
  the
*prescribed* extension to `exists_baseChanged_laurent_reduction` and
`exists_isWeakSolution_of_baseChanged_artinSchreier_residue`, both of which already take the
extension as an input rather than producing one.  Nothing is duplicated: the layer keeps its own
proof, and this theorem is the same four calls in the same order with the base ring dropped.

The `K`-dependence of the presentation is avoided by instantiating
`exists_artinSchreier_presentation_of_charP` at `K := L`, legitimate because that theorem uses its
first argument only to derive `CharP L p`.

The disjunction is the layer's own `by_cases` on whether the minimal pole order vanishes: on the
left `ξ` is already integral, which is the unramified branch and needs no Laurent data.

Perfect-core membership is spelled out as `∀ m, ∃ y, y ^ p ^ m = coeff j` rather than written
`coeff j ∈ perfectCore κ_B p`, for the same reason the finite-support layer does so: the latter
needs an `ExpChar κ_B p` instance, which is derivable from `hp` and `[CharP L p]` inside the proof
but is not in scope where the statement is elaborated.  `mem_perfectCore_iff` converts. -/
theorem exists_artinSchreier_laurent_data
    (B L M : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [IsFractionRing B L] [Algebra L M]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (πB : B) (hπB : Irreducible πB) :
    ∃ (ξ : L) (z : M), z ^ p - z = algebraMap L M ξ ∧ Algebra.adjoin L {z} = ⊤ ∧
      (ξ ∈ (algebraMap B L).range ∨
        ∃ (n : ℕ) (σ : IsLocalRing.ResidueField B → B)
          (s : IsLocalRing.ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ n)
          (coeff : ℕ → IsLocalRing.ResidueField B) (b : B),
          0 < n ∧ (∀ x, IsLocalRing.residue B (σ x) = x) ∧
          (∀ x, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (σ x) = s x) ∧
          ξ = (∑ i ∈ Finset.range n,
            algebraMap B L (σ (coeff i)) * (algebraMap B L πB)⁻¹ ^ (n - i)) +
              algebraMap B L b ∧
          (∀ (m : ℕ) (ξ' : L) (z' : M), z' ^ p - z' = algebraMap L M ξ' →
            Algebra.adjoin L {z'} = ⊤ →
            algebraMap B L πB ^ m * ξ' ∈ (algebraMap B L).range → n ≤ m) ∧
          (∀ j ∈ Finset.range n,
            ¬ (∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = coeff j) →
            ∀ j' ∈ Finset.range n,
              ¬ (∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = coeff j') → j ≠ j' →
                ∀ r : ℕ, n - j' ≠ (n - j) * p ^ r)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
  obtain ⟨n, ξ, z, hz, hgen, hn, hmin⟩ :=
    exists_artinSchreier_presentation_minimal_poleOrder B L M p hπB
      (exists_artinSchreier_presentation_of_charP L L M p hp hdegree)
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨ξ, z, hz, hgen, Or.inl (by simpa using hn)⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    obtain ⟨σ, hσ, s, hs⟩ := exists_residueField_lift_mod_pow (B := B) p n hnpos
    obtain ⟨coeff, b, hexp⟩ := exists_laurent_expansion hπB σ hσ n ξ hn
    have htB : algebraMap B L πB ≠ 0 := algebraMap_ne_zero_of_irreducible L hπB
    have hI := maximalIdeal_pow_le_span_pow_of_irreducible hπB n
    have hP : ∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = 0 :=
      fun m => ⟨0, zero_pow (pow_pos hp.pos m).ne'⟩
    obtain ⟨ξ', z', coeff', b', hz', hgen', hexp', hsep⟩ :=
      exists_artinSchreier_laurent_presentation_without_related_poles p πB htB n
        ((IsLocalRing.maximalIdeal B) ^ n) hI σ s hs
        (fun x => ∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = x) hP
        ξ z coeff b hz hgen hexp
    exact ⟨ξ', z', hz', hgen',
      Or.inr ⟨n, σ, s, coeff', b', hnpos, hσ, hs, hexp', hmin, hsep⟩⟩

/-- **The wild support of a Laurent expansion, with its terminal depths.**

From the coefficients of an Artin–Schreier parameter and the separation property returned by
`exists_artinSchreier_laurent_data`, the wild index set

  `J = {j < n : coeff j ∉ perfectCore κ_B p}`

together with, at each `j ∈ J`, a terminal Frobenius depth `depth j` and a `root j` satisfying
`root j ^ (p ^ depth j) = coeff j` and admitting no further `p`-th root.

This is the input `exists_shared_orbit_parameters` wants, and it is why that lemma must be applied
to `J` and **not** to all of `Finset.range n`: the separation property holds precisely between
coefficients *outside* the perfect core, which is what
`exists_artinSchreier_laurent_presentation_without_related_poles` arranges, and specialising to the
full range makes it fail — for `p = 2` already at `n = 3`, `j = 2`, `j' = 1`.

Note that the parameters lemma needs only numerical data (`n`, `J`, `depth`), so a family of
conjugate factors can be prepared together even though their residue fields are pairwise different
types. The depths come from `exists_pow_eq_and_not_pow_of_notMem_perfectCore`, the intrinsic form
carrying no hypothesis relating `κ_A` to `κ_B`: the depth is spent inside `κ_B`, before any base
field is interrogated, which is what lets the preparation precede the choice of base extension.

Off `J` the returned `depth` and `root` are junk, as the guards make explicit. A consumer feeding
the single-factor endpoint, whose `hpow` and `hpoleMax` range over all of `Finset.range n`, extends
them there by giving each perfect-core position the depth `rank` and a `p ^ rank`-th root from
`exists_mem_perfectCore_pow_eq`; such a position then has scaled pole order
`(n - i) * p ^ (rank - rank) = n - i ≤ n`, which the large-pole clause puts strictly below the
distinguished position. -/
theorem exists_wildSupport_of_laurent_data
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (p : ℕ) [ExpChar (IsLocalRing.ResidueField B) p]
    (n : ℕ) (coeff : ℕ → IsLocalRing.ResidueField B)
    (hsep : ∀ j ∈ Finset.range n,
      ¬ (∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = coeff j) →
      ∀ j' ∈ Finset.range n,
        ¬ (∀ m : ℕ, ∃ y : IsLocalRing.ResidueField B, y ^ p ^ m = coeff j') → j ≠ j' →
          ∀ r : ℕ, n - j' ≠ (n - j) * p ^ r) :
    ∃ (J : Finset ℕ) (depth : ℕ → ℕ) (root : ℕ → IsLocalRing.ResidueField B),
      (∀ j, j ∈ J ↔ (j ∈ Finset.range n ∧
          coeff j ∉ perfectCore (IsLocalRing.ResidueField B) p)) ∧
      (∀ j ∈ J, j < n) ∧
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ r : ℕ, n - j' ≠ (n - j) * p ^ r) ∧
      (∀ j ∈ J, root j ^ (p ^ depth j) = coeff j ∧
        ¬∃ z : IsLocalRing.ResidueField B, z ^ p = root j) := by
  classical
  have hchoice : ∀ j : ℕ, ∃ (rj : ℕ) (yj : IsLocalRing.ResidueField B),
      coeff j ∉ perfectCore (IsLocalRing.ResidueField B) p →
        yj ^ (p ^ rj) = coeff j ∧ ¬∃ z : IsLocalRing.ResidueField B, z ^ p = yj := by
    intro j
    by_cases hj : coeff j ∉ perfectCore (IsLocalRing.ResidueField B) p
    · obtain ⟨r, y, hy, hny⟩ := exists_pow_eq_and_not_pow_of_notMem_perfectCore p hj
      exact ⟨r, y, fun _ => ⟨hy, hny⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose depth root hdr using hchoice
  refine ⟨(Finset.range n).filter
      (fun j => coeff j ∉ perfectCore (IsLocalRing.ResidueField B) p),
    depth, root, fun j => by simp [Finset.mem_filter], ?_, ?_, ?_⟩
  · exact fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  · intro j hj j' hj' hne r
    exact hsep j (Finset.mem_filter.mp hj).1
      (fun hc => (Finset.mem_filter.mp hj).2 (mem_perfectCore_iff.mpr hc))
      j' (Finset.mem_filter.mp hj').1
      (fun hc => (Finset.mem_filter.mp hj').2 (mem_perfectCore_iff.mpr hc)) hne r
  · exact fun j hj => hdr j (Finset.mem_filter.mp hj).2

end IsDiscreteValuationRing
