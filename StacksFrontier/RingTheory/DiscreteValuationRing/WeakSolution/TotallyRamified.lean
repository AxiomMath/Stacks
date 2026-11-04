module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Substitution
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Totally ramified base change of a weakly unramified extension

If `A → B` is weakly unramified and `K₁ / K` is a finite separable extension totally ramified
with respect to `A`, then the base change `A₁ → B₁` is again a weakly unramified extension of
discrete valuation rings (Tag 09ER).
-/

@[expose] public section

open scoped Pointwise TensorProduct

universe uk uA uB uK uL uK₁ uL₁ uA₁ uB₁ v u

namespace IsDiscreteValuationRing

/-! ### Totally ramified base change of a weakly unramified extension -/

private theorem isDomain_of_maximalIdeal_eq_span_regular
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (π : R) (hπ : IsRegular π)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {π}) : IsDomain R := by
  have hreg : ∀ x : R, x ≠ 0 → IsRegular x := by
    intro x hx
    have hf : FiniteMultiplicity π x := by
      by_contra h
      apply hx
      have hxmem : x ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n := by
        simp only [Submodule.mem_iInf, hm, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton]
        have hh : ∀ n : ℕ, π ^ (n + 1) ∣ x := by
          simpa only [FiniteMultiplicity, not_exists, not_not] using h
        intro n
        exact (pow_dvd_pow π (Nat.le_succ n)).trans (hh n)
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
        Submodule.mem_bot] at hxmem
    obtain ⟨c, heq, hc⟩ := hf.exists_eq_pow_mul_and_not_dvd
    have hu : IsUnit c := by
      by_contra hnu
      exact hc (by rw [← Ideal.mem_span_singleton, ← hm]; exact hnu)
    rw [heq]
    exact (hπ.pow _).mul hu.isRegular
  have : NoZeroDivisors R := ⟨fun {x y} h =>
    or_iff_not_imp_left.mpr fun hx => (hreg x hx).left (by simpa using h)⟩
  exact NoZeroDivisors.to_isDomain R

/-- The structure map from a local ring to an integral extension pulls a maximal ideal back to the
maximal ideal. -/
private theorem comap_eq_maximalIdeal_of_isMaximal
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Algebra.IsIntegral R S] (q : Ideal S) [q.IsMaximal] :
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q)

/-- The structure map from a domain `A` to the integral closure of `A` in a finite extension
`E` of its fraction field `K` is injective. -/
private theorem algebraMap_integralClosure_injective
    (A K E : Type*) [CommRing A] [IsDomain A] [Field K] [Field E] [Algebra A K]
    [IsFractionRing A K] [Algebra K E] [Algebra A E] [IsScalarTower A K E] :
    Function.Injective (algebraMap A (integralClosure A E)) := by
  intro a b h
  apply IsFractionRing.injective A K
  apply (algebraMap K E).injective
  simpa [IsScalarTower.algebraMap_apply A K E] using congrArg Subtype.val h

/-- If a finite separable extension `E` of the fraction field `K` of a discrete valuation ring
`A` is totally ramified with respect to `A`, then the integral closure of `A` in `E` is again a
discrete valuation ring. -/
@[sga "6 X 7.16" "special case"]
theorem isDiscreteValuationRing_integralClosure_of_totallyRamified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (htot : IsTotallyRamifiedWithRespectTo A K E) :
    IsDiscreteValuationRing (integralClosure A E) := by
  let S := integralClosure A E
  have : Module.Finite A S := IsIntegralClosure.finite A K E S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain A K E
  obtain ⟨m, hm, hml, huniq, _⟩ := htot
  have : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨m, hm, fun q hq => huniq q hq
    ⟨(comap_eq_maximalIdeal_of_isMaximal A S q).symm⟩⟩
  refine IsDiscreteValuationRing.mk fun h => ?_
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField
      (algebraMap_integralClosure_injective A K E)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h))

private theorem isDiscreteValuationRing_tensorProduct
    (A B S : Type*) [CommRing A] [CommRing B] [CommRing S]
    [IsDomain A] [IsDomain B] [IsDomain S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing S]
    [Algebra A B] [Algebra A S] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A S] [Module.Flat A S]
    (hweak : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (e : (S ⧸ IsLocalRing.maximalIdeal S) ≃ₐ[A]
      (A ⧸ IsLocalRing.maximalIdeal A)) :
    ∃ hd : IsDomain (B ⊗[A] S),
      let := hd
      ∃ hv : IsDiscreteValuationRing (B ⊗[A] S),
        let := hv
        Ideal.map Algebra.TensorProduct.includeRight.toRingHom
          (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal (B ⊗[A] S) := by
  let T := B ⊗[A] S
  let f : S →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let J := Ideal.map f (IsLocalRing.maximalIdeal S)
  have hJ : J.IsMaximal := by
    let eqv : (T ⧸ J) ≃+* (B ⧸ IsLocalRing.maximalIdeal B) :=
      (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B S B
        (IsLocalRing.maximalIdeal S)).symm.toRingEquiv |>.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) e).toRingEquiv) |>.trans
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
          (IsLocalRing.maximalIdeal A)).symm.toRingEquiv |>.trans
        (Ideal.quotEquivOfEq hweak)
    exact Ideal.Quotient.maximal_of_isField J
      (MulEquiv.isField
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance) eqv.toMulEquiv)
  have hJle : ∀ q : Ideal T, q.IsMaximal → J ≤ q := by
    intro q hq
    let := hq
    have hqB : q.comap (algebraMap B T) = IsLocalRing.maximalIdeal B :=
      comap_eq_maximalIdeal_of_isMaximal B T q
    have hqA : q.comap (algebraMap A T) = IsLocalRing.maximalIdeal A := by
      rw [IsScalarTower.algebraMap_eq A B T, ← Ideal.comap_comap, hqB]
      exact IsLocalRing.maximalIdeal_comap (algebraMap A B)
    have hqS : (q.comap f).IsMaximal := by
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A)
      have heq : (q.comap f).comap (algebraMap A S) = IsLocalRing.maximalIdeal A := by
        rw [Ideal.comap_comap]
        change q.comap ((Algebra.TensorProduct.includeRight : S →ₐ[A] T).toRingHom.comp
          (algebraMap A S)) = _
        exact (congrArg (fun k : A →+* T => q.comap k)
          (Algebra.TensorProduct.includeRight : S →ₐ[A] T).comp_algebraMap).trans hqA
      rw [heq]
      infer_instance
    exact Ideal.map_le_iff_le_comap.mpr (IsLocalRing.eq_maximalIdeal hqS).ge
  have : IsLocalRing T := IsLocalRing.of_unique_max_ideal
    ⟨J, hJ, fun q hq => (hJ.eq_of_le hq.ne_top (hJle q hq)).symm⟩
  have hmax : IsLocalRing.maximalIdeal T = J := (IsLocalRing.eq_maximalIdeal hJ).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hmπ : IsLocalRing.maximalIdeal T = Ideal.span {f π} := by
    rw [hmax]
    change Ideal.map f (IsLocalRing.maximalIdeal S) = _
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have : IsNoetherianRing T := isNoetherian_of_tower B (inferInstanceAs (IsNoetherian B T))
  have hreg : IsRegular (f π) := by
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible A
    have haS : algebraMap A S a ∈ IsLocalRing.maximalIdeal S := by
      change a ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap A S)
      rw [comap_eq_maximalIdeal_of_isMaximal A S, ha.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self a
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at haS
    obtain ⟨c, hc⟩ := haS
    have hregA : IsRegular (algebraMap A T a) := by
      rw [IsScalarTower.algebraMap_apply A B T]
      exact (Commute.isRegular_iff fun _ => mul_comm _ _).mpr <| IsSMulRegular.of_flat (S := T)
        (IsRegular.of_ne_zero ((map_ne_zero_iff (algebraMap A B)
          (FaithfulSMul.algebraMap_injective A B)).mpr ha.ne_zero)).left
    have heq : algebraMap A T a = f π * f c := by
      rw [← map_mul, ← hc]
      exact ((Algebra.TensorProduct.includeRight : S →ₐ[A] T).commutes a).symm
    rw [heq] at hregA
    exact hregA.of_mul_left
  have : IsDomain T := isDomain_of_maximalIdeal_eq_span_regular T (f π) hreg hmπ
  have : (IsLocalRing.maximalIdeal T).IsPrincipal := by
    rw [hmπ]
    infer_instance
  have : IsPrincipalIdealRing T := by
    apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain T).out 5 1).mp
    infer_instance
  have hv : IsDiscreteValuationRing T := IsDiscreteValuationRing.mk (by
    rw [hmπ, ne_eq, Ideal.span_singleton_eq_bot]
    exact hreg.ne_zero)
  exact ⟨inferInstance, hv, hmax.symm⟩

private theorem isFractionRing_tensorProduct_of_isDiscreteValuationRing
    (A B S K L E : Type*) [CommRing A] [CommRing B] [CommRing S]
    [Field K] [Field L] [Field E] [IsDomain B] [IsDomain S]
    [Algebra A B] [Algebra A S]
    [Algebra K L] [Algebra K E] [Algebra B L] [Algebra S E]
    [FaithfulSMul A B] [FaithfulSMul A S] [Module.Flat A B] [Module.Flat A S]
    [IsFractionRing B L] [IsFractionRing S E]
    [IsDiscreteValuationRing S] [IsDomain (B ⊗[A] S)]
    [IsDiscreteValuationRing (B ⊗[A] S)]
    (g : B ⊗[A] S →+* L ⊗[K] E)
    (hg : ∀ b s, g (b ⊗ₜ[A] s) = algebraMap B L b ⊗ₜ[K] algebraMap S E s)
    (hm : Ideal.map Algebra.TensorProduct.includeRight.toRingHom
      (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal (B ⊗[A] S)) :
    let := g.toAlgebra
    IsFractionRing (B ⊗[A] S) (L ⊗[K] E) := by
  let T := B ⊗[A] S
  let U := L ⊗[K] E
  let := g.toAlgebra
  have hiB : Function.Injective (Algebra.TensorProduct.includeLeft : B →ₐ[A] T) :=
    Algebra.TensorProduct.includeLeft_injective (FaithfulSMul.algebraMap_injective A S)
  have hiS : Function.Injective (Algebra.TensorProduct.includeRight : S →ₐ[A] T) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective A B)
  have hunits : ∀ x : nonZeroDivisors T, IsUnit (g x) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
    have hπT : Irreducible ((Algebra.TensorProduct.includeRight : S →ₐ[A] T) π) := by
      apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      rw [← hm, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
      rfl
    intro x
    obtain ⟨n, u, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp x.property) hπT
    rw [hx, map_mul, map_pow]
    refine (u.isUnit.map g).mul (IsUnit.pow _ ?_)
    change IsUnit (g (1 ⊗ₜ[A] π))
    rw [hg, map_one]
    exact (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hπ.ne_zero)).map
      (Algebra.TensorProduct.includeRight : E →ₐ[K] U)
  have hinj : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro x hx
    by_contra hn
    have hu := hunits ⟨x, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩
    rw [hx] at hu
    exact not_isUnit_zero hu
  refine ⟨hunits, ?_, fun h => ⟨1, by simpa using hinj h⟩⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨⟨0, 1⟩, by simp⟩
  | tmul l e =>
    obtain ⟨⟨b, d⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors B) l
    obtain ⟨⟨s, t⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors S) e
    have hd : (d.val ⊗ₜ[A] t.val : T) ≠ 0 := by
      have heq : (d.val ⊗ₜ[A] t.val : T) =
          (Algebra.TensorProduct.includeLeft : B →ₐ[A] T) d.val *
            (Algebra.TensorProduct.includeRight : S →ₐ[A] T) t.val := by simp
      rw [heq]
      exact mul_ne_zero ((map_ne_zero_iff _ hiB).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp d.property))
        ((map_ne_zero_iff _ hiS).mpr (mem_nonZeroDivisors_iff_ne_zero.mp t.property))
    refine ⟨⟨b ⊗ₜ[A] s, ⟨d.val ⊗ₜ[A] t.val, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩⟩, ?_⟩
    change (l ⊗ₜ[K] e) * g (d.val ⊗ₜ[A] t.val) = g (b ⊗ₜ[A] s)
    rw [hg, hg, Algebra.TensorProduct.tmul_mul_tmul, hb, hs]
  | add z w hz hw =>
    obtain ⟨⟨a, d⟩, ha⟩ := hz
    obtain ⟨⟨b, e⟩, hb⟩ := hw
    refine ⟨⟨a * e + b * d, d * e⟩, ?_⟩
    change (z + w) * g (d.val * e.val) = g (a * e.val + b * d.val)
    change z * g d.val = g a at ha
    change w * g e.val = g b at hb
    simp only [map_mul, map_add]
    calc
      (z + w) * (g d.val * g e.val) =
          (z * g d.val) * g e.val + (w * g e.val) * g d.val := by ring
      _ = g a * g e.val + g b * g d.val := by rw [ha, hb]

/-- A finite separable extension totally ramified with respect to the lower discrete valuation
ring preserves a weakly unramified extension after tensor-product base change. The tensor
product is canonically the integral closure in the base-changed fraction field. -/
@[stacks 09ER]
theorem isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [FiniteDimensional K K₁] [Algebra.IsSeparable K K₁]
    (hweak : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (htot : IsTotallyRamifiedWithRespectTo A K K₁) :
    let A₁ := integralClosure A K₁
    let B₁ := B ⊗[A] A₁
    let L₁ := L ⊗[K] K₁
    let C₁ := integralClosure B L₁
    ∃ hL₁ : IsField L₁,
      letI := hL₁.toField
      ∃ hA₁ : IsDiscreteValuationRing A₁,
        letI := hA₁
        ∃ hBdom : IsDomain B₁,
          letI := hBdom
          ∃ hB₁ : IsDiscreteValuationRing B₁,
            letI := hB₁
            let f : A₁ →+* B₁ := Algebra.TensorProduct.includeRight.toRingHom
            Function.Injective f ∧
              Ideal.map f (IsLocalRing.maximalIdeal A₁) = IsLocalRing.maximalIdeal B₁ ∧
              ∃ hCdom : IsDomain C₁,
                letI := hCdom
                ∃ hC₁ : IsDiscreteValuationRing C₁,
                  letI := hC₁
                  ∃ _ : IsFractionRing C₁ L₁,
                    ∃ e : B₁ ≃ₐ[B] C₁,
                      (∀ a : A₁,
                        ((e ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B₁) a) : C₁)
                            : L₁) =
                          (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L₁) (a : K₁)) ∧
                        let f' : A₁ →+* C₁ :=
                          e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
                        Function.Injective f' ∧
                          Ideal.map f' (IsLocalRing.maximalIdeal A₁) =
                            IsLocalRing.maximalIdeal C₁  := by
  classical
  let A₁ := integralClosure A K₁
  let B₁ := B ⊗[A] A₁
  let L₁ := L ⊗[K] K₁
  let C₁ := integralClosure B L₁
  have : Module.Finite A A₁ := IsIntegralClosure.finite A K K₁ A₁
  have : IsDiscreteValuationRing A₁ :=
    isDiscreteValuationRing_integralClosure_of_totallyRamified A K K₁ htot
  have hinjA : Function.Injective (algebraMap A A₁) :=
    algebraMap_integralClosure_injective A K K₁
  have : FaithfulSMul A A₁ := (faithfulSMul_iff_algebraMap_injective A A₁).mpr hinjA
  have : Module.IsTorsionFree A A₁ := Module.isTorsionFree_iff_algebraMap_injective.mpr hinjA
  have : Module.Flat A A₁ := inferInstance
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A B)
  have : Module.Flat A B := inferInstance
  obtain ⟨m, hm, hml, _, hf⟩ := htot
  have heqm : m = IsLocalRing.maximalIdeal A₁ := IsLocalRing.eq_maximalIdeal hm
  rw [heqm] at hf hml
  let := hml
  let := Ideal.Quotient.algebraOfLiesOver (IsLocalRing.maximalIdeal A₁)
    (IsLocalRing.maximalIdeal A)
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : Module.Free (A ⧸ IsLocalRing.maximalIdeal A)
      (A₁ ⧸ IsLocalRing.maximalIdeal A₁) := Module.Free.of_divisionRing _ _
  have hfmax : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
      (A₁ ⧸ IsLocalRing.maximalIdeal A₁) = 1 := by simpa using hf
  have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfmax
  let er : (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[A]
      (A₁ ⧸ IsLocalRing.maximalIdeal A₁) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom A _ _) hbij
  obtain ⟨hBdom, hB₁, hmax⟩ := isDiscreteValuationRing_tensorProduct A B A₁ hweak er.symm
  let := hBdom
  let := hB₁
  let j : A₁ →ₐ[A] L₁ :=
    ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L₁).restrictScalars A).comp
      (integralClosure A K₁).val
  let g : B₁ →ₐ[B] L₁ := Algebra.TensorProduct.lift (Algebra.ofId B L₁) j
    (fun _ _ => Commute.all _ _)
  have hg : ∀ b a, g (b ⊗ₜ[A] a) = algebraMap B L b ⊗ₜ[K] (a : K₁) := by
    intro b a
    change (algebraMap B L b ⊗ₜ[K] (1 : K₁)) * (1 ⊗ₜ[K] (a : K₁)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let : Algebra B₁ L₁ := g.toRingHom.toAlgebra
  let : IsScalarTower B B₁ L₁ :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := B₁) (A := L₁) (fun x => (g.commutes x).symm)
  let : IsFractionRing A₁ K₁ := integralClosure.isFractionRing_of_finite_extension K K₁
  let : IsFractionRing B₁ L₁ :=
    isFractionRing_tensorProduct_of_isDiscreteValuationRing A B A₁ K L K₁
      g.toRingHom hg hmax
  have hL₁ : IsField L₁ := (IsFractionRing.toField B₁).toIsField
  refine ⟨hL₁, ?_⟩
  let := hL₁.toField
  refine ⟨inferInstance, hBdom, hB₁, ?_⟩
  have hright : Function.Injective (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B₁) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective A B)
  refine ⟨hright, hmax, inferInstance, ?_⟩
  let e : B₁ ≃ₐ[B] C₁ := IsIntegralClosure.equiv B B₁ L₁ C₁
  let : IsDiscreteValuationRing C₁ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  let : IsFractionRing C₁ L₁ := integralClosure.isFractionRing_of_finite_extension L L₁
  refine ⟨inferInstance, inferInstance, e, ?_, ?_⟩
  · intro a
    change algebraMap C₁ L₁ (e (1 ⊗ₜ[A] a)) = _
    rw [IsIntegralClosure.algebraMap_equiv]
    change g (1 ⊗ₜ[A] a) = _
    simpa using hg 1 a
  · refine ⟨e.injective.comp hright, ?_⟩
    rw [← Ideal.map_map, hmax]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

end IsDiscreteValuationRing
