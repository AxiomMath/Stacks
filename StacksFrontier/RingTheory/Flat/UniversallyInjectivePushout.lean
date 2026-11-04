module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Universal injectivity across a pushout of rings

Let `R → A` and `R → B` be ring maps and let `C = B ⊗_R A` be their pushout. If `u : M → N` is
a map of `A`-modules which is universally injective as a map of `R`-modules, then its base
change `C ⊗_A u` is universally injective as a map of `B`-modules: for a `B`-module `Q` the
map `(C ⊗_A M) ⊗_B Q → (C ⊗_A N) ⊗_B Q` is `u ⊗_R Q`, read through the canonical
identification `(C ⊗_A M) ⊗_B Q ≅ M ⊗_R Q`.

The form proved here asks less: universal injectivity is only needed after inverting an element
`a ∈ R` which becomes a unit in `B`. That is the form in which Stacks 05IA delivers it.

## Main results

* `Stacks.UniversalInjectivity.rTensor_injective_of_localizedModule_powers`: if `a` acts
  bijectively on `Q`, injectivity of `u_a ⊗_R Q` gives injectivity of `u ⊗_R Q`.
* `Stacks.UniversalInjectivity.universallyInjective_baseChange_of_isPushout`: the statement
  above.

## References

* [Stacks Project, Tag 058I](https://stacks.math.columbia.edu/tag/058I)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.UniversalInjectivity

/-- If `a ∈ R` acts bijectively on `Q`, then injectivity of `u_a ⊗_R Q`, for the localization
`u_a` of `u` at the powers of `a`, gives injectivity of `u ⊗_R Q`: the localization map
`M ⊗_R Q → M_a ⊗_R Q` is injective, because `a` already acts injectively on `M ⊗_R Q`. -/
theorem rTensor_injective_of_localizedModule_powers {R : Type u} [CommRing R]
    {M N Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] (u : M →ₗ[R] N) (a : R)
    (ha : Function.Bijective (LinearMap.lsmul R Q a))
    (h : Function.Injective
      (((LocalizedModule.map (Submonoid.powers a) u).restrictScalars R).rTensor Q)) :
    Function.Injective (u.rTensor Q) := by
  set S := Submonoid.powers a
  set ιM : M ⊗[R] Q →ₗ[R] LocalizedModule S M ⊗[R] Q :=
    AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap S M)
  set ιN : N ⊗[R] Q →ₗ[R] LocalizedModule S N ⊗[R] Q :=
    AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap S N)
  have hsq : ((LocalizedModule.map S u).restrictScalars R).rTensor Q ∘ₗ ιM = ιN ∘ₗ u.rTensor Q := by
    apply TensorProduct.ext'
    intro m q
    simp [ιM, ιN, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
  -- `a` acts injectively on `M ⊗[R] Q`
  set e : Q ≃ₗ[R] Q := LinearEquiv.ofBijective _ ha
  have hsmul : ∀ x : M ⊗[R] Q, a • x = (e.lTensor M) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m q => simp [e, TensorProduct.tmul_smul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  have hinj : Function.Injective ιM := by
    intro x y hxy
    have : IsLocalizedModule S ιM :=
      IsLocalizedModule.rTensor (R := R) (A := R) S (N := Q) (LocalizedModule.mkLinearMap S M)
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S ιM).mp hxy
    obtain ⟨k, hk⟩ := c.2
    have hpow : ∀ n : ℕ, ∀ x y : M ⊗[R] Q, a ^ n • x = a ^ n • y → x = y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro x y hxy'
        apply ih
        apply (e.lTensor M).injective
        rw [← hsmul, ← hsmul, ← mul_smul, ← mul_smul, ← pow_succ', hxy']
    apply hpow k
    have hk' : a ^ k = c := hk
    rw [hk']
    exact hc
  intro x y hxy
  apply hinj
  apply h
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hsq, LinearMap.comp_apply,
    LinearMap.comp_apply, hxy]

/-- **Universal injectivity across a pushout of rings.** Let `C` be the pushout of `R → A` and
`R → B`, let `u : M → N` be a map of `A`-modules, and let `a ∈ R` become a unit in `B`. If the
localization of `u` at the powers of `a` is universally injective as a map of `R`-modules, then
the base change `C ⊗_A u` is universally injective as a map of `B`-modules. -/
theorem universallyInjective_baseChange_of_isPushout {R A B C : Type u} [CommRing R]
    [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra A C] [Algebra B C] [IsScalarTower R A C] [IsScalarTower R B C]
    [Algebra.IsPushout R B A C] {M N : Type u} [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (u : M →ₗ[A] N) (a : R) (ha : IsUnit (algebraMap R B a))
    (h : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q], Function.Injective
      (((LocalizedModule.map (Submonoid.powers a) (u.restrictScalars R)).restrictScalars
        R).rTensor Q)) :
    UniversallyInjective ((u.baseChange C).restrictScalars B) := by
  intro Q _ _
  let : Module R Q := Module.compHom Q (algebraMap R B)
  have : IsScalarTower R B Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- `C ⊗[A] M ≃ B ⊗[R] M`
  set eM := Algebra.IsPushout.cancelBaseChange R B A C M
  set eN := Algebra.IsPushout.cancelBaseChange R B A C N
  set v : B ⊗[R] M →ₗ[B] B ⊗[R] N := (u.restrictScalars R).baseChange B
  have key : ((u.baseChange C).restrictScalars B) ∘ₗ eM.symm.toLinearMap =
      eN.symm.toLinearMap ∘ₗ v := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b m
    simp [eM, eN, v, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  have hsq₁ : (u.baseChange C).restrictScalars B =
      eN.symm.toLinearMap ∘ₗ v ∘ₗ eM.toLinearMap := by
    ext x
    have := congrArg (fun f ↦ f (eM x)) key
    simpa using this
  -- `(B ⊗[R] M) ⊗[B] Q ≃ Q ⊗[R] M`
  set fM : (B ⊗[R] M) ⊗[B] Q ≃ₗ[B] Q ⊗[R] M :=
    TensorProduct.comm B (B ⊗[R] M) Q ≪≫ₗ AlgebraTensorModule.cancelBaseChange R B B Q M
  set fN : (B ⊗[R] N) ⊗[B] Q ≃ₗ[B] Q ⊗[R] N :=
    TensorProduct.comm B (B ⊗[R] N) Q ≪≫ₗ AlgebraTensorModule.cancelBaseChange R B B Q N
  have hsq₂ : ∀ z, (u.restrictScalars R).lTensor Q (fM z) = fN (v.rTensor Q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x q =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m => simp [fM, fN, v]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- injectivity of `u ⊗[R] Q`
  have hu : Function.Injective ((u.restrictScalars R).rTensor Q) := by
    refine rTensor_injective_of_localizedModule_powers _ a ?_ (h Q)
    obtain ⟨w, hw⟩ := ha
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨(w⁻¹ : Bˣ).1 • y, ?_⟩⟩
    · have hxy' : (algebraMap R B a) • x = (algebraMap R B a) • y := hxy
      rw [← hw] at hxy'
      have := congrArg (fun z ↦ (w⁻¹ : Bˣ).1 • z) hxy'
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this
    · show (algebraMap R B a) • ((w⁻¹ : Bˣ).1 • y) = y
      rw [← hw, smul_smul, Units.mul_inv, one_smul]
  have hlu : Function.Injective ((u.restrictScalars R).lTensor Q) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj Q _).2 hu
  have hv : Function.Injective (v.rTensor Q) := by
    intro x y hxy
    apply fM.injective
    apply hlu
    rw [hsq₂, hsq₂, hxy]
  rw [hsq₁, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
  simp only [LinearMap.coe_comp]
  exact (LinearEquiv.rTensor Q eN.symm).injective.comp
    (hv.comp (LinearEquiv.rTensor Q eM).injective)

end Stacks.UniversalInjectivity
