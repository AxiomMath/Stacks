module

public import StacksFrontier.Algebra.Module.RegularLocalNakayama
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.Algebra.Module.TwoTermComplex.Noetherian

/-!
# Cohomology and base change for a map to a two-term complex, over a ring with regular stalks

Let `R` be a ring and `(φ₀, φ₁)` a map from a complex `C₀ ⟶ C₁ ⟶ C₂` of flat `R`-modules to a
two-term complex `D₀ ⟶ D₁` of flat `R`-modules, whose cohomology stays finite after every
Noetherian base change. At the maximal ideals `𝔪` of `R` at which `R` is regular:

* `Stacks.ConeNakayama.isExactAt_cone_localization`: if the map is onto on `H⁰` and one-to-one on
  `H¹` after base change to the residue field `R/𝔪`, it is so after base change to `R_𝔪`;
* `Stacks.ConeNakayama.exists_lift_of_surjZero`: in that case a cocycle `w` of `D` lifts, after
  multiplication by some `a ∉ 𝔪`, to a cocycle of `C`;
* `Stacks.ConeNakayama.ker_coneD₀_eq_bot`: if the map is injective on `H⁰` after base change to
  every residue field, it is injective on `H⁰` over `R`;
* `Stacks.ConeNakayama.ker_d₀_eq_bot`: if `R` is a domain and `H⁰` vanishes after base change to
  one residue field, it vanishes over `R`.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public section

open TensorProduct IsLocalRing

universe u

namespace Stacks.ConeNakayama

open Stacks.FlatComplexNakayama

variable {R : Type u} [CommRing R]
variable {C₀ C₁ C₂ D₀ D₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [Module R C₀] [Module R C₁] [Module R C₂] [Module R D₀]
  [Module R D₁] (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (δ₀ : D₀ →ₗ[R] D₁) (φ₀ : C₀ →ₗ[R] D₀)
  (φ₁ : C₁ →ₗ[R] D₁)

/-- The residue field of `R` at a maximal ideal is the residue field of the localization, as an
`R`-algebra. -/
noncomputable def quotEquivLocalization (m : Ideal R) [m.IsMaximal] :
    (R ⧸ m) ≃ₐ[R] (Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m)) :=
  AlgEquiv.ofRingEquiv (f := IsLocalization.AtPrime.equivQuotMaximalIdeal m
    (Localization.AtPrime m)) fun _ => rfl

/-- The map `M ⟶ R_𝔪 ⊗ M` is a localization. -/
theorem isLocalizedModule_tmul (m : Ideal R) [m.IsPrime] (M : Type u) [AddCommGroup M]
    [Module R M] :
    IsLocalizedModule m.primeCompl (TensorProduct.mk R (Localization.AtPrime m) M 1) :=
  (isLocalizedModule_iff_isBaseChange m.primeCompl (Localization.AtPrime m) _).mpr
    (TensorProduct.isBaseChange R M (Localization.AtPrime m))

/-- **Onto on `H⁰` and one-to-one on `H¹` propagates from the residue field to the local
ring.** -/
theorem isExactAt_cone_localization [Module.Flat R C₂] [Module.Flat R D₁]
    (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hfinC : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsNoetherianRing S],
      Module.Finite S (homology d₀ d₁ S))
    (hfinD : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsNoetherianRing S],
      Module.Finite S (LinearMap.ker (δ₀.baseChange S)))
    (m : Ideal R) [m.IsMaximal] [IsRegularLocalRing (Localization.AtPrime m)]
    (hbase : SurjZero d₀ δ₀ φ₀ (R ⧸ m) ∧ InjOne d₀ d₁ δ₀ φ₁ (R ⧸ m)) :
    SurjZero d₀ δ₀ φ₀ (Localization.AtPrime m) ∧ InjOne d₀ d₁ δ₀ φ₁ (Localization.AtPrime m) := by
  rw [← isExactAt_cone_iff d₀ d₁ δ₀ φ₀ φ₁ _ hφ] at hbase ⊢
  have : Module.Flat R (C₂ × D₁) := Stacks.TwoTermComplex.flat_prod
  have hcone := coneD₁_comp_coneD₀ d₀ d₁ δ₀ φ₀ φ₁ hd hφ
  refine isExactAt_of_isRegularLocalRing (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) hcone ?_ ?_
  · intro S _ _ _
    exact finite_homology_cone d₀ d₁ δ₀ φ₀ φ₁ S hφ (hfinD S) (hfinC S)
  · exact isExactAt_congr _ _ (quotEquivLocalization m) hbase

/-- **Spreading out a lift.** If the map is onto on `H⁰` over `R_𝔪`, then every cocycle `w` of
`D` lifts, after multiplication by some `a ∉ 𝔪`, to a cocycle of `C`. -/
theorem exists_lift_of_surjZero (m : Ideal R) [m.IsPrime]
    (h : SurjZero d₀ δ₀ φ₀ (Localization.AtPrime m)) (w : D₀) (hw : δ₀ w = 0) :
    ∃ a ∉ m, ∃ y : C₀, d₀ y = 0 ∧ φ₀ y = a • w := by
  set Rm := Localization.AtPrime m
  have hloc := isLocalizedModule_tmul m C₀
  obtain ⟨c, hc0, hcw⟩ := h ((1 : Rm) ⊗ₜ w) (by simp [hw])
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.mk'_surjective m.primeCompl
    (TensorProduct.mk R Rm C₀ 1) c
  simp only [Function.uncurry_apply_pair] at hxs
  subst hxs
  have key : ∀ (N : Type u) [AddCommGroup N] [Module R N] (g : C₀ →ₗ[R] N),
      g.baseChange Rm (IsLocalizedModule.mk' (TensorProduct.mk R Rm C₀ 1) x s) =
        IsLocalizedModule.mk' (TensorProduct.mk R Rm N 1) (g x) s := by
    intro N _ _ g
    have hN := isLocalizedModule_tmul m N
    symm
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def]
    have hc : (s : R) • IsLocalizedModule.mk' (TensorProduct.mk R Rm C₀ 1) x s =
        TensorProduct.mk R Rm C₀ 1 x := by
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    rw [← LinearMap.map_smul_of_tower, hc]
    simp
  rw [key] at hc0 hcw
  have hN1 := isLocalizedModule_tmul m C₁
  rw [IsLocalizedModule.mk'_eq_zero'] at hc0
  obtain ⟨s₁, hs₁⟩ := hc0
  have hN2 := isLocalizedModule_tmul m D₀
  have hcw' : IsLocalizedModule.mk' (TensorProduct.mk R Rm D₀ 1) (φ₀ x) s =
      IsLocalizedModule.mk' (TensorProduct.mk R Rm D₀ 1) w (1 : m.primeCompl) := by
    rw [IsLocalizedModule.mk'_one]; exact hcw
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hcw'
  obtain ⟨s₂, hs₂⟩ := hcw'
  simp only [one_smul, Submonoid.smul_def] at hs₂ hs₁
  refine ⟨((s₁ * s₂ * s : m.primeCompl) : R), (s₁ * s₂ * s).2, ((s₁ * s₂ : m.primeCompl) : R) • x,
    ?_, ?_⟩
  · rw [map_smul, Submonoid.coe_mul, mul_comm, mul_smul, hs₁, smul_zero]
  · rw [map_smul, Submonoid.coe_mul, mul_smul, ← hs₂, Submonoid.coe_mul, ← mul_smul, ← mul_smul,
      mul_assoc, Submonoid.coe_mul, mul_assoc]

/-- A kernel element `x` of `f` gives the kernel element `1 ⊗ x` of its base change. -/
private theorem one_tmul_mem_ker_baseChange {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (S : Type u) [CommRing S] [Algebra R S] (f : M →ₗ[R] N) {x : M}
    (hx : f x = 0) : (1 : S) ⊗ₜ x ∈ LinearMap.ker (f.baseChange S) := by
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, hx, tmul_zero]

/-- **Injectivity on `H⁰` over `R` from injectivity over every residue field**, at maximal
ideals where `R` is regular. -/
theorem ker_coneD₀_eq_bot [Module.Flat R C₁] [Module.Flat R D₀]
    (hfinK : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsNoetherianRing S],
      Module.Finite S (LinearMap.ker (d₀.baseChange S)))
    (hreg : ∀ (m : Ideal R) [m.IsMaximal], IsRegularLocalRing (Localization.AtPrime m))
    (hbase : ∀ (m : Ideal R) [m.IsMaximal],
      LinearMap.ker ((coneD₀ d₀ φ₀).baseChange (R ⧸ m)) = ⊥) :
    LinearMap.ker (coneD₀ d₀ φ₀) = ⊥ := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal],
      LinearMap.ker ((coneD₀ d₀ φ₀).baseChange (Localization.AtPrime m)) = ⊥ := by
    intro m _
    have := hreg m
    have : Module.Flat R (C₁ × D₀) := Stacks.TwoTermComplex.flat_prod
    refine ker_eq_bot_of_isRegularLocalRing (coneD₀ d₀ φ₀) ?_ ?_
    · intro S _ _ _
      have h := hfinK S
      have hle : LinearMap.ker ((coneD₀ d₀ φ₀).baseChange S) ≤ LinearMap.ker (d₀.baseChange S) := by
        intro c hc
        have := congrArg (fun w => (TensorProduct.prodRight R S S C₁ D₀ w).1)
          (LinearMap.mem_ker.mp hc)
        simp only [prodRight_coneD₀, map_zero, Prod.fst_zero] at this
        exact this
      exact Module.Finite.of_injective (Submodule.inclusion hle)
        (Submodule.inclusion_injective hle)
    · exact ker_eq_bot_congr _ (quotEquivLocalization m) (hbase m)
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) C₀ 1) := fun P _ => isLocalizedModule_tmul P C₀
  refine Module.eq_zero_of_localization_maximal (Mₚ := fun P _ => Localization.AtPrime P ⊗[R] C₀)
    (f := fun P _ => TensorProduct.mk R (Localization.AtPrime P) C₀ 1) x (fun P _ => ?_)
  have := hloc P
  have hmem := one_tmul_mem_ker_baseChange (Localization.AtPrime P) (coneD₀ d₀ φ₀)
    (LinearMap.mem_ker.mp hx)
  rw [this] at hmem
  exact (Submodule.mem_bot _).mp hmem

/-- **Vanishing of `H⁰` from one residue field**, over a domain with a regular stalk there. -/
theorem ker_d₀_eq_bot [IsDomain R] [Module.Flat R C₀] [Module.Flat R C₁]
    (hfinK : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsNoetherianRing S],
      Module.Finite S (LinearMap.ker (d₀.baseChange S)))
    (m : Ideal R) [m.IsMaximal] [IsRegularLocalRing (Localization.AtPrime m)]
    (hbase : LinearMap.ker (d₀.baseChange (R ⧸ m)) = ⊥) :
    LinearMap.ker d₀ = ⊥ := by
  have hloc : LinearMap.ker (d₀.baseChange (Localization.AtPrime m)) = ⊥ :=
    ker_eq_bot_of_isRegularLocalRing d₀ (fun S _ _ _ => hfinK S)
      (ker_eq_bot_congr _ (quotEquivLocalization m) hbase)
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hmem := one_tmul_mem_ker_baseChange (Localization.AtPrime m) d₀ (LinearMap.mem_ker.mp hx)
  rw [hloc, Submodule.mem_bot] at hmem
  have hl := isLocalizedModule_tmul m C₀
  have h0 : IsLocalizedModule.mk' (TensorProduct.mk R (Localization.AtPrime m) C₀ 1) x
      (1 : m.primeCompl) = 0 := by rw [IsLocalizedModule.mk'_one]; exact hmem
  rw [IsLocalizedModule.mk'_eq_zero'] at h0
  obtain ⟨s, hs⟩ := h0
  have hs0 : (s : R) ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero fun h => s.2 (h ▸ m.zero_mem)
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors hs0).right_eq_zero_of_smul hs

end Stacks.ConeNakayama

end
