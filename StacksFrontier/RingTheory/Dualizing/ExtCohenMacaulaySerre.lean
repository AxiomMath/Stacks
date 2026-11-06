module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.DepthLemmas.Ext
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Serre's condition `(S₂)` for an `Ext` into a Cohen–Macaulay module

Let `S` be a Noetherian local ring, `M` a finite Cohen–Macaulay `S`-module, `N` a finite
`S`-module killed by an ideal `I`, and `c ≤ depth_I(M)`.  Then `Ext^c_S(N, M)` satisfies the local
form of Serre's condition `(S₂)`:

`min(2, dim Supp Ext^c_S(N, M)) ≤ depth Ext^c_S(N, M)` .

## Main results

* `CategoryTheory.Abelian.Ext.smul_eq_zero_of_mem_annihilator`: an element of the annihilator of
  `N` acts by zero on `Ext^n_S(N, M)`.
* `Dualizing.extQuotSMulTopLinearEquiv`: the connecting map
  `Ext^c_S(N, M/xM) ≃ Ext^{c+1}_S(N, M)` for `x` regular on `M` and killing `N`, when
  `Ext^c_S(N, M) = 0`.
* `Dualizing.min_two_le_moduleDepth_ext_of_le_depth`: the bound above.
-/

@[expose] public section

open CategoryTheory Abelian

universe u

namespace CategoryTheory.Abelian.Ext

variable {S : Type u} [CommRing S]

/-- An element of the annihilator of `N` acts by zero on `Ext^n_S(N, M)`. -/
theorem smul_eq_zero_of_mem_annihilator {N M : ModuleCat.{u} S} {x : S}
    (hx : x ∈ Module.annihilator S N) {n : ℕ} (e : Ext N M n) : x • e = 0 := by
  have hzero : x • 𝟙 N = 0 := by
    ext m
    exact Module.mem_annihilator.mp hx m
  calc x • e = x • (Ext.mk₀ (𝟙 N)).comp e (zero_add n) := by rw [Ext.mk₀_id_comp]
    _ = (x • Ext.mk₀ (𝟙 N)).comp e (zero_add n) := (Ext.smul_comp _ _ _ x).symm
    _ = (Ext.mk₀ (x • 𝟙 N)).comp e (zero_add n) := by rw [Ext.mk₀_smul]
    _ = 0 := by rw [hzero, Ext.mk₀_zero, Ext.zero_comp]

end CategoryTheory.Abelian.Ext

namespace Dualizing

variable {S : Type u} [CommRing S]

/-- Let `x` be a nonzerodivisor on `M` which kills `N`.  If `Ext^c_S(N, M) = 0`, the connecting
map of the long exact sequence of `0 → M →(x) M → M/xM → 0` is an `S`-linear isomorphism
`Ext^c_S(N, M/xM) ≅ Ext^{c+1}_S(N, M)`. -/
noncomputable def extQuotSMulTopLinearEquiv {M N : ModuleCat.{u} S} {x : S}
    (hreg : IsSMulRegular M x) (hx : x ∈ Module.annihilator S N) (c : ℕ)
    (hc : Subsingleton (Ext N M c)) :
    Ext N (ModuleCat.of S (QuotSMulTop x M)) c ≃ₗ[S] Ext N M (c + 1) := by
  have hS := hreg.smulShortComplex_shortExact
  let f : Ext N (ModuleCat.of S (QuotSMulTop x M)) c →ₗ[S] Ext N M (c + 1) :=
    Ext.bilinearCompOfLinear S N (ModuleCat.of S (QuotSMulTop x M)) M c 1 (c + 1) rfl |>.flip
      hS.extClass
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ N hS e rfl he
    rw [← hy, @Subsingleton.elim _ hc y 0]
    exact Ext.zero_comp N c (Ext.mk₀ (ModuleCat.smulShortComplex M x).g) c (add_zero c)
  · intro y
    have hy : y.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero (c + 1)) = 0 := by
      rw [← Ext.smul_eq_comp_mk₀, Ext.smul_eq_zero_of_mem_annihilator hx]
    exact Ext.covariant_sequence_exact₁ N hS y hy rfl

/-- A module with at most one element satisfies the local form of `(S₂)`. -/
theorem min_two_le_moduleDepth_of_subsingleton [IsLocalRing S] (E : Type*) [AddCommGroup E]
    [Module S E] [Subsingleton E] :
    min (2 : ℕ∞) ((moduleSupportDim S E).unbotD 0) ≤ moduleDepth S E := by
  have hbot : moduleSupportDim S E = ⊥ := by
    unfold moduleSupportDim
    rw [topologicalKrullDim_eq_bot_iff_isEmpty]
    exact Set.isEmpty_coe_sort.mpr (Module.support_eq_empty_iff.mpr inferInstance)
  rw [hbot]
  simp

/-- A Cohen–Macaulay module satisfies the local form of `(S₂)`. -/
theorem min_two_le_moduleDepth_of_isCohenMacaulayAtMaximalIdeal [IsLocalRing S] (M : Type*)
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hM : Module.IsCohenMacaulayAtMaximalIdeal S M) :
    min (2 : ℕ∞) ((moduleSupportDim S M).unbotD 0) ≤ moduleDepth S M := by
  rcases subsingleton_or_nontrivial M with hsub | hnt
  · exact min_two_le_moduleDepth_of_subsingleton M
  · rw [moduleDepth_eq_depth, moduleSupportDim_eq_Module_supportDim]
    unfold Module.IsCohenMacaulayAtMaximalIdeal at hM
    rw [← hM, WithBot.unbotD_coe]
    exact min_le_right _ _

/-- Cancellation of `+ 1` in `WithBot ℕ∞`. -/
private theorem withBot_add_one_injective {a b : WithBot ℕ∞} (h : a + 1 = b + 1) : a = b := by
  induction a with
  | bot =>
    induction b with
    | bot => rfl
    | coe b => exact absurd h.symm (by simp [← WithBot.coe_one, ← WithBot.coe_add])
  | coe a =>
    induction b with
    | bot => exact absurd h (by simp [← WithBot.coe_one, ← WithBot.coe_add])
    | coe b =>
      rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      exact congrArg _ ((ENat.add_left_injective_of_ne_top ENat.one_ne_top) h)

/-- Let `S` be a Noetherian local ring, `I ⊆ S` an ideal, `N` a finite `S`-module killed by
`I` and `M` a finite Cohen–Macaulay `S`-module.  If `c ≤ depth_I(M)`, then

`min(2, dim Supp Ext^c_S(N, M)) ≤ depth Ext^c_S(N, M)` . -/
theorem min_two_le_moduleDepth_ext_of_le_depth [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal S) (N : ModuleCat.{u} S) [Module.Finite S N]
    (hN : I ≤ Module.annihilator S N) (c : ℕ) :
    ∀ (M : ModuleCat.{u} S) [Module.Finite S M], Module.IsCohenMacaulayAtMaximalIdeal S M →
      (c : ℕ∞) ≤ Module.depth S I M →
      min (2 : ℕ∞) ((moduleSupportDim S (Ext N M c)).unbotD 0) ≤ moduleDepth S (Ext N M c) := by
  induction c with
  | zero =>
    intro M _ hM _
    let e : Ext N M 0 ≃ₗ[S] (N →ₗ[S] M) := Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
    rw [moduleSupportDim_eq_of_linearEquiv e, moduleDepth_eq_of_linearEquiv e]
    exact propertySk_linearMap_local 2 (Or.inr rfl)
      (min_two_le_moduleDepth_of_isCohenMacaulayAtMaximalIdeal M hM)
  | succ c ih =>
    intro M _ hM hc
    by_cases hI : I = ⊤
    · have h1 : (1 : S) ∈ Module.annihilator S N := hN (hI ▸ Submodule.mem_top)
      have : Subsingleton (Ext N M (c + 1)) := subsingleton_of_forall_eq 0 fun e => by
        rw [← one_smul S e, Ext.smul_eq_zero_of_mem_annihilator h1]
      exact min_two_le_moduleDepth_of_subsingleton _
    rcases subsingleton_or_nontrivial M with hsub | hnt
    · have h0 : (1 : S) • 𝟙 M = 0 := by
        ext m
        exact Subsingleton.elim _ _
      have : Subsingleton (Ext N M (c + 1)) := subsingleton_of_forall_eq 0 fun e => by
        rw [← one_smul S e, Ext.smul_eq_comp_mk₀, h0, Ext.mk₀_zero, Ext.comp_zero]
      exact min_two_le_moduleDepth_of_subsingleton _
    have hImax : I ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hI
    have hdepth0 : Module.depth S I M ≠ 0 := fun h0 => by simp [h0] at hc
    obtain ⟨x, hxI, hreg⟩ := Module.exists_mem_isSMulRegular_of_depth_ne_zero I hdepth0
    have hxm : x ∈ IsLocalRing.maximalIdeal S := hImax hxI
    let M' : ModuleCat.{u} S := ModuleCat.of S (QuotSMulTop x M)
    have hdI := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 x hxI
      hreg
    have hdm := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (IsLocalRing.maximalIdeal S) M).1 x hxm hreg
    have hsd := Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hxm
    have hM' : Module.IsCohenMacaulayAtMaximalIdeal S M' := by
      unfold Module.IsCohenMacaulayAtMaximalIdeal at hM ⊢
      refine withBot_add_one_injective ?_
      show ((Module.depth S (IsLocalRing.maximalIdeal S) (QuotSMulTop x M) : ℕ∞) :
        WithBot ℕ∞) + 1 = Module.supportDim S (QuotSMulTop x M) + 1
      rw [hsd, ← hM, ← hdm]
      rfl
    have hc' : (c : ℕ∞) ≤ Module.depth S I M' := by
      show (c : ℕ∞) ≤ Module.depth S I (QuotSMulTop x M)
      rw [← hdI] at hc
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp (by exact_mod_cast hc)
    have hIM : I • (⊤ : Submodule S M) ≠ ⊤ := by
      intro htop
      have hle : I • (⊤ : Submodule S M) ≤ IsLocalRing.maximalIdeal S • ⊤ :=
        Submodule.smul_mono_left hImax
      rw [htop] at hle
      exact Module.maximalIdeal_smul_top_ne_top M (top_le_iff.mp hle)
    have hsub : Subsingleton (Ext N M c) :=
      ModuleCat.subsingleton_ext_of_lt_ideal_depth I M N hIM (k := 1) (by simpa using hN)
        (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self c) hc)
    let e := extQuotSMulTopLinearEquiv hreg (hN hxI) c hsub
    rw [← moduleSupportDim_eq_of_linearEquiv e, ← moduleDepth_eq_of_linearEquiv e]
    exact ih M' hM' hc'

end Dualizing

end
