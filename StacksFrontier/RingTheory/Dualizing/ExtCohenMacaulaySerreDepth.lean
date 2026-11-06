module

public import StacksFrontier.RingTheory.Dualizing.ExtCohenMacaulaySerre
import all StacksFrontier.RingTheory.Dualizing.ExtCohenMacaulaySerre

/-!
# Depth of Ext modules in low degrees

Declarations built on `StacksFrontier.RingTheory.Dualizing.ExtCohenMacaulaySerre`.

## Main results

* `withBot_add_le_of_add_succ_le`
* `le_depth_linearMap_of_le_two`
* `min_two_supportDim_le_moduleDepth_ext_of_le_depth`
-/

@[expose] public section

open CategoryTheory Abelian

universe u

namespace CategoryTheory.Abelian.Ext

variable {S : Type u} [CommRing S]

end CategoryTheory.Abelian.Ext

namespace Dualizing

variable {S : Type u} [CommRing S]

/-- Cancellation of `+ 1` in an inequality in `WithBot ℕ∞`. -/
private theorem withBot_add_le_of_add_succ_le {a b : WithBot ℕ∞} {c : ℕ}
    (h : a + ((c + 1 : ℕ) : WithBot ℕ∞) ≤ b + 1) : a + c ≤ b := by
  induction a with
  | bot => simp
  | coe a =>
    induction b with
    | bot =>
      rw [WithBot.bot_add] at h
      exact absurd (le_bot_iff.mp h) (by
        rw [← WithBot.coe_natCast, ← WithBot.coe_add]
        exact WithBot.coe_ne_bot)
    | coe b =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add,
        WithBot.coe_le_coe, Nat.cast_succ, ← add_assoc] at h
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe]
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h

/-- A bound `k ≤ 2` on the depth of `M` passes to `Hom_S(N, M)`
([Stacks, Tag 0AV6] in its local form). -/
private theorem le_depth_linearMap_of_le_two [IsNoetherianRing S] [IsLocalRing S]
    {M N : Type u} [AddCommGroup M] [Module S M] [Module.Finite S M] [AddCommGroup N]
    [Module S N] [Module.Finite S N] (k : ℕ∞) (hk : k ≤ 2)
    (hM : k ≤ Module.depth S (IsLocalRing.maximalIdeal S) M) :
    k ≤ Module.depth S (IsLocalRing.maximalIdeal S) (N →ₗ[S] M) := by
  have hk' : k ≠ ⊤ := ne_top_of_le_ne_top (by simp) hk
  lift k to ℕ using hk'
  have hk2 : k ≤ 2 := by exact_mod_cast hk
  interval_cases k
  · exact bot_le
  · exact one_le_depth_and_two_le_depth_linearMap.1 (by exact_mod_cast hM)
  · exact one_le_depth_and_two_le_depth_linearMap.2 (by exact_mod_cast hM)

/-- A module on which `1 : S` acts as zero is a subsingleton. -/
private theorem subsingleton_of_forall_one_smul_eq_zero {X : Type*} [AddCommGroup X] [Module S X]
    (h : ∀ x : X, (1 : S) • x = 0) : Subsingleton X :=
  ⟨fun a b => by rw [← one_smul S a, ← one_smul S b, h a, h b]⟩

/-- **The depth of `Ext^c_S(N, M)` at the grade.**  Let `S` be a Noetherian local ring, `I ⊆ S`
an ideal, `N` a finite `S`-module killed by `I` and `M` a finite Cohen–Macaulay `S`-module. If
`c ≤ depth_I(M)` and `dim Supp N + c ≤ dim Supp M`, then a nonzero `Ext^c_S(N, M)` has

`min(2, dim Supp N) ≤ depth Ext^c_S(N, M)` . -/
theorem min_two_supportDim_le_moduleDepth_ext_of_le_depth [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal S) (N : ModuleCat.{u} S) [Module.Finite S N]
    (hN : I ≤ Module.annihilator S N) (c : ℕ) :
    ∀ (M : ModuleCat.{u} S) [Module.Finite S M], Module.IsCohenMacaulayAtMaximalIdeal S M →
      (c : ℕ∞) ≤ Module.depth S I M →
      Module.supportDim S N + c ≤ Module.supportDim S M → Nontrivial (Ext N M c) →
      min (2 : ℕ∞) ((Module.supportDim S N).unbotD 0) ≤ moduleDepth S (Ext N M c) := by
  induction c with
  | zero =>
    intro M _ hM _ hdim hnt
    let e : Ext N M 0 ≃ₗ[S] (N →ₗ[S] M) := Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv
    have : Nontrivial (N →ₗ[S] M) := e.symm.toEquiv.nontrivial
    rw [moduleDepth_eq_of_linearEquiv e, moduleDepth_eq_depth]
    refine le_depth_linearMap_of_le_two _ (min_le_left _ _) ?_
    rcases subsingleton_or_nontrivial N with hsN | hnN
    · rw [Module.supportDim_eq_bot_of_subsingleton]
      simp
    · have hne := Module.supportDim_ne_bot_of_nontrivial (R := S) (M := N)
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
      rw [← hd, WithBot.unbotD_coe]
      refine (min_le_right _ _).trans ?_
      unfold Module.IsCohenMacaulayAtMaximalIdeal at hM
      have h := hdim
      rw [← hd, ← hM, Nat.cast_zero, add_zero] at h
      exact_mod_cast h
  | succ c ih =>
    intro M _ hM hc hdim hnt
    by_cases hI : I = ⊤
    · have h1 : (1 : S) ∈ Module.annihilator S N := hN (hI ▸ Submodule.mem_top)
      exact absurd hnt (not_nontrivial_iff_subsingleton.mpr
        (subsingleton_of_forall_one_smul_eq_zero (S := S)
          (Ext.smul_eq_zero_of_mem_annihilator h1)))
    rcases subsingleton_or_nontrivial M with hsub | hntM
    · refine absurd hnt (not_nontrivial_iff_subsingleton.mpr
        (subsingleton_of_forall_one_smul_eq_zero (S := S) fun e => ?_))
      rw [Ext.smul_eq_comp_mk₀]
      have : (1 : S) • 𝟙 M = 0 := by
        ext m
        exact Subsingleton.elim _ _
      rw [this, Ext.mk₀_zero, Ext.comp_zero]
    have hImax : I ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hI
    have hdepth0 : Module.depth S I M ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact absurd hc (by simp)
    obtain ⟨x, hxI, hreg⟩ := Module.exists_mem_isSMulRegular_of_depth_ne_zero I hdepth0
    have hxm : x ∈ IsLocalRing.maximalIdeal S := hImax hxI
    have hxN : x ∈ Module.annihilator S N := hN hxI
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
    have hdim' : Module.supportDim S N + c ≤ Module.supportDim S M' := by
      show _ ≤ Module.supportDim S (QuotSMulTop x M)
      rw [← hsd] at hdim
      exact withBot_add_le_of_add_succ_le hdim
    have hIM : I • (⊤ : Submodule S M) ≠ ⊤ := by
      intro htop
      have hle : I • (⊤ : Submodule S M) ≤ IsLocalRing.maximalIdeal S • ⊤ :=
        Submodule.smul_mono_left hImax
      rw [htop] at hle
      exact Module.maximalIdeal_smul_top_ne_top M (top_le_iff.mp hle)
    have hsub : Subsingleton (Ext N M c) :=
      ModuleCat.subsingleton_ext_of_lt_ideal_depth I M N hIM (k := 1) (by simpa using hN)
        (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self c) hc)
    let e := extQuotSMulTopLinearEquiv hreg hxN c hsub
    rw [← moduleDepth_eq_of_linearEquiv e]
    exact ih M' hM' hc' hdim' (e.toEquiv.nontrivial_congr.mpr hnt)

end Dualizing

end
