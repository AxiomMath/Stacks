module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleHomGlue

/-!
# Krull's intersection theorem for sections of a coherent module

Let `X` be a locally Noetherian scheme, `I` a quasi-coherent sheaf of ideals on `X` and `F` a
coherent `𝒪_X`-module. A section `s` of `F` over an open `W` lies in the subsheaf `I ^ n F` for
every `n` exactly when it vanishes on an open neighbourhood of `V(I) ∩ W` inside `W`.

This is Krull's intersection theorem read on an affine open `U`: there the sections of `I ^ n F`
are `I(U) ^ n • Γ(F, U)`, the ring `Γ(X, U)` is Noetherian and `Γ(F, U)` is a finite module, so a
section in every `I(U) ^ n • Γ(F, U)` is fixed by some `r ∈ I(U)`, hence killed by `1 - r`, hence
zero on the basic open `D(1 - r)`, which contains `V(I) ∩ U`. Conversely, off `V(I)` the ideal
is the unit ideal, so `I ^ n F` agrees with `F` there, and membership in a subsheaf is local.

## Main results

* `AlgebraicGeometry.forall_mem_idealPowerMultiple_iff_exists_restrict_eq_zero`: a section of
  a coherent module over `W` lies in every `I ^ n F` iff it vanishes on an open neighbourhood of
  `V(I) ∩ W` in `W`.
* `AlgebraicGeometry.forall_mem_idealPowerMultiple_top_iff`: the case of global sections.

## References

* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
* [Stacks Project, Tag 00IR](https://stacks.math.columbia.edu/tag/00IR)
* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
-/

public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.SubmoduleHomGlue (presheaf_map_map)

universe u

namespace AlgebraicGeometry

/-- **Krull's intersection theorem, sheafified.** On a locally Noetherian scheme, a section `s`
of a coherent module `F` over an open `W` lies in the subsheaf `I ^ n F` for every `n` if and
only if it vanishes on some open `V ⊆ W` containing `V(I) ∩ W`. -/
theorem forall_mem_idealPowerMultiple_iff_exists_restrict_eq_zero
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsCoherent] (W : X.Opens) (s : Γ(F, W)) :
    (∀ n : ℕ, s ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n F).toSubmodule.obj
        (Opposite.op W)) ↔
      ∃ (V : X.Opens) (hVW : V ≤ W), (I.support : Set X) ∩ W ⊆ V ∧
        F.presheaf.map (homOfLE hVW).op s = 0 := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  constructor
  · intro hs
    have key : ∀ z ∈ (I.support : Set X) ∩ W, ∃ (O : X.Opens) (hO : O ≤ W), z ∈ O ∧
        F.presheaf.map (homOfLE hO).op s = 0 := by
      rintro z ⟨hzI, hzW⟩
      obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hzW W.2
      replace hUW : U ≤ W := hUW
      let U' : X.affineOpens := ⟨U, hU⟩
      have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
      have : Module.Finite Γ(X, U) Γ(F, U) :=
        Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hU
      set t := F.presheaf.map (homOfLE hUW).op s with ht_def
      have ht : t ∈ (⨅ i : ℕ, I.ideal U' ^ i • ⊤ : Submodule Γ(X, U) Γ(F, U)) :=
        Submodule.mem_iInf _ |>.2 fun n =>
          (Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine I n F U').le
            ((Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n F).map_mem
              (homOfLE hUW).op (hs n))
      obtain ⟨⟨r, hrI⟩, hr⟩ := (I.ideal U').mem_iInf_smul_pow_eq_bot_iff t |>.1 ht
      refine ⟨X.basicOpen (1 - r), (X.basicOpen_le _).trans hUW, ?_, ?_⟩
      · have hz : z ∈ X.zeroLocus (U := U) (I.ideal U' : Set Γ(X, U)) :=
          (I.mem_support_iff_of_mem (U := U') hzU).1 hzI
        have hzr : z ∉ X.basicOpen r := (X.mem_zeroLocus_iff _ z).1 hz r hrI
        rw [X.mem_basicOpen _ z hzU] at hzr ⊢
        rw [map_sub, map_one]
        exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left hzr
      · have h0 : (1 - r) • t = 0 := by rw [sub_smul, one_smul, hr, sub_self]
        have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (1 - r))).op (1 - r)) :=
          X.toRingedSpace.isUnit_res_basicOpen (1 - r)
        have hres := F.map_smul (homOfLE (X.basicOpen_le (1 - r))) (1 - r) t
        rw [h0, map_zero] at hres
        rw [← presheaf_map_map hUW (X.basicOpen_le (1 - r)) s, ← ht_def]
        exact hunit.smul_eq_zero.mp hres.symm
    choose O hOW hzO hO0 using key
    let S : Set X := (I.support : Set X) ∩ W
    refine ⟨⨆ z : S, O z.1 z.2, iSup_le fun z => hOW z.1 z.2,
      fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzO z hz⟩, ?_⟩
    refine Stacks.Algebraization.eq_zero_of_locally_eq_zero F _ _ fun x hx => ?_
    obtain ⟨z, hxz⟩ := Opens.mem_iSup.1 hx
    refine ⟨O z.1 z.2, le_iSup (fun z : S => O z.1 z.2) z, hxz, ?_⟩
    rw [presheaf_map_map]
    exact hO0 z.1 z.2
  · rintro ⟨V, hVW, hsupp, hs0⟩ n
    let P := Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n F
    have htop : ∀ (O : X.Opens), O ≤ I.support.compl → ∀ t : Γ(F, O),
        t ∈ P.toSubmodule.obj (op O) := by
      intro O hO t
      refine Stacks.Algebraization.mem_submodule_of_affine P O t fun A i => ?_
      exact (Stacks.Algebraization.idealPowerMultiple_obj_eq_top_of_le_compl_support I n F A
        ((leOfHom i).trans hO)).ge Submodule.mem_top
    apply P.isSheaf
    rw [Opens.mem_grothendieckTopology]
    intro x hxW
    by_cases hx : x ∈ V
    · refine ⟨V, homOfLE hVW, ?_, hx⟩
      show F.presheaf.map (homOfLE hVW).op s ∈ P.toSubmodule.obj (op V)
      rw [hs0]
      exact zero_mem _
    · exact ⟨W ⊓ I.support.compl, homOfLE inf_le_left, htop _ inf_le_right _, hxW,
        fun h => hx (hsupp ⟨h, hxW⟩)⟩

/-- **Krull's intersection theorem for global sections.** On a locally Noetherian scheme, a
global section `s` of a coherent module `F` lies in `I ^ n F` for every `n` if and only if it
vanishes on some open neighbourhood of `V(I)`. -/
theorem forall_mem_idealPowerMultiple_top_iff
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsCoherent] (s : Γ(F, ⊤)) :
    (∀ n : ℕ, s ∈ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n F).toSubmodule.obj
        (Opposite.op ⊤)) ↔
      ∃ V : X.Opens, (I.support : Set X) ⊆ V ∧
        F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s = 0 := by
  rw [forall_mem_idealPowerMultiple_iff_exists_restrict_eq_zero I F ⊤ s]
  simp only [Opens.coe_top, Set.inter_univ]
  exact ⟨fun ⟨V, _, h₁, h₂⟩ => ⟨V, h₁, h₂⟩, fun ⟨V, h₁, h₂⟩ => ⟨V, le_top, h₁, h₂⟩⟩

end AlgebraicGeometry
