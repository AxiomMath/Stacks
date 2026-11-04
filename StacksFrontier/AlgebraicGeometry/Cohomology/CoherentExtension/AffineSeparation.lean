module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.MorphismExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Support
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic

/-!
# Separating a morphism from its kernel over one affine open

Let `X` be a locally Noetherian scheme, `M` a coherent `𝒪_X`-module, `K ⊆ M` a quasi-coherent
submodule and `p : M ⟶ F` a morphism to a coherent module which is injective on the sections of
`K` over every open contained in an open `V`. The sections of `K` on which `p` is injective can be
enlarged from `V` to `V ∪ W`, for `W` any *affine* open, by replacing `K` with `ℐ ^ m K` for `ℐ`
the ideal of the closed complement of `V` and `m` large: the ideal is the unit ideal over `V`, so
nothing changes there, and over the affine open `W` a single Artin–Rees constant separates the
kernel of `p` from a high enough ideal power.

One affine open at a time is all that a scheme which is not quasi-compact allows. The Artin–Rees
constant of `AlgebraicGeometry.exists_ideal_pow_smul_inf_eq` is the supremum of the one-chart
constants over a *finite* affine cover, and the exponent annihilating a torsion sheaf is obtained
the same way; both are therefore unavailable globally, and both are available on each affine open.
This module is the resulting one-chart statement, which is what a Zorn argument over the opens
`V ⊆ X` consumes.

## Main results

* `AlgebraicGeometry.basicOpen_le_of_mem_closedIdeal` — a section of the structure sheaf lying in
  the ideal of the closed complement of `V` is nonvanishing only inside `V`.
* `AlgebraicGeometry.exists_pow_smul_submodule_obj_eq_bot` — the annihilation step on one affine
  open: a power of that ideal annihilates the sections over an affine open of a quasi-coherent
  submodule which vanishes over `V`.
* `AlgebraicGeometry.exists_submodule_eq_of_injective_sup_affine` — the separation step on one
  affine open, in the form described above.

## Implementation notes

Injectivity of `p` on the sections of a submodule is written out as "a section of the submodule
killed by `p` is zero" rather than as `Function.Injective` of a composite or as `Mono`: the
statement then restricts to a smaller open with no bookkeeping, and the zero sections of the
submodules in play are compared directly.

The annihilation step is proved from the localization property of a quasi-coherent module rather
than from `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`, which needs the
scheme to be quasi-compact. A section `a` of the ideal of the closed complement of `V` is
nonvanishing only inside `V`, where the submodule has no sections at all, so the localization of
its sections away from `a` vanishes and every section is killed by a power of `a`; the module of
sections over an affine open is finite, so one power kills all of them, and that says `a` is in
the radical of the annihilator.

## References

* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 0FD0](https://stacks.math.columbia.edu/tag/0FD0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerSmul (closedIdeal)

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A section of the structure sheaf over an affine open which lies in the ideal of the closed
complement of `V` is nonvanishing only inside `V`: the closed set it cuts out contains that
complement. -/
theorem basicOpen_le_of_mem_closedIdeal (V : X.Opens) (W : X.affineOpens) (a : Γ(X, W.1))
    (ha : a ∈ (closedIdeal ⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩).ideal W) :
    X.basicOpen a ≤ V := by
  intro x hx
  by_contra hxV
  have hxW : x ∈ W.1 := X.basicOpen_le a hx
  have hxsupp : x ∈ (closedIdeal ⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩).support :=
    (Scheme.IdealSheafData.coe_support_vanishingIdeal
      (⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩ : Closeds X)).ge hxV
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxW, Scheme.mem_zeroLocus_iff] at hxsupp
  exact hxsupp a ha hx

/-- **The annihilation step on one affine open.** Let `N` be a quasi-coherent submodule of a
coherent module on a locally Noetherian scheme, with no sections over any open contained in `V`.
Then a power of the ideal of the closed complement of `V` annihilates the sections of `N` over any
affine open.

A section `a` of that ideal is nonvanishing only inside `V`, so `N` has no sections over the basic
open of `a`; those sections are the localization of the sections over the affine open away from
`a`, so every section is killed by a power of `a`, and finiteness of the module of sections turns
the pointwise powers into one. That says `a` lies in the radical of the annihilator, and the
annihilator contains a power of a finitely generated ideal lying in its radical. -/
theorem exists_pow_smul_submodule_obj_eq_bot [IsLocallyNoetherian X] (M : X.Modules)
    [M.IsCoherent] (N : M.Submodule) (hN : N.toSheafOfModules.IsQuasicoherent) (V : X.Opens)
    (hvan : ∀ W₀ : X.Opens, W₀ ≤ V → N.toSubmodule.obj (op W₀) = ⊥) (W : X.affineOpens) :
    ∃ k : ℕ, (closedIdeal ⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩).ideal W ^ k •
      (show Submodule Γ(X, W.1) Γ(M, W.1) from N.toSubmodule.obj (op W.1)) = ⊥ := by
  classical
  have hNqc : (N.toSheafOfModules : X.Modules).IsQuasicoherent := hN
  have hring : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  have hMfin : Module.Finite Γ(X, W.1) Γ(M, W.1) := moduleFinite_sections M W
  have hMnoeth : _root_.IsNoetherian Γ(X, W.1) Γ(M, W.1) := inferInstance
  set NW : Submodule Γ(X, W.1) Γ(M, W.1) := N.toSubmodule.obj (op W.1) with hNW
  have hrad : (closedIdeal ⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩).ideal W ≤
      NW.annihilator.radical := by
    intro a ha
    have hbasic : X.basicOpen a ≤ V := basicOpen_le_of_mem_closedIdeal V W a ha
    have hle : X.basicOpen a ≤ W.1 := X.basicOpen_le a
    have hbot : N.toSubmodule.obj (op (X.basicOpen a)) = ⊥ := hvan _ hbasic
    let _hmod := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE
      (N.toSheafOfModules : X.Modules) hle
    have hloc : IsLocalizedModule.Away a
        (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ
          (N.toSheafOfModules : X.Modules) hle) :=
      Stacks.AlgebraicGeometry.QcohPushforwardOpen.isLocalizedModule_restrictₗ_of_eq
        (N.toSheafOfModules : X.Modules) W.2.isCompact W.2.isQuasiSeparated a rfl hle
    -- every section over `W` is killed by a power of `a`
    have htor : ∀ s ∈ NW, ∃ j : ℕ, a ^ j • s = 0 := by
      intro s hs
      have hres : (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ
          (N.toSheafOfModules : X.Modules) hle)
            (⟨s, hs⟩ : Γ((N.toSheafOfModules : X.Modules), W.1)) = 0 :=
        Subtype.ext ((_root_.Submodule.mem_bot _).1
          (hbot.le (N.toSubmodule.map_mem (CategoryTheory.homOfLE hle).op hs)))
      obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) _).1 hres
      obtain ⟨j, hj⟩ := t.2
      refine ⟨j, ?_⟩
      rw [show a ^ j = (t : Γ(X, W.1)) from hj]
      exact congrArg Subtype.val ht
    obtain ⟨g, hg⟩ : NW.FG := IsNoetherian.noetherian _
    choose! jj hjj using htor
    refine Ideal.mem_radical_iff.2 ⟨g.sup fun y => jj y, ?_⟩
    rw [_root_.Submodule.mem_annihilator]
    intro m hm
    rw [← hg] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
        have hxmem : x ∈ NW := hg.le (Submodule.subset_span hx)
        rw [show a ^ (g.sup fun y => jj y) = a ^ ((g.sup fun y => jj y) - jj x) * a ^ jj x by
          rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := fun y => jj y) hx)],
          mul_smul, hjj x hxmem, smul_zero]
    | zero => rw [smul_zero]
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_comm, hx, smul_zero]
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨k, _root_.Submodule.le_annihilator_iff.1 hk⟩


/-- **The separation step on one affine open.** Let `X` be locally Noetherian, `M` a coherent
module, `K` a quasi-coherent submodule of `M` and `p : M ⟶ F` a morphism to a coherent module
which kills no nonzero section of `K` over an open contained in `V`. Then for every affine open
`W` there is a quasi-coherent submodule `B ≤ K` which agrees with `K` over `V` and which `p` kills
no nonzero section of over an open contained in `V ⊔ W`.

`B` is `ℐ ^ m K` for `ℐ` the ideal of the closed complement of `V`, read inside `M`. Over `V` the
ideal is the unit ideal, so `B` is `K` there; over the affine open `W` the sections of the kernel
of `p` on `K` are annihilated by a power of `ℐ`, and Artin–Rees on that one chart separates them
from a high enough ideal power. Vanishing of the intersection then spreads from `W` to all of its
opens because the intersection is quasi-coherent, and the two halves of `V ⊔ W` are glued by the
locality of vanishing. -/
theorem exists_submodule_eq_of_injective_sup_affine [IsLocallyNoetherian X] (M F : X.Modules)
    [M.IsCoherent] [F.IsCoherent] (p : M ⟶ F) (K : M.Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherent) (V : X.Opens)
    (hinj : ∀ W₀ : X.Opens, W₀ ≤ V → ∀ s ∈ K.toSubmodule.obj (op W₀),
      (p.val.app (op W₀)) s = 0 → s = 0)
    (W : X.affineOpens) :
    ∃ B : M.Submodule, B.toSheafOfModules.IsQuasicoherent ∧ B ≤ K ∧
      (∀ W₀ : X.Opens, W₀ ≤ V → B.toSubmodule.obj (op W₀) = K.toSubmodule.obj (op W₀)) ∧
      ∀ W₀ : X.Opens, W₀ ≤ V ⊔ W.1 → ∀ s ∈ B.toSubmodule.obj (op W₀),
        (p.val.app (op W₀)) s = 0 → s = 0 := by
  classical
  have hKqc : (K.toSheafOfModules : X.Modules).IsQuasicoherent := hK
  have hMqc : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hKcoh : (K.toSheafOfModules : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule M K hK
  set ℐ : X.IdealSheafData := closedIdeal ⟨(V : Set X)ᶜ, isClosed_compl_iff.mpr V.2⟩ with hℐ
  set ψ : (K.toSheafOfModules : X.Modules) ⟶ F := K.ι ≫ p with hψ
  set n : (K.toSheafOfModules : X.Modules).Submodule :=
    Stacks.Algebraization.kernelSubmodule ψ with hn
  -- the kernel of `p` on `K` has no sections over an open contained in `V`
  have hnvan : ∀ W₀ : X.Opens, W₀ ≤ V → n.toSubmodule.obj (op W₀) = ⊥ := by
    intro W₀ hW₀
    refine le_antisymm (fun a ha => ?_) bot_le
    have h1 : (p.val.app (op W₀)) a.1 = 0 := (mem_kernelSubmodule_iff ψ W₀ a).1 ha
    exact (_root_.Submodule.mem_bot _).2 (Subtype.ext (hinj W₀ hW₀ a.1 a.2 h1))
  have hnqc : (n.toSheafOfModules : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Stacks.Algebraization.kernelSubmoduleIso ψ).symm
      (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _)
  -- the annihilation step and Artin-Rees, both on the single affine open `W`
  obtain ⟨k, hk⟩ := exists_pow_smul_submodule_obj_eq_bot (K.toSheafOfModules : X.Modules) n
    hnqc V hnvan W
  have hIqc : (Stacks.Algebraization.kernelSubmodule
      (SheafOfModules.unitToPushforwardObjUnit
        ℐ.subschemeι.toRingCatSheafHom)).toSheafOfModules.IsQuasicoherent :=
    Stacks.Algebraization.idealKernel_isQuasicoherent _
  obtain ⟨c, hc⟩ := exists_local_shift (K.toSheafOfModules : X.Modules) n
    (Stacks.Algebraization.kernelSubmodule
      (SheafOfModules.unitToPushforwardObjUnit ℐ.subschemeι.toRingCatSheafHom)) W
  -- a high enough ideal power meets the kernel in zero over `W`
  have hsep : (Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul ℐ (k + c)
      (K.toSheafOfModules : X.Modules) ⊓ n).toSubmodule.obj (op W.1) = ⊥ := by
    rw [submodule_inf_obj,
      Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul ℐ (k + c)
        (K.toSheafOfModules : X.Modules) W]
    have hcW := hc (k + c) (Nat.le_add_left c k)
    rw [Stacks.Algebraization.kernelSubmodule_obj_affine ℐ W, Nat.add_sub_cancel] at hcW
    exact le_antisymm (hcW.le.trans
      ((smul_mono_right _ inf_le_right).trans (le_of_eq hk))) bot_le
  -- so it meets the kernel in zero over every open contained in `W`
  have hseple : ∀ W₀ : X.Opens, W₀ ≤ W.1 →
      (Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul ℐ (k + c)
        (K.toSheafOfModules : X.Modules) ⊓ n).toSubmodule.obj (op W₀) = ⊥ := by
    intro W₀ hW₀
    exact submodule_obj_eq_bot_of_le_affine _
      (isQuasicoherent_inf_kernelSubmodule _
        (Stacks.AlgebraicGeometry.IdealPowerSmul.isQuasicoherent_idealPowSmul ℐ (k + c) _) ψ)
      W.2 hsep hW₀
  -- the ideal power, read inside `M`
  set P : (K.toSheafOfModules : X.Modules).Submodule :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul ℐ (k + c)
      (K.toSheafOfModules : X.Modules) with hP
  set q : ((P.toSheafOfModules : X.Modules)) ⟶ M := P.ι ≫ K.ι with hq
  have hqmono : Mono q := by rw [hq]; infer_instance
  have hPqc : (P.toSheafOfModules : X.Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.isQuasicoherent_idealPowSmul ℐ (k + c) _
  have hBK : imageSubmodule q ≤ K := by
    intro W₀ s hs
    obtain ⟨W₀, rfl⟩ : ∃ W₁ : X.Opens, op W₁ = W₀ := ⟨W₀.unop, rfl⟩
    rw [imageSubmodule_obj q hqmono W₀] at hs
    obtain ⟨t, rfl⟩ := hs
    exact (P.ι.val.app (op W₀) t).2
  refine ⟨imageSubmodule q, isQuasicoherent_imageSubmodule q, hBK, ?_, ?_⟩
  · -- `B` agrees with `K` over `V`
    intro W₀ hW₀
    have htop : P.toSubmodule.obj (op W₀) = ⊤ :=
      idealPowSmul_obj_eq_top ℐ (k + c) (K.toSheafOfModules : X.Modules) V
        (closedIdeal_compl_ideal_eq_top V) W₀ hW₀
    refine le_antisymm (hBK _) fun s hs => ?_
    rw [imageSubmodule_obj q hqmono W₀]
    exact ⟨⟨⟨s, hs⟩, htop.ge _root_.Submodule.mem_top⟩, rfl⟩
  · -- `p` kills no nonzero section of `B` over an open contained in `V ⊔ W`
    intro W₀ hW₀ s hs hps
    have hker : ∀ (W₁ : X.Opens) (hW₁ : W₁ ≤ W₀), W₁ ≤ V ∨ W₁ ≤ W.1 →
        (M.val.map (CategoryTheory.homOfLE hW₁).op s : Γ(M, W₁)) = 0 := by
      intro W₁ hW₁ hcase
      have hsres : (M.val.map (CategoryTheory.homOfLE hW₁).op s : Γ(M, W₁)) ∈
          (imageSubmodule q).toSubmodule.obj (op W₁) :=
        val_map_mem_submodule (imageSubmodule q) (CategoryTheory.homOfLE hW₁).op hs
      have hpres : (p.val.app (op W₁)) (M.val.map (CategoryTheory.homOfLE hW₁).op s) = 0 := by
        rw [PresheafOfModules.naturality_apply p.val (CategoryTheory.homOfLE hW₁).op s, hps]
        exact map_zero _
      rw [imageSubmodule_obj q hqmono W₁] at hsres
      obtain ⟨a, ha⟩ := hsres
      have hpa : (p.val.app (op W₁)) (q.val.app (op W₁) a) = 0 := by rw [ha]; exact hpres
      rw [← ha]
      rcases hcase with hV | hWW
      · exact hinj W₁ hV a.1.1 a.1.2 hpa
      · have ha1 : a.1 = 0 := by
          have hamem : a.1 ∈ (P ⊓ n).toSubmodule.obj (op W₁) :=
            ⟨a.2, (mem_kernelSubmodule_iff ψ W₁ a.1).2 hpa⟩
          rw [hseple W₁ hWW] at hamem
          exact (_root_.Submodule.mem_bot _).1 hamem
        exact congrArg Subtype.val ha1
    have hmem : s ∈ (Stacks.Algebraization.kernelSubmodule (𝟙 M)).toSubmodule.obj (op W₀) := by
      refine mem_submodule_of_locally_mem _ W₀ s fun x hx => ?_
      obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, (U ≤ V ∨ U ≤ W.1) ∧ x ∈ U :=
        (TopologicalSpace.Opens.mem_sup.1 (hW₀ hx)).elim (fun h => ⟨V, .inl le_rfl, h⟩)
          fun h => ⟨W.1, .inr le_rfl, h⟩
      exact ⟨W₀ ⊓ U, inf_le_left, ⟨hx, hxU⟩,
        (kernelSubmodule_id_obj M (op (W₀ ⊓ U))).ge ((_root_.Submodule.mem_bot _).2
          (hker (W₀ ⊓ U) inf_le_left (hU.imp (inf_le_right.trans ·) (inf_le_right.trans ·))))⟩
    exact (_root_.Submodule.mem_bot _).1
      ((kernelSubmodule_id_obj M (op W₀)).le hmem)

end AlgebraicGeometry

end
