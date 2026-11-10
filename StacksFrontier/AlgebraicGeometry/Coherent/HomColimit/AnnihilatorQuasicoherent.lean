module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerBridge
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic
/-!
# Quasi-coherence of the sections annihilated by a power of an ideal sheaf

For a sheaf of ideals `I` of finite type on a scheme `X` and a quasi-coherent `𝒪_X`-module `F`,
the subsheaf of sections annihilated by `Iⁿ` is quasi-coherent.  This is [Stacks, Tag 01PO] (1),
stated there for `I` itself; the proof is the same for every power because `Iⁿ` is again a
quasi-coherent sheaf of ideals of finite type.

Quasi-coherence of a subsheaf cannot be read off a presentation, so the criterion used is
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`:
it suffices that for each affine open `U` and each `a : Γ(X, U)` the sections of the annihilator
over `X.basicOpen a` are the localization away from `a` of its sections over `U`.  Both opens are
affine, so `Stacks.AlgebraicGeometry.IdealPowerColimit.mem_idealPowerAnnihilator_affineOpen`
computes both sides, and the statement becomes the algebraic assertion that the annihilator of a
finitely generated ideal localizes.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.annihilatorModule`: the annihilator subsheaf
  bundled as an object of `X.Modules`, with `annihilatorVal` and `annihilatorMk` naming the two
  directions of the identification of its sections with the annihilated sections of `F`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.isLocalizedModule_annihilatorModule`: **the
  localization statement.** For an affine open `U` on which `I(U)ⁿ` is finitely generated, the
  sections of the annihilator over `X.basicOpen a` are the localization away from `a` of its
  sections over `U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_annihilatorModule_of_fg`: the
  annihilator of `Iⁿ` is quasi-coherent when `I` is of finite type, and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_idealPowerAnnihilator` is the
  instance for a locally Noetherian scheme, where the finite generation is automatic.
* `Stacks.AlgebraicGeometry.IdealPowerColimit`
  `.exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot`: the consequence [Stacks, Tag 01YB]
  draws from this together with Artin-Rees, that `Iᵐ F` meets the `n`-th annihilator in zero for
  `m` large.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_idealAnnihilator` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.mem_idealAnnihilator_affineOpen`: assertions (1)
  and (2) of [Stacks, Tag 01PO], the case `n = 1`.

## Implementation notes

**Finite generation is used once.** Only the third hypothesis of
`IsLocalizedModule.Away.mk_of_addCommGroup` — that every section of the annihilator over
`X.basicOpen a` is, after multiplication by a power of `a`, the restriction of a section of the
annihilator over `U` — needs `I(U)ⁿ` finitely generated.  A section of `F` over `U` restricting
to the given one is annihilated by each generator only after multiplication by some power of `a`,
and finitely many generators admit a common power.  This is the step the source singles out
("and this is where we use that `I` is finitely generated").  The other three hypotheses are
inherited from `F`: in particular the preimage under `a` of an annihilated section is itself
annihilated, because `a` acts injectively on the sections over `X.basicOpen a`.

**The two scalar actions.** The hazard recorded elsewhere in the tree — that `moduleOfLE` and
`restrictₗ` are supplied by `letI`, so that instance search can pick up the wrong module
structure — does not bite here, because the annihilator is a subobject of `F` and every
compatibility needed between the two is definitional: `annihilatorVal` commutes with the scalar
action and with restriction by `rfl`, for the native `Γ(X, W)`-action and for the
`Γ(X, U)`-action obtained from `moduleOfLE` alike.  What is not definitional is the relation
between the `Γ(X, U)`-action on sections over `X.basicOpen a` and the `Γ(X, X.basicOpen a)`-
action: the proof carries the local `hsm` for it, whose statement is the one place where the
restriction map must be written out.

**Reduction to `n = 1`.** `idealPower_unitSubmodule_one` identifies the first power of the ideal
subsheaf attached to `I` with that subsheaf itself, which is what makes the `n = 1` case of the
results above literally the annihilator of `I`, as [Stacks, Tag 01PO] states it.  Assertion (3)
of that tag, the computation of the stalks of the annihilator, is not proved here, so the two
tags placed are clause tags and tag 01PO is not complete.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.GabberColimit
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The annihilator subsheaf as a sheaf of modules -/

/-- The subsheaf of sections annihilated by `Iⁿ`, bundled as an `𝒪_X`-module.

The type `X.Modules` is a definition for `SheafOfModules X.ringCatSheaf` that does not unfold at
instance-reducible transparency, so without this bundling the `Module Γ(X, U) Γ(_, U)` instance
of `AlgebraicGeometry.Scheme.Modules` is not found for the underlying sheaf of modules. -/
noncomputable def annihilatorModule (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) : X.Modules :=
  (idealPowerAnnihilator I.unitSubmodule F n).toSheafOfModules

/-- The underlying section of `F` of a section of the annihilator subsheaf. -/
noncomputable def annihilatorVal {I : X.IdealSheafData} {F : X.Modules} {n : ℕ} {W : X.Opens}
    (z : Γ(annihilatorModule I F n, W)) : Γ(F, W) :=
  z.1

/-- An annihilated section of `F`, viewed as a section of the annihilator subsheaf. -/
noncomputable def annihilatorMk (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) {W : X.Opens}
    (s : Γ(F, W))
    (hs : s ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W)) :
    Γ(annihilatorModule I F n, W) :=
  ⟨s, hs⟩

/-- A section of the annihilator subsheaf is an annihilated section of `F`. -/
theorem annihilatorVal_mem {I : X.IdealSheafData} {F : X.Modules} {n : ℕ} {W : X.Opens}
    (z : Γ(annihilatorModule I F n, W)) :
    annihilatorVal z ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W) :=
  z.2

/-- Sections of the annihilator subsheaf are determined by the underlying sections of `F`. -/
theorem annihilatorVal_inj {I : X.IdealSheafData} {F : X.Modules} {n : ℕ} {W : X.Opens}
    {z₁ z₂ : Γ(annihilatorModule I F n, W)} (h : annihilatorVal z₁ = annihilatorVal z₂) :
    z₁ = z₂ :=
  Subtype.ext h

/-- Equal sections of the annihilator subsheaf have equal underlying sections of `F`. -/
theorem annihilatorVal_eq {I : X.IdealSheafData} {F : X.Modules} {n : ℕ} {W : X.Opens}
    {z₁ z₂ : Γ(annihilatorModule I F n, W)} (h : z₁ = z₂) :
    annihilatorVal z₁ = annihilatorVal z₂ := by
  rw [h]

/-- The underlying section of `annihilatorMk I F n s hs` is `s`. -/
@[simp]
theorem annihilatorVal_annihilatorMk (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) {W : X.Opens}
    (s : Γ(F, W))
    (hs : s ∈ (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op W)) :
    annihilatorVal (annihilatorMk I F n s hs) = s :=
  rfl

/-- `annihilatorVal` commutes with the scalar action of `Γ(X, W)`. -/
@[simp]
theorem annihilatorVal_smul {I : X.IdealSheafData} {F : X.Modules} {n : ℕ} {W : X.Opens}
    (r : Γ(X, W)) (z : Γ(annihilatorModule I F n, W)) :
    annihilatorVal (r • z) = r • annihilatorVal z :=
  rfl

/-! ### Localization on basic opens -/

/-- **The annihilator of a finitely generated ideal localizes.** Let `U` be an affine open of `X`
on which the ideal `I(U)ⁿ` is finitely generated, and let `a : Γ(X, U)`.  Then the sections over
`X.basicOpen a` of the subsheaf of sections annihilated by `Iⁿ` are the localization away from
`a` of its sections over `U`.

Finite generation enters only through the third condition of
`IsLocalizedModule.Away.mk_of_addCommGroup`: a common power of `a` must annihilate all the
generators at once. -/
theorem isLocalizedModule_annihilatorModule (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (hFG : (I.ideal ⟨U, hU⟩ ^ n : Ideal Γ(X, U)).FG) (a : Γ(X, U)) :
    letI := moduleOfLE (annihilatorModule I F n) (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (annihilatorModule I F n) (X.basicOpen_le a)) := by
  let := moduleOfLE (annihilatorModule I F n) (X.basicOpen_le a)
  let := moduleOfLE F (X.basicOpen_le a)
  have hlocF : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨hFinj, hFsurj⟩ :=
    smul_bijective_of_isLocalizedModule (restrictₗ F (X.basicOpen_le a)) a
  have hVaff : IsAffineOpen (X.basicOpen a) := hU.basicOpen a
  -- the `Γ(X, U)`-action on sections over `X.basicOpen a` is restriction followed by the
  -- `Γ(X, X.basicOpen a)`-action
  have hsm : ∀ (r : Γ(X, U)) (x : Γ(F, X.basicOpen a)),
      r • x = X.presheaf.map (homOfLE (X.basicOpen_le a)).op r • x := fun _ _ ↦ rfl
  -- a section over `U` whose restriction vanishes is killed by a power of `a`
  have hann : ∀ y : Γ(F, U), restrictₗ F (X.basicOpen_le a) y = 0 → ∃ k : ℕ, a ^ k • y = 0 :=
    fun y hy ↦ by
      obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq a (y := (0 : Γ(F, U)))
        (by rw [hy, map_zero])
      exact ⟨k, by rwa [smul_zero] at hk⟩
  have hmemV : ∀ z : Γ(annihilatorModule I F n, X.basicOpen a),
      ∀ b ∈ (I.ideal ⟨X.basicOpen a, hVaff⟩ ^ n : Ideal Γ(X, X.basicOpen a)),
        b • annihilatorVal z = (0 : Γ(F, X.basicOpen a)) := fun z ↦
    (mem_idealPowerAnnihilator_affineOpen I F n ⟨X.basicOpen a, hVaff⟩ (annihilatorVal z)).mp
      (annihilatorVal_mem z)
  refine IsLocalizedModule.Away.mk_of_addCommGroup (isUnit_algebraMap_end ?_ ?_) ?_ ?_
  · exact fun z₁ z₂ hz ↦
      annihilatorVal_inj (hFinj _ _ (annihilatorVal_eq hz))
  · -- the preimage under `a` of an annihilated section is annihilated, since `a` acts injectively
    intro z
    obtain ⟨w, hw⟩ := hFsurj (annihilatorVal z)
    have hwmem : ∀ b ∈ (I.ideal ⟨X.basicOpen a, hVaff⟩ ^ n : Ideal Γ(X, X.basicOpen a)),
        b • w = (0 : Γ(F, X.basicOpen a)) := by
      intro b hb
      refine hFinj (b • w) 0 ?_
      rw [smul_zero, hsm a (b • w), smul_comm, ← hsm a w, hw]
      exact hmemV z b hb
    exact ⟨annihilatorMk I F n w
      ((mem_idealPowerAnnihilator_affineOpen I F n ⟨X.basicOpen a, hVaff⟩ w).mpr hwmem),
      annihilatorVal_inj hw⟩
  · -- a common power of `a` annihilates the finitely many generators of `I(U)ⁿ`
    intro z
    obtain ⟨k, x₀, hx₀⟩ :=
      IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le a)) a (annihilatorVal z)
    obtain ⟨G, hG⟩ := hFG
    have hkill : ∀ g : Γ(X, U), ∃ m : ℕ, g ∈ G → a ^ m • (g • x₀) = (0 : Γ(F, U)) := by
      intro g
      by_cases hg : g ∈ G
      · have hg' : g ∈ (I.ideal ⟨U, hU⟩ ^ n : Ideal Γ(X, U)) := by
          rw [← hG]; exact Submodule.subset_span hg
        obtain ⟨m, hm⟩ := hann (g • x₀) (by
          rw [map_smul, ← hx₀, smul_comm, hsm g,
            hmemV z _ (res_mem_idealPow I n (U := ⟨U, hU⟩) (W := ⟨X.basicOpen a, hVaff⟩)
              (X.basicOpen_le a) hg'), smul_zero])
        exact ⟨m, fun _ ↦ hm⟩
      · exact ⟨0, fun h ↦ absurd h hg⟩
    choose mfun hmfun using hkill
    set M := G.sup mfun with hM
    have hkey : ∀ g ∈ G, a ^ M • (g • x₀) = (0 : Γ(F, U)) := by
      intro g hg
      rw [show a ^ M = a ^ (M - mfun g) * a ^ mfun g by
        rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup hg)], mul_smul, hmfun g hg, smul_zero]
    have hmem : ∀ b ∈ (I.ideal ⟨U, hU⟩ ^ n : Ideal Γ(X, U)),
        b • (a ^ M • x₀) = (0 : Γ(F, U)) := by
      intro b hb
      rw [← hG] at hb
      induction hb using Submodule.span_induction with
      | mem c hc => rw [smul_smul, mul_comm, ← smul_smul]; exact hkey c hc
      | zero => rw [zero_smul]
      | add p q _ _ hp hq => rw [add_smul, hp, hq, add_zero]
      | smul r p _ hp => rw [smul_eq_mul, mul_smul, hp, smul_zero]
    refine ⟨M + k, annihilatorMk I F n (a ^ M • x₀)
      ((mem_idealPowerAnnihilator_affineOpen I F n ⟨U, hU⟩ _).mpr hmem), annihilatorVal_inj ?_⟩
    change a ^ (M + k) • annihilatorVal z = restrictₗ F (X.basicOpen_le a) (a ^ M • x₀)
    rw [map_smul, ← hx₀, smul_smul, ← pow_add]
  · -- injectivity up to powers of `a`, inherited from `F`
    intro y hy
    obtain ⟨k, hk⟩ := hann (annihilatorVal y) (annihilatorVal_eq hy)
    exact ⟨k, annihilatorVal_inj hk⟩

/-! ### Quasi-coherence -/

/-- **The sections annihilated by `Iⁿ` form a quasi-coherent subsheaf** when the sheaf of ideals
`I` is of finite type.

This is [Stacks, Tag 01PO] (1) for the ideal sheaf `Iⁿ`; the tag is placed on the case `n = 1`
below, where the ideal is `I` itself, as the source states it. -/
theorem isQuasicoherent_annihilatorModule_of_fg (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hFG : ∀ U : X.affineOpens, (I.ideal U).FG) :
    (idealPowerAnnihilator I.unitSubmodule F n).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (annihilatorModule I F n)
    fun U hU a ↦ isLocalizedModule_annihilatorModule I F n hU (hFG ⟨U, hU⟩).pow a

/-- On a locally Noetherian scheme the sections annihilated by `Iⁿ` form a quasi-coherent
subsheaf, every ideal of a Noetherian ring being finitely generated.

This is the hypothesis in the form the ascending-chain argument of [Stacks, Tag 01Y8] needs it,
the chain being `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowerAnnihilator_monotone`. -/
instance isQuasicoherent_idealPowerAnnihilator [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (idealPowerAnnihilator I.unitSubmodule F n).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_annihilatorModule_of_fg I F n fun U ↦
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    IsNoetherian.noetherian _

/-! ### Artin-Rees against the annihilator -/

/-- **A high power of `I` meets the `n`-th annihilator in zero.** For a coherent sheaf `F` on a
Noetherian scheme there is an `m ≥ n` such that, on every affine open, the submodule
`I(U)ᵐ • Γ(F, U)` meets the sections annihilated by `I(U)ⁿ` only in `0`.

This is the step of [Stacks, Tag 01YB] that makes the subsheaf `F' = Iᵐ F` have vanishing
annihilators: Artin-Rees supplies a `c` with `Iᵐ F ∩ F_n = I^(m-c)(I^c F ∩ F_n)`, and taking
`m = n + c` the right-hand side lies in `Iⁿ • F_n`, which is zero.

The quasi-coherence of `F_n` required by Artin-Rees is
`isQuasicoherent_idealPowerAnnihilator`, so this result is a consequence of the localization
statement above. -/
theorem exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot [IsNoetherian X] (F : X.Modules)
    [F.IsCoherent] (I : X.IdealSheafData) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ ∀ U : X.affineOpens,
      (I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op U.1) = ⊥ := by
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨c, hc⟩ :=
    exists_ideal_pow_smul_inf_eq_ideal F (idealPowerAnnihilator I.unitSubmodule F n) I
  refine ⟨n + c, Nat.le_add_right n c, fun U ↦ ?_⟩
  rw [← hc (n + c) (Nat.le_add_left c n) U, Nat.add_sub_cancel]
  refine le_antisymm (Submodule.smul_le.mpr fun a ha s hs ↦ ?_) bot_le
  have hmem : a • s ∈ (I.ideal U ^ n : Ideal Γ(X, U.1)) •
      (show Submodule Γ(X, U.1) Γ(F, U.1) from
        (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op U.1)) :=
    Submodule.smul_mem_smul ha hs.2
  rwa [idealPow_smul_idealPowerAnnihilator_affineOpen I F n U] at hmem

/-! ### The case `n = 1`: the subsheaf of sections annihilated by `I` -/

/-- The first power of the ideal subsheaf attached to ideal-sheaf data is that subsheaf itself,
so that the case `n = 1` of the results above concerns the sections annihilated by `I`.

This is `idealPower_unitSubmodule` at `n = 1`, since `I.unitSubmodule` is by definition
`I ^ 1 • 𝒪_X`. -/
theorem idealPower_unitSubmodule_one (I : X.IdealSheafData) :
    AlgebraicGeometry.idealPower I.unitSubmodule 1 = I.unitSubmodule :=
  (idealPower_unitSubmodule I 1).trans (idealPowerMultiple_one_eq_unitSubmodule I)

/-- **[Stacks, Tag 01PO] (1).** For a quasi-coherent sheaf of ideals `I` of finite type on a
scheme and a quasi-coherent `𝒪_X`-module `F`, the subsheaf of sections annihilated by `I` is
quasi-coherent.

Assertion (2) of the tag is `mem_idealAnnihilator_affineOpen` below.  Assertion (3), the
description of the stalks, is not proved, so this is a clause tag. -/
@[stacks 01PO "(1)"]
theorem isQuasicoherent_idealAnnihilator (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (hFG : ∀ U : X.affineOpens, (I.ideal U).FG) :
    (idealPowerAnnihilator I.unitSubmodule F 1).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_annihilatorModule_of_fg I F 1 hFG

/-- **[Stacks, Tag 01PO] (2).** On an affine open `U` the subsheaf of sections annihilated by `I`
consists of the sections of `F` over `U` annihilated by `I(U)`.

No finiteness hypothesis is needed for this half: it is
`mem_idealPowerAnnihilator_affineOpen` at `n = 1`, and `idealPower_unitSubmodule_one` identifies
the ideal sheaf being annihilated with `I` rather than its first power. -/
@[stacks 01PO "(2)"]
theorem mem_idealAnnihilator_affineOpen (I : X.IdealSheafData) (F : X.Modules)
    (V : X.affineOpens) (s : Γ(F, V.1)) :
    s ∈ (idealPowerAnnihilator I.unitSubmodule F 1).toSubmodule.obj (op V.1) ↔
      ∀ a ∈ (I.ideal V : Ideal Γ(X, V.1)), a • s = 0 := by
  refine (mem_idealPowerAnnihilator_affineOpen I F 1 V s).trans ?_
  rw [pow_one]

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
