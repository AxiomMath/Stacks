module

public import StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic

/-!
# Quasi-coherence of the subsheaf of sections annihilated by an ideal sheaf

Let `X` be a scheme, `I` a quasi-coherent ideal subsheaf of `𝒪_X` of finite type and `F` a
quasi-coherent `𝒪_X`-module. This file proves that the subsheaf `N` of `F` of sections
annihilated by `I` is quasi-coherent, which is part (1) of [Stacks, Tag 01PO].

## Main results

* `mem_of_smul_mem_of_le_basicOpen`: dividing a section of `N` by a function invertible on the
  domain leaves the quotient in `N`.
* `isLocalizedModule_restrictₗ_of_isAnnihilatorSubsheaf`: the sections of `N` over a basic open
  `X.basicOpen a` of an affine open `U` are the localization away from `a` of its sections over
  `U`.
* `IsAnnihilatorSubsheaf.isQuasicoherent`: **part (1) of [Stacks, Tag 01PO]**.
* `isQuasicoherent_annihilatorSubmodule`: the same for the explicit ideal transporter.

## Implementation notes

Quasi-coherence of a subsheaf cannot be read off a presentation, so it is checked through the
localization criterion
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
exactly as the quasi-coherence of the torsion subsheaf is. The three conditions of
`IsLocalizedModule.Away.mk_of_addCommGroup` are discharged as follows, the corresponding
statements for `F` itself coming from
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

* That `a` acts invertibly on the sections of `N` over `X.basicOpen a` needs the one genuinely
  new step, `mem_of_smul_mem_of_le_basicOpen`: the quotient `w` of a section of `N` by `a`
  satisfies `a|_V • (r • w|_V) = 0` for every `V ≤ X.basicOpen a` and every `r : Γ(I, V)`, and
  `a|_V` is a unit there, so `r • w|_V = 0`.
* Injectivity up to powers of `a` is inherited from `F` verbatim, `N` being a subobject.
* Surjectivity up to powers of `a` is the one place where **finite type** of `I` is used, and it
  is the only place in this development where it is used at all. A section `x₀` of `F` over `U`
  lifting a section of `N` over `X.basicOpen a` is killed by each element of `Γ(I, U)` only
  after multiplication by some power of `a`, and the exponent depends on the element; a finite
  generating family of `Γ(I, U)` makes the exponent uniform by taking the supremum, and
  `smul_eq_zero_of_span_eq_top` propagates the conclusion from the generators to all of
  `Γ(I, U)`. The affine description of the sections of `N`
  (`IsAnnihilatorSubsheaf.mem_iff_of_isAffineOpen`) then puts the corrected section into `N`.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.AnnihilatorQcoh

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule}
  {F : X.Modules} {N : F.Submodule}

/-- **Dividing a section of the annihilator subsheaf by a function invertible on the domain
leaves the quotient in the annihilator subsheaf.** This is the step that has no counterpart for
`F` itself, and the reason the annihilator subsheaf is a localization rather than merely a
submodule of one. -/
theorem mem_of_smul_mem_of_le_basicOpen (hN : IsAnnihilatorSubsheaf I F N)
    {U : X.Opens} (a : Γ(X, U)) (w t : Γ(F, X.basicOpen a))
    (ht : t ∈ N.toSubmodule.obj (op (X.basicOpen a)))
    (hw : X.presheaf.map (homOfLE (X.basicOpen_le a)).op a • w = t) :
    w ∈ N.toSubmodule.obj (op (X.basicOpen a)) := by
  refine (hN (X.basicOpen a) w).mpr fun V hV r hr ↦ ?_
  have haV : IsUnit (X.presheaf.map (homOfLE (hV.trans (X.basicOpen_le a))).op a) :=
    isUnit_map_of_le_basicOpen a hV
  refine eq_zero_of_isUnit_smul_eq_zero haV ?_
  have hzero : r • F.presheaf.map (homOfLE hV).op t = 0 := (hN _ t).mp ht V hV r hr
  have hres : F.presheaf.map (homOfLE hV).op t =
      X.presheaf.map (homOfLE (hV.trans (X.basicOpen_le a))).op a •
        F.presheaf.map (homOfLE hV).op w := by
    rw [← hw, Scheme.Modules.map_smul, ← X.presheaf.map_comp_apply]
    rfl
  rw [hres, smul_comm] at hzero
  exact hzero

/-- **The sections of the annihilator subsheaf over a basic open are a localization.** For an
affine open `U` and `a ∈ Γ(X, U)`, the restriction of the sections of `N` over `U` to
`X.basicOpen a` is a localization away from `a`. -/
theorem isLocalizedModule_restrictₗ_of_isAnnihilatorSubsheaf (hN : IsAnnihilatorSubsheaf I F N)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType] [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE N.toSheafOfModules (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ N.toSheafOfModules (X.basicOpen_le a)) := by
  let := moduleOfLE N.toSheafOfModules (X.basicOpen_le a)
  let := moduleOfLE F (X.basicOpen_le a)
  have hFloc : IsLocalizedModule.Away a (restrictₗ F (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  obtain ⟨hFinj, hFsurj⟩ :=
    TorsionQuasicoherent.smul_bijective_of_isLocalizedModule (restrictₗ F (X.basicOpen_le a)) a
  obtain ⟨T, hT⟩ := exists_finset_span_eq_top I hU
  have hker : ∀ z : Γ(F, U), restrictₗ F (X.basicOpen_le a) z = 0 → ∃ n : ℕ, a ^ n • z = 0 := by
    intro z hz
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq
      (f := restrictₗ F (X.basicOpen_le a)) a (hz.trans (map_zero _).symm)
    exact ⟨n, by simpa using hn⟩
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (TorsionQuasicoherent.isUnit_algebraMap_end ?_ ?_) ?_ ?_
  · -- `a` acts injectively on the sections of `N` over `X.basicOpen a`, from `F`.
    intro y₁ y₂ hy
    exact subVal_injective N (hFinj _ _ (congrArg (subVal N) hy))
  · -- `a` acts surjectively, by dividing in `F` and putting the quotient back into `N`.
    intro y
    obtain ⟨w, hw⟩ := hFsurj (subVal N y)
    exact ⟨⟨w, mem_of_smul_mem_of_le_basicOpen hN a w _ (subVal_mem N y) hw⟩,
      subVal_injective N hw⟩
  · -- Surjectivity up to powers of `a`: the uniform exponent over a generating family.
    intro y
    obtain ⟨n, x₀, hx₀⟩ :=
      IsLocalizedModule.Away.surj (restrictₗ F (X.basicOpen_le a)) a (subVal N y)
    have hgen : ∀ z ∈ T, ∃ m : ℕ, a ^ m • (idealVal I z • x₀) = 0 := by
      intro z _
      have hmem : X.presheaf.map (homOfLE (X.basicOpen_le a)).op (idealVal I z) ∈
          I.toSubmodule.obj (op (X.basicOpen a)) :=
        I.toSubmodule.map_mem _ (idealVal_mem I z)
      have hkill : idealVal I z • subVal N y = 0 :=
        hN.smul_section_eq_zero (X.basicOpen a) (subVal_mem N y)
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op (idealVal I z)) hmem
      refine hker _ ?_
      rw [(restrictₗ F (X.basicOpen_le a)).map_smul, ← hx₀, smul_smul,
        mul_comm (idealVal I z) (a ^ n), ← smul_smul, hkill, smul_zero]
    choose! m hm using hgen
    have hsup : ∀ z ∈ T, a ^ T.sup m • (idealVal I z • x₀) = 0 := by
      intro z hz
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) hz)
      rw [hk, show m z + k = k + m z from by omega, pow_add, mul_smul, hm z hz, smul_zero]
    have hx₁gen : ∀ z ∈ T, idealVal I z • (a ^ T.sup m • x₀) = 0 := by
      intro z hz
      rw [smul_smul, mul_comm (idealVal I z) (a ^ T.sup m), ← smul_smul, hsup z hz]
    have hx₁mem : a ^ T.sup m • x₀ ∈ N.toSubmodule.obj (op U) :=
      (hN.mem_iff_of_isAffineOpen hU _).mpr fun r hr ↦
        smul_eq_zero_of_span_eq_top I (T : Set Γ(I.toSheafOfModules, U)) hT _ hx₁gen r hr
    refine ⟨T.sup m + n, ⟨a ^ T.sup m • x₀, hx₁mem⟩, subVal_injective N ?_⟩
    show a ^ (T.sup m + n) • subVal N y = restrictₗ F (X.basicOpen_le a) (a ^ T.sup m • x₀)
    rw [(restrictₗ F (X.basicOpen_le a)).map_smul, ← hx₀, pow_add, mul_smul]
  · -- Injectivity up to powers of `a`, inherited from `F`.
    intro z hz
    obtain ⟨n, hn⟩ := hker _ (congrArg (subVal N) hz)
    refine ⟨n, subVal_injective N ?_⟩
    show a ^ n • subVal N z = (0 : Γ(F, U))
    exact hn

/-- **Part (1) of [Stacks, Tag 01PO].** The subsheaf of sections of a quasi-coherent module
annihilated by a quasi-coherent ideal sheaf of finite type is quasi-coherent.

Such a subsheaf exists for every `I` and `F` (`isAnnihilatorSubsheaf_annihilatorSubmodule`) and
is unique (`IsAnnihilatorSubsheaf.unique`), so the hypothesis `hN` is not a restriction. -/
@[stacks 01PO "part (1)"]
theorem IsAnnihilatorSubsheaf.isQuasicoherent (hN : IsAnnihilatorSubsheaf I F N)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType] [F.IsQuasicoherent] :
    N.toSheafOfModules.IsQuasicoherent :=
  TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ N.toSheafOfModules
    fun _ hU a ↦ isLocalizedModule_restrictₗ_of_isAnnihilatorSubsheaf hN hU a

/-- Part (1) read off for the explicit ideal transporter, which is where the annihilator
subsheaf is constructed. -/
theorem isQuasicoherent_annihilatorSubmodule
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules)
    [I.toSheafOfModules.IsQuasicoherent] [I.toSheafOfModules.IsFiniteType] [F.IsQuasicoherent] :
    (Stacks.SheafOfModules.annihilatorSubmodule F
      (mul_comm_ringCatSheaf X) I).toSheafOfModules.IsQuasicoherent :=
  (isAnnihilatorSubsheaf_annihilatorSubmodule I F).isQuasicoherent

end Stacks.AlgebraicGeometry.AnnihilatorQcoh

end
