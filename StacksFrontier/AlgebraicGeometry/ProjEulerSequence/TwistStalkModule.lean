module

public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract

/-!
# The two stalk actions on the sheaf associated to a graded module agree

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`, let `M` be a `ℤ`-graded
`S`-module with grading `𝒨`, and let `x` be a point of `Proj(S)`. The stalk at `x` of the sheaf
`M̃` associated to `M` is a module over the stalk `𝒪_{Proj(S),x}` of the structure sheaf in two
ways: by transporting the degree-zero localization `M₍p₎` along the identification
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkEquiv`, and by the
general action of the stalk of a presheaf of rings on the stalk of a presheaf of modules over it.
The two actions are equal. Through the identification `SemilinearStalk.commStalkRingEquiv` of
the `CommRingCat`-valued and `RingCat`-valued stalks of the structure sheaf, the transported action
also agrees with the action of the `RingCat`-valued stalk.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafGerm_smul`: the germ of
  a product of a scalar section and a section is the product of their germs.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk_smul_eq` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkModule_eq`: the two
  module structures on the stalk have the same scalar multiplication, hence are equal.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk_ringCat_smul`:
  the transported action of the `CommRingCat`-valued stalk agrees with the action of the
  `RingCat`-valued stalk through `SemilinearStalk.commStalkRingEquiv`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

omit [Decomposition 𝒨] in
/-- The identification of the stalk of `M̃` with the degree-zero localization `M₍p₎` turns the
transported action of the structure-sheaf stalk into the action of `S₍p₎`. -/
theorem associatedModuleSheafStalkEquiv_smul (x : ProjectiveSpectrum.top 𝒮)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
    (z : associatedModuleSheafStalk 𝒮 𝒨 x) :
    associatedModuleSheafStalkEquiv 𝒮 𝒨 x (r • z) =
      Proj.stalkIso' 𝒮 x r • associatedModuleSheafStalkEquiv 𝒮 𝒨 x z := by
  show associatedModuleSheafStalkEquiv 𝒮 𝒨 x
      ((associatedModuleSheafStalkEquiv 𝒮 𝒨 x).symm
        (Proj.stalkIso' 𝒮 x r • associatedModuleSheafStalkEquiv 𝒮 𝒨 x z)) = _
  simp

omit [Decomposition 𝒨] in
/-- The germ at `x` of the product of a section of the structure sheaf and a section of `M̃` is
the product of their germs, for the action transported from the degree-zero localization. -/
theorem associatedModuleSheafGerm_smul (x : ProjectiveSpectrum.top 𝒮)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (hx : x ∈ U)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op U))
    (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op U)) :
    associatedModuleSheafGerm 𝒮 𝒨 x U hx (r • s) =
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.germ U x hx r •
        associatedModuleSheafGerm 𝒮 𝒨 x U hx s := by
  refine (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).injective ?_
  rw [associatedModuleSheafStalkEquiv_germ_smul, associatedModuleSheafStalkEquiv_smul]

/-- The action of the structure-sheaf stalk on the stalk of `M̃` given by the general module
structure on the stalk of a presheaf of modules. -/
@[instance_reducible]
def associatedModuleSheafStalkModuleOfPresheaf (x : ProjectiveSpectrum.top 𝒮) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
      (associatedModuleSheafStalk 𝒮 𝒨 x) :=
  inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf x))

omit [Decomposition 𝒨] in
/-- The action transported from the degree-zero localization is the general action of the stalk
of a presheaf of rings on the stalk of a presheaf of modules over it. -/
theorem associatedModuleSheafStalk_smul_eq (x : ProjectiveSpectrum.top 𝒮)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
    (m : associatedModuleSheafStalk 𝒮 𝒨 x) :
    r • m = haveI := associatedModuleSheafStalkModuleOfPresheaf 𝒮 𝒨 x; r • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ :=
    TopCat.Presheaf.exists_germ_eq (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf r
  obtain ⟨U₂, hU₂, m₀, hm⟩ := associatedModuleSheafStalk_exists_germ 𝒮 𝒨 x m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hr' := (TopCat.Presheaf.germ_res_apply (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf
    (homOfLE inf_le_left) x hmem r₀).trans hr
  have hm' := (TopCat.Presheaf.germ_res_apply
    (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf
    (homOfLE inf_le_right) x hmem m₀).trans hm
  rw [← hr', ← hm']
  exact (associatedModuleSheafGerm_smul 𝒮 𝒨 x (U₁ ⊓ U₂) hmem _ _).symm.trans
    (PresheafOfModules.germ_smul
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val x (U₁ ⊓ U₂) hmem _ _)

omit [Decomposition 𝒨] in
/-- **The two module structures on the stalk of `M̃` are equal**: the one transported from the
degree-zero localization `M₍p₎` and the general one on the stalk of a presheaf of modules. -/
theorem associatedModuleSheafStalkModule_eq (x : ProjectiveSpectrum.top 𝒮) :
    associatedModuleSheafStalkModule 𝒮 𝒨 x = associatedModuleSheafStalkModuleOfPresheaf 𝒮 𝒨 x :=
  Module.ext' _ _ fun r m => associatedModuleSheafStalk_smul_eq 𝒮 𝒨 x r m

/-- The action of the `RingCat`-valued stalk of the structure sheaf on the stalk of `M̃`, given
by the general module structure on the stalk of a presheaf of modules. -/
@[instance_reducible]
def associatedModuleSheafStalkRingCatModule (x : ProjectiveSpectrum.top 𝒮) :
    Module (TopCat.Presheaf.stalk (C := RingCat.{u})
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}) x)
      (associatedModuleSheafStalk 𝒮 𝒨 x) :=
  inferInstanceAs (Module _ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.presheaf x))

omit [Decomposition 𝒨] in
/-- The action transported from the degree-zero localization `M₍p₎` agrees with the action of the
`RingCat`-valued stalk of the structure sheaf, through the identification
`SemilinearStalk.commStalkRingEquiv` of the two stalks. -/
theorem associatedModuleSheafStalk_ringCat_smul (x : ProjectiveSpectrum.top 𝒮)
    (s : TopCat.Presheaf.stalk (C := RingCat.{u})
      ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) x)
    (m : associatedModuleSheafStalk 𝒮 𝒨 x) :
    SemilinearStalk.commStalkRingEquiv (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj x s • m =
      haveI := associatedModuleSheafStalkRingCatModule 𝒮 𝒨 x; s • m :=
  (associatedModuleSheafStalk_smul_eq 𝒮 𝒨 x _ m).trans
    (SheafOfModules.commStalkRingEquiv_smul_eq' (ProjectiveSpectrum.Proj.structureSheaf 𝒮) x
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val s m)

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end
