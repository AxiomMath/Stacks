module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftForPresentationSmallSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentSectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeSmallSections

/-!
# Every coherent module on an algebraic space is a universe lift

Let `F` be an algebraic space over a scheme in `Type u`. Its `𝒪_F`-modules appear with sections
in different universes: the universe `u` of the structure sheaf, where direct images and higher
direct images live, and larger universes such as the universe `max (u + 1) w` of the Euler
characteristic of Stacks 0DN1. This file shows that nothing is lost by working in the universe
`u` for coherent modules: every coherent `𝒪_F`-module with sections in `Type (max (u + 1) w)` is
the universe lift `SheafOfModules.uliftForPresentation` of a coherent `𝒪_F`-module with sections
in `Type u`.

A coherent module is of finite type, so on the essentially small étale site its modules of
sections are `u`-small (`SheafOfModules.small_sections_of_isFiniteType`), hence it is the lift of
the sheaf of its shrunk sections (`SheafOfModules.uliftForPresentationShrinkSectionsIso`); and
quasi-coherence and coherence on the site descend to the shrunk sections.

## Main results

* `AlgebraicGeometry.Space.isCoherent_uliftForPresentation`: the universe lift of a coherent
  `𝒪_F`-module is coherent.
* `AlgebraicGeometry.Space.exists_iso_uliftForPresentation_of_isCoherent`: **every coherent
  `𝒪_F`-module is, up to isomorphism, the universe lift of a coherent `𝒪_F`-module with sections
  in the universe of the structure sheaf.**
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The universe lift of a coherent `𝒪_F`-module is coherent**: quasi-coherence and coherence on
the site are unchanged by raising the universe of the sections. -/
instance isCoherent_uliftForPresentation (M : Modules.{u, u} B S hS F hF)
    [hM : IsCoherent B S hS F hF M] :
    IsCoherent B S hS F hF
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) where
  toIsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation' hM.toIsQuasicoherentOnSite
  toIsCoherentOnSite :=
    SheafOfModules.isCoherentOnSite_uliftForPresentation M hM.toIsCoherentOnSite

/-- **Every coherent `𝒪_F`-module is the universe lift of a coherent module with sections in the
universe of the structure sheaf.** -/
theorem exists_iso_uliftForPresentation_of_isCoherent
    (M : Modules.{u, max (u + 1) w} B S hS F hF) [hM : IsCoherent B S hS F hF M] :
    ∃ M' : Modules.{u, u} B S hS F hF, IsCoherent B S hS F hF M' ∧
      Nonempty (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M' ≅ M) := by
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : ∀ X, Small.{u} (M.val.obj X) :=
    SheafOfModules.small_sections_of_isFiniteType.{u} M
  let M' := SheafOfModules.shrinkSections.{u + 1, u, u, u, max (u + 1) w} M
  let e := SheafOfModules.uliftForPresentationShrinkSectionsIso.{u + 1, u, u, u, max (u + 1) w} M
  refine ⟨M', ?_, ⟨e⟩⟩
  have hq : M'.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hM.toIsQuasicoherentOnSite)
  let eM (V) : M.val.obj V ≃+ M'.val.obj V :=
    (SheafOfModules.shrinkSectionsEquiv.{u + 1, u, u, u, max (u + 1) w} M V).symm.toAddEquiv
  have he (V) (a) (x : M.val.obj V) : eM V (a • x) = RingEquiv.refl _ a • eM V x :=
    map_smul (SheafOfModules.shrinkSectionsEquiv.{u + 1, u, u, u, max (u + 1) w} M V).symm a x
  have hn {V W} (f : V ⟶ W) (x : M.val.obj V) :
      eM W (M.val.restrictₛₗ f x) = M'.val.restrictₛₗ f (eM V x) := by
    change _ = (SheafOfModules.shrinkSectionsEquiv.{u + 1, u, u, u, max (u + 1) w} M W).symm
      (M.val.restrictₛₗ f (SheafOfModules.shrinkSectionsEquiv.{u + 1, u, u, u, max (u + 1) w} M V
        ((SheafOfModules.shrinkSectionsEquiv.{u + 1, u, u, u, max (u + 1) w} M V).symm x)))
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hc : SheafOfModules.IsCoherentOnSite M' :=
    { isFiniteType := Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
        (fun _ ↦ RingEquiv.refl _) eM he hn hM.isFiniteType
      kernel_isFiniteType := fun U n s ↦
        Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv
          (fun _ ↦ RingEquiv.refl _) (fun _ _ ↦ rfl) eM he hn s
          (hM.kernel_isFiniteType U n _) }
  exact { toIsQuasicoherentOnSite := hq, toIsCoherentOnSite := hc }

end AlgebraicGeometry.Space

end
