module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections

/-!
# Direct images of K-injective complexes compute derived sections

Let `i : Z ⟶ X` and `p : X ⟶ Y` be morphisms of ringed spaces and `V ⊆ Y` open. For a K-injective
complex `ℐ` of `𝒪_Z`-modules, the direct image `i_* ℐ` computes derived sections over `p⁻¹ V`:
the unit `Γ(p⁻¹ V, i_* ℐ) ⟶ RΓ(p⁻¹ V, i_* ℐ)` is an isomorphism, although `i_* ℐ` need not be
K-injective. This is the content of [Stacks, Tag 0D5W] at the level of complexes.

## Main results

Both results live in the namespace `Stacks.Cohomology.DerivedSectionsLeray`.

* `isIso_derivedPreimageSectionsUnit_app_pushforward`: the unit statement above, at the standard
  model.
* `quasiIso_preimageSections_map_pushforward_of_isKInjective`: the same statement with no derived
  category in it: sections over `p⁻¹ V` carry a quasi-isomorphism from `i_* ℐ` into a K-injective
  complex to a quasi-isomorphism. Because it mentions no derived category, it holds for every
  model.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit exists_quasiIso_isKInjective
    isIso_derivedPushforwardUnit_app_of_isKInjective)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Opens Y.carrier)

attribute [local instance] HasDerivedCategory.standard in
/-- **Direct images of K-injective complexes compute derived sections.** For a K-injective
complex `ℐ` of `𝒪_Z`-modules the unit of `RΓ(p⁻¹ V, -)` is invertible at `i_* ℐ`. -/
theorem isIso_derivedPreimageSectionsUnit_app_pushforward
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPreimageSectionsUnit p V).app
      (((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
          (ComplexShape.up ℤ)).obj I))) := by
  have h₁ : IsIso ((derivedPreimageSectionsUnit (i ≫ p) V).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopyPreimageSections (i ≫ p) V) (exists_quasiIso_isKInjective Z)).2
      DerivedCategory.Qh (derivedPreimageSections (i ≫ p) V)
      (derivedPreimageSectionsUnit (i ≫ p) V) I hI
  have h₂ := isIso_lerayCompositeComparison i p V
  have h₃ : IsIso ((lerayCompositeUnit i p V).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)).obj I)) := by
    rw [← lerayCompositeComparison_fac_app]
    infer_instance
  have h₄ := isIso_derivedPushforwardUnit_app_of_isKInjective i I hI
  simp only [lerayCompositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h₃
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp h₃)

attribute [local instance] HasDerivedCategory.standard in
/-- **Direct images of K-injective complexes compute derived sections, with no derived category
in the statement.** If `ℐ` is a K-injective complex of `𝒪_Z`-modules and `s` is a
quasi-isomorphism from `i_* ℐ` to a K-injective complex of `𝒪_X`-modules, then sections over
`p⁻¹ V` carry `s` to a quasi-isomorphism of complexes of `Γ(V, 𝒪_Y)`-modules. -/
theorem quasiIso_preimageSections_map_pushforward_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (hI : I.IsKInjective)
    (J : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hJ : J.IsKInjective)
    (s : ((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
            (ComplexShape.up ℤ)).obj I) ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))
      (ComplexShape.up ℤ)
      (((preimageSections p V).mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  rw [← DerivedCategory.isIso_Qh_map_iff]
  have h₁ := isIso_derivedPreimageSectionsUnit_app_pushforward i p V I hI
  have h₂ : IsIso ((derivedPreimageSectionsUnit p V).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj J)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopyPreimageSections p V) (exists_quasiIso_isKInjective X)).2
      DerivedCategory.Qh (derivedPreimageSections p V) (derivedPreimageSectionsUnit p V) J hJ
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh _ s hs
  have h₃ : IsIso ((homotopyPreimageSections p V).map s ≫
      (derivedPreimageSectionsUnit p V).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj J)) := by
    rw [(derivedPreimageSectionsUnit p V).naturality s]
    dsimp only [Functor.comp_map]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h₃

end Stacks.Cohomology.DerivedSectionsLeray

end
