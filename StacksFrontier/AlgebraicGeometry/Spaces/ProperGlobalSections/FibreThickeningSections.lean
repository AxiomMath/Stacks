module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Thickening

/-!
# Global sections of quotients identified with direct images of structure sheaves

For a closed subspace `Z` of an algebraic space `X` and an `𝒪_X`-module `Q` identified with
`i_*𝒪_Z` by an isomorphism `c`, the global sections of `Q` are the global functions of `Z`
(Stacks 0732).  This file records how that identification interacts with the structure
projections and with the transition maps between two closed subspaces `Z ⊆ Z'`: both are
restriction of functions.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardSectionsTopos`: `Γ(X, Q) ⟶ Γ(Z, 𝒪_Z)` for `Q ≅ i_*𝒪_Z`.

## Main results

* `AlgebraicGeometry.Space.pushforwardSectionsTopos_map_eq`: a projection `𝒪_X ⟶ Q`
  identified with the structure projection is restriction of functions on global sections.
* `AlgebraicGeometry.Space.pushforwardSectionsTopos_transition`: a map `Q' ⟶ Q` under the
  projections, for `Z ⊆ Z'`, is restriction of functions along `Z ⊆ Z'` on global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open Stacks.Sheaves.RingedToposModules (fSharpSet pushforwardModules)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Sections

/-- The comparison of Stacks 0732 on the structure sheaf, read at the topos spelling. -/
theorem globalSectionsPushforwardIsoSite_hom_app_unit_apply {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W)
    (s : ((modulePushforward B S hS k).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Z))).sections) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS Z))).hom s =
      globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS k) (toposUnit B S hS Z)
        (SheafOfModules.sectionsMap
          ((modulePushforwardIso B S hS k).inv.app (toposUnit B S hS Z)) s) :=
  rfl

/-- A quotient map identified with the structure projection of a closed subspace is, at the topos
spelling of the direct image, the canonical morphism `1 ⟶ i_*1`. -/
theorem comp_isoTopos_hom_eq_pushforwardUnitSection {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1)
    {Q : Modules.{u, u} B S hS X.1 X.2} (p : SheafOfModules.unit _ ⟶ Q)
    (c : Q ≅ pushforwardStructureSheaf B S hS X Z)
    (hc : p ≫ c.hom = structureProjection B S hS X Z) :
    p ≫ (c ≪≫ ((modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).app
      (toposUnit B S hS ⟨Z.1.toFunctor, Z.2.1⟩)).symm).hom =
      pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS
        (subspaceInclusion B S hS X Z)) :=
  comp_comp_eq_of_comp_eq _ _ _ _ _
    (Iso.hom_inv_id_app (modulePushforwardIso B S hS (subspaceInclusion B S hS X Z))
      (toposUnit B S hS ⟨Z.1.toFunctor, Z.2.1⟩))
    (hc.trans (pushforwardUnitSection_comp_modulePushforwardIso_hom B S hS X Z).symm)

/-- Global sections of a module identified with `k_*𝒪_W`, as global sections of the structure
sheaf of `W`, at the topos spelling. -/
def pushforwardSectionsTopos {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y)
    {Q : Modules.{u, u} B S hS Y.1 Y.2}
    (c : Q ≅ (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W)))
    (x : Q.sections) : (toposUnit B S hS W).sections :=
  globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS k) (toposUnit B S hS W)
    (SheafOfModules.sectionsMap (c ≪≫ ((modulePushforwardIso B S hS k).app
      (toposUnit B S hS W)).symm).hom x)

/-- The topos spelling of the identification is the comparison of Stacks 0732. -/
theorem pushforwardSectionsTopos_eq {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y)
    {Q : Modules.{u, u} B S hS Y.1 Y.2}
    (c : Q ≅ (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W)))
    (x : Q.sections) :
    (pushforwardSectionsTopos k c x).1 =
      (((globalSectionsPushforwardIsoSite B S hS k).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS W))).hom
          (SheafOfModules.sectionsMap c.hom x)).1 :=
  rfl

/-- A projection `𝒪_Y ⟶ Q` followed by the identification with `k_*𝒪_W`, on global sections. -/
theorem pushforwardSectionsTopos_map_eq_of_comp_eq {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y)
    {Q : Modules.{u, u} B S hS Y.1 Y.2} (p : SheafOfModules.unit _ ⟶ Q)
    (c : Q ≅ (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W)))
    (σ : SheafOfModules.unit _ ⟶
      (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W)))
    (hc : p ≫ c.hom = σ) (s : (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections) :
    (pushforwardSectionsTopos k c (SheafOfModules.sectionsMap p s)).1 =
      (((globalSectionsPushforwardIsoSite B S hS k).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS W))).hom
          (SheafOfModules.sectionsMap σ s)).1 := by
  subst hc
  rfl

/-- **A projection `𝒪_X ⟶ Q` identified with the structure projection of `Z` is restriction of
functions on global sections.** -/
theorem pushforwardSectionsTopos_map_eq {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1)
    {Q : Modules.{u, u} B S hS X.1 X.2} (p : SheafOfModules.unit _ ⟶ Q)
    (c : Q ≅ pushforwardStructureSheaf B S hS X Z)
    (hc : p ≫ c.hom = structureProjection B S hS X Z)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    (pushforwardSectionsTopos (subspaceInclusion B S hS X Z) c
        (SheafOfModules.sectionsMap p s)).1 =
      (globalSectionsRingHomSite B S hS (subspaceInclusion B S hS X Z) ⟨s.1, s.2⟩).1 :=
  (pushforwardSectionsTopos_map_eq_of_comp_eq (subspaceInclusion B S hS X Z) p c
    (structureProjection B S hS X Z) hc s).trans
    (globalSectionsPushforwardIsoSite_hom_structureProjection B S hS X Z s)

/-- The identification on a section given by a morphism out of the structure sheaf. -/
theorem pushforwardSectionsTopos_unitHomEquiv {W Y : AlgebraicSpaces B S hS} (k : W ⟶ Y)
    {Q R : Modules.{u, u} B S hS Y.1 Y.2}
    (c : Q ≅ (modulePushforward B S hS k).obj (SheafOfModules.unit (structureRingSheaf B S hS W)))
    (b : SheafOfModules.unit _ ⟶ R) (q : R ⟶ Q) :
    pushforwardSectionsTopos k c (SheafOfModules.sectionsMap q (SheafOfModules.unitHomEquiv _ b)) =
      globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS k) (toposUnit B S hS W)
        (SheafOfModules.unitHomEquiv _ ((b ≫ q) ≫ (c ≪≫ ((modulePushforwardIso B S hS k).app
          (toposUnit B S hS W)).symm).hom)) :=
  rfl

/-- **Transitions at the topos spelling, for arbitrary morphisms `j ≫ i' = i`.** -/
theorem globalSectionsPushforwardEquiv_sectionsMap_transition {W W' Y : AlgebraicSpaces B S hS}
    (j : W ⟶ W') (i' : W' ⟶ Y) (i : W ⟶ Y) (h : j ≫ i' = i)
    {Q Q' : Modules.{u, u} B S hS Y.1 Y.2}
    (p' : SheafOfModules.unit _ ⟶ Q') (p : SheafOfModules.unit _ ⟶ Q) (q : Q' ⟶ Q) (hq : p' ≫ q = p)
    [hp' : Epi p']
    (c' : Q' ≅ (pushforwardModules (smallEtaleRingedToposModulesHom B S hS i')).obj
      (toposUnit B S hS W'))
    (c : Q ≅ (pushforwardModules (smallEtaleRingedToposModulesHom B S hS i)).obj
      (toposUnit B S hS W))
    (hc' : p' ≫ c'.hom = pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS i'))
    (hc : p ≫ c.hom = pushforwardUnitSection (smallEtaleRingedToposModulesHom B S hS i))
    (x : Q'.sections) :
    (globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i) _
        (SheafOfModules.sectionsMap c.hom (SheafOfModules.sectionsMap q x))).1 =
      (globalSectionsRingHom (smallEtaleRingedToposModulesHom B S hS j)
        ⟨(globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i') _
            (SheafOfModules.sectionsMap c'.hom x)).1,
          (globalSectionsPushforwardEquiv (smallEtaleRingedToposModulesHom B S hS i') _
            (SheafOfModules.sectionsMap c'.hom x)).2⟩).1 := by
  obtain ⟨b, rfl⟩ := (SheafOfModules.unitHomEquiv Q').surjective x
  exact globalSectionsPushforwardEquiv_transition_of_comp_eq j i' i h p' p q hq c' c hc' hc b

/-- **Transitions between quotients identified with direct images of structure sheaves of closed
subspaces `Z ⊆ Z'` are restriction of functions along `Z ⊆ Z'`.** -/
theorem pushforwardSectionsTopos_transition {X : AlgebraicSpaces B S hS}
    (Z Z' : ClosedSubspaces B S hS X.1)
    (j : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z'.1.toFunctor, Z'.2.1⟩)
    (h : j ≫ subspaceInclusion B S hS X Z' = subspaceInclusion B S hS X Z)
    {Q Q' : Modules.{u, u} B S hS X.1 X.2}
    (p' : SheafOfModules.unit _ ⟶ Q') (p : SheafOfModules.unit _ ⟶ Q) (q : Q' ⟶ Q) (hq : p' ≫ q = p)
    [hp' : Epi p']
    (c' : Q' ≅ pushforwardStructureSheaf B S hS X Z')
    (c : Q ≅ pushforwardStructureSheaf B S hS X Z)
    (hc' : p' ≫ c'.hom = structureProjection B S hS X Z')
    (hc : p ≫ c.hom = structureProjection B S hS X Z) (x : Q'.sections) :
    (pushforwardSectionsTopos (subspaceInclusion B S hS X Z) c
        (SheafOfModules.sectionsMap q x)).1 =
      (globalSectionsRingHom (smallEtaleRingedToposModulesHom B S hS j)
        ⟨(pushforwardSectionsTopos (subspaceInclusion B S hS X Z') c' x).1,
          (pushforwardSectionsTopos (subspaceInclusion B S hS X Z') c' x).2⟩).1 :=
  globalSectionsPushforwardEquiv_sectionsMap_transition j _ _ h p' p q hq
    (c' ≪≫ ((modulePushforwardIso B S hS (subspaceInclusion B S hS X Z')).app
      (toposUnit B S hS ⟨Z'.1.toFunctor, Z'.2.1⟩)).symm)
    (c ≪≫ ((modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)).app
      (toposUnit B S hS ⟨Z.1.toFunctor, Z.2.1⟩)).symm)
    (comp_isoTopos_hom_eq_pushforwardUnitSection Z' p' c' hc')
    (comp_isoTopos_hom_eq_pushforwardUnitSection Z p c hc) x

end Sections

end AlgebraicGeometry.Space
