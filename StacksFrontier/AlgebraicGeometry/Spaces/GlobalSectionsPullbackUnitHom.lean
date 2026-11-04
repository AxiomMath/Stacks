module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeGlobalSectionsSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange

/-!
# The inverse image of a global section, read as a map out of the structure sheaf

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`𝓝` be an `𝒪_Y`-module. A global section `σ` of `𝓝` is a map `𝒪_Y ⟶ 𝓝`, and its inverse image
`g^*σ` (`AlgebraicGeometry.Space.globalSectionsPullbackMap`) is a global section of `g^*𝓝`, that
is, a map `𝒪_{Y'} ⟶ g^*𝓝`. This file records that this map is the pullback `g^*(𝒪_Y ⟶ 𝓝)` read
out of `𝒪_{Y'} ≅ g^*𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.unitHomEquiv_symm_globalSectionsPushforwardEquiv_unit`: the same
  statement for a morphism of ringed topoi, with Stacks 0732 applied to the image of the section
  under the unit of `f^* ⊣ f_*`.
* `AlgebraicGeometry.Space.unitHomEquiv_symm_globalSectionsPullbackMap`: the map
  `𝒪_{Y'} ⟶ g^*𝓝` named by `g^*σ` is `𝒪_{Y'} ≅ g^*𝒪_Y ⟶ g^*𝓝`, the pullback of the map named
  by `σ`.

## Implementation notes

The modules on an algebraic space are spelled over the small étale ringed site, while the
pullback adjunction and Stacks 0732 are stated over the small étale ringed topos. The two
spellings are definitionally equal, but the elaborator compares them slowly inside large terms,
so every passage between them is made in a separate lemma about variables:
`globalSectionsPushforwardIsoSite_hom_app_eq`, `globalSectionsPushforwardEquiv_congr` and
`unitHomEquiv_symm_eq_of_eq_globalSectionsPushforwardEquiv_unit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Stacks 0732 at the module spelling of the direct image, on a global section: the
ringed-topos comparison of global sections after the identification of the two direct images. -/
theorem globalSectionsPushforwardIsoSite_hom_app_eq {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (s : ((modulePushforward B S hS k).obj N).sections) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom s =
      Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
        (smallEtaleRingedToposModulesHom B S hS k) N
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePushforwardIso B S hS k).inv.app N)).hom s) := rfl

/-- The map out of the structure sheaf named by the image of a global section under a morphism
of modules is the composite. -/
theorem unitHomEquiv_symm_globalSectionsFunctor_map {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ : Modules.{u, u} B S hS Z.1 Z.2} (φ : M₁ ⟶ M₂)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj M₁) :
    (SheafOfModules.unitHomEquiv M₂).symm
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map φ).hom s) =
      (SheafOfModules.unitHomEquiv M₁).symm s ≫ φ :=
  (SheafOfModules.unitHomEquiv_symm_comp s φ).symm

/-- `Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv` respects equality of
sections, stated at the module spelling of the global sections. -/
theorem globalSectionsPushforwardEquiv_congr {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (N : Modules.{u, u} B S hS Z.1 Z.2)
    {a b : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules
          (smallEtaleRingedToposModulesHom B S hS k)).obj N)} (h : a = b) :
    Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
        (smallEtaleRingedToposModulesHom B S hS k) N a =
      Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
        (smallEtaleRingedToposModulesHom B S hS k) N b :=
  congrArg _ h

/-- A morphism followed by an isomorphism and its inverse, stated abstractly so that it can be
instantiated at large terms. -/
private theorem comp_hom_comp_inv {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b) (e : b ≅ c) :
    (f ≫ e.hom) ≫ e.inv = f := by
  simp

/-- **The section of a pullback named by the unit, in the ringed-topos spelling.** For a
morphism of ringed topoi `f` and a global section `σ` of `𝓝`, Stacks 0732 applied to the image of
`σ` under the unit `𝓝 ⟶ f_*f^*𝓝` names the map `𝒪 ≅ f^*𝒪 ⟶ f^*𝓝`, the pullback of the map named
by `σ`. -/
theorem unitHomEquiv_symm_globalSectionsPushforwardEquiv_unit
    {X Y : RingedTopos.{u, u + 1, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (N : SheafOfModules.{u} (ringSheaf Y.O)) (σ : N.sections) :
    (SheafOfModules.unitHomEquiv (f.pullbackModules.obj N)).symm
        (Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv f (f.pullbackModules.obj N)
          (SheafOfModules.sectionsMap
            ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f).unit.app N) σ)) =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f).hom ≫
        f.pullbackModules.map ((SheafOfModules.unitHomEquiv N).symm σ) := by
  rw [Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv_apply, Equiv.symm_apply_apply,
    ← SheafOfModules.unitHomEquiv_symm_comp,
    Stacks.Cohomology.SiteModules.pushforwardUnitHomEquiv_apply,
    Adjunction.homEquiv_naturality_left_symm]
  have htri : ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f).homEquiv _
      _).symm
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f).unit.app N) = 𝟙 _ := by
    rw [Equiv.symm_apply_eq]
    exact (Adjunction.homEquiv_id _ _).symm
  rw [htri, Category.comp_id]
  rfl

/-- `AlgebraicGeometry.Space.unitHomEquiv_symm_globalSectionsPushforwardEquiv_unit` for the
small étale ringed topoi of a morphism of algebraic spaces, at the module spelling. -/
theorem unitHomEquiv_symm_eq_of_eq_globalSectionsPushforwardEquiv_unit
    {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (σ : N.sections) (x : ((modulePullback B S hS g).obj N).sections)
    (h : x = Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
      (smallEtaleRingedToposModulesHom B S hS g) ((modulePullback B S hS g).obj N)
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (X := smallEtaleRingedTopos B S hS Y') (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposModulesHom B S hS g)).unit.app N)).hom σ)) :
    (SheafOfModules.unitHomEquiv ((modulePullback B S hS g).obj N)).symm x =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (smallEtaleRingedToposModulesHom B S hS g)).hom ≫
        (modulePullback B S hS g).map ((SheafOfModules.unitHomEquiv N).symm σ) := by
  subst h
  exact unitHomEquiv_symm_globalSectionsPushforwardEquiv_unit
    (smallEtaleRingedToposModulesHom B S hS g) N σ

/-- **The inverse image of a global section is the pullback of the map it names.** For
`g : Y' ⟶ Y` and a global section `σ` of an `𝒪_Y`-module `𝓝`, the map `𝒪_{Y'} ⟶ g^*𝓝` named by
the inverse image of `σ` is the comparison `𝒪_{Y'} ≅ g^*𝒪_Y` followed by `g^*` of the map
`𝒪_Y ⟶ 𝓝` named by `σ`.

The inverse image of global sections is the unit of the adjunction `g^* ⊣ g_*` followed by
Stacks 0732, and Stacks 0732 reads a section of `g_*M` as a map `𝒪_Y ⟶ g_*M`, takes its adjunct
`g^*𝒪_Y ⟶ M` and precomposes `𝒪_{Y'} ≅ g^*𝒪_Y`; the adjunct of `σ` followed by the unit is
`g^*σ` by a triangle identity. -/
theorem unitHomEquiv_symm_globalSectionsPullbackMap {Y Y' : AlgebraicSpaces B S hS}
    (g : Y' ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) (σ : N.sections) :
    (SheafOfModules.unitHomEquiv ((modulePullback B S hS g).obj N)).symm
        ((globalSectionsPullbackMap B S hS g N).hom σ) =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (smallEtaleRingedToposModulesHom B S hS g)).hom ≫
        (modulePullback B S hS g).map ((SheafOfModules.unitHomEquiv N).symm σ) := by
  have hη : (modulePullbackAdjunction B S hS g).unit.app N =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (X := smallEtaleRingedTopos B S hS Y') (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposModulesHom B S hS g)).unit.app N ≫
        (modulePushforwardIso B S hS g).hom.app ((modulePullback B S hS g).obj N) :=
    (Adjunction.homEquiv_id _ N).symm.trans
      ((Adjunction.homEquiv_ofNatIsoRight_apply _ (modulePushforwardIso B S hS g) (𝟙 _)).trans
        (congrArg (· ≫ (modulePushforwardIso B S hS g).hom.app ((modulePullback B S hS g).obj N))
          (Adjunction.homEquiv_id _ N)))
  have e1 := globalSectionsPullbackMap_apply g N σ
  have h₀ := globalSectionsPushforwardIsoSite_hom_app_eq g ((modulePullback B S hS g).obj N)
  have h₂ := (globalSectionsFunctor_map_comp_apply ((modulePullbackAdjunction B S hS g).unit.app N)
    ((modulePushforwardIso B S hS g).inv.app ((modulePullback B S hS g).obj N)) σ).symm
  have hunit : (modulePullbackAdjunction B S hS g).unit.app N ≫
      (modulePushforwardIso B S hS g).inv.app ((modulePullback B S hS g).obj N) =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (X := smallEtaleRingedTopos B S hS Y') (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposModulesHom B S hS g)).unit.app N := by
    rw [hη]
    exact comp_hom_comp_inv _ ((modulePushforwardIso B S hS g).app
        ((modulePullback B S hS g).obj N))
  have h₃ := congrArg (fun φ => ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map φ).hom σ) hunit
  have t1 := e1.trans (h₀ _)
  have t2 := h₂.trans h₃
  have t3 := globalSectionsPushforwardEquiv_congr g ((modulePullback B S hS g).obj N) t2
  exact unitHomEquiv_symm_eq_of_eq_globalSectionsPushforwardEquiv_unit g N σ _ (t1.trans t3)

end AlgebraicGeometry.Space

end
