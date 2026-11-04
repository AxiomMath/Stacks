module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquareComparison
public import StacksFrontier.CategoryTheory.CatCommSqHInvCube
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonCube
public meta import StacksFrontier.Tactic.HEqCongr
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel

/-!
# The comparison of models along a commutative square of schemes

For a morphism of schemes `f`, `AlgebraicGeometry.Scheme.Hom.zariskiDerivedPullbackModelIso`
identifies the derived pullback along `f` read on Zariski ringed topoi at the standard model with
`Lf^*` of Stacks 08DW at the locally small model. This file sets up, along a commutative square
`p ≫ q = r ≫ s` of schemes, the 2-cell of Stacks 0D6D on Zariski ringed topoi attached to the
square, and identifies it on modules and on complexes with the composition isomorphisms of
pullbacks of modules of ringed spaces.

## Main definitions

* `AlgebraicGeometry.Scheme.zariskiSquarePullbackModulesIso`: the 2-cell of the square on
  pullbacks of modules.
* `AlgebraicGeometry.Scheme.zariskiSquareDerivedPullbackIso`: its derived counterpart.
* `AlgebraicGeometry.Scheme.zariskiModelInverseSquare`: the model square read through the
  inverses of the comparisons of models.

## Main results

* `AlgebraicGeometry.Scheme.zariskiSquarePullbackModulesIso_hom_app_modulePullbackComp`: the 2-cell
  on pullbacks of modules through the identifications with pullbacks along ringed spaces.
* `AlgebraicGeometry.Scheme.zariskiSquare_mapHomotopyCategory_comp`: the same on degreewise
  pullbacks of complexes.
* `AlgebraicGeometry.Scheme.zariskiDerivedPullbackModelIso_cube`: the comparisons of models
  carry the 2-cell `zariskiSquareDerivedPullbackIso` to the composition isomorphisms of 0D5S.
* `AlgebraicGeometry.Scheme.zariskiModelInverseSquare_cube`: the same through the inverses of the
  comparisons of models.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Scheme

variable {W' W T' T : Scheme.{u}} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (w₀ : p ≫ q = r ≫ s)

/-- The comparison of `Lf^*` with degreewise pullback, transported along an equality of
morphisms of schemes. -/
theorem derivedPullbackComparison_eqToIso {X Y : Scheme.{u}} {t₁ t₂ : X ⟶ Y} (h : t₁ = t₂)
    (K : HomotopyCategory Y.Modules (ComplexShape.up ℤ)) :
    (eqToIso (congrArg Stacks.Duality.derivedPullback h)).hom.app (DerivedCategory.Qh.obj K) ≫
        (Stacks.Duality.derivedPullbackComparison t₂).app K =
      (Stacks.Duality.derivedPullbackComparison t₁).app K ≫
        DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
          (Scheme.Modules.pullbackCongr h) (ComplexShape.up ℤ)).hom.app K) := by
  subst h
  simp [Stacks.Homology.mapHomotopyCategoryIso, Scheme.Modules.pullbackCongr]

/-- The composite of the composition isomorphisms of Stacks 0D5S along a commutative square,
at an object. -/
theorem derivedPullbackCompIso_square_app (X : DerivedCategory T.Modules) :
    ((Stacks.Duality.derivedPullbackCompIso p q).hom ≫
      eqToHom (congrArg Stacks.Duality.derivedPullback w₀) ≫
      (Stacks.Duality.derivedPullbackCompIso r s).inv).app X =
      (Stacks.Duality.derivedPullbackCompIso p q).hom.app X ≫
        eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj X) w₀) ≫
        (Stacks.Duality.derivedPullbackCompIso r s).inv.app X := by
  simp only [NatTrans.comp_app, eqToHom_app]

end AlgebraicGeometry.Scheme

namespace Stacks.Duality

/-- `Lf^*` of Stacks 08DW is a left derived functor of degreewise pullback, in the scheme
spelling. -/
theorem isLeftDerivedFunctor_derivedPullback {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback f).IsLeftDerivedFunctor (derivedPullbackComparison f)
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    f.toLRSHom.toShHom).IsLeftDerivedFunctor
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison _)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
      (ComplexShape.up ℤ)))

end Stacks.Duality

namespace AlgebraicGeometry.Scheme

variable {W' W T' T : Scheme.{u}} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (w₀ : p ≫ q = r ≫ s)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The Zariski 2-cell of a commutative square of schemes**, on pullbacks of modules of
Zariski ringed topoi: `q^* ⋙ p^* ≅ s^* ⋙ r^*` read through
`zariskiPullbackModulesIsoSchemeModules` and the composition isomorphisms of
`Scheme.Modules.pullback`. -/
abbrev zariskiSquarePullbackModulesIso :
    q.zariskiRingedToposHom.toModulesHom.pullbackModules ⋙
        p.zariskiRingedToposHom.toModulesHom.pullbackModules ≅
      s.zariskiRingedToposHom.toModulesHom.pullbackModules ⋙
        r.zariskiRingedToposHom.toModulesHom.pullbackModules :=
  Functor.isoWhiskerLeft _ p.zariskiPullbackModulesIsoSchemeModules ≪≫
    Functor.isoWhiskerRight q.zariskiPullbackModulesIsoSchemeModules (Scheme.Modules.pullback p) ≪≫
    Scheme.Modules.pullbackComp p q ≪≫ Scheme.Modules.pullbackCongr w₀ ≪≫
    (Scheme.Modules.pullbackComp r s).symm ≪≫
    Functor.isoWhiskerRight s.zariskiPullbackModulesIsoSchemeModules.symm
      (Scheme.Modules.pullback r) ≪≫
    Functor.isoWhiskerLeft _ r.zariskiPullbackModulesIsoSchemeModules.symm

/-- The derived pullback along `q ∘ p`, as a morphism of Zariski ringed topoi, exists. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_zariskiComp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (pullbackOnHomotopy (X := X.zariskiRingedTopos) (Y := Z.zariskiRingedTopos)
      (RingedToposHom.comp (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        (Z := Z.zariskiRingedTopos) g.zariskiRingedToposHom f.zariskiRingedToposHom)
        ).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := Z.zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (X := X.zariskiRingedTopos) (Y := Z.zariskiRingedTopos)
    (RingedToposHom.comp (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
        (Z := Z.zariskiRingedTopos) g.zariskiRingedToposHom f.zariskiRingedToposHom)

/-- **The Zariski 2-cell on derived categories**: `Lq^* ⋙ Lp^* ≅ Ls^* ⋙ Lr^*` for the
derived pullbacks of Zariski ringed topoi (standard model), the left derived isomorphism of
`zariskiSquarePullbackModulesIso` between the two composites (Stacks 0D6D). -/
abbrev zariskiSquareDerivedPullbackIso :
    derivedPullback (X := W.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
        q.zariskiRingedToposHom ⋙
      derivedPullback (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
        p.zariskiRingedToposHom ≅
    derivedPullback (X := T'.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
        s.zariskiRingedToposHom ⋙
      derivedPullback (X := W'.zariskiRingedTopos) (Y := T'.zariskiRingedTopos)
        r.zariskiRingedToposHom :=
  derivedPullbackCompIso (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
      (Z := T.zariskiRingedTopos) p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
    derivedPullbackIsoOfPullbackModulesIso (X := W'.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
      (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
        zariskiSquarePullbackModulesIso p q r s w₀ ≪≫
        (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          r.zariskiRingedToposHom s.zariskiRingedToposHom).symm) ≪≫
    (derivedPullbackCompIso (X := W'.zariskiRingedTopos) (Y := T'.zariskiRingedTopos)
      (Z := T.zariskiRingedTopos) r.zariskiRingedToposHom s.zariskiRingedToposHom).symm

/-- The model square of `f` for the inverses of the comparisons of models:
`C_Y⁻¹ ⋙ Lf^*_{Zar} ≅ Lf^* ⋙ C_X⁻¹`. -/
abbrev zariskiModelInverseSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (StacksDraft.DerivedModel.schemeModulesComparison Y).inverse ⋙
        derivedPullback (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
          f.zariskiRingedToposHom ≅
      Stacks.Duality.derivedPullback f ⋙
        (StacksDraft.DerivedModel.schemeModulesComparison X).inverse :=
  (CatCommSq.hInv (StacksDraft.DerivedModel.schemeModulesComparison Y)
    (derivedPullback (X := X.zariskiRingedTopos) (Y := Y.zariskiRingedTopos)
      f.zariskiRingedToposHom)
    (Stacks.Duality.derivedPullback f) (StacksDraft.DerivedModel.schemeModulesComparison X)
    ⟨f.zariskiDerivedPullbackModelIso.symm⟩).iso

/-- Whiskering `e.symm` and then `e` on the left is the identity, at an object. -/
private theorem isoWhiskerLeft_symm_hom_app_comp_hom_app {C D E : Type*} [Category C]
    [Category D] [Category E] (G : C ⥤ D) {F F' : D ⥤ E} (e : F ≅ F') (N : C) :
    (Functor.isoWhiskerLeft G e.symm).hom.app N ≫ (Functor.isoWhiskerLeft G e).hom.app N =
      𝟙 ((G ⋙ F').obj N) :=
  Iso.inv_hom_id_app e (G.obj N)

section Factors

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (M : SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.zariskiRingedTopos.J) Z.zariskiRingedTopos.O)))

/-- The whiskered inverse and direct comparisons of `zariskiPullbackModulesIsoSchemeModules`
cancel. -/
theorem isoWhiskerLeft_zariskiPullbackModulesIso_symm_hom_app_comp :
    (Functor.isoWhiskerLeft g.zariskiRingedToposHom.toModulesHom.pullbackModules
        f.zariskiPullbackModulesIsoSchemeModules.symm).hom.app M ≫
      (Functor.isoWhiskerLeft g.zariskiRingedToposHom.toModulesHom.pullbackModules
        f.zariskiPullbackModulesIsoSchemeModules).hom.app M =
      𝟙 ((g.zariskiRingedToposHom.toModulesHom.pullbackModules ⋙
        Scheme.Modules.pullback f).obj M) :=
  isoWhiskerLeft_symm_hom_app_comp_hom_app _ _ M

/-- Naturality of `zariskiPullbackModulesIsoModulePullback` at the comparison for `g`. -/
theorem zariskiPullbackModulesIsoModulePullback_hom_app_naturality :
    f.zariskiRingedToposHom.toModulesHom.pullbackModules.map
        (g.zariskiPullbackModulesIsoModulePullback.hom.app M) ≫
      f.zariskiPullbackModulesIsoModulePullback.hom.app
        ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj M) =
      (Functor.isoWhiskerLeft g.zariskiRingedToposHom.toModulesHom.pullbackModules
        f.zariskiPullbackModulesIsoSchemeModules).hom.app M ≫
      (Functor.isoWhiskerRight g.zariskiPullbackModulesIsoModulePullback
        (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom)).hom.app M :=
  f.zariskiPullbackModulesIsoModulePullback.hom.naturality
    (g.zariskiPullbackModulesIsoModulePullback.hom.app M)

/-- The whiskered inverse of `zariskiPullbackModulesIsoSchemeModules` and its ringed-space
spelling cancel. -/
theorem isoWhiskerRight_zariskiPullbackModulesIso_symm_hom_app_comp :
    (Functor.isoWhiskerRight g.zariskiPullbackModulesIsoSchemeModules.symm
        (Scheme.Modules.pullback f)).hom.app M ≫
      (Functor.isoWhiskerRight g.zariskiPullbackModulesIsoModulePullback
        (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom)).hom.app M =
      𝟙 ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M) :=
  ((Scheme.Modules.pullback f).map_comp _ _).symm.trans
    ((congrArg (Scheme.Modules.pullback f).map
      (Iso.inv_hom_id_app g.zariskiPullbackModulesIsoSchemeModules M)).trans
      (CategoryTheory.Functor.map_id _ _))

/-- The inverse of `Scheme.Modules.pullbackComp` cancels its ringed-space spelling. -/
theorem pullbackComp_inv_app_comp_modulePullbackComp_hom_app :
    (Scheme.Modules.pullbackComp f g).inv.app M ≫
      (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
        g.toLRSHom.toShHom).hom.app M = 𝟙 _ := by
  rw [Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp f g]
  exact Iso.inv_hom_id_app _ M

end Factors

include w₀ in
/-- A commutative square of schemes is a commutative square of ringed spaces. -/
theorem toShHom_comp_eq :
    p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom = r.toLRSHom.toShHom ≫ s.toLRSHom.toShHom :=
  congrArg (fun t : W' ⟶ T => t.toLRSHom.toShHom) w₀

include w₀ in
/-- `pullbackComp` followed by `pullbackCongr w₀`, in the ringed-space spelling. -/
theorem pullbackComp_hom_app_comp_pullbackCongr_hom_app
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.zariskiRingedTopos.J)
        T.zariskiRingedTopos.O))) :
    (Scheme.Modules.pullbackComp p q).hom.app M ≫
    (Scheme.Modules.pullbackCongr w₀).hom.app M =
    (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
      q.toLRSHom.toShHom).hom.app M ≫
    (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
      (toShHom_comp_eq p q r s w₀))).hom.app M := by
  rw [Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp p q]
  rfl

/-- The 2-cell `zariskiSquarePullbackModulesIso` at a module, as the composite of its factors. -/
theorem zariskiSquarePullbackModulesIso_hom_app_eq
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.zariskiRingedTopos.J)
        T.zariskiRingedTopos.O))) :
    (zariskiSquarePullbackModulesIso p q r s w₀).hom.app M =
      (Functor.isoWhiskerLeft q.zariskiRingedToposHom.toModulesHom.pullbackModules
          p.zariskiPullbackModulesIsoSchemeModules).hom.app M ≫
        (Functor.isoWhiskerRight q.zariskiPullbackModulesIsoModulePullback
          (RingedSpaceModuleAdjunction.modulePullback p.toLRSHom.toShHom)).hom.app M ≫
        (Scheme.Modules.pullbackComp p q).hom.app M ≫
        (Scheme.Modules.pullbackCongr w₀).hom.app M ≫
        (Scheme.Modules.pullbackComp r s).inv.app M ≫
        (Functor.isoWhiskerRight s.zariskiPullbackModulesIsoSchemeModules.symm
          (Scheme.Modules.pullback r)).hom.app M ≫
        (Functor.isoWhiskerLeft s.zariskiRingedToposHom.toModulesHom.pullbackModules
          r.zariskiPullbackModulesIsoSchemeModules.symm).hom.app M :=
  rfl

/-- The 2-cell `zariskiSquarePullbackModulesIso`, read through the identifications of the
pullbacks of modules of Zariski ringed topoi with those of ringed spaces, is the composite of the
composition isomorphisms of pullbacks of modules of ringed spaces along the square. -/
theorem zariskiSquarePullbackModulesIso_hom_app_modulePullbackComp
    (M : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.zariskiRingedTopos.J)
        T.zariskiRingedTopos.O))) :
    (zariskiSquarePullbackModulesIso p q r s w₀).hom.app M ≫
        r.zariskiRingedToposHom.toModulesHom.pullbackModules.map
          (s.zariskiPullbackModulesIsoModulePullback.hom.app M) ≫
        r.zariskiPullbackModulesIsoModulePullback.hom.app
          ((RingedSpaceModuleAdjunction.modulePullback s.toLRSHom.toShHom).obj M) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp r.toLRSHom.toShHom
          s.toLRSHom.toShHom).hom.app M =
      p.zariskiRingedToposHom.toModulesHom.pullbackModules.map
          (q.zariskiPullbackModulesIsoModulePullback.hom.app M) ≫
        p.zariskiPullbackModulesIsoModulePullback.hom.app
          ((RingedSpaceModuleAdjunction.modulePullback q.toLRSHom.toShHom).obj M) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
          q.toLRSHom.toShHom).hom.app M ≫
        (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
          (toShHom_comp_eq p q r s w₀))).hom.app M := by
  have e := zariskiSquarePullbackModulesIso_hom_app_eq p q r s w₀ M
  have hl := isoWhiskerLeft_zariskiPullbackModulesIso_symm_hom_app_comp r s M
  have hr := zariskiPullbackModulesIsoModulePullback_hom_app_naturality r s M
  have hm := isoWhiskerRight_zariskiPullbackModulesIso_symm_hom_app_comp r s M
  have hcrs := pullbackComp_inv_app_comp_modulePullbackComp_hom_app r s M
  have hcpq := pullbackComp_hom_app_comp_pullbackCongr_hom_app p q r s w₀ M
  have hp := zariskiPullbackModulesIsoModulePullback_hom_app_naturality p q M
  have hjZ := (whisker_eq _ ((reassoc_of% hm) _)).trans
    ((whisker_eq _ (Category.id_comp _)).trans hcrs)
  have hR1 := whisker_eq
    ((Functor.isoWhiskerLeft q.zariskiRingedToposHom.toModulesHom.pullbackModules
      p.zariskiPullbackModulesIsoSchemeModules).hom.app M)
    (whisker_eq ((Functor.isoWhiskerRight q.zariskiPullbackModulesIsoModulePullback
      (RingedSpaceModuleAdjunction.modulePullback p.toLRSHom.toShHom)).hom.app M)
      ((whisker_eq _ (Category.comp_id _)).trans hcpq))
  have hR2 := (reassoc_of% hp) ((Stacks.DerivedPullback.Composition.modulePullbackComp
        p.toLRSHom.toShHom q.toLRSHom.toShHom).hom.app M ≫
        (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
          (toShHom_comp_eq p q r s w₀))).hom.app M)
  have hR := hR1.trans hR2.symm
  exact StacksDraft.DerivedModel.comp_chase_square _ _ _ _ _ _ _ _ _ _ _ _ _
    (𝟙 ((Scheme.Modules.pullback (r ≫ s)).obj M)) _ e hl hr hjZ hR

/-- The transport of degreewise pullback along `w₀`, in the scheme and in the ringed-space
spelling. -/
theorem mapHomotopyCategoryIso_pullbackCongr
    (K : HomotopyCategory T.Modules (ComplexShape.up ℤ)) :
    (Stacks.Homology.mapHomotopyCategoryIso (Scheme.Modules.pullbackCongr w₀)
      (ComplexShape.up ℤ)).hom.app K =
    (Stacks.Homology.mapHomotopyCategoryIso
      (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
        (toShHom_comp_eq p q r s w₀)))
      (ComplexShape.up ℤ)).hom.app K :=
  eq_of_heq (by heq_congr_full)

end

/-- `derivedPullbackComparison_eqToIso` along `w₀`, with the transport of degreewise pullback in
the ringed-space spelling. -/
theorem derivedPullbackComparison_eqToIso_square
    (K : HomotopyCategory T.Modules (ComplexShape.up ℤ)) :
    (eqToIso (congrArg Stacks.Duality.derivedPullback w₀)).hom.app (DerivedCategory.Qh.obj K) ≫
        (Stacks.Duality.derivedPullbackComparison (r ≫ s)).app K =
      (Stacks.Duality.derivedPullbackComparison (p ≫ q)).app K ≫
        DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
          (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
            (toShHom_comp_eq p q r s w₀))) (ComplexShape.up ℤ)).hom.app K) :=
  (derivedPullbackComparison_eqToIso w₀ K).trans
    (whisker_eq _ (Functor.congr_map _ (mapHomotopyCategoryIso_pullbackCongr p q r s w₀ K)))

/-- Transport of an equation through two heterogeneous equalities. -/
private theorem eq_of_heq_of_eq_of_heq {α β : Sort _} {a b : α} {c d : β} (h₁ : HEq a c)
    (h₂ : c = d) (h₃ : HEq d b) : a = b :=
  eq_of_heq (h₁.trans ((heq_of_eq h₂).trans h₃))

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The 2-cell of the square on degreewise pullbacks of complexes, read through the
identifications with pullbacks of modules of ringed spaces, is the composite of the composition
isomorphisms of degreewise pullback. -/
theorem zariskiSquare_mapHomotopyCategory_comp
    (K : HomotopyCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.zariskiRingedTopos.J)
        T.zariskiRingedTopos.O))) (ComplexShape.up ℤ)) :
    (pullbackMapHomotopySquareIso (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
        (Y' := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos) p.zariskiRingedToposHom
        q.zariskiRingedToposHom r.zariskiRingedToposHom s.zariskiRingedToposHom
        (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
            (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
            p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
          zariskiSquarePullbackModulesIso p q r s w₀ ≪≫
          (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
            (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
            r.zariskiRingedToposHom s.zariskiRingedToposHom).symm)).hom.app K ≫
      (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := W'.zariskiRingedTopos)
        (Y := T'.zariskiRingedTopos) r.zariskiRingedToposHom).map
        ((@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
        (RingedToposHom.pullbackModules_additive s.zariskiRingedToposHom)
        (RingedSpaceModuleAdjunction.modulePullback_additive s.toLRSHom.toShHom)
        s.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ)).hom.app K) ≫
      (@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
        (RingedToposHom.pullbackModules_additive r.zariskiRingedToposHom)
        (RingedSpaceModuleAdjunction.modulePullback_additive r.toLRSHom.toShHom)
        r.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ)).hom.app
        (((RingedSpaceModuleAdjunction.modulePullback s.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso r.toLRSHom.toShHom
        s.toLRSHom.toShHom).hom.app K =
    (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := W'.zariskiRingedTopos)
        (Y := W.zariskiRingedTopos) p.zariskiRingedToposHom).map
        ((@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
        (RingedToposHom.pullbackModules_additive q.zariskiRingedToposHom)
        (RingedSpaceModuleAdjunction.modulePullback_additive q.toLRSHom.toShHom)
        q.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ)).hom.app K) ≫
      (@Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
        (RingedToposHom.pullbackModules_additive p.zariskiRingedToposHom)
        (RingedSpaceModuleAdjunction.modulePullback_additive p.toLRSHom.toShHom)
        p.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ)).hom.app
        (((RingedSpaceModuleAdjunction.modulePullback q.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso p.toLRSHom.toShHom
        q.toLRSHom.toShHom).hom.app K ≫
      (Stacks.Homology.mapHomotopyCategoryIso
        (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
          (toShHom_comp_eq p q r s w₀)))
        (ComplexShape.up ℤ)).hom.app K := by
  have key := StacksDraft.DerivedModel.mapHomotopyCategory_square_comp' (ComplexShape.up ℤ)
    (hFzq := RingedToposHom.pullbackModules_additive q.zariskiRingedToposHom)
    (hFzp := RingedToposHom.pullbackModules_additive p.zariskiRingedToposHom)
    (hFzs := RingedToposHom.pullbackModules_additive s.zariskiRingedToposHom)
    (hFzr := RingedToposHom.pullbackModules_additive r.zariskiRingedToposHom)
    (hFq := RingedSpaceModuleAdjunction.modulePullback_additive q.toLRSHom.toShHom)
    (hFp := RingedSpaceModuleAdjunction.modulePullback_additive p.toLRSHom.toShHom)
    (hFs := RingedSpaceModuleAdjunction.modulePullback_additive s.toLRSHom.toShHom)
    (hFr := RingedSpaceModuleAdjunction.modulePullback_additive r.toLRSHom.toShHom)
    (hFzpq := RingedToposHom.pullbackModules_additive
      (RingedToposHom.comp (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
        (Z := T.zariskiRingedTopos) q.zariskiRingedToposHom p.zariskiRingedToposHom))
    (hFzrs := RingedToposHom.pullbackModules_additive
      (RingedToposHom.comp (X := W'.zariskiRingedTopos) (Y := T'.zariskiRingedTopos)
        (Z := T.zariskiRingedTopos) s.zariskiRingedToposHom r.zariskiRingedToposHom))
    (hFpq := RingedSpaceModuleAdjunction.modulePullback_additive
      (p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom))
    (hFrs := RingedSpaceModuleAdjunction.modulePullback_additive
      (r.toLRSHom.toShHom ≫ s.toLRSHom.toShHom))
    (zq := q.zariskiPullbackModulesIsoModulePullback)
    (zp := p.zariskiPullbackModulesIsoModulePullback)
    (zs := s.zariskiPullbackModulesIsoModulePullback)
    (zr := r.zariskiPullbackModulesIsoModulePullback)
    (γpq := RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
        (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
        p.zariskiRingedToposHom q.zariskiRingedToposHom)
    (γrs := RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
        (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
        r.zariskiRingedToposHom s.zariskiRingedToposHom)
    (bpq := Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
      q.toLRSHom.toShHom)
    (brs := Stacks.DerivedPullback.Composition.modulePullbackComp r.toLRSHom.toShHom
      s.toLRSHom.toShHom)
    (k := eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
      (toShHom_comp_eq p q r s w₀)))
    (ψ := zariskiSquarePullbackModulesIso p q r s w₀)
    (hψ := fun M => eq_of_heq_of_eq_of_heq (by heq_congr)
      (zariskiSquarePullbackModulesIso_hom_app_modulePullbackComp p q r s w₀ M) (by heq_congr))
    (σz := pullbackMapHomotopySquareIso (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
      (Y' := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos) p.zariskiRingedToposHom
      q.zariskiRingedToposHom r.zariskiRingedToposHom s.zariskiRingedToposHom
      (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
        zariskiSquarePullbackModulesIso p q r s w₀ ≪≫
        (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          r.zariskiRingedToposHom s.zariskiRingedToposHom).symm)) (hσ := rfl)
    (zHq := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive q.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive q.toLRSHom.toShHom)
      q.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zHp := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive p.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive p.toLRSHom.toShHom)
      p.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zHs := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive s.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive s.toLRSHom.toShHom)
      s.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zHr := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive r.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive r.toLRSHom.toShHom)
      r.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (βpq := Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso p.toLRSHom.toShHom
      q.toLRSHom.toShHom)
    (βrs := Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso r.toLRSHom.toShHom
      s.toLRSHom.toShHom)
    (κH := Stacks.Homology.mapHomotopyCategoryIso
      (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
        (toShHom_comp_eq p q r s w₀)))
      (ComplexShape.up ℤ))
    (hzq := rfl) (hzp := rfl) (hzs := rfl) (hzr := rfl)
    (hβpq := rfl) (hβrs := rfl) (hκH := rfl) (K := K)
  exact eq_of_heq_of_eq_of_heq (by heq_congr) key (by heq_congr)


/-- **The cube for the model squares**: along a commutative square `p ≫ q = r ≫ s` of
schemes, the comparisons of models of the derived pullbacks carry the 2-cell
`zariskiSquareDerivedPullbackIso` to the composition isomorphisms of Stacks 0D5S. -/
theorem zariskiDerivedPullbackModelIso_cube
    (Y : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := T.zariskiRingedTopos.J)
        T.zariskiRingedTopos.O)))) :
    (StacksDraft.DerivedModel.schemeModulesComparison W').functor.map
        ((zariskiSquareDerivedPullbackIso p q r s w₀).hom.app Y) ≫
      r.zariskiDerivedPullbackModelIso.hom.app
        ((derivedPullback (X := T'.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
          s.zariskiRingedToposHom).obj Y) ≫
      (Stacks.Duality.derivedPullback r).map (s.zariskiDerivedPullbackModelIso.hom.app Y) =
    p.zariskiDerivedPullbackModelIso.hom.app
        ((derivedPullback (X := W.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
          q.zariskiRingedToposHom).obj Y) ≫
      (Stacks.Duality.derivedPullback p).map (q.zariskiDerivedPullbackModelIso.hom.app Y) ≫
      (Stacks.Duality.derivedPullbackCompIso p q).hom.app
        ((StacksDraft.DerivedModel.schemeModulesComparison T).functor.obj Y) ≫
      (eqToIso (congrArg Stacks.Duality.derivedPullback w₀)).hom.app
        ((StacksDraft.DerivedModel.schemeModulesComparison T).functor.obj Y) ≫
      (Stacks.Duality.derivedPullbackCompIso r s).inv.app
        ((StacksDraft.DerivedModel.schemeModulesComparison T).functor.obj Y) := by
  have hcube := StacksDraft.DerivedModel.modelIso_cube
    (Pzq := Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := W.zariskiRingedTopos)
      (Y := T.zariskiRingedTopos) q.zariskiRingedToposHom)
    (Pzp := Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := W'.zariskiRingedTopos)
      (Y := W.zariskiRingedTopos) p.zariskiRingedToposHom)
    (Pzs := Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := T'.zariskiRingedTopos)
      (Y := T.zariskiRingedTopos) s.zariskiRingedToposHom)
    (Pzr := Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy (X := W'.zariskiRingedTopos)
      (Y := T'.zariskiRingedTopos) r.zariskiRingedToposHom)
    (sh₁ := StacksDraft.DerivedModel.shrinkComparisonQhIso T.Modules)
    (sh₂ := StacksDraft.DerivedModel.shrinkComparisonQhIso W.Modules)
    (sh₃ := StacksDraft.DerivedModel.shrinkComparisonQhIso T'.Modules)
    (sh₄ := StacksDraft.DerivedModel.shrinkComparisonQhIso W'.Modules)
    (cmpZq := derivedPullbackComparison (X := W.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
      q.zariskiRingedToposHom)
    (cmpZp := derivedPullbackComparison (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
      p.zariskiRingedToposHom)
    (cmpZs := derivedPullbackComparison (X := T'.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
      s.zariskiRingedToposHom)
    (cmpZr := derivedPullbackComparison (X := W'.zariskiRingedTopos)
      (Y := T'.zariskiRingedTopos) r.zariskiRingedToposHom)
    (cmpLSq := Stacks.Duality.derivedPullbackComparison q)
    (cmpLSp := Stacks.Duality.derivedPullbackComparison p)
    (cmpLSs := Stacks.Duality.derivedPullbackComparison s)
    (cmpLSr := Stacks.Duality.derivedPullbackComparison r)
    (cmpLSpq := Stacks.Duality.derivedPullbackComparison (p ≫ q))
    (cmpLSrs := Stacks.Duality.derivedPullbackComparison (r ≫ s))
    (zpq := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive q.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive q.toLRSHom.toShHom)
      q.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zpp := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive p.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive p.toLRSHom.toShHom)
      p.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zps := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive s.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive s.toLRSHom.toShHom)
      s.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (zpr := @Stacks.Homology.mapHomotopyCategoryIso _ _ _ _ _ _ _ _
      (RingedToposHom.pullbackModules_additive r.zariskiRingedToposHom)
      (RingedSpaceModuleAdjunction.modulePullback_additive r.toLRSHom.toShHom)
      r.zariskiPullbackModulesIsoModulePullback (ComplexShape.up ℤ))
    (Mq := q.zariskiDerivedPullbackModelIso) (Mp := p.zariskiDerivedPullbackModelIso)
    (Ms := s.zariskiDerivedPullbackModelIso) (Mr := r.zariskiDerivedPullbackModelIso)
    (cpq := Stacks.Duality.derivedPullbackCompIso p q)
    (crs := Stacks.Duality.derivedPullbackCompIso r s)
    (βpq := Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso p.toLRSHom.toShHom
      q.toLRSHom.toShHom)
    (βrs := Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso r.toLRSHom.toShHom
      s.toLRSHom.toShHom)
    (Θ := zariskiSquareDerivedPullbackIso p q r s w₀)
    (σz := pullbackMapHomotopySquareIso (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
      (Y' := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos) p.zariskiRingedToposHom
      q.zariskiRingedToposHom r.zariskiRingedToposHom s.zariskiRingedToposHom
      (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
        zariskiSquarePullbackModulesIso p q r s w₀ ≪≫
        (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
          (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
          r.zariskiRingedToposHom s.zariskiRingedToposHom).symm))
    (κ := eqToIso (congrArg Stacks.Duality.derivedPullback w₀))
    (κH := Stacks.Homology.mapHomotopyCategoryIso
      (eqToIso (congrArg RingedSpaceModuleAdjunction.modulePullback
        (toShHom_comp_eq p q r s w₀)))
      (ComplexShape.up ℤ))
    (W := quasiIsoTarget (Y := T.zariskiRingedTopos))
    (hQ₁ := Hom.isLocalization_zariskiQh T)
    (hQ'₁ := inferInstanceAs
      (Functor.IsLocalization _ (HomotopyCategory.quasiIso T.Modules (ComplexShape.up ℤ))))
    (hLS := Stacks.Duality.isLeftDerivedFunctor_derivedPullback (r ≫ s))
    (hMq := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (q.zariskiDerivedPullbackModelIso_hom_app_comparison K) (by heq_congr))
    (hMp := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (p.zariskiDerivedPullbackModelIso_hom_app_comparison K) (by heq_congr))
    (hMs := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (s.zariskiDerivedPullbackModelIso_hom_app_comparison K) (by heq_congr))
    (hMr := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (r.zariskiDerivedPullbackModelIso_hom_app_comparison K) (by heq_congr))
    (hcpq := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (Stacks.Duality.derivedPullbackCompIso_hom_app_comparison p q K) (by heq_congr))
    (hcrs := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (Stacks.Duality.derivedPullbackCompIso_hom_app_comparison r s K) (by heq_congr))
    (hΘ := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (derivedPullbackSquareIso_hom_app_comparison (X := W'.zariskiRingedTopos)
        (Y := W.zariskiRingedTopos) (Y' := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
        p.zariskiRingedToposHom q.zariskiRingedToposHom r.zariskiRingedToposHom
        s.zariskiRingedToposHom
        (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
            (Y := W.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
            p.zariskiRingedToposHom q.zariskiRingedToposHom ≪≫
          zariskiSquarePullbackModulesIso p q r s w₀ ≪≫
          (RingedToposHom.pullbackModulesCompIso (X := W'.zariskiRingedTopos)
            (Y := T'.zariskiRingedTopos) (Z := T.zariskiRingedTopos)
            r.zariskiRingedToposHom s.zariskiRingedToposHom).symm) K) (by heq_congr))
    (hκ := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (derivedPullbackComparison_eqToIso_square p q r s w₀ K) (by heq_congr))
    (hH := fun K => eq_of_heq_of_eq_of_heq (by heq_congr)
      (zariskiSquare_mapHomotopyCategory_comp p q r s w₀ K) (by heq_congr))
    (Y := Y)
  exact eq_of_heq_of_eq_of_heq (by heq_congr) hcube (by heq_congr)

/-- **The Zariski 2-cell through the inverses of the comparisons of models**: along a
commutative square `p ≫ q = r ≫ s` of schemes, the composition isomorphisms of Stacks 0D5S at
the locally small model correspond, through the model squares, to the Zariski 2-cell
`zariskiSquareDerivedPullbackIso`. -/
theorem zariskiModelInverseSquare_cube (X : DerivedCategory T.Modules) :
    (zariskiModelInverseSquare p).inv.app ((Stacks.Duality.derivedPullback q).obj X) ≫
      (derivedPullback (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
          p.zariskiRingedToposHom).map ((zariskiModelInverseSquare q).inv.app X) ≫
      (zariskiSquareDerivedPullbackIso p q r s w₀).hom.app
        ((StacksDraft.DerivedModel.schemeModulesComparison T).inverse.obj X) =
    (StacksDraft.DerivedModel.schemeModulesComparison W').inverse.map
        ((Stacks.Duality.derivedPullbackCompIso p q).hom.app X ≫
          eqToHom (congrArg (fun t => (Stacks.Duality.derivedPullback t).obj X) w₀) ≫
          (Stacks.Duality.derivedPullbackCompIso r s).inv.app X) ≫
      (zariskiModelInverseSquare r).inv.app ((Stacks.Duality.derivedPullback s).obj X) ≫
      (derivedPullback (X := W'.zariskiRingedTopos) (Y := T'.zariskiRingedTopos)
          r.zariskiRingedToposHom).map ((zariskiModelInverseSquare s).inv.app X) := by
  have h := CatCommSq.hInv_cube (StacksDraft.DerivedModel.schemeModulesComparison T)
    (StacksDraft.DerivedModel.schemeModulesComparison W)
    (StacksDraft.DerivedModel.schemeModulesComparison T')
    (StacksDraft.DerivedModel.schemeModulesComparison W')
    (derivedPullback (X := W.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
      q.zariskiRingedToposHom)
    (derivedPullback (X := W'.zariskiRingedTopos) (Y := W.zariskiRingedTopos)
      p.zariskiRingedToposHom)
    (derivedPullback (X := T'.zariskiRingedTopos) (Y := T.zariskiRingedTopos)
      s.zariskiRingedToposHom)
    (derivedPullback (X := W'.zariskiRingedTopos) (Y := T'.zariskiRingedTopos)
      r.zariskiRingedToposHom)
    (Stacks.Duality.derivedPullback q) (Stacks.Duality.derivedPullback p)
    (Stacks.Duality.derivedPullback s) (Stacks.Duality.derivedPullback r)
    ⟨q.zariskiDerivedPullbackModelIso.symm⟩ ⟨p.zariskiDerivedPullbackModelIso.symm⟩
    ⟨s.zariskiDerivedPullbackModelIso.symm⟩ ⟨r.zariskiDerivedPullbackModelIso.symm⟩
    (zariskiSquareDerivedPullbackIso p q r s w₀).hom.app
    ((Stacks.Duality.derivedPullbackCompIso p q).hom ≫
      eqToHom (congrArg Stacks.Duality.derivedPullback w₀) ≫
      (Stacks.Duality.derivedPullbackCompIso r s).inv)
    (fun Y => by
      refine Eq.trans ?_ (whisker_eq _ (whisker_eq _
        (derivedPullbackCompIso_square_app p q r s w₀ _).symm))
      refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _ (eq_whisker
        (eqToHom_app (congrArg Stacks.Duality.derivedPullback w₀) _) _))))
      exact eq_of_heq_of_eq_of_heq (by heq_congr)
        (zariskiDerivedPullbackModelIso_cube p q r s w₀ Y) (by heq_congr)) X
  have h' := h.trans (eq_whisker (Functor.congr_map
    (StacksDraft.DerivedModel.schemeModulesComparison W').inverse
    (derivedPullbackCompIso_square_app p q r s w₀ X)) _)
  exact eq_of_heq_of_eq_of_heq (by heq_congr) h' (by heq_congr)

end

end AlgebraicGeometry.Scheme
