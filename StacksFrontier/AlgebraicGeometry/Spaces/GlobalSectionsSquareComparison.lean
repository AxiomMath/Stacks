module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.ToposModuleBaseChangeSquare

/-!
# Global sections around a commutative square of algebraic spaces

For a commutative square of algebraic spaces

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

a global section of `f_*g'_*N` over `Y` is a global section of `N` over `X'` in two ways: through
the global-sections isomorphisms of **Stacks 0732** for `f` and then for `g'`, or, after the
comparison `f_* ∘ g'_* ⟶ g_* ∘ f'_*` of the two composite direct images — the comparison the base
change map of **Stacks 0736** is the mate of — through those for `g` and then for `f'`.  This file
proves that the two agree.

## Main results

* `Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv_eq_terminal`: for a morphism of
  ringed topoi, the comparison of global sections of **Stacks 0732** is, on compatible families,
  the geometric comparison `MorphismOfTopoi.pushforwardTerminalHomEquiv` of the global sections of
  the underlying sheaves of sets.
* `AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite_hom_app_apply`: the same for the
  direct image of modules of algebraic spaces, at the spelling
  `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.pushforwardTerminalHomEquiv_squareComparison`: global sections of
  sheaves of sets around a commutative square, read through the comparison of **Stacks 03G2**,
  part (3).
* `AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite_squareComparison`: **the two readings
  of a global section of `f_*g'_*N` agree.**

## Implementation notes

The direct image of modules is spelled two ways in this development, and the underlying sheaf of
sets of a module two more; the identifications between the spellings are definitional but
expensive to check when they occur inside a composite.  Every crossing here is therefore made on
global sections of the underlying sheaves of sets of a *variable* module, read through
`AlgebraicGeometry.Space.smallEtaleDirectImage` and the pinned forgetful functor
`AlgebraicGeometry.Space.moduleSetSheafFunctor`, and the comparison around the square is entered
as a hypothesis `m = …` that is discharged by `subst` rather than by unfolding.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules (pushforwardModules pushforwardModulesUnitHomEquiv)
open Stacks.Cohomology.SiteModules (pushforwardUnitHomEquiv globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe w w' v u v' u'

namespace Stacks.Cohomology.SiteModules

open _root_.AlgebraicGeometry (RingedTopos)
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The comparison of global sections of Stacks 0732 is the geometric one.**  On compatible
families of sections, `Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv` is the
comparison `MorphismOfTopoi.pushforwardTerminalHomEquiv` of the global sections of the underlying
sheaves of sets, read through `terminalHomEquivSections`. -/
theorem globalSectionsPushforwardEquiv_eq_terminal
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : ((pushforwardModules f).obj N).sections) :
    globalSectionsPushforwardEquiv f N s =
      terminalHomEquivSections (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
        (f.toToposHom.pushforwardTerminalHomEquiv
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
          ((terminalHomEquivSections (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))).symm s)) := by
  rw [globalSectionsPushforwardEquiv_apply]
  refine (Equiv.apply_symm_apply (terminalHomEquivSections
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) _).symm.trans ?_
  refine (congrArg (terminalHomEquivSections
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (unitTerminalHomEquiv_pushforwardUnitHomEquiv f N _)).trans ?_
  exact congrArg (fun z ↦ terminalHomEquivSections
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
    (f.toToposHom.pushforwardTerminalHomEquiv _ ((terminalHomEquivSections _).symm z)))
    (Equiv.apply_symm_apply (SheafOfModules.unitHomEquiv ((pushforwardModules f).obj N)) s)

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-- The pinned forgetful functor and the forgetful functor of the ringed-topos spelling of the
structure sheaf act the same way on a morphism of modules.  Stated at a variable morphism, where
the identification of the two spellings is between small terms. -/
theorem moduleSetSheafFunctor_map_eq_topos {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (moduleSetSheafFunctor B S hS Z).map φ =
      (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)).map φ :=
  rfl

/-- The inverse of a component of `AlgebraicGeometry.Space.modulePushforwardIso` is the identity
on sections. -/
theorem modulePushforwardIso_inv_app_val_app {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (y : ((modulePushforward B S hS k).obj M).val.obj V) :
    ((modulePushforwardIso B S hS k).inv.app M).val.app V y = y :=
  (modulePushforwardIso_hom_app_val_app B S hS k M V
      (((modulePushforwardIso B S hS k).inv.app M).val.app V y)).symm.trans
    (modulesHom_val_app_congr (Iso.inv_hom_id_app (modulePushforwardIso B S hS k) M) V y)

/-- **The inverse comparison of the two direct images of modules is the identity on underlying
sheaves of sets.** -/
theorem moduleSheafFunctor_map_modulePushforwardIso_inv_app {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS W).O)).map
        ((modulePushforwardIso B S hS k).inv.app M) =
      CategoryStruct.id ((smallEtaleDirectImage B S hS k).obj (moduleSetSheaf B S hS Z M)) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_eq_of_val_app.{u, u, u + 1} _ _
    (fun V y ↦ modulePushforwardIso_inv_app_val_app k M V y)

/-- The global sections of the direct image of a module, as global sections of the geometric
direct image of its underlying sheaf of sets. -/
abbrev modulePushforwardSectionsEquivToposPushforward {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePushforward B S hS k).obj N).sections ≃
      ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos B S hS Z).O)).obj N)).obj.sections :=
  Equiv.refl _

/-- **Stacks 0732 at the module spelling of the direct image, on global sections**, is the
geometric comparison of the global sections of the underlying sheaves of sets. -/
theorem globalSectionsPushforwardIsoSite_hom_app_apply {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (s : ((modulePushforward B S hS k).obj N).sections) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom s =
      terminalHomEquivSections ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)).obj N)
        ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv _
          ((terminalHomEquivSections _).symm
            (modulePushforwardSectionsEquivToposPushforward k N s))) := by
  have h₀ : ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom s =
      Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv
        (smallEtaleRingedToposModulesHom B S hS k) N
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePushforwardIso B S hS k).inv.app N)).hom s) := rfl
  have hsec : (terminalHomEquivSections
        ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforward.obj
          ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos B S hS Z).O)).obj N))).symm
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map
          ((modulePushforwardIso B S hS k).inv.app N)).hom s) =
      (terminalHomEquivSections _).symm (modulePushforwardSectionsEquivToposPushforward k N s) :=
    Sheaf.hom_ext_sections fun V _ ↦ modulePushforwardIso_inv_app_val_app k N V (s.val V)
  exact h₀.trans ((Stacks.Cohomology.SiteModules.globalSectionsPushforwardEquiv_eq_terminal
    (smallEtaleRingedToposModulesHom B S hS k) N _).trans
    (congrArg (fun z ↦ terminalHomEquivSections ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)).obj N)
        ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv _ z))
      hsec))

/-- `globalSectionsPushforwardIsoSite_hom_app_apply` with the underlying sheaves of sets at the
pinned forgetful functor `AlgebraicGeometry.Space.moduleSetSheafFunctor`. -/
theorem globalSectionsPushforwardIsoSite_hom_app_apply_set {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (s : ((modulePushforward B S hS k).obj N).sections) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom s =
      terminalHomEquivSections ((moduleSetSheafFunctor B S hS Z).obj N)
        ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv _
          ((terminalHomEquivSections ((smallEtaleDirectImage B S hS k).obj
            ((moduleSetSheafFunctor B S hS Z).obj N))).symm s)) :=
  globalSectionsPushforwardIsoSite_hom_app_apply k N s

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- `pushforwardTerminalHomEquiv_comp_eqToHom` with the equality of direct images spelled
through `AlgebraicGeometry.Space.smallEtaleDirectImage`. -/
theorem pushforwardTerminalHomEquiv_comp_eqToHom {Z W : AlgebraicSpaces B S hS} {k k' : Z ⟶ W}
    (h : k = k') (F : Sheaf (SmallEtale.topology B S hS Z.1) (Type u))
    (c : ⊤_ (Sheaf (SmallEtale.topology B S hS W.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS k).obj F) :
    (smallEtaleRingedToposModulesHom B S hS k').toToposHom.pushforwardTerminalHomEquiv F
        (c ≫ (eqToHom (congrArg (fun m : Z ⟶ W ↦ smallEtaleDirectImage B S hS m) h)).app F) =
      (smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv F c := by
  subst h
  exact congrArg _ ((congrArg (c ≫ ·) (eqToHom_app rfl F)).trans (Category.comp_id c))

/-- `pushforwardTerminalHomEquiv_squareComparison` with the comparison of **Stacks 03G2**,
part (3), spelled through `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso`. -/
theorem pushforwardTerminalHomEquiv_squareComparison (comm : g' ≫ f = f' ≫ g)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (x : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS f).obj ((smallEtaleDirectImage B S hS g').obj E)) :
    (smallEtaleRingedToposModulesHom B S hS f').toToposHom.pushforwardTerminalHomEquiv E
        ((smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforwardTerminalHomEquiv
          ((smallEtaleDirectImage B S hS f').obj E)
          (x ≫ ((smallEtaleDirectImageCompIso B S hS g' f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) comm) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv).app E)) =
      (smallEtaleRingedToposModulesHom B S hS g').toToposHom.pushforwardTerminalHomEquiv E
        ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
          ((smallEtaleDirectImage B S hS g').obj E) x) := by
  have h₂ := MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans
    (smallEtaleRingedToposModulesHom B S hS f').toToposHom
    (smallEtaleRingedToposModulesHom B S hS g).toToposHom
    (smallEtaleRingedToposModulesHom B S hS (f' ≫ g)).toToposHom
    (smallEtaleDirectImageCompIso B S hS f' g).hom E
    (x ≫ ((smallEtaleDirectImageCompIso B S hS g' f).hom ≫
      eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) comm) ≫
      (smallEtaleDirectImageCompIso B S hS f' g).inv).app E)
  have h₁ := MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans
    (smallEtaleRingedToposModulesHom B S hS g').toToposHom
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom
    (smallEtaleRingedToposModulesHom B S hS (g' ≫ f)).toToposHom
    (smallEtaleDirectImageCompIso B S hS g' f).hom E x
  have heq : (x ≫ ((smallEtaleDirectImageCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) comm) ≫
        (smallEtaleDirectImageCompIso B S hS f' g).inv).app E) ≫
        (smallEtaleDirectImageCompIso B S hS f' g).hom.app E =
      (x ≫ (smallEtaleDirectImageCompIso B S hS g' f).hom.app E) ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) comm)).app E := by
    simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact h₂.symm.trans ((congrArg _ heq).trans
    ((pushforwardTerminalHomEquiv_comp_eqToHom comm E _).trans h₁))

/-- Reading a global section of the underlying sheaf of `k_*N` as one of the geometric direct
image of the underlying sheaf of `N`, and back, is the identity, at the pinned spelling. -/
theorem terminalHomEquivSections_symm_modulePushforwardSections {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (z : ⊤_ (Sheaf (SmallEtale.topology B S hS W.1) (Type u)) ⟶
      (moduleSetSheafFunctor B S hS W).obj ((modulePushforward B S hS k).obj N)) :
    (terminalHomEquivSections ((smallEtaleDirectImage B S hS k).obj
        ((moduleSetSheafFunctor B S hS Z).obj N))).symm
        (terminalHomEquivSections _ z) = z :=
  Equiv.symm_apply_apply (terminalHomEquivSections _) z

/-- The global sections of a morphism of modules into a direct image, read on the underlying
sheaves of sets, at the pinned spelling. -/
theorem terminalHomEquivSections_symm_globalSectionsFunctor_map {Z W : AlgebraicSpaces B S hS}
    (k : Z ⟶ W) (N : Modules.{u, u} B S hS Z.1 Z.2) {M : Modules.{u, u} B S hS W.1 W.2}
    (φ : M ⟶ (modulePushforward B S hS k).obj N) (s : M.sections) :
    (terminalHomEquivSections ((smallEtaleDirectImage B S hS k).obj
        ((moduleSetSheafFunctor B S hS Z).obj N))).symm
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O)).map φ).hom s) =
      (terminalHomEquivSections ((moduleSetSheafFunctor B S hS W).obj M)).symm s ≫
        (moduleSetSheafFunctor B S hS W).map φ :=
  rfl

/-- `pushforwardTerminalHomEquiv_squareComparison` read on compatible families of sections, for a
morphism `m` known to be the comparison of **Stacks 03G2**, part (3), around the square. -/
theorem terminalHomEquivSections_squareComparison (comm : g' ≫ f = f' ≫ g)
    (E : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (x : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS f).obj ((smallEtaleDirectImage B S hS g').obj E))
    (m : (smallEtaleDirectImage B S hS f).obj ((smallEtaleDirectImage B S hS g').obj E) ⟶
      (smallEtaleDirectImage B S hS g).obj ((smallEtaleDirectImage B S hS f').obj E))
    (hm : m = ((smallEtaleDirectImageCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) comm) ≫
        (smallEtaleDirectImageCompIso B S hS f' g).inv).app E) :
    terminalHomEquivSections E
        ((smallEtaleRingedToposModulesHom B S hS f').toToposHom.pushforwardTerminalHomEquiv E
          ((smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforwardTerminalHomEquiv
            ((smallEtaleDirectImage B S hS f').obj E) (x ≫ m))) =
      terminalHomEquivSections E
        ((smallEtaleRingedToposModulesHom B S hS g').toToposHom.pushforwardTerminalHomEquiv E
          ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
            ((smallEtaleDirectImage B S hS g').obj E) x)) := by
  subst hm
  exact congrArg (terminalHomEquivSections E)
    (pushforwardTerminalHomEquiv_squareComparison f g f' g' comm E x)

/-- Stacks 0732 for two composable direct images of modules, on underlying sheaves of sets. -/
private theorem globalSectionsPushforwardIsoSite_hom_app_comp_apply
    {Z W V : AlgebraicSpaces B S hS} (k : Z ⟶ W) (j : W ⟶ V) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (t : ((modulePushforward B S hS j).obj ((modulePushforward B S hS k).obj N)).sections) :
    ((globalSectionsPushforwardIsoSite B S hS k).hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS j).hom.app
          ((modulePushforward B S hS k).obj N)).hom t) =
      terminalHomEquivSections ((moduleSetSheafFunctor B S hS Z).obj N)
        ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv
          ((moduleSetSheafFunctor B S hS Z).obj N)
          ((smallEtaleRingedToposModulesHom B S hS j).toToposHom.pushforwardTerminalHomEquiv
            ((smallEtaleDirectImage B S hS k).obj ((moduleSetSheafFunctor B S hS Z).obj N))
            ((terminalHomEquivSections ((smallEtaleDirectImage B S hS j).obj
              ((smallEtaleDirectImage B S hS k).obj
                ((moduleSetSheafFunctor B S hS Z).obj N)))).symm t))) := by
  refine (globalSectionsPushforwardIsoSite_hom_app_apply_set k N _).trans ?_
  refine congrArg (fun z ↦ terminalHomEquivSections _
      ((smallEtaleRingedToposModulesHom B S hS k).toToposHom.pushforwardTerminalHomEquiv _ z)) ?_
  refine (congrArg (fun w ↦ (terminalHomEquivSections _).symm w)
    (globalSectionsPushforwardIsoSite_hom_app_apply_set j
      ((modulePushforward B S hS k).obj N) t)).trans
    ?_
  exact terminalHomEquivSections_symm_modulePushforwardSections k N _

/-- One side of `globalSectionsPushforwardIsoSite_squareComparison`, on underlying sheaves of
sets. -/
theorem globalSectionsPushforwardIsoSite_squareComparison_right
    (N : Modules.{u, u} B S hS X'.1 X'.2)
    (s : ((modulePushforward B S hS f).obj ((modulePushforward B S hS g').obj N)).sections) :
    ((globalSectionsPushforwardIsoSite B S hS g').hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS f).hom.app
          ((modulePushforward B S hS g').obj N)).hom s) =
      terminalHomEquivSections ((moduleSetSheafFunctor B S hS X').obj N)
        ((smallEtaleRingedToposModulesHom B S hS g').toToposHom.pushforwardTerminalHomEquiv
          ((moduleSetSheafFunctor B S hS X').obj N)
          ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
            ((smallEtaleDirectImage B S hS g').obj ((moduleSetSheafFunctor B S hS X').obj N))
            ((terminalHomEquivSections ((smallEtaleDirectImage B S hS f).obj
              ((smallEtaleDirectImage B S hS g').obj
                ((moduleSetSheafFunctor B S hS X').obj N)))).symm s))) := by
  exact globalSectionsPushforwardIsoSite_hom_app_comp_apply g' f N s

/-- The other side of `globalSectionsPushforwardIsoSite_squareComparison`, on underlying sheaves
of sets. -/
theorem globalSectionsPushforwardIsoSite_squareComparison_left (comm : g' ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2)
    (s : ((modulePushforward B S hS f).obj ((modulePushforward B S hS g').obj N)).sections) :
    ((globalSectionsPushforwardIsoSite B S hS f').hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS g).hom.app
          ((modulePushforward B S hS f').obj N)).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
            ((modulePushforwardSquareComparison B S hS g' f' f g comm).app N)).hom s)) =
      terminalHomEquivSections ((moduleSetSheafFunctor B S hS X').obj N)
        ((smallEtaleRingedToposModulesHom B S hS f').toToposHom.pushforwardTerminalHomEquiv
          ((moduleSetSheafFunctor B S hS X').obj N)
          ((smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforwardTerminalHomEquiv
            ((smallEtaleDirectImage B S hS f').obj ((moduleSetSheafFunctor B S hS X').obj N))
            ((terminalHomEquivSections ((smallEtaleDirectImage B S hS f).obj
              ((smallEtaleDirectImage B S hS g').obj
                ((moduleSetSheafFunctor B S hS X').obj N)))).symm s ≫
              (moduleSetSheafFunctor B S hS Y).map
                ((modulePushforwardSquareComparison B S hS g' f' f g comm).app N)))) := by
  have h₂ := terminalHomEquivSections_symm_globalSectionsFunctor_map g
    ((modulePushforward B S hS f').obj N)
    ((modulePushforwardSquareComparison B S hS g' f' f g comm).app N) s
  refine (globalSectionsPushforwardIsoSite_hom_app_comp_apply f' g N _).trans ?_
  exact congrArg (fun z ↦ terminalHomEquivSections _
    ((smallEtaleRingedToposModulesHom B S hS f').toToposHom.pushforwardTerminalHomEquiv _
      ((smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforwardTerminalHomEquiv _ z))) h₂

/-- **Global sections around a commutative square of algebraic spaces.**  A global section of
`f_*g'_*N` over `Y`, read on `X'` through **Stacks 0732** for `f` and then for `g'`, is the global
section obtained by first applying the comparison `f_* ∘ g'_* ⟶ g_* ∘ f'_*` of the two composite
direct images and then reading through Stacks 0732 for `g` and then for `f'`.

On underlying sheaves of sets the comparison of the composite direct images is the comparison of
**Stacks 03G2**, part (3), around the square
(`AlgebraicGeometry.Space.moduleSetSheafFunctor_map_modulePushforwardSquareComparison`), and
Stacks 0732 is the geometric comparison of global sections, which is compatible with composites
(`MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans`). -/
theorem globalSectionsPushforwardIsoSite_squareComparison (comm : g' ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2)
    (s : ((modulePushforward B S hS f).obj ((modulePushforward B S hS g').obj N)).sections) :
    ((globalSectionsPushforwardIsoSite B S hS f').hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS g).hom.app
          ((modulePushforward B S hS f').obj N)).hom
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
            ((modulePushforwardSquareComparison B S hS g' f' f g comm).app N)).hom s)) =
      ((globalSectionsPushforwardIsoSite B S hS g').hom.app N).hom
        (((globalSectionsPushforwardIsoSite B S hS f).hom.app
          ((modulePushforward B S hS g').obj N)).hom s) := by
  refine (globalSectionsPushforwardIsoSite_squareComparison_left f g f' g' comm N s).trans ?_
  refine Eq.trans ?_ (globalSectionsPushforwardIsoSite_squareComparison_right f g' N s).symm
  exact terminalHomEquivSections_squareComparison f g f' g' comm _ _ _
    (moduleSetSheafFunctor_map_modulePushforwardSquareComparison B S hS g' f' f g comm N)

end AlgebraicGeometry.Space

end
