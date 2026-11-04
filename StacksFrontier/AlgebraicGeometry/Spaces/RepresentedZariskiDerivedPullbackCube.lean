module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackModulesSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiDerivedModelSquareCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomCube
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The cube of the squares `Lε^* ⋙ Lf^* ≅ Lg₀^* ⋙ Lε'^*` of a representable algebraic space

For a morphism `g : T' ⟶ T` of the site,
`AlgebraicGeometry.Space.representedZariskiToposDerivedPullbackCompIso` is the square of derived
pullbacks between the Zariski topos of `T` and the small étale topos of the algebraic space it
represents (Stacks 08GH, via 0D6D). Along a commutative square
`p ≫ q = r ≫ s` of the site, the two pastings of these squares agree, read through the composition
laws of the derived pullbacks of the small étale topoi and of the Zariski topoi.

## Main results

* `AlgebraicGeometry.Space.representedZariskiToposDerivedPullbackCompIso_cube`: the cube.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

namespace AlgebraicGeometry.Space



attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W' W T' T : BigFppfOver B S hS} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (hw : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
    representedSpaceMap B S hS r ≫ representedSpaceMap B S hS s)
  (w₀ : B.inclusion.map p.left ≫ B.inclusion.map q.left =
    B.inclusion.map r.left ≫ B.inclusion.map s.left)

/-- **The cube of the squares `ρ_g : Lε_T^* ⋙ Lf_g^* ≅ Lg₀^* ⋙ Lε_{T'}^*`** (Stacks 08GH via 0D6D,
inverse form): along a commutative square `p ≫ q = r ≫ s` of the site, the two pastings
agree, read through the composition laws of the small étale and of the Zariski derived
pullbacks. -/
theorem representedZariskiToposDerivedPullbackCompIso_cube
    (Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))) :
    (representedZariskiToposDerivedPullbackCompIso B S hS p).inv.app
        ((derivedPullback
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map q.left).zariskiRingedToposHom).obj Y) ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS p)).map
        ((representedZariskiToposDerivedPullbackCompIso B S hS q).inv.app Y) ≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q)).hom ≫
        (smallEtaleDerivedModulePullbackCongr B S hS hw).hom ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS r)
          (representedSpaceMap B S hS s)).inv).app
            ((representedZariskiDerivedPullback B S hS T).obj Y) =
    (representedZariskiDerivedPullback B S hS W').map
        ((@Scheme.zariskiSquareDerivedPullbackIso
          (representedSchemeRepresentedZariskiRingedToposHom B S hS W')
          (representedSchemeRepresentedZariskiRingedToposHom B S hS W)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (B.inclusion.map p.left) (B.inclusion.map q.left) (B.inclusion.map r.left)
          (B.inclusion.map s.left) w₀).hom.app Y) ≫
      (representedZariskiToposDerivedPullbackCompIso B S hS r).inv.app
        ((derivedPullback
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map s.left).zariskiRingedToposHom).obj Y) ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS r)).map
        ((representedZariskiToposDerivedPullbackCompIso B S hS s).inv.app Y) := by
  have w : p ≫ q = r ≫ s := yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp]; exact congrArg (fun f => f.hom) hw)
  have H := derivedPullbackSquareIso_cube (ET := (smallEtaleRingedTopos B S hS
      (representedSpace T))) (EW := (smallEtaleRingedTopos B S hS
        (representedSpace W)))
    (ET' := (smallEtaleRingedTopos B S hS (representedSpace T'))) (EW' :=
      (smallEtaleRingedTopos B S hS (representedSpace W')))
    (ZT := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos) (ZW :=
      (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos) (ZT' :=
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos) (ZW' :=
          (representedSchemeRepresentedZariskiRingedToposHom B S hS W').zariskiRingedTopos)
    (B.inclusion.map q.left).zariskiRingedToposHom (B.inclusion.map p.left).zariskiRingedToposHom
      (B.inclusion.map s.left).zariskiRingedToposHom (B.inclusion.map r.left).zariskiRingedToposHom
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS q))
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS p))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS s))
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS r))
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W')
    (representedZariskiPullbackModulesCompIso B S hS q)
      (representedZariskiPullbackModulesCompIso B S hS p)
    (representedZariskiPullbackModulesCompIso B S hS s)
      (representedZariskiPullbackModulesCompIso B S hS r)
    (smallEtaleRingedToposHom B S hS (X := representedSpace W')
      (Y := representedSpace T)) hw
    (pullbackModulesCompTransport B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q))
    (pullbackModulesCompTransport B S hS (representedSpaceMap B S hS r)
      (representedSpaceMap B S hS s))
    (Scheme.zariskiSquarePullbackModulesIso (B.inclusion.map p.left) (B.inclusion.map q.left)
      (B.inclusion.map r.left) (B.inclusion.map s.left) w₀)
    (derivedPullback
      (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (B.inclusion.map q.left).zariskiRingedToposHom) HEq.rfl
    (derivedPullback
      (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS W').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
      (B.inclusion.map p.left).zariskiRingedToposHom) HEq.rfl
    (derivedPullback
      (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (B.inclusion.map s.left).zariskiRingedToposHom) HEq.rfl
    (derivedPullback
      (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS W').zariskiRingedTopos)
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (B.inclusion.map r.left).zariskiRingedToposHom) HEq.rfl
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q)) HEq.rfl
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS p)) HEq.rfl
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS s)) HEq.rfl
          (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS r)) HEq.rfl
    (representedZariskiDerivedPullback B S hS T) HEq.rfl
      (representedZariskiDerivedPullback B S hS W) HEq.rfl
        (representedZariskiDerivedPullback B S hS T') HEq.rfl
          (representedZariskiDerivedPullback B S hS W') HEq.rfl
    (smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q)) HEq.rfl
    (smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS r ≫ representedSpaceMap B S hS s)) HEq.rfl
    rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl rfl HEq.rfl
    (representedZariskiToposDerivedPullbackCompIso B S hS q) HEq.rfl
    (representedZariskiToposDerivedPullbackCompIso B S hS p) HEq.rfl
    (representedZariskiToposDerivedPullbackCompIso B S hS s) HEq.rfl
    (representedZariskiToposDerivedPullbackCompIso B S hS r) HEq.rfl
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q)) HEq.rfl
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS r)
      (representedSpaceMap B S hS s)) HEq.rfl
    (smallEtaleDerivedModulePullbackCongr B S hS hw) HEq.rfl
    (@Scheme.zariskiSquareDerivedPullbackIso
          (representedSchemeRepresentedZariskiRingedToposHom B S hS W')
          (representedSchemeRepresentedZariskiRingedToposHom B S hS W)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T')
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (B.inclusion.map p.left) (B.inclusion.map q.left) (B.inclusion.map r.left)
          (B.inclusion.map s.left) w₀) HEq.rfl
    (representedZariskiPullbackModulesSquareApp B S hS q)
      (fun M => by delta representedZariskiPullbackModulesSquareApp; heq_congr_full)
      (representedZariskiPullbackModulesSquareApp B S hS p)
        (fun M => by delta representedZariskiPullbackModulesSquareApp; heq_congr_full)
      (representedZariskiPullbackModulesSquareApp B S hS s)
        (fun M => by delta representedZariskiPullbackModulesSquareApp; heq_congr_full)
      (representedZariskiPullbackModulesSquareApp B S hS r)
        (fun M => by delta representedZariskiPullbackModulesSquareApp; heq_congr_full)
      (fun M => (B.inclusion.map p.left).zariskiPullbackModulesIsoSchemeModules.hom.app _ ≫
          (Scheme.Modules.pullback (B.inclusion.map p.left)).map
            ((B.inclusion.map q.left).zariskiPullbackModulesIsoSchemeModules.hom.app M) ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map p.left)
            (B.inclusion.map q.left)).hom.app M ≫
          (Scheme.Modules.pullbackCongr w₀).hom.app M ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map r.left)
            (B.inclusion.map s.left)).inv.app M ≫
          (Scheme.Modules.pullback (B.inclusion.map r.left)).map
            ((B.inclusion.map s.left).zariskiPullbackModulesIsoSchemeModules.inv.app M) ≫
          (B.inclusion.map r.left).zariskiPullbackModulesIsoSchemeModules.inv.app _)
      (fun M => by heq_congr_full)
      (fun M => (RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (representedSpace W'))
        (Y := smallEtaleRingedTopos B S hS (representedSpace W))
        (Z := smallEtaleRingedTopos B S hS (representedSpace T))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS p))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS q))).inv.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (pullbackModulesCompTransport B S hS (representedSpaceMap B S hS p)
        (representedSpaceMap B S hS q)).hom.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (eqToIso (congrArg (fun φ => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS (representedSpace W'))
          (Y := smallEtaleRingedTopos B S hS (representedSpace T))
          (smallEtaleRingedToposHom B S hS φ).toModulesHom) hw)).hom.app
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (pullbackModulesCompTransport B S hS (representedSpaceMap B S hS r)
        (representedSpaceMap B S hS s)).inv.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (representedSpace W'))
        (Y := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Z := smallEtaleRingedTopos B S hS (representedSpace T))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS r))
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS s))).hom.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M))
      (fun M => by heq_congr_full)
      (fun M => eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
        (representedZariskiPullbackModulesCompIso_cube B S hS p q r s w hw w₀ M))
          (by heq_congr)))) Y
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq H) (by heq_congr)))
end AlgebraicGeometry.Space
