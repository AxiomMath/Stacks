module

public meta import StacksFrontier.Tactic.HEqCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedPullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSquareCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtaleComp

/-!
# The topos form of the square of `ε^*` at one module

`AlgebraicGeometry.Space.representedZariskiPullbackModulesSquareApp` is the square
`f_g^*(ε_T^* M) ⟶ ε_{T'}^*(g_0^* M)` of pullbacks of modules of ringed topoi read off
`AlgebraicGeometry.Space.representedZariskiPullbackModulesCompIso`, and
`AlgebraicGeometry.Space.representedZariskiPullbackModulesSquareApp_eq` identifies it with the
square `AlgebraicGeometry.Space.representedZariskiModulePullbackCompIso` read through the
comparisons `AlgebraicGeometry.Space.pullbackModulesIsoModulePullback` and
`AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIsoSchemeModules` of the two pullbacks.
`AlgebraicGeometry.Space.pullbackModulesIsoModulePullback_congr` is the transport of the first
comparison along an equality of morphisms.

`AlgebraicGeometry.Space.representedZariskiPullbackModulesCompIso_cube` is the cube of these
squares along a commutative square `p ≫ q = r ≫ s` of the site: the two pastings agree, read
through the composition laws of the pullbacks of modules of the small étale ringed topoi and of the
Zariski pullbacks of the schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of the two pullbacks of modules along a morphism of algebraic spaces is
compatible with transport along an equality of morphisms. -/
theorem pullbackModulesIsoModulePullback_congr {X' Y' : AlgebraicSpaces B S hS} {f f' : X' ⟶ Y'}
    (h : f = f') :
    (pullbackModulesIsoModulePullback B S hS f).hom ≫ eqToHom (congrArg (modulePullback B S hS) h) =
      eqToHom (congrArg (fun φ => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y')
        (smallEtaleRingedToposHom B S hS φ).toModulesHom) h) ≫
            (pullbackModulesIsoModulePullback B S hS f').hom := by
  subst h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- An equality sandwiched between two heterogeneous equalities gives an equality. -/
private theorem eq_of_eq_of_heq_congr.{u_1} {α β : Sort u_1} {a b : α} {c d : β} (h : c = d)
    (h₁ : HEq a c) (h₂ : HEq d b) : a = b := by
  subst h
  exact eq_of_heq (h₁.trans h₂)

section Square

/-- The topos-level square `θ_g : ε_T^* ⋙ f_g^* ≅ g_0^* ⋙ ε_{T'}^*` read off
`representedZariskiPullbackModulesCompIso`, at one module. -/
def representedZariskiPullbackModulesSquareApp {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (schemeSpace T'))
        (Y := smallEtaleRingedTopos B S hS (schemeSpace T))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap g)).toModulesHom).obj
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ⟶
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').obj
        (((B.inclusion.map g.left).zariskiRingedToposHom.toModulesHom.pullbackModules).obj M) :=
  (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T)).inv.app M ≫
    (representedZariskiPullbackModulesCompIso B S hS g).hom.app M ≫
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (B.inclusion.map g.left).zariskiRingedToposHom).hom.app M

/-- The topos-level square at one module is the square of `ε^*` read through the comparisons of
the two pullbacks on both sides. -/
theorem representedZariskiPullbackModulesSquareApp_eq {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    representedZariskiPullbackModulesSquareApp B S hS g M =
      (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS g)).hom.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
        (representedZariskiModulePullbackCompIso B S hS g).hom.app M ≫
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').map
          ((B.inclusion.map g.left).zariskiPullbackModulesIsoSchemeModules.inv.app M) := by
  have key := Stacks.CategoryTheory.SquareComposition.conjugatedSquare_hom_app_of_eq
    (c := RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := smallEtaleRingedTopos B S hS (representedSpace T))
        (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T))
    (c' := RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (representedSpace T'))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
        (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
        (B.inclusion.map g.left).zariskiRingedToposHom)
    (π := pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS g))
    (τ := representedZariskiModulePullbackCompIso B S hS g)
    (ζ := (B.inclusion.map g.left).zariskiPullbackModulesIsoSchemeModules)
    (ρ := representedZariskiPullbackModulesCompIso B S hS g) rfl M
  exact eq_of_eq_of_heq_congr key (by heq_congr) (by heq_congr)

end Square

section Cube

/- The two instances below make the pullbacks of modules of the small étale ringed topoi cheap to
elaborate and to check in the statement of the cube. -/
attribute [local instance 10000] AlgebraicGeometry.Space.hasSheafCompose_smallEtale_forget₂_ringCat

attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

variable {W' W T' T : BigFppfOver B S hS} (p : W' ⟶ W) (q : W ⟶ T) (r : W' ⟶ T') (s : T' ⟶ T)
  (w : p ≫ q = r ≫ s)
  (hw : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
    representedSpaceMap B S hS r ≫ representedSpaceMap B S hS s)
  (w₀ : B.inclusion.map p.left ≫ B.inclusion.map q.left =
    B.inclusion.map r.left ≫ B.inclusion.map s.left)

include w in
/-- **The cube of `representedZariskiPullbackModulesCompIso`** (the topos form of the square of
Stacks 08GH on pullbacks of modules): along a commutative square `p ≫ q = r ≫ s` of the site, the
two pastings of the squares `ε_T^* ⋙ f_g^* ≅ g_0^* ⋙ ε_{T'}^*` agree, read through the composition
laws of the pullbacks of modules of the small étale ringed topoi (Stacks 0D6D underived) and of the
Zariski pullbacks of the schemes. -/
theorem representedZariskiPullbackModulesCompIso_cube
    (M : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS (schemeSpace W'))
        (Y := smallEtaleRingedTopos B S hS (schemeSpace W))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap p)).toModulesHom).map
        (representedZariskiPullbackModulesSquareApp B S hS q M) ≫
      representedZariskiPullbackModulesSquareApp B S hS p
        (((B.inclusion.map q.left).zariskiRingedToposHom.toModulesHom.pullbackModules).obj M) ≫
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS W').map
        ((B.inclusion.map p.left).zariskiPullbackModulesIsoSchemeModules.hom.app _ ≫
          (Scheme.Modules.pullback (B.inclusion.map p.left)).map
            ((B.inclusion.map q.left).zariskiPullbackModulesIsoSchemeModules.hom.app M) ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map p.left)
              (B.inclusion.map q.left)).hom.app M ≫
          (Scheme.Modules.pullbackCongr w₀).hom.app M ≫
          (Scheme.Modules.pullbackComp (B.inclusion.map r.left)
              (B.inclusion.map s.left)).inv.app M ≫
          (Scheme.Modules.pullback (B.inclusion.map r.left)).map
            ((B.inclusion.map s.left).zariskiPullbackModulesIsoSchemeModules.inv.app M) ≫
          (B.inclusion.map r.left).zariskiPullbackModulesIsoSchemeModules.inv.app _) =
    ((RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (schemeSpace W'))
        (Y := smallEtaleRingedTopos B S hS (schemeSpace W))
        (Z := smallEtaleRingedTopos B S hS (schemeSpace T))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap p))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap q))).inv.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (pullbackModulesCompTransport B S hS (schemeSpaceMap p)
        (schemeSpaceMap q)).hom.app
            ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (eqToIso (congrArg (fun φ => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS (schemeSpace W'))
          (Y := smallEtaleRingedTopos B S hS (schemeSpace T))
          (smallEtaleRingedToposHom B S hS φ).toModulesHom) hw)).hom.app
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (pullbackModulesCompTransport B S hS (schemeSpaceMap r)
        (schemeSpaceMap s)).inv.app
            ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M) ≫
      (RingedToposHom.pullbackModulesCompIso
        (X := smallEtaleRingedTopos B S hS (schemeSpace W'))
        (Y := smallEtaleRingedTopos B S hS (schemeSpace T'))
        (Z := smallEtaleRingedTopos B S hS (schemeSpace T))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap r))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap s))).hom.app
          ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj M)) ≫
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS (schemeSpace W'))
        (Y := smallEtaleRingedTopos B S hS (schemeSpace T'))
        (smallEtaleRingedToposHom B S hS (schemeSpaceMap r)).toModulesHom).map
        (representedZariskiPullbackModulesSquareApp B S hS s M) ≫
      representedZariskiPullbackModulesSquareApp B S hS r
        (((B.inclusion.map s.left).zariskiRingedToposHom.toModulesHom.pullbackModules).obj M) := by
  delta representedZariskiPullbackModulesSquareApp
  have hcube := representedZariskiModulePullbackCompIso_cube B S hS p q r s w hw w₀ M
  have key := Stacks.CategoryTheory.SquareComposition.conjugatedSquare_comparison_cube
    (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS p))
        (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS q))
        (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS r))
        (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS s))
    (pullbackModulesIsoModulePullback B S hS
        ((representedSpaceMap B S hS p) ≫ (representedSpaceMap B S hS q)))
    (pullbackModulesIsoModulePullback B S hS
        ((representedSpaceMap B S hS r) ≫ (representedSpaceMap B S hS s)))
    (B.inclusion.map p.left).zariskiPullbackModulesIsoSchemeModules
        (B.inclusion.map q.left).zariskiPullbackModulesIsoSchemeModules
        (B.inclusion.map r.left).zariskiPullbackModulesIsoSchemeModules
        (B.inclusion.map s.left).zariskiPullbackModulesIsoSchemeModules
    (representedZariskiModulePullbackCompIso B S hS p)
        (representedZariskiModulePullbackCompIso B S hS q) (representedZariskiModulePullbackCompIso
        B S hS r) (representedZariskiModulePullbackCompIso B S hS s)
    (Scheme.Modules.pullbackComp (B.inclusion.map p.left) (B.inclusion.map q.left)).hom
    (Scheme.Modules.pullbackCongr w₀).hom
    (Scheme.Modules.pullbackComp (B.inclusion.map r.left) (B.inclusion.map s.left)).inv
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace W))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS p))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W))
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS q))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T))
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS r))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T'))
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := smallEtaleRingedTopos B S hS (representedSpace T))
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS s))
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T))
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W')
      (B.inclusion.map p.left).zariskiRingedToposHom)
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W).zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W)
      (B.inclusion.map q.left).zariskiRingedToposHom)
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace W'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS W').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS W')
      (B.inclusion.map r.left).zariskiRingedToposHom)
    (RingedToposHom.pullbackModulesCompIso
      (X := smallEtaleRingedTopos B S hS (representedSpace T'))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
      (Z := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T')
      (B.inclusion.map s.left).zariskiRingedToposHom)
    (representedZariskiPullbackModulesCompIso B S hS p)
        (representedZariskiPullbackModulesCompIso B S hS q)
        (representedZariskiPullbackModulesCompIso B S hS r)
        (representedZariskiPullbackModulesCompIso B S hS s)
    rfl rfl rfl rfl
    (pullbackModulesCompIso_inv_comp_pullbackModulesIsoModulePullback (representedSpaceMap B S hS p)
        (representedSpaceMap B S hS q))
    (pullbackModulesCompIso_inv_comp_pullbackModulesIsoModulePullback (representedSpaceMap B S hS r)
        (representedSpaceMap B S hS s))
    (pullbackModulesIsoModulePullback_congr B S hS hw) M
    (eq_of_eq_of_heq_congr hcube (by heq_congr) (by heq_congr))
  exact eq_of_eq_of_heq_congr key (by heq_congr) (by heq_congr)

end Cube

end AlgebraicGeometry.Space
