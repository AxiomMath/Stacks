module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence

/-!
# The derived base change map of algebraic spaces through the underived one

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces.  Its derived base change map
`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` (`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap`,
Stacks 07A7) is the mate of the comparison of the two iterated derived pullbacks.  The same
construction on unbounded homotopy categories, with degreewise pullback and direct image of
modules, gives the *underived* base change map `g^* f_* ⟶ f'_* (g')^*`,
`AlgebraicGeometry.Space.smallEtaleUnderivedBaseChangeMap`.

This file shows that the derived map is computed by the underived one at K-injective complexes,
when the horizontal morphisms `g` and `g'` are étale: then degreewise pullback along them is
exact, so computes the derived pullback, and preserves K-injective complexes, so that both
derived direct images are computed degreewise.  Consequently, if the underived base change map
is invertible, so is the derived one, at every object.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso` and
  `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackSquareIso`: the two composites of
  degreewise pullback around the square, identified with degreewise pullback along `f' ≫ g`.
* `AlgebraicGeometry.Space.smallEtaleUnderivedBaseChangeMap`: the underived base change map.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_hom_app_comparison` and
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSquareIso_hom_app_comparison`: the composition
  law of derived pullbacks (Stacks 0D6D) and the square comparison are induced by the underived
  ones through the comparisons `Lf^* ⟶ f^*`.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale` and
  `AlgebraicGeometry.Space.isKInjective_pullbackModules_of_isEtale`: along an étale morphism,
  `La^* = a^*` and `a^*` preserves K-injective complexes.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isIso_underived`: for `g`
  and `g'` étale, invertibility of the underived base change map gives invertibility of the
  derived one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pullbackMapHomotopy
  pushforwardOnHomotopy sourceQuasiIso pushforwardMapHomotopy pullbackAdjPushforwardMapHomotopy)

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comparisons

variable {X Y Z : AlgebraicSpaces B S hS}

/-- Degreewise pullback of complexes of modules along a morphism of algebraic spaces, on the
unbounded homotopy categories. -/
abbrev smallEtalePullbackMapHomotopy (f : X ⟶ Y) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) :=
  pullbackMapHomotopy (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f)

/-- Degreewise direct image of complexes of modules along a morphism of algebraic spaces, on the
unbounded homotopy categories. -/
abbrev smallEtalePushforwardMapHomotopy (f : X ⟶ Y) :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) :=
  pushforwardMapHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The degreewise adjunction `f^* ⊣ f_*` on unbounded homotopy categories. -/
abbrev smallEtaleMapHomotopyAdjunction (f : X ⟶ Y) :
    smallEtalePullbackMapHomotopy B S hS f ⊣ smallEtalePushforwardMapHomotopy B S hS f :=
  pullbackAdjPushforwardMapHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- Degreewise pullback along a composite of algebraic spaces is the composite of the degreewise
pullbacks, on unbounded homotopy categories: the compositor of the morphisms of ringed topoi
followed by the 2-isomorphism of Stacks 03G8 between the composite of the morphisms of ringed
topoi and the morphism of ringed topoi of the composite. -/
def smallEtaleUnderivedPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePullbackMapHomotopy B S hS g ⋙
        smallEtalePullbackMapHomotopy B S hS f ≅
      smallEtalePullbackMapHomotopy B S hS (f ≫ g) :=
  haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f g)
  haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS (f ≫ g))
  pullbackMapHomotopyCompIso (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) ≪≫
    Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
      (ComplexShape.up ℤ)

/-- The composition law of derived pullbacks of algebraic spaces is induced, through the
comparisons `Lf^* ⟶ f^*`, by the underived one. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_comparison (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (f ≫ g)).app M =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS f).app
          ((smallEtalePullbackMapHomotopy B S hS g).obj M) ≫
        DerivedCategory.Qh.map ((smallEtaleUnderivedPullbackCompIso B S hS f g).hom.app M) := by
  rw [smallEtaleDerivedModulePullbackCompIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have h := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g) (pullbackModulesCompTransport B S hS f g) M
  have e := derivedPullbackCompIso_hom (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g)
  rw [e, smallEtaleUnderivedPullbackCompIso]
  refine h.trans ?_
  congr 2

/-- The transport of degreewise pullbacks along an equality of morphisms of algebraic spaces. -/
def smallEtaleUnderivedPullbackCongr {f f' : X ⟶ Y} (h : f = f') :
    smallEtalePullbackMapHomotopy B S hS f ≅
      smallEtalePullbackMapHomotopy B S hS f' :=
  eqToIso (congrArg (smallEtalePullbackMapHomotopy B S hS) h)

/-- The transport of derived pullbacks along an equality of morphisms is induced by that of
degreewise pullbacks. -/
theorem smallEtaleDerivedModulePullbackCongr_hom_app_comparison {f f' : X ⟶ Y} (h : f = f')
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackCongr B S hS h).hom.app (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS f').app M =
      (smallEtaleDerivedModulePullbackComparison B S hS f).app M ≫
        DerivedCategory.Qh.map ((smallEtaleUnderivedPullbackCongr B S hS h).hom.app M) := by
  subst h
  simp [smallEtaleDerivedModulePullbackCongr, smallEtaleUnderivedPullbackCongr]

/-- The counit of `Lf^* ⊣ Rf_*` is induced, through the comparison `Lf^* ⟶ f^*` and the unit
`f_* ⟶ Rf_*` of the derived direct image, by the counit of the degreewise adjunction
(Stacks 0FPI). -/
theorem smallEtaleDerivedModuleAdjunction_counit_fac (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullback B S hS f).map
        (((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
            (sourceQuasiIso (smallEtaleRingedTopos B S hS X))).app K) ≫
        (smallEtaleDerivedModuleAdjunction B S hS f).counit.app (DerivedCategory.Qh.obj K) =
      (smallEtaleDerivedModulePullbackComparison B S hS f).app
          ((smallEtalePushforwardMapHomotopy B S hS f).obj K) ≫
        DerivedCategory.Qh.map ((smallEtaleMapHomotopyAdjunction B S hS f).counit.app K) :=
  derivedAdjunction_counit_fac (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) K

end Comparisons

section Etale

variable {X Y : AlgebraicSpaces B S hS}

/-- The pullback of modules along the morphism of small étale ringed topoi of an étale morphism
of algebraic spaces is isomorphic to étale restriction. -/
private def pullbackModulesIsoEtaleModulePullback (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS a).toModulesHom ≅
    etaleModulePullback.{u, u} B S hS a ha :=
  pullbackModulesIsoModulePullback B S hS a ≪≫ modulePullbackIsoEtaleModulePullback B S hS a ha

/-- The pullback of modules along the morphism of small étale ringed topoi of an étale morphism
of algebraic spaces is left exact: it is étale restriction. -/
theorem preservesFiniteLimits_pullbackModules_of_isEtale (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) :
    PreservesFiniteLimits (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS a).toModulesHom) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (pullbackModulesIsoEtaleModulePullback B S hS a ha).symm
    (preservesFiniteLimits_etaleModulePullback B S hS a ha)

/-- Along an étale morphism of algebraic spaces the comparison `La^* ⟶ a^*` is an isomorphism
at every complex: degreewise pullback is exact, so computes the derived pullback. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale (a : X ⟶ Y)
    (ha : IsEtale B S hS a.hom)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS a).app M) :=
  have := preservesFiniteLimits_pullbackModules_of_isEtale B S hS a ha
  isIso_derivedPullbackComparison_app (smallEtaleRingedToposHom B S hS a) ⊤
    (hasResolutions_top (Y := smallEtaleRingedTopos B S hS Y))
    (pullbackInvertsQuasiIso_top (smallEtaleRingedToposHom B S hS a)) M trivial

/-- Degreewise pullback along an étale morphism of algebraic spaces carries K-injective
complexes to K-injective complexes. -/
theorem isKInjective_pullbackModules_of_isEtale (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS a).toModulesHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS a).toModulesHom
  let G : type_of% F := etaleModulePullback.{u, u} B S hS a ha
  have : G.Additive := etaleModulePullback_additive B S hS a ha
  let e : F ≅ G := pullbackModulesIsoEtaleModulePullback B S hS a ha
  have : CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_etaleModulePullback B S hS a ha (etaleModuleLowerShriekAdjunction B S hS a ha) I hI
  CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).symm.app I)

end Etale

section BaseChange

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- Degreewise pullback around the top and right of a commutative square, identified with
degreewise pullback along `f' ≫ g`. -/
def smallEtaleUnderivedPullbackSquareIso :
    smallEtalePullbackMapHomotopy B S hS f ⋙
        smallEtalePullbackMapHomotopy B S hS g' ≅
      smallEtalePullbackMapHomotopy B S hS (f' ≫ g) :=
  smallEtaleUnderivedPullbackCompIso B S hS g' f ≪≫ smallEtaleUnderivedPullbackCongr B S hS w

/-- The comparison of the two iterated derived pullbacks around the square is the composition
law followed by the transport along `g' ≫ f = f' ≫ g`. -/
theorem smallEtaleDerivedPullbackSquareIso_eq :
    smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w =
      smallEtaleDerivedModulePullbackCompIso B S hS g' f ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS w := rfl

/-- The comparison of the two composites of degreewise pullback around the square is the
composition law followed by the transport along `g' ≫ f = f' ≫ g`. -/
theorem smallEtaleUnderivedPullbackSquareIso_eq :
    smallEtaleUnderivedPullbackSquareIso B S hS f g f' g' w =
      smallEtaleUnderivedPullbackCompIso B S hS g' f ≪≫
        smallEtaleUnderivedPullbackCongr B S hS w := rfl

/-- `smallEtaleDerivedPullbackSquareIso_eq` on the underlying morphisms. -/
theorem smallEtaleDerivedPullbackSquareIso_hom :
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).hom =
      (smallEtaleDerivedModulePullbackCompIso B S hS g' f).hom ≫
        (smallEtaleDerivedModulePullbackCongr B S hS w).hom := rfl

/-- `smallEtaleUnderivedPullbackSquareIso_eq` on the underlying morphisms. -/
theorem smallEtaleUnderivedPullbackSquareIso_hom :
    (smallEtaleUnderivedPullbackSquareIso B S hS f g f' g' w).hom =
      (smallEtaleUnderivedPullbackCompIso B S hS g' f ≪≫
        smallEtaleUnderivedPullbackCongr B S hS w).hom := rfl

/-- The comparison of the two iterated derived pullbacks around the square is induced, through
the comparisons `Lf^* ⟶ f^*`, by that of the two degreewise pullbacks. -/
theorem smallEtaleDerivedPullbackSquareIso_hom_app_comparison
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).hom.app
          (DerivedCategory.Qh.obj M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (f' ≫ g)).app M =
      (smallEtaleDerivedModulePullback B S hS g').map
          ((smallEtaleDerivedModulePullbackComparison B S hS f).app M) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS g').app
          ((smallEtalePullbackMapHomotopy B S hS f).obj M) ≫
        DerivedCategory.Qh.map
          ((smallEtaleUnderivedPullbackSquareIso B S hS f g f' g' w).hom.app M) := by
  have h₁ := smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS g' f M
  have h₂ := smallEtaleDerivedModulePullbackCongr_hom_app_comparison B S hS w M
  rw [smallEtaleDerivedPullbackSquareIso_hom, NatTrans.comp_app, Category.assoc, h₂,
    reassoc_of% h₁, smallEtaleUnderivedPullbackSquareIso_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp]

/-- **The underived base change map** `g^* f_* K ⟶ f'_* (g')^* K` of a commutative square of
algebraic spaces, on unbounded homotopy categories of modules: the transpose, under the
degreewise adjunctions `f^* ⊣ f_*` and `f'^* ⊣ f'_*`, of the comparison of the two composites
of degreewise pullback followed by `(g')^*` of the counit. -/
abbrev smallEtaleUnderivedBaseChangeMap
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :=
  Stacks.CategoryTheory.BaseChange.map
    (smallEtaleMapHomotopyAdjunction B S hS f)
    (smallEtaleMapHomotopyAdjunction B S hS f')
    (smallEtaleUnderivedPullbackCompIso B S hS f' g)
    (smallEtaleUnderivedPullbackSquareIso B S hS f g f' g' w) K

/-- The base change map of the pullback and direct image of modules along the morphisms of small
étale ringed topoi around a commutative square: the mate of the composition laws of Stacks 03D6
followed by the 2-isomorphisms of Stacks 03G8 and the transport along `g' ≫ f = f' ≫ g`. -/
abbrev smallEtaleModuleBaseChangeMap
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  Stacks.CategoryTheory.BaseChange.map
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f'))
    ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f' g)
    (((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g')
        (smallEtaleRingedToposHom B S hS f)).symm ≪≫ pullbackModulesCompTransport B S hS g' f) ≪≫
      eqToIso (congrArg (fun k : X' ⟶ Y =>
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS k).toModulesHom) w)) M

/-- The underived base change map on homotopy categories is invertible as soon as the base
change map of modules is invertible at every module. -/
theorem isIso_smallEtaleUnderivedBaseChangeMap_of_isIso
    (hiso : ∀ M, IsIso (smallEtaleModuleBaseChangeMap B S hS f g f' g' w M))
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    IsIso (smallEtaleUnderivedBaseChangeMap B S hS f g f' g' w K) :=
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f' g)
  have := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS g' f)
  Stacks.CategoryTheory.BaseChange.isIso_map_mapHomotopyCategory
    (fun k : X' ⟶ Y => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS k).toModulesHom) w
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X')
      (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS f'))
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f')
        (smallEtaleRingedToposHom B S hS g)).symm (pullbackModulesCompTransport B S hS f' g)
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g')
        (smallEtaleRingedToposHom B S hS f)).symm (pullbackModulesCompTransport B S hS g' f)
    hiso K

/-- **The derived base change map is invertible as soon as the underived one is**, for a
commutative square of algebraic spaces whose horizontal morphisms are étale.

At a K-injective complex `I` the three derived functors in sight are computed degreewise:
`Rf_* I = f_* I`; restriction along the étale `g'` preserves K-injectivity, so
`Rf'_*((g')^* I) = f'_*((g')^* I)`; and the derived pullback along an étale morphism is
degreewise pullback.  Through these identifications the derived base change map at `I` is the
underived one (`Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_twoSquare_eq`), and every
object of `D(𝒪_X)` is isomorphic to a K-injective complex. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_isIso_underived (hg : IsEtale B S hS g.hom)
    (hg' : IsEtale B S hS g'.hom)
    (hβ : ∀ K, IsIso (smallEtaleUnderivedBaseChangeMap B S hS f g f' g' w K))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh K
  let uf := (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X))
  let uf' := (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS Y')
    (smallEtaleRingedToposHom B S hS f')).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS X'))
  let I₀ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  have h₁ : IsIso (uf.app I₀) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ _ I hI
  have h₂ : IsIso (uf'.app ((smallEtalePullbackMapHomotopy B S hS g').obj I₀)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ _ _
      (isKInjective_pullbackModules_of_isEtale B S hS g' hg' I hI)
  have h₃ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS g' hg' I₀
  have h₄ := isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS g hg
    ((smallEtalePushforwardMapHomotopy B S hS f).obj I₀)
  have h₅ := hβ I₀
  unfold smallEtaleUnderivedBaseChangeMap at h₅
  rw [smallEtaleUnderivedPullbackSquareIso_eq, smallEtaleUnderivedPullbackCongr] at h₅
  have key := Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_twoSquare_eq
    (smallEtaleMapHomotopyAdjunction B S hS f) (smallEtaleMapHomotopyAdjunction B S hS f')
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (smallEtaleDerivedModulePullbackComparison B S hS f')
    (smallEtaleDerivedModulePullbackComparison B S hS g)
    (smallEtaleDerivedModulePullbackComparison B S hS g') uf uf'
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f) (smallEtalePullbackMapHomotopy B S hS)
    (fun f ↦ smallEtaleDerivedModulePullbackComparison B S hS f) w
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso B S hS g' f)
    (smallEtaleUnderivedPullbackCompIso B S hS f' g)
    (smallEtaleUnderivedPullbackCompIso B S hS g' f)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f')
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS f' g)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS g' f) I₀ h₁ h₃ h₄ h₅ h₂
  rw [← smallEtaleDerivedModulePullbackCongr.eq_1 (h := w), ← smallEtaleDerivedPullbackSquareIso_eq]
    at key
  have hK := (Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso _ _ _ _ e).1 key
  exact hK

end BaseChange

end AlgebraicGeometry.Space

end
